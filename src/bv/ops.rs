// Copyright 2023-2024 The Regents of the University of California
// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>
//
// Traits for operations on bit-vectors.

use crate::bv::arithmetic::mask_double_word;
use crate::bv::io::strings::ParseIntError;
use crate::bv::owned::{double_word_from_words, double_word_to_words};
use crate::{mask, BitVecValue, BitVecValueRef, DoubleWord, WidthInt, Word};

/// Declares an arithmetic function which takes in two equal size bitvector and yields a
/// bitvector of the same size.
macro_rules! declare_arith_bin_fn {
    ($name:ident) => {
        fn $name<R: BitVecOps>(&self, rhs: &R) -> BitVecValue {
            debug_assert_eq!(self.width(), rhs.width());
            debug_assert_eq!(self.words().len(), rhs.words().len());
            let mut out = BitVecValue::zero(self.width());
            if self.words().len() == 1 {
                // specialized for 1-word case
                crate::bv::arithmetic::$name(
                    &mut out.words_mut()[0..1],
                    &self.words()[0..1],
                    &rhs.words()[0..1],
                    self.width(),
                );
            } else {
                crate::bv::arithmetic::$name(
                    out.words_mut(),
                    self.words(),
                    rhs.words(),
                    self.width(),
                );
            }
            out
        }
    };
}

/// Declares a bitwise function which takes in two equal size bitvector and yields a
/// bitvector of the same size.
macro_rules! declare_bit_arith_bin_fn {
    ($name:ident) => {
        fn $name<R: BitVecOps>(&self, rhs: &R) -> BitVecValue {
            debug_assert_eq!(self.width(), rhs.width());
            debug_assert_eq!(self.words().len(), rhs.words().len());
            let mut out = BitVecValue::zero(self.width());
            if self.words().len() == 1 {
                // specialized for 1-word case
                crate::bv::arithmetic::$name(
                    &mut out.words_mut()[0..1],
                    &self.words()[0..1],
                    &rhs.words()[0..1],
                );
            } else {
                crate::bv::arithmetic::$name(out.words_mut(), self.words(), rhs.words());
            }
            out
        }
    };
}

/// Operations over immutable bit-vector values.
pub trait BitVecOps {
    fn width(&self) -> WidthInt;
    fn words(&self) -> &[Word];

    /// Convert to a string of 1s and 0s.
    fn to_bit_str(&self) -> String {
        crate::bv::io::strings::to_bit_str(self.words(), self.width())
    }

    /// Convert to a string of 1s and 0s with a `-` if the value is negative.
    fn to_bit_str_signed(&self) -> String {
        crate::bv::io::strings::to_bit_str_signed(self.words(), self.width())
    }

    /// Convert to a string of hex characters
    fn to_hex_str(&self) -> String {
        crate::bv::io::strings::to_hex_str(self.words(), self.width())
    }

    /// Convert to a string of a decimal number. No leading zeros.
    fn to_dec_str(&self) -> String {
        crate::bv::io::strings::to_dec_str(self.words(), self.width())
    }

    /// Convert to a string of hex characters with a `-` if the value is negative.
    fn to_hex_str_signed(&self) -> String {
        crate::bv::io::strings::to_hex_str_signed(self.words(), self.width())
    }

    fn to_bytes_le(&self) -> Vec<u8> {
        crate::bv::io::bytes::to_bytes_le(self.words(), self.width())
    }

    #[cfg(feature = "bigint")]
    fn to_big_int(&self) -> num_bigint::BigInt {
        crate::bv::io::bigint::to_big_int(self.words(), self.width())
    }

    #[cfg(feature = "bigint")]
    fn to_big_uint(&self) -> num_bigint::BigUint {
        crate::bv::io::bigint::to_big_uint(self.words())
    }

    #[cfg(feature = "fraction1")]
    fn to_signed_fixed_point(&self, fraction_width: WidthInt) -> Option<fraction::Fraction> {
        debug_assert!(fraction_width <= self.width());
        if self.is_negative() {
            // before we do a costly conversion we make sure that we can actually fit into 64-bits
            if self.width() > u64::BITS {
                None
            } else {
                let negated = self.negate();
                let frac = negated.to_unsigned_fixed_point(fraction_width);
                frac.map(|f| -f)
            }
        } else {
            self.to_unsigned_fixed_point(fraction_width)
        }
    }

    #[cfg(feature = "fraction1")]
    fn to_unsigned_fixed_point(&self, fraction_width: WidthInt) -> Option<fraction::Fraction> {
        debug_assert!(fraction_width <= self.width());
        let denom = 1u64 << fraction_width;
        self.to_u64().map(|v| fraction::Fraction::new(v, denom))
    }

    /// Returns value as a bool iff the value is a 1-bit value.
    fn to_bool(&self) -> Option<bool> {
        if self.width() == 1 {
            Some(crate::bv::arithmetic::word_to_bool(self.words()[0]))
        } else {
            None
        }
    }

    /// Returns the value as a 64-bit unsigned integer if the value can be represented
    fn to_u64(&self) -> Option<u64> {
        debug_assert_eq!(Word::BITS, u64::BITS);
        // check msbs
        let non_zero_msb = self.words().iter().skip(1).any(|w| *w != 0);
        if non_zero_msb {
            None
        } else {
            Some(self.words().iter().next().cloned().unwrap_or(0))
        }
    }

    /// Returns the value as a 64-bit signed integer if the value can be represented
    fn to_i64(&self) -> Option<i64> {
        debug_assert_eq!(Word::BITS, i64::BITS);
        if self.width() <= i64::BITS {
            if self.width() == 0 {
                Some(0)
            } else if self.width() == i64::BITS {
                Some(self.words()[0] as i64)
            } else {
                debug_assert_eq!(self.words().len(), 1);
                if crate::bv::arithmetic::is_neg(self.words(), self.width()) {
                    let extra_sign_bits =
                        crate::bv::arithmetic::mask(Word::BITS - self.width()) << self.width();
                    Some((self.words()[0] | extra_sign_bits) as i64)
                } else {
                    Some(self.words()[0] as i64)
                }
            }
        } else {
            let all_zero_msbs = self.words().iter().skip(1).all(|w| *w == 0);
            let word_0 = self.words()[0];
            let all_max_msbs = self.words().iter().skip(1).all(|w| *w == Word::MAX);
            match (
                all_zero_msbs,
                all_max_msbs,
                crate::bv::arithmetic::is_neg(&[word_0], Word::BITS),
            ) {
                (true, false, false) => Some(word_0 as i64),
                (false, true, true) => Some(word_0 as i64),
                _ => None,
            }
        }
    }

    fn is_true(&self) -> bool {
        self.width() == 1 && self.words()[0] == 1
    }

    fn is_false(&self) -> bool {
        self.width() == 1 && self.words()[0] == 0
    }

    fn is_zero(&self) -> bool {
        self.words().iter().all(|w| *w == 0)
    }

    fn is_one(&self) -> bool {
        let msbs_are_zero = self.words().iter().skip(1).all(|w| *w == 0);
        msbs_are_zero && self.words()[0] == 1
    }

    fn is_all_ones(&self) -> bool {
        let lsbs_are_max = self
            .words()
            .iter()
            .take(self.words().len() - 1)
            .all(|w| *w == Word::MAX);
        lsbs_are_max && (*self.words().last().unwrap() == mask(self.width() % Word::BITS))
    }

    fn is_negative(&self) -> bool {
        crate::bv::arithmetic::is_neg(self.words(), self.width())
    }

    fn is_pow_2(&self) -> Option<WidthInt> {
        // find most significant bit set
        let mut bit_pos = None;
        for (word_ii, &word) in self.words().iter().enumerate() {
            if bit_pos.is_none() {
                if word != 0 {
                    // is there only one bit set?
                    if word.leading_zeros() + word.trailing_zeros() == Word::BITS - 1 {
                        bit_pos = Some(word.trailing_zeros() + word_ii as WidthInt * Word::BITS);
                    } else {
                        // more than one bit set
                        return None;
                    }
                }
            } else if word != 0 {
                // more than one bit set
                return None;
            }
        }
        bit_pos
    }

    /// Computes all ranges for which the bits are one.
    fn bit_set_intervals(&self) -> Vec<std::ops::Range<WidthInt>> {
        match self.width() {
            0 => vec![],
            1 if self.is_zero() => vec![],
            1 => {
                let range = 0..1;
                vec![range]
            }
            _ => crate::bv::arithmetic::find_ranges_of_ones(self.words()),
        }
    }

    declare_arith_bin_fn!(add);
    declare_arith_bin_fn!(sub);
    declare_arith_bin_fn!(shift_left);
    declare_arith_bin_fn!(shift_right);
    declare_arith_bin_fn!(arithmetic_shift_right);

    fn mul<R: BitVecOps>(&self, rhs: &R) -> BitVecValue {
        debug_assert_eq!(self.width(), rhs.width());
        debug_assert_eq!(self.words().len(), rhs.words().len());
        match (self.words(), rhs.words()) {
            ([a], [b]) => {
                BitVecValue::from_u64(a.overflowing_mul(*b).0 & mask(self.width()), self.width())
            }
            ([a_lsb, a_msb], [b_lsb, b_msb]) => BitVecValue::from_u128(
                double_word_from_words(*a_lsb, *a_msb)
                    .overflowing_mul(double_word_from_words(*b_lsb, *b_msb))
                    .0
                    & mask_double_word(self.width()),
                self.width(),
            ),
            (a_words, b_words) => {
                let mut out = BitVecValue::zero(self.width());
                crate::bv::arithmetic::mul(out.words_mut(), a_words, b_words, self.width());
                out
            }
        }
    }

    declare_bit_arith_bin_fn!(and);
    declare_bit_arith_bin_fn!(or);
    declare_bit_arith_bin_fn!(xor);

    fn is_equal<R: BitVecOps + ?Sized>(&self, rhs: &R) -> bool {
        debug_assert_eq!(
            self.width(),
            rhs.width(),
            "cannot compare bv<{}> with bv<{}>",
            self.width(),
            rhs.width()
        );
        debug_assert_eq!(self.words().len(), rhs.words().len());
        if self.words().len() == 1 {
            // specialized for 1-word case
            crate::bv::arithmetic::cmp_equal(self.words(), rhs.words())
        } else {
            crate::bv::arithmetic::cmp_equal(self.words(), rhs.words())
        }
    }

    fn is_not_equal<R: BitVecOps + ?Sized>(&self, rhs: &R) -> bool {
        !self.is_equal(rhs)
    }

    fn is_greater<R: BitVecOps + ?Sized>(&self, rhs: &R) -> bool {
        debug_assert_eq!(self.width(), rhs.width());
        debug_assert_eq!(self.words().len(), rhs.words().len());
        if self.words().len() == 1 {
            // specialized for 1-word case
            crate::bv::arithmetic::cmp_greater(&self.words()[0..1], &rhs.words()[0..1])
        } else {
            crate::bv::arithmetic::cmp_greater(self.words(), rhs.words())
        }
    }

    fn is_greater_or_equal<R: BitVecOps + ?Sized>(&self, rhs: &R) -> bool {
        debug_assert_eq!(self.width(), rhs.width());
        debug_assert_eq!(self.words().len(), rhs.words().len());
        if self.words().len() == 1 {
            // specialized for 1-word case
            crate::bv::arithmetic::cmp_greater_equal(&self.words()[0..1], &rhs.words()[0..1])
        } else {
            crate::bv::arithmetic::cmp_greater(self.words(), rhs.words())
        }
    }

    fn is_less<R: BitVecOps + ?Sized>(&self, rhs: &R) -> bool {
        // a < b <=> b > a
        rhs.is_greater(self)
    }

    fn is_less_or_equal<R: BitVecOps + ?Sized>(&self, rhs: &R) -> bool {
        // a <= b <=> b >= a
        rhs.is_greater_or_equal(self)
    }

    fn is_greater_signed<R: BitVecOps + ?Sized>(&self, rhs: &R) -> bool {
        debug_assert_eq!(self.width(), rhs.width());
        debug_assert_eq!(self.words().len(), rhs.words().len());
        if self.words().len() == 1 {
            // specialized for 1-word case
            crate::bv::arithmetic::cmp_greater_signed(
                &self.words()[0..1],
                &rhs.words()[0..1],
                self.width(),
            )
        } else {
            crate::bv::arithmetic::cmp_greater_signed(self.words(), rhs.words(), self.width())
        }
    }

    fn is_greater_or_equal_signed<R: BitVecOps + ?Sized>(&self, rhs: &R) -> bool {
        debug_assert_eq!(self.width(), rhs.width());
        debug_assert_eq!(self.words().len(), rhs.words().len());
        if self.words().len() == 1 {
            // specialized for 1-word case
            crate::bv::arithmetic::cmp_greater_equal_signed(
                &self.words()[0..1],
                &rhs.words()[0..1],
                self.width(),
            )
        } else {
            crate::bv::arithmetic::cmp_greater_equal_signed(self.words(), rhs.words(), self.width())
        }
    }

    fn is_less_signed<R: BitVecOps + ?Sized>(&self, rhs: &R) -> bool {
        // a < b <=> b > a
        rhs.is_greater_signed(self)
    }

    fn is_less_or_equal_signed<R: BitVecOps + ?Sized>(&self, rhs: &R) -> bool {
        // a <= b <=> b >= a
        rhs.is_greater_or_equal_signed(self)
    }

    fn slice(&self, msb: WidthInt, lsb: WidthInt) -> BitVecValue {
        debug_assert!(msb <= self.width());
        debug_assert!(msb >= lsb);
        let out_width = msb - lsb + 1;
        let mut out = BitVecValue::zero(out_width);
        if out_width <= Word::BITS {
            // specialized for 1-word case
            crate::bv::arithmetic::slice(&mut out.words_mut()[0..1], self.words(), msb, lsb);
        } else {
            crate::bv::arithmetic::slice(out.words_mut(), self.words(), msb, lsb);
        }
        out
    }

    fn is_bit_set(&self, pos: WidthInt) -> bool {
        crate::bv::arithmetic::is_bit_set(self.words(), pos)
    }

    fn sign_extend(&self, by: WidthInt) -> BitVecValue {
        let out_width = self.width() + by;
        let mut out = BitVecValue::zero(out_width);
        if out_width <= Word::BITS {
            // specialized for 1-word case
            crate::bv::arithmetic::sign_extend(
                &mut out.words_mut()[0..1],
                &self.words()[0..1],
                self.width(),
                out_width,
            );
        } else {
            crate::bv::arithmetic::sign_extend(
                out.words_mut(),
                self.words(),
                self.width(),
                out_width,
            );
        }
        out
    }

    fn zero_extend(&self, by: WidthInt) -> BitVecValue {
        let out_width = self.width() + by;
        let mut out = BitVecValue::zero(out_width);
        if out_width <= Word::BITS {
            // specialized for 1-word case
            crate::bv::arithmetic::zero_extend(&mut out.words_mut()[0..1], &self.words()[0..1]);
        } else {
            crate::bv::arithmetic::zero_extend(out.words_mut(), self.words());
        }
        out
    }

    fn not(&self) -> BitVecValue {
        let mut out = BitVecValue::zero(self.width());
        if self.words().len() <= 1 {
            // specialized for 1-word case
            crate::bv::arithmetic::not(
                &mut out.words_mut()[0..1],
                &self.words()[0..1],
                self.width(),
            );
        } else {
            crate::bv::arithmetic::not(out.words_mut(), self.words(), self.width());
        }
        out
    }

    fn negate(&self) -> BitVecValue {
        let mut out = BitVecValue::zero(self.width());
        if self.words().len() <= 1 {
            // specialized for 1-word case
            crate::bv::arithmetic::negate(
                &mut out.words_mut()[0..1],
                &self.words()[0..1],
                self.width(),
            );
        } else {
            crate::bv::arithmetic::negate(out.words_mut(), self.words(), self.width());
        }
        out
    }

    fn concat<R: BitVecOps + ?Sized>(&self, rhs: &R) -> BitVecValue {
        let out_width = self.width() + rhs.width();
        let mut out = BitVecValue::zero(out_width);
        if out_width <= Word::BITS {
            // specialized for 1-word case
            crate::bv::arithmetic::concat(
                &mut out.words_mut()[0..1],
                &self.words()[0..1],
                &rhs.words()[0..1],
                rhs.width(),
            );
        } else {
            crate::bv::arithmetic::concat(out.words_mut(), self.words(), rhs.words(), rhs.width());
        }
        out
    }
}

/// Operations over mutable bit-vector values.
pub trait BitVecMutOps: BitVecOps {
    fn words_mut(&mut self) -> &mut [Word];

    fn assign<'a>(&mut self, value: impl Into<BitVecValueRef<'a>>) {
        let value = value.into();
        debug_assert_eq!(self.width(), value.width());
        debug_assert_eq!(self.words_mut().len(), value.words().len());
        self.words_mut().copy_from_slice(value.words());
    }

    /// ensures that all unused bits in the most significant word are set to zero
    fn mask_msb(&mut self) {
        let width = self.width();
        crate::bv::arithmetic::mask_msb(self.words_mut(), width);
    }

    /// sets all bits to zero
    fn clear(&mut self) {
        self.words_mut().iter_mut().for_each(|w| {
            *w = 0;
        });
    }

    /// sets all bits to one
    fn assign_ones(&mut self) {
        // set everything to one and then mask off the msb
        self.words_mut().iter_mut().for_each(|w| {
            *w = Word::MAX;
        });
        self.mask_msb();
    }

    fn assign_from_u64(&mut self, value: u64) {
        debug_assert_eq!(Word::BITS, u64::BITS, "basic assumption of this function");
        // clear all words
        self.clear();
        // assign lsb
        self.words_mut()[0] = value;
        // make sure the value agrees with the bit width
        self.mask_msb();
        debug_assert_eq!(
            self.words()[0],
            value,
            "value {value} does not fit into {} bits",
            self.width()
        );
    }

    fn assign_from_u128(&mut self, value: u128) {
        debug_assert_eq!(
            DoubleWord::BITS,
            u128::BITS,
            "basic assumption of this function"
        );
        // clear all words
        self.clear();
        // assign values
        let words = double_word_to_words(value);
        self.words_mut()[0] = words[0];
        self.words_mut()[1] = words[1];
        // make sure the value agrees with the bit width
        self.mask_msb();
        debug_assert_eq!(
            self.words()[0],
            words[0],
            "value {value} does not fit into {} bits",
            self.width()
        );
        debug_assert_eq!(
            self.words()[1],
            words[1],
            "value {value} does not fit into {} bits",
            self.width()
        );
    }

    fn assign_from_i64(&mut self, value: i64) {
        debug_assert_eq!(Word::BITS, i64::BITS, "basic assumption of this function");
        let width = self.width();
        // clear all words
        self.clear();
        // assign lsb and sign extend if necessary
        if self.words().len() == 1 {
            let masked = value as u64 & crate::bv::arithmetic::mask(width);
            self.words_mut()[0] = masked;
        } else {
            crate::bv::arithmetic::sign_extend(self.words_mut(), &[value as u64], u64::BITS, width);
        };

        #[cfg(debug_assertions)]
        if self.is_negative() {
            if self.width() < Word::BITS {
                let extra_sign_bits =
                    crate::bv::arithmetic::mask(Word::BITS - self.width()) << self.width();
                let word_0 = self.words()[0];
                let word_0_with_bits = word_0 | extra_sign_bits;
                debug_assert_eq!(
                    word_0_with_bits,
                    value as u64,
                    "value {value} does not fit into {} bits",
                    self.width()
                );
            } else {
                debug_assert_eq!(
                    self.words()[0],
                    value as u64,
                    "value {value} does not fit into {} bits",
                    self.width()
                );
            }
        } else {
            debug_assert_eq!(
                self.words()[0],
                value as u64,
                "value {value} does not fit into {} bits",
                self.width()
            );
        }
    }

    fn assign_from_str_radix(&mut self, value: &str, radix: u32) -> Result<(), ParseIntError> {
        let width = self.width();
        crate::bv::io::strings::from_str_radix(value, radix, self.words_mut(), width)
    }

    fn set_bit(&mut self, pos: WidthInt) {
        crate::bv::arithmetic::set_bit(self.words_mut(), pos);
    }

    fn clear_bit(&mut self, pos: WidthInt) {
        crate::bv::arithmetic::clear_bit(self.words_mut(), pos);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn assign_bit_vector() {
        let mut dst = BitVecValue::zero(123);

        // owned values need to be passed as reference
        let src = BitVecValue::from_u64(1111111111, 123);
        dst.assign(&src);

        // bit vec value references are copy, so we can just pass them around as values
        let src = BitVecValue::from_u64(1111111111 * 2, 123);
        let src_ref = BitVecValueRef::from(&src);
        dst.assign(src_ref);

        // make sure src_ref was not moved
        let value = src_ref.to_u64().unwrap();
        assert_eq!(value, 1111111111 * 2);
    }

    #[test]
    fn test_is_all_ones() {
        let mut a = BitVecValue::ones(23);
        assert!(a.is_all_ones());
        a.clear_bit(20);
        assert!(!a.is_all_ones());

        let mut a = BitVecValue::ones(1345);
        assert!(a.is_all_ones());
        a.clear_bit(1000);
        assert!(!a.is_all_ones());
        a.set_bit(1000);
        assert!(a.is_all_ones());
    }

    #[test]
    fn test_is_one() {
        let mut a = BitVecValue::zero(23);
        assert!(!a.is_one());
        a.set_bit(0);
        assert!(a.is_one());
        a.set_bit(20);
        assert!(!a.is_one());
    }

    #[test]
    fn test_is_pow_2() {
        let mut a = BitVecValue::zero(1456);
        assert_eq!(a.is_pow_2(), None);
        a.set_bit(0);
        assert_eq!(a.is_pow_2(), Some(0));
        a.set_bit(20);
        assert_eq!(a.is_pow_2(), None);

        for bit in 0..a.width() {
            a.clear();
            a.set_bit(bit);
            assert_eq!(a.is_pow_2(), Some(bit));
        }
    }

    #[test]
    fn test_bit_set_intervals() {
        let a = BitVecValue::zero(1456);
        assert_eq!(a.bit_set_intervals(), []);
        let a = BitVecValue::from_u64(Word::MAX, Word::BITS);
        assert_eq!(a.bit_set_intervals(), [0..Word::BITS]);
        let mut a = BitVecValue::from_u64((1 as Word) << (Word::BITS - 1), 127);
        assert_eq!(a.bit_set_intervals(), [(Word::BITS - 1)..Word::BITS]);
        a.set_bit(Word::BITS);
        assert_eq!(a.bit_set_intervals(), [(Word::BITS - 1)..(Word::BITS + 1)]);
        a.clear_bit(Word::BITS - 1);
        assert_eq!(a.bit_set_intervals(), [Word::BITS..(Word::BITS + 1)]);
        a.set_bit(13);
        assert_eq!(
            a.bit_set_intervals(),
            [13..14, Word::BITS..(Word::BITS + 1)]
        );
        a.set_bit(14);
        assert_eq!(
            a.bit_set_intervals(),
            [13..15, Word::BITS..(Word::BITS + 1)]
        );
    }
}
