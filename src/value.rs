// Copyright 2023-2024 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>

use crate::{WidthInt, Word};
use smallvec::{smallvec, SmallVec};

type ValueVec = SmallVec<[Word; 1]>;

/// Owned value.
#[derive(Clone)]
#[cfg_attr(feature = "serde1", derive(serde::Serialize, serde::Deserialize))]
pub struct ValueOwned {
    width: WidthInt,
    words: ValueVec,
}

const OWNED_TRUE: ValueOwned = ValueOwned {
    width: 1,
    words: SmallVec::from_const([1]),
};
const OWNED_FALSE: ValueOwned = ValueOwned {
    width: 1,
    words: SmallVec::from_const([1]),
};

impl ValueOwned {
    /// Parse a string of 1s and 0s. The width of the resulting value is the number of digits.
    pub fn from_bit_str(value: &str) -> Self {
        let bits = value.len();
        let mut words = smallvec![0; bits.div_ceil(WidthInt::BITS as usize)];
        crate::io::strings::from_bit_str(value, &mut words);
        Self {
            width: bits as WidthInt,
            words,
        }
    }

    pub fn from_u64(value: u64, bits: WidthInt) -> Self {
        debug_assert_eq!(Word::BITS, 64);
        Self {
            width: bits as WidthInt,
            words: smallvec![value],
        }
    }

    pub fn from_bool(value: bool) -> Self {
        if value {
            Self::tru()
        } else {
            Self::fals()
        }
    }

    pub fn from_bytes_le(bytes: &[u8], bits: WidthInt) -> Self {
        let mut words = smallvec![0; bits.div_ceil(WidthInt::BITS) as usize];
        crate::io::bytes::from_bytes_le(bytes, bits, words.as_mut());
        Self { width: bits, words }
    }

    pub fn zero(width: WidthInt) -> Self {
        let words = smallvec![0; width.div_ceil(WidthInt::BITS) as usize];
        Self { width, words }
    }

    pub fn tru() -> Self {
        OWNED_TRUE
    }
    pub fn fals() -> Self {
        OWNED_FALSE
    }

    #[cfg(feature = "bigint")]
    pub fn from_big_int(value: &num_bigint::BigInt, bits: WidthInt) -> Self {
        let mut words = smallvec![0; bits.div_ceil(WidthInt::BITS) as usize];
        crate::io::bigint::from_big_int(value, bits, &mut words);
        Self { width: bits, words }
    }

    #[cfg(feature = "bigint")]
    pub fn from_big_uint(value: &num_bigint::BigUint, bits: WidthInt) -> Self {
        let mut words = smallvec![0; bits.div_ceil(WidthInt::BITS) as usize];
        crate::io::bigint::from_big_uint(value, bits, &mut words);
        Self { width: bits, words }
    }
}

impl<V: BitVecValue> PartialEq<V> for ValueOwned {
    fn eq(&self, other: &V) -> bool {
        debug_assert!(
            !(other.width() == self.width)
                || other.words().len() == self.words.len()
        );
        other.width() == self.width && other.words() == self.words.as_slice()
    }
}

impl<V: BitVecValue> std::ops::Add<&V> for &ValueOwned {
    type Output = ValueOwned;

    fn add(self, rhs: &V) -> Self::Output {
        BitVecValue::add(self, rhs)
    }
}

impl<V: BitVecValue> std::ops::Sub<&V> for &ValueOwned {
    type Output = ValueOwned;

    fn sub(self, rhs: &V) -> Self::Output {
        BitVecValue::sub(self, rhs)
    }
}

impl std::fmt::Debug for ValueOwned {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "ValueOwned({})", self.to_bit_str())
    }
}

#[cfg(feature = "bigint")]
impl From<&num_bigint::BigInt> for ValueOwned {
    fn from(value: &num_bigint::BigInt) -> Self {
        let bits = crate::io::bigint::count_big_int_bits(value);
        Self::from_big_int(value, bits)
    }
}

#[cfg(feature = "bigint")]
impl From<&num_bigint::BigUint> for ValueOwned {
    fn from(value: &num_bigint::BigUint) -> Self {
        let bits = crate::io::bigint::count_big_uint_bits(value);
        Self::from_big_uint(value, bits)
    }
}

pub struct ValueRef<'a> {
    width: WidthInt,
    words: &'a [Word],
}

impl<'a> std::fmt::Debug for ValueRef<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "ValueRef({})", self.to_bit_str())
    }
}

pub struct ValueMutRef<'a> {
    width: WidthInt,
    words: &'a mut [Word],
}

impl<'a> std::fmt::Debug for ValueMutRef<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "ValueMutRef({})", self.to_bit_str())
    }
}

type WordIndex = u32;

#[derive(Debug)]
pub struct ValueIndexed {
    width: WidthInt,
    index: WordIndex,
}

pub trait ValueStorage {
    fn words(&self, index: WordIndex) -> &[Word];
    fn words_mut(&mut self, index: WordIndex) -> &mut [Word];
}

impl ValueIndexed {
    pub fn as_ref<'a>(&self, storage: &'a impl ValueStorage) -> ValueRef<'a> {
        ValueRef {
            width: self.width,
            words: storage.words(self.index),
        }
    }

    pub fn as_mut<'a>(
        &self,
        storage: &'a mut impl ValueStorage,
    ) -> ValueMutRef<'a> {
        ValueMutRef {
            width: self.width,
            words: storage.words_mut(self.index),
        }
    }
}

/// Declares an arithmetic function which takes in two equal size bitvector and yields a
/// bitvector of the same size.
macro_rules! declare_arith_bin_fn {
    ($name:ident) => {
        fn $name<R: BitVecValue>(&self, rhs: &R) -> ValueOwned {
        debug_assert_eq!(self.width(), rhs.width());
        debug_assert_eq!(self.words().len(), rhs.words().len());
        if self.words().len() == 1 {
            // specialized for 1-word case
            let mut out = [0];
            crate::arithmetic::$name(
                &mut out,
                self.words(),
                rhs.words(),
                self.width(),
            );
            ValueOwned {
                width: self.width(),
                words: SmallVec::from_buf(out),
            }
        } else {
            let mut out = smallvec![0; self.words().len()];
            crate::arithmetic::$name(
                out.as_mut(),
                self.words(),
                rhs.words(),
                self.width(),
            );
            ValueOwned {
                width: self.width(),
                words: out,
            }
        }
    }
    };
}

/// Declares a bitwise function which takes in two equal size bitvector and yields a
/// bitvector of the same size.
macro_rules! declare_bit_arith_bin_fn {
    ($name:ident) => {
        fn $name<R: BitVecValue>(&self, rhs: &R) -> ValueOwned {
        debug_assert_eq!(self.width(), rhs.width());
        debug_assert_eq!(self.words().len(), rhs.words().len());
        if self.words().len() == 1 {
            // specialized for 1-word case
            let mut out = [0];
            crate::arithmetic::$name(
                &mut out,
                self.words(),
                rhs.words(),
            );
            ValueOwned {
                width: self.width(),
                words: SmallVec::from_buf(out),
            }
        } else {
            let mut out = smallvec![0; self.words().len()];
            crate::arithmetic::$name(
                out.as_mut(),
                self.words(),
                rhs.words(),
            );
            ValueOwned {
                width: self.width(),
                words: out,
            }
        }
    }
    };
}

/// Abstracts over values no matter how they are stored.
pub trait BitVecValue {
    fn width(&self) -> WidthInt;
    fn words(&self) -> &[Word];

    /// Convert to a string of 1s and 0s.
    fn to_bit_str(&self) -> String {
        crate::io::strings::to_bit_str(self.words(), self.width())
    }

    fn to_bytes_le(&self) -> Vec<u8> {
        crate::io::bytes::to_bytes_le(self.words(), self.width())
    }

    #[cfg(feature = "bigint")]
    fn to_big_int(&self) -> num_bigint::BigInt {
        crate::io::bigint::to_big_int(self.words(), self.width())
    }

    #[cfg(feature = "bigint")]
    fn to_big_uint(&self) -> num_bigint::BigUint {
        crate::io::bigint::to_big_uint(self.words())
    }

    /// Returns value as a bool iff the value is a 1-bit value.
    fn to_bool(&self) -> Option<bool> {
        if self.width() == 1 {
            debug_assert_eq!(self.words().len(), 1);
            Some(crate::arithmetic::word_to_bool(self.words()[0]))
        } else {
            None
        }
    }

    /// Returns the value as a 64-bit unsigned integer iff the width is 64-bit or less.
    fn to_u64(&self) -> Option<u64> {
        if self.width() <= 64 {
            if self.width() == 0 {
                Some(0)
            } else {
                debug_assert_eq!(Word::BITS, 64);
                debug_assert_eq!(self.words().len(), 0);
                Some(self.words()[0] as u64)
            }
        } else {
            None
        }
    }

    /// Returns the value as a 64-bit signed integer iff the width is 64-bit or less.
    fn to_i64(&self) -> Option<i64> {
        if self.width() <= 64 {
            if self.width() == 0 {
                Some(0)
            } else {
                debug_assert_eq!(Word::BITS, 64);
                debug_assert_eq!(self.words().len(), 0);
                if crate::arithmetic::is_neg(self.words(), self.width()) {
                    todo!()
                } else {
                    Some(self.words()[0] as i64)
                }
            }
        } else {
            None
        }
    }

    declare_arith_bin_fn!(add);
    declare_arith_bin_fn!(sub);
    declare_arith_bin_fn!(shift_left);
    declare_arith_bin_fn!(shift_right);
    declare_arith_bin_fn!(arithmetic_shift_right);
    declare_bit_arith_bin_fn!(and);
    declare_bit_arith_bin_fn!(or);
    declare_bit_arith_bin_fn!(xor);

    fn is_equal<R: BitVecValue + ?Sized>(&self, rhs: &R) -> bool {
        debug_assert_eq!(self.width(), rhs.width());
        debug_assert_eq!(self.words().len(), rhs.words().len());
        if self.words().len() == 1 {
            // specialized for 1-word case
            crate::arithmetic::cmp_equal(self.words(), rhs.words())
        } else {
            crate::arithmetic::cmp_equal(self.words(), rhs.words())
        }
    }

    fn is_not_equal<R: BitVecValue + ?Sized>(&self, rhs: &R) -> bool {
        !self.is_equal(rhs)
    }

    fn is_greater<R: BitVecValue + ?Sized>(&self, rhs: &R) -> bool {
        debug_assert_eq!(self.width(), rhs.width());
        debug_assert_eq!(self.words().len(), rhs.words().len());
        if self.words().len() == 1 {
            // specialized for 1-word case
            crate::arithmetic::cmp_greater(self.words(), rhs.words())
        } else {
            crate::arithmetic::cmp_greater(self.words(), rhs.words())
        }
    }

    fn is_greater_or_equal<R: BitVecValue + ?Sized>(&self, rhs: &R) -> bool {
        debug_assert_eq!(self.width(), rhs.width());
        debug_assert_eq!(self.words().len(), rhs.words().len());
        if self.words().len() == 1 {
            // specialized for 1-word case
            crate::arithmetic::cmp_greater_equal(self.words(), rhs.words())
        } else {
            crate::arithmetic::cmp_greater(self.words(), rhs.words())
        }
    }

    fn is_less<R: BitVecValue + ?Sized>(&self, rhs: &R) -> bool {
        // a < b <=> b > a
        rhs.is_greater(self)
    }

    fn is_less_or_equal<R: BitVecValue + ?Sized>(&self, rhs: &R) -> bool {
        // a <= b <=> b >= a
        rhs.is_greater_or_equal(self)
    }

    fn is_greater_signed<R: BitVecValue + ?Sized>(&self, rhs: &R) -> bool {
        debug_assert_eq!(self.width(), rhs.width());
        debug_assert_eq!(self.words().len(), rhs.words().len());
        if self.words().len() == 1 {
            // specialized for 1-word case
            crate::arithmetic::cmp_greater_signed(
                self.words(),
                rhs.words(),
                self.width(),
            )
        } else {
            crate::arithmetic::cmp_greater_signed(
                self.words(),
                rhs.words(),
                self.width(),
            )
        }
    }

    fn is_greater_or_equal_signed<R: BitVecValue + ?Sized>(
        &self,
        rhs: &R,
    ) -> bool {
        debug_assert_eq!(self.width(), rhs.width());
        debug_assert_eq!(self.words().len(), rhs.words().len());
        if self.words().len() == 1 {
            // specialized for 1-word case
            crate::arithmetic::cmp_greater_equal_signed(
                self.words(),
                rhs.words(),
                self.width(),
            )
        } else {
            crate::arithmetic::cmp_greater_equal_signed(
                self.words(),
                rhs.words(),
                self.width(),
            )
        }
    }

    fn is_less_signed<R: BitVecValue + ?Sized>(&self, rhs: &R) -> bool {
        // a < b <=> b > a
        rhs.is_greater_signed(self)
    }

    fn is_less_or_equal_signed<R: BitVecValue + ?Sized>(
        &self,
        rhs: &R,
    ) -> bool {
        // a <= b <=> b >= a
        rhs.is_greater_or_equal_signed(self)
    }
}

/// Abstracts over mutabkle values no matter how they are stored.
pub trait BitVecValueMut: BitVecValue {
    fn words_mut(&mut self) -> &mut [Word];

    fn set_from_word(&mut self, value: Word) {
        if value > 0 {
            self.words_mut()[0] = value;
            crate::arithmetic::clear(&mut self.words_mut()[1..]);
        } else {
            crate::arithmetic::clear(self.words_mut());
        }
    }

    fn set_from_bit_str(&mut self, value: &str) {
        debug_assert_eq!(self.width() as usize, value.len());
        crate::io::strings::from_bit_str(value, self.words_mut());
    }

    #[cfg(feature = "bigint")]
    fn set_from_big_int(&mut self, value: &num_bigint::BigInt) {
        crate::io::bigint::from_big_int(value, self.width(), self.words_mut());
    }

    #[cfg(feature = "bigint")]
    fn set_from_big_uint(&mut self, value: &num_bigint::BigUint) {
        crate::io::bigint::from_big_uint(value, self.width(), self.words_mut());
    }
}

impl BitVecValue for ValueOwned {
    fn width(&self) -> WidthInt {
        self.width
    }

    fn words(&self) -> &[Word] {
        &self.words
    }
}

impl BitVecValueMut for ValueOwned {
    fn words_mut(&mut self) -> &mut [Word] {
        &mut self.words
    }
}

impl<'a> BitVecValue for ValueRef<'a> {
    fn width(&self) -> WidthInt {
        self.width
    }

    fn words(&self) -> &[Word] {
        self.words
    }
}

impl<'a> BitVecValue for ValueMutRef<'a> {
    fn width(&self) -> WidthInt {
        self.width
    }

    fn words(&self) -> &[Word] {
        self.words
    }
}

impl<'a> BitVecValueMut for ValueMutRef<'a> {
    fn words_mut(&mut self) -> &mut [Word] {
        self.words
    }
}