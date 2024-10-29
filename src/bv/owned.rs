// Copyright 2023-2024 The Regents of the University of California
// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>
use crate::bv::borrowed::BitVecValueRefImpl;
use crate::bv::io::strings::ParseIntError;
use crate::{BitVecMutOps, BitVecOps, BitVecValueRef, DoubleWord, WidthInt, Word};

/// Owned bit-vector value.
/// Note: Ord does not necessarily order by value.
#[derive(Clone, Hash, PartialOrd, Ord)]
#[cfg_attr(feature = "serde1", derive(serde::Serialize, serde::Deserialize))]
pub struct BitVecValue(pub(super) BitVecValueImpl);

/// Implementation enum for the owned bit-vector value.
/// We hide this inside a `pub struct` in order not to expose the individual enum entries to the
/// user.
#[derive(Clone, Hash, PartialOrd, Ord, Eq, PartialEq)]
#[cfg_attr(feature = "serde1", derive(serde::Serialize, serde::Deserialize))]
pub(super) enum BitVecValueImpl {
    Word(WidthInt, Word),
    Double(WidthInt, [Word; 2]),
    Big(WidthInt, Box<[Word]>),
}

impl BitVecValueImpl {
    /// Create a new value that fits into a single word
    const fn new_word(value: Word, width: WidthInt) -> Self {
        debug_assert!(width > 0 && width <= Word::BITS);
        Self::Word(width, value)
    }

    /// Create a new value of 64 < width <= 128
    const fn new_double_word(value: DoubleWord, width: WidthInt) -> Self {
        debug_assert!(width > Word::BITS && width <= DoubleWord::BITS);
        Self::Double(width, double_word_to_words(value))
    }

    /// Create a new value of width > 128. It will be initialized to all zeros.
    fn new_big_zero(width: WidthInt) -> Self {
        debug_assert!(width > DoubleWord::BITS);
        let num_words = width.div_ceil(Word::BITS) as usize;
        Self::Big(width, vec![0; num_words].into_boxed_slice())
    }
}

const fn double_word_to_words(value: DoubleWord) -> [Word; 2] {
    // lsb first, then msb
    [value as Word, (value >> Word::BITS) as Word]
}

/// divides width into three different classes
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub(crate) enum W {
    Word,
    Double,
    Big,
}

const MIN_DOUBLE_BITS: u32 = Word::BITS + 1;
impl From<WidthInt> for W {
    fn from(value: WidthInt) -> Self {
        match value {
            0 => panic!("zero bit is not supported!"),
            1..=Word::BITS => Self::Word,
            MIN_DOUBLE_BITS..=DoubleWord::BITS => Self::Double,
            _ => Self::Big,
        }
    }
}

const FALS_VALUE: BitVecValueImpl = BitVecValueImpl::new_word(0, 1);
const TRU_VALUE: BitVecValueImpl = BitVecValueImpl::new_word(1, 1);

impl BitVecValue {
    /// Parse a string of 1s and 0s. The width of the resulting value is the number of digits.
    pub fn from_bit_str(value: &str) -> Result<Self, ParseIntError> {
        let width = crate::bv::io::strings::determine_width_from_str_radix(value, 2);
        Self::from_str_radix(value, 2, width)
    }

    /// Parse a string of hex digits. The width of the resulting value is the number of digits times 4.
    pub fn from_hex_str(value: &str) -> Result<Self, ParseIntError> {
        let width = crate::bv::io::strings::determine_width_from_str_radix(value, 16);
        Self::from_str_radix(value, 16, width)
    }

    pub fn from_str_radix(value: &str, radix: u32, width: WidthInt) -> Result<Self, ParseIntError> {
        let mut out = Self::zero(width);
        out.assign_from_str_radix(value, radix)?;
        Ok(out)
    }

    pub fn from_u64(value: u64, width: WidthInt) -> Self {
        let mut out = Self::zero(width);
        out.assign_from_u64(value);
        out
    }

    pub fn from_i64(value: i64, width: WidthInt) -> Self {
        let mut out = Self::zero(width);
        out.assign_from_i64(value);
        out
    }

    pub fn from_bool(value: bool) -> Self {
        if value {
            Self::tru()
        } else {
            Self::fals()
        }
    }

    pub fn from_bytes_le(bytes: &[u8], width: WidthInt) -> Self {
        debug_assert!(width.div_ceil(u8::BITS) as usize >= bytes.len());
        match width.into() {
            W::Word => {
                let mut b = [0u8; Word::BITS.div_ceil(u8::BITS) as usize];
                b[0..bytes.len()].copy_from_slice(bytes);
                Self(BitVecValueImpl::new_word(Word::from_le_bytes(b), width))
            }
            W::Double => {
                let mut b = [0u8; DoubleWord::BITS.div_ceil(u8::BITS) as usize];
                b[0..bytes.len()].copy_from_slice(bytes);
                Self(BitVecValueImpl::new_double_word(
                    DoubleWord::from_le_bytes(b),
                    width,
                ))
            }
            W::Big => {
                let mut out = BitVecValue::zero(width);
                crate::bv::io::bytes::from_bytes_le(bytes, width, out.words_mut());
                out
            }
        }
    }

    pub fn zero(width: WidthInt) -> Self {
        Self(match width.into() {
            W::Word => BitVecValueImpl::new_word(0, width),
            W::Double => BitVecValueImpl::new_double_word(0, width),
            W::Big => BitVecValueImpl::new_big_zero(width),
        })
    }

    pub fn ones(width: WidthInt) -> Self {
        let mut out = Self::zero(width);
        out.assign_ones();
        out
    }

    #[inline]
    pub fn tru() -> Self {
        Self(TRU_VALUE.clone())
    }
    pub fn fals() -> Self {
        Self(FALS_VALUE.clone())
    }

    #[cfg(feature = "bigint")]
    pub fn from_big_int(value: &num_bigint::BigInt, bits: WidthInt) -> Self {
        let mut out = Self::zero(bits);
        crate::bv::io::bigint::from_big_int(value, bits, out.words_mut());
        out
    }

    #[cfg(feature = "bigint")]
    pub fn from_big_uint(value: &num_bigint::BigUint, bits: WidthInt) -> Self {
        let mut out = Self::zero(bits);
        crate::bv::io::bigint::from_big_uint(value, bits, out.words_mut());
        out
    }
}

impl<O: BitVecOps> PartialEq<O> for BitVecValue {
    fn eq(&self, other: &O) -> bool {
        if other.width() == self.width() {
            self.is_equal(other)
        } else {
            false
        }
    }
}

impl Eq for BitVecValue {}

impl From<bool> for BitVecValue {
    fn from(value: bool) -> Self {
        BitVecValue::from_bool(value)
    }
}

impl<'a> From<BitVecValueRef<'a>> for BitVecValue {
    fn from(value: BitVecValueRef<'a>) -> Self {
        Self(match value.0 {
            BitVecValueRefImpl::Word(width, value) => BitVecValueImpl::Word(width, value),
            BitVecValueRefImpl::Double(width, value) => BitVecValueImpl::Double(width, value),
            BitVecValueRefImpl::Big(width, value) => BitVecValueImpl::Big(width, Box::from(value)),
        })
    }
}

impl<V: BitVecOps> std::ops::Add<&V> for &BitVecValue {
    type Output = BitVecValue;

    fn add(self, rhs: &V) -> Self::Output {
        BitVecOps::add(self, rhs)
    }
}

impl<V: BitVecOps> std::ops::Sub<&V> for &BitVecValue {
    type Output = BitVecValue;

    fn sub(self, rhs: &V) -> Self::Output {
        BitVecOps::sub(self, rhs)
    }
}

impl std::fmt::Debug for BitVecValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "ValueOwned({})", self.to_bit_str())
    }
}

#[cfg(feature = "bigint")]
impl From<&num_bigint::BigInt> for BitVecValue {
    fn from(value: &num_bigint::BigInt) -> Self {
        let bits = crate::bv::io::bigint::count_big_int_bits(value);
        Self::from_big_int(value, bits)
    }
}

#[cfg(feature = "bigint")]
impl From<&num_bigint::BigUint> for BitVecValue {
    fn from(value: &num_bigint::BigUint) -> Self {
        let bits = crate::bv::io::bigint::count_big_uint_bits(value);
        Self::from_big_uint(value, bits)
    }
}

impl BitVecOps for BitVecValue {
    fn width(&self) -> WidthInt {
        match &self.0 {
            BitVecValueImpl::Word(w, _) => *w,
            BitVecValueImpl::Double(w, _) => *w,
            BitVecValueImpl::Big(w, _) => *w,
        }
    }

    fn words(&self) -> &[Word] {
        match &self.0 {
            BitVecValueImpl::Word(_, value) => std::slice::from_ref(value),
            BitVecValueImpl::Double(_, value) => value.as_slice(),
            BitVecValueImpl::Big(_, value) => value.as_ref(),
        }
    }
}

impl BitVecMutOps for BitVecValue {
    fn words_mut(&mut self) -> &mut [Word] {
        match &mut self.0 {
            BitVecValueImpl::Word(_, value) => std::slice::from_mut(value),
            BitVecValueImpl::Double(_, value) => value.as_mut_slice(),
            BitVecValueImpl::Big(_, value) => value.as_mut(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn type_size() {
        // by default we use 32 bits to represent the width
        assert_eq!(std::mem::size_of::<WidthInt>(), 4);
        // we use a 64-bit word size
        assert_eq!(std::mem::size_of::<Word>(), 8);
        assert_eq!(std::mem::size_of::<[Word; 2]>(), 2 * 8);
        assert_eq!(std::mem::size_of::<Box<[Word]>>(), 2 * 8);
        // width + value + padding
        assert_eq!(std::mem::size_of::<BitVecValueImpl>(), 3 * 8);
    }

    #[test]
    fn test_tru_fals() {
        assert!(BitVecValue::tru().to_bool().unwrap());
        assert!(!BitVecValue::fals().to_bool().unwrap());
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic] // debug assertions won't allow oversize values
    fn test_from_u64_in_debug_mode() {
        let _ = BitVecValue::from_u64(16, 4);
    }

    #[test]
    #[cfg(not(debug_assertions))]
    fn test_from_u64_in_release_mode() {
        // in release mode the upper bits just get cleared
        assert_eq!(
            BitVecValue::from_u64(16, 4).to_u64().unwrap(),
            0,
            "should mask the top bits"
        );
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic] // debug assertions won't allow oversize values
    fn test_from_i64_in_debug_mode() {
        let _ = BitVecValue::from_i64(-8, 4); // this should be OK
        let _ = BitVecValue::from_i64(7, 4); // this should be OK
        let _ = BitVecValue::from_i64(-9, 4); // this should fail
    }

    #[test]
    #[cfg(not(debug_assertions))]
    fn test_from_i64_in_release_mode() {
        // in release mode the upper bits just get cleared
        assert_eq!(
            BitVecValue::from_i64(-9, 4).to_u64().unwrap(),
            7,
            "should mask the top bits"
        );
    }

    #[test]
    fn test_ones() {
        let a = BitVecValue::ones(3);
        assert_eq!(a.words(), &[0b111]);
        let b = BitVecValue::ones(3 + Word::BITS);
        assert_eq!(b.words(), &[Word::MAX, 0b111]);
    }
}
