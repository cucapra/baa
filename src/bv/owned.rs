// Copyright 2023-2024 The Regents of the University of California
// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::bv::io::strings::ParseIntError;
use crate::{BitVecMutOps, BitVecOps, BitVecValueRef, WidthInt, Word};

pub(crate) type ValueVec = Vec<Word>;

/// Owned bit-vector value.
/// Note: Ord does not necessarily order by value.
#[derive(Clone, Hash, Ord, PartialOrd)]
#[cfg_attr(feature = "serde1", derive(serde::Serialize, serde::Deserialize))]
pub struct BitVecValue {
    width: WidthInt,
    words: ValueVec,
}

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

    pub fn from_bytes_le(bytes: &[u8], bits: WidthInt) -> Self {
        let mut words = value_vec_zeros(bits);
        crate::bv::io::bytes::from_bytes_le(bytes, bits, words.as_mut());
        Self { width: bits, words }
    }

    pub fn zero(width: WidthInt) -> Self {
        let words = value_vec_zeros(width);
        Self { width, words }
    }

    pub fn ones(width: WidthInt) -> Self {
        let mut out = Self::zero(width);
        out.assign_ones();
        out
    }

    pub fn tru() -> Self {
        Self::from_u64(1, 1)
    }
    pub fn fals() -> Self {
        Self::from_u64(0, 1)
    }

    #[cfg(feature = "bigint")]
    pub fn from_big_int(value: &num_bigint::BigInt, bits: WidthInt) -> Self {
        let mut words = value_vec_zeros(bits);
        crate::bv::io::bigint::from_big_int(value, bits, &mut words);
        Self { width: bits, words }
    }

    #[cfg(feature = "bigint")]
    pub fn from_big_uint(value: &num_bigint::BigUint, bits: WidthInt) -> Self {
        let mut words = value_vec_zeros(bits);
        crate::bv::io::bigint::from_big_uint(value, bits, &mut words);
        Self { width: bits, words }
    }

    /// Raw constructor for internal use.
    pub(crate) fn new(width: WidthInt, words: ValueVec) -> Self {
        Self { width, words }
    }
}

impl From<bool> for BitVecValue {
    fn from(value: bool) -> Self {
        BitVecValue::from_bool(value)
    }
}

impl<'a> From<BitVecValueRef<'a>> for BitVecValue {
    fn from(value: BitVecValueRef<'a>) -> Self {
        Self::new(value.width, Vec::from(value.words))
    }
}

#[inline]
pub(crate) fn value_vec_zeros(width: WidthInt) -> ValueVec {
    vec![0; width.div_ceil(Word::BITS) as usize]
}

impl<V: BitVecOps> PartialEq<V> for BitVecValue {
    fn eq(&self, other: &V) -> bool {
        debug_assert!(other.width() != self.width || other.words().len() == self.words.len());
        other.width() == self.width && other.words() == self.words.as_slice()
    }
}

impl Eq for BitVecValue {}

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
        self.width
    }

    fn words(&self) -> &[Word] {
        &self.words
    }
}

impl BitVecMutOps for BitVecValue {
    fn words_mut(&mut self) -> &mut [Word] {
        &mut self.words
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
        assert_eq!(std::mem::size_of::<[Word; 2]>(), 16);
        // 8 bytes (usize) for the capacity, 8 byte pointer + 8 byte allocation size
        assert_eq!(std::mem::size_of::<ValueVec>(), 8 + 8 + 8);
        assert_eq!(
            std::mem::size_of::<ValueVec>(),
            std::mem::size_of::<Vec<Word>>()
        );
        // width + value + padding
        assert_eq!(std::mem::size_of::<BitVecValue>(), 4 * 8);
        assert_eq!(
            std::mem::size_of::<BitVecValue>(),
            std::mem::size_of::<ValueVec>() + std::mem::size_of::<WidthInt>() + 4
        );
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
        assert_eq!(a.words.as_slice(), &[0b111]);
        let b = BitVecValue::ones(3 + Word::BITS);
        assert_eq!(b.words.as_slice(), &[Word::MAX, 0b111]);
    }
}
