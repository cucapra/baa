// Copyright 2023-2024 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>
//
// Borrowed bit-vector and array values.

use crate::bv::owned::BitVecValueImpl;
use crate::{BitVecMutOps, BitVecOps, BitVecValue, WidthInt, Word};
use std::borrow::Borrow;

/// Bit-vector value that does not own its storage.
#[derive(Clone, Copy, Hash)]
pub struct BitVecValueRef<'a>(pub(super) BitVecValueRefImpl<'a>);

#[derive(Clone, Copy, Hash)]
pub(super) enum BitVecValueRefImpl<'a> {
    Word(WidthInt, Word),
    Double(WidthInt, [Word; 2]),
    Big(WidthInt, &'a [Word]),
}

impl<'a> BitVecValueRef<'a> {
    pub(crate) fn new(words: &'a [Word], width: WidthInt) -> Self {
        debug_assert_eq!(width.div_ceil(Word::BITS) as usize, words.len());
        match words {
            [] => panic!("0-bit not allowed!"),
            [one] => Self(BitVecValueRefImpl::Word(width, *one)),
            [lsb, msb] => Self(BitVecValueRefImpl::Double(width, [*lsb, *msb])),
            more => Self(BitVecValueRefImpl::Big(width, more)),
        }
    }
}

impl<'a> From<&'a BitVecValue> for BitVecValueRef<'a> {
    fn from(value: &'a BitVecValue) -> Self {
        Self(match &value.0 {
            BitVecValueImpl::Word(width, value) => BitVecValueRefImpl::Word(*width, *value),
            BitVecValueImpl::Double(width, value) => BitVecValueRefImpl::Double(*width, *value),
            BitVecValueImpl::Big(width, value) => BitVecValueRefImpl::Big(*width, value),
        })
    }
}

impl std::fmt::Debug for BitVecValueRef<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "BitVecValueRef({})", self.to_bit_str())
    }
}

impl<O: BitVecOps> PartialEq<O> for BitVecValueRef<'_> {
    fn eq(&self, other: &O) -> bool {
        if other.width() == self.width() {
            self.is_equal(other)
        } else {
            false
        }
    }
}

impl Eq for BitVecValueRef<'_> {}

pub struct BitVecValueMutRef<'a> {
    pub(crate) width: WidthInt,
    pub(crate) words: &'a mut [Word],
}

impl<'a> BitVecValueMutRef<'a> {
    pub(crate) fn new(width: WidthInt, words: &'a mut [Word]) -> Self {
        Self { width, words }
    }
}

impl<'a> From<&'a mut BitVecValue> for BitVecValueMutRef<'a> {
    fn from(value: &'a mut BitVecValue) -> Self {
        Self::new(value.width(), value.words_mut())
    }
}
impl std::fmt::Debug for BitVecValueMutRef<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "BitVecValueMutRef({})", self.to_bit_str())
    }
}

impl BitVecOps for BitVecValueRef<'_> {
    fn width(&self) -> WidthInt {
        match &self.0 {
            BitVecValueRefImpl::Word(w, _) => *w,
            BitVecValueRefImpl::Double(w, _) => *w,
            BitVecValueRefImpl::Big(w, _) => *w,
        }
    }

    fn words(&self) -> &[Word] {
        match &self.0 {
            BitVecValueRefImpl::Word(_, value) => std::slice::from_ref(value),
            BitVecValueRefImpl::Double(_, value) => value.as_slice(),
            BitVecValueRefImpl::Big(_, value) => value.as_ref(),
        }
    }
}

impl BitVecOps for BitVecValueMutRef<'_> {
    fn width(&self) -> WidthInt {
        self.width
    }

    fn words(&self) -> &[Word] {
        self.words
    }
}

impl BitVecMutOps for BitVecValueMutRef<'_> {
    fn words_mut(&mut self) -> &mut [Word] {
        self.words
    }
}

impl<'a> Borrow<BitVecValueRef<'a>> for BitVecValue {
    fn borrow(&self) -> &BitVecValueRef<'a> {
        todo!()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::BitVecValue;
    use proptest::prelude::*;
    use std::borrow::Borrow;
    use std::hash::{DefaultHasher, Hash, Hasher};

    /// Signature is copied from HashTable::get
    fn get_hash<Q: ?Sized>(key: &Q) -> u64
    where
        BitVecValue: Borrow<Q>,
        Q: Hash + Eq,
    {
        let mut hasher = DefaultHasher::new();
        key.borrow().hash(&mut hasher);
        hasher.finish()
    }

    fn check_hash(value: BitVecValue) {
        let value_hash = get_hash(&value);
        let re = BitVecValueRef::from(&value);
        let re_hash = get_hash(&re);
        assert_eq!(value, re);
        assert_eq!(value_hash, re_hash);
    }

    #[test]
    fn borrowed_hash() {
        check_hash(BitVecValue::zero(1));
        check_hash(BitVecValue::zero(1000000));
        check_hash(BitVecValue::from_bit_str("11").unwrap());
    }

    fn bit_str_arg() -> impl Strategy<Value = String> {
        "[01]+"
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(2000))]

        #[test]
        fn test_is_neg(a in bit_str_arg()) {
            let a = BitVecValue::from_bit_str(&a).unwrap();
            check_hash(a);
        }
    }
}
