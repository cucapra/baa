// Copyright 2023-2024 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>
//
// Access a slice of `Word` as a bit-vector.

use crate::bv::borrowed::{BitVecValueMutRef, BitVecValueRef};
use crate::{BitVecOps, WidthInt, Word};
use std::borrow::Borrow;
use std::collections::HashMap;
use std::fmt::{Debug, Formatter};

type WordIndex = u32;

/// Index of a bit-vector value in a shared value store.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct BitVecValueIndex {
    width: WidthInt,
    pub(crate) index: WordIndex,
}

impl BitVecValueIndex {
    #[inline]
    pub fn new(index: WordIndex, width: WidthInt) -> Self {
        Self { index, width }
    }

    #[inline]
    pub fn words(&self) -> usize {
        self.width.div_ceil(Word::BITS) as usize
    }

    #[inline]
    pub fn to_range(&self) -> std::ops::Range<usize> {
        let start = self.index as usize;
        let end = start + self.words();
        start..end
    }

    #[inline]
    pub fn width(&self) -> WidthInt {
        self.width
    }
}

/// Implemented by a value stores to convert indices into value references.
pub trait IndexToRef<I, O> {
    fn get_ref(self, index: I) -> O;
}

impl<'a, I> IndexToRef<I, BitVecValueRef<'a>> for &'a [Word]
where
    I: Borrow<BitVecValueIndex>,
{
    fn get_ref(self, index: I) -> BitVecValueRef<'a> {
        BitVecValueRef {
            width: index.borrow().width,
            words: &self[index.borrow().to_range()],
        }
    }
}

impl<'a, I> IndexToRef<(I, I), (BitVecValueRef<'a>, BitVecValueRef<'a>)> for &'a [Word]
where
    I: Borrow<BitVecValueIndex>,
{
    fn get_ref(self, (a, b): (I, I)) -> (BitVecValueRef<'a>, BitVecValueRef<'a>) {
        (
            BitVecValueRef {
                width: a.borrow().width,
                words: &self[a.borrow().to_range()],
            },
            BitVecValueRef {
                width: b.borrow().width,
                words: &self[b.borrow().to_range()],
            },
        )
    }
}

/// Implemented by value stores to convert indices into mutable value references.
pub trait IndexToMutRef<I, O> {
    fn get_mut_ref(self, index: I) -> O;
}

impl<'a, I> IndexToMutRef<I, BitVecValueMutRef<'a>> for &'a mut [Word]
where
    I: Borrow<BitVecValueIndex>,
{
    fn get_mut_ref(self, index: I) -> BitVecValueMutRef<'a> {
        BitVecValueMutRef {
            width: index.borrow().width,
            words: &mut self[index.borrow().to_range()],
        }
    }
}

impl<'a, I> IndexToMutRef<(I, I), (BitVecValueMutRef<'a>, BitVecValueRef<'a>)> for &'a mut [Word]
where
    I: Borrow<BitVecValueIndex>,
{
    fn get_mut_ref(self, (a, b): (I, I)) -> (BitVecValueMutRef<'a>, BitVecValueRef<'a>) {
        let (a_words, b_words) = split_borrow_1(self, a.borrow().to_range(), b.borrow().to_range());

        (
            BitVecValueMutRef {
                width: a.borrow().width,
                words: a_words,
            },
            BitVecValueRef {
                width: b.borrow().width,
                words: b_words,
            },
        )
    }
}

impl<'a, I>
    IndexToMutRef<
        (I, I, I),
        (
            BitVecValueMutRef<'a>,
            BitVecValueRef<'a>,
            BitVecValueRef<'a>,
        ),
    > for &'a mut [Word]
where
    I: Borrow<BitVecValueIndex>,
{
    fn get_mut_ref(
        self,
        (a, b, c): (I, I, I),
    ) -> (
        BitVecValueMutRef<'a>,
        BitVecValueRef<'a>,
        BitVecValueRef<'a>,
    ) {
        let (a_words, b_words, c_words) = split_borrow_2(
            self,
            a.borrow().to_range(),
            b.borrow().to_range(),
            c.borrow().to_range(),
        );

        (
            BitVecValueMutRef {
                width: a.borrow().width,
                words: a_words,
            },
            BitVecValueRef {
                width: b.borrow().width,
                words: b_words,
            },
            BitVecValueRef {
                width: c.borrow().width,
                words: c_words,
            },
        )
    }
}

#[inline]
pub(crate) fn split_borrow_1(
    data: &mut [Word],
    dst: std::ops::Range<usize>,
    src: std::ops::Range<usize>,
) -> (&mut [Word], &[Word]) {
    let (before_dst, after_dst_start) = data.split_at_mut(dst.start);
    let (dst_words, after_dst) = after_dst_start.split_at_mut(dst.end - dst.start);
    let after_dst_offset = dst.end;
    let src_words = if src.start >= after_dst_offset {
        &after_dst[move_range(src, after_dst_offset)]
    } else {
        &before_dst[src]
    };
    (dst_words, src_words)
}

#[inline]
fn move_range(rng: std::ops::Range<usize>, offset: usize) -> std::ops::Range<usize> {
    std::ops::Range {
        start: rng.start - offset,
        end: rng.end - offset,
    }
}

#[inline]
fn split_borrow_2(
    data: &mut [Word],
    dst: std::ops::Range<usize>,
    src_a: std::ops::Range<usize>,
    src_b: std::ops::Range<usize>,
) -> (&mut [Word], &[Word], &[Word]) {
    let (before_dst, after_dst_start) = data.split_at_mut(dst.start);
    let (dst_words, after_dst) = after_dst_start.split_at_mut(dst.end - dst.start);
    let after_dst_offset = dst.end;
    let a_words = if src_a.start >= after_dst_offset {
        &after_dst[move_range(src_a, after_dst_offset)]
    } else {
        &before_dst[src_a]
    };
    let b_words = if src_b.start >= after_dst_offset {
        &after_dst[move_range(src_b, after_dst_offset)]
    } else {
        &before_dst[src_b]
    };
    (dst_words, a_words, b_words)
}

/// Ensures that each bit vector value gets a unique index. And each combination of value and
/// width will get a unique BitVecValueIndex
#[derive(Clone)]
pub struct ValueInterner {
    words: Vec<Word>,
    small: HashMap<Word, WordIndex>,
    large: HashMap<Box<[Word]>, WordIndex>,
}

impl Default for ValueInterner {
    fn default() -> Self {
        Self::new()
    }
}

impl Debug for ValueInterner {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "ValueInterner({} small, {} large)",
            self.small.len(),
            self.large.len()
        )
    }
}

impl ValueInterner {
    pub fn new() -> Self {
        // initialize with some important constants
        let words = vec![0, 1, 2, 3, 4, 5, 6, 7];
        let small = HashMap::new();
        let large = HashMap::new();
        Self {
            words,
            small,
            large,
        }
    }

    pub fn is_zero<I: Borrow<BitVecValueIndex>>(index: I) -> bool {
        index.borrow().index == 0
    }

    pub fn is_one<I: Borrow<BitVecValueIndex>>(index: I) -> bool {
        index.borrow().index == 1
    }

    pub fn get_index<'a>(&mut self, value: impl Into<BitVecValueRef<'a>>) -> BitVecValueIndex {
        let value = value.into();
        let (words, width) = (value.words(), value.width());
        if let &[word] = words {
            debug_assert!(width <= Word::BITS);
            if word < 8 {
                BitVecValueIndex::new(word as WordIndex, width)
            } else if let Some(index) = self.small.get(&word) {
                BitVecValueIndex::new(*index, width)
            } else {
                let index = self.words.len() as WordIndex;
                self.words.push(word);
                self.small.insert(word, index);
                BitVecValueIndex::new(index, width)
            }
        } else {
            debug_assert!(width > Word::BITS);
            if let Some(index) = self.large.get(words) {
                BitVecValueIndex::new(*index, width)
            } else {
                let index = self.words.len() as WordIndex;
                self.words.extend_from_slice(words);
                self.large.insert(Box::from(words), index);
                BitVecValueIndex::new(index, width)
            }
        }
    }

    pub fn words(&self) -> &[Word] {
        &self.words
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{BitVecMutOps, BitVecValue};

    #[test]
    fn type_size() {
        assert_eq!(std::mem::size_of::<WidthInt>(), 4);
        assert_eq!(std::mem::size_of::<WordIndex>(), 4);
        assert_eq!(std::mem::size_of::<BitVecValueIndex>(), 8);
    }

    #[test]
    fn test_bv_index() {
        let mut backend = [0; 16];
        let a = BitVecValueIndex::new(0, 8);
        let b = BitVecValueIndex::new(1, 8);
        {
            let mut a = backend.get_mut_ref(a);
            a.assign(&BitVecValue::from_u64(123, 8));
        }
        assert_eq!(backend[0], 123);
        backend[1] = 111;
        {
            let (mut a, b) = backend.get_mut_ref((a, b));
            a.assign(b);
        }
        assert_eq!(backend[0], 111);
    }

    #[test]
    fn test_split_borrow() {
        let data: &mut [Word] = &mut [0, 1, 2, 3];
        let (dst, src) = split_borrow_1(data, 0..1, 2..4);
        assert_eq!(dst, &[0]);
        assert_eq!(src, &[2, 3]);
        let (dst2, src2) = split_borrow_1(data, 2..4, 0..2);
        assert_eq!(dst2, &[2, 3]);
        assert_eq!(src2, &[0, 1]);

        let (dst3, src_a_3, src_b_3) = split_borrow_2(data, 2..4, 1..2, 0..2);
        assert_eq!(dst3, &[2, 3]);
        assert_eq!(src_a_3, &[1]);
        assert_eq!(src_b_3, &[0, 1]);
    }

    #[test]
    fn test_interner() {
        let mut i = ValueInterner::new();
        assert_eq!(i.get_index(&BitVecValue::tru()).index, 1);
        assert_eq!(i.get_index(&BitVecValue::fals()).index, 0);
        assert_eq!(i.get_index(&BitVecValue::from_u64(0, 4)).index, 0);
        assert!(ValueInterner::is_zero(
            i.get_index(&BitVecValue::from_u64(0, 4))
        ));
        assert!(!ValueInterner::is_one(
            i.get_index(&BitVecValue::from_u64(0, 4))
        ));
        assert!(ValueInterner::is_one(
            i.get_index(&BitVecValue::from_u64(1, 4))
        ));
    }

    #[cfg(feature = "bigint")]
    use num_bigint::*;
    use proptest::prelude::*;

    #[cfg(feature = "bigint")]
    fn interner_should_return_same_value(value: &BigInt, width: WidthInt) {
        let mut intern = ValueInterner::new();
        let i0 = intern.get_index(&BitVecValue::from_big_int(value, width));
        let i1 = intern.get_index(&BitVecValue::from_big_int(value, width));
        assert_eq!(i0.index, i1.index);
        assert_eq!(i0.width, i1.width);
        let v0 = intern.words().get_ref(i0);
        assert_eq!(BitVecValue::from_big_int(value, width), v0);
    }

    #[cfg(all(test, feature = "bigint"))]
    fn gen_big_uint(bits: WidthInt) -> impl Strategy<Value = BigUint> {
        let byte_count = bits.div_ceil(u8::BITS);
        let words = prop::collection::vec(any::<u8>(), byte_count as usize);
        words.prop_map(move |mut words| {
            // first we mask the msbs
            if bits % u8::BITS > 0 {
                let mask = (1u8 << (bits % u8::BITS)) - 1;
                *words.last_mut().unwrap() &= mask;
            }
            BigUint::from_bytes_le(&words)
        })
    }

    #[cfg(all(test, feature = "bigint"))]
    fn gen_big_int(bits: WidthInt) -> impl Strategy<Value = BigInt> {
        gen_big_uint(bits - 1)
            .prop_flat_map(|unsigned| (any::<bool>(), Just(unsigned)))
            .prop_map(|(negative, unsigned)| {
                let sign = if negative { Sign::Minus } else { Sign::Plus };
                BigInt::from_biguint(sign, unsigned)
            })
    }

    #[cfg(all(test, feature = "bigint"))]
    fn gen_big_int_and_width() -> impl Strategy<Value = (BigInt, WidthInt)> {
        let max_bits = 16 * Word::BITS;
        (1..max_bits).prop_flat_map(|width| (gen_big_int(width), Just(width)))
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(2000))]

        #[test]
        #[cfg(feature = "bigint")]
        fn prop_test_interner((value, width) in gen_big_int_and_width()) {
            interner_should_return_same_value(&value, width);
        }
    }
}
