// Copyright 2024 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>

use crate::{WidthInt, Word};

const BYTES_PER_WORD: u32 = Word::BITS.div_ceil(8);
const BYTE_MASK: Word = (1 << u8::BITS) - 1;

pub(crate) fn to_bytes_le(values: &[Word], width: WidthInt) -> Vec<u8> {
    let byte_count = width.div_ceil(u8::BITS) as usize;
    let mut out = Vec::with_capacity(byte_count);
    for word in values.iter() {
        let mut value = *word;
        for _ in 0..BYTES_PER_WORD {
            if out.len() == byte_count {
                break;
            }
            out.push((value & BYTE_MASK) as u8);
            value >>= u8::BITS;
        }
    }
    out
}

pub(crate) fn to_bytes_be(values: &[Word], width: WidthInt) -> Vec<u8> {
    let mut out = to_bytes_le(values, width);
    out.reverse();
    out
}

pub(crate) fn from_bytes_le(
    bytes: impl ExactSizeIterator + Iterator<Item = u8>,
    width: WidthInt,
    out: &mut [Word],
) {
    let word_count = width.div_ceil(Word::BITS) as usize;
    debug_assert!(out.len() >= word_count);
    if width == 0 {
        return;
    }
    let max_word_ii = (bytes.len() - 1) / BYTES_PER_WORD as usize;
    debug_assert!(max_word_ii < out.len());
    crate::bv::arithmetic::clear(out);
    for (ii, bb) in bytes.enumerate() {
        let word_ii = ii / BYTES_PER_WORD as usize;
        let shift_by = u8::BITS * (ii as u32 % BYTES_PER_WORD);
        out[word_ii] |= (bb as Word) << shift_by;
    }
    crate::bv::arithmetic::mask_msb(out, width);
}

pub(crate) fn from_bytes_be(
    bytes: impl DoubleEndedIterator + ExactSizeIterator + Iterator<Item = u8>,
    width: WidthInt,
    out: &mut [Word],
) {
    from_bytes_le(bytes.rev(), width, out);
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::proptest;

    #[test]
    fn test_to_bytes_le() {
        let out0 = to_bytes_le(&[0x1234], 16);
        assert_eq!(out0, [0x34, 0x12]);
        let out1 = to_bytes_le(&[0x1234, 0xf], 64 + 8);
        assert_eq!(out1, [0x34, 0x12, 0, 0, 0, 0, 0, 0, 0xf]);
    }

    #[test]
    fn test_from_bytes_le() {
        let mut out0 = vec![0; 1];
        from_bytes_le([0x34, 0x12].iter().cloned(), 16, &mut out0);
        assert_eq!(out0, [0x1234]);
    }

    #[test]
    fn test_from_bytes_be() {
        let mut out0 = vec![0; 1];
        from_bytes_be([1].iter().cloned(), 1, &mut out0);
        assert_eq!(out0, [1]);
        let out1 = to_bytes_be(&out0, 1);
        assert_eq!(out1, [1]);
    }

    fn do_test_from_to_bytes_le(b: &[u8]) {
        let width = if b.is_empty() {
            0
        } else {
            (b.len() - 1) * u8::BITS as usize
                + std::cmp::max(8 - b.last().unwrap().leading_zeros() as usize, 1)
        } as u32;
        let words = width.div_ceil(Word::BITS) as usize;
        let mut out = vec![0; words];
        from_bytes_le(b.iter().cloned(), width, &mut out);
        crate::bv::arithmetic::assert_unused_bits_zero(&out, width);
        let b_out = to_bytes_le(&out, width);
        assert_eq!(b, b_out);
    }

    fn do_test_from_to_bytes_be(b: &[u8]) {
        let width = if b.is_empty() {
            0
        } else {
            (b.len() - 1) * u8::BITS as usize
                + std::cmp::max(8 - b.first().unwrap().leading_zeros() as usize, 1)
        } as u32;
        let words = width.div_ceil(Word::BITS) as usize;
        let mut out = vec![0; words];
        from_bytes_be(b.iter().cloned(), width, &mut out);
        crate::bv::arithmetic::assert_unused_bits_zero(&out, width);
        let b_out = to_bytes_be(&out, width);
        assert_eq!(b, b_out);
    }

    #[test]
    fn test_le_empty() {
        do_test_from_to_bytes_le(&[]);
        do_test_from_to_bytes_be(&[]);
    }

    #[test]
    fn test_le_zero() {
        do_test_from_to_bytes_le(&[0]);
        do_test_from_to_bytes_be(&[0]);
    }

    proptest! {
        #[test]
        fn test_from_to_bytes_le(b: Vec<u8>) {
            do_test_from_to_bytes_le(&b);
        }

        #[test]
        fn test_from_to_bytes_be(b: Vec<u8>) {
            do_test_from_to_bytes_be(&b);
        }
    }
}
