// Copyright 2023-2024 The Regents of the University of California
// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>
//
// basic arithmetic implementations

use crate::{WidthInt, Word};
use std::cmp::Ordering;

// TODO: make sure this is updated together with the Word type
type DoubleWord = u128;

#[inline]
pub fn mask(bits: WidthInt) -> Word {
    if bits == Word::BITS || bits == 0 {
        Word::MAX
    } else {
        assert!(bits < Word::BITS);
        ((1 as Word) << bits) - 1
    }
}

#[inline]
pub fn mask_double_word(bits: WidthInt) -> DoubleWord {
    if bits == DoubleWord::BITS || bits == 0 {
        DoubleWord::MAX
    } else {
        assert!(bits < DoubleWord::BITS);
        ((1 as DoubleWord) << bits) - 1
    }
}

#[inline]
pub(crate) fn clear(dst: &mut [Word]) {
    for w in dst.iter_mut() {
        *w = 0;
    }
}

#[inline]
fn set(dst: &mut [Word]) {
    for w in dst.iter_mut() {
        *w = Word::MAX;
    }
}

#[inline]
pub(crate) fn assign(dst: &mut [Word], source: &[Word]) {
    for (d, s) in dst.iter_mut().zip(source.iter()) {
        *d = *s;
    }
}

#[inline]
pub(crate) fn zero_extend(dst: &mut [Word], source: &[Word]) {
    // copy source to dst
    assign(dst, source);
    // zero out remaining words
    clear(&mut dst[source.len()..]);
}

#[inline]
pub(crate) fn sign_extend(
    dst: &mut [Word],
    source: &[Word],
    src_width: WidthInt,
    dst_width: WidthInt,
) {
    // copy source to dst
    assign(dst, source);
    if is_neg(source, src_width) {
        // set source msbs in destination
        let lsbs_in_msb = src_width % Word::BITS;
        if lsbs_in_msb > 0 {
            let msbs_in_msb = Word::BITS - lsbs_in_msb;
            dst[source.len() - 1] |= mask(msbs_in_msb) << lsbs_in_msb;
        }
        // set other dst bytes to all 1s
        set(&mut dst[source.len()..]);
        // clear destination msbs
        mask_msb(dst, dst_width);
    } else {
        clear(&mut dst[source.len()..]);
    }
}

#[inline]
pub(crate) fn mask_msb(dst: &mut [Word], width: WidthInt) {
    debug_assert_eq!(width.div_ceil(Word::BITS) as usize, dst.len());
    let m = mask(width % Word::BITS);
    *dst.last_mut().unwrap() &= m;
}

#[inline]
pub(crate) fn is_bit_set(source: &[Word], pos: WidthInt) -> bool {
    let bit_idx = pos % Word::BITS;
    let word_idx = (pos / Word::BITS) as usize;
    (source[word_idx] >> bit_idx) & 1 == 1
}

#[inline]
pub(crate) fn set_bit(dst: &mut [Word], pos: WidthInt) {
    let bit_idx = pos % Word::BITS;
    let word_idx = (pos / Word::BITS) as usize;
    dst[word_idx] |= 1 << bit_idx;
}

#[inline]
pub(crate) fn clear_bit(dst: &mut [Word], pos: WidthInt) {
    let bit_idx = pos % Word::BITS;
    let word_idx = (pos / Word::BITS) as usize;
    dst[word_idx] &= !(1 << bit_idx);
}

#[inline]
pub(crate) fn slice(dst: &mut [Word], source: &[Word], hi: WidthInt, lo: WidthInt) {
    let lo_offset = lo % Word::BITS;
    let hi_word = (hi / Word::BITS) as usize;
    let lo_word = (lo / Word::BITS) as usize;
    let src = &source[lo_word..(hi_word + 1)];

    let shift_right = lo_offset;
    if shift_right == 0 {
        assign(dst, src);
    } else {
        // assign with a shift
        let shift_left = Word::BITS - shift_right;
        let m = mask(shift_right);
        let mut prev = src[0] >> shift_right;
        // We append a zero to the src iter in case src.len() == dst.len().
        // If src.len() == dst.len() + 1, then the 0 will just be ignored by `zip`.
        for (d, s) in dst.iter_mut().zip(src.iter().skip(1).chain([0].iter())) {
            *d = prev | ((*s) & m) << shift_left;
            prev = (*s) >> shift_right;
        }
    }
    // mask the result msb
    mask_msb(dst, hi - lo + 1);
}

#[inline]
pub(crate) fn concat(dst: &mut [Word], msb: &[Word], lsb: &[Word], lsb_width: WidthInt) {
    // copy lsb to dst
    assign(dst, lsb);

    let lsb_offset = lsb_width % Word::BITS;
    if lsb_offset == 0 {
        // copy msb to dst
        for (d, m) in dst.iter_mut().skip(lsb.len()).zip(msb.iter()) {
            *d = *m;
        }
    } else {
        // copy a shifted version of the msb to dst
        let shift_right = Word::BITS - lsb_offset;
        let m = mask(shift_right);
        let mut prev = dst[lsb.len() - 1]; // the msb of the lsb
        for (d, s) in dst
            .iter_mut()
            .skip(lsb.len() - 1)
            .zip(msb.iter().chain([0].iter()))
        {
            *d = prev | ((*s) & m) << lsb_offset;
            prev = (*s) >> shift_right;
        }
    }
}

#[inline]
pub(crate) fn not(dst: &mut [Word], source: &[Word], width: WidthInt) {
    bitwise_un_op(dst, source, |e| !e);
    mask_msb(dst, width);
}

#[inline]
fn bitwise_un_op(dst: &mut [Word], source: &[Word], op: fn(Word) -> Word) {
    for (d, s) in dst.iter_mut().zip(source.iter()) {
        *d = (op)(*s);
    }
}

#[inline]
pub(crate) fn and(dst: &mut [Word], a: &[Word], b: &[Word]) {
    bitwise_bin_op(dst, a, b, |a, b| a & b)
}

#[inline]
pub(crate) fn or(dst: &mut [Word], a: &[Word], b: &[Word]) {
    bitwise_bin_op(dst, a, b, |a, b| a | b)
}

#[inline]
pub(crate) fn xor(dst: &mut [Word], a: &[Word], b: &[Word]) {
    bitwise_bin_op(dst, a, b, |a, b| a ^ b)
}

#[inline]
fn bitwise_bin_op(dst: &mut [Word], a: &[Word], b: &[Word], op: fn(Word, Word) -> Word) {
    for (d, (a, b)) in dst.iter_mut().zip(a.iter().zip(b.iter())) {
        *d = (op)(*a, *b);
    }
}

#[inline]
fn adc(dst: &mut Word, carry: u8, a: Word, b: Word) -> u8 {
    let sum = carry as DoubleWord + a as DoubleWord + b as DoubleWord;
    let new_carry = (sum >> Word::BITS) as u8;
    *dst = sum as Word;
    new_carry
}

/// Add function inspired by the num-bigint implementation: https://docs.rs/num-bigint/0.4.4/src/num_bigint/biguint/addition.rs.html
#[inline]
pub(crate) fn add(dst: &mut [Word], a: &[Word], b: &[Word], width: WidthInt) {
    let mut carry = 0;
    for (dd, (aa, bb)) in dst.iter_mut().zip(a.iter().zip(b.iter())) {
        carry = adc(dd, carry, *aa, *bb);
    }
    mask_msb(dst, width);
}

/// Sub function inspired by the num-bigint implementation: https://docs.rs/num-bigint/0.4.4/src/num_bigint/biguint/subtraction.rs.html
#[inline]
pub(crate) fn sub(dst: &mut [Word], a: &[Word], b: &[Word], width: WidthInt) {
    // we add one by setting the input carry to one
    let mut carry = 1;
    for (dd, (aa, bb)) in dst.iter_mut().zip(a.iter().zip(b.iter())) {
        // we invert b which in addition to adding 1 turns it into `-b`
        carry = adc(dd, carry, *aa, !(*bb));
    }
    mask_msb(dst, width);
}

/// Mul function inspired by the num-bigint implementation: https://docs.rs/num-bigint/0.4.4/src/num_bigint/biguint/multiplication.rs.html
#[inline]
pub(crate) fn mul(dst: &mut [Word], a: &[Word], b: &[Word], width: WidthInt) {
    if width <= Word::BITS {
        let (res, _) = a[0].overflowing_mul(b[0]);
        dst[0] = res & mask(width);
    } else {
        todo!(
            "implement multiplication for bit vectors larger {}",
            Word::BITS
        );
    }
}

#[inline]
pub(crate) fn shift_right(
    dst: &mut [Word],
    a: &[Word],
    b: &[Word],
    width: WidthInt,
) -> Option<WidthInt> {
    // clear the destination
    clear(dst);

    // check to see if we are shifting for more than our width
    let shift_amount = get_shift_amount(b, width)?;

    // otherwise we actually perform the shift by converting it to a slice
    let hi = width - 1;
    let lo = shift_amount;
    let result_width = hi - lo + 1;
    let result_words = result_width.div_ceil(Word::BITS) as usize;
    slice(&mut dst[..result_words], a, hi, lo);
    Some(shift_amount)
}

#[inline]
pub(crate) fn arithmetic_shift_right(dst: &mut [Word], a: &[Word], b: &[Word], width: WidthInt) {
    // perform shift
    let shift_amount = shift_right(dst, a, b, width);

    // pad with sign bit if necessary
    if is_neg(a, width) {
        match shift_amount {
            None => {
                // over shift => we just need to set everything to 1
                for d in dst.iter_mut() {
                    *d = Word::MAX;
                }
                mask_msb(dst, width);
            }
            Some(amount) => {
                if amount > 0 {
                    let res_width = width - amount;
                    let local_msb = (res_width - 1) % Word::BITS;
                    let msb_word = ((res_width - 1) / Word::BITS) as usize;
                    if local_msb < (Word::BITS - 1) {
                        let msb_word_mask = mask(Word::BITS - (local_msb + 1));
                        dst[msb_word] |= msb_word_mask << (local_msb + 1);
                    }
                    for d in dst[(msb_word + 1)..].iter_mut() {
                        *d = Word::MAX;
                    }
                    mask_msb(dst, width);
                }
            }
        }
    }
}

#[inline]
pub(crate) fn shift_left(dst: &mut [Word], a: &[Word], b: &[Word], width: WidthInt) {
    // check to see if we are shifting for more than our width
    let shift_amount = match get_shift_amount(b, width) {
        None => {
            clear(dst);
            return;
        }
        Some(value) => value,
    };

    // otherwise we actually perform the shift
    let shift_left = shift_amount % Word::BITS;
    let shift_words = shift_amount / Word::BITS;
    let shift_right = Word::BITS - shift_left;
    let zeros = std::iter::repeat(&(0 as Word)).take(shift_words as usize);
    let mut prev = 0;
    for (d, s) in dst.iter_mut().zip(zeros.chain(a.iter())) {
        if shift_left == 0 {
            *d = *s;
        } else {
            *d = (*s << shift_left) | prev;
            prev = *s >> shift_right;
        }
    }
    if shift_left > 0 {
        mask_msb(dst, width);
    }
}

#[inline]
fn get_shift_amount(b: &[Word], width: WidthInt) -> Option<WidthInt> {
    let msb_set = b.iter().skip(1).any(|w| *w != 0);
    let shift_amount = b[0];
    if msb_set || shift_amount >= width as Word {
        None // result is just zero or the sign bit
    } else {
        Some(shift_amount as WidthInt)
    }
}

#[inline]
pub(crate) fn negate(dst: &mut [Word], b: &[Word], width: WidthInt) {
    dst.clone_from_slice(b);
    negate_in_place(dst, width);
}

#[inline]
pub(crate) fn negate_in_place(dst: &mut [Word], width: WidthInt) {
    // we add one by setting the input carry to one
    let mut carry = 1;
    for dd in dst.iter_mut() {
        // we invert b which in addition to adding 1 turns it into `-b`
        let b = !(*dd);
        carry = adc(dd, carry, 0, b);
    }
    mask_msb(dst, width);
}

#[inline]
pub(crate) fn cmp_equal(a: &[Word], b: &[Word]) -> bool {
    a.iter().zip(b.iter()).all(|(a, b)| a == b)
}

#[inline]
pub(crate) fn cmp_greater(a: &[Word], b: &[Word]) -> bool {
    is_greater_and_not_less(a, b).unwrap_or(false)
}

#[inline]
pub(crate) fn is_neg(src: &[Word], width: WidthInt) -> bool {
    let msb_bit_id = (width - 1) % Word::BITS;
    let msb_word = src.last().unwrap();
    let msb_bit_value = ((msb_word) >> msb_bit_id) & 1;
    msb_bit_value == 1
}

#[inline]
pub(crate) fn cmp_greater_signed(a: &[Word], b: &[Word], width: WidthInt) -> bool {
    let (is_neg_a, is_neg_b) = (is_neg(a, width), is_neg(b, width));
    match (is_neg_a, is_neg_b) {
        (true, false) => false, // -|a| < |b|
        (false, true) => true,  // |a| > -|b|
        (false, false) => cmp_greater(a, b),
        (true, true) => cmp_greater(a, b), // TODO: does this actually work?
    }
}

/// `Some(true)` if `a > b`, `Some(false)` if `a < b`, None if `a == b`
#[inline]
fn is_greater_and_not_less(a: &[Word], b: &[Word]) -> Option<bool> {
    for (a, b) in a.iter().rev().zip(b.iter().rev()) {
        match a.cmp(b) {
            Ordering::Less => return Some(false),
            Ordering::Equal => {} // continue
            Ordering::Greater => return Some(true),
        }
    }
    None
}

#[inline]
pub(crate) fn cmp_greater_equal(a: &[Word], b: &[Word]) -> bool {
    is_greater_and_not_less(a, b).unwrap_or(true)
}

#[inline]
pub(crate) fn cmp_greater_equal_signed(a: &[Word], b: &[Word], width: WidthInt) -> bool {
    match (is_neg(a, width), is_neg(b, width)) {
        (true, false) => false, // -|a| < |b|
        (false, true) => true,  // |a| > -|b|
        (false, false) => cmp_greater_equal(a, b),
        (true, true) => cmp_greater_equal(a, b), // TODO: does this actually work?
    }
}

#[inline]
pub(crate) fn word_to_bool(value: Word) -> bool {
    (value & 1) == 1
}

#[cfg(test)]
pub(crate) fn assert_unused_bits_zero(value: &[Word], width: WidthInt) {
    let offset = width % Word::BITS;
    if offset > 0 {
        let msb = *value.last().unwrap();
        let m = !mask(offset);
        let unused = msb & m;
        assert_eq!(unused, 0, "unused msb bits need to be zero!")
    }
}

pub(crate) fn find_ranges_of_ones(words: &[Word]) -> Vec<std::ops::Range<WidthInt>> {
    // the actual width does not matter since we assume that all unused bits in the msb are set to zero
    let mut out = vec![];
    let mut range_start: Option<WidthInt> = None;
    for (word_ii, word) in words.iter().enumerate() {
        let lsb_ii = word_ii as WidthInt * Word::BITS;
        let mut word = *word;
        let mut bits_consumed = 0;

        // handle open range from previous word
        if let Some(start) = range_start {
            let ones = word.trailing_ones();
            bits_consumed += ones;
            word >>= ones;
            if ones < Word::BITS {
                range_start = None;
                out.push(start..lsb_ii + bits_consumed);
            }
        }

        // find ranges in this word
        while bits_consumed < Word::BITS {
            debug_assert!(range_start.is_none());
            if word == 0 {
                // done
                bits_consumed = Word::BITS;
            } else {
                let zeros = word.trailing_zeros();
                bits_consumed += zeros;
                word >>= zeros;
                let start = bits_consumed;
                let ones = word.trailing_ones();
                bits_consumed += ones;
                word = word.overflowing_shr(ones).0;
                match bits_consumed.cmp(&Word::BITS) {
                    Ordering::Less => {
                        let end = bits_consumed;
                        out.push(lsb_ii + start..lsb_ii + end);
                    }
                    Ordering::Equal => {
                        // done, range might expand to next word
                        range_start = Some(start + lsb_ii);
                    }
                    Ordering::Greater => {
                        unreachable!("")
                    }
                }
            }
        }
    }
    // finish open range
    if let Some(start) = range_start {
        let end = words.len() as WidthInt * Word::BITS;
        out.push(start..end);
    }

    out
}
