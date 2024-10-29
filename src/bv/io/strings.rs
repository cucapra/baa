// Copyright 2023-2024 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>

use crate::bv::arithmetic::{is_neg, negate_in_place};
use crate::{WidthInt, Word};
use std::fmt::Write;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseIntError {
    pub kind: IntErrorKind,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IntErrorKind {
    /// An invalid digit was encountered.
    InvalidDigit,
    /// The integer does not fit into the size of the bitvector.
    ExceedsWidth,
}
impl From<std::num::ParseIntError> for ParseIntError {
    fn from(e: std::num::ParseIntError) -> Self {
        let kind = match e.kind() {
            std::num::IntErrorKind::NegOverflow | std::num::IntErrorKind::PosOverflow => {
                IntErrorKind::ExceedsWidth
            }
            _ => IntErrorKind::InvalidDigit,
        };
        ParseIntError { kind }
    }
}

/// Interprets the bits as a two's complement integer.
pub(crate) fn to_bit_str_signed(values: &[Word], width: WidthInt) -> String {
    if is_neg(values, width) {
        let mut copy = Vec::from(values);
        negate_in_place(&mut copy, width);
        let mut out = String::with_capacity(width as usize + 1);
        out.push('-');
        to_bit_str_internal(&copy, width - 1, out)
    } else {
        to_bit_str(values, width - 1)
    }
}

pub(crate) fn to_bit_str(values: &[Word], width: WidthInt) -> String {
    let out = String::with_capacity(width as usize);
    to_bit_str_internal(values, width, out)
}

fn to_bit_str_internal(values: &[Word], width: WidthInt, mut out: String) -> String {
    if width == 0 {
        return "".to_string();
    }
    let start_bit = (width - 1) % Word::BITS;
    let msb = values.last().unwrap();
    for ii in (0..(start_bit + 1)).rev() {
        let value = (msb >> ii) & 1;
        if value == 1 {
            out.push('1');
        } else {
            out.push('0');
        }
    }
    for word in values.iter().rev().skip(1) {
        for ii in (0..Word::BITS).rev() {
            let value = (word >> ii) & 1;
            if value == 1 {
                out.push('1');
            } else {
                out.push('0');
            }
        }
    }
    out
}

/// 4 bits fit into a single hex digit
const BITS_PER_HEX_DIGIT: u32 = 4;
const WORD_HEX_DIGITS: u32 = Word::BITS / BITS_PER_HEX_DIGIT;
const WORD_HEX_MASK: Word = ((1 as Word) << BITS_PER_HEX_DIGIT) - 1;

/// Interprets the bits as a two's complement integer.
pub(crate) fn to_hex_str_signed(values: &[Word], width: WidthInt) -> String {
    if is_neg(values, width) {
        let mut copy = Vec::from(values);
        negate_in_place(&mut copy, width);
        let mut out = String::with_capacity(width as usize + 1);
        out.push('-');
        to_hex_str_internal(select_words_for_width(&copy, width - 1), width - 1, out)
    } else {
        to_hex_str(select_words_for_width(values, width - 1), width - 1)
    }
}

#[inline]
fn select_words_for_width(words: &[Word], width: WidthInt) -> &[Word] {
    let words_needed = width.div_ceil(Word::BITS) as usize;
    debug_assert!(words.len() >= words_needed, "not enough words!");
    &words[0..words_needed]
}

pub(crate) fn to_hex_str(values: &[Word], width: WidthInt) -> String {
    let out = String::with_capacity(width.div_ceil(BITS_PER_HEX_DIGIT) as usize);
    to_hex_str_internal(values, width, out)
}

fn to_hex_str_internal(values: &[Word], width: WidthInt, mut out: String) -> String {
    debug_assert_eq!(width.div_ceil(Word::BITS) as usize, values.len());
    if width == 0 {
        return "".to_string();
    }
    let bits_in_msb = width % Word::BITS;
    let digits_in_msb = bits_in_msb.div_ceil(BITS_PER_HEX_DIGIT);
    let msb = values.last().unwrap();
    for ii in (0..digits_in_msb).rev() {
        let value = (msb >> (ii * BITS_PER_HEX_DIGIT)) & WORD_HEX_MASK;
        out.push(char::from_digit(value as u32, 16).unwrap());
    }
    let skip_num = if digits_in_msb > 0 { 1 } else { 0 };
    for word in values.iter().rev().skip(skip_num) {
        for ii in (0..WORD_HEX_DIGITS).rev() {
            let value = (word >> (ii * BITS_PER_HEX_DIGIT)) & WORD_HEX_MASK;
            out.push(char::from_digit(value as u32, 16).unwrap());
        }
    }
    out
}

pub(crate) fn to_dec_str(values: &[Word], width: WidthInt) -> String {
    let out = String::with_capacity((width * 3 / 10) as usize);
    to_dec_str_internal(values, out)
}

/// Returns the number of lsb words that are non-zero
#[inline]
fn words_used(words: &[Word]) -> usize {
    let mut len = words.len();
    for &w in words.iter().rev() {
        if w != 0 {
            return len;
        }
        len -= 1;
    }
    0 // all words are zero
}

#[inline]
fn words_to_u128(words: &[Word]) -> u128 {
    debug_assert!(words.len() >= 2);
    debug_assert_eq!(Word::BITS * 2, u128::BITS);
    ((words[1] as u128) << Word::BITS) | words[0] as u128
}

fn to_dec_str_internal(values: &[Word], mut out: String) -> String {
    // see how many words are actually used
    let words_used = words_used(values);

    match words_used {
        0 => out.push('0'),
        1 => write!(out, "{}", values[0]).unwrap(),
        2 => write!(out, "{}", words_to_u128(values)).unwrap(),
        _ => to_dec_str_wide(&values[0..words_used], &mut out),
    }
    out
}

fn to_dec_str_wide(_words: &[Word], _out: &mut str) {
    todo!()
}

pub(crate) fn determine_width_from_str_radix(value: &str, radix: u32) -> WidthInt {
    debug_assert!(
        radix == 2 || radix == 16,
        "only works for 2 or 16 bit basis"
    );
    let starts_with_minus = value.starts_with('-');
    let num_digits = match value.as_bytes() {
        [] => 0,
        [b'+' | b'-'] => 0,
        [b'+' | b'-', digits @ ..] => digits.len() as WidthInt,
        digits => digits.len() as WidthInt,
    };

    let base_width = match radix {
        2 => num_digits,
        16 => num_digits * 4,
        _ => todo!(),
    };
    base_width + starts_with_minus as WidthInt
}

#[inline]
fn hex_digit_value(digit: u8) -> Result<u8, ParseIntError> {
    let value = match digit {
        b'0'..=b'9' => digit - b'0',
        b'a'..=b'f' => digit - b'a' + 10,
        b'A'..=b'F' => digit - b'A' + 10,
        _ => {
            return Err(ParseIntError {
                kind: IntErrorKind::InvalidDigit,
            })
        }
    };
    Ok(value)
}

/// Converts number string into bit vector value. Similar to `from_str_radix` in the Rust standard library.
pub(crate) fn from_str_radix(
    value: &str,
    radix: u32,
    out: &mut [Word],
    width: WidthInt,
) -> Result<(), ParseIntError> {
    // The empty string becomes a 0-bit vector.
    if value.is_empty() {
        return Ok(());
    }

    // remove any minus
    let (is_negative, value) = match value.strip_prefix('-') {
        Some(value) => (true, value),
        None => (false, value),
    };

    // special handling for 0-bit strings
    if width == 0 {
        if value == "0" {
            return Ok(());
        } else {
            return Err(ParseIntError {
                kind: IntErrorKind::ExceedsWidth,
            });
        }
    }

    if value.is_empty() {
        return Err(ParseIntError {
            kind: IntErrorKind::InvalidDigit,
        });
    }

    // use Rust standard parsing infrastructure when the result needs to fit into a u64 or u128
    match out {
        [out] => {
            debug_assert!(width <= 64);
            *out = match u64::from_str_radix(value, radix) {
                Ok(v) => v,
                Err(e) => {
                    let kind = match e.kind() {
                        std::num::IntErrorKind::NegOverflow
                        | std::num::IntErrorKind::PosOverflow => IntErrorKind::ExceedsWidth,
                        _ => IntErrorKind::InvalidDigit,
                    };
                    return Err(ParseIntError { kind });
                }
            };
        }
        [lsb, msb] => {
            debug_assert!(width <= 128);
            let out = match u128::from_str_radix(value, radix) {
                Ok(v) => v,
                Err(e) => {
                    let kind = match e.kind() {
                        std::num::IntErrorKind::NegOverflow
                        | std::num::IntErrorKind::PosOverflow => IntErrorKind::ExceedsWidth,
                        _ => IntErrorKind::InvalidDigit,
                    };
                    return Err(ParseIntError { kind });
                }
            };
            *lsb = out as Word;
            *msb = (out >> Word::BITS) as Word;
        }
        _ => {
            debug_assert_eq!(width.div_ceil(Word::BITS) as usize, out.len());

            // use our own custom implementation for larger sizes
            // treat string as bytes
            let digits = value.as_bytes();

            // strip '+'
            let digits = match digits {
                [b'+'] => {
                    return Err(ParseIntError {
                        kind: IntErrorKind::InvalidDigit,
                    });
                }
                [b'+', rest @ ..] => rest,
                _ => digits,
            };

            match radix {
                2 => parse_base_2(digits, out, width)?,
                10 => parse_base_10(digits, out, width)?,
                16 => parse_base_16(digits, out)?,
                _ => todo!("Implement support for base {radix}. Currently the following bases are available: 2, 10, 16"),
            };
        }
    }

    // TODO: check width
    // let m = super::super::arithmetic::mask(width);
    // if *out != *out & m {
    //     Err(ParseIntError {
    //         kind: IntErrorKind::ExceedsWidth,
    //     })
    // } else {
    //     Ok(())
    // }

    if is_negative {
        negate_in_place(out, width)
    }
    Ok(())
}

fn parse_base_16(digits: &[u8], out: &mut [Word]) -> Result<WidthInt, ParseIntError> {
    let num_digits = digits.len();
    let words = (num_digits as u32 * BITS_PER_HEX_DIGIT).div_ceil(Word::BITS);
    let mut word = 0 as Word;
    let mut out_ii = (words - 1) as usize;

    // read from right to left
    for (ii, cc) in digits.iter().enumerate() {
        let ii_rev = num_digits - ii - 1;
        if ii > 0 && ((ii_rev + 1) % WORD_HEX_DIGITS as usize) == 0 {
            out[out_ii] = word;
            out_ii -= 1;
            word = 0;
        }
        let value = hex_digit_value(*cc)?;
        word = (word << BITS_PER_HEX_DIGIT) | (value as Word);
    }
    debug_assert_eq!(out_ii, 0);
    out[0] = word;
    Ok(num_digits as u32 * BITS_PER_HEX_DIGIT)
}

fn parse_base_10(
    _digits: &[u8],
    _out: &mut [Word],
    _max_width: WidthInt,
) -> Result<WidthInt, ParseIntError> {
    // let other = BitVecValue::
    todo!()
}

fn parse_base_2(
    digits: &[u8],
    out: &mut [Word],
    max_width: WidthInt,
) -> Result<WidthInt, ParseIntError> {
    let width = digits.len() as WidthInt;
    // TODO: ignore zeros
    if width > max_width {
        return Err(ParseIntError {
            kind: IntErrorKind::ExceedsWidth,
        });
    }

    let words = width.div_ceil(Word::BITS);
    let mut word = 0 as Word;
    let mut out_ii = (words - 1) as usize;

    for (ii, cc) in digits.iter().enumerate() {
        let ii_rev = width as usize - ii - 1;
        if ii > 0 && ((ii_rev + 1) % Word::BITS as usize) == 0 {
            out[out_ii] = word;
            out_ii -= 1;
            word = 0;
        }

        let value = match cc {
            b'1' => 1,
            b'0' => 0,
            _ => {
                return Err(ParseIntError {
                    kind: IntErrorKind::InvalidDigit,
                })
            }
        };
        word = (word << 1) | value;
    }
    debug_assert_eq!(out_ii, 0);
    out[0] = word;
    Ok(width)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{BitVecMutOps, BitVecOps, BitVecValue};

    #[test]
    fn test_to_bit_str_with_extra_words() {
        let value = BitVecValue::zero(7);
        let input = value.words();
        assert_eq!(to_bit_str(&input, 7), "0000000");
        assert_eq!(to_bit_str(&input, 33), "0".repeat(33));
    }

    #[test]
    fn test_hex_digit_value() {
        assert_eq!(hex_digit_value(b'a').unwrap(), 10);
        assert_eq!(hex_digit_value(b'A').unwrap(), 10);
    }

    #[test]
    fn test_to_hex_str() {
        let mut value = BitVecValue::zero(64);
        let input = value.words_mut();
        assert_eq!(to_hex_str(&input, 7), "00");
        assert_eq!(to_hex_str(&input, 33), "0".repeat(9));
        input[0] = 0xa4aa78;
        assert_eq!(to_hex_str(&input, 6 * 4), "a4aa78");
        let mut value = BitVecValue::zero(128);
        let input = value.words_mut();
        input[0] = 0xaaaaaaaaaaaaaaaa;
        assert_eq!(to_hex_str(&input, 7 + Word::BITS), "00aaaaaaaaaaaaaaaa");
        assert_eq!(
            to_hex_str(&input, 33 + Word::BITS),
            format!("{}aaaaaaaaaaaaaaaa", "0".repeat(9))
        );
        input[1] = 0xa4aa78;
        assert_eq!(
            to_hex_str(&input, 6 * 4 + Word::BITS),
            "a4aa78aaaaaaaaaaaaaaaa"
        );
        // regressions test
        let mut value = BitVecValue::zero(64);
        let input = value.words_mut();
        input[0] = 768603298337958570;
        assert_eq!(to_hex_str(&input, 64), "0aaaa0a0aaa0aaaa");
    }
}
