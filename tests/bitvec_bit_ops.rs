// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>
//
// Contains tests for bit vector operations that are easy to verify on the
// bit-level: is_negative, concat, slice, shift (<<, >>, >>>), zext, sext
use baa::*;
use proptest::prelude::*;

fn do_test_is_negative(a: &str) {
    let expected = a.starts_with('1');
    let value = BitVecValue::from_bit_str(a).unwrap();
    let actual = value.is_negative();
    assert_eq!(actual, expected, "{a}")
}

fn do_test_concat(a: &str, b: &str) {
    let a_value = BitVecValue::from_bit_str(a).unwrap();
    let b_value = BitVecValue::from_bit_str(b).unwrap();
    let c_value = a_value.concat(&b_value);
    let expected = format!("{a}{b}");
    assert_eq!(c_value.to_bit_str(), expected);
}

fn do_test_slice(src: &str, hi: WidthInt, lo: WidthInt) {
    assert!(
        !src.is_empty(),
        "slice only works with vectors that are at least 1-bit!"
    );
    let src_value = BitVecValue::from_bit_str(src).unwrap();
    assert!(hi >= lo);
    assert!(hi < src_value.width());
    let res = src_value.slice(hi, lo);
    assert_eq!(res.width(), hi - lo + 1);
    let expected: String = src
        .chars()
        .skip((src_value.width() - 1 - hi) as usize)
        .take(res.width() as usize)
        .collect();
    assert_eq!(res.to_bit_str(), expected);
}

fn do_test_shift(src: &str, by: WidthInt, right: bool, signed: bool) {
    assert!(!(!right && signed), "left shift is always unsigned!");
    let a = BitVecValue::from_bit_str(src).unwrap();
    let b = BitVecValue::from_u64(by as u64, a.width());
    assert_eq!(a.width(), b.width());
    let res = if right {
        if signed {
            a.arithmetic_shift_right(&b)
        } else {
            a.shift_right(&b)
        }
    } else {
        a.shift_left(&b)
    };

    let padding_len = std::cmp::min(by, a.width()) as usize;
    let pad_char = if signed {
        src.chars().next().unwrap()
    } else {
        '0'
    };

    let mut expected: String = pad_char.to_string().repeat(padding_len);
    if right {
        let msb: String = src.chars().take(a.width() as usize - padding_len).collect();
        expected.push_str(&msb);
    } else {
        let mut msb: String = src.chars().skip(padding_len).collect();
        msb.push_str(&expected);
        expected = msb;
    }
    let expected = BitVecValue::from_bit_str(&expected).unwrap();
    assert_eq!(res, expected, "{src:?} {by} {res:?} {expected:?}");
}

fn do_test_shift_right(src: &str, by: WidthInt) {
    do_test_shift(src, by, true, false);
}
fn do_test_shift_left(src: &str, by: WidthInt) {
    do_test_shift(src, by, false, false);
}

fn do_test_arithmetic_shift_right(src: &str, by: WidthInt) {
    do_test_shift(src, by, true, true);
}

fn do_test_zero_ext(src: &str, by: WidthInt) {
    let value = BitVecValue::from_bit_str(src).unwrap();
    let expected_res_width = value.width() + by;
    let actual = value.zero_extend(by);
    assert_eq!(expected_res_width, actual.width());
    let expected =
        BitVecValue::from_bit_str(&format!("{}{}", "0".repeat(by as usize), src)).unwrap();
    assert_eq!(
        actual,
        expected,
        "{} vs. {}",
        actual.to_bit_str(),
        expected.to_bit_str()
    );
}

fn do_test_sign_ext(src: &str, by: WidthInt) {
    assert!(!src.is_empty(), "sign extend only works for non zero bits");
    let value = BitVecValue::from_bit_str(src).unwrap();
    let expected_res_width = value.width() + by;
    let actual = value.sign_extend(by);
    assert_eq!(expected_res_width, actual.width());
    let sign_bit = src.chars().next().unwrap().to_string();
    let expected =
        BitVecValue::from_bit_str(&format!("{}{}", sign_bit.repeat(by as usize), src)).unwrap();
    assert_eq!(
        actual,
        expected,
        "{} vs. {}",
        actual.to_bit_str(),
        expected.to_bit_str()
    );
}

//////////////////////////
// generators for proptest
//////////////////////////
fn bit_str_arg() -> impl Strategy<Value = String> {
    "[01]+"
}

fn slice_args() -> impl Strategy<Value = (String, WidthInt, WidthInt)> {
    bit_str_arg()
        .prop_flat_map(|bits: String| {
            let len = std::cmp::max(bits.len(), 1);
            (Just(bits), 0..(len as WidthInt))
        })
        .prop_flat_map(|(bits, msb)| (Just(bits), Just(msb), 0..(msb + 1)))
}

/// biases `by` value to be more interesting
fn shift_args() -> impl Strategy<Value = (String, WidthInt)> {
    bit_str_arg().prop_flat_map(|bits: String| {
        let len = std::cmp::max(bits.len(), 1);
        let max_shift =
            std::cmp::min(mask(bits.len() as WidthInt) + 1, WidthInt::MAX as Word) as WidthInt;
        let by = prop_oneof![0..(len as WidthInt), 0..(max_shift)];
        (Just(bits), by)
    })
}

//////////////////////////
// Unit Tests
//////////////////////////

#[test]
fn do_test_is_negative_regressions() {
    let a = "0101101001111010000111000001011010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000";
    do_test_is_negative(a);
}

#[test]
fn test_arithmetic_shift_right_regression() {
    do_test_arithmetic_shift_right("1", 0);
    do_test_arithmetic_shift_right("10", 1);
    do_test_arithmetic_shift_right(&format!("1{}", "0".repeat(Word::BITS as usize)), 1);
    do_test_arithmetic_shift_right(&format!("1{}", "0".repeat((Word::BITS * 2) as usize)), 1);
    do_test_arithmetic_shift_right(
        &format!("1{}", "0".repeat((Word::BITS * 2) as usize)),
        Word::BITS,
    );
    do_test_arithmetic_shift_right(
        &format!("1{}", "0".repeat((Word::BITS * 2) as usize)),
        Word::BITS * 2,
    );
}

//////////////////////////
// Random Tests
//////////////////////////

proptest! {
    #![proptest_config(ProptestConfig::with_cases(5000))]

    #[test]
    fn test_is_negative(a in bit_str_arg()) {
        do_test_is_negative(&a);
    }

    #[test]
    fn test_concat(a in bit_str_arg(), b in bit_str_arg()) {
        do_test_concat(&a, &b);
    }

    #[test]
    fn test_slice((s, msb, lsb) in slice_args()) {
        do_test_slice(&s, msb, lsb);
    }

    #[test]
    fn test_shift_right((s, by) in shift_args()) {
        do_test_shift_right(&s, by);
    }

    #[test]
    fn test_shift_left((s, by) in shift_args()) {
        do_test_shift_left(&s, by);
    }

    #[test]
    fn test_arithmetic_shift_right((s, by) in shift_args()) {
        do_test_arithmetic_shift_right(&s, by);
    }

    #[test]
    fn test_zero_extend(s in bit_str_arg(), by in 0..(1000 as WidthInt)) {
        do_test_zero_ext(&s, by);
    }

    #[test]
    fn test_sign_extend(s in bit_str_arg(), by in 0..(1000 as WidthInt)) {
        do_test_sign_ext(&s, by);
    }
}
