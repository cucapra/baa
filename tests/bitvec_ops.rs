// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use baa::*;
use proptest::prelude::*;

fn do_test_is_negative(a: &str) {
    let expected = a.starts_with('1');
    let value = BitVecValue::from_bit_str(a).unwrap();
    let actual = value.is_negative();
    assert_eq!(actual, expected, "{a}")
}

#[test]
fn do_test_is_negative_regressions() {
    let a = "0101101001111010000111000001011010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000";
    do_test_is_negative(a);
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

// generators for proptest
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

    //#[test]
    // fn test_shift_right((s, by) in shift_args()) {
    //     do_test_shift_right(&s, by);
    // }
    //
    // #[test]
    // fn test_shift_left((s, by) in shift_args()) {
    //     do_test_shift_left(&s, by);
    // }
    //
    // #[test]
    // fn test_arithmetic_shift_right((s, by) in shift_args()) {
    //     do_test_arithmetic_shift_right(&s, by);
    // }
    //
    // #[test]
    // fn test_zero_extend(s in bit_str_arg(), by in 0..(1000 as WidthInt)) {
    //     do_test_zero_ext(&s, by);
    // }
    //
    // #[test]
    // fn test_sign_extend(s in bit_str_arg(), by in 0..(1000 as WidthInt)) {
    //     do_test_sign_ext(&s, by);
    // }
}
