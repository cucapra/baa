// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>
//
// Test string parsing and serialization
use baa::*;
use proptest::prelude::*;

fn do_test_from_to_bit_str(s: &str) {
    let value = BitVecValue::from_bit_str(s).unwrap();
    let bit_str = if s.starts_with('-') {
        value.to_bit_str_signed()
    } else {
        value.to_bit_str()
    };
    compare_digit_str(&bit_str, &s.to_ascii_lowercase());
}

#[test]
fn test_from_to_bit_str_regression() {
    // do_test_from_to_bit_str("+0");
    do_test_from_to_bit_str("-0");
    do_test_from_to_bit_str("-1");
    do_test_from_to_bit_str("-11");
}

fn do_test_from_to_hex_str(s: &str) {
    let value = BitVecValue::from_hex_str(s).unwrap();
    let hex_str = if s.starts_with('-') {
        value.to_hex_str_signed()
    } else {
        value.to_hex_str()
    };
    compare_digit_str(&hex_str, &s.to_ascii_lowercase());
}

fn compare_digit_str(ours: &str, original: &str) {
    let expected = if let Some(e) = original.strip_prefix('+') {
        e.to_ascii_lowercase()
    } else {
        original.to_ascii_lowercase()
    };
    if let Some(wm) = expected.strip_prefix('-') {
        // if the original string was zero with any number of zeros, the result will always
        // be positive (we do not distinguish between -0 and +0, this is not floating point!!!
        if wm.chars().all(|c| c == '0') {
            assert_eq!(ours, wm);
        } else {
            assert_eq!(ours, expected);
        }
    } else {
        assert_eq!(ours, expected);
    }
}

#[test]
fn test_from_to_hex_str_regression() {
    do_test_from_to_hex_str("a");
    do_test_from_to_hex_str("A");
    do_test_from_to_hex_str("0aaaA0a0aAA0aaaA");
    do_test_from_to_hex_str("+A");
    do_test_from_to_hex_str("0");
    do_test_from_to_hex_str("+aaaa0aa0aaaa0aaa00a0aaaaaa00aa00");
    do_test_from_to_hex_str("-aaaa00aaaaaaaaa0");
}

fn do_test_to_from_decimal_str(s: &str) {
    let expected = BitVecValue::from_bit_str(s).unwrap();
    let dec_str = expected.to_dec_str();
    let actual = BitVecValue::from_str_radix(&dec_str, 10, expected.width()).unwrap();
    assert_eq!(expected, actual);
}

#[test]
fn test_to_from_dec_str_regression() {
    // the empty string is not allowed
    // TODO: turn into error instead of panic
    // do_test_to_from_decimal_str("");
    do_test_to_from_decimal_str("1000000");
}

#[test]
fn test_to_from_dec_str_small_value() {
    let dec_str = "34";
    let value = BitVecValue::from_str_radix(dec_str, 10, 512).unwrap();
    assert_eq!(value.to_u64().unwrap(), 34);
    assert_eq!(value.to_dec_str(), dec_str);
}

#[test]
fn test_to_from_dec_str_large_value() {
    let dec_str = "596886253802847701482483271715688189726967057213902170277048855852747875443594200622744233395250662615839263196891363475349438107920290669854978619157637";

    // converted using python, added a single leading zero for padding
    let eq_hex_str = "0b6584ec8ec7ccc11f45b8bb2fc98439f9e09d3d4bae2461b212c796d027d334a9defeda2bc5328aeeff4b5210d9e9dd25afe7d1b05660d2f22d22c7fce72c85";
    assert_eq!(eq_hex_str.len() * 4, 512);

    // test parse function
    let value = BitVecValue::from_str_radix(dec_str, 10, 512).unwrap();
    assert_eq!(value.to_hex_str(), eq_hex_str);
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(10000))]

    #[test]
    fn test_from_to_bit_str(s in "([-+])?[01]+") {
        do_test_from_to_bit_str(&s);
    }
    #[test]
    fn test_from_to_hex_str(s in "([-+])?[01a-fA-F]+") {
        do_test_from_to_hex_str(&s);
    }
    #[test]
    fn test_to_from_decimal_str(s in "([-+])?[01]+") {
        do_test_to_from_decimal_str(&s);
    }
}
