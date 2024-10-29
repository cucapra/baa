// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>
//
// Contains tests for bit vector comparison operations. We use num-bigint as a
// reference implementation.
use baa::*;
use num_bigint::*;
use proptest::prelude::*;

fn do_test_cmp_signed(
    a: BigInt,
    b: BigInt,
    width: WidthInt,
    our: fn(&BitVecValue, &BitVecValue) -> bool,
    big: fn(BigInt, BigInt) -> bool,
) {
    let a_vec = BitVecValue::from_big_int(&a, width);
    let b_vec = BitVecValue::from_big_int(&b, width);
    let res_bool = our(&a_vec, &b_vec);
    let expected_bool = big(a.clone(), b.clone());
    assert_eq!(expected_bool, res_bool, "{a} {b} {expected_bool}");
}

fn do_test_cmp_unsigned(
    a_signed: BigInt,
    b_signed: BigInt,
    width: WidthInt,
    our: fn(&BitVecValue, &BitVecValue) -> bool,
    big: fn(BigUint, BigUint) -> bool,
) {
    let a = a_signed.magnitude();
    let b = b_signed.magnitude();
    let a_vec = BitVecValue::from_big_uint(a, width);
    let b_vec = BitVecValue::from_big_uint(b, width);
    let res_bool = our(&a_vec, &b_vec);
    let expected_bool = big(a.clone(), b.clone());
    assert_eq!(expected_bool, res_bool, "{a} {b} {expected_bool}");
}

fn do_test_cmp_greater(a: BigInt, b: BigInt, width: WidthInt) {
    do_test_cmp_unsigned(a, b, width, |a, b| a.is_greater(b), |a, b| a > b)
}
fn do_test_cmp_greater_signed(a: BigInt, b: BigInt, width: WidthInt) {
    do_test_cmp_signed(a, b, width, |a, b| a.is_greater_signed(b), |a, b| a > b)
}

fn do_test_cmp_greater_equal(a: BigInt, b: BigInt, width: WidthInt) {
    do_test_cmp_unsigned(a, b, width, |a, b| a.is_greater_or_equal(b), |a, b| a >= b)
}
fn do_test_cmp_greater_equal_signed(a: BigInt, b: BigInt, width: WidthInt) {
    do_test_cmp_signed(
        a,
        b,
        width,
        |a, b| a.is_greater_or_equal_signed(b),
        |a, b| a >= b,
    )
}

fn do_test_cmp_equal(a: BigInt, b: BigInt, width: WidthInt) {
    do_test_cmp_unsigned(a, b, width, |a, b| a.is_equal(b), |a, b| a == b)
}
fn do_test_cmp_equal_signed(a: BigInt, b: BigInt, width: WidthInt) {
    do_test_cmp_signed(a, b, width, |a, b| a.is_equal(b), |a, b| a == b)
}

//////////////////////////
// Unit Tests
//////////////////////////

#[test]
fn do_test_cmp_greater_signed_regressions() {
    do_test_cmp_greater_signed(
        BigInt::parse_bytes(b"2812269376756553621043437133860079836754636903388049287067766551164406258259928767528960", 10).unwrap(),
        BigInt::parse_bytes(b"16927137481", 10).unwrap(),
        292
    );
}

//////////////////////////
// Random Tests
//////////////////////////
mod bitvec_arithmetic;
use bitvec_arithmetic::gen_big_int_pair;

proptest! {
    #![proptest_config(ProptestConfig::with_cases(5000))]


    #[test]
    fn test_cmp_greater((a, b, width) in gen_big_int_pair()) {
        do_test_cmp_greater(a, b, width);
    }

     #[test]
    fn test_cmp_greater_signed((a, b, width) in gen_big_int_pair()) {
        do_test_cmp_greater_signed(a, b, width);
    }

    #[test]
    fn test_cmp_greater_equal((a, b, width) in gen_big_int_pair()) {
        do_test_cmp_greater_equal(a, b, width);
    }

     #[test]
    fn test_cmp_greater_equal_signed((a, b, width) in gen_big_int_pair()) {
        do_test_cmp_greater_equal_signed(a, b, width);
    }

    #[test]
    fn test_cmp_equal((a, b, width) in gen_big_int_pair()) {
        do_test_cmp_equal(a, b, width);
    }

     #[test]
    fn test_cmp_equal_signed((a, b, width) in gen_big_int_pair()) {
        do_test_cmp_equal_signed(a, b, width);
    }
}
