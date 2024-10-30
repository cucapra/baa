// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>
//
// Contains tests for arithmetic bit vector operations. We use num-bigint as a
// reference implementation.
// We currently test: add, sub, mul
#[cfg(feature = "bigint")]
use baa::*;
#[cfg(feature = "bigint")]
use num_bigint::*;
use proptest::prelude::*;

#[cfg(feature = "bigint")]
fn do_test_arith(
    a: BigInt,
    b: BigInt,
    width: WidthInt,
    our: fn(&BitVecValue, &BitVecValue) -> BitVecValue,
    big: fn(BigInt, BigInt) -> BigInt,
) {
    let a_vec = BitVecValue::from_big_int(&a, width);
    let b_vec = BitVecValue::from_big_int(&b, width);
    let res = our(&a_vec, &b_vec);

    // check result
    let expected_mask = (BigInt::from(1) << width) - 1;
    let expected_num: BigInt = big(a.clone(), b.clone()) & expected_mask;
    // after masking, only the magnitude counts
    let expected = BitVecValue::from_big_uint(expected_num.magnitude(), width);
    assert_eq!(expected, res, "{a} {b} {expected_num}");
}

#[cfg(feature = "bigint")]
fn do_test_add(a: BigInt, b: BigInt, width: WidthInt) {
    do_test_arith(a, b, width, |a, b| a.add(b), |a, b| a + b)
}

#[cfg(feature = "bigint")]
fn do_test_sub(a: BigInt, b: BigInt, width: WidthInt) {
    do_test_arith(a, b, width, |a, b| a.sub(b), |a, b| a - b)
}

#[cfg(feature = "bigint")]
fn do_test_mul(a: BigInt, b: BigInt, width: WidthInt) {
    do_test_arith(a, b, width, |a, b| a.mul(b), |a, b| a * b)
}

//////////////////////////
// generators for proptest
//////////////////////////

#[cfg(feature = "bigint")]
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

#[cfg(feature = "bigint")]
fn gen_big_int(bits: WidthInt) -> impl Strategy<Value = BigInt> {
    gen_big_uint(bits - 1)
        .prop_flat_map(|unsigned| (any::<bool>(), Just(unsigned)))
        .prop_map(|(negative, unsigned)| {
            let sign = if negative { Sign::Minus } else { Sign::Plus };
            BigInt::from_biguint(sign, unsigned)
        })
}

#[cfg(feature = "bigint")]
// generates two big ints of equal bit width
pub fn gen_big_int_pair() -> impl Strategy<Value = (BigInt, BigInt, WidthInt)> {
    let max_bits = 16 * Word::BITS;
    (1..max_bits)
        .prop_flat_map(|bits| (Just(bits), 1..(bits + 1)))
        .prop_flat_map(|(width, second_width)| {
            prop_oneof![
                (gen_big_int(width), gen_big_int(second_width), Just(width)),
                (gen_big_int(second_width), gen_big_int(width), Just(width)),
            ]
        })
}

//////////////////////////
// Unit Tests
//////////////////////////
#[test]
#[cfg(feature = "bigint")]
fn test_sub_regressions() {
    do_test_sub(BigInt::from(-32), BigInt::from(32), 7);
}

#[test]
#[cfg(feature = "bigint")]
fn test_mul_regressions() {
    do_test_mul(
        BigInt::from(1099511627776i64),
        BigInt::from(1099511627776i64),
        50,
    );
    do_test_mul(BigInt::from(0), BigInt::from(0), 108);
    do_test_mul(
        BigInt::from(20282409603651670423947251286016i128),
        BigInt::from(5350908559360i128),
        108,
    )
}

//////////////////////////
// Random Tests
//////////////////////////

proptest! {
    #![proptest_config(ProptestConfig::with_cases(5000))]

    #[test]
    #[cfg(feature = "bigint")]
    fn test_add((a, b, width) in gen_big_int_pair()) {
        do_test_add(a, b, width);
    }

    #[test]
    #[cfg(feature = "bigint")]
    fn test_sub((a, b, width) in gen_big_int_pair()) {
        do_test_sub(a, b, width);
    }

    #[test]
    #[cfg(feature = "bigint")]
    fn test_mul((a, b, width) in gen_big_int_pair()) {
        do_test_mul(a, b, width);
    }
}
