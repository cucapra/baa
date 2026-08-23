// Copyright 2023-2024 The Regents of the University of California
// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use baa::*;
use proptest::prelude::*;

#[test]
fn i64_roundtrip_regression() {
    assert_eq!(BitVecValue::from_i64(0, 64).to_i64().unwrap(), 0);
    assert_eq!(BitVecValue::from_i64(-1, 64).to_i64().unwrap(), -1);
}

#[test]
#[cfg(feature = "bigint")]
fn i32_to_ibig_regression() {
    let input = 0;
    let val = BitVecValue::from_i64(input as i64, 32);
    assert_eq!(val.to_big_int(), input.into())
}

fn without_trailing_zeros(v: &[u8]) -> &[u8] {
    let num_trailing_zeros = v.iter().rev().take_while(|v| **v == 0).count();
    &v[0..v.len() - num_trailing_zeros]
}

fn without_leading_zeros(v: &[u8]) -> &[u8] {
    let num_leading_zeros = v.iter().take_while(|v| **v == 0).count();
    &v[num_leading_zeros..]
}

fn do_bytes_le_roundtrip(b: Vec<u8>) {
    let width = if b.is_empty() {
        // a width of 0 is currently unsupported, so we treat &[] as a 1-bit zero.
        1
    } else {
        // try to avoid making width always a multiple of 8
        (b.len() - 1) * u8::BITS as usize
            + std::cmp::max(8 - b.last().unwrap().leading_zeros() as usize, 1)
    } as u32;
    let bitvec = BitVecValue::from_bytes_le(&b, width);
    let out = bitvec.to_bytes_le();
    assert_eq!(without_trailing_zeros(&out), without_trailing_zeros(&b));
}

fn do_bytes_be_roundtrip(b: Vec<u8>) {
    let width = if b.is_empty() {
        // a width of 0 is currently unsupported, so we treat &[] as a 1-bit zero.
        1
    } else {
        // try to avoid making width always a multiple of 8
        (b.len() - 1) * u8::BITS as usize
            + std::cmp::max(8 - b.first().unwrap().leading_zeros() as usize, 1)
    } as u32;
    let bitvec = BitVecValue::from_bytes_be(&b, width);
    let out = bitvec.to_bytes_be();
    assert_eq!(without_leading_zeros(&out), without_leading_zeros(&b));
}

#[test]
fn bytes_be_roundtrip_regression() {
    do_bytes_be_roundtrip(vec![1]);
}

proptest! {

    #[test]
    fn i64_roundtrip(value: i64) {
        let bitvec = BitVecValue::from_i64(value, 64);
        prop_assert_eq!(bitvec.to_i64().unwrap(), value);
    }

    #[test]
    fn u64_roundtrip(value: u64) {
        let bitvec = BitVecValue::from_u64(value, 64);
        prop_assert_eq!(bitvec.to_u64().unwrap(), value);
    }

    #[test]
    #[cfg(feature = "bigint")]
    fn i32_to_ibig(input: i32) {
        let val = BitVecValue::from_i64(input as i64, 32);
        prop_assert_eq!(val.to_big_int(), input.into())
    }

    #[test]
    fn bytes_le_roundtrip(b: Vec<u8>) {
        do_bytes_le_roundtrip(b)
    }

    #[test]
    fn bytes_be_roundtrip(b: Vec<u8>) {
        do_bytes_be_roundtrip(b)
    }
}

#[test]
fn test_value_container_to_u64() {
    let value = Value::BitVec(BitVecValue::from_u128(123, 128));
    assert_eq!(value.try_into(), Ok(123));
    let value = Value::BitVec(BitVecValue::from_u128(u128::MAX >> 10, 128));
    assert!(<Value as TryInto<u64>>::try_into(value).is_err());
}
