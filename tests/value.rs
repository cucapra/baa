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
}

#[test]
fn test_value_container_to_u64() {
    let value = Value::BitVec(BitVecValue::from_u128(123, 128));
    assert_eq!(value.try_into(), Ok(123));
    let value = Value::BitVec(BitVecValue::from_u128(u128::MAX >> 10, 128));
    assert!(<Value as TryInto<u64>>::try_into(value).is_err());
}
