mod array;
mod bv;

/// This type restricts the maximum width that a bit-vector type is allowed to have.
pub type WidthInt = u32;

/// Word size for values.
pub type Word = u64;

pub type DoubleWord = u128;

const _: () = assert!(Word::BITS * 2 == DoubleWord::BITS);

/// Wraps either an array or a bit vector value.
#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    Array(ArrayValue),
    BitVec(BitVecValue),
}

impl TryFrom<Value> for ArrayValue {
    type Error = ();

    fn try_from(value: Value) -> Result<Self, Self::Error> {
        match value {
            Value::Array(v) => Ok(v),
            Value::BitVec(_) => Err(()),
        }
    }
}

impl TryFrom<Value> for BitVecValue {
    type Error = ();

    fn try_from(value: Value) -> Result<Self, Self::Error> {
        match value {
            Value::BitVec(v) => Ok(v),
            Value::Array(_) => Err(()),
        }
    }
}

impl TryFrom<Value> for u64 {
    type Error = ();

    fn try_from(value: Value) -> Result<Self, Self::Error> {
        let value: BitVecValue = value.try_into()?;
        value.to_u64().ok_or(())
    }
}

impl Value {
    pub fn try_into_u64(self) -> Result<u64, ()> {
        <Self as TryInto<u64>>::try_into(self)
    }
}

pub use array::*;
pub use bv::*;
