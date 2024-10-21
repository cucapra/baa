mod array;
mod bv;

/// This type restricts the maximum width that a bit-vector type is allowed to have.
pub type WidthInt = u32;

/// Word size for values.
pub type Word = u64;

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

pub use array::*;
pub use bv::*;
