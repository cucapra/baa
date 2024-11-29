// Copyright 2023-2024 The Regents of the University of California
// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::array::ops::{ArrayMutOps, ArrayOps};
use crate::{
    BitVecMutOps, BitVecOps, BitVecValue, BitVecValueMutRef, BitVecValueRef, WidthInt, Word,
};
use std::collections::HashMap;
use std::fmt::{Debug, Formatter};

/// Owned Array Container.
#[derive(Clone)]
#[cfg_attr(feature = "serde1", derive(serde::Serialize, serde::Deserialize))]
pub struct ArrayValue {
    data: ArrayImpl,
}

#[derive(Clone)]
#[cfg_attr(feature = "serde1", derive(serde::Serialize, serde::Deserialize))]
enum ArrayImpl {
    Sparse(SparseArrayValue),
    Dense(DenseArrayValue),
}

impl Debug for ArrayValue {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match &self.data {
            ArrayImpl::Sparse(s) => s.fmt(f),
            ArrayImpl::Dense(d) => d.fmt(f),
        }
    }
}

impl ArrayValue {
    pub fn new_dense<'a>(index_width: WidthInt, default: impl Into<BitVecValueRef<'a>>) -> Self {
        let data = ArrayImpl::Dense(DenseArrayValue::new(index_width, default));
        Self { data }
    }
    pub fn new_sparse<'a>(index_width: WidthInt, default: impl Into<BitVecValueRef<'a>>) -> Self {
        let data = ArrayImpl::Sparse(SparseArrayValue::new(index_width, default));
        Self { data }
    }

    pub fn is_dense(&self) -> bool {
        matches!(self.data, ArrayImpl::Dense(_))
    }

    pub fn is_sparse(&self) -> bool {
        matches!(self.data, ArrayImpl::Sparse(_))
    }

    /// Turns the underlying storage into a dense representation if it is not already.
    pub fn make_dense(&mut self) {
        if self.is_dense() {
            // nothing to do
            return;
        }

        let value: DenseArrayValue = match &self.data {
            ArrayImpl::Dense(_) => {
                unreachable!("should have passed the self.is_dense check earlier!");
            }
            ArrayImpl::Sparse(data) => data.into(),
        };
        self.data = ArrayImpl::Dense(value);
    }

    /// Checks equivalence for two arrays of the same type (index_width x data_width).
    pub fn is_equal(&self, other: &Self) -> Option<bool> {
        match (&self.data, &other.data) {
            (ArrayImpl::Dense(a), ArrayImpl::Dense(b)) => a.is_equal(b),
            (ArrayImpl::Sparse(a), ArrayImpl::Sparse(b)) => a.is_equal(b),
            (ArrayImpl::Sparse(a), ArrayImpl::Dense(b)) => is_equal_mixed(b, a),
            (ArrayImpl::Dense(a), ArrayImpl::Sparse(b)) => is_equal_mixed(a, b),
        }
    }
}

impl From<&[bool]> for ArrayValue {
    fn from(value: &[bool]) -> Self {
        Self {
            data: ArrayImpl::Dense(value.into()),
        }
    }
}

impl From<&[u8]> for ArrayValue {
    fn from(value: &[u8]) -> Self {
        Self {
            data: ArrayImpl::Dense(value.into()),
        }
    }
}

impl From<&[u64]> for ArrayValue {
    fn from(value: &[u64]) -> Self {
        Self {
            data: ArrayImpl::Dense(value.into()),
        }
    }
}

impl From<ArrayValue> for SparseArrayValue {
    fn from(value: ArrayValue) -> Self {
        match value.data {
            ArrayImpl::Sparse(s) => s,
            ArrayImpl::Dense(d) => (&d).into(),
        }
    }
}

impl PartialEq<ArrayValue> for ArrayValue {
    fn eq(&self, other: &ArrayValue) -> bool {
        self.is_equal(other).unwrap_or_default()
    }
}

fn is_equal_mixed(dense: &DenseArrayValue, sparse: &SparseArrayValue) -> Option<bool> {
    // check early to avoid costly computations
    if dense.index_width != sparse.index_width || dense.data_width != sparse.data_width {
        return None;
    }

    // TODO: implement more efficient version which does not densify
    let other_dense = DenseArrayValue::from(sparse);
    other_dense.is_equal(dense)
}

impl ArrayOps for ArrayValue {
    fn index_width(&self) -> WidthInt {
        match &self.data {
            ArrayImpl::Sparse(v) => v.index_width(),
            ArrayImpl::Dense(v) => v.index_width(),
        }
    }

    fn data_width(&self) -> WidthInt {
        match &self.data {
            ArrayImpl::Sparse(v) => v.data_width(),
            ArrayImpl::Dense(v) => v.data_width(),
        }
    }

    fn select<'a>(&self, index: impl Into<BitVecValueRef<'a>>) -> BitVecValue {
        match &self.data {
            ArrayImpl::Sparse(v) => v.select(index),
            ArrayImpl::Dense(v) => v.select(index),
        }
    }
}

impl ArrayMutOps for ArrayValue {
    fn store<'a, 'b>(
        &mut self,
        index: impl Into<BitVecValueRef<'a>>,
        data: impl Into<BitVecValueRef<'b>>,
    ) {
        match &mut self.data {
            ArrayImpl::Sparse(v) => v.store(index, data),
            ArrayImpl::Dense(v) => v.store(index, data),
        }
    }

    fn clear(&mut self) {
        match &mut self.data {
            ArrayImpl::Sparse(v) => v.clear(),
            ArrayImpl::Dense(v) => v.clear(),
        }
    }
}

#[derive(Clone)]
#[cfg_attr(feature = "serde1", derive(serde::Serialize, serde::Deserialize))]
struct DenseArrayValue {
    index_width: WidthInt,
    data_width: WidthInt,
    data: DenseArrayImpl,
}

impl Debug for DenseArrayValue {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "DenseArrayValue(..)")
    }
}

#[inline]
fn index_width_from_len(len: usize) -> WidthInt {
    if len == 0 {
        0
    } else {
        usize::BITS - (len - 1).leading_zeros()
    }
}

#[inline]
fn num_elements_from_index_width(index_width: WidthInt) -> usize {
    1usize << index_width
}

impl From<&[bool]> for DenseArrayValue {
    fn from(values: &[bool]) -> Self {
        let index_width = index_width_from_len(values.len());
        let num_elements = num_elements_from_index_width(index_width);
        let mut data = BitVecValue::zero(num_elements as WidthInt);
        for (ii, v) in values.iter().enumerate() {
            if *v {
                data.set_bit(ii as WidthInt);
            }
        }
        Self {
            index_width,
            data_width: 1,
            data: DenseArrayImpl::Bit(data),
        }
    }
}

impl From<&[u8]> for DenseArrayValue {
    fn from(values: &[u8]) -> Self {
        let index_width = index_width_from_len(values.len());
        let num_elements = num_elements_from_index_width(index_width);
        let mut data: Vec<u8> = values.into();
        // pad with zeros if possible
        data.resize(num_elements, 0);
        data.shrink_to_fit();
        Self {
            index_width,
            data_width: 8,
            data: DenseArrayImpl::U8(data),
        }
    }
}

impl From<&[u64]> for DenseArrayValue {
    fn from(values: &[u64]) -> Self {
        let index_width = index_width_from_len(values.len());
        let num_elements = num_elements_from_index_width(index_width);
        let mut data: Vec<u64> = values.into();
        // pad with zeros if possible
        data.resize(num_elements, 0);
        data.shrink_to_fit();
        Self {
            index_width,
            data_width: 64,
            data: DenseArrayImpl::U64(data),
        }
    }
}

#[derive(Clone)]
#[cfg_attr(feature = "serde1", derive(serde::Serialize, serde::Deserialize))]
enum DenseArrayImpl {
    Bit(BitVecValue),
    U8(Vec<u8>),
    U64(Vec<u64>),
    Big(Vec<Word>),
}

/// 1 GiB max for a dense array, otherwise something is fishy!
const DENSE_ARRAY_MAX_BYTES: usize = 1024 * 1024 * 1024;

fn approx_dense_storage_size(index_width: WidthInt, data_width: WidthInt) -> usize {
    let elements = 1usize << index_width;
    if data_width == 1 {
        // using the Bit representation
        elements.div_ceil(u8::BITS as usize)
    } else if data_width <= u8::BITS {
        // using the U8 representation
        elements
    } else if data_width <= u64::BITS {
        // using the U64 representation
        elements * (u64::BITS / u8::BITS) as usize
    } else {
        // using the Big representation
        elements * data_width.div_ceil(Word::BITS) as usize
    }
}

impl DenseArrayValue {
    fn new<'a>(index_width: WidthInt, default: impl Into<BitVecValueRef<'a>>) -> Self {
        let default = default.into();
        let data_width = default.width();
        let storage_size = approx_dense_storage_size(index_width, data_width);
        debug_assert!(
            storage_size <= DENSE_ARRAY_MAX_BYTES,
            "array would take up too much space: {storage_size} bytes"
        );

        let elements = 1usize << index_width;
        let data = if data_width == 1 {
            if default.is_true() {
                DenseArrayImpl::Bit(BitVecValue::ones(elements as WidthInt))
            } else {
                debug_assert!(default.is_false());
                DenseArrayImpl::Bit(BitVecValue::zero(elements as WidthInt))
            }
        } else if data_width <= u8::BITS {
            let default = default.to_u64().unwrap() as u8;
            DenseArrayImpl::U8(vec![default; elements])
        } else if data_width <= u64::BITS {
            let default = default.to_u64().unwrap();
            DenseArrayImpl::U64(vec![default; elements])
        } else {
            let mut v = Vec::with_capacity(elements * default.words().len());
            for _ in 0..elements {
                v.extend_from_slice(default.words());
            }
            DenseArrayImpl::Big(v)
        };
        Self {
            index_width,
            data_width,
            data,
        }
    }

    /// Checks equivalence for two arrays of the same type (index_width x data_width).
    fn is_equal(&self, other: &Self) -> Option<bool> {
        if other.index_width != self.index_width || other.data_width != self.data_width {
            return None;
        }
        match (&self.data, &other.data) {
            (DenseArrayImpl::Bit(value_a), DenseArrayImpl::Bit(value_b)) => {
                Some(value_a.is_equal(value_b))
            }
            (DenseArrayImpl::U8(values_a), DenseArrayImpl::U8(values_b)) => {
                Some(values_a == values_b)
            }
            (DenseArrayImpl::U64(values_a), DenseArrayImpl::U64(values_b)) => {
                Some(values_a == values_b)
            }
            (DenseArrayImpl::Big(values_a), DenseArrayImpl::Big(values_b)) => {
                Some(values_a == values_b)
            }
            _ => unreachable!(
                "the representation for two arrays of the same type should always be the same!"
            ),
        }
    }

    fn select_usize(&self, index: usize) -> BitVecValue {
        match &self.data {
            DenseArrayImpl::Bit(value) => value.is_bit_set(index as WidthInt).into(),
            DenseArrayImpl::U8(values) => {
                BitVecValue::from_u64(values[index] as u64, self.data_width)
            }
            DenseArrayImpl::U64(values) => BitVecValue::from_u64(values[index], self.data_width),
            DenseArrayImpl::Big(values) => {
                let start = self.words_per_element() * index;
                let end = start + self.words_per_element();
                let value_ref = BitVecValueRef::new(&values[start..end], self.data_width());
                value_ref.into()
            }
        }
    }
}

impl ArrayOps for DenseArrayValue {
    fn index_width(&self) -> WidthInt {
        self.index_width
    }

    fn data_width(&self) -> WidthInt {
        self.data_width
    }

    fn select<'a>(&self, index: impl Into<BitVecValueRef<'a>>) -> BitVecValue {
        let index = index.into();
        debug_assert_eq!(index.width(), self.index_width);
        self.select_usize(index.to_u64().unwrap() as usize)
    }
}

impl ArrayMutOps for DenseArrayValue {
    fn store<'a, 'b>(
        &mut self,
        index: impl Into<BitVecValueRef<'a>>,
        data: impl Into<BitVecValueRef<'b>>,
    ) {
        let index = index.into();
        debug_assert_eq!(index.width(), self.index_width);
        let index = index.to_u64().unwrap() as usize;
        let data = data.into();
        debug_assert_eq!(data.width(), self.data_width);
        let data_width = self.data_width();
        let words_per_element = self.words_per_element();
        match &mut self.data {
            DenseArrayImpl::Bit(value) => {
                if data.is_true() {
                    value.set_bit(index as WidthInt);
                } else {
                    value.clear_bit(index as WidthInt);
                }
            }
            DenseArrayImpl::U8(values) => {
                values[index] = data.to_u64().unwrap() as u8;
            }
            DenseArrayImpl::U64(values) => {
                values[index] = data.to_u64().unwrap();
            }
            DenseArrayImpl::Big(values) => {
                let start = words_per_element * index;
                let end = start + words_per_element;
                let mut value_ref = BitVecValueMutRef::new(data_width, &mut values[start..end]);
                value_ref.assign(data);
            }
        }
    }

    fn clear(&mut self) {
        match &mut self.data {
            DenseArrayImpl::Bit(value) => value.clear(),
            DenseArrayImpl::U8(values) => values.iter_mut().for_each(|v| *v = 0),
            DenseArrayImpl::U64(values) => values.iter_mut().for_each(|v| *v = 0),
            DenseArrayImpl::Big(values) => values.iter_mut().for_each(|v| *v = 0),
        }
    }
}

impl From<&SparseArrayValue> for DenseArrayValue {
    fn from(value: &SparseArrayValue) -> Self {
        let mut dense = Self::new(value.index_width, &value.default());
        debug_assert_eq!(value.data_width, dense.data_width);
        debug_assert_eq!(value.index_width, dense.index_width);
        match &value.data {
            SparseArrayImpl::U64U64(_, m) => {
                for (index, v) in m.iter() {
                    match &mut dense.data {
                        DenseArrayImpl::Bit(value) => {
                            if *v == 1 {
                                value.set_bit(*index as WidthInt);
                            } else {
                                debug_assert_eq!(*v, 0);
                                value.clear_bit(*index as WidthInt);
                            }
                        }
                        DenseArrayImpl::U8(values) => {
                            values[*index as usize] = *v as u8;
                        }
                        DenseArrayImpl::U64(values) => {
                            values[*index as usize] = *v;
                        }
                        DenseArrayImpl::Big(_) => {
                            unreachable!("data_width does not match")
                        }
                    }
                }
            }
            SparseArrayImpl::U64Big(_, m) => {
                let mut index_bv = BitVecValue::zero(value.data_width);
                for (k, v) in m.iter() {
                    index_bv.assign_from_u64(*k);
                    dense.store(&index_bv, v);
                }
            }
            SparseArrayImpl::BigBig(_, _) => {
                unreachable!(
                    "index size is too large, creating the dense array should have failed!"
                )
            }
        }
        dense
    }
}

const MAX_HASH_TABLE_SIZE_FOR_DEFAULT_SEARCH: usize = 1024 * 1024;

impl From<&DenseArrayValue> for SparseArrayValue {
    fn from(value: &DenseArrayValue) -> Self {
        match &value.data {
            DenseArrayImpl::Bit(data) => {
                // find default value
                let mut count = [0usize; 2];
                for bit in 0..value.num_elements() {
                    count[data.is_bit_set(bit as WidthInt) as usize] += 1;
                }
                let default = count[1] > count[0];
                let bv_default = BitVecValue::from(default);
                let mut out = SparseArrayValue::new(value.index_width(), &bv_default);

                // find all indices that do not carry the default value
                for bit in 0..value.num_elements() {
                    if data.is_bit_set(bit as WidthInt) != default {
                        out.store_u64_u64(bit as u64, !default as u64);
                    }
                }
                out
            }
            DenseArrayImpl::U8(data) => {
                // find default value
                let mut count = [0usize; u8::BITS as usize];
                for bit in 0..value.num_elements() {
                    count[data[bit] as usize] += 1;
                }
                let default = count
                    .into_iter()
                    .enumerate()
                    .max_by_key(|(_, count)| *count)
                    .map(|(ii, _)| ii as u8)
                    .unwrap();
                let bv_default = BitVecValue::from_u64(default as u64, value.data_width());
                let mut out = SparseArrayValue::new(value.index_width(), &bv_default);

                // find all indices that do not carry the default value
                for (bit, &data) in data.iter().enumerate() {
                    if data != default {
                        out.store_u64_u64(bit as u64, data as u64);
                    }
                }
                out
            }
            DenseArrayImpl::U64(data) => {
                // find default value
                let mut count = HashMap::<u64, usize>::new();
                for &data in data.iter() {
                    *count.entry(data).or_insert(0) += 1;
                    if count.len() > MAX_HASH_TABLE_SIZE_FOR_DEFAULT_SEARCH {
                        // if our hash table is exploding in size
                        // => give up and just use the data we have collected so far
                        break;
                    }
                }
                let default = count
                    .into_iter()
                    .max_by_key(|(_, count)| *count)
                    .map(|(v, _)| v)
                    .unwrap();
                let bv_default = BitVecValue::from_u64(default, value.data_width());
                let mut out = SparseArrayValue::new(value.index_width(), &bv_default);

                // find all indices that do not carry the default value
                for (bit, &data) in data.iter().enumerate() {
                    if data != default {
                        out.store_u64_u64(bit as u64, data);
                    }
                }
                out
            }
            DenseArrayImpl::Big(_) => {
                // find default value
                let mut count = HashMap::<BitVecValue, usize>::new();
                for bit in 0..value.num_elements() {
                    let value = value.select_usize(bit);
                    *count.entry(value).or_insert(0) += 1;
                    if count.len() > MAX_HASH_TABLE_SIZE_FOR_DEFAULT_SEARCH {
                        // if our hash table is exploding in size
                        // => give up and just use the data we have collected so far
                        break;
                    }
                }
                let default = count
                    .into_iter()
                    .max_by_key(|(_, count)| *count)
                    .map(|(v, _)| v)
                    .unwrap();
                let mut out = SparseArrayValue::new(value.index_width(), &default);

                // find all indices that do not carry the default value
                for bit in 0..value.num_elements() {
                    let value = value.select_usize(bit);
                    if value != default {
                        out.store_u64_big(bit as u64, &value);
                    }
                }
                out
            }
        }
    }
}

#[derive(Clone)]
#[cfg_attr(feature = "serde1", derive(serde::Serialize, serde::Deserialize))]
pub struct SparseArrayValue {
    index_width: WidthInt,
    data_width: WidthInt,
    data: SparseArrayImpl,
}

impl Debug for SparseArrayValue {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "SparseArrayValue(..)")
    }
}

#[derive(Clone)]
#[cfg_attr(feature = "serde1", derive(serde::Serialize, serde::Deserialize))]
enum SparseArrayImpl {
    U64U64(u64, HashMap<u64, u64>),
    U64Big(BitVecValue, HashMap<u64, BitVecValue>),
    BigBig(BitVecValue, HashMap<BitVecValue, BitVecValue>),
}

impl SparseArrayValue {
    pub fn new<'a>(index_width: WidthInt, default: impl Into<BitVecValueRef<'a>>) -> Self {
        let default = default.into();
        let data_width = default.width();
        let data = if index_width > Word::BITS {
            SparseArrayImpl::BigBig(default.into(), HashMap::new())
        } else if data_width > Word::BITS {
            SparseArrayImpl::U64Big(default.into(), HashMap::new())
        } else {
            SparseArrayImpl::U64U64(default.to_u64().unwrap(), HashMap::new())
        };
        Self {
            index_width,
            data_width,
            data,
        }
    }

    /// Checks equivalence for two arrays of the same type (index_width x data_width).
    fn is_equal(&self, other: &Self) -> Option<bool> {
        if other.index_width != self.index_width || other.data_width != self.data_width {
            return None;
        }
        match (&self.data, &other.data) {
            (
                SparseArrayImpl::U64U64(default_a, map_a),
                SparseArrayImpl::U64U64(default_b, map_b),
            ) => {
                if default_a == default_b {
                    // here we rely on the fact that the default value may never appear in the map
                    if map_a.len() == map_b.len() {
                        return Some(map_a == map_b);
                    }
                }
                Some(false)
            }
            (
                SparseArrayImpl::U64Big(default_a, map_a),
                SparseArrayImpl::U64Big(default_b, map_b),
            ) => {
                if default_a == default_b {
                    // here we rely on the fact that the default value may never appear in the map
                    if map_a.len() == map_b.len() {
                        return Some(map_a == map_b);
                    }
                }
                Some(false)
            }
            (
                SparseArrayImpl::BigBig(default_a, map_a),
                SparseArrayImpl::BigBig(default_b, map_b),
            ) => {
                if default_a == default_b {
                    // here we rely on the fact that the default value may never appear in the map
                    if map_a.len() == map_b.len() {
                        return Some(map_a == map_b);
                    }
                }
                Some(false)
            }
            _ => unreachable!(
                "the representation for two arrays of the same type should always be the same!"
            ),
        }
    }

    pub fn default(&self) -> BitVecValue {
        match &self.data {
            SparseArrayImpl::U64U64(default, _) => BitVecValue::from_u64(*default, self.data_width),
            SparseArrayImpl::U64Big(default, _) => default.clone(),
            SparseArrayImpl::BigBig(default, _) => default.clone(),
        }
    }

    fn store_u64_u64(&mut self, index: u64, data: u64) {
        match &mut self.data {
            SparseArrayImpl::U64U64(default, map) => {
                if data == *default {
                    // ensures that the default value is used for the given index
                    map.remove(&index);
                } else {
                    map.insert(index, data);
                }
            }
            _ => panic!("store_u64_u64 can only be used when index and data bit width is at or under 64 bit.")
        }
    }

    fn store_u64_big<'b>(&mut self, index: u64, data: impl Into<BitVecValueRef<'b>>) {
        let data = data.into();
        match &mut self.data {
            SparseArrayImpl::U64U64(default, map) => {
                let data = data.to_u64().unwrap();
                if data == *default {
                    // ensures that the default value is used for the given index
                    map.remove(&index);
                } else {
                    map.insert(index, data);
                }
            }
            SparseArrayImpl::U64Big(default, map) => {
                if data.is_equal(default) {
                    // ensures that the default value is used for the given index
                    map.remove(&index);
                } else {
                    map.insert(index, data.into());
                }
            }
            _ => panic!(
                "store_u64_big can only be used when the index bit width is at or under 64 bit."
            ),
        }
    }

    /// Returns an iterator to all index/data pairs that do not evaluate to the default value.
    /// Note that the order of entries is non-deterministic. Convert to a Vec and sort of you
    /// want to ensure a predictable outcome.
    pub fn non_default_entries(&self) -> SparseArrayEntryIter {
        let underlying = match &self.data {
            SparseArrayImpl::U64U64(_, m) => SparseArrayIterImpl::U64U64(m.iter()),
            SparseArrayImpl::U64Big(_, m) => SparseArrayIterImpl::U64Big(m.iter()),
            SparseArrayImpl::BigBig(_, m) => SparseArrayIterImpl::BigBig(m.iter()),
        };
        let (index_width, data_width) = (self.index_width, self.data_width);
        SparseArrayEntryIter {
            index_width,
            data_width,
            underlying,
        }
    }
}

pub struct SparseArrayEntryIter<'a> {
    index_width: WidthInt,
    data_width: WidthInt,
    underlying: SparseArrayIterImpl<'a>,
}

enum SparseArrayIterImpl<'a> {
    U64U64(std::collections::hash_map::Iter<'a, u64, u64>),
    U64Big(std::collections::hash_map::Iter<'a, u64, BitVecValue>),
    BigBig(std::collections::hash_map::Iter<'a, BitVecValue, BitVecValue>),
}

impl Iterator for SparseArrayEntryIter<'_> {
    type Item = (BitVecValue, BitVecValue);

    fn next(&mut self) -> Option<Self::Item> {
        match &mut self.underlying {
            SparseArrayIterImpl::U64U64(iter) => {
                let (index, value) = iter.next()?;
                Some((
                    BitVecValue::from_u64(*index, self.index_width),
                    BitVecValue::from_u64(*value, self.data_width),
                ))
            }
            SparseArrayIterImpl::U64Big(iter) => {
                let (index, value) = iter.next()?;
                Some((
                    BitVecValue::from_u64(*index, self.index_width),
                    value.clone(),
                ))
            }
            SparseArrayIterImpl::BigBig(iter) => {
                let (index, value) = iter.next()?;
                Some((index.clone(), value.clone()))
            }
        }
    }
}

impl ArrayOps for SparseArrayValue {
    fn index_width(&self) -> WidthInt {
        self.index_width
    }
    fn data_width(&self) -> WidthInt {
        self.data_width
    }
    fn select<'a>(&self, index: impl Into<BitVecValueRef<'a>>) -> BitVecValue {
        let index = index.into();
        debug_assert_eq!(index.width(), self.index_width);
        match &self.data {
            SparseArrayImpl::U64U64(default, map) => {
                let index = index.to_u64().unwrap();
                let value = map.get(&index).copied().unwrap_or(*default);
                BitVecValue::from_u64(value, self.data_width)
            }
            SparseArrayImpl::U64Big(default, map) => {
                let index = index.to_u64().unwrap();
                let value = map.get(&index).cloned().unwrap_or_else(|| default.clone());
                value
            }
            SparseArrayImpl::BigBig(default, map) => {
                let value = map.get(&index).cloned().unwrap_or_else(|| default.clone());
                value
            }
        }
    }
}

impl ArrayMutOps for SparseArrayValue {
    fn store<'a, 'b>(
        &mut self,
        index: impl Into<BitVecValueRef<'a>>,
        data: impl Into<BitVecValueRef<'b>>,
    ) {
        let index = index.into();
        debug_assert_eq!(index.width(), self.index_width);
        let data = data.into();
        debug_assert_eq!(data.width(), self.data_width);
        match &mut self.data {
            SparseArrayImpl::U64U64(default, map) => {
                let index = index.to_u64().unwrap();
                let data = data.to_u64().unwrap();
                if data == *default {
                    // ensures that the default value is used for the given index
                    map.remove(&index);
                } else {
                    map.insert(index, data);
                }
            }
            SparseArrayImpl::U64Big(default, map) => {
                let index = index.to_u64().unwrap();
                if data.is_equal(default) {
                    // ensures that the default value is used for the given index
                    map.remove(&index);
                } else {
                    map.insert(index, data.into());
                }
            }
            SparseArrayImpl::BigBig(default, map) => {
                if data.is_equal(default) {
                    // ensures that the default value is used for the given index
                    map.remove(&index);
                } else {
                    map.insert(index.into(), data.into());
                }
            }
        }
    }

    fn clear(&mut self) {
        match &mut self.data {
            SparseArrayImpl::U64U64(default, map) => {
                *default = 0;
                map.clear();
            }
            SparseArrayImpl::U64Big(default, map) => {
                *default = BitVecValue::zero(self.data_width);
                map.clear();
            }
            SparseArrayImpl::BigBig(default, map) => {
                *default = BitVecValue::zero(self.data_width);
                map.clear();
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn type_size() {
        // Dense Array Size
        assert_eq!(std::mem::size_of::<Vec<u8>>(), 24);
        assert_eq!(std::mem::size_of::<BitVecValue>(), 3 * 8);
        assert_eq!(std::mem::size_of::<DenseArrayImpl>(), 4 * 8); // BitVecValue size + tag + padding
        assert_eq!(std::mem::size_of::<DenseArrayValue>(), (4 + 1) * 8); // Impl + size + padding

        // Sparse Array Size

        // the hash table size is independent of the key/value types
        assert_eq!(std::mem::size_of::<HashMap<u64, u64>>(), 48);
        assert_eq!(std::mem::size_of::<HashMap<u64, BitVecValue>>(), 48);
        assert_eq!(std::mem::size_of::<HashMap<BitVecValue, BitVecValue>>(), 48);

        // HashMap + BitVecValue + tag + padding
        assert_eq!(std::mem::size_of::<SparseArrayImpl>(), 48 + 24 + 8);
        assert_eq!(std::mem::size_of::<SparseArrayValue>(), 80 + 8); // Impl + size + padding
    }

    #[test]
    fn test_index_width_from_len() {
        assert_eq!(index_width_from_len(0), 0);
        assert_eq!(index_width_from_len(1), 0);
        assert_eq!(index_width_from_len(2), 1);
        assert_eq!(index_width_from_len(3), 2);
        assert_eq!(index_width_from_len(8), 3);
        assert_eq!(index_width_from_len(9), 4);
    }

    #[test]
    fn test_conversions_bool() {
        let dense0: DenseArrayValue = [true, false, false, false, true].as_slice().into();
        let sparse0: SparseArrayValue = (&dense0).into();
        let dense1: DenseArrayValue = (&sparse0).into();
        assert!(is_equal_mixed(&dense0, &sparse0).unwrap());
        assert!(dense0.is_equal(&dense1).unwrap());
    }

    #[test]
    fn test_conversions_u8() {
        let dense0: DenseArrayValue = [1u8, 2, 3, 4, 5, 6, 1, 1, 1].as_slice().into();
        let sparse0: SparseArrayValue = (&dense0).into();
        let dense1: DenseArrayValue = (&sparse0).into();
        assert!(is_equal_mixed(&dense0, &sparse0).unwrap());
        assert!(dense0.is_equal(&dense1).unwrap());
    }

    #[test]
    fn test_conversions_u64() {
        let dense0: DenseArrayValue = [1u64, 2, 3, 4, 5, 6, 1, 1, 1].as_slice().into();
        let sparse0: SparseArrayValue = (&dense0).into();
        let dense1: DenseArrayValue = (&sparse0).into();
        assert!(is_equal_mixed(&dense0, &sparse0).unwrap());
        assert!(dense0.is_equal(&dense1).unwrap());
    }
}
