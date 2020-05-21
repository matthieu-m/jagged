//! Capacity of the Jagged Array.
//!
//! Apart from holding the capacity itself, assembles various computing
//! primitives based off the capacity.

use super::root::{cmp, mem};

//  Capacity.
// 
//  A building block for computations related to the capacity of buckets.
#[derive(Clone, Copy, Debug, Hash, Eq, PartialEq, Ord, PartialOrd)]
pub struct Capacity {
    log2: u8,
    max_buckets: u8,
}

impl Capacity {
    //  Creates an instance, rounding to the next power of 2 if necessary.
    //
    //  #   Panics
    //
    //  Panics if `capacity_of_0` is greater than half `usize::MAX / 2 + 1`.
    pub fn new(capacity_of_0: usize, max_buckets: usize) -> Self {
        let log2 = ceil_log2(capacity_of_0);
        assert!(log2 < USIZE_BITS);

        let max_buckets = cmp::min(max_buckets, (USIZE_BITS - log2) as usize);
        debug_assert!(max_buckets < 256);

        Self { log2, max_buckets: max_buckets as u8 }
    }

    //  Returns the maximum number of buckets.
    pub fn max_buckets(self) -> NumberBuckets {
        NumberBuckets(self.max_buckets as usize)
    }

    //  Returns the maximum capacity.
    pub fn max_capacity(self) -> usize {
        self.before_bucket(BucketIndex(self.max_buckets as usize)).0
    }

    //  Returns the number of buckets necessary to accomodate `length` elements.
    pub fn number_buckets(self, length: Length) -> NumberBuckets {
        if length.0 == 0 {
            NumberBuckets(0)
        } else {
            let index = ElementIndex(length.0 - 1);
            NumberBuckets(self.bucket_of(index).0 + 1)
        }
    }

    //  Returns the capacity of a given bucket.
    pub fn of_bucket(self, bucket: BucketIndex) -> BucketCapacity {
        //  <= is used to allow querying for the total capacity.
        debug_assert!(bucket.0 <= self.max_buckets as usize);

        let multiplier = if bucket.0 == 0 {
                1
            } else {
                1usize << (bucket.0 - 1)
            };

        BucketCapacity(multiplier << self.log2)
    }

    //  Returns the capacity before a given bucket.
    pub fn before_bucket(self, bucket: BucketIndex) -> BucketCapacity {
        //  As each bucket beyond doubles the capacity of the vector, their
        //  capacity equals the sum of the capacity of all previous buckets.
        if bucket.0 == 0 { BucketCapacity(0) } else { self.of_bucket(bucket) }
    }

    //  Returns the index of the Bucket in which the ith element can be found.
    //
    //  The result may be out of bounds.
    pub fn bucket_of(self, index: ElementIndex) -> BucketIndex {
        let multiplier = index.0 >> self.log2;

        if multiplier == 0 {
            BucketIndex(0)
        } else {
            BucketIndex(floor_log2(multiplier) as usize + 1)
        }
    }

    //  Returns the index of the Bucket, and within the Bucket.
    pub fn indexes(self, index: ElementIndex) -> (BucketIndex, InnerIndex) {
        let outer = self.bucket_of(index);
        let prior = self.before_bucket(outer);

        (outer, InnerIndex(index.0 - prior.0))
    }

    //  Returns the length of the initialized part of the Bucket.
    pub fn len_bucket(self, bucket: BucketIndex, length: Length)
        -> BucketLength
    {
        let prior = self.before_bucket(bucket);
        let current = self.of_bucket(bucket);

        let length = length.0 - prior.0;

        BucketLength(cmp::min(length, current.0))
    }
}

/// The capacity of a Bucket.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct BucketCapacity(pub usize);

/// The index of a Bucket.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct BucketIndex(pub usize);

/// The length of a Bucket.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct BucketLength(pub usize);

/// The (global) index of an element.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct ElementIndex(pub usize);

/// The index of an element within a Bucket.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct InnerIndex(pub usize);

/// The number of contiguous elements in all Buckets.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct Length(pub usize);

/// The number of Buckets.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct NumberBuckets(pub usize);

//
//  Implementation Details
//

//  Number of bits in usize.
const USIZE_BITS: u8 = mem::size_of::<usize>() as u8 * 8;

//  Returns the log2 of n, rounded up to the next integer.
//
//  For practical purposes, the log2 of 0 is defined as 0.
fn ceil_log2(n: usize) -> u8 {
    match n {
        0 | 1 => 0,
        _ if n.count_ones() == 1 => USIZE_BITS - 1 - n.leading_zeros() as u8,
        _ => USIZE_BITS - n.leading_zeros() as u8,
    }
}

//  Returns the log2 of n, rounded down to the previous integer.
//
//  For practical purposes, the log2 of 0 is defined as 0.
fn floor_log2(n: usize) -> u8 {
    match n {
        0 | 1 => 0,
        _ => USIZE_BITS - 1 - n.leading_zeros() as u8,
    }
}

#[cfg(test)]
mod tests {

use super::*;

const HALF_USIZE: usize = 1usize << (USIZE_BITS - 1);

#[test]
fn capacity_new() {
    Capacity::new(HALF_USIZE, 22);
}

#[test]
#[should_panic]
fn capacity_new_too_large() {
    Capacity::new(HALF_USIZE + 1, 22);
}

#[test]
fn capacity_max_buckets_22() {
    fn max_buckets(log2: usize) -> usize {
        let capacity = Capacity::new(1usize << log2, 22);
        capacity.max_buckets().0
    }

    assert_eq!(22, max_buckets(0));
    assert_eq!(22, max_buckets(42));
    assert_eq!(21, max_buckets(43));
    assert_eq!(1, max_buckets(63));
}

#[test]
fn capacity_max_buckets_255() {
    fn max_buckets(log2: usize) -> usize {
        let capacity = Capacity::new(1usize << log2, 255);
        capacity.max_buckets().0
    }

    assert_eq!(64, max_buckets(0));
    assert_eq!(22, max_buckets(42));
    assert_eq!(21, max_buckets(43));
    assert_eq!(1, max_buckets(63));
}

#[test]
fn capacity_max_capacity_1() {
    fn max_capacity(number_buckets: u8) -> usize {
        let capacity = Capacity::new(1, number_buckets as usize);
        capacity.max_capacity()
    }

    assert_eq!(0, max_capacity(0));
    assert_eq!(1, max_capacity(1));
    assert_eq!(2_097_152, max_capacity(22));
    assert_eq!(536_870_912, max_capacity(30));
    assert_eq!(HALF_USIZE, max_capacity(USIZE_BITS));
}

#[test]
fn capacity_max_capacity_4() {
    fn max_capacity(number_buckets: u8) -> usize {
        let capacity = Capacity::new(4, number_buckets as usize);
        capacity.max_capacity()
    }

    assert_eq!(0, max_capacity(0));
    assert_eq!(4, max_capacity(1));
    assert_eq!(8_388_608, max_capacity(22));
    assert_eq!(2_147_483_648, max_capacity(30));
    assert_eq!(HALF_USIZE, max_capacity(USIZE_BITS));
}

#[test]
fn capacity_max_capacity_unlimited() {
    fn max_capacity(log2: u8) -> usize {
        let capacity = Capacity::new(1usize << log2, 255);
        capacity.max_capacity()
    }

    assert_eq!(HALF_USIZE, max_capacity(0));
    assert_eq!(HALF_USIZE, max_capacity(1));
    assert_eq!(HALF_USIZE, max_capacity(USIZE_BITS - 1));
}

#[test]
fn capacity_number_buckets_1() {
    fn number_buckets(n: usize) -> usize {
        let capacity = Capacity::new(1, 20);
        capacity.number_buckets(Length(n)).0
    }

    assert_eq!(0, number_buckets(0));
    assert_eq!(1, number_buckets(1));
    assert_eq!(2, number_buckets(2));
    assert_eq!(3, number_buckets(3));
    assert_eq!(3, number_buckets(4));
    assert_eq!(4, number_buckets(5));
    assert_eq!(4, number_buckets(8));
    assert_eq!(5, number_buckets(9));
    assert_eq!(5, number_buckets(16));
    assert_eq!(6, number_buckets(17));
    assert_eq!(6, number_buckets(32));
}

#[test]
fn capacity_number_buckets_4() {
    fn number_buckets(n: usize) -> usize {
        let capacity = Capacity::new(4, 20);
        capacity.number_buckets(Length(n)).0
    }

    assert_eq!(0, number_buckets(0));
    assert_eq!(1, number_buckets(1));
    assert_eq!(1, number_buckets(4));
    assert_eq!(2, number_buckets(5));
    assert_eq!(2, number_buckets(8));
    assert_eq!(3, number_buckets(9));
    assert_eq!(3, number_buckets(16));
    assert_eq!(4, number_buckets(17));
    assert_eq!(4, number_buckets(32));
}

#[test]
fn capacity_of_bucket_1() {
    fn of_bucket(n: usize) -> usize {
        let capacity = Capacity::new(1, 20);
        capacity.of_bucket(BucketIndex(n)).0
    }

    assert_eq!(1, of_bucket(0));
    assert_eq!(1, of_bucket(1));
    assert_eq!(2, of_bucket(2));
    assert_eq!(4, of_bucket(3));
    assert_eq!(8, of_bucket(4));
    assert_eq!(16, of_bucket(5));
}

#[test]
fn capacity_of_bucket_4() {
    fn of_bucket(n: usize) -> usize {
        let capacity = Capacity::new(4, 20);
        capacity.of_bucket(BucketIndex(n)).0
    }

    assert_eq!(4, of_bucket(0));
    assert_eq!(4, of_bucket(1));
    assert_eq!(8, of_bucket(2));
    assert_eq!(16, of_bucket(3));
    assert_eq!(32, of_bucket(4));
    assert_eq!(64, of_bucket(5));
}

#[test]
fn capacity_before_bucket_1() {
    fn before_bucket(n: usize) -> usize {
        let capacity = Capacity::new(1, 20);
        capacity.before_bucket(BucketIndex(n)).0
    }

    assert_eq!(0, before_bucket(0));
    assert_eq!(1, before_bucket(1));
    assert_eq!(2, before_bucket(2));
    assert_eq!(4, before_bucket(3));
    assert_eq!(8, before_bucket(4));
    assert_eq!(16, before_bucket(5));
}

#[test]
fn capacity_before_bucket_4() {
    fn before_bucket(n: usize) -> usize {
        let capacity = Capacity::new(4, 20);
        capacity.before_bucket(BucketIndex(n)).0
    }

    assert_eq!(0, before_bucket(0));
    assert_eq!(4, before_bucket(1));
    assert_eq!(8, before_bucket(2));
    assert_eq!(16, before_bucket(3));
    assert_eq!(32, before_bucket(4));
    assert_eq!(64, before_bucket(5));
}

#[test]
fn capacity_bucket_of_1() {
    fn bucket_of(n: usize) -> usize {
        let capacity = Capacity::new(1, 20);
        capacity.bucket_of(ElementIndex(n)).0
    }

    assert_eq!(0, bucket_of(0));
    assert_eq!(1, bucket_of(1));
    assert_eq!(2, bucket_of(2));
    assert_eq!(2, bucket_of(3));
    assert_eq!(3, bucket_of(4));
    assert_eq!(3, bucket_of(7));
    assert_eq!(4, bucket_of(8));
    assert_eq!(4, bucket_of(15));
}

#[test]
fn capacity_bucket_of_4() {
    fn bucket_of(n: usize) -> usize {
        let capacity = Capacity::new(4, 20);
        capacity.bucket_of(ElementIndex(n)).0
    }

    assert_eq!(0, bucket_of(0));
    assert_eq!(0, bucket_of(3));
    assert_eq!(1, bucket_of(4));
    assert_eq!(1, bucket_of(7));
    assert_eq!(2, bucket_of(8));
    assert_eq!(2, bucket_of(15));
    assert_eq!(3, bucket_of(16));
    assert_eq!(3, bucket_of(31));
}

#[test]
fn capacity_indexes_1() {
    fn indexes(n: usize) -> (usize, usize) {
        let capacity = Capacity::new(1, 20);
        let (outer, inner) = capacity.indexes(ElementIndex(n));
        (outer.0, inner.0)
    }

    assert_eq!((0, 0), indexes(0));
    assert_eq!((1, 0), indexes(1));
    assert_eq!((2, 0), indexes(2));
    assert_eq!((2, 1), indexes(3));
    assert_eq!((3, 0), indexes(4));
    assert_eq!((3, 3), indexes(7));
    assert_eq!((4, 0), indexes(8));
    assert_eq!((4, 7), indexes(15));
}

#[test]
fn capacity_indexes_4() {
    fn indexes(n: usize) -> (usize, usize) {
        let capacity = Capacity::new(4, 20);
        let (outer, inner) = capacity.indexes(ElementIndex(n));
        (outer.0, inner.0)
    }

    assert_eq!((0, 0), indexes(0));
    assert_eq!((0, 3), indexes(3));
    assert_eq!((1, 0), indexes(4));
    assert_eq!((1, 3), indexes(7));
    assert_eq!((2, 0), indexes(8));
    assert_eq!((2, 7), indexes(15));
    assert_eq!((3, 0), indexes(16));
    assert_eq!((3, 15), indexes(31));
}

#[test]
fn capacity_len_bucket_1() {
    fn len_bucket(bucket: usize, length: usize) -> usize {
        let capacity = Capacity::new(1, 20);
        capacity.len_bucket(BucketIndex(bucket), Length(length)).0
    }

    assert_eq!(0, len_bucket(0, 0));
    assert_eq!(1, len_bucket(0, 1));
    assert_eq!(0, len_bucket(1, 1));
    assert_eq!(1, len_bucket(1, 2));
    assert_eq!(0, len_bucket(2, 2));
    assert_eq!(1, len_bucket(2, 3));
    assert_eq!(2, len_bucket(2, 4));
    assert_eq!(0, len_bucket(3, 4));
    assert_eq!(1, len_bucket(3, 5));
    assert_eq!(4, len_bucket(3, 8));
    assert_eq!(0, len_bucket(4, 8));
    assert_eq!(1, len_bucket(4, 9));
    assert_eq!(8, len_bucket(4, 16));
}

#[test]
fn capacity_len_bucket_4() {
    fn len_bucket(bucket: usize, length: usize) -> usize {
        let capacity = Capacity::new(4, 20);
        capacity.len_bucket(BucketIndex(bucket), Length(length)).0
    }

    assert_eq!(0, len_bucket(0, 0));
    assert_eq!(1, len_bucket(0, 1));
    assert_eq!(4, len_bucket(0, 4));
    assert_eq!(0, len_bucket(1, 4));
    assert_eq!(1, len_bucket(1, 5));
    assert_eq!(4, len_bucket(1, 8));
    assert_eq!(0, len_bucket(2, 8));
    assert_eq!(1, len_bucket(2, 9));
    assert_eq!(8, len_bucket(2, 16));
    assert_eq!(0, len_bucket(3, 16));
    assert_eq!(1, len_bucket(3, 17));
    assert_eq!(16, len_bucket(3, 32));
}

#[test]
fn ceil_log2_zero() {
    assert_eq!(0, ceil_log2(0));
}

#[test]
fn ceil_log2_manual() {
    assert_eq!(0, ceil_log2(1));
    assert_eq!(1, ceil_log2(2));
    assert_eq!(2, ceil_log2(3));
    assert_eq!(2, ceil_log2(4));
    assert_eq!(3, ceil_log2(5));
    assert_eq!(3, ceil_log2(6));
    assert_eq!(3, ceil_log2(7));
    assert_eq!(3, ceil_log2(8));
}

#[test]
fn ceil_log2_exact() {
    for i in 0..31 {
        let n = 1usize << i;
        assert_eq!(i, ceil_log2(n));
    }
}

#[test]
fn ceil_log2_rounding_up() {
    for i in 2..31 {
        let n = (1usize << i) - 1;
        assert_eq!(i, ceil_log2(n));
    }
}

#[test]
fn floor_log2_zero() {
    assert_eq!(0, floor_log2(0));
}

#[test]
fn floor_log2_manual() {
    assert_eq!(0, floor_log2(1));
    assert_eq!(1, floor_log2(2));
    assert_eq!(1, floor_log2(3));
    assert_eq!(2, floor_log2(4));
    assert_eq!(2, floor_log2(5));
    assert_eq!(2, floor_log2(6));
    assert_eq!(2, floor_log2(7));
    assert_eq!(3, floor_log2(8));
}

#[test]
fn floor_log2_exact() {
    for i in 0..31 {
        let n = 1usize << i;
        assert_eq!(i, floor_log2(n));
    }
}

#[test]
fn floor_log2_rounding_down() {
    for i in 1..31 {
        let n = (1usize << i) - 1;
        assert_eq!(i - 1, floor_log2(n));
    }
}

}
