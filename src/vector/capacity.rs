//! The Vector capacity.

use crate::utils::capacity;

use super::root::cmp;

pub use self::capacity::{BucketCapacity, BucketIndex, ElementIndex, NumberBuckets};

//  Capacity.
//
//  A building block for computations related to the capacity of buckets.
#[derive(Clone, Copy, Debug, Hash, Eq, PartialEq, Ord, PartialOrd)]
pub struct Capacity(self::capacity::Capacity);

impl Capacity {
    //  Creates an instance, rounding to the next power of 2 if necessary.
    //
    //  #   Panics
    //
    //  Panics if `capacity_of_0` is greater than half `usize::MAX / 2 + 1`.
    pub fn new(capacity_of_0: usize, max_buckets: usize) -> Self {
        Self(self::capacity::Capacity::new(capacity_of_0, max_buckets))
    }

    //  Returns the maximum number of buckets.
    pub fn max_buckets(self) -> NumberBuckets { self.0.max_buckets() }

    //  Returns the maximum capacity.
    pub fn max_capacity(self) -> usize { self.0.max_capacity() }

    //  Returns the capacity of a given bucket.
    pub fn of_bucket(self, bucket: BucketIndex) -> BucketCapacity {
        self.0.of_bucket(bucket)
    }

    //  Returns the capacity before a given bucket.
    pub fn before_bucket(self, bucket: BucketIndex) -> BucketCapacity {
        self.0.before_bucket(bucket)
    }

    //  Returns the index of the Bucket in which the ith element can be found.
    //
    //  The result may be out of bounds.
    pub fn bucket_of(self, index: ElementIndex) -> BucketIndex {
        self.0.bucket_of(index)
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

/// The length of a Bucket.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct BucketLength(pub usize);

/// The index of an element within a Bucket.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct InnerIndex(pub usize);

/// The number of contiguous elements in all Buckets.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct Length(pub usize);

#[cfg(test)]
mod tests {

use super::*;

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

}
