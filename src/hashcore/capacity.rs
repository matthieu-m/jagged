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
        //  With buckets loaded at half-capacity, the behavior is irregular
        //  for buckets with a capacity of 1 -- and irregular complicates code.
        let capacity_of_0 = cmp::max(capacity_of_0, 2);
        Self(self::capacity::Capacity::new(capacity_of_0, max_buckets))
    }

    //  Returns the maximum number of buckets.
    pub fn max_buckets(self) -> NumberBuckets { self.0.max_buckets() }

    //  Returns the maximum capacity.
    pub fn max_capacity(self) -> usize {
        //  Effective capacity is 50% due to load factor of 0.5.
        self.0.max_capacity() / 2
    }

    //  Returns the capacity of a given bucket.
    pub fn of_bucket(self, bucket: BucketIndex) -> BucketCapacity {
        self.0.of_bucket(bucket)
    }

    //  Returns the capacity before a given bucket.
    pub fn before_bucket(self, bucket: BucketIndex) -> BucketCapacity {
        self.0.before_bucket(bucket)
    }

    //  Returns the number of buckets necessary to accomodate `size` elements.
    //
    //  This assumes a load of 0.5, and that buckets of capacity 1 are fully loaded.
    pub fn number_buckets(self, size: Size) -> NumberBuckets {
        if size.0 == 0 {
            NumberBuckets(0)
        } else if size.0 - 1 > usize::MAX / 2 {
            NumberBuckets(self.max_buckets().0 + 1)
        } else {
            let index = ElementIndex((size.0 - 1) * 2);
            NumberBuckets(self.0.bucket_of(index).0 + 1)
        }
    }

    //  Returns the length of the initialized part of the Bucket.
    pub fn size_bucket(self, bucket: BucketIndex, size: Size)
        -> BucketSize
    {
        let prior = self.before_bucket(bucket);
        let current = self.of_bucket(bucket);

        let size = size.0 - prior.0 / 2;

        BucketSize(cmp::min(size, current.0 / 2))
    }
}

/// The number of elements in a Bucket.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct BucketSize(pub usize);

/// The number of elements in all Buckets.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct Size(pub usize);

#[cfg(test)]
mod tests {

use super::*;

#[test]
fn capacity_max_capacity() {
    fn max_capacity(n: usize) -> usize {
        let capacity = Capacity::new(n, 20);
        capacity.max_capacity()
    }

    assert_eq!(512 * 1024, max_capacity(1));
    assert_eq!(512 * 1024, max_capacity(2));
    assert_eq!(1024 * 1024, max_capacity(3));
    assert_eq!(1024 * 1024, max_capacity(4));
    assert_eq!(4 * 1024 * 1024, max_capacity(16));
}

#[test]
fn capacity_number_buckets_2() {
    fn number_buckets(n: usize) -> usize {
        let capacity = Capacity::new(2, 20);
        capacity.number_buckets(Size(n)).0
    }

    //  [0] = [X.]
    //  [1] = [X.]
    //  [2] = [XX..]
    //  [3] = [XXXX....]
    //  ...

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

    const MAX_CAPACITY: usize = 1usize << 19;

    assert_eq!(20, number_buckets(MAX_CAPACITY));
    assert_eq!(21, number_buckets(MAX_CAPACITY + 1));
    assert_eq!(21, number_buckets(usize::MAX / 2 + 1));
    assert_eq!(21, number_buckets(usize::MAX));
}

#[test]
fn capacity_number_buckets_4() {
    fn number_buckets(n: usize) -> usize {
        let capacity = Capacity::new(4, 20);
        capacity.number_buckets(Size(n)).0
    }

    //  [0] = [XX..]
    //  [1] = [XX..]
    //  [2] = [XXXX....]
    //  [3] = [XXXXXXXX........]
    //  ...

    assert_eq!(0, number_buckets(0));
    assert_eq!(1, number_buckets(1));
    assert_eq!(1, number_buckets(2));
    assert_eq!(2, number_buckets(3));
    assert_eq!(2, number_buckets(4));
    assert_eq!(3, number_buckets(5));
    assert_eq!(3, number_buckets(8));
    assert_eq!(4, number_buckets(9));
    assert_eq!(4, number_buckets(16));
    assert_eq!(5, number_buckets(17));

    const MAX_CAPACITY: usize = 1usize << 20;

    assert_eq!(20, number_buckets(MAX_CAPACITY));
    assert_eq!(21, number_buckets(MAX_CAPACITY + 1));
    assert_eq!(21, number_buckets(usize::MAX / 2 + 1));
    assert_eq!(21, number_buckets(usize::MAX));
}

#[test]
fn capacity_size_bucket_2() {
    fn size_bucket(bucket: usize, n: usize) -> usize {
        let capacity = Capacity::new(2, 20);
        capacity.size_bucket(BucketIndex(bucket), Size(n)).0
    }

    //  [0] = [X.]
    //  [1] = [X.]
    //  [2] = [XX..]
    //  [3] = [XXXX....]
    //  ...

    assert_eq!(0, size_bucket(0, 0));
    assert_eq!(1, size_bucket(0, 1));
    assert_eq!(1, size_bucket(0, 2));

    assert_eq!(0, size_bucket(1, 1));
    assert_eq!(1, size_bucket(1, 2));
    assert_eq!(1, size_bucket(1, 3));

    assert_eq!(0, size_bucket(2, 2));
    assert_eq!(1, size_bucket(2, 3));
    assert_eq!(2, size_bucket(2, 4));
    assert_eq!(2, size_bucket(2, 5));

    assert_eq!(0, size_bucket(3, 4));
    assert_eq!(1, size_bucket(3, 5));
    assert_eq!(4, size_bucket(3, 8));
    assert_eq!(4, size_bucket(3, 9));
}

#[test]
fn capacity_size_bucket_4() {
    fn size_bucket(bucket: usize, n: usize) -> usize {
        let capacity = Capacity::new(4, 20);
        capacity.size_bucket(BucketIndex(bucket), Size(n)).0
    }

    //  [0] = [XX..]
    //  [1] = [XX..]
    //  [2] = [XXXX....]
    //  [3] = [XXXXXXXX........]
    //  ...

    assert_eq!(0, size_bucket(0, 0));
    assert_eq!(1, size_bucket(0, 1));
    assert_eq!(2, size_bucket(0, 2));
    assert_eq!(2, size_bucket(0, 3));

    assert_eq!(0, size_bucket(1, 2));
    assert_eq!(1, size_bucket(1, 3));
    assert_eq!(2, size_bucket(1, 4));
    assert_eq!(2, size_bucket(1, 5));

    assert_eq!(0, size_bucket(2, 4));
    assert_eq!(1, size_bucket(2, 5));
    assert_eq!(4, size_bucket(2, 8));
    assert_eq!(4, size_bucket(2, 9));

    assert_eq!(0, size_bucket(3, 8));
    assert_eq!(1, size_bucket(3, 9));
    assert_eq!(8, size_bucket(3, 16));
    assert_eq!(8, size_bucket(3, 17));
}

}
