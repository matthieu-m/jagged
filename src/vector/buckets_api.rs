//! The high-level API of the Buckets of the vector.

pub use super::buckets::BucketArray;

use super::root::{cmp, fmt, hash, iter};

use super::allocator::Allocator;
use super::buckets::MAX_BUCKETS;
use super::capacity::{Capacity, BucketIndex, ElementIndex, Length};
use super::failure::{Failure, Result};

//  Shared Reader
pub struct BucketsSharedReader<'a, T> {
    buckets: &'a BucketArray<T>,
    length: Length,
    capacity: Capacity,
}

impl<'a, T> BucketsSharedReader<'a, T> {
    //  Creates a new instance.
    //
    //  #   Safety
    //
    //  -   Assumes that length is less than the current length.
    pub unsafe fn new(
        buckets: &'a BucketArray<T>,
        length: Length,
        capacity: Capacity
    )
        -> Self
    {
        Self { buckets, length, capacity }
    }

    //  Returns whether the instance contains any element, or not.
    pub fn is_empty(&self) -> bool { self.length.0 == 0 }

    //  Returns the number of elements contained in the instance.
    pub fn len(&self) -> usize { self.length.0 }

    //  Returns the current capacity of the instance.
    pub fn capacity(&self) -> usize {
        let nb_buckets = self.number_buckets();
        self.capacity.before_bucket(BucketIndex(nb_buckets)).0
    }

    //  Returns the maximum capacity achievable by the instance.
    pub fn max_capacity(&self) -> usize { self.capacity.max_capacity() }

    //  Returns the number of buckets currently used.
    pub fn number_buckets(&self) -> usize {
        let length = Length(self.len());
        self.capacity.number_buckets(length).0
    }

    //  Returns the maximum number of buckets.
    pub fn max_buckets(&self) -> usize { self.capacity.max_buckets().0 }

    //  Returns a reference to the ith element, if any.
    pub fn get(&self, index: ElementIndex) -> Option<&'a T> {
        //  Safety:
        //  -   length is less than the current length of the vector.
        unsafe { self.buckets.get(index, self.length, self.capacity) }
    }

    //  Returns a reference to the ith element, if any.
    //
    //  #   Safety
    //
    //  -   Assumes that `index` is less than the `self.len()`
    pub unsafe fn get_unchecked(&self, index: ElementIndex) -> &'a T {
        //  Safety:
        //  -   `index` is less than `length`.
        //  -   `length` is less than the current length of the vector.
        self.buckets.get_unchecked(index, self.capacity)
    }

    //  Returns a slice comprising the initialized part of the Bucket.
    pub fn bucket(&self, bucket: BucketIndex) -> &'a [T] {
        let nb_buckets = self.capacity.number_buckets(self.length);
        debug_assert!(nb_buckets <= self.capacity.max_buckets());

        if bucket.0 >= nb_buckets.0 {
            return &[];
        }

        //  Safety:
        //  -   length is less than the current length of the vector.
        unsafe {
            self.buckets.initialized_bucket(bucket, self.length, self.capacity)
        }
    }

    //  Returns an iterator to iterate over the buckets.
    pub fn iter_buckets(&self) -> BucketIterator<'a, T> {
        BucketIterator::create(self)
    }
}

impl<'a, T: fmt::Debug> BucketsSharedReader<'a, T> {
    //  Formats the Debug representation of the buckets.
    pub fn debug(&self, name: &str, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} {{ capacity: {}, length: {}, buckets: [",
            name, self.capacity(), self.len())?;

        for (index, bucket) in self.iter_buckets().enumerate() {
            if index != 0 {
                write!(f, ", ")?;
            }
            write!(f, "{:?}", bucket)?;
        }

        write!(f, "] }}")
    }
}

impl<'a, T: PartialEq> BucketsSharedReader<'a, T> {
    fn equal_direct(&self, other: &Self) -> bool {
        debug_assert!(self.length == other.length);
        debug_assert!(self.capacity == other.capacity);

        for index in 0..self.number_buckets() {
            let index = BucketIndex(index);

            if self.bucket(index) != other.bucket(index) {
                return false;
            }
        }

        true
    }

    fn equal_iter(&self, other: &Self) -> bool {
        debug_assert!(self.length == other.length);

        for (a, b) in self.into_iter().zip(other.into_iter()) {
            if a != b {
                return false;
            }
        }

        true
    }
}

impl<'a, T: PartialOrd> BucketsSharedReader<'a, T> {
    fn partial_compare_direct(&self, other: &Self) -> Option<cmp::Ordering> {
        debug_assert!(self.capacity == other.capacity);

        let smaller = self.length < other.length;
        let buckets =
            if smaller { self.number_buckets() } else { other.number_buckets() };

        for index in 0..buckets {
            let index = BucketIndex(index);

            let result = self.bucket(index).partial_cmp(other.bucket(index));

            if result != Some(cmp::Ordering::Equal) {
                return result;
            }
        }

        self.length.partial_cmp(&other.length)
    }

    fn partial_compare_iter(&self, other: &Self) -> Option<cmp::Ordering> {
        for (a, b) in self.into_iter().zip(other.into_iter()) {
            let result = a.partial_cmp(b);

            if result != Some(cmp::Ordering::Equal) {
                return result;
            }
        }

        self.length.partial_cmp(&other.length)
    }
}

impl<'a, T: Ord> BucketsSharedReader<'a, T> {
    fn compare_direct(&self, other: &Self) -> cmp::Ordering {
        debug_assert!(self.capacity == other.capacity);

        let smaller = self.length < other.length;
        let buckets =
            if smaller { self.number_buckets() } else { other.number_buckets() };

        for index in 0..buckets {
            let index = BucketIndex(index);

            let result = self.bucket(index).cmp(other.bucket(index));

            if result != cmp::Ordering::Equal {
                return result;
            }
        }

        self.length.cmp(&other.length)
    }

    fn compare_iter(&self, other: &Self) -> cmp::Ordering {
        for (a, b) in self.into_iter().zip(other.into_iter()) {
            let result = a.cmp(b);

            if result != cmp::Ordering::Equal {
                return result;
            }
        }

        self.length.cmp(&other.length)
    }
}

impl<'a, T> Clone for BucketsSharedReader<'a, T> {
    fn clone(&self) -> Self { *self }
}

impl<'a, T> Copy for BucketsSharedReader<'a, T> {}

impl<'a, T: hash::Hash> hash::Hash for BucketsSharedReader<'a, T> {
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        for bucket in self.iter_buckets() {
            bucket.hash(state);
        }
    }
}

impl<'a, T: Eq> Eq for BucketsSharedReader<'a, T> {}

impl<'a, T: PartialEq> PartialEq for BucketsSharedReader<'a, T> {
    fn eq(&self, other: &Self) -> bool {
        if self.length != other.length {
            return false;
        }

        if self.buckets as *const _ == other.buckets as *const _ {
            return true;
        }

        if self.capacity == other.capacity {
            self.equal_direct(other)
        } else {
            self.equal_iter(other)
        }
    }
}

impl<'a, T: Ord> Ord for BucketsSharedReader<'a, T> {
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        if self.length == other.length &&
            self.buckets as *const _ == other.buckets as *const _
        {
            return cmp::Ordering::Equal;
        }

        if self.capacity == other.capacity {
            self.compare_direct(other)
        } else {
            self.compare_iter(other)
        }
    }
}

impl<'a, T: PartialOrd> PartialOrd for BucketsSharedReader<'a, T> {
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        if self.length == other.length &&
            self.buckets as *const _ == other.buckets as *const _
        {
            return Some(cmp::Ordering::Equal);
        }

        if self.capacity == other.capacity {
            self.partial_compare_direct(other)
        } else {
            self.partial_compare_iter(other)
        }
    }
}

impl<'a, T> iter::IntoIterator for BucketsSharedReader<'a, T> {
    type Item = &'a T;
    type IntoIter = ElementIterator<'a, T>;

    fn into_iter(self) -> ElementIterator<'a, T> {
        ElementIterator::create(self)
    }
}

//  Shared Writer
pub struct BucketsSharedWriter<'a, T> {
    buckets: &'a BucketArray<T>,
    length: Length,
    capacity: Capacity,
}

impl<'a, T> BucketsSharedWriter<'a, T> {
    //  Creates a new instance.
    //
    //  #   Safety
    //
    //  -   Assumes than length exactly matches the current length.
    //  -   Assumes a single writer thread.
    pub unsafe fn new(
        buckets: &'a BucketArray<T>,
        length: Length,
        capacity: Capacity
    )
        -> Self
    {
        Self { buckets, length, capacity }
    }

    //  Shrinks the buckets, releasing unused memory.
    pub fn shrink<A: Allocator>(self, allocator: &A) {
        //  Safety:
        //  -   length is the current length of the vector.
        //  -   invalidating the instance is unnecessary, but shrink being
        //      idempotent, there is no point in calling it twice in a row.
        unsafe { self.buckets.shrink(self.length, self.capacity, allocator) }
    }

    //  Reserves buckets for up to `extra` elements.
    //
    //  #   Error
    //
    //  Returns an error if sufficient space cannot be reserved.
    pub fn try_reserve<A: Allocator>(&self, extra: Length, allocator: &A)
        -> Result<()>
    {
        //  Safety:
        //  -   single writer thread.
        unsafe {
            self.buckets.try_reserve(extra, self.length, self.capacity, allocator)
        }
    }

    //  Appends an element to the back.
    // 
    //  #   Errors
    // 
    //  Returns an error if the value cannot be pushed.
    pub fn try_push<A: Allocator>(self, value: T, allocator: &A)
        -> Result<Length>
    {
        //  Safety:
        //  -   length is the current length of the vector.
        //  -   the instance is invalidated by pushing, as length is modified.
        //  -   single writer thread.
        unsafe {
            self.buckets.try_push(value, self.length, self.capacity, allocator)
        }
    }

    //  Appends the elements to the back.
    // 
    //  Returns the new length of the vector.
    //
    //  #   Errors
    //
    //  Returns an error if the vector cannot be fully extended.
    pub fn try_extend<C, A>(self, collection: C, allocator: &A)
        -> (Length, Option<Failure>)
    where
        C: IntoIterator<Item = T>,
        A: Allocator,
    {
        //  Safety:
        //  -   length is the current length of the vector.
        //  -   the instance is invalidated by pushing, as length is modified.
        //  -   single writer thread.
        unsafe {
            self.buckets
                .try_extend(collection, self.length, self.capacity, allocator)
        }
    }
}

//  Exclusive Writer
pub struct BucketsExclusiveWriter<'a, T> {
    buckets: &'a mut BucketArray<T>,
    length: Length,
    capacity: Capacity,
}

impl<'a, T> BucketsExclusiveWriter<'a, T> {
    //  Creates a new instance.
    //
    //  #   Safety
    //
    //  -   Assumes than length exactly matches the current length.
    pub unsafe fn new(
        buckets: &'a mut BucketArray<T>,
        length: Length,
        capacity: Capacity
    )
        -> Self
    {
        Self { buckets, length, capacity }
    }

    //  Returns a slice comprising the initialized part of the Bucket.
    pub fn bucket_mut(self, bucket: BucketIndex) -> &'a mut [T] {
        let nb_buckets = self.capacity.number_buckets(self.length);
        debug_assert!(nb_buckets <= self.capacity.max_buckets());

        if bucket.0 >= nb_buckets.0 {
            return &mut [];
        }

        //  Safety:
        //  -   length is less than the current length of the vector.
        unsafe {
            self.buckets.initialized_bucket_mut(bucket, self.length, self.capacity)
        }
    }

    //  Clears the buckets.
    pub fn clear(self) {
        //  Safety:
        //  -   length is the current length of the vector.
        //  -   the instance is invalidated by clearing, as length is modified.
        unsafe { self.buckets.clear(self.length, self.capacity) }
    }
}

/// BucketIterator
///
/// An iterator over the buckets of a Vector.
///
/// While less ergonomic, it can be faster to take advantage of the chunked
/// nature of the underlying storage rather than incur bounds checks cost for
/// every element.
pub struct BucketIterator<'a, T> {
    buckets: [&'a [T]; MAX_BUCKETS],
    index: BucketIndex,
}

impl<'a, T> BucketIterator<'a, T> {
    //  Creates an instance of BucketIterator.
    fn create(reader: &BucketsSharedReader<'a, T>) -> Self {
        let mut result = BucketIterator {
            buckets: Default::default(),
            index: BucketIndex(0),
        };

        for index in 0..reader.number_buckets() {
            let index = BucketIndex(index);
            result.buckets[index.0] = reader.bucket(index);
        }

        result
    }
}

impl<'a, T> iter::Iterator for BucketIterator<'a, T> {
    type Item = &'a [T];

    fn next(&mut self) -> Option<&'a [T]> {
        if self.index.0 > self.buckets.len() {
            return None;
        }

        let slice = self.buckets[self.index.0];

        if slice.is_empty() {
            self.index = BucketIndex(MAX_BUCKETS);
            None
        } else {
            self.index = BucketIndex(self.index.0 + 1);
            Some(slice)
        }
    }
}

/// ElementIterator
///
/// An iterator over the elements of a Vector.
///
/// Due to the jagged nature of the Vector, it may be less efficient than a
/// BucketIterator.
pub struct ElementIterator<'a, T> {
    buckets: BucketsSharedReader<'a, T>,
    index: ElementIndex,
}

impl<'a, T> ElementIterator<'a, T> {
    //  Creates an instance of ElementIterator.
    fn create(reader: BucketsSharedReader<'a, T>) -> Self {
        ElementIterator { buckets: reader, index: ElementIndex(0) }
    }
}

impl<'a, T> iter::Iterator for ElementIterator<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        if let Some(e) = self.buckets.get(self.index) {
            self.index = ElementIndex(self.index.0 + 1);
            Some(e)
        } else {
            None
        }
    }
}
