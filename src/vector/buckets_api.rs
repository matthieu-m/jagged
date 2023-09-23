//! The high-level API of the Buckets of the vector.

pub use super::buckets::BucketArray;

use super::root::{cmp, fmt, hash, iter};

use super::allocator::Allocator;
use super::buckets::MAX_BUCKETS;
use super::capacity::{BucketIndex, Capacity, ElementIndex, Length};
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
    pub unsafe fn new(buckets: &'a BucketArray<T>, length: Length, capacity: Capacity) -> Self {
        Self {
            buckets,
            length,
            capacity,
        }
    }

    //  Returns whether the instance contains any element, or not.
    pub fn is_empty(&self) -> bool {
        self.length.0 == 0
    }

    //  Returns the number of elements contained in the instance.
    pub fn len(&self) -> usize {
        self.length.0
    }

    //  Returns the current capacity of the instance.
    pub fn capacity(&self) -> usize {
        let nb_buckets = self.number_buckets();
        self.capacity.before_bucket(BucketIndex(nb_buckets)).0
    }

    //  Returns the maximum capacity achievable by the instance.
    pub fn max_capacity(&self) -> usize {
        self.capacity.max_capacity()
    }

    //  Returns the number of buckets currently used.
    pub fn number_buckets(&self) -> usize {
        let length = Length(self.len());
        self.capacity.number_buckets(length).0
    }

    //  Returns the maximum number of buckets.
    pub fn max_buckets(&self) -> usize {
        self.capacity.max_buckets().0
    }

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
        unsafe { self.buckets.initialized_bucket(bucket, self.length, self.capacity) }
    }

    //  Returns an iterator to iterate over the buckets.
    pub fn iter_buckets(&self) -> BucketIterator<'a, T> {
        BucketIterator::create(self)
    }
}

impl<'a, T: fmt::Debug> BucketsSharedReader<'a, T> {
    //  Formats the Debug representation of the buckets.
    pub fn debug(&self, name: &str, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{} {{ capacity: {}, length: {}, buckets: [",
            name,
            self.capacity(),
            self.len()
        )?;

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
        let buckets = if smaller {
            self.number_buckets()
        } else {
            other.number_buckets()
        };

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
        let buckets = if smaller {
            self.number_buckets()
        } else {
            other.number_buckets()
        };

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
    fn clone(&self) -> Self {
        *self
    }
}

impl<'a, T> Copy for BucketsSharedReader<'a, T> {}

impl<'a, T: fmt::Debug> fmt::Debug for BucketsSharedReader<'a, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.debug("BucketsSharedReader", f)
    }
}

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

        if self.capacity == other.capacity {
            self.equal_direct(other)
        } else {
            self.equal_iter(other)
        }
    }
}

impl<'a, T: Ord> Ord for BucketsSharedReader<'a, T> {
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        if self.length == other.length && self.buckets as *const _ == other.buckets as *const _ {
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
    pub unsafe fn new(buckets: &'a BucketArray<T>, length: Length, capacity: Capacity) -> Self {
        Self {
            buckets,
            length,
            capacity,
        }
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
    pub fn try_reserve<A: Allocator>(&self, extra: Length, allocator: &A) -> Result<()> {
        //  Safety:
        //  -   single writer thread.
        unsafe { self.buckets.try_reserve(extra, self.length, self.capacity, allocator) }
    }

    //  Appends an element to the back.
    //
    //  #   Errors
    //
    //  Returns an error if the value cannot be pushed.
    pub fn try_push<A: Allocator>(self, value: T, allocator: &A) -> Result<Length> {
        //  Safety:
        //  -   length is the current length of the vector.
        //  -   the instance is invalidated by pushing, as length is modified.
        //  -   single writer thread.
        unsafe { self.buckets.try_push(value, self.length, self.capacity, allocator) }
    }

    //  Appends the elements to the back.
    //
    //  Returns the new length of the vector.
    //
    //  #   Errors
    //
    //  Returns an error if the vector cannot be fully extended.
    pub fn try_extend<C, A>(self, collection: C, allocator: &A) -> (Length, Option<Failure>)
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
    pub unsafe fn new(buckets: &'a mut BucketArray<T>, length: Length, capacity: Capacity) -> Self {
        Self {
            buckets,
            length,
            capacity,
        }
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
        unsafe { self.buckets.initialized_bucket_mut(bucket, self.length, self.capacity) }
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
/// While less ergonomic, it can be faster to take advantage of the chunked nature of the underlying storage rather than
/// incur bounds checks cost for every element.
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
        if self.index.0 >= self.buckets.len() {
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
/// Due to the jagged nature of the Vector, it may be less efficient than a BucketIterator.
pub struct ElementIterator<'a, T> {
    buckets: BucketsSharedReader<'a, T>,
    index: ElementIndex,
}

impl<'a, T> ElementIterator<'a, T> {
    //  Creates an instance of ElementIterator.
    fn create(reader: BucketsSharedReader<'a, T>) -> Self {
        ElementIterator {
            buckets: reader,
            index: ElementIndex(0),
        }
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

#[cfg(test)]
mod tests {

    use super::*;

    use crate::utils::tester::*;

    fn construct<T, C, A>(collection: C, capacity: Capacity, allocator: &A) -> (Length, BucketArray<T>)
    where
        C: iter::IntoIterator<Item = T>,
        A: Allocator,
    {
        let buckets = BucketArray::default();

        let (length, failure) = unsafe { buckets.try_extend(collection, Length(0), capacity, allocator) };

        assert_eq!(None, failure);

        (length, buckets)
    }

    unsafe fn shared_reader<'a, T>(
        buckets: &'a BucketArray<T>,
        length: Length,
        capacity: Capacity,
    ) -> BucketsSharedReader<'a, T> {
        BucketsSharedReader::new(buckets, length, capacity)
    }

    unsafe fn shared_writer<'a, T>(
        buckets: &'a BucketArray<T>,
        length: Length,
        capacity: Capacity,
    ) -> BucketsSharedWriter<'a, T> {
        BucketsSharedWriter::new(buckets, length, capacity)
    }

    unsafe fn exclusive_writer<'a, T>(
        buckets: &'a mut BucketArray<T>,
        length: Length,
        capacity: Capacity,
    ) -> BucketsExclusiveWriter<'a, T> {
        BucketsExclusiveWriter::new(buckets, length, capacity)
    }

    #[test]
    fn reader_copy() {
        fn ensure_copy<T: Copy>(_: T) {}

        let allocator = TestAllocator::unlimited();

        let capacity = Capacity::new(1, MAX_BUCKETS);

        let (_, buckets) = construct(vec!["Hello".to_string()], capacity, &allocator);

        {
            let reader = unsafe { shared_reader(&buckets, Length(1), capacity) };
            ensure_copy(reader);
        }

        let mut buckets = buckets;
        unsafe { buckets.clear(Length(1), capacity) };
    }

    #[test]
    fn reader_properties() {
        let allocator = TestAllocator::unlimited();

        let capacity = Capacity::new(1, MAX_BUCKETS);

        let (length, buckets) = construct(vec![1], capacity, &allocator);

        let reader = unsafe { shared_reader(&buckets, Length(0), capacity) };
        assert!(reader.is_empty());
        assert_eq!(0, reader.len());
        assert_eq!(0, reader.number_buckets());

        assert_eq!(0, reader.capacity());
        assert_eq!(2 * 1024 * 1024, reader.max_capacity());
        assert_eq!(MAX_BUCKETS, reader.max_buckets());

        let reader = unsafe { shared_reader(&buckets, length, capacity) };
        assert!(!reader.is_empty());
        assert_eq!(1, reader.len());
        assert_eq!(1, reader.number_buckets());

        assert_eq!(1, reader.capacity());
        assert_eq!(2 * 1024 * 1024, reader.max_capacity());
        assert_eq!(MAX_BUCKETS, reader.max_buckets());
    }

    #[test]
    fn reader_get() {
        let allocator = TestAllocator::unlimited();

        let capacity = Capacity::new(1, MAX_BUCKETS);

        let (_, buckets) = construct(vec![1, 2, 3], capacity, &allocator);

        let reader = unsafe { shared_reader(&buckets, Length(0), capacity) };
        assert_eq!(None, reader.get(ElementIndex(0)));

        let reader = unsafe { shared_reader(&buckets, Length(2), capacity) };
        assert_eq!(Some(&2), reader.get(ElementIndex(1)));
        assert_eq!(None, reader.get(ElementIndex(2)));
    }

    #[test]
    fn reader_get_unchecked() {
        let allocator = TestAllocator::unlimited();

        let capacity = Capacity::new(1, MAX_BUCKETS);

        let (_, buckets) = construct(vec![1, 2, 3], capacity, &allocator);

        let reader = unsafe { shared_reader(&buckets, Length(0), capacity) };
        assert_eq!(&3, unsafe { reader.get_unchecked(ElementIndex(2)) });
    }

    #[test]
    fn reader_bucket() {
        const EMPTY: &'static [i32] = &[];

        let allocator = TestAllocator::unlimited();

        let capacity = Capacity::new(2, MAX_BUCKETS);

        let (_, buckets) = construct(vec![1, 2, 3, 4, 5], capacity, &allocator);

        let reader = unsafe { shared_reader(&buckets, Length(0), capacity) };
        assert_eq!(EMPTY, reader.bucket(BucketIndex(0)));

        let reader = unsafe { shared_reader(&buckets, Length(1), capacity) };
        assert_eq!(&[1], reader.bucket(BucketIndex(0)));

        let reader = unsafe { shared_reader(&buckets, Length(2), capacity) };
        assert_eq!(&[1, 2], reader.bucket(BucketIndex(0)));
        assert_eq!(EMPTY, reader.bucket(BucketIndex(1)));

        let reader = unsafe { shared_reader(&buckets, Length(3), capacity) };
        assert_eq!(&[1, 2], reader.bucket(BucketIndex(0)));
        assert_eq!(&[3], reader.bucket(BucketIndex(1)));

        let reader = unsafe { shared_reader(&buckets, Length(4), capacity) };
        assert_eq!(&[1, 2], reader.bucket(BucketIndex(0)));
        assert_eq!(&[3, 4], reader.bucket(BucketIndex(1)));
        assert_eq!(EMPTY, reader.bucket(BucketIndex(2)));

        let reader = unsafe { shared_reader(&buckets, Length(5), capacity) };
        assert_eq!(&[1, 2], reader.bucket(BucketIndex(0)));
        assert_eq!(&[3, 4], reader.bucket(BucketIndex(1)));
        assert_eq!(&[5], reader.bucket(BucketIndex(2)));
    }

    #[test]
    fn reader_debug() {
        let allocator = TestAllocator::unlimited();

        let capacity = Capacity::new(2, MAX_BUCKETS);

        let (_, buckets) = construct(vec![1, 2, 3, 4, 5], capacity, &allocator);

        let reader = unsafe { shared_reader(&buckets, Length(0), capacity) };
        assert_eq!(
            "BucketsSharedReader { capacity: 0, length: 0, buckets: [] }",
            format!("{:?}", reader)
        );

        let reader = unsafe { shared_reader(&buckets, Length(5), capacity) };
        assert_eq!(
            "BucketsSharedReader { capacity: 8, length: 5, buckets: [[1, 2], [3, 4], [5]] }",
            format!("{:?}", reader)
        );
    }

    #[test]
    fn reader_equal_same_underlying() {
        let allocator = TestAllocator::unlimited();

        let capacity = Capacity::new(2, MAX_BUCKETS);

        let (_, buckets) = construct(vec![1, 2, 3, 4, 5], capacity, &allocator);

        let left = unsafe { shared_reader(&buckets, Length(0), capacity) };
        let right = unsafe { shared_reader(&buckets, Length(1), capacity) };

        assert_ne!(left, right);

        let left = unsafe { shared_reader(&buckets, Length(3), capacity) };
        let right = unsafe { shared_reader(&buckets, Length(3), capacity) };

        assert_eq!(left, right);
    }

    #[test]
    fn reader_equal_different_underlying() {
        let allocator = TestAllocator::unlimited();

        let capacity = Capacity::new(2, MAX_BUCKETS);

        let (_, left_buckets) = construct(vec![1, 2, 3, 4], capacity, &allocator);
        let (_, right_buckets) = construct(vec![1, 2, 4, 8], capacity, &allocator);

        let left = unsafe { shared_reader(&left_buckets, Length(2), capacity) };
        let right = unsafe { shared_reader(&right_buckets, Length(2), capacity) };

        assert_eq!(left, right);

        let left = unsafe { shared_reader(&left_buckets, Length(3), capacity) };
        let right = unsafe { shared_reader(&right_buckets, Length(3), capacity) };

        assert_ne!(left, right);
    }

    #[test]
    fn reader_equal_different_capacity() {
        let allocator = TestAllocator::unlimited();

        let left_capacity = Capacity::new(1, MAX_BUCKETS);
        let right_capacity = Capacity::new(2, MAX_BUCKETS);

        let (_, left_buckets) = construct(vec![1, 2, 3, 4, 5], left_capacity, &allocator);
        let (_, right_buckets) = construct(vec![1, 2, 3, 5, 7], right_capacity, &allocator);

        let left = unsafe { shared_reader(&left_buckets, Length(0), left_capacity) };
        let right = unsafe { shared_reader(&right_buckets, Length(1), right_capacity) };

        assert_ne!(left, right);

        let left = unsafe { shared_reader(&left_buckets, Length(3), left_capacity) };
        let right = unsafe { shared_reader(&right_buckets, Length(3), right_capacity) };

        assert_eq!(left, right);

        let left = unsafe { shared_reader(&left_buckets, Length(5), left_capacity) };
        let right = unsafe { shared_reader(&right_buckets, Length(5), right_capacity) };

        assert_ne!(left, right);
    }

    #[test]
    fn reader_hash() {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};

        let allocator = TestAllocator::unlimited();

        let capacity = Capacity::new(2, MAX_BUCKETS);

        let (_, buckets) = construct(vec![1, 2, 3, 4, 5], capacity, &allocator);

        let reader = unsafe { shared_reader(&buckets, Length(5), capacity) };

        let mut hasher = DefaultHasher::new();
        reader.hash(&mut hasher);
        assert_eq!(4282359133143147680, hasher.finish());
    }

    #[test]
    fn reader_partialord_same_underlying() {
        let allocator = TestAllocator::unlimited();

        let capacity = Capacity::new(2, MAX_BUCKETS);

        let (_, buckets) = construct(vec![1.0, 2.0, f64::NAN], capacity, &allocator);

        let left = unsafe { shared_reader(&buckets, Length(0), capacity) };
        let right = unsafe { shared_reader(&buckets, Length(1), capacity) };

        assert_eq!(Some(cmp::Ordering::Less), left.partial_cmp(&right));
        assert_eq!(Some(cmp::Ordering::Greater), right.partial_cmp(&left));

        let left = unsafe { shared_reader(&buckets, Length(2), capacity) };
        let right = unsafe { shared_reader(&buckets, Length(2), capacity) };

        assert_eq!(Some(cmp::Ordering::Equal), left.partial_cmp(&right));

        let left = unsafe { shared_reader(&buckets, Length(3), capacity) };
        let right = unsafe { shared_reader(&buckets, Length(3), capacity) };

        assert_eq!(None, left.partial_cmp(&right));
    }

    #[test]
    fn reader_partialord_different_underlying() {
        let allocator = TestAllocator::unlimited();

        let capacity = Capacity::new(2, MAX_BUCKETS);

        let (_, left_buckets) = construct(vec![1.0, 2.0, f64::NAN], capacity, &allocator);
        let (_, right_buckets) = construct(vec![1.0, 2.0, f64::NAN], capacity, &allocator);

        let left = unsafe { shared_reader(&left_buckets, Length(0), capacity) };
        let right = unsafe { shared_reader(&right_buckets, Length(1), capacity) };

        assert_eq!(Some(cmp::Ordering::Less), left.partial_cmp(&right));
        assert_eq!(Some(cmp::Ordering::Greater), right.partial_cmp(&left));

        let left = unsafe { shared_reader(&left_buckets, Length(2), capacity) };
        let right = unsafe { shared_reader(&right_buckets, Length(2), capacity) };

        assert_eq!(Some(cmp::Ordering::Equal), left.partial_cmp(&right));

        let left = unsafe { shared_reader(&left_buckets, Length(3), capacity) };
        let right = unsafe { shared_reader(&right_buckets, Length(3), capacity) };

        assert_eq!(None, left.partial_cmp(&right));
    }

    #[test]
    fn reader_partialord_different_capacity() {
        let allocator = TestAllocator::unlimited();

        let left_cap = Capacity::new(1, MAX_BUCKETS);
        let right_cap = Capacity::new(2, MAX_BUCKETS);

        let (_, left_buckets) = construct(vec![1.0, 2.0, f64::NAN], left_cap, &allocator);
        let (_, right_buckets) = construct(vec![1.0, 2.0, f64::NAN], right_cap, &allocator);

        let left = unsafe { shared_reader(&left_buckets, Length(0), left_cap) };
        let right = unsafe { shared_reader(&right_buckets, Length(1), right_cap) };

        assert_eq!(Some(cmp::Ordering::Less), left.partial_cmp(&right));
        assert_eq!(Some(cmp::Ordering::Greater), right.partial_cmp(&left));

        let left = unsafe { shared_reader(&left_buckets, Length(2), left_cap) };
        let right = unsafe { shared_reader(&right_buckets, Length(2), right_cap) };

        assert_eq!(Some(cmp::Ordering::Equal), left.partial_cmp(&right));

        let left = unsafe { shared_reader(&left_buckets, Length(3), left_cap) };
        let right = unsafe { shared_reader(&right_buckets, Length(3), right_cap) };

        assert_eq!(None, left.partial_cmp(&right));
    }

    #[test]
    fn reader_ord_same_underlying() {
        let allocator = TestAllocator::unlimited();

        let capacity = Capacity::new(2, MAX_BUCKETS);

        let (_, buckets) = construct(vec![1, 2, 3], capacity, &allocator);

        let left = unsafe { shared_reader(&buckets, Length(0), capacity) };
        let right = unsafe { shared_reader(&buckets, Length(1), capacity) };

        assert_eq!(cmp::Ordering::Less, left.cmp(&right));
        assert_eq!(cmp::Ordering::Greater, right.cmp(&left));

        let left = unsafe { shared_reader(&buckets, Length(2), capacity) };
        let right = unsafe { shared_reader(&buckets, Length(1), capacity) };

        assert_eq!(cmp::Ordering::Greater, left.cmp(&right));

        let left = unsafe { shared_reader(&buckets, Length(3), capacity) };
        let right = unsafe { shared_reader(&buckets, Length(3), capacity) };

        assert_eq!(cmp::Ordering::Equal, left.cmp(&right));
    }

    #[test]
    fn reader_ord_different_underlying() {
        let allocator = TestAllocator::unlimited();

        let capacity = Capacity::new(2, MAX_BUCKETS);

        let (_, left_buckets) = construct(vec![1, 2, 3], capacity, &allocator);
        let (_, right_buckets) = construct(vec![1, 2, 4], capacity, &allocator);

        let left = unsafe { shared_reader(&left_buckets, Length(0), capacity) };
        let right = unsafe { shared_reader(&right_buckets, Length(1), capacity) };

        assert_eq!(cmp::Ordering::Less, left.cmp(&right));
        assert_eq!(cmp::Ordering::Greater, right.cmp(&left));

        let left = unsafe { shared_reader(&left_buckets, Length(2), capacity) };
        let right = unsafe { shared_reader(&right_buckets, Length(2), capacity) };

        assert_eq!(cmp::Ordering::Equal, left.cmp(&right));

        let left = unsafe { shared_reader(&left_buckets, Length(3), capacity) };
        let right = unsafe { shared_reader(&right_buckets, Length(3), capacity) };

        assert_eq!(cmp::Ordering::Less, left.cmp(&right));
    }

    #[test]
    fn reader_ord_different_capacity() {
        let allocator = TestAllocator::unlimited();

        let left_cap = Capacity::new(1, MAX_BUCKETS);
        let right_cap = Capacity::new(2, MAX_BUCKETS);

        let (_, left_buckets) = construct(vec![1, 2, 3], left_cap, &allocator);
        let (_, right_buckets) = construct(vec![1, 2, 4], right_cap, &allocator);

        let left = unsafe { shared_reader(&left_buckets, Length(0), left_cap) };
        let right = unsafe { shared_reader(&right_buckets, Length(1), right_cap) };

        assert_eq!(cmp::Ordering::Less, left.cmp(&right));
        assert_eq!(cmp::Ordering::Greater, right.cmp(&left));

        let left = unsafe { shared_reader(&left_buckets, Length(2), left_cap) };
        let right = unsafe { shared_reader(&right_buckets, Length(2), right_cap) };

        assert_eq!(cmp::Ordering::Equal, left.cmp(&right));

        let left = unsafe { shared_reader(&left_buckets, Length(3), left_cap) };
        let right = unsafe { shared_reader(&right_buckets, Length(3), right_cap) };

        assert_eq!(cmp::Ordering::Less, left.cmp(&right));
    }

    #[test]
    fn reader_iter_buckets() {
        let allocator = TestAllocator::unlimited();

        let capacity = Capacity::new(2, MAX_BUCKETS);

        let (length, buckets) = construct(0..11, capacity, &allocator);

        let reader = unsafe { shared_reader(&buckets, length, capacity) };

        let mut iterator = reader.iter_buckets();
        assert_eq!(Some(&[0, 1][..]), iterator.next());
        assert_eq!(Some(&[2, 3][..]), iterator.next());
        assert_eq!(Some(&[4, 5, 6, 7][..]), iterator.next());
        assert_eq!(Some(&[8, 9, 10][..]), iterator.next());
        assert_eq!(None, iterator.next());
        assert_eq!(None, iterator.next());
    }

    #[test]
    fn reader_iter_elements() {
        let allocator = TestAllocator::unlimited();

        let capacity = Capacity::new(2, MAX_BUCKETS);

        let (length, buckets) = construct(0..5, capacity, &allocator);

        let reader = unsafe { shared_reader(&buckets, length, capacity) };

        let mut iterator = reader.into_iter();
        assert_eq!(Some(&0), iterator.next());
        assert_eq!(Some(&1), iterator.next());
        assert_eq!(Some(&2), iterator.next());
        assert_eq!(Some(&3), iterator.next());
        assert_eq!(Some(&4), iterator.next());
        assert_eq!(None, iterator.next());
        assert_eq!(None, iterator.next());
    }

    #[test]
    fn writer_shrink() {
        let allocator = TestAllocator::unlimited();

        let capacity = Capacity::new(2, MAX_BUCKETS);

        let (length, mut buckets) = construct(0..5, capacity, &allocator);

        {
            let writer = unsafe { shared_writer(&buckets, length, capacity) };
            writer.shrink(&allocator);
        }

        assert_eq!(3, allocator.allocations().len());

        unsafe { buckets.clear(length, capacity) };

        {
            let writer = unsafe { shared_writer(&buckets, Length(0), capacity) };
            writer.shrink(&allocator);
        }

        assert_eq!(0, allocator.allocations().len());
    }

    #[test]
    fn writer_try_reserve() {
        let allocator = TestAllocator::unlimited();

        let capacity = Capacity::new(2, MAX_BUCKETS);

        let (length, buckets) = construct(0..5, capacity, &allocator);

        let writer = unsafe { shared_writer(&buckets, length, capacity) };

        let result = writer.try_reserve(Length(3), &allocator);
        assert_eq!(Ok(()), result);
    }

    #[test]
    fn writer_try_push() {
        let allocator = TestAllocator::unlimited();

        let capacity = Capacity::new(2, MAX_BUCKETS);

        let (length, buckets) = construct(0..5, capacity, &allocator);

        let writer = unsafe { shared_writer(&buckets, length, capacity) };

        let result = writer.try_push(5, &allocator);
        assert_eq!(Ok(Length(6)), result);
    }

    #[test]
    fn writer_try_extend() {
        let allocator = TestAllocator::new(4);

        let capacity = Capacity::new(2, MAX_BUCKETS);

        let (length, buckets) = construct(0..5, capacity, &allocator);

        let writer = unsafe { shared_writer(&buckets, length, capacity) };

        let (length, failure) = writer.try_extend(5..18, &allocator);
        assert_eq!(Length(16), length);
        assert_eq!(Some(Failure::OutOfMemory), failure);
    }

    #[test]
    fn exclusive_bucket_mut() {
        const EMPTY: &'static [i32] = &[];

        let allocator = TestAllocator::unlimited();

        let capacity = Capacity::new(2, MAX_BUCKETS);

        let (length, mut buckets) = construct(0..5, capacity, &allocator);

        let writer = unsafe { exclusive_writer(&mut buckets, length, capacity) };
        assert_eq!(&[0, 1], writer.bucket_mut(BucketIndex(0)));

        let writer = unsafe { exclusive_writer(&mut buckets, length, capacity) };
        assert_eq!(&[2, 3], writer.bucket_mut(BucketIndex(1)));

        let writer = unsafe { exclusive_writer(&mut buckets, length, capacity) };
        assert_eq!(&[4], writer.bucket_mut(BucketIndex(2)));

        let writer = unsafe { exclusive_writer(&mut buckets, length, capacity) };
        assert_eq!(EMPTY, writer.bucket_mut(BucketIndex(3)));
    }

    #[test]
    fn exclusive_clear() {
        let allocator = TestAllocator::unlimited();

        let capacity = Capacity::new(2, MAX_BUCKETS);

        let items = vec!["a".to_string(), "b".to_string(), "c".to_string()];
        let (length, mut buckets) = construct(items, capacity, &allocator);

        let writer = unsafe { exclusive_writer(&mut buckets, length, capacity) };
        writer.clear();
    }
}
