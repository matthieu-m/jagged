//! The core Buckets of the vector.

use super::root::{cell, cmp, marker, mem, ptr, slice};

use super::allocator::{Allocator, Layout};
use super::capacity::{
    Capacity, BucketCapacity, BucketIndex, BucketLength, ElementIndex,
    InnerIndex, Length, NumberBuckets,
};
use super::failure::{Failure, Result};
use super::raw::Raw;

//  Tailored just so the default Vector takes exactly 3 cache lines.
pub const MAX_BUCKETS: usize = 22;

//  The storage.
pub struct BucketArray<T>([Bucket<T>; MAX_BUCKETS]);

impl<T> BucketArray<T> {
    //  Returns the capacity for the Vector.
    pub fn capacity(capacity: usize) -> Capacity {
        Capacity::new(capacity, MAX_BUCKETS)
    }

    //  Returns the number of buckets currently allocated.
    pub fn number_buckets(&self) -> NumberBuckets {
        let result = self.0.iter()
            .position(|bucket| !bucket.is_allocated())
            .unwrap_or(MAX_BUCKETS);
        NumberBuckets(result)
    }

    //  Returns a reference to the ith element, if any.
    //
    //  #   Safety
    //
    //  -   Assumes than length is less than the current length of the vector.
    pub unsafe fn get(
        &self,
        index: ElementIndex,
        length: Length,
        capacity: Capacity
    )
        -> Option<&T>
    {
        if index.0 >= length.0 {
            None
        } else {
            Some(self.get_unchecked(index, capacity))
        }
    }

    //  Returns a reference to the ith element.
    //
    //  #   Safety
    //
    //  -   Assumes than index is less than the current length of the vector.
    pub unsafe fn get_unchecked(&self, index: ElementIndex, capacity: Capacity)
        -> &T
    {
        let (bucket, inner) = capacity.indexes(index);

        //  Safety:
        //  -   bucket is within bounds.
        let bucket = self.0.get_unchecked(bucket.0);

        //  Safety:
        //  -   inner is within bounds.
        bucket.get_unchecked(inner)
    }

    //  Returns a reference to the ith element, if any.
    //
    //  #   Safety
    //
    //  -   Assumes than length is less than the current length of the vector.
    pub unsafe fn get_mut(
        &mut self,
        index: ElementIndex,
        length: Length,
        capacity: Capacity
    )
        -> Option<&mut T>
    {
        if index.0 >= length.0 {
            None
        } else {
            Some(self.get_unchecked_mut(index, capacity))
        }
    }

    //  Returns a reference to the ith element.
    //
    //  #   Safety
    //
    //  -   Assumes than index is less than the current length of the vector.
    pub unsafe fn get_unchecked_mut(
        &mut self,
        index: ElementIndex,
        capacity: Capacity
    )
        -> &mut T
    {
        let (bucket, inner) = capacity.indexes(index);

        //  Safety:
        //  -   bucket is within bounds.
        let bucket = self.0.get_unchecked_mut(bucket.0);

        //  Safety:
        //  -   inner is within bounds.
        bucket.get_unchecked_mut(inner)
    }

    //  Clears the buckets.
    //
    //  #   Safety
    //
    //  -   Assumes that `length` is exactly the current length of the vector.
    //  -   Assumes that `capacity` matches the capacity of the vector.
    pub unsafe fn clear(&mut self, length: Length, capacity: Capacity) {
        let nb_buckets = capacity.number_buckets(length);
        debug_assert!(nb_buckets <= capacity.max_buckets());

        let mut total = 0;

        for index in 0..nb_buckets.0 {
            //  Safety:
            //  -   index is assumed to be within bounds.
            let bucket = self.0.get_unchecked_mut(index);
            let index = BucketIndex(index);

            let length = Self::bucket_properties(index, length, capacity).0;
            total += length.0;

            //  Safety:
            //  -   The first length elements are initialized.
            bucket.clear(length);
        }

        debug_assert!(length.0 == total);
    }

    //  Shrinks the buckets, releasing unused memory.
    //
    //  #   Safety
    //
    //  -   Assumes a single writer thread.
    //  -   Assumes that `length` is exactly the current length of the vector.
    //  -   Assumes that `capacity` matches the capacity of the vector.
    pub unsafe fn shrink<A>(
        &self,
        length: Length,
        capacity: Capacity,
        allocator: &A,
    )
    where
        A: Allocator,
    {
        let nb_buckets = capacity.number_buckets(length);
        debug_assert!(nb_buckets <= capacity.max_buckets());

        for index in nb_buckets.0..capacity.max_buckets().0 {
            let index = BucketIndex(index);
            let capacity = capacity.of_bucket(index);
        
            //  Safety:
            //  -   The index is within bounds.
            let bucket = self.0.get_unchecked(index.0);

            //  Safety:
            //  -   The capacity matches the bucket capacity.
            bucket.deallocate(capacity, allocator);
        }
    }

    //  Reserves additional buckets, for up to `extra` more elements.
    //
    //  #   Errors
    //
    //  If the request amount of space cannot be reserved, this may leave the
    //  vector modified.
    //
    //  #   Safety
    //
    //  -   Assumes a single writer thread.
    //  -   Assumes that `capacity` matches the capacity of the vector.
    pub unsafe fn try_reserve<A>(
        &self,
        extra: Length,
        length: Length,
        capacity: Capacity,
        allocator: &A,
    )
        -> Result<()>
    where
        A: Allocator,
    {
        let total = if let Some(total) = extra.0.checked_add(length.0) {
            Length(total)
        } else {
            return Err(Failure::ElementsOverflow);
        };

        let mut nb_buckets = capacity.number_buckets(length);
        let target = capacity.number_buckets(total);

        while nb_buckets < target {
            nb_buckets = self.push_bucket(nb_buckets, capacity, allocator)?;
        }

        Ok(())
    }

    //  Appends an element to the back.
    //
    //  Returns the new length of the vector.
    // 
    //  #   Errors
    //
    //  If the value cannot be pushed, leaving the vector unchanged.
    //
    //  #   Safety
    //
    //  -   Assumes a single writer thread.
    //  -   Assumes that `length` is exactly the current length of the vector.
    //  -   Assumes that `capacity` matches the capacity of the vector.
    pub unsafe fn try_push<A>(
        &self,
        value: T,
        length: Length,
        capacity: Capacity,
        allocator: &A,
    )
        -> Result<Length>
    where
        A: Allocator,
    {
        let mut nb_buckets = capacity.number_buckets(length);

        if length.0 == capacity.before_bucket(BucketIndex(nb_buckets.0)).0 {
            nb_buckets = self.push_bucket(nb_buckets, capacity, allocator)?;
        }

        debug_assert!(nb_buckets.0 > 0);
        debug_assert!(nb_buckets <= capacity.max_buckets());

        let index = BucketIndex(nb_buckets.0 - 1);

        //  Safety:
        //  -   index is within bounds.
        //  -   length is assumed to match the current length of the vector.
        let bucket = self.uninitialized_bucket_mut(index, length, capacity);
        debug_assert!(!bucket.is_empty());

        //  Safety:
        //  -   bucket is not empty.
        let raw = bucket.get_unchecked_mut(0);

        raw.write(value);

        Ok(Length(length.0 + 1))
    }

    //  Appends the elements to the back.
    //
    //  Returns the new length of the vector.
    //
    //  #   Error
    //
    //  If the vector cannot be fully extended, this may leave the vector
    //  modified.
    //
    //  #   Safety
    //
    //  -   Assumes a single writer thread.
    //  -   Assumes that `length` is exactly the current length of the vector.
    //  -   Assumes that `capacity` matches the capacity of the vector.
    pub unsafe fn try_extend<C, A>(
        &self,
        collection: C,
        length: Length,
        capacity: Capacity,
        allocator: &A,
    )
        -> (Length, Option<Failure>)
    where
        C: IntoIterator<Item = T>,
        A: Allocator,
    {
        let mut length = length;

        //  TODO: optimize to avoid repeated computations to obtain the current
        //  slice.
        for e in collection {
            length = match self.try_push(e, length, capacity, allocator) {
                Err(error) => return (length, Some(error)),
                Ok(length) => length,
            };
        }

        (length, None)
    }

    //  Returns a slice comprising the initialized part of the Bucket.
    //
    //  #   Safety
    //
    //  -   Assumes that `bucket` is within bounds.
    //  -   Assumes that `length` is less than the current length of the vector.
    //  -   Assumes that `capacity` matches the capacity of the vector.
    pub unsafe fn initialized_bucket(
        &self,
        bucket: BucketIndex,
        length: Length,
        capacity: Capacity,
    )
        -> &[T]
    {
        debug_assert!(bucket.0 < capacity.max_buckets().0);

        let bucket_length = capacity.len_bucket(bucket, length);

        //  Safety:
        //  -   The index is guaranteed to be within bounds.
        let bucket = self.0.get_unchecked(bucket.0);

        //  Safety:
        //  -   The first `bucket_length` elements are initialized, due to
        //      `length` being less than the length of the vector, and
        //      `capacity` matching that of the vector.
        bucket.get_initialized_slice(bucket_length)
    }

    //  Returns a slice comprising the initialized part of the Bucket.
    //
    //  #   Safety
    //
    //  -   Assumes that `bucket` is within bounds.
    //  -   Assumes that `length` is less than the current length of the vector.
    //  -   Assumes that `capacity` matches the capacity of the vector.
    pub unsafe fn initialized_bucket_mut(
        &mut self,
        bucket: BucketIndex,
        length: Length,
        capacity: Capacity,
    )
        -> &mut [T]
    {
        debug_assert!(bucket.0 < capacity.max_buckets().0);

        let bucket_length = capacity.len_bucket(bucket, length);

        //  Safety:
        //  -   The index is guaranteed to be within bounds.
        let bucket = self.0.get_unchecked_mut(bucket.0);

        //  Safety:
        //  -   The first `bucket_length` elements are initialized, due to
        //      `length` being less than the length of the vector, and
        //      `capacity` matching that of the vector.
        bucket.get_initialized_slice_mut(bucket_length)
    }

    //  Returns a slice comprising the uninitialized part of Bucket.
    //
    //  #   Safety
    //
    //  -   Assumes that `bucket` is within bounds.
    //  -   Assumes that `length` is exactly the current length of the vector.
    //  -   Assumes that `capacity` matches the capacity of the vector.
    #[allow(clippy::mut_from_ref)]
    unsafe fn uninitialized_bucket_mut(
        &self,
        bucket: BucketIndex,
        length: Length,
        capacity: Capacity,
    )
        -> &mut [Raw<T>]
    {
        debug_assert!(bucket.0 < capacity.max_buckets().0);

        let (length, bucket_capacity)
            = Self::bucket_properties(bucket, length, capacity);
        debug_assert!(length.0 <= bucket_capacity.0);
        debug_assert!(bucket_capacity == capacity.of_bucket(bucket));

        //  Safety:
        //  -   The index is guaranteed to be within bounds.
        let bucket = self.0.get_unchecked(bucket.0);

        //  Safety:
        //  -   The length matches the number of initialized elements.
        //  -   The capacity matches the capacity of the bucket.
        bucket.get_uninitialized_slice_mut(length, bucket_capacity)
    }

    //  Initializes the next bucket, if necessary, returns the new number of
    //  buckets.
    //
    //  #   Safety
    //
    //  -   Assumes a single writer thread.
    //
    //  #   Errors
    //
    //  Returns an error if a bucket cannot be pushed.
    unsafe fn push_bucket<A: Allocator>(
        &self,
        nb_buckets: NumberBuckets,
        capacity: Capacity,
        allocator: &A,
    )
        -> Result<NumberBuckets>
    {
        if nb_buckets >= capacity.max_buckets() {
            return Err(Failure::OutOfBuckets);
        }

        let index = BucketIndex(nb_buckets.0);
        let capacity = capacity.of_bucket(index);

        //  Safety:
        //  -   Index checked to be within bounds.
        let bucket = self.0.get_unchecked(index.0);

        //  Safety:
        //  -   Exclusive access is assumed.
        bucket.allocate(capacity, allocator)?;

        Ok(NumberBuckets(index.0 + 1))
    }

    //  Returns the properties of the Bucket.
    //
    //  The result is the number of initialized elements, and the capacity.
    fn bucket_properties(
        bucket: BucketIndex,
        length: Length,
        capacity: Capacity
    )
        -> (BucketLength, BucketCapacity)
    {
        let prior = capacity.before_bucket(bucket);
        let capacity = capacity.of_bucket(bucket);

        if length.0 <= prior.0 {
            return (BucketLength(0), capacity);
        }

        let length = length.0 - prior.0;

        (BucketLength(cmp::min(length, capacity.0)), capacity)
    }
}

impl<T> Default for BucketArray<T> {
    fn default() -> Self {
        if mem::size_of::<T>() == 0 {
            panic_zero_sized_element();
        }
        Self(Default::default())
    }
}

//
//  Implementation Details
//

//  A single Bucket.
struct Bucket<T>(cell::Cell<*mut Raw<T>>, marker::PhantomData<T>);

impl<T> Bucket<T> {
    //  Returns whether the bucket is allocated, or not.
    fn is_allocated(&self) -> bool { !self.0.get().is_null() }

    //  Allocates a bucket of the given capacity.
    //
    //  #   Safety
    //
    //  -   Assumes a single writer thread.
    unsafe fn allocate<A: Allocator>(
        &self,
        capacity: BucketCapacity,
        allocator: &A,
    )
        -> Result<()>
    {
        //  May already be allocated.
        if self.is_allocated() {
            return Ok(());
        }

        let layout = Self::allocation_layout(capacity)?;

        //  Safety:
        //  -   The layout is valid.
        let ptr = allocator.allocate(layout);

        if ptr.is_null() { return Err(Failure::OutOfMemory) }

        //  Safety:
        //  -   The pointer is correctly aligned.
        let ptr = ptr as *mut Raw<T>;

        self.0.set(ptr);

        Ok(())
    }

    //  Deallocates a bucket of the given capacity, if allocated.
    //
    //  #   Safety
    //
    //  -   Assumes a single writer thread.
    //  -   Assumes that the capacity matches that of the allocation.
    unsafe fn deallocate<A: Allocator>(
        &self,
        capacity: BucketCapacity,
        allocator: &A,
    )
    {
        if !self.is_allocated() {
            return;
        }

        let layout = match Self::allocation_layout(capacity) {
            Ok(layout) => layout,
            Err(_) => {
                //  Safety:
                //  -   Cannot error, it succeeded during the allocation.
                debug_assert!(false, "{:?} succeeded in allocation!", capacity);
                std::hint::unreachable_unchecked()
            },
        };

        //  Safety:
        //  -   The pointer matches the pointer of the allocation.
        //  -   The layout matches the layout of the allocation.
        allocator.deallocate(self.0.get() as *mut u8, layout);

        self.0.set(ptr::null_mut());
    }

    //  Gets a reference to the element at index.
    //
    //  #   Safety
    //
    //  -   Assumes that the element at index is initialized.
    unsafe fn get_unchecked(&self, index: InnerIndex) -> &T {
        let ptr = self.0.get().add(index.0);

        //  Safety:
        //  -   The bucket contains at least index+1 elements.
        let raw: &Raw<T> = &*ptr;

        //  Safety:
        //  -   The element is assumed to be initialized.
        raw.get()
    }

    //  Gets a mutable reference to the element at index.
    //
    //  #   Safety
    //
    //  -   Assumes that the element at index is initialized.
    unsafe fn get_unchecked_mut(&mut self, index: InnerIndex) -> &mut T {
        let ptr = self.0.get().add(index.0);

        //  Safety:
        //  -   The bucket contains at least index+1 elements.
        //  -   The access is exclusive, as per &mut self.
        let raw: &mut Raw<T> = &mut *ptr;

        //  Safety:
        //  -   The element is assumed to be initialized.
        raw.get_mut()
    }

    //  Returns a slice to the first length elements.
    //
    //  #   Safety
    //
    //  -   Assumes that the first length elements are initialized.
    unsafe fn get_initialized_slice(&self, length: BucketLength) -> &[T] {
        let ptr = self.0.get();
        let raw = &*ptr;

        //  Safety:
        //  -   The first length elements are assumed to be initialized.
        slice::from_raw_parts(raw.as_ptr(), length.0)
    }

    //  Returns a slice to the first length elements.
    //
    //  #   Safety
    //
    //  -   Assumes that the first length elements are initialized.
    unsafe fn get_initialized_slice_mut(&mut self, length: BucketLength)
        -> &mut [T]
    {
        let ptr = self.0.get();

        //  Safety:
        //  -   Exclusive access to `raw` is guaranteed by `&mut self`.
        let raw = &mut *ptr;

        //  Safety:
        //  -   The first length elements are assumed to be initialized.
        slice::from_raw_parts_mut(raw.as_mut_ptr(), length.0)
    }

    //  Returns a slice to the first length elements.
    //
    //  #   Safety
    //
    //  -   Assumes exclusive access past the first length elements.
    //  -   Assumes capacity matches the capacity of the bucket.
    #[allow(clippy::mut_from_ref)]
    unsafe fn get_uninitialized_slice_mut(
        &self,
        length: BucketLength,
        capacity: BucketCapacity
    )
        -> &mut [Raw<T>]
    {
        debug_assert!(length.0 <= capacity.0);

        let ptr = self.0.get().add(length.0);

        //  Safety:
        //  -   Exclusive access past the first length elements is assumed.
        //  -   Length is assumed to be less than capacity.
        slice::from_raw_parts_mut(ptr, capacity.0 - length.0)
    }

    //  Clears a bucket of its elements.
    //
    //  #   Safety
    //
    //  -   Assumes that the first length elements are initialized.
    unsafe fn clear(&mut self, length: BucketLength) {
        let ptr = self.0.get();

        //  Safety:
        //  -   The bucket is assumed to contain at least length elements.
        let slice: &mut [Raw<T>] = slice::from_raw_parts_mut(ptr, length.0);

        for e in slice {
            //  Safety:
            //  -   The first length elements are assumed to be initialized.
            e.drop();
        }
    }

    //  Computes the layout for a given capacity.
    //
    //  #   Fails
    //
    //  -   If the necessary size overflows.
    fn allocation_layout(capacity: BucketCapacity) -> Result<Layout> {
        let size = mem::size_of::<Raw<T>>();
        let alignment = mem::align_of::<Raw<T>>();
    
        if let Some(result) = capacity.0.checked_mul(size) {
            //  Safety:
            //  -   Size is non-zero, as guaranted by the constructor.
            //  -   Size is a multiple of Alignment.
            Ok(unsafe { Layout::from_size_align_unchecked(result, alignment) })
        } else {
            Err(Failure::BytesOverflow)
        }
    }
}

impl<T> Default for Bucket<T> {
    fn default() -> Self {
        Self(cell::Cell::new(ptr::null_mut()), marker::PhantomData)
    }
}

#[cold]
#[inline(never)]
fn panic_zero_sized_element() -> ! {
    panic!("Zero-sized elements are not supported");
}

#[cfg(test)]
mod tests {

use super::*;

use crate::utils::tester::*;

#[test]
fn bucket_allocation_layout() {
    fn allocation_layout<T>(capacity: usize) -> Result<usize> {
        match Bucket::<T>::allocation_layout(BucketCapacity(capacity)) {
            Ok(layout) => {
                assert_eq!(mem::align_of::<T>(), layout.align());
                Ok(layout.size())
            },
            Err(error) => Err(error),
        }
    }

    const CAPACITY_BOUNDARY: usize = usize::MAX / 8;

    assert_eq!(Ok(8), allocation_layout::<u64>(1));
    assert_eq!(Ok(32), allocation_layout::<u64>(4));
    assert_eq!(Ok(32), allocation_layout::<[u64; 4]>(1));

    assert_eq!(
        Ok(CAPACITY_BOUNDARY * 8),
        allocation_layout::<u64>(CAPACITY_BOUNDARY)
    );
    assert_eq!(
        Err(Failure::BytesOverflow),
        allocation_layout::<u64>(CAPACITY_BOUNDARY + 1)
    );
}

#[test]
fn bucket_allocate_failure() {
    let allocator = TestAllocator::default();

    let bucket = Bucket::<SpyElement<'_>>::default();
    let allocated = unsafe { bucket.allocate(BucketCapacity(1), &allocator) };

    assert_eq!(Err(Failure::OutOfMemory), allocated);
}

#[test]
fn bucket_allocate_success() {
    let allocator = TestAllocator::default();
    allocator.allowed.set(1);

    let bucket = Bucket::<SpyElement<'_>>::default();
    let allocated = unsafe { bucket.allocate(BucketCapacity(1), &allocator) };

    assert_eq!(Ok(()), allocated);

    let allocation = allocator.allocations().last().copied().unwrap();

    assert_eq!(mem::size_of::<usize>(), allocation.size);
    assert_eq!(mem::align_of::<usize>(), allocation.alignment);
}

#[test]
fn bucket_allocate_skip() {
    let allocator = TestAllocator::default();
    allocator.allowed.set(1);

    let bucket = Bucket::<SpyElement<'_>>::default();
    let allocated = unsafe { bucket.allocate(BucketCapacity(1), &allocator) };

    assert_eq!(Ok(()), allocated);
    assert_eq!(1, allocator.allocations().len());

    let allocated = unsafe { bucket.allocate(BucketCapacity(2), &allocator) };

    assert_eq!(Ok(()), allocated);
    assert_eq!(1, allocator.allocations().len());
}

#[test]
fn bucket_deallocate() {
    let allocator = TestAllocator::default();
    allocator.allowed.set(1);

    let bucket = Bucket::<SpyElement<'_>>::default();
    let allocated = unsafe { bucket.allocate(BucketCapacity(1), &allocator) };

    assert_eq!(Ok(()), allocated);
    assert_eq!(1, allocator.allocations().len());

    unsafe { bucket.deallocate(BucketCapacity(1), &allocator) };

    assert_eq!(0, allocator.allocations().len());
}

#[test]
fn bucket_clear() {
    let capacity = BucketCapacity(4);
    let initialized = 3;
    assert!(initialized <= capacity.0);

    let allocator = TestAllocator::default();
    allocator.allowed.set(1);

    let bucket = Bucket::<SpyElement<'_>>::default();
    let allocated = unsafe { bucket.allocate(capacity, &allocator) };

    assert_eq!(Ok(()), allocated);

    let count = SpyCount::zero();
    let uninitialized =
        unsafe { bucket.get_uninitialized_slice_mut(BucketLength(0), capacity) };

    for place in &mut uninitialized[..initialized] {
        place.write(SpyElement::new(&count));
    }

    assert_eq!(initialized, count.get());

    let mut bucket = bucket;
    unsafe { bucket.clear(BucketLength(initialized)) };

    assert_eq!(0, count.get());
}

#[test]
fn bucket_array_bucket_properties_1() {
    fn bucket_properties(bucket: usize, length: usize) -> (usize, usize) {
        type BA = BucketArray<SpyElement<'static>>;

        let capacity = BA::capacity(1);
        let (length, capacity) =
            BA::bucket_properties(BucketIndex(bucket), Length(length), capacity);
        (length.0, capacity.0)
    }

    assert_eq!((0, 1), bucket_properties(0, 0));
    assert_eq!((1, 1), bucket_properties(0, 1));
    assert_eq!((1, 1), bucket_properties(0, 9));

    assert_eq!((0, 1), bucket_properties(1, 1));
    assert_eq!((1, 1), bucket_properties(1, 2));
    assert_eq!((1, 1), bucket_properties(1, 9));

    assert_eq!((0, 2), bucket_properties(2, 2));
    assert_eq!((1, 2), bucket_properties(2, 3));
    assert_eq!((2, 2), bucket_properties(2, 4));
    assert_eq!((2, 2), bucket_properties(2, 9));
}

#[test]
fn bucket_array_bucket_properties_4() {
    fn bucket_properties(bucket: usize, length: usize) -> (usize, usize) {
        type BA = BucketArray<SpyElement<'static>>;

        let capacity = BA::capacity(4);
        let (length, capacity) =
            BA::bucket_properties(BucketIndex(bucket), Length(length), capacity);
        (length.0, capacity.0)
    }

    assert_eq!((0, 4), bucket_properties(0, 0));
    assert_eq!((1, 4), bucket_properties(0, 1));
    assert_eq!((4, 4), bucket_properties(0, 4));
    assert_eq!((4, 4), bucket_properties(0, 9));

    assert_eq!((0, 4), bucket_properties(1, 4));
    assert_eq!((1, 4), bucket_properties(1, 5));
    assert_eq!((4, 4), bucket_properties(1, 8));
    assert_eq!((4, 4), bucket_properties(1, 9));

    assert_eq!((0, 8), bucket_properties(2, 8));
    assert_eq!((1, 8), bucket_properties(2, 9));
    assert_eq!((8, 8), bucket_properties(2, 16));
    assert_eq!((8, 8), bucket_properties(2, 17));
}

#[test]
fn bucket_array_push_bucket() {
    let allocator = TestAllocator::default();
    allocator.allowed.set(usize::MAX);

    let buckets = BucketArray::<SpyElement<'static>>::default();
    let capacity = Capacity::new(1, MAX_BUCKETS);

    unsafe {
        buckets.push_bucket(NumberBuckets(0), capacity, &allocator).unwrap();
        buckets.push_bucket(NumberBuckets(1), capacity, &allocator).unwrap();
        buckets.push_bucket(NumberBuckets(2), capacity, &allocator).unwrap();
    }

    assert_eq!(vec![8, 8, 16], allocator.allocation_sizes());

    for index in 0..3 {
        assert!(buckets.0[index].is_allocated());
    }

    for index in 4..MAX_BUCKETS {
        assert!(!buckets.0[index].is_allocated());
    }
}

#[test]
fn bucket_array_push_bucket_out_of_buckets() {
    const NUMBER_BUCKETS: usize = 3;

    let allocator = TestAllocator::default();
    allocator.allowed.set(usize::MAX);

    let buckets = BucketArray::<SpyElement<'static>>::default();
    let capacity = Capacity::new(1, NUMBER_BUCKETS);

    let pushed = unsafe {
        buckets.push_bucket(NumberBuckets(NUMBER_BUCKETS - 1), capacity, &allocator)
    };
    assert_eq!(Ok(NumberBuckets(NUMBER_BUCKETS)), pushed);

    let pushed = unsafe {
        buckets.push_bucket(NumberBuckets(NUMBER_BUCKETS), capacity, &allocator)
    };
    assert_eq!(Err(Failure::OutOfBuckets), pushed);
}

#[test]
fn bucket_array_push_bucket_out_of_memory() {
    let allocator = TestAllocator::default();

    let buckets = BucketArray::<SpyElement<'static>>::default();
    let capacity = Capacity::new(1, MAX_BUCKETS);

    let pushed = unsafe {
        buckets.push_bucket(NumberBuckets(0), capacity, &allocator)
    };
    assert_eq!(Err(Failure::OutOfMemory), pushed);
}

#[test]
fn bucket_array_try_reserve() {
    let allocator = TestAllocator::default();
    allocator.allowed.set(usize::MAX);

    let buckets = BucketArray::<SpyElement<'static>>::default();
    let capacity = Capacity::new(1, MAX_BUCKETS);

    let reserved = unsafe {
        buckets.try_reserve(Length(17), Length(0), capacity, &allocator)
    };

    assert_eq!(Ok(()), reserved);
    assert_eq!(vec![8, 8, 16, 32, 64, 128], allocator.allocation_sizes());

    for index in 0..6 {
        assert!(buckets.0[index].is_allocated());
    }

    for index in 6..MAX_BUCKETS {
        assert!(!buckets.0[index].is_allocated());
    }
}

#[test]
fn bucket_array_try_reserve_elements_overflow() {
    let allocator = TestAllocator::default();
    allocator.allowed.set(0);

    let buckets = BucketArray::<SpyElement<'static>>::default();
    let capacity = Capacity::new(1, MAX_BUCKETS);

    let half_usize = Length(usize::MAX / 2 + 1);

    let reserved = unsafe {
        buckets.try_reserve(half_usize, half_usize, capacity, &allocator)
    };

    assert_eq!(Err(Failure::ElementsOverflow), reserved);
}

#[test]
fn bucket_array_try_reserve_out_of_buckets() {
    const NUMBER_BUCKETS: usize = 3;

    let allocator = TestAllocator::default();
    allocator.allowed.set(usize::MAX);

    let buckets = BucketArray::<SpyElement<'static>>::default();
    let capacity = Capacity::new(1, NUMBER_BUCKETS);

    let extra = Length(1usize << NUMBER_BUCKETS);

    let reserved = unsafe {
        buckets.try_reserve(extra, Length(0), capacity, &allocator)
    };

    assert_eq!(Err(Failure::OutOfBuckets), reserved);
    assert_eq!(vec![8, 8, 16], allocator.allocation_sizes());

    for index in 0..NUMBER_BUCKETS {
        assert!(buckets.0[index].is_allocated());
    }

    for index in NUMBER_BUCKETS..MAX_BUCKETS {
        assert!(!buckets.0[index].is_allocated());
    }
}

#[test]
fn bucket_array_try_reserve_out_of_memory() {
    const NUMBER_BUCKETS: usize = 3;

    let allocator = TestAllocator::default();
    allocator.allowed.set(NUMBER_BUCKETS);

    let buckets = BucketArray::<SpyElement<'static>>::default();
    let capacity = Capacity::new(1, MAX_BUCKETS);

    let extra = Length(1usize << NUMBER_BUCKETS);

    let reserved = unsafe {
        buckets.try_reserve(extra, Length(0), capacity, &allocator)
    };

    assert_eq!(Err(Failure::OutOfMemory), reserved);
    assert_eq!(vec![8, 8, 16], allocator.allocation_sizes());

    for index in 0..NUMBER_BUCKETS {
        assert!(buckets.0[index].is_allocated());
    }

    for index in NUMBER_BUCKETS..MAX_BUCKETS {
        assert!(!buckets.0[index].is_allocated());
    }
}

#[test]
fn bucket_array_try_push() {
    let allocator = TestAllocator::default();
    allocator.allowed.set(usize::MAX);

    let count = SpyCount::zero();

    let buckets = BucketArray::<SpyElement<'_>>::default();
    let capacity = Capacity::new(1, MAX_BUCKETS);

    let pushed = unsafe {
        let value = SpyElement::new(&count);
        buckets.try_push(value, Length(0), capacity, &allocator)
    };

    assert_eq!(Ok(Length(1)), pushed);
    assert_eq!(vec![8], allocator.allocation_sizes());

    let pushed = unsafe {
        let value = SpyElement::new(&count);
        buckets.try_push(value, Length(1), capacity, &allocator)
    };

    assert_eq!(Ok(Length(2)), pushed);
    assert_eq!(vec![8, 8], allocator.allocation_sizes());

    let pushed = unsafe {
        let value = SpyElement::new(&count);
        buckets.try_push(value, Length(2), capacity, &allocator)
    };

    assert_eq!(Ok(Length(3)), pushed);
    assert_eq!(vec![8, 8, 16], allocator.allocation_sizes());

    let pushed = unsafe {
        let value = SpyElement::new(&count);
        buckets.try_push(value, Length(3), capacity, &allocator)
    };

    assert_eq!(Ok(Length(4)), pushed);
    assert_eq!(vec![8, 8, 16], allocator.allocation_sizes());
}

#[test]
fn bucket_array_try_push_out_of_buckets() {
    const NUMBER_BUCKETS: usize = 2;

    let allocator = TestAllocator::default();
    allocator.allowed.set(NUMBER_BUCKETS);

    let count = SpyCount::zero();

    let buckets = BucketArray::<SpyElement<'_>>::default();
    let capacity = Capacity::new(1, NUMBER_BUCKETS);

    let pushed = unsafe {
        let value = SpyElement::new(&count);
        buckets.try_push(value, Length(0), capacity, &allocator)
    };

    assert_eq!(Ok(Length(1)), pushed);
    assert_eq!(vec![8], allocator.allocation_sizes());

    let pushed = unsafe {
        let value = SpyElement::new(&count);
        buckets.try_push(value, Length(1), capacity, &allocator)
    };

    assert_eq!(Ok(Length(2)), pushed);
    assert_eq!(vec![8, 8], allocator.allocation_sizes());

    let pushed = unsafe {
        let value = SpyElement::new(&count);
        buckets.try_push(value, Length(2), capacity, &allocator)
    };

    assert_eq!(Err(Failure::OutOfBuckets), pushed);
    assert_eq!(vec![8, 8], allocator.allocation_sizes());
}

#[test]
fn bucket_array_try_push_out_of_memory() {
    const NUMBER_BUCKETS: usize = 2;

    let allocator = TestAllocator::default();
    allocator.allowed.set(NUMBER_BUCKETS);

    let count = SpyCount::zero();

    let buckets = BucketArray::<SpyElement<'_>>::default();
    let capacity = Capacity::new(1, MAX_BUCKETS);

    let pushed = unsafe {
        let value = SpyElement::new(&count);
        buckets.try_push(value, Length(0), capacity, &allocator)
    };

    assert_eq!(Ok(Length(1)), pushed);
    assert_eq!(vec![8], allocator.allocation_sizes());

    let pushed = unsafe {
        let value = SpyElement::new(&count);
        buckets.try_push(value, Length(1), capacity, &allocator)
    };

    assert_eq!(Ok(Length(2)), pushed);
    assert_eq!(vec![8, 8], allocator.allocation_sizes());

    let pushed = unsafe {
        let value = SpyElement::new(&count);
        buckets.try_push(value, Length(2), capacity, &allocator)
    };

    assert_eq!(Err(Failure::OutOfMemory), pushed);
    assert_eq!(vec![8, 8], allocator.allocation_sizes());
}

#[test]
fn bucket_array_try_extend() {
    let allocator = TestAllocator::default();
    allocator.allowed.set(usize::MAX);

    let count = SpyCount::zero();
    let collection = vec![
        SpyElement::new(&count), SpyElement::new(&count),
        SpyElement::new(&count), SpyElement::new(&count),
    ];

    let buckets = BucketArray::<SpyElement<'_>>::default();
    let capacity = Capacity::new(1, MAX_BUCKETS);

    let (length, failure) = unsafe {
        buckets.try_extend(collection, Length(0), capacity, &allocator)
    };

    assert_eq!(Length(4), length);
    assert_eq!(None, failure);
    assert_eq!(vec![8, 8, 16], allocator.allocation_sizes());
}

#[test]
fn bucket_array_try_extend_out_of_buckets() {
    const NUMBER_BUCKETS: usize = 3;

    let allocator = TestAllocator::default();
    allocator.allowed.set(NUMBER_BUCKETS + 1);

    let count = SpyCount::zero();
    let collection = vec![
        SpyElement::new(&count), SpyElement::new(&count),
        SpyElement::new(&count), SpyElement::new(&count),
        SpyElement::new(&count), SpyElement::new(&count),
    ];

    let buckets = BucketArray::<SpyElement<'_>>::default();
    let capacity = Capacity::new(1, NUMBER_BUCKETS);

    let (length, failure) = unsafe {
        buckets.try_extend(collection, Length(0), capacity, &allocator)
    };

    assert_eq!(Length(4), length);
    assert_eq!(Some(Failure::OutOfBuckets), failure);
    assert_eq!(vec![8, 8, 16], allocator.allocation_sizes());
}

#[test]
fn bucket_array_try_extend_out_of_memory() {
    const NUMBER_BUCKETS: usize = 3;

    let allocator = TestAllocator::default();
    allocator.allowed.set(NUMBER_BUCKETS);

    let count = SpyCount::zero();
    let collection = vec![
        SpyElement::new(&count), SpyElement::new(&count),
        SpyElement::new(&count), SpyElement::new(&count),
        SpyElement::new(&count), SpyElement::new(&count),
    ];

    let buckets = BucketArray::<SpyElement<'_>>::default();
    let capacity = Capacity::new(1, MAX_BUCKETS);

    let (length, failure) = unsafe {
        buckets.try_extend(collection, Length(0), capacity, &allocator)
    };

    assert_eq!(Length(4), length);
    assert_eq!(Some(Failure::OutOfMemory), failure);
    assert_eq!(vec![8, 8, 16], allocator.allocation_sizes());
}

#[test]
fn bucket_array_shrink_none() {
    let allocator = TestAllocator::default();
    allocator.allowed.set(usize::MAX);

    let count = SpyCount::zero();
    let collection = vec![
        SpyElement::new(&count), SpyElement::new(&count),
        SpyElement::new(&count), SpyElement::new(&count),
    ];

    let buckets = BucketArray::<SpyElement<'_>>::default();
    let capacity = Capacity::new(1, MAX_BUCKETS);

    unsafe {
        buckets.try_extend(collection, Length(0), capacity, &allocator);
    }

    assert_eq!(vec![8, 8, 16], allocator.allocation_sizes());

    unsafe {
        buckets.shrink(Length(4), capacity, &allocator);
    }

    assert_eq!(vec![8, 8, 16], allocator.allocation_sizes());
}

#[test]
fn bucket_array_shrink_partial() {
    let allocator = TestAllocator::default();
    allocator.allowed.set(usize::MAX);

    let count = SpyCount::zero();
    let collection = vec![
        SpyElement::new(&count), SpyElement::new(&count),
        SpyElement::new(&count), SpyElement::new(&count),
    ];

    let buckets = BucketArray::<SpyElement<'_>>::default();
    let capacity = Capacity::new(1, MAX_BUCKETS);

    unsafe {
        let _ = buckets.try_reserve(Length(16), Length(0), capacity, &allocator);
    }

    assert_eq!(vec![8, 8, 16, 32, 64], allocator.allocation_sizes());

    unsafe {
        buckets.try_extend(collection, Length(0), capacity, &allocator);
    }

    unsafe {
        buckets.shrink(Length(4), capacity, &allocator);
    }

    assert_eq!(vec![8, 8, 16], allocator.allocation_sizes());
}

#[test]
fn bucket_array_shrink_all() {
    let allocator = TestAllocator::default();
    allocator.allowed.set(usize::MAX);

    let buckets = BucketArray::<SpyElement<'_>>::default();
    let capacity = Capacity::new(1, MAX_BUCKETS);

    unsafe {
        let _ = buckets.try_reserve(Length(16), Length(0), capacity, &allocator);
    }

    assert_eq!(vec![8, 8, 16, 32, 64], allocator.allocation_sizes());

    unsafe {
        buckets.shrink(Length(0), capacity, &allocator);
    }

    assert_eq!(0, allocator.allocations().len());
}

#[test]
fn bucket_array_clear_empty() {
    let allocator = TestAllocator::default();
    allocator.allowed.set(usize::MAX);

    let buckets = BucketArray::<SpyElement<'_>>::default();
    let capacity = Capacity::new(1, MAX_BUCKETS);

    unsafe {
        let _ = buckets.try_reserve(Length(16), Length(0), capacity, &allocator);
    }

    let mut buckets = buckets;
    unsafe {
        buckets.clear(Length(0), capacity);
    }

}

#[test]
fn bucket_array_clear_all() {
    let allocator = TestAllocator::default();
    allocator.allowed.set(usize::MAX);

    let count = SpyCount::zero();
    let collection = vec![
        SpyElement::new(&count), SpyElement::new(&count),
        SpyElement::new(&count), SpyElement::new(&count),
    ];

    let buckets = BucketArray::<SpyElement<'_>>::default();
    let capacity = Capacity::new(1, MAX_BUCKETS);

    unsafe {
        buckets.try_extend(collection, Length(0), capacity, &allocator);
    }

    let mut buckets = buckets;
    unsafe {
        buckets.clear(Length(4), capacity);
    }

    assert_eq!(0, count.get());
}

//  TODO:
//  -   Test when allocation/deallocation occurs.
//  -   Test BucketArray.
//  -   Ensure Errors are covered.

}
