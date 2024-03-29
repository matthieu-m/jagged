//! The jagged buckets underlying the HashMap and HashSet.

use super::root::{array, borrow, cell, hash, hint, iter, marker, mem, ptr, slice};

use super::allocator::{Allocator, Layout};
use super::capacity::{BucketCapacity, BucketIndex, Capacity, NumberBuckets, Size};
use super::element::{Element, Generation};
use super::failure::{Failure, Result};
use super::key::Key;

use self::borrow::Borrow;

//  Tailored just so the default HashMap/HashSet takes exactly 3 cache lines.
pub const DEFAULT_BUCKETS: usize = 20;

//  The storage.
pub struct BucketArray<T, const N: usize>([Bucket<T>; N]);

impl<T, const N: usize> BucketArray<T, N> {
    //  Returns the capacity for the Vector.
    pub fn capacity(capacity: usize) -> Capacity {
        Capacity::new(capacity, DEFAULT_BUCKETS)
    }

    //  Returns a slice.
    pub fn as_slice(&self) -> BucketSlice<'_, T> {
        BucketSlice(&self.0)
    }

    //  Clears the buckets.
    //
    //  #   Safety
    //
    //  -   Assumes that `size` matches the size of the collection.
    //  -   Assumes that `capacity` matches the capacity of the collection.
    pub unsafe fn clear(&mut self, size: Size, capacity: Capacity) {
        let nb_buckets = capacity.number_buckets(size);
        debug_assert!(nb_buckets <= capacity.max_buckets());

        for index in 0..nb_buckets.0 {
            //  Safety:
            //  -   index is assumed to be within bounds.
            let bucket = unsafe { self.0.get_unchecked_mut(index) };

            let capacity = capacity.of_bucket(BucketIndex(index));

            //  Safety:
            //  -   The capacity matches the bucket.
            unsafe { bucket.clear(capacity) };
        }
    }

    //  Gets the element whose key matches.
    //
    //  Returns a reference to the element if it could be found.
    //
    //  Warning: modifying the part of the element that determines its key may
    //  result in corrupting the invariants of the map. Not unsafe, but unwise.
    //
    //  #   Safety
    //
    //  -   Assumes that `size` is less than the current size of the collection.
    //  -   Assumes that `capacity` matches the capacity of the collection.
    pub unsafe fn get_mut<Q, H>(&mut self, key: &Q, size: Size, capacity: Capacity, hook: &H) -> Option<&mut T>
    where
        T: Key,
        T::Key: Borrow<Q>,
        Q: ?Sized + Eq + hash::Hash,
        H: hash::BuildHasher,
    {
        let hash = hash(key, hook);

        //  Safety:
        //  -   `size` and `capacity` match, as per pre-conditions.
        let entry = unsafe { self.as_slice().entry(key, hash, size, capacity) };

        entry
            .and_then(|e| e.occupied())
            //  Safety:
            //  -   The element is initialized, since the entry is occupied.
            //  -   The caller has exclusive access since `&mut self`.
            .map(|e| unsafe { e.get_unchecked_mut() })
    }
}

impl<T, const N: usize> Default for BucketArray<T, N> {
    fn default() -> Self {
        if mem::size_of::<T>() == 0 {
            panic_zero_sized_element();
        }

        Self(array::from_fn(|_| Bucket::default()))
    }
}

//  The slice.
pub struct BucketSlice<'a, T>(&'a [Bucket<T>]);

impl<'a, T> BucketSlice<'a, T> {
    //  Returns the number of buckets currently allocated.
    pub fn number_buckets(&self) -> NumberBuckets {
        let result = self
            .0
            .iter()
            .position(|bucket| !bucket.is_allocated())
            .unwrap_or(DEFAULT_BUCKETS);
        NumberBuckets(result)
    }

    //  Shrinks the buckets, releasing unused memory.
    //
    //  #   Safety
    //
    //  -   Assumes a single writer thread.
    //  -   Assumes that `size` is exactly the current size of the collection.
    //  -   Assumes that `capacity` matches the capacity of the collection.
    pub unsafe fn shrink<A>(&self, size: Size, capacity: Capacity, allocator: &A)
    where
        A: Allocator,
    {
        let nb_buckets = capacity.number_buckets(size);
        debug_assert!(nb_buckets <= capacity.max_buckets());

        for index in nb_buckets.0..capacity.max_buckets().0 {
            let index = BucketIndex(index);
            let capacity = capacity.of_bucket(index);

            //  Safety:
            //  -   The index is within bounds.
            let bucket = unsafe { self.0.get_unchecked(index.0) };

            //  Safety:
            //  -   The capacity matches the bucket capacity.
            unsafe { bucket.deallocate(capacity, allocator) };
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
    pub unsafe fn try_reserve<A>(&self, extra: Size, size: Size, capacity: Capacity, allocator: &A) -> Result<()>
    where
        A: Allocator,
    {
        let total = if let Some(total) = extra.0.checked_add(size.0) {
            Size(total)
        } else {
            return Err(Failure::ElementsOverflow);
        };

        let mut nb_buckets = capacity.number_buckets(size);
        let target = capacity.number_buckets(total);

        while nb_buckets < target {
            //  Safety:
            //  -   Single writer thread, per pre-condition.
            //  -   `capacity` match, per pre-condition.
            nb_buckets = unsafe { self.push_bucket(nb_buckets, capacity, allocator)? };
        }

        Ok(())
    }

    //  Gets the element whose key matches.
    //
    //  Returns a reference to the element if it could be found.
    //
    //  #   Safety
    //
    //  -   Assumes that `size` is less than the current size of the collection.
    //  -   Assumes that `capacity` matches the capacity of the collection.
    pub unsafe fn get<Q, H>(&self, key: &Q, size: Size, capacity: Capacity, hook: &H) -> Option<&'a T>
    where
        T: Key,
        T::Key: Borrow<Q>,
        Q: ?Sized + Eq + hash::Hash,
        H: hash::BuildHasher,
    {
        let hash = hash(key, hook);

        //  Safety:
        //  -   `size` and `capacity` match, per pre-condition.
        let entry = unsafe { self.entry(key, hash, size, capacity) };

        entry
            .and_then(|e| e.occupied())
            //  Safety:
            //  -   The element is initialized, since the entry is occupied.
            .map(|e| unsafe { e.get_unchecked() })
    }

    //  Inserts the element.
    //
    //  Returns the new size, as well the element if insertion failed.
    //
    //  The size is not modified in case of failure.
    //
    //  #   Safety
    //
    //  -   Assumes a single writer thread.
    //  -   Assumes that `size` matches the current size of the collection.
    //  -   Assumes that `capacity` matches the capacity of the collection.
    pub unsafe fn try_insert<H>(
        &self,
        element: T,
        size: Size,
        capacity: Capacity,
        hook: &H,
    ) -> Result<(Size, Option<T>)>
    where
        T: Key,
        T::Key: Eq + hash::Hash,
        H: Allocator + hash::BuildHasher,
    {
        let hash = hash(element.key(), hook);

        let generation = Generation(size.0);
        let new_size = Size(size.0 + 1);

        //  Safety:
        //  -   `size` is less than the current size of the collection.
        //  -   `capacity` matches the capacity of the collection.
        let entry = unsafe { self.entry(element.key(), hash, size, capacity) };

        if let Some(entry) = entry {
            let result = match entry {
                //  The element was found.
                Entry::Occupied(_) => Ok((size, Some(element))),
                //  A location for insertion was found.
                Entry::Vacant(location) => {
                    debug_assert!(capacity.number_buckets(size) == capacity.number_buckets(new_size));
                    unsafe { location.set(generation, element) };
                    Ok((new_size, None))
                }
            };

            return result;
        }

        //  A new bucket is necessary.

        let nb_buckets = capacity.number_buckets(size);

        //  Safety:
        //  -   Single writer thread.
        let nb_buckets = unsafe { self.push_bucket(nb_buckets, capacity, hook)? };
        debug_assert!(nb_buckets == capacity.number_buckets(new_size));

        let last_index = BucketIndex(nb_buckets.0 - 1);
        let last_capacity = capacity.of_bucket(last_index);

        //  Safety:
        //  -   The index is within bounds.
        let last_bucket = unsafe { self.0.get_unchecked(last_index.0) };

        //  Safety:
        //  -   `generation` is less than the current size of the collection.
        //  -   `capacity` matches the capacity of the collection.
        let entry = unsafe { last_bucket.entry(element.key(), hash, generation, last_capacity) };

        match entry {
            Entry::Vacant(location) => {
                //  Safety:
                //  -   `generation` matches.
                unsafe { location.set(generation, element) };
                Ok((new_size, None))
            }
            //  Safety:
            //  -   A newly allocated bucket has no element.
            Entry::Occupied(_) => unsafe { hint::unreachable_unchecked() },
        }
    }

    //  Inserts multiple elements to the collection.
    //
    //  Returns the new size of the collection.
    //
    //  #   Error
    //
    //  If the collection cannot be fully extended, this may leave the collection modified.
    //
    //  #   Safety
    //
    //  -   Assumes a single writer thread.
    //  -   Assumes that `size` is exactly the current size of the collection.
    //  -   Assumes that `capacity` matches the capacity of the collection.
    pub unsafe fn try_extend<C, H>(
        &self,
        collection: C,
        size: Size,
        capacity: Capacity,
        hooks: &H,
    ) -> (Size, Option<Failure>)
    where
        C: IntoIterator<Item = T>,
        T: Key,
        T::Key: Eq + hash::Hash,
        H: Allocator + hash::BuildHasher,
    {
        //  In a typical HashMap/Set implementation, the collection would be queried to ascertain its minimal length, in
        //  an attempt to minimize the number of re-allocations.
        //
        //  There is no re-allocation, ever, in Vector, so this step is unnecessary.

        let mut size = size;

        //  TODO: optimize to avoid repeated computations to obtain the current slice.
        for e in collection {
            //  Safety:
            //  -   `size` and `capacity` match.
            let result = unsafe { self.try_insert(e, size, capacity, hooks) };

            size = match result {
                Err(error) => return (size, Some(error)),
                Ok((size, _)) => size,
            };
        }

        (size, None)
    }

    //  Returns a BucketIterator which can safely iterate over the bucket.
    //
    //  #   Safety
    //
    //  -   Assumes that `bucket` is within bounds.
    //  -   Assumes that `generation` is less than the current size of the collection.
    //  -   Assumes that `capacity` matches the capacity of the vector.
    pub unsafe fn bucket(
        &self,
        bucket: BucketIndex,
        generation: Generation,
        capacity: Capacity,
    ) -> BucketIterator<'a, T> {
        debug_assert!(bucket.0 < capacity.max_buckets().0);

        let capacity = capacity.of_bucket(bucket);

        //  Safety:
        //  -   `bucket` is within bounds.
        let bucket = unsafe { self.0.get_unchecked(bucket.0) };

        //  Safety:
        //  -   `capacity` matches the bucket.
        let slice = unsafe { bucket.get_slice(capacity) };

        //  Safety:
        //  -   `generation` is less than the current size of the collection.
        unsafe { BucketIterator::new(slice, generation) }
    }

    //  Looks up the element, or where it could be inserted.
    //
    //  #   Safety
    //
    //  -   Assumes that `generation` is less than the current size of the collection.
    //  -   Assumes that `capacity` matches the capacity of the collection.
    unsafe fn entry<Q>(&self, key: &Q, hash: Hash, size: Size, capacity: Capacity) -> Option<Entry<'a, T>>
    where
        T: Key,
        T::Key: Borrow<Q>,
        Q: ?Sized + Eq,
    {
        let nb_buckets = capacity.number_buckets(size);
        let generation = Generation(size.0);

        if nb_buckets.0 == 0 {
            return None;
        }

        //  We only ever insert in the last bucket, as all previous buckets are full.
        let last_index = BucketIndex(nb_buckets.0 - 1);
        let last_capacity = capacity.of_bucket(last_index);

        let entry = {
            //  Safety:
            //  -   last_index is within bounds.
            let bucket = unsafe { self.0.get_unchecked(last_index.0) };

            //  Safety:
            //  -   `generation` and `last_capacity` match.
            unsafe { bucket.entry(key, hash, generation, last_capacity) }
        };

        if entry.is_occupied() {
            debug_assert!(unsafe { entry.occupied().unwrap().get(generation).is_some() });
            return Some(entry);
        }

        //  Iterate in reverse order as the latter buckets contain the most elements, and thus are more likely to
        //  contain the element of interest.
        for bucket in (0..last_index.0).rev() {
            let capacity = capacity.of_bucket(BucketIndex(bucket));

            //  Safety:
            //  -   bucket is within bounds.
            let bucket = unsafe { self.0.get_unchecked(bucket) };

            //  Safety:
            //  -   `generation` and `capacity` match.
            let e = unsafe { bucket.find(key, hash, generation, capacity) };

            if let Some(e) = e {
                debug_assert!(unsafe { e.get(generation).is_some() });
                return Some(Entry::Occupied(e));
            }
        }

        debug_assert!(unsafe { entry.vacant().unwrap().get(generation).is_none() });

        //  No vacancy if the last bucket is already fully loaded (50%).
        let last_size = capacity.size_bucket(last_index, size);

        if last_size.0 < last_capacity.0 / 2 {
            Some(entry)
        } else {
            None
        }
    }

    //  Initializes the next bucket, if necessary, returns the new number of buckets.
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
    ) -> Result<NumberBuckets> {
        if nb_buckets >= capacity.max_buckets() {
            return Err(Failure::OutOfBuckets);
        }

        let index = BucketIndex(nb_buckets.0);
        let capacity = capacity.of_bucket(index);

        //  Safety:
        //  -   Index checked to be within bounds.
        let bucket = unsafe { self.0.get_unchecked(index.0) };

        //  Safety:
        //  -   Exclusive access is assumed.
        unsafe { bucket.allocate(capacity, allocator)? };

        Ok(NumberBuckets(index.0 + 1))
    }
}

impl<'a, T> Clone for BucketSlice<'a, T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<'a, T> Copy for BucketSlice<'a, T> {}

//  A safe view over a bucket.
pub struct BucketIterator<'a, T> {
    bucket: &'a [Element<T>],
    generation: Generation,
}

impl<'a, T> BucketIterator<'a, T> {
    //  Creates an instance.
    //
    //  #   Safety
    //
    //  -   Assumes that `generation` is less than the current size of the collection.
    unsafe fn new(bucket: &'a [Element<T>], generation: Generation) -> Self {
        BucketIterator { bucket, generation }
    }
}

impl<'a, T> Clone for BucketIterator<'a, T> {
    fn clone(&self) -> Self {
        BucketIterator {
            bucket: self.bucket,
            generation: self.generation,
        }
    }
}

impl<'a, T> iter::Iterator for BucketIterator<'a, T> {
    type Item = Option<&'a T>;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some((head, tail)) = self.bucket.split_first() {
            self.bucket = tail;

            //  Safety:
            //  -   `self.generation` is less than the current size of the collection.
            Some(unsafe { head.get(self.generation) })
        } else {
            None
        }
    }
}

//
//  Implementation Details
//

fn hash<Q, H>(key: &Q, hook: &H) -> Hash
where
    Q: ?Sized + hash::Hash,
    H: hash::BuildHasher,
{
    use self::hash::Hasher;

    let mut hasher = hook.build_hasher();
    key.hash(&mut hasher);
    Hash(hasher.finish() as usize)
}

//  The hash of an element.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
struct Hash(pub usize);

//  A single Bucket.
struct Bucket<T>(cell::Cell<*mut Element<T>>, marker::PhantomData<T>);

impl<T> Bucket<T> {
    //  Returns whether the bucket is allocated, or not.
    fn is_allocated(&self) -> bool {
        !self.0.get().is_null()
    }

    //  Allocates a bucket of the given capacity.
    //
    //  Initializes the bucket, as well.
    //
    //  #   Safety
    //
    //  -   Assumes a single writer thread.
    unsafe fn allocate<A: Allocator>(&self, capacity: BucketCapacity, allocator: &A) -> Result<()> {
        //  May already be allocated.
        if self.is_allocated() {
            return Ok(());
        }

        let layout = Self::allocation_layout(capacity)?;

        //  Safety:
        //  -   The layout is valid.
        let ptr = unsafe { allocator.allocate(layout) };

        if ptr.is_null() {
            return Err(Failure::OutOfMemory);
        }

        //  Safety:
        //  -   The pointer is correctly aligned.
        let ptr = ptr as *mut Element<T>;

        self.0.set(ptr);

        for offset in 0..capacity.0 {
            //  Safety:
            //  -   The result is within bounds of the allocation.
            let e = unsafe { ptr.add(offset) };

            //  Safety:
            //  -   Exclusive access is guaranteed as it as not been leaked yet.
            unsafe { ptr::write(e, Element::new()) };
        }

        Ok(())
    }

    //  Deallocates a bucket of the given capacity, if allocated.
    //
    //  #   Safety
    //
    //  -   Assumes a single writer thread.
    //  -   Assumes that the capacity matches that of the allocation.
    unsafe fn deallocate<A: Allocator>(&self, capacity: BucketCapacity, allocator: &A) {
        if !self.is_allocated() {
            return;
        }

        let layout = match Self::allocation_layout(capacity) {
            Ok(layout) => layout,
            Err(_) => {
                //  Safety:
                //  -   Cannot error, it succeeded during the allocation.
                debug_assert!(false, "{:?} succeeded in allocation!", capacity);
                unsafe { std::hint::unreachable_unchecked() }
            }
        };

        let ptr = self.0.get();

        //  Pre-pooping your pants.
        //
        //  If `deallocate` panicks, there is no guarantee the pointer is still usable.
        self.0.set(ptr::null_mut());

        //  Safety:
        //  -   The pointer matches the pointer of the allocation.
        //  -   The layout matches the layout of the allocation.
        unsafe { allocator.deallocate(ptr as *mut u8, layout) };
    }

    //  Returns a slice of the Bucket elements.
    //
    //  #   Safety
    //
    //  -   Assumes that the capacity matches the bucket.
    unsafe fn get_slice(&self, capacity: BucketCapacity) -> &[Element<T>] {
        let ptr = self.0.get();

        //  Safety:
        //  -   The capacity is assumed to match.
        unsafe { slice::from_raw_parts(ptr as *const _, capacity.0) }
    }

    //  Returns a slice of the Bucket elements.
    //
    //  #   Safety
    //
    //  -   Assumes that the capacity matches the bucket.
    unsafe fn get_slice_mut(&mut self, capacity: BucketCapacity) -> &mut [Element<T>] {
        let ptr = self.0.get();

        //  Safety:
        //  -   The capacity is assumed to match.
        unsafe { slice::from_raw_parts_mut(ptr, capacity.0) }
    }

    //  Clears a bucket of its elements.
    //
    //  #   Safety
    //
    //  -   Assumes that the capacity matches the bucket.
    unsafe fn clear(&mut self, capacity: BucketCapacity) {
        //  Safety:
        //  -   The capacity is assumed to match.
        let slice = unsafe { self.get_slice_mut(capacity) };

        for e in slice {
            e.drop();
        }
    }

    //  Finds the element.
    //
    //  Returns Option<&Element> if the element is found.
    //
    //  #   Safety
    //
    //  -   Assumes that `generation` is less than the current size of the collection.
    //  -   Assumes that `capacity` matches the capacity of the collection.
    unsafe fn find<Q>(
        &self,
        key: &Q,
        hash: Hash,
        generation: Generation,
        capacity: BucketCapacity,
    ) -> Option<&Element<T>>
    where
        T: Key,
        T::Key: Borrow<Q>,
        Q: ?Sized + Eq,
    {
        //  Safety:
        //  -   `generation` is less than the current size of the collection, per pre-condition.
        //  -   `capcaity` matches the capacity of the collection, per pre-condition.
        let entry = unsafe { self.entry(key, hash, generation, capacity) };
        entry.occupied()
    }

    //  Looks up the element.
    //
    //  Returns either the element, or the location at which it could be inserted.
    //
    //  #   Safety
    //
    //  -   Assumes that `generation` is less than the current size of the collection.
    //  -   Assumes that `capacity` matches the capacity of the collection.
    unsafe fn entry<Q>(&self, key: &Q, hash: Hash, generation: Generation, capacity: BucketCapacity) -> Entry<'_, T>
    where
        T: Key,
        T::Key: Borrow<Q>,
        Q: ?Sized + Eq,
    {
        //  Safety:
        //  -   `capacity` matches that of the collection.
        let slice = unsafe { self.get_slice(capacity) };
        debug_assert!(slice.len() >= 2);
        debug_assert!(slice.len().count_ones() == 1);

        let (head, tail) = {
            let point = hash.0 & (slice.len() - 1);
            slice.split_at(point)
        };

        for e in tail {
            //  Safety:
            //  -   `generation` is the current generation.
            let candidate = unsafe { e.get(generation) };

            if let Some(candidate) = candidate {
                if candidate.key().borrow() == key {
                    return Entry::Occupied(e);
                }
            } else {
                return Entry::Vacant(e);
            }
        }

        for e in head {
            //  Safety:
            //  -   `generation` is the current generation.
            let candidate = unsafe { e.get(generation) };

            if let Some(candidate) = candidate {
                if candidate.key().borrow() == key {
                    return Entry::Occupied(e);
                }
            } else {
                return Entry::Vacant(e);
            }
        }

        //  Safety:
        //  -   A bucket never has more than HALF its elements initialized.
        //  -   A bucket has a capacity of at least 2.
        //  -   Ergo, either head or tail contained an empty spot.
        debug_assert!(false);
        unsafe { hint::unreachable_unchecked() };
    }

    //  Computes the layout for a given capacity.
    //
    //  #   Fails
    //
    //  -   If the necessary size overflows.
    fn allocation_layout(capacity: BucketCapacity) -> Result<Layout> {
        let size = mem::size_of::<Element<T>>();
        let alignment = mem::align_of::<Element<T>>();

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

//  The location of an element, which or may not be initialized.
enum Entry<'a, T> {
    //  The element was located.
    Occupied(&'a Element<T>),
    //  The element can be inserted here, if on the writer thread.
    Vacant(&'a Element<T>),
}

impl<'a, T> Entry<'a, T> {
    //  Returns whether the entry is occupied, or not.
    fn is_occupied(&self) -> bool {
        matches!(self, Entry::Occupied(_))
    }

    //  Returns the element, if occupied.
    fn occupied(&self) -> Option<&'a Element<T>> {
        if let Entry::Occupied(e) = self {
            Some(e)
        } else {
            None
        }
    }

    //  Returns the element, if vacant.
    fn vacant(&self) -> Option<&'a Element<T>> {
        if let Entry::Vacant(e) = self {
            Some(e)
        } else {
            None
        }
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

    //  A value which may panic on drop.
    #[derive(Debug)]
    pub struct PanickyEq(u32, bool);

    impl PanickyEq {
        //  Creates a normal instance.
        pub fn new(value: u32) -> Self {
            Self(value, false)
        }

        //  Creates a panicky instance.
        pub fn panicky(value: u32) -> Self {
            Self(value, true)
        }
    }

    impl Key for PanickyEq {
        type Key = Self;

        fn key(&self) -> &Self {
            self
        }
    }

    impl hash::Hash for PanickyEq {
        fn hash<H: hash::Hasher>(&self, hasher: &mut H) {
            self.0.hash(hasher)
        }
    }

    impl Eq for PanickyEq {}

    impl PartialEq for PanickyEq {
        fn eq(&self, other: &Self) -> bool {
            if self.1 || other.1 {
                panic!("{:?} <> {:?}", self, other);
            }
            self.0 == other.0
        }
    }

    #[test]
    fn bucket_allocation_layout() {
        fn allocation_layout<T>(capacity: usize) -> Result<usize> {
            match Bucket::<T>::allocation_layout(BucketCapacity(capacity)) {
                Ok(layout) => {
                    assert_eq!(mem::align_of::<T>(), layout.align());
                    Ok(layout.size())
                }
                Err(error) => Err(error),
            }
        }

        const CAPACITY_BOUNDARY: usize = usize::MAX / 16;

        assert_eq!(Ok(16), allocation_layout::<u64>(1));
        assert_eq!(Ok(64), allocation_layout::<u64>(4));
        assert_eq!(Ok(40), allocation_layout::<[u64; 4]>(1));

        assert_eq!(Ok(CAPACITY_BOUNDARY * 16), allocation_layout::<u64>(CAPACITY_BOUNDARY));
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
        let allocator = TestAllocator::new(1);

        let bucket = Bucket::<SpyElement<'_>>::default();
        let allocated = unsafe { bucket.allocate(BucketCapacity(1), &allocator) };

        assert_eq!(Ok(()), allocated);

        let allocation = allocator.allocations().last().copied().unwrap();

        assert_eq!(mem::size_of::<usize>() * 2, allocation.size);
        assert_eq!(mem::align_of::<usize>(), allocation.alignment);
    }

    #[test]
    fn bucket_allocate_skip() {
        let allocator = TestAllocator::new(1);

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
        let allocator = TestAllocator::new(1);

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

        let allocator = TestAllocator::new(1);

        let mut bucket = Bucket::<SpyElement<'_>>::default();
        let allocated = unsafe { bucket.allocate(capacity, &allocator) };

        assert_eq!(Ok(()), allocated);

        let count = SpyCount::zero();
        let uninitialized = unsafe { bucket.get_slice_mut(capacity) };

        for element in &mut uninitialized[..initialized] {
            unsafe { element.set(Generation(0), SpyElement::new(&count)) };
        }

        assert_eq!(initialized, count.get());

        unsafe { bucket.clear(capacity) };

        assert_eq!(0, count.get());
    }

    #[test]
    #[should_panic]
    fn bucket_array_zero_sized() {
        BucketArray::<(), DEFAULT_BUCKETS>::default();
    }

    #[test]
    fn bucket_array_get_mut() {
        let hooks = TestHooks::unlimited();

        let count = SpyCount::zero();
        let collection = vec![
            SpyKey::new(1, &count),
            SpyKey::new(2, &count),
            SpyKey::new(3, &count),
            SpyKey::new(4, &count),
        ];

        let mut buckets: BucketArray<_, DEFAULT_BUCKETS> = BucketArray::default();
        let capacity = Capacity::new(1, DEFAULT_BUCKETS);

        let (size, failure) = unsafe { buckets.as_slice().try_extend(collection, Size(0), capacity, &hooks) };

        assert_eq!(Size(4), size);
        assert_eq!(None, failure);

        assert!(unsafe { buckets.get_mut(&2, size, capacity, &hooks) }.is_some());
        assert!(unsafe { buckets.get_mut(&7, size, capacity, &hooks) }.is_none());
    }

    #[test]
    fn bucket_array_push_bucket() {
        let allocator = TestAllocator::unlimited();

        let buckets = BucketArray::<SpyElement<'static>, DEFAULT_BUCKETS>::default();
        let capacity = Capacity::new(1, DEFAULT_BUCKETS);

        unsafe {
            buckets
                .as_slice()
                .push_bucket(NumberBuckets(0), capacity, &allocator)
                .unwrap();
            buckets
                .as_slice()
                .push_bucket(NumberBuckets(1), capacity, &allocator)
                .unwrap();
            buckets
                .as_slice()
                .push_bucket(NumberBuckets(2), capacity, &allocator)
                .unwrap();
        }

        assert_eq!(vec![32, 32, 64], allocator.allocation_sizes());

        for index in 0..3 {
            assert!(buckets.0[index].is_allocated());
        }

        for index in 4..DEFAULT_BUCKETS {
            assert!(!buckets.0[index].is_allocated());
        }
    }

    #[test]
    fn bucket_array_push_bucket_out_of_buckets() {
        const NUMBER_BUCKETS: usize = 3;

        let allocator = TestAllocator::unlimited();

        let buckets = BucketArray::<SpyElement<'static>, DEFAULT_BUCKETS>::default();
        let capacity = Capacity::new(1, NUMBER_BUCKETS);

        let pushed = unsafe {
            buckets
                .as_slice()
                .push_bucket(NumberBuckets(NUMBER_BUCKETS - 1), capacity, &allocator)
        };
        assert_eq!(Ok(NumberBuckets(NUMBER_BUCKETS)), pushed);

        let pushed = unsafe {
            buckets
                .as_slice()
                .push_bucket(NumberBuckets(NUMBER_BUCKETS), capacity, &allocator)
        };
        assert_eq!(Err(Failure::OutOfBuckets), pushed);
    }

    #[test]
    fn bucket_array_push_bucket_out_of_memory() {
        let allocator = TestAllocator::default();

        let buckets = BucketArray::<SpyElement<'static>, DEFAULT_BUCKETS>::default();
        let capacity = Capacity::new(1, DEFAULT_BUCKETS);

        let pushed = unsafe { buckets.as_slice().push_bucket(NumberBuckets(0), capacity, &allocator) };
        assert_eq!(Err(Failure::OutOfMemory), pushed);
    }

    #[test]
    fn bucket_array_try_reserve() {
        let allocator = TestAllocator::unlimited();

        let buckets = BucketArray::<SpyElement<'static>, DEFAULT_BUCKETS>::default();
        let capacity = Capacity::new(1, DEFAULT_BUCKETS);

        let reserved = unsafe { buckets.as_slice().try_reserve(Size(17), Size(0), capacity, &allocator) };

        assert_eq!(Ok(()), reserved);
        assert_eq!(vec![32, 32, 64, 128, 256, 512], allocator.allocation_sizes());
        assert_eq!(NumberBuckets(6), buckets.as_slice().number_buckets());

        for index in 0..6 {
            assert!(buckets.0[index].is_allocated());
        }

        for index in 6..DEFAULT_BUCKETS {
            assert!(!buckets.0[index].is_allocated());
        }
    }

    #[test]
    #[ignore] //  Too expensive with MIRI
    fn bucket_array_try_reserve_all() {
        let allocator = TestAllocator::unlimited();

        let buckets = BucketArray::<i32, DEFAULT_BUCKETS>::default();
        let capacity = Capacity::new(1, DEFAULT_BUCKETS);

        let reserved = unsafe {
            buckets
                .as_slice()
                .try_reserve(Size(1024 * 1024), Size(0), capacity, &allocator)
        };

        assert_eq!(Err(Failure::OutOfBuckets), reserved);
        assert_eq!(DEFAULT_BUCKETS, allocator.allocations().len());
        assert_eq!(NumberBuckets(DEFAULT_BUCKETS), buckets.as_slice().number_buckets());

        for index in 0..DEFAULT_BUCKETS {
            assert!(buckets.0[index].is_allocated());
        }
    }

    #[test]
    fn bucket_array_try_reserve_elements_overflow() {
        let allocator = TestAllocator::new(0);

        let buckets = BucketArray::<SpyElement<'static>, DEFAULT_BUCKETS>::default();
        let capacity = Capacity::new(1, DEFAULT_BUCKETS);

        let half_usize = Size(usize::MAX / 2 + 1);

        let reserved = unsafe {
            buckets
                .as_slice()
                .try_reserve(half_usize, half_usize, capacity, &allocator)
        };

        assert_eq!(Err(Failure::ElementsOverflow), reserved);
    }

    #[test]
    fn bucket_array_try_reserve_out_of_buckets() {
        const NUMBER_BUCKETS: usize = 3;

        let allocator = TestAllocator::unlimited();

        let buckets = BucketArray::<SpyElement<'static>, DEFAULT_BUCKETS>::default();
        let capacity = Capacity::new(1, NUMBER_BUCKETS);

        let extra = Size(1usize << NUMBER_BUCKETS);

        let reserved = unsafe { buckets.as_slice().try_reserve(extra, Size(0), capacity, &allocator) };

        assert_eq!(Err(Failure::OutOfBuckets), reserved);
        assert_eq!(vec![32, 32, 64], allocator.allocation_sizes());
        assert_eq!(NumberBuckets(3), buckets.as_slice().number_buckets());

        for index in 0..NUMBER_BUCKETS {
            assert!(buckets.0[index].is_allocated());
        }

        for index in NUMBER_BUCKETS..DEFAULT_BUCKETS {
            assert!(!buckets.0[index].is_allocated());
        }
    }

    #[test]
    fn bucket_array_try_reserve_out_of_memory() {
        const NUMBER_BUCKETS: usize = 3;

        let allocator = TestAllocator::new(NUMBER_BUCKETS);

        let buckets = BucketArray::<SpyElement<'static>, DEFAULT_BUCKETS>::default();
        let capacity = Capacity::new(1, DEFAULT_BUCKETS);

        let extra = Size(1usize << NUMBER_BUCKETS);

        let reserved = unsafe { buckets.as_slice().try_reserve(extra, Size(0), capacity, &allocator) };

        assert_eq!(Err(Failure::OutOfMemory), reserved);
        assert_eq!(vec![32, 32, 64], allocator.allocation_sizes());
        assert_eq!(NumberBuckets(3), buckets.as_slice().number_buckets());

        for index in 0..NUMBER_BUCKETS {
            assert!(buckets.0[index].is_allocated());
        }

        for index in NUMBER_BUCKETS..DEFAULT_BUCKETS {
            assert!(!buckets.0[index].is_allocated());
        }
    }

    #[test]
    fn bucket_array_try_insert() {
        let hooks = TestHooks::unlimited();

        let count = SpyCount::zero();

        let buckets = BucketArray::<SpyKey<'_>, DEFAULT_BUCKETS>::default();
        let capacity = Capacity::new(1, DEFAULT_BUCKETS);

        let try_insert = |counter: usize| -> Result<Size> {
            let (size, _) = unsafe {
                let value = SpyKey::new(counter as u64, &count);
                buckets.as_slice().try_insert(value, Size(counter), capacity, &hooks)?
            };
            Ok(size)
        };

        let inserted = try_insert(0);

        assert_eq!(Ok(Size(1)), inserted);
        assert_eq!(vec![48], hooks.allocation_sizes());

        let inserted = try_insert(1);

        assert_eq!(Ok(Size(2)), inserted);
        assert_eq!(vec![48, 48], hooks.allocation_sizes());

        let inserted = try_insert(2);

        assert_eq!(Ok(Size(3)), inserted);
        assert_eq!(vec![48, 48, 96], hooks.allocation_sizes());

        let inserted = try_insert(3);

        assert_eq!(Ok(Size(4)), inserted);
        assert_eq!(vec![48, 48, 96], hooks.allocation_sizes());
    }

    #[test]
    fn bucket_array_try_insert_out_of_buckets() {
        const NUMBER_BUCKETS: usize = 2;

        let hooks = TestHooks::new(NUMBER_BUCKETS);

        let count = SpyCount::zero();

        let buckets = BucketArray::<SpyKey<'_>, DEFAULT_BUCKETS>::default();
        let capacity = Capacity::new(1, NUMBER_BUCKETS);

        let try_insert = |counter: usize| -> Result<Size> {
            let (size, _) = unsafe {
                let value = SpyKey::new(counter as u64, &count);
                buckets.as_slice().try_insert(value, Size(counter), capacity, &hooks)?
            };
            Ok(size)
        };

        let inserted = try_insert(0);

        assert_eq!(Ok(Size(1)), inserted);
        assert_eq!(vec![48], hooks.allocation_sizes());

        let inserted = try_insert(1);

        assert_eq!(Ok(Size(2)), inserted);
        assert_eq!(vec![48, 48], hooks.allocation_sizes());

        let inserted = try_insert(2);

        assert_eq!(Err(Failure::OutOfBuckets), inserted);
        assert_eq!(vec![48, 48], hooks.allocation_sizes());
    }

    #[test]
    fn bucket_array_try_insert_out_of_memory() {
        const NUMBER_BUCKETS: usize = 2;

        let hooks = TestHooks::new(NUMBER_BUCKETS);

        let count = SpyCount::zero();

        let buckets = BucketArray::<SpyKey<'_>, DEFAULT_BUCKETS>::default();
        let capacity = Capacity::new(1, DEFAULT_BUCKETS);

        let try_insert = |counter: usize| -> Result<Size> {
            let (size, _) = unsafe {
                let value = SpyKey::new(counter as u64, &count);
                buckets.as_slice().try_insert(value, Size(counter), capacity, &hooks)?
            };
            Ok(size)
        };

        let inserted = try_insert(0);

        assert_eq!(Ok(Size(1)), inserted);
        assert_eq!(vec![48], hooks.allocation_sizes());

        let inserted = try_insert(1);

        assert_eq!(Ok(Size(2)), inserted);
        assert_eq!(vec![48, 48], hooks.allocation_sizes());

        let inserted = try_insert(2);

        assert_eq!(Err(Failure::OutOfMemory), inserted);
        assert_eq!(vec![48, 48], hooks.allocation_sizes());
    }

    #[test]
    fn bucket_array_try_extend() {
        let hooks = TestHooks::new(usize::MAX);

        let count = SpyCount::zero();
        let collection = vec![
            SpyKey::new(1, &count),
            SpyKey::new(2, &count),
            SpyKey::new(3, &count),
            SpyKey::new(4, &count),
        ];

        let buckets = BucketArray::<SpyKey<'_>, DEFAULT_BUCKETS>::default();
        let capacity = Capacity::new(1, DEFAULT_BUCKETS);

        let (size, failure) = unsafe { buckets.as_slice().try_extend(collection, Size(0), capacity, &hooks) };

        assert_eq!(Size(4), size);
        assert_eq!(None, failure);
        assert_eq!(vec![48, 48, 96], hooks.allocation_sizes());
    }

    #[test]
    fn bucket_array_try_extend_out_of_buckets() {
        const NUMBER_BUCKETS: usize = 3;

        let hooks = TestHooks::new(NUMBER_BUCKETS + 1);

        let count = SpyCount::zero();
        let collection = vec![
            SpyKey::new(1, &count),
            SpyKey::new(2, &count),
            SpyKey::new(3, &count),
            SpyKey::new(4, &count),
            SpyKey::new(5, &count),
            SpyKey::new(6, &count),
        ];

        let buckets = BucketArray::<SpyKey<'_>, DEFAULT_BUCKETS>::default();
        let capacity = Capacity::new(1, NUMBER_BUCKETS);

        let (size, failure) = unsafe { buckets.as_slice().try_extend(collection, Size(0), capacity, &hooks) };

        assert_eq!(Size(4), size);
        assert_eq!(Some(Failure::OutOfBuckets), failure);
        assert_eq!(vec![48, 48, 96], hooks.allocation_sizes());
    }

    #[test]
    fn bucket_array_try_extend_out_of_memory() {
        const NUMBER_BUCKETS: usize = 3;

        let hooks = TestHooks::new(NUMBER_BUCKETS);

        let count = SpyCount::zero();
        let collection = vec![
            SpyKey::new(1, &count),
            SpyKey::new(2, &count),
            SpyKey::new(3, &count),
            SpyKey::new(4, &count),
            SpyKey::new(5, &count),
            SpyKey::new(6, &count),
        ];

        let buckets = BucketArray::<SpyKey<'_>, DEFAULT_BUCKETS>::default();
        let capacity = Capacity::new(1, DEFAULT_BUCKETS);

        let (size, failure) = unsafe { buckets.as_slice().try_extend(collection, Size(0), capacity, &hooks) };

        assert_eq!(Size(4), size);
        assert_eq!(Some(Failure::OutOfMemory), failure);
        assert_eq!(vec![48, 48, 96], hooks.allocation_sizes());
    }

    #[test]
    fn bucket_array_shrink_none() {
        let hooks = TestHooks::unlimited();

        let count = SpyCount::zero();
        let collection = vec![
            SpyKey::new(1, &count),
            SpyKey::new(2, &count),
            SpyKey::new(3, &count),
            SpyKey::new(4, &count),
        ];

        let buckets = BucketArray::<SpyKey<'_>, DEFAULT_BUCKETS>::default();
        let capacity = Capacity::new(1, DEFAULT_BUCKETS);

        unsafe {
            buckets.as_slice().try_extend(collection, Size(0), capacity, &hooks);
        }

        assert_eq!(vec![48, 48, 96], hooks.allocation_sizes());

        unsafe {
            buckets.as_slice().shrink(Size(4), capacity, &hooks);
        }

        assert_eq!(vec![48, 48, 96], hooks.allocation_sizes());
    }

    #[test]
    fn bucket_array_shrink_partial() {
        let hooks = TestHooks::unlimited();

        let count = SpyCount::zero();
        let collection = vec![
            SpyKey::new(1, &count),
            SpyKey::new(2, &count),
            SpyKey::new(3, &count),
            SpyKey::new(4, &count),
        ];

        let buckets = BucketArray::<SpyKey<'_>, DEFAULT_BUCKETS>::default();
        let capacity = Capacity::new(1, DEFAULT_BUCKETS);

        unsafe {
            let _ = buckets.as_slice().try_reserve(Size(16), Size(0), capacity, &hooks);
        }

        assert_eq!(vec![48, 48, 96, 192, 384], hooks.allocation_sizes());

        unsafe {
            buckets.as_slice().try_extend(collection, Size(0), capacity, &hooks);
        }

        unsafe {
            buckets.as_slice().shrink(Size(4), capacity, &hooks);
        }

        assert_eq!(vec![48, 48, 96], hooks.allocation_sizes());
    }

    #[test]
    fn bucket_array_shrink_all() {
        let allocator = TestAllocator::unlimited();

        let buckets = BucketArray::<SpyKey<'_>, DEFAULT_BUCKETS>::default();
        let capacity = Capacity::new(1, DEFAULT_BUCKETS);

        unsafe {
            let _ = buckets.as_slice().try_reserve(Size(16), Size(0), capacity, &allocator);
        }

        assert_eq!(vec![48, 48, 96, 192, 384], allocator.allocation_sizes());

        unsafe {
            buckets.as_slice().shrink(Size(0), capacity, &allocator);
        }

        assert_eq!(0, allocator.allocations().len());
    }

    #[test]
    fn bucket_array_clear_empty() {
        let allocator = TestAllocator::unlimited();

        let buckets = BucketArray::<SpyKey<'_>, DEFAULT_BUCKETS>::default();
        let capacity = Capacity::new(1, DEFAULT_BUCKETS);

        unsafe {
            let _ = buckets.as_slice().try_reserve(Size(16), Size(0), capacity, &allocator);
        }

        let mut buckets = buckets;
        unsafe {
            buckets.clear(Size(0), capacity);
        }
    }

    #[test]
    fn bucket_array_clear_all() {
        let hooks = TestHooks::unlimited();

        let count = SpyCount::zero();
        let collection = vec![
            SpyKey::new(1, &count),
            SpyKey::new(2, &count),
            SpyKey::new(3, &count),
            SpyKey::new(4, &count),
        ];

        let buckets = BucketArray::<SpyKey<'_>, DEFAULT_BUCKETS>::default();
        let capacity = Capacity::new(1, DEFAULT_BUCKETS);

        unsafe {
            buckets.as_slice().try_extend(collection, Size(0), capacity, &hooks);
        }

        let mut buckets = buckets;
        unsafe {
            buckets.clear(Size(4), capacity);
        }

        assert_eq!(0, count.get());
    }

    #[test]
    fn bucket_array_panic_allocate() {
        use std::panic::{catch_unwind, AssertUnwindSafe};

        const NB_ALLOCATIONS: usize = 2;

        let allocator = PanickyAllocator::default();
        allocator.allowed.set(NB_ALLOCATIONS);

        let buckets = BucketArray::<SpyKey<'static>, DEFAULT_BUCKETS>::default();
        let capacity = Capacity::new(1, DEFAULT_BUCKETS);

        let panicked = catch_unwind(AssertUnwindSafe(|| unsafe {
            let _ = buckets.as_slice().try_reserve(Size(4), Size(0), capacity, &allocator);
        }));
        assert!(panicked.is_err());

        assert!(buckets.0[0].is_allocated());
        assert!(buckets.0[1].is_allocated());
        assert!(!buckets.0[NB_ALLOCATIONS].is_allocated());
    }

    #[test]
    fn bucket_array_panic_deallocate() {
        use std::panic::{catch_unwind, AssertUnwindSafe};

        const FAILED_DEALLOCATION: usize = 1;

        let allocator = TestAllocator::unlimited();

        let buckets = BucketArray::<SpyKey<'static>, DEFAULT_BUCKETS>::default();
        let capacity = Capacity::new(1, DEFAULT_BUCKETS);

        unsafe {
            let _ = buckets.as_slice().try_reserve(Size(4), Size(0), capacity, &allocator);
        }
        assert_eq!(3, allocator.allocations.borrow().len());

        allocator.allocations.borrow_mut().remove(FAILED_DEALLOCATION);

        let panicked = catch_unwind(AssertUnwindSafe(|| {
            unsafe { buckets.as_slice().shrink(Size(0), capacity, &allocator) };
        }));
        assert!(panicked.is_err());

        assert!(!buckets.0[0].is_allocated());
        assert!(!buckets.0[FAILED_DEALLOCATION].is_allocated());
        assert!(buckets.0[2].is_allocated());
    }

    #[test]
    fn bucket_array_panic_next() {
        use std::panic::{catch_unwind, AssertUnwindSafe};

        let hooks = TestHooks::unlimited();

        let buckets: BucketArray<_, DEFAULT_BUCKETS> = BucketArray::default();
        let capacity = Capacity::new(1, DEFAULT_BUCKETS);

        let panicked = catch_unwind(AssertUnwindSafe(|| unsafe {
            let collection = PanickyIterator::new(3);
            buckets.as_slice().try_extend(collection, Size(0), capacity, &hooks);
        }));
        assert!(panicked.is_err());

        assert!(buckets.0[0].is_allocated());
        assert!(buckets.0[1].is_allocated());
        assert!(buckets.0[2].is_allocated());
        assert!(!buckets.0[3].is_allocated());
    }

    #[test]
    fn bucket_array_panic_hash_get() {
        use std::panic::{catch_unwind, AssertUnwindSafe};

        let hooks = TestHooks::unlimited();

        let buckets: BucketArray<_, DEFAULT_BUCKETS> = BucketArray::default();
        let capacity = Capacity::new(1, DEFAULT_BUCKETS);

        unsafe {
            buckets.as_slice().try_extend(0..4, Size(0), capacity, &hooks);
        }

        hooks.set_panic_hash(0);

        let panicked = catch_unwind(AssertUnwindSafe(|| {
            unsafe { buckets.as_slice().get(&1, Size(4), capacity, &hooks) };
        }));
        assert!(panicked.is_err());
    }

    #[test]
    fn bucket_array_panic_hash_insert() {
        use std::panic::{catch_unwind, AssertUnwindSafe};

        let hooks = TestHooks::unlimited();
        hooks.set_panic_hash(3);

        let buckets: BucketArray<_, DEFAULT_BUCKETS> = BucketArray::default();
        let capacity = Capacity::new(1, DEFAULT_BUCKETS);

        let panicked = catch_unwind(AssertUnwindSafe(|| unsafe {
            buckets.as_slice().try_extend(0..4, Size(0), capacity, &hooks);
        }));
        assert!(panicked.is_err());

        assert!(buckets.0[0].is_allocated());
        assert!(buckets.0[1].is_allocated());
        assert!(buckets.0[2].is_allocated());
        assert!(!buckets.0[3].is_allocated());
    }

    #[test]
    fn bucket_array_panic_eq_get() {
        use std::panic::{catch_unwind, AssertUnwindSafe};

        let hooks = TestHooks::unlimited();

        let collection = vec![
            PanickyEq::new(0),
            PanickyEq::new(1),
            PanickyEq::new(2),
            PanickyEq::new(3),
        ];

        let buckets: BucketArray<_, DEFAULT_BUCKETS> = BucketArray::default();
        let capacity = Capacity::new(1, DEFAULT_BUCKETS);

        unsafe {
            buckets.as_slice().try_extend(collection, Size(0), capacity, &hooks);
        }

        let panicked = catch_unwind(AssertUnwindSafe(|| {
            unsafe {
                buckets
                    .as_slice()
                    .get(&PanickyEq::panicky(3), Size(4), capacity, &hooks)
            };
        }));
        assert!(panicked.is_err());
    }

    #[test]
    fn bucket_array_panic_eq_insert() {
        use std::panic::{catch_unwind, AssertUnwindSafe};

        let hooks = TestHooks::unlimited();

        let collection = vec![
            PanickyEq::new(0),
            PanickyEq::new(1),
            PanickyEq::panicky(2),
            PanickyEq::new(3),
        ];

        let buckets: BucketArray<_, DEFAULT_BUCKETS> = BucketArray::default();
        let capacity = Capacity::new(1, DEFAULT_BUCKETS);

        let panicked = catch_unwind(AssertUnwindSafe(|| unsafe {
            buckets.as_slice().try_extend(collection, Size(0), capacity, &hooks);
        }));
        assert!(panicked.is_err());

        assert!(buckets.0[0].is_allocated());
        assert!(buckets.0[1].is_allocated());
        assert!(!buckets.0[2].is_allocated());
    }

    #[test]
    fn bucket_iterator() {
        let array: [Element<i32>; 10] = Default::default();

        for &i in [1, 3, 5, 7, 9].iter() {
            unsafe { array[10 - i as usize].set(Generation(i as usize), i) };
        }

        {
            let vec: Vec<_> = unsafe { BucketIterator::new(&array, Generation(4)) }.collect();

            assert_eq!(
                vec![None, None, None, None, None, None, None, Some(&3), None, Some(&1)],
                vec
            );
        }

        {
            let vec: Vec<_> = unsafe { BucketIterator::new(&array, Generation(9)) }.collect();

            assert_eq!(
                vec![
                    None,
                    None,
                    None,
                    Some(&7),
                    None,
                    Some(&5),
                    None,
                    Some(&3),
                    None,
                    Some(&1)
                ],
                vec
            );
        }
    }
}
