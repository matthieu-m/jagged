//! The jagged buckets underlying the HashMap and HashSet.

use super::root::{borrow, cell, hash, hint, iter, marker, mem, ptr, slice};

use super::allocator::{Allocator, Layout};
use super::capacity::{Capacity, BucketCapacity, BucketIndex, NumberBuckets, Size};
use super::element::{Element, Generation};
use super::failure::{Failure, Result};
use super::key::Key;

use self::borrow::Borrow;

//  Tailored just so the default HashMap/HashSet takes exactly 3 cache lines.
pub const MAX_BUCKETS: usize = 20;

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
            let bucket = self.0.get_unchecked_mut(index);

            let capacity = capacity.of_bucket(BucketIndex(index));

            //  Safety:
            //  -   The capacity matches the bucket.
            bucket.clear(capacity);
        }
    }

    //  Shrinks the buckets, releasing unused memory.
    //
    //  #   Safety
    //
    //  -   Assumes a single writer thread.
    //  -   Assumes that `size` is exactly the current size of the collection.
    //  -   Assumes that `capacity` matches the capacity of the collection.
    pub unsafe fn shrink<A>(
        &self,
        size: Size,
        capacity: Capacity,
        allocator: &A,
    )
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
        extra: Size,
        size: Size,
        capacity: Capacity,
        allocator: &A,
    )
        -> Result<()>
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
            nb_buckets = self.push_bucket(nb_buckets, capacity, allocator)?;
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
    pub unsafe fn get<Q, H>(
        &self,
        key: &Q,
        size: Size,
        capacity: Capacity,
        hook: &H,
    )
        ->  Option<&T>
    where
        T: Key,
        T::Key: Borrow<Q>,
        Q: ?Sized + Eq + hash::Hash,
        H: hash::BuildHasher,
    {
        let hash = Self::hash(key, hook);

        let entry = self.entry(key, hash, size, capacity);

        entry.and_then(|e| e.occupied())
            //  Safety:
            //  -   The element is initialized, since the entry is occupied.
            .map(|e| e.get_unchecked())
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
    pub unsafe fn get_mut<Q, H>(
        &mut self,
        key: &Q,
        size: Size,
        capacity: Capacity,
        hook: &H,
    )
        ->  Option<&mut T>
    where
        T: Key,
        T::Key: Borrow<Q>,
        Q: ?Sized + Eq + hash::Hash,
        H: hash::BuildHasher,
    {
        if let Some(e) = self.get(key, size, capacity, hook) {
            let e: &T = e;
            let ptr: *mut T = e as *const _ as *mut _;
            //  Safety:
            //  -   Exclusive access, due to `&mut self`.
            Some(&mut *ptr)
        } else {
            None
        }
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
    )
        -> Result<(Size, Option<T>)>
    where
        T: Key,
        T::Key: Eq + hash::Hash,
        H: Allocator + hash::BuildHasher,
    {
        let hash = Self::hash(element.key(), hook);

        let generation = Generation(size.0);
        let new_size = Size(size.0 + 1);

        //  Safety:
        //  -   `size` is less than the current size of the collection.
        //  -   `capacity` matches the capacity of the collection.
        if let Some(entry) = self.entry(element.key(), hash, size, capacity) {
            let result = match entry {
                //  The element was found.
                Entry::Occupied(_) => Ok((size, Some(element))),
                //  A location for insertion was found.
                Entry::Vacant(location) => {
                    debug_assert!(
                        capacity.number_buckets(size) ==
                        capacity.number_buckets(new_size)
                    );
                    location.set(generation, element);
                    Ok((new_size, None))
                },
            };

            return result;
        }

        //  A new bucket is necessary.

        //  Safety:
        //  -   Single writer thread.
        let nb_buckets = capacity.number_buckets(size);
        let nb_buckets = self.push_bucket(nb_buckets, capacity, hook)?;
        debug_assert!(nb_buckets == capacity.number_buckets(new_size));

        let last_index = BucketIndex(nb_buckets.0 - 1);
        let last_capacity = capacity.of_bucket(last_index);

        //  Safety:
        //  -   The index is within bounds.
        let last_bucket = self.0.get_unchecked(last_index.0);

        //  Safety:
        //  -   `generation` is less than the current size of the collection.
        //  -   `capacity` matches the capacity of the collection.
        let entry = last_bucket.entry(element.key(), hash, generation, last_capacity);

        match entry {
            Entry::Vacant(location) => {
                location.set(generation, element);
                Ok((new_size, None))
            },
            //  Safety:
            //  -   A newly allocated bucket has no element.
            Entry::Occupied(_) => hint::unreachable_unchecked(),
        }
    }

    //  Inserts multiple elements to the collection.
    //
    //  Returns the new size of the collection.
    //
    //  #   Error
    //
    //  If the collection cannot be fully extended, this may leave the collection
    //  modified.
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
    )
        -> (Size, Option<Failure>)
    where
        C: IntoIterator<Item = T>,
        T: Key,
        T::Key: Eq + hash::Hash,
        H: Allocator + hash::BuildHasher,
    {
        let mut size = size;

        //  TODO: optimize to avoid repeated computations to obtain the current
        //  slice.
        for e in collection {
            size = match self.try_insert(e, size, capacity, hooks) {
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
    )
        -> BucketIterator<'_, T>
    {
        debug_assert!(bucket.0 < capacity.max_buckets().0);

        let capacity = capacity.of_bucket(bucket);

        //  Safety:
        //  -   `bucket` is within bounds.
        let bucket = self.0.get_unchecked(bucket.0);

        //  Safety:
        //  -   `capacity` matches the bucket.
        let slice = bucket.get_slice(capacity);

        //  Safety:
        //  -   `generation` is less than the current size of the collection.
        BucketIterator::new(slice, generation)
    }

    //  Looks up the element, or where it could be inserted.
    //
    //  #   Safety
    //
    //  -   Assumes that `generation` is less than the current size of the collection.
    //  -   Assumes that `capacity` matches the capacity of the collection.
    unsafe fn entry<Q>(
        &self,
        key: &Q,
        hash: Hash,
        size: Size,
        capacity: Capacity,
    )
        ->  Option<Entry<'_, T>>
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

        //  We only ever insert in the last bucket, as all previous buckets are
        //  full.
        let last_index = BucketIndex(nb_buckets.0 - 1);
        let last_capacity = capacity.of_bucket(last_index);

        let entry = {
            //  Safety:
            //  -   last_index is within bounds.
            let bucket = self.0.get_unchecked(last_index.0);

            bucket.entry(key, hash, generation, last_capacity)
        };

        if entry.is_occupied() {
            debug_assert!(entry.occupied().unwrap().get(generation).is_some());
            return Some(entry);
        }

        //  Iterate in reverse order as the latter buckets contain the most
        //  elements, and thus are more likely to contain the element of
        //  interest.
        for bucket in (0..last_index.0).rev() {
            let capacity = capacity.of_bucket(BucketIndex(bucket));

            //  Safety:
            //  -   bucket is within bounds.
            let bucket = self.0.get_unchecked(bucket);

            if let Some(e) = bucket.find(key, hash, generation, capacity) {
                debug_assert!(e.get(generation).is_some());
                return Some(Entry::Occupied(e));
            }
        }

        debug_assert!(entry.vacant().unwrap().get(generation).is_none());

        //  No vacancy if the last bucket is already fully loaded (50%).
        let last_size = capacity.size_bucket(last_index, size);

        if last_size.0 < last_capacity.0 / 2 {
            Some(entry)
        } else {
            None
        }
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
}

impl<T> Default for BucketArray<T> {
    fn default() -> Self {
        if mem::size_of::<T>() == 0 {
            panic_zero_sized_element();
        }
        Self(Default::default())
    }
}

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
        BucketIterator { bucket: self.bucket, generation: self.generation }
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

//  The hash of an element.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
struct Hash(pub usize);

//  A single Bucket.
struct Bucket<T>(cell::Cell<*mut Element<T>>, marker::PhantomData<T>);

impl<T> Bucket<T> {
    //  Returns whether the bucket is allocated, or not.
    fn is_allocated(&self) -> bool { !self.0.get().is_null() }

    //  Allocates a bucket of the given capacity.
    //
    //  Initializes the bucket, as well.
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
        let ptr = ptr as *mut Element<T>;

        self.0.set(ptr);

        for offset in 0..capacity.0 {
            //  Safety:
            //  -   The result is within bounds of the allocation.
            let e = ptr.add(offset);
            ptr::write(e, Element::new());
        }

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

    //  Returns a slice of the Bucket elements.
    //
    //  #   Safety
    //
    //  -   Assumes that the capacity matches the bucket.
    unsafe fn get_slice(&self, capacity: BucketCapacity) -> &[Element<T>] {
        let ptr = self.0.get();

        //  Safety:
        //  -   The capacity is assumed to match.
        slice::from_raw_parts(ptr as *const _, capacity.0)
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
        slice::from_raw_parts_mut(ptr, capacity.0)
    }

    //  Clears a bucket of its elements.
    //
    //  #   Safety
    //
    //  -   Assumes that the capacity matches the bucket.
    unsafe fn clear(&mut self, capacity: BucketCapacity) {
        //  Safety:
        //  -   The capacity is assumed to match.
        let slice = self.get_slice_mut(capacity);

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
    )
        ->  Option<&Element<T>>
    where
        T: Key,
        T::Key: Borrow<Q>,
        Q: ?Sized + Eq,
    {
        let entry = self.entry(key, hash, generation, capacity);
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
    unsafe fn entry<Q>(
        &self,
        key: &Q,
        hash: Hash,
        generation: Generation,
        capacity: BucketCapacity,
    )
        ->  Entry<'_, T>
    where
        T: Key,
        T::Key: Borrow<Q>,
        Q: ?Sized + Eq,
    {
        let slice = self.get_slice(capacity);
        debug_assert!(slice.len() >= 2);
        debug_assert!(slice.len().count_ones() == 1);

        let (head, tail) = {
            let point = hash.0 & (slice.len() - 1);
            slice.split_at(point)
        };

        for e in tail {
            if let Some(candidate) = e.get(generation) {
                if candidate.key().borrow() == key {
                    return Entry::Occupied(e);
                }
            } else {
                return Entry::Vacant(e);
            }
        }

        for e in head {
            if let Some(candidate) = e.get(generation) {
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
        hint::unreachable_unchecked();
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
        if let Entry::Occupied(_) = self {
            true
        } else {
            false
        }
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
}
