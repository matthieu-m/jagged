//! The high-level API of the Buckets of the HashMap and HashSet.

pub use super::buckets::BucketArray;

use super::root::{borrow, fmt, hash, iter};

use super::allocator::Allocator;
use super::buckets::BucketIterator;
use super::capacity::{Capacity, BucketIndex, Size};
use super::element::Generation;
use super::failure::{Failure, Result};
use super::key::Key;

use self::borrow::Borrow;

//  Shared Reader
pub struct BucketsSharedReader<'a, T, H> {
    buckets: &'a BucketArray<T>,
    hook: &'a H,
    size: Size,
    capacity: Capacity,
}

impl<'a, T, H> BucketsSharedReader<'a, T, H> {
    //  Creates a new instance.
    //
    //  #   Safety
    //
    //  -   Assumes that `size` is less than the current size.
    pub unsafe fn new(
        buckets: &'a BucketArray<T>,
        hook: &'a H,
        size: Size,
        capacity: Capacity
    )
        -> Self
    {
        Self { buckets, hook, size, capacity }
    }

    //  Returns whether the instance contains any element, or not.
    pub fn is_empty(&self) -> bool { self.size.0 == 0 }

    //  Returns the number of elements contained in the instance.
    pub fn len(&self) -> usize { self.size.0 }

    //  Returns the current capacity of the instance.
    pub fn capacity(&self) -> usize {
        let nb_buckets = self.number_buckets();
        self.capacity.before_bucket(BucketIndex(nb_buckets)).0
    }

    //  Returns the maximum capacity achievable by the instance.
    pub fn max_capacity(&self) -> usize { self.capacity.max_capacity() }

    //  Returns the number of buckets currently used.
    pub fn number_buckets(&self) -> usize {
        let size = Size(self.len());
        self.capacity.number_buckets(size).0
    }

    //  Returns the maximum number of buckets.
    pub fn max_buckets(&self) -> usize { self.capacity.max_buckets().0 }

    //  Checks whether an element matches the key.
    pub fn contains_key<Q>(&self, key: &Q) -> bool
    where
        T: Key,
        T::Key: Borrow<Q>,
        H: hash::BuildHasher,
        Q: ?Sized + Eq + hash::Hash,
    {
        self.get(key).is_some()
    }

    //  Gets the element whose key matches.
    //
    //  Returns a reference to the element if it could be found.
    pub fn get<Q>(&self, key: &Q) -> Option<&'a T>
    where
        T: Key,
        T::Key: Borrow<Q>,
        H: hash::BuildHasher,
        Q: ?Sized + Eq + hash::Hash,
    {
        //  Safety:
        //  -   `self.size` is less than the current size of the collection.
        //  -   `self.capacity` matches the capacity of the collection.
        unsafe {
            self.buckets.get(key, self.size, self.capacity, self.hook)
        }
    }
}

impl<'a, T, H> Clone for BucketsSharedReader<'a, T, H> {
    fn clone(&self) -> Self { *self }
}

impl<'a, T, H> Copy for BucketsSharedReader<'a, T, H> {}

impl<'a, T, H> BucketsSharedReader<'a, T, H>
where
    T: fmt::Debug
{
    //  Formats the Debug representation of the buckets.
    pub fn debug(&self, name: &str, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} {{ capacity: {}, length: {}, buckets: [",
            name, self.capacity(), self.len())?;

        let generation = Generation(self.len());
        let nb_buckets = self.capacity.number_buckets(self.size);

        for index in 0..nb_buckets.0 {
            if index == 0 {
                write!(f, "[")?;
            } else {
                write!(f, ", [")?;
            }

            //  Safety:
            //  -   `index` is within bounds.
            //  -   `generation` is less than the current size of the collection.
            //  -   `self.capacity` matches the capacity of the collection.
            let bucket = unsafe {
                self.buckets.bucket(BucketIndex(index), generation, self.capacity)
            };

            for (index, e) in bucket.enumerate() {
                if index == 0 {
                    write!(f, " ")?;
                } else {
                    write!(f, ", ")?;
                }

                if let Some(e) = e {
                    write!(f, "{:?}", e)?;
                } else {
                    write!(f, "<none>")?;
                }
            }

            write!(f, " ]")?;
        }

        write!(f, "] }}")
    }
}

impl<'a, T, H> Eq for BucketsSharedReader<'a, T, H>
where
    T: Key + Eq,
    T::Key: Eq + hash::Hash,
    H: hash::BuildHasher
{}

impl<'a, T, H, OH> PartialEq<BucketsSharedReader<'a, T, OH>> for BucketsSharedReader<'a, T, H>
where
    T: Key + PartialEq,
    T::Key: Eq + hash::Hash,
    OH: hash::BuildHasher
{
    fn eq(&self, other: &BucketsSharedReader<'a, T, OH>) -> bool {
        if self.size != other.size {
            return false;
        }

        if self.buckets as *const _ == other.buckets as *const _ {
            return true;
        }

        self.into_iter().all(|e| Some(e) == other.get(e.key()))
    }
}

impl<'a, T, H> iter::IntoIterator for BucketsSharedReader<'a, T, H> {
    type Item = &'a T;
    type IntoIter = ElementIterator<'a, T>;

    fn into_iter(self) -> ElementIterator<'a, T> {
        ElementIterator::create(self)
    }
}

//  Shared Writer
pub struct BucketsSharedWriter<'a, T, H> {
    buckets: &'a BucketArray<T>,
    hook: &'a H,
    size: Size,
    capacity: Capacity,
}

impl<'a, T, H> BucketsSharedWriter<'a, T, H> {
    //  Creates a new instance.
    //
    //  #   Safety
    //
    //  -   Assumes that `size` exactly matches the current size.
    //  -   Assumes a single writer thread.
    pub unsafe fn new(
        buckets: &'a BucketArray<T>,
        hook: &'a H,
        size: Size,
        capacity: Capacity
    )
        -> Self
    {
        Self { buckets, hook, size, capacity }
    }

    //  Shrinks the buckets, releasing unused memory.
    pub fn shrink(self)
    where
        H: Allocator
    {
        //  Safety:
        //  -   size is the current size of the vector.
        //  -   invalidating the instance is unnecessary, but shrink being
        //      idempotent, there is no point in calling it twice in a row.
        unsafe { self.buckets.shrink(self.size, self.capacity, self.hook) }
    }

    //  Reserves buckets for up to `extra` elements.
    //
    //  #   Error
    //
    //  Returns an error if sufficient space cannot be reserved.
    pub fn try_reserve(&self, extra: Size) -> Result<()>
    where
        H: Allocator,
    {
        //  Safety:
        //  -   single writer thread.
        unsafe {
            self.buckets.try_reserve(extra, self.size, self.capacity, self.hook)
        }
    }

    //  Inserts the element.
    //
    //  Returns the new size. The size is not modified in case of failure.
    //
    //  #   Errors
    //
    //  Returns an error if the value cannot be inserted due to external factors.
    pub fn try_insert(self, element: T) -> Result<(Size, Option<T>)>
    where
        T: Key,
        T::Key: Eq + hash::Hash,
        H: Allocator + hash::BuildHasher,
    {
        //  Safety:
        //  -   size is the current size of the vector.
        //  -   the instance is invalidated by inserting, as size is modified.
        //  -   single writer thread.
        unsafe {
            self.buckets.try_insert(element, self.size, self.capacity, self.hook)
        }
    }

    //  Inserts the element.
    //
    //  Returns the new size. The size is not modified in case of failure.
    //
    //  #   Errors
    //
    //  Returns an error if the value cannot be inserted due to external factors.
    pub fn try_extend<C>(self, collection: C) -> (Size, Option<Failure>)
    where
        C: IntoIterator<Item = T>,
        T: Key,
        T::Key: Eq + hash::Hash,
        H: Allocator + hash::BuildHasher,
    {
        //  Safety:
        //  -   size is the current size of the vector.
        //  -   the instance is invalidated by inserting, as size is modified.
        //  -   single writer thread.
        unsafe {
            self.buckets.try_extend(collection, self.size, self.capacity, self.hook)
        }
    }
}

//  Exclusive Writer
pub struct BucketsExclusiveWriter<'a, T> {
    buckets: &'a mut BucketArray<T>,
    size: Size,
    capacity: Capacity,
}

impl<'a, T> BucketsExclusiveWriter<'a, T> {
    //  Creates a new instance.
    //
    //  #   Safety
    //
    //  -   Assumes that `size` exactly matches the current size.
    pub unsafe fn new(
        buckets: &'a mut BucketArray<T>,
        size: Size,
        capacity: Capacity
    )
        -> Self
    {
        Self { buckets, size, capacity }
    }

    //  Clears the buckets.
    pub fn clear(self) {
        //  Safety:
        //  -   size is the current size of the vector.
        //  -   the instance is invalidated by clearing, as size is modified.
        unsafe { self.buckets.clear(self.size, self.capacity) }
    }
}

/// ElementIterator
///
/// An iterator over the elements of a Vector.
///
/// Due to the jagged nature of the Vector, it may be less efficient than a
/// BucketIterator.
pub struct ElementIterator<'a, T> {
    buckets: &'a BucketArray<T>,
    generation: Generation,
    capacity: Capacity,
    index: BucketIndex,
    current: BucketIterator<'a, T>,
}

impl<'a, T> ElementIterator<'a, T> {
    //  Creates an instance of ElementIterator.
    fn create<H>(reader: BucketsSharedReader<'a, T, H>) -> Self {
        let buckets = reader.buckets;
        let generation = Generation(reader.size.0);
        let capacity = reader.capacity;
        let index = BucketIndex(0);

        //  Safety:
        //  -   `index` is within bounds.
        //  -   `generation` is less than the current size of the collection.
        //  -   `capacity` matches that of the collection.
        let current = unsafe { buckets.bucket(index, generation, capacity) };

        ElementIterator { buckets, generation, capacity, index, current }
    }
}

impl<'a, T> Clone for ElementIterator<'a, T> {
    fn clone(&self) -> Self {
        ElementIterator {
            buckets: self.buckets,
            generation: self.generation,
            capacity: self.capacity,
            index: self.index,
            current: self.current.clone(),
        }
    }
}

impl<'a, T> iter::Iterator for ElementIterator<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        let nb_buckets = self.capacity.number_buckets(Size(self.generation.0));

        if self.index.0 == nb_buckets.0 {
            return None;
        }

        loop {
            while let Some(e) = self.current.next() {
                if e.is_some() {
                    return e;
                }
            }

            self.index = BucketIndex(self.index.0 + 1);

            if self.index.0 == nb_buckets.0 {
                return None;
            }

            //  Safety:
            //  -   `self.index` is within bounds.
            //  -   `self.generation` is less than the current size of the collection.
            //  -   `self.capacity` matches the capacity of the collection.
            self.current = unsafe {
                self.buckets.bucket(self.index, self.generation, self.capacity)
            };
        }
    }
}
