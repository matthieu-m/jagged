//! The HashSet

use super::root::{borrow, fmt, hash, hint, iter};

use super::{HashSetReader, HashSetSnapshot};

use super::atomic::AcqRelUsize;
use super::entry::Entry;
use super::failure::{Failure, Result};
use super::hashcore::HashHooks;
use super::hashcore::buckets_api::{
    BucketArray, BucketsExclusiveWriter, BucketsSharedReader, BucketsSharedWriter
};
use super::hashcore::capacity::{Capacity, BucketIndex, Size};

#[cfg(feature = "with-std")]
use super::hashcore::DefaultHashHooks;

//
//  Public Interface
//

/// `HashSet`
///
/// Limitation: the maximum number of buckets cannot be specified, due to the
///             lack of const generics.
#[cfg(not(feature = "with-std"))]
pub struct HashSet<T, H: HashHooks> {
    hooks: H,
    capacity: Capacity,
    size: AcqRelUsize,
    buckets: BucketArray<Entry<T>>,
}

/// `HashSet`
///
/// Limitation: the maximum number of buckets cannot be specified, due to the
///             lack of const generics.
#[cfg(feature = "with-std")]
pub struct HashSet<T, H: HashHooks = DefaultHashHooks> {
    //  Hooks of the HashSet.
    hooks: H,
    //  Capacity of the first bucket.
    capacity: Capacity,
    //  The number of elements in the set:
    //
    //  -   Should be loaded before reading any element.
    //  -   Should be stored into after writing any element.
    //
    //  The Acquire/Release semantics are used to guarantee that when an element
    //  is read it reflects the last write.
    size: AcqRelUsize,
    buckets: BucketArray<Entry<T>>,
}

impl<T, H: HashHooks + Default> HashSet<T, H> {
    /// Creates a new instance of the `HashSet` with a maximum capacity of 2 for
    /// the first bucket.
    ///
    /// No memory is allocated.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::hashset::HashSet;
    /// let set: HashSet<i32> = HashSet::new();
    ///
    /// assert_eq!(0, set.len());
    /// assert_eq!(0, set.capacity());
    /// assert_eq!(512 * 1024, set.max_capacity());
    /// ```
    pub fn new() -> Self { Self::with_hooks(H::default()) }

    /// Creates a new instace of the `HashSet` with a capacity of at least
    /// `capacity_of_0` for the first bucket.
    ///
    /// If `capacity_of_0` is not a power of 2, it is rounded up.
    /// If `capacity_of_0` is 1, it is rounded up to 2.
    ///
    /// No memory is allocated.
    ///
    /// #   Panics
    ///
    /// Panics if `capacity_of_0` is strictly greater than `usize::MAX / 2 + 1`.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::hashset::HashSet;
    /// let set: HashSet<i32> = HashSet::with_max_capacity(4);
    ///
    /// assert_eq!(0, set.len());
    /// assert_eq!(0, set.capacity());
    /// assert_eq!(1024 * 1024, set.max_capacity());
    /// ```
    pub fn with_max_capacity(capacity_of_0: usize) -> Self {
        Self::with_max_capacity_and_hooks(capacity_of_0, H::default())
    }
}

impl<T, H: HashHooks> HashSet<T, H> {
    /// Creates a new instance of the `HashSet` with a capacity of 2 for
    /// the first bucket.
    ///
    /// No memory is allocated.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::hashset::{HashSet, DefaultHashHooks};
    /// let set: HashSet<i32> = HashSet::with_hooks(DefaultHashHooks::default());
    ///
    /// assert_eq!(0, set.len());
    /// assert_eq!(0, set.capacity());
    /// assert_eq!(512 * 1024, set.max_capacity());
    /// ```
    pub fn with_hooks(hooks: H) -> Self {
        Self::with_max_capacity_and_hooks(2, hooks)
    }

    /// Creates a new instace of the `HashSet` with a capacity of at least
    /// `capacity_of_0` for the first bucket.
    ///
    /// If `capacity_of_0` is not a power of 2, it is rounded up.
    /// If `capacity_of_0` is 1, it is rounded up to 2.
    ///
    /// No memory is allocated.
    ///
    /// #   Panics
    ///
    /// Panics if `capacity_of_0` is strictly greater than `usize::MAX / 2 + 1`.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::hashset::{HashSet, DefaultHashHooks};
    /// let hooks = DefaultHashHooks::default();
    /// let set: HashSet<i32> = HashSet::with_max_capacity_and_hooks(4, hooks);
    ///
    /// assert_eq!(0, set.len());
    /// assert_eq!(0, set.capacity());
    /// assert_eq!(1024 * 1024, set.max_capacity());
    /// ```
    pub fn with_max_capacity_and_hooks(capacity_of_0: usize, hooks: H)
        -> Self
    {
        Self {
            hooks,
            capacity: BucketArray::<Entry<T>>::capacity(capacity_of_0),
            size: AcqRelUsize::new(0),
            buckets: Default::default(),
        }
    }
}

impl<T, H: HashHooks> HashSet<T, H> {
    /// Creates a `HashSetReader`.
    ///
    /// A `HashSetReader` is a read-only view of the `HashSet` instance it is
    /// created from which it reflects updates.
    ///
    /// Reflecting updates comes at the small synchronization cost of having to
    /// read one atomic variable for each access.
    ///
    /// If synchronization is unnecessary, consider using a `HashSetSnapshot`
    /// instead.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::hashset::HashSet;
    /// let set: HashSet<_> = HashSet::new();
    /// let reader = set.reader();
    ///
    /// set.insert(1);
    /// assert_eq!(Some(&1), reader.get(&1));
    /// ```
    pub fn reader(&self) -> HashSetReader<'_, T, H> {
        HashSetReader::new(&self.buckets, &self.hooks, &self.size, self.capacity)
    }

    /// Creates a `HashSetSnapshot`.
    ///
    /// A `HashSetSnapshot` is a read-only view of the `HashSet` instance it is
    /// created from which it does not reflect updates. Once created, it is
    /// immutable.
    ///
    /// A `HashSetSnapshot` can also be created from a `HashSetReader`.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::hashset::HashSet;
    /// let set: HashSet<_> = HashSet::new();
    /// let snapshot = set.snapshot();
    ///
    /// set.insert(1);
    /// assert_eq!(None, snapshot.get(&1));
    /// ```
    pub fn snapshot(&self) -> HashSetSnapshot<'_, T, H> {
        HashSetSnapshot::new(self.shared_reader())
    }

    /// Returns whether the instance contains any element, or not.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::hashset::HashSet;
    /// let set: HashSet<_> = HashSet::new();
    /// assert!(set.is_empty());
    ///
    /// set.insert(1);
    /// assert!(!set.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool { self.shared_reader().is_empty() }

    /// Returns the number of elements contained in the instance.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::hashset::HashSet;
    /// let set: HashSet<_> = HashSet::new();
    /// assert_eq!(0, set.len());
    ///
    /// set.insert(1);
    /// assert_eq!(1, set.len());
    /// ```
    pub fn len(&self) -> usize { self.shared_reader().len() }

    /// Returns the current capacity of the instance.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::hashset::HashSet;
    /// let set: HashSet<_> = HashSet::new();
    /// assert_eq!(0, set.capacity());
    ///
    /// set.extend([1, 2, 3, 4, 5].iter().copied());
    /// assert_eq!(8, set.capacity());
    /// ```
    pub fn capacity(&self) -> usize {
        let number_buckets = self.buckets.number_buckets();
        let capacity = self.capacity.before_bucket(BucketIndex(number_buckets.0)).0;

        //  Load 50%
        capacity / 2
    }

    /// Returns the maximum capacity achievable by the instance.
    ///
    /// The maximum capacity depends:
    ///
    /// -   On the capacity of the first bucket, 1 by default.
    /// -   On the maximum number of buckets, at most 20 in the absence of const
    ///     generics, but possibly less if the capacity of the first bucket is
    ///     really large.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::hashset::HashSet;
    /// let set: HashSet<i32> = HashSet::new();
    /// assert_eq!(512 * 1024, set.max_capacity());
    /// ```
    pub fn max_capacity(&self) -> usize {
        let capacity = self.shared_reader().max_capacity();

        //  Load 50%
        capacity / 2
    }

    /// Returns the number of buckets currently used.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::hashset::HashSet;
    /// let set: HashSet<_> = HashSet::new();
    /// assert_eq!(0, set.number_buckets());
    ///
    /// set.extend([1, 2, 3, 4, 5].iter().copied());
    /// assert_eq!(4, set.number_buckets());
    /// ```
    pub fn number_buckets(&self) -> usize {
        self.shared_reader().number_buckets()
    }

    /// Returns the maximum number of buckets.
    ///
    /// In general, this method should return 20.
    ///
    /// If the capacity of the first bucket is large enough that having 20
    /// buckets would result in `max_capacity` overflowing `usize`, then the
    /// maximum number of buckets will be just as low as necessary to avoid this
    /// fate.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::hashset::HashSet;
    /// let set: HashSet<i32> = HashSet::new();
    /// assert_eq!(20, set.max_buckets());
    ///
    /// let set: HashSet<i32> = HashSet::with_max_capacity(usize::MAX / 8);
    /// assert_eq!(3, set.max_buckets());
    /// ```
    pub fn max_buckets(&self) -> usize { self.shared_reader().max_buckets() }

    /// Returns `true` if the set contains the value.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::hashset::HashSet;
    /// let set: HashSet<_> = HashSet::new();
    /// set.insert(1);
    ///
    /// assert!(set.contains(&1));
    /// assert!(!set.contains(&0));
    /// ```
    pub fn contains<Q>(&self, value: &Q) -> bool
    where
        T: borrow::Borrow<Q>,
        Q: ?Sized + Eq + hash::Hash,
    {
        self.shared_reader().contains_key(value)
    }

    /// Returns a reference to the value, if any.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::hashset::HashSet;
    /// let set: HashSet<_> = HashSet::new();
    /// set.insert(1);
    ///
    /// assert_eq!(Some(&1), set.get(&1));
    /// assert_eq!(None, set.get(&0));
    /// ```
    pub fn get<Q>(&self, value: &Q) -> Option<&T>
    where
        T: borrow::Borrow<Q>,
        Q: ?Sized + Eq + hash::Hash,
    {
        self.shared_reader().get(value).map(|e| &e.0)
    }

    /// Clears the instance.
    ///
    /// The instance is then empty, although it retains previously allocated
    /// memory.
    ///
    /// Use `shrink` to release excess memory.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::hashset::HashSet;
    /// let mut set: HashSet<_> = HashSet::new();
    /// set.extend([1, 2, 3].iter().copied());
    ///
    /// set.clear();
    /// assert_eq!(0, set.len());
    /// assert_eq!(4, set.capacity());
    /// ```
    pub fn clear(&mut self) {
        let size = Size(self.size.load());

        //  Pre-pooping our pants in case a Drop panics.
        self.size.store(0);

        //  Safety:
        //  -   `size` exactly matches the size of the vector.
        //  -   `size` does not increase between creation and use.
        let exclusive = unsafe {
            BucketsExclusiveWriter::new(&mut self.buckets, size, self.capacity)
        };

        exclusive.clear();
    }

    /// Shrinks the instance.
    ///
    /// This method releases excess capacity, retaining just enough to
    /// accomodate the current elements.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::hashset::HashSet;
    /// let set: HashSet<_> = HashSet::new();
    /// set.reserve(16);
    /// assert_eq!(16, set.capacity());
    ///
    /// set.extend([1, 2, 3].iter().copied());
    ///
    /// set.shrink();
    /// assert_eq!(4, set.capacity());
    /// ```
    pub fn shrink(&self) {
        //  Safety:
        //  -   `size` does not increase between creation and use.
        unsafe { self.shared_writer() }.shrink();
    }

    /// Reserves buckets for up to `extra` elements.
    ///
    /// Calling this method reserves enough capacity to be able to insert `extra`
    /// more elements into the instance without allocation failure.
    ///
    /// Calling this method has no effect if there is already sufficient
    /// capacity for `extra` elements.
    ///
    /// More capacity than strictly necessary may be allocated.
    ///
    /// #   Errors
    ///
    /// Returns an error if sufficient space cannot be reserved to accomodate
    /// `extra` elements.
    ///
    /// The behavior is not transactional, so that even in the case an error is
    /// returned, extra capacity may have been reserved.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::failure::Failure;
    /// #   use jagged::hashset::HashSet;
    /// //  BytesOverflow signals that the size of the bucket to allocate, in
    /// //  bytes, overflows `usize`.
    /// let set: HashSet<i32> = HashSet::with_max_capacity(usize::MAX / 2);
    /// assert_eq!(Err(Failure::BytesOverflow), set.try_reserve(1));
    ///
    /// //  ElementsOverflow signals that the total number of elements overflows
    /// //  `usize`.
    /// let set: HashSet<_> = HashSet::new();
    /// set.insert(1);
    /// assert_eq!(Err(Failure::ElementsOverflow), set.try_reserve(usize::MAX));
    ///
    /// //  OutOfBuckets signals that the maximum number of buckets has been
    /// //  reached, and no further bucket can be reserved.
    /// let set: HashSet<i32> = HashSet::new();
    /// assert_eq!(Err(Failure::OutOfBuckets), set.try_reserve(usize::MAX));
    ///
    /// //  OutOfMemory signals that the allocator failed to provide the
    /// //  requested memory; here because the amount requested is too large.
    /// let set: HashSet<i32> = HashSet::with_max_capacity(usize::MAX / 32);
    /// assert_eq!(Err(Failure::OutOfMemory), set.try_reserve(1));
    ///
    /// //  Fortunately, in general, `try_reserve` should succeed.
    /// let set: HashSet<i32> = HashSet::new();
    /// assert_eq!(Ok(()), set.try_reserve(6));
    /// assert_eq!(8, set.capacity());
    /// ```
    pub fn try_reserve(&self, extra: usize) -> Result<()> {
        //  Safety:
        //  -   `size` does not increase between creation and use.
        unsafe { self.shared_writer() }.try_reserve(Size(extra))

        //  Note:   The writes are sequenced with a store to `self.size`, this
        //          is unnecessary here as there will be no read before
        //          `self.size` increases to cover the new buckets.
    }

    /// Reserves buckets for up to `extra` elements.
    ///
    /// Calling this method is equivalent to calling `try_reserve` and panicking
    /// on error.
    ///
    /// #   Panics
    ///
    /// Panics if sufficient space cannot be reserve to accomodate `extra`
    /// elements.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::hashset::HashSet;
    /// let set: HashSet<i32> = HashSet::new();
    /// set.reserve(6);
    /// assert_eq!(8, set.capacity());
    /// ```
    pub fn reserve(&self, extra: usize) {
        self.try_reserve(extra).unwrap_or_else(panic_from_failure);
    }

    /// Inserts a value into the set.
    ///
    /// If the value already exists, returns it.
    ///
    /// #   Errors
    ///
    /// Returns an error if the value cannot be pushed, which may happen either:
    ///
    /// -   If `capacity` is already equal to `max_capacity`.
    /// -   Or if the allocator fails to allocate memory.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::hashset::HashSet;
    /// let set: HashSet<_> = HashSet::new();
    ///
    /// assert_eq!(Ok(None), set.try_insert(3));
    /// assert_eq!(Ok(Some(3)), set.try_insert(3));
    ///
    /// assert_eq!(Some(&3), set.get(&3));
    /// ```
    pub fn try_insert(&self, value: T) -> Result<Option<T>>
    where
        T: Eq + hash::Hash,
    {
        //  Safety:
        //  -   `size` does not increase between creation and use.
        let (size, entry) = unsafe { self.shared_writer() }
            .try_insert(Entry(value))?;

        self.size.store(size.0);

        Ok(entry.map(|e| (e.0)))
    }

    /// Inserts a value into the set.
    ///
    /// Calling this method is equivalent to calling `try_insert` and panicking on
    /// error.
    ///
    /// #   Panics
    ///
    /// Panics if the value cannot be inserted.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::hashset::HashSet;
    /// let set: HashSet<_> = HashSet::new();
    ///
    /// assert_eq!(None, set.insert(3));
    /// assert_eq!(Some(3), set.insert(3));
    ///
    /// assert_eq!(Some(&3), set.get(&3));
    /// ```
    pub fn insert(&self, value: T) -> Option<T>
    where
        T: Eq + hash::Hash,
    {
        match self.try_insert(value) {
            Ok(result) => result,
            Err(error) => {
                panic_from_failure(error);
                //  Safety:
                //  -   As the name of the above function implies...
                unsafe { hint::unreachable_unchecked() }
            },
        }
    }

    /// Inserts multiple values in the set.
    ///
    /// If a value cannot be inserted because it is already present, it is
    /// dropped.
    ///
    /// #   Errors
    ///
    /// Returns an error if any of the values cannot be inserted, which may
    /// happen either:
    ///
    /// -   If `capacity` reaches `max_capacity`.
    /// -   Or if the allocator fails to allocate memory.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::hashset::HashSet;
    /// let set: HashSet<_> = HashSet::new();
    /// assert_eq!(Ok(()), set.try_extend([1, 2, 3].iter().copied()));
    /// assert_eq!(3, set.len());
    /// ```
    pub fn try_extend<C>(&self, collection: C) -> Result<()>
    where
        C: IntoIterator<Item = T>,
        T: Eq + hash::Hash,
    {
        let collection = collection.into_iter();
        let collection = collection.map(|value| Entry(value));

        //  Safety:
        //  -   `size` does not increase between creation and use.
        let (size, failure) = unsafe { self.shared_writer() }
            .try_extend(collection);

        self.size.store(size.0);

        if let Some(failure) = failure {
            Err(failure)
        } else {
            Ok(())
        }
    }

    /// Inserts multiple values in the set.
    ///
    /// If a value cannot be inserted because it is already present, it is
    /// dropped.
    ///
    /// Calling this method is equivalent to calling `try_extend` and panicking
    /// on error.
    ///
    /// #   Panics
    ///
    /// Panics if any of the values cannot be inserted due to an error.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::hashset::HashSet;
    /// let set: HashSet<_> = HashSet::new();
    /// set.extend([1, 2, 3].iter().copied());
    /// assert_eq!(3, set.len());
    /// ```
    pub fn extend<C>(&self, collection: C)
    where
        C: IntoIterator<Item = T>,
        T: Eq + hash::Hash,
    {
        self.try_extend(collection).unwrap_or_else(panic_from_failure);
    }

    //  Returns a SharedReader.
    fn shared_reader(&self) -> BucketsSharedReader<'_, Entry<T>, H> {
        let size = Size(self.size.load());
        //  Safety:
        //  -   `size` is less than the size of the collection.
        unsafe {
            BucketsSharedReader::new(&self.buckets, &self.hooks, size, self.capacity)
        }
    }

    //  Returns a SharedWriter.
    //
    //  #   Safety
    //
    //  -   Assumes that `self.size` will not increase outside of this instance.
    unsafe fn shared_writer(&self) -> BucketsSharedWriter<'_, Entry<T>, H> {
        let size = Size(self.size.load());
        //  Safety:
        //  -   `size` exactly matches the size of the collection.
        //  -   single writer thread.
        BucketsSharedWriter::new(&self.buckets, &self.hooks, size, self.capacity)
    }
}

/// A `HashSet<T>` can be `Send` across threads whenever the standard
/// `HashSet` can.
///
/// #   Example of Send.
///
/// With most types, it is possible to send a `HashSet` across threads.
///
/// ```
/// # use jagged::hashset::HashSet;
/// fn ensure_send<T: Send>(_: T) {}
///
/// let set: HashSet<_> = HashSet::new();
/// set.insert("Hello, World");
///
/// ensure_send(set);
/// ```
///
/// #   Example of not Send.
///
/// A non-Send T prevents the HashSet from being Send.
///
/// ```compile_fail
/// # use std::rc::Rc;
/// # use jagged::hashset::HashSet;
/// fn ensure_send<T: Send>(_: T) {}
///
/// let set: HashSet<_> = HashSet::new();
/// set.insert(Rc::new(3));
///
/// ensure_send(set);
/// ```
///
/// #   Example of not Sync.
///
/// It is never possible to share a reference to `HashSet<T>` across threads.
///
/// ```compile_fail
/// # use std::rc::Rc;
/// # use jagged::hashset::HashSet;
/// fn ensure_sync<T: Sync>(_: T) {}
///
/// let set: HashSet<_> = HashSet::new();
/// set.insert(1);
///
/// ensure_sync(set);
/// ```
unsafe impl<T: Send, H: HashHooks + Send> Send for HashSet<T, H> {}

impl<T, H: HashHooks> Drop for HashSet<T, H> {
    fn drop(&mut self) {
        self.clear();
        self.shrink();
    }
}

impl<T, H: HashHooks + Default> Default for HashSet<T, H> {
    fn default() -> Self { Self::new() }
}

impl<T: fmt::Debug, H: HashHooks> fmt::Debug for HashSet<T, H> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.shared_reader().debug("HashSet", f)
    }
}

impl<T, H> iter::FromIterator<T> for HashSet<T, H>
where
    T: Eq + hash::Hash,
    H: HashHooks + Default,
{
    fn from_iter<C>(collection: C) -> Self
    where
        C: IntoIterator<Item = T>
    {
        let result: HashSet<_, _> = HashSet::with_hooks(H::default());
        result.extend(collection);
        result
    }
}

#[cold]
#[inline(never)]
fn panic_from_failure(failure: Failure) {
    panic!("{}", failure);
}

#[cfg(test)]
mod tests {

use std::mem;

use super::HashSet;

#[test]
fn size_of() {
    const PTR_SIZE: usize = mem::size_of::<usize>();

    assert_eq!(24 * PTR_SIZE, mem::size_of::<HashSet<u8>>());
}

#[test]
fn trait_debug() {
    use std::fmt::Write;

    let set: HashSet<_> = HashSet::new();
    set.extend([1, 2, 3, 4, 5].iter().copied());

    let mut sink = String::new();
    let _ = write!(sink, "{:?}", set);

    assert!(sink.starts_with("HashSet { capacity: 16, length: 5, buckets: [["));
    assert!(sink.ends_with("]] }"));
}

#[test]
fn trait_from_iterator() {
    let set: HashSet<_> = [1, 2, 3, 4, 5].iter().copied().collect();

    assert_eq!(5, set.len());
}

}   //  mod tests
