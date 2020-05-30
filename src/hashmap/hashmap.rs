//! The HashMap

use super::root::{borrow, fmt, hash, hint, iter};

use super::{HashMapReader, HashMapSnapshot};

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

/// `HashMap`
///
/// Limitation: the maximum number of buckets cannot be specified, due to the
///             lack of const generics.
#[cfg(not(feature = "with-std"))]
pub struct HashMap<K, V, H: HashHooks> {
    hooks: H,
    capacity: Capacity,
    size: AcqRelUsize,
    buckets: BucketArray<Entry<K, V>>,
}

/// `HashMap`
///
/// Limitation: the maximum number of buckets cannot be specified, due to the
///             lack of const generics.
#[cfg(feature = "with-std")]
pub struct HashMap<K, V, H: HashHooks = DefaultHashHooks> {
    //  Hooks of the HashMap.
    hooks: H,
    //  Capacity of the first bucket.
    capacity: Capacity,
    //  The number of elements in the map:
    //
    //  -   Should be loaded before reading any element.
    //  -   Should be stored into after writing any element.
    //
    //  The Acquire/Release semantics are used to guarantee that when an element
    //  is read it reflects the last write.
    size: AcqRelUsize,
    buckets: BucketArray<Entry<K, V>>,
}

impl<K, V, H: HashHooks + Default> HashMap<K, V, H> {
    /// Creates a new instance of the `HashMap` with a maximum capacity of 2 for
    /// the first bucket.
    ///
    /// No memory is allocated.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::hashmap::HashMap;
    /// let map: HashMap<i32, i32> = HashMap::new();
    ///
    /// assert_eq!(0, map.len());
    /// assert_eq!(0, map.capacity());
    /// assert_eq!(512 * 1024, map.max_capacity());
    /// ```
    pub fn new() -> Self { Self::with_hooks(H::default()) }

    /// Creates a new instace of the `HashMap` with a capacity of at least
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
    /// #   use jagged::hashmap::HashMap;
    /// let map: HashMap<i32, i32> = HashMap::with_max_capacity(4);
    ///
    /// assert_eq!(0, map.len());
    /// assert_eq!(0, map.capacity());
    /// assert_eq!(1024 * 1024, map.max_capacity());
    /// ```
    pub fn with_max_capacity(capacity_of_0: usize) -> Self {
        Self::with_max_capacity_and_hooks(capacity_of_0, H::default())
    }
}

impl<K, V, H: HashHooks> HashMap<K, V, H> {
    /// Creates a new instance of the `HashMap` with a capacity of 2 for
    /// the first bucket.
    ///
    /// No memory is allocated.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::hashmap::{HashMap, DefaultHashHooks};
    /// let map: HashMap<i32, i32> = HashMap::with_hooks(DefaultHashHooks::default());
    ///
    /// assert_eq!(0, map.len());
    /// assert_eq!(0, map.capacity());
    /// assert_eq!(512 * 1024, map.max_capacity());
    /// ```
    pub fn with_hooks(hooks: H) -> Self {
        Self::with_max_capacity_and_hooks(2, hooks)
    }

    /// Creates a new instace of the `HashMap` with a capacity of at least
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
    /// #   use jagged::hashmap::{HashMap, DefaultHashHooks};
    /// let hooks = DefaultHashHooks::default();
    /// let map: HashMap<i32, i32> = HashMap::with_max_capacity_and_hooks(4, hooks);
    ///
    /// assert_eq!(0, map.len());
    /// assert_eq!(0, map.capacity());
    /// assert_eq!(1024 * 1024, map.max_capacity());
    /// ```
    pub fn with_max_capacity_and_hooks(capacity_of_0: usize, hooks: H)
        -> Self
    {
        Self {
            hooks,
            capacity: BucketArray::<Entry<K, V>>::capacity(capacity_of_0),
            size: AcqRelUsize::new(0),
            buckets: Default::default(),
        }
    }
}

impl<K, V, H: HashHooks> HashMap<K, V, H> {
    /// Creates a `HashMapReader`.
    ///
    /// A `HashMapReader` is a read-only view of the `HashMap` instance it is
    /// created from which it reflects updates.
    ///
    /// Reflecting updates comes at the small synchronization cost of having to
    /// read one atomic variable for each access.
    ///
    /// If synchronization is unnecessary, consider using a `HashMapSnapshot`
    /// instead.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::hashmap::HashMap;
    /// let map: HashMap<_, _> = HashMap::new();
    /// let reader = map.reader();
    ///
    /// map.insert(1, false);
    /// assert_eq!(Some(&false), reader.get(&1));
    /// ```
    pub fn reader(&self) -> HashMapReader<'_, K, V, H> {
        HashMapReader::new(&self.buckets, &self.hooks, &self.size, self.capacity)
    }

    /// Creates a `HashMapSnapshot`.
    ///
    /// A `HashMapSnapshot` is a read-only view of the `HashMap` instance it is
    /// created from which it does not reflect updates. Once created, it is
    /// immutable.
    ///
    /// A `HashMapSnapshot` can also be created from a `HashMapReader`.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::hashmap::HashMap;
    /// let map: HashMap<_, _> = HashMap::new();
    /// let snapshot = map.snapshot();
    ///
    /// map.insert(1, false);
    /// assert_eq!(None, snapshot.get(&1));
    /// ```
    pub fn snapshot(&self) -> HashMapSnapshot<'_, K, V, H> {
        HashMapSnapshot::new(self.shared_reader())
    }

    /// Returns whether the instance contains any element, or not.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::hashmap::HashMap;
    /// let map: HashMap<_, _> = HashMap::new();
    /// assert!(map.is_empty());
    ///
    /// map.insert(1, 1);
    /// assert!(!map.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool { self.shared_reader().is_empty() }

    /// Returns the number of elements contained in the instance.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::hashmap::HashMap;
    /// let map: HashMap<_, _> = HashMap::new();
    /// assert_eq!(0, map.len());
    ///
    /// map.insert(1, 2);
    /// assert_eq!(1, map.len());
    /// ```
    pub fn len(&self) -> usize { self.shared_reader().len() }

    /// Returns the current capacity of the instance.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::hashmap::HashMap;
    /// let map: HashMap<_, _> = HashMap::new();
    /// assert_eq!(0, map.capacity());
    ///
    /// map.extend([(1, 1), (2, 2), (3, 3), (4, 4), (5, 5)].iter().copied());
    /// assert_eq!(8, map.capacity());
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
    /// #   use jagged::hashmap::HashMap;
    /// let map: HashMap<i32, i32> = HashMap::new();
    /// assert_eq!(512 * 1024, map.max_capacity());
    /// ```
    pub fn max_capacity(&self) -> usize { self.shared_reader().max_capacity() }

    /// Returns the number of buckets currently used.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::hashmap::HashMap;
    /// let map: HashMap<_, _> = HashMap::new();
    /// assert_eq!(0, map.number_buckets());
    ///
    /// map.extend([(1, 1), (2, 2), (3, 3), (4, 4), (5, 5)].iter().copied());
    /// assert_eq!(4, map.number_buckets());
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
    /// #   use jagged::hashmap::HashMap;
    /// let map: HashMap<i32, i32> = HashMap::new();
    /// assert_eq!(20, map.max_buckets());
    ///
    /// let map: HashMap<i32, i32> = HashMap::with_max_capacity(usize::MAX / 8);
    /// assert_eq!(3, map.max_buckets());
    /// ```
    pub fn max_buckets(&self) -> usize { self.shared_reader().max_buckets() }

    /// Returns `true` if the map contains a value for the specified key.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::hashmap::HashMap;
    /// let map: HashMap<_, _> = HashMap::new();
    /// map.insert(1, false);
    ///
    /// assert!(map.contains_key(&1));
    /// assert!(!map.contains_key(&0));
    /// ```
    pub fn contains_key<Q>(&self, key: &Q) -> bool
    where
        K: borrow::Borrow<Q>,
        Q: ?Sized + Eq + hash::Hash,
    {
        self.shared_reader().contains_key(key)
    }

    /// Returns a reference to the value corresponding to the key, if any.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::hashmap::HashMap;
    /// let map: HashMap<_, _> = HashMap::new();
    /// map.insert(1, false);
    ///
    /// assert_eq!(Some(&false), map.get(&1));
    /// assert_eq!(None, map.get(&0));
    /// ```
    pub fn get<Q>(&self, key: &Q) -> Option<&V>
    where
        K: borrow::Borrow<Q>,
        Q: ?Sized + Eq + hash::Hash,
    {
        self.shared_reader().get(key).map(|e| &e.value)
    }

    /// Returns the key-value pair corresponding to the key, if any.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::hashmap::HashMap;
    /// let map: HashMap<_, _> = HashMap::new();
    /// map.insert(1, false);
    ///
    /// assert_eq!(Some((&1, &false)), map.get_key_value(&1));
    /// assert_eq!(None, map.get(&0));
    /// ```
    pub fn get_key_value<Q>(&self, key: &Q) -> Option<(&K, &V)>
    where
        K: borrow::Borrow<Q>,
        Q: ?Sized + Eq + hash::Hash,
    {
        self.shared_reader().get(key).map(|e| (&e.key, &e.value))
    }

    /// Returns a reference to the ith element, if any.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::hashmap::HashMap;
    /// let mut map: HashMap<_, _> = HashMap::new();
    /// map.insert(1, false);
    ///
    /// if let Some(e) = map.get_mut(&1) {
    ///     *e = true;
    /// }
    /// assert_eq!(Some(&true), map.get(&1));
    /// ```
    pub fn get_mut<Q>(&mut self, key: &Q) -> Option<&mut V>
    where
        K: borrow::Borrow<Q>,
        Q: ?Sized + Eq + hash::Hash,
    {
        let size = Size(self.size.load());
        //  Safety:
        //  -   `size` is less than the current size of the map.
        //  -   `capacity` matches the capacity of the map.
        let entry = unsafe {
            self.buckets.get_mut(key, size, self.capacity, &self.hooks)
        };

        entry.map(|e| &mut e.value)
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
    /// #   use jagged::hashmap::HashMap;
    /// let mut map: HashMap<_, _> = HashMap::new();
    /// map.extend([(1, false), (2, true), (3, false)].iter().copied());
    ///
    /// map.clear();
    /// assert_eq!(0, map.len());
    /// assert_eq!(4, map.capacity());
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
    /// #   use jagged::hashmap::HashMap;
    /// let map: HashMap<_, _> = HashMap::new();
    /// map.reserve(16);
    /// assert_eq!(16, map.capacity());
    ///
    /// map.extend([(1, false), (2, true), (3, false)].iter().copied());
    ///
    /// map.shrink();
    /// assert_eq!(4, map.capacity());
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
    /// #   use jagged::hashmap::HashMap;
    /// //  BytesOverflow signals that the size of the bucket to allocate, in
    /// //  bytes, overflows `usize`.
    /// let map: HashMap<i32, i32> = HashMap::with_max_capacity(usize::MAX / 2);
    /// assert_eq!(Err(Failure::BytesOverflow), map.try_reserve(1));
    ///
    /// //  ElementsOverflow signals that the total number of elements overflows
    /// //  `usize`.
    /// let map: HashMap<_, _> = HashMap::new();
    /// map.insert(1, false);
    /// assert_eq!(Err(Failure::ElementsOverflow), map.try_reserve(usize::MAX));
    ///
    /// //  OutOfBuckets signals that the maximum number of buckets has been
    /// //  reached, and no further bucket can be reserved.
    /// let map: HashMap<i32, i32> = HashMap::new();
    /// assert_eq!(Err(Failure::OutOfBuckets), map.try_reserve(usize::MAX));
    ///
    /// //  OutOfMemory signals that the allocator failed to provide the
    /// //  requested memory; here because the amount requested is too large.
    /// let map: HashMap<i32, i32> = HashMap::with_max_capacity(usize::MAX / 32);
    /// assert_eq!(Err(Failure::OutOfMemory), map.try_reserve(1));
    ///
    /// //  Fortunately, in general, `try_reserve` should succeed.
    /// let map: HashMap<i32, i32> = HashMap::new();
    /// assert_eq!(Ok(()), map.try_reserve(6));
    /// assert_eq!(8, map.capacity());
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
    /// #   use jagged::hashmap::HashMap;
    /// let map: HashMap<i32, i32> = HashMap::new();
    /// map.reserve(6);
    /// assert_eq!(8, map.capacity());
    /// ```
    pub fn reserve(&self, extra: usize) {
        self.try_reserve(extra).unwrap_or_else(panic_from_failure);
    }

    /// Inserts a key-value pair into the map.
    ///
    /// If the key already exists, returns both key and value.
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
    /// #   use jagged::hashmap::HashMap;
    /// let map: HashMap<_, _> = HashMap::new();
    ///
    /// assert_eq!(Ok(None), map.try_insert(3, false));
    /// assert_eq!(Ok(Some((3, true))), map.try_insert(3, true));
    ///
    /// assert_eq!(Some(&false), map.get(&3));
    /// ```
    pub fn try_insert(&self, key: K, value: V) -> Result<Option<(K, V)>>
    where
        K: Eq + hash::Hash,
    {
        //  Safety:
        //  -   `size` does not increase between creation and use.
        let (size, entry) = unsafe { self.shared_writer() }
            .try_insert(Entry{ key, value })?;

        self.size.store(size.0);

        Ok(entry.map(|e| (e.key, e.value)))
    }

    /// Inserts a key-value pair into the map.
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
    /// #   use jagged::hashmap::HashMap;
    /// let map: HashMap<_, _> = HashMap::new();
    ///
    /// assert_eq!(None, map.insert(3, false));
    /// assert_eq!(Some((3, true)), map.insert(3, true));
    ///
    /// assert_eq!(Some(&false), map.get(&3));
    /// ```
    pub fn insert(&self, key: K, value: V) -> Option<(K, V)>
    where
        K: Eq + hash::Hash,
    {
        match self.try_insert(key, value) {
            Ok(result) => result,
            Err(error) => {
                panic_from_failure(error);
                //  Safety:
                //  -   As the name of the above function implies...
                unsafe { hint::unreachable_unchecked() }
            },
        }
    }

    /// Inserts multiple key-value pairs in the map.
    ///
    /// If a key-value pair cannot be inserted because the key is already
    /// present, it is dropped.
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
    /// #   use jagged::hashmap::HashMap;
    /// let map: HashMap<_, _> = HashMap::new();
    /// assert_eq!(Ok(()), map.try_extend([(1, 1), (2, 2), (3, 3)].iter().copied()));
    /// assert_eq!(3, map.len());
    /// ```
    pub fn try_extend<C>(&self, collection: C) -> Result<()>
    where
        C: IntoIterator<Item = (K, V)>,
        K: Eq + hash::Hash,
    {
        let collection = collection.into_iter();
        let collection = collection.map(|(key, value)| Entry { key, value });

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

    /// Inserts multiple key-value pairs in the map.
    ///
    /// If a key-value pair cannot be inserted because the key is already
    /// present, it is dropped.
    ///
    /// Calling this method is equivalent to calling `try_extend` and panicking
    /// on error.
    ///
    /// #   Panics
    ///
    /// Panics if any of the key-value pairs cannot be inserted due to an error.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::hashmap::HashMap;
    /// let map: HashMap<_, _> = HashMap::new();
    /// map.extend([(1, 1), (2, 2), (3, 3)].iter().copied());
    /// assert_eq!(3, map.len());
    /// ```
    pub fn extend<C>(&self, collection: C)
    where
        C: IntoIterator<Item = (K, V)>,
        K: Eq + hash::Hash,
    {
        self.try_extend(collection).unwrap_or_else(panic_from_failure);
    }

    //  Returns a SharedReader.
    fn shared_reader(&self) -> BucketsSharedReader<'_, Entry<K, V>, H> {
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
    unsafe fn shared_writer(&self) -> BucketsSharedWriter<'_, Entry<K, V>, H> {
        let size = Size(self.size.load());
        //  Safety:
        //  -   `size` exactly matches the size of the collection.
        //  -   single writer thread.
        BucketsSharedWriter::new(&self.buckets, &self.hooks, size, self.capacity)
    }
}

/// A `HashMap<K, V>` can be `Send` across threads whenever the standard
/// `HashMap` can.
///
/// #   Example of Send.
///
/// With most types, it is possible to send a `HashMap` across threads.
///
/// ```
/// # use jagged::hashmap::HashMap;
/// fn ensure_send<T: Send>(_: T) {}
///
/// let map: HashMap<_, _> = HashMap::new();
/// map.insert("Hello", "World");
///
/// ensure_send(map);
/// ```
///
/// #   Example of Key not being Send.
///
/// A non-Send Key prevents the HashMap from being Send.
///
/// ```compile_fail
/// # use std::rc::Rc;
/// # use jagged::hashmap::HashMap;
/// fn ensure_send<T: Send>(_: T) {}
///
/// let map: HashMap<_, _> = HashMap::new();
/// map.insert(Rc::new(3), "World");
///
/// ensure_send(map);
/// ```
///
/// #   Example of Value not being Send.
///
/// A non-Send Value prevents the HashMap from being Send.
///
/// ```compile_fail
/// # use std::rc::Rc;
/// # use jagged::hashmap::HashMap;
/// fn ensure_send<T: Send>(_: T) {}
///
/// let map: HashMap<_, _> = HashMap::new();
/// map.insert("Hello", Rc::new(3));
///
/// ensure_send(map);
/// ```
///
/// #   Example of not Sync.
///
/// It is never possible to share a reference to `HashMap<K, V>` across threads.
///
/// ```compile_fail
/// # use std::rc::Rc;
/// # use jagged::hashmap::HashMap;
/// fn ensure_sync<T: Sync>(_: T) {}
///
/// let map: HashMap<_, _> = HashMap::new();
/// map.insert(1, 2);
///
/// ensure_sync(map);
/// ```
unsafe impl<K: Send, V: Send, H: HashHooks + Send> Send for HashMap<K, V, H> {}

/// A `HashMap<K, V>` is always safe to use across panics.
///
/// #   Example of UnwindSafe.
///
/// ```
/// # use std::panic::UnwindSafe;
/// # use std::rc::Rc;
/// # use jagged::hashmap::HashMap;
/// fn ensure_unwind_safe<T: UnwindSafe>(_: T) {}
///
/// let map: HashMap<_, _> = HashMap::new();
/// map.insert(Rc::new(4), "Go!");
///
/// ensure_unwind_safe(map);
/// ```
#[cfg(feature = "with-std")]
impl<K, V, H: HashHooks> std::panic::UnwindSafe for HashMap<K, V, H> {}

#[cfg(feature = "with-std")]
impl<K, V, H: HashHooks> std::panic::RefUnwindSafe for HashMap<K, V, H> {}

impl<K, V, H: HashHooks> Drop for HashMap<K, V, H> {
    fn drop(&mut self) {
        self.clear();
        self.shrink();
    }
}

impl<K, V, H: HashHooks + Default> Default for HashMap<K, V, H> {
    fn default() -> Self { Self::new() }
}

impl<K: fmt::Debug, V: fmt::Debug, H: HashHooks> fmt::Debug for HashMap<K, V, H> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.shared_reader().debug("HashMap", f)
    }
}

impl<K, V, H> iter::FromIterator<(K, V)> for HashMap<K, V, H>
where
    K: Eq + hash::Hash,
    H: HashHooks + Default,
{
    fn from_iter<C>(collection: C) -> Self
    where
        C: IntoIterator<Item = (K, V)>
    {
        let result: HashMap<_, _, _> = HashMap::with_hooks(H::default());
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

use super::HashMap;

use crate::utils::tester::*;

#[test]
fn size_of() {
    const PTR_SIZE: usize = mem::size_of::<usize>();

    assert_eq!(24 * PTR_SIZE, mem::size_of::<HashMap<u8, u8>>());
}

#[test]
fn trait_debug() {
    use std::fmt::Write;

    let map: HashMap<_, _> = HashMap::new();
    map.extend([(1, 1), (2, 2), (3, 3), (4, 4), (5, 5)].iter().copied());

    let mut sink = String::new();
    let _ = write!(sink, "{:?}", map);

    assert!(sink.starts_with("HashMap { capacity: 16, length: 5, buckets: [["));
    assert!(sink.ends_with("]] }"));
}

#[test]
fn trait_from_iterator() {
    let map: HashMap<_, _> =
        [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5)].iter().copied().collect();

    assert_eq!(5, map.len());
}

#[test]
fn panic_drop() {
    use std::panic::{AssertUnwindSafe, catch_unwind};

    let collection = vec![
        (PanickyDrop::new(0), 0),
        (PanickyDrop::new(1), 1),
        (PanickyDrop::panicky(2), 2),
        (PanickyDrop::new(3), 3),
    ];

    let mut map: HashMap<_, _> = HashMap::default();
    map.extend(collection);

    let panicked = catch_unwind(AssertUnwindSafe(|| {
        map.clear();
    }));
    assert!(panicked.is_err());

    assert_eq!(0, map.len());
}

}   //  mod tests
