//! A Reader of the HashSet.
//!
//! The `HashSetReader` is read-only, and reflects updates to the referred
//! `HashSet`.

use super::root::{borrow, fmt, hash};

use super::HashSetSnapshot;

use super::atomic::AcqRelUsize;
use super::entry::Entry;
use super::hashcore::HashHooks;
use super::hashcore::buckets_api::{BucketArray, BucketsSharedReader};
use super::hashcore::capacity::{Capacity, Size};

/// `HashSetReader`
///
/// A `HashSetReader` is an up-to-date read-only view of the `HashSet` it was
/// created from.
///
/// It always reflects updates to the underlying instance.
pub struct HashSetReader<'a, T, H> {
    buckets: &'a BucketArray<Entry<T>>,
    hooks: &'a H,
    size: &'a AcqRelUsize,
    capacity: Capacity,
}

impl<'a, T, H> HashSetReader<'a, T, H> {
    //  Creates a new instance.
    pub(crate) fn new(
        buckets: &'a BucketArray<Entry<T>>,
        hooks: &'a H,
        size: &'a AcqRelUsize,
        capacity: Capacity,
    )
        -> Self
    {
        Self { buckets, hooks, size, capacity }
    }

    /// Creates a `HashSetSnapshot`.
    ///
    /// A `HashSetSnapshot` is a read-only view of the `HashSetReader` instance it
    /// is created from which it does not reflect updates. Once created, it is
    /// immutable.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::hashset::HashSet;
    /// let set: HashSet<_> = HashSet::new();
    /// let reader = set.reader();
    /// let snapshot = reader.snapshot();
    ///
    /// set.insert(1);
    ///
    /// assert_eq!(Some(&1), reader.get(&1));
    /// assert_eq!(None, snapshot.get(&1));
    /// ```
    pub fn snapshot(&self) -> HashSetSnapshot<'a, T, H> {
        HashSetSnapshot::new(self.shared_reader())
    }

    /// Returns whether the `HashSet` instance contains any element, or not.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::hashset::HashSet;
    /// let set: HashSet<_> = HashSet::new();
    /// let reader = set.reader();
    /// assert!(reader.is_empty());
    ///
    /// set.insert(1);
    /// assert!(!reader.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool { self.shared_reader().is_empty() }

    /// Returns the number of elements contained in the `HashSet` instance.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::hashset::HashSet;
    /// let set: HashSet<_> = HashSet::new();
    /// let reader = set.reader();
    /// assert_eq!(0, reader.len());
    ///
    /// set.insert(1);
    /// assert_eq!(1, reader.len());
    /// ```
    pub fn len(&self) -> usize { self.shared_reader().len() }

    /// Returns the maximum capacity achievable by the `HashSet` instance.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::hashset::HashSet;
    /// let set: HashSet<i32> = HashSet::new();
    /// let reader = set.reader();
    /// assert_eq!(512 * 1024, reader.max_capacity());
    /// ```
    pub fn max_capacity(&self) -> usize { self.shared_reader().max_capacity() / 2 }

    /// Returns the number of buckets currently used by the `HashSet` instance.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::hashset::HashSet;
    /// let set: HashSet<_> = HashSet::new();
    /// let reader = set.reader();
    /// assert_eq!(0, reader.number_buckets());
    ///
    /// set.extend([1, 2, 3, 4, 5].iter().copied());
    /// assert_eq!(4, reader.number_buckets());
    /// ```
    pub fn number_buckets(&self) -> usize {
        self.shared_reader().number_buckets()
    }

    /// Returns the maximum number of buckets.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::hashset::HashSet;
    /// let set: HashSet<i32> = HashSet::new();
    /// let reader = set.reader();
    /// assert_eq!(20, reader.max_buckets());
    /// ```
    pub fn max_buckets(&self) -> usize { self.shared_reader().max_buckets() }

    //  Returns a SharedReader.
    fn shared_reader(&self) -> BucketsSharedReader<'a, Entry<T>, H> {
        let size = Size(self.size.load());
        //  Safety:
        //  -   `size` is less than the size of the hashmap.
        unsafe {
            BucketsSharedReader::new(self.buckets, self.hooks, size, self.capacity)
        }
    }
}

impl<'a, T, H: HashHooks> HashSetReader<'a, T, H> {
    /// Returns `true` if the set contains the specified value.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::hashset::HashSet;
    /// let set: HashSet<_> = HashSet::new();
    /// let reader = set.reader();
    /// assert!(!reader.contains(&1));
    ///
    /// set.insert(1);
    ///
    /// assert!(reader.contains(&1));
    /// assert!(!reader.contains(&0));
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
    /// let reader = set.reader();
    /// assert_eq!(None, reader.get(&1));
    ///
    /// set.insert(1);
    ///
    /// assert_eq!(Some(&1), reader.get(&1));
    /// assert_eq!(None, reader.get(&0));
    /// ```
    pub fn get<Q>(&self, value: &Q) -> Option<&T>
    where
        T: borrow::Borrow<Q>,
        Q: ?Sized + Eq + hash::Hash,
    {
        self.shared_reader().get(value).map(|e| &e.0)
    }
}

/// A `HashSetReader<T>` can be `Send` across threads whenever a
/// `&[T]` can.
///
/// #   Example of Send.
///
/// With most types, it is possible to send a `HashSetReader` across threads.
///
/// ```
/// # use jagged::hashset::HashSet;
/// fn ensure_send<T: Send>(_: T) {}
///
/// let set: HashSet<_> = HashSet::new();
/// set.insert("Hello, World".to_string());
///
/// ensure_send(set.reader());
/// ```
///
/// #   Example of not Send.
///
/// A non-Sync Value prevents the `HashSetReader` from being Send.
///
/// ```compile_fail
/// # use std::rc::Rc;
/// # use jagged::hashset::HashSet;
/// fn ensure_send<T: Send>(_: T) {}
///
/// let set: HashSet<_> = HashSet::new();
/// set.insert(Rc::new(3));
///
/// ensure_send(set.reader());
/// ```
/// ```
unsafe impl<'a, T: Sync, H: Sync> Send for HashSetReader<'a, T, H> {}

/// A `HashSetReader<T>` can be shared across threads whenever `&[T]` can.
///
/// #   Example of Sync.
///
/// With most types, it is possible to share a `HashSetReader` across threads.
///
/// ```
/// # use jagged::hashset::HashSet;
/// fn ensure_sync<T: Sync>(_: T) {}
///
/// let set: HashSet<_> = HashSet::new();
/// set.insert("Hello, World".to_string());
///
/// ensure_sync(set.reader());
/// ```
///
/// #   Example of not Sync.
///
/// A non-Sync Value prevents the `HashSetReader` from being Send.
///
/// ```compile_fail
/// # use std::rc::Rc;
/// # use jagged::hashset::HashSet;
/// fn ensure_sync<T: Sync>(_: T) {}
///
/// let set: HashSet<_> = HashSet::new();
/// set.insert(Rc::new(3));
///
/// ensure_send(set.reader());
/// ```
unsafe impl<'a, T: Sync, H: Sync> Sync for HashSetReader<'a, T, H> {}

impl<'a, T, H> Clone for HashSetReader<'a, T, H> {
    fn clone(&self) -> Self { *self }
}

impl<'a, T, H> Copy for HashSetReader<'a, T, H> {}

impl<'a, T: fmt::Debug, H> fmt::Debug for HashSetReader<'a, T, H> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        self.shared_reader().debug("HashSetReader", f)
    }
}


#[cfg(test)]
mod tests {

use hashset::HashSet;

#[test]
fn trait_clone() {
    #[derive(Eq, Hash, PartialEq)]
    struct NotClonable(u8);

    let set: HashSet<_> = HashSet::new();
    set.insert(NotClonable(0));

    let reader = set.reader();
    std::mem::drop(reader.clone());
}

#[test]
fn trait_copy() {
    let set: HashSet<_> = HashSet::new();
    set.insert("Hello, World".to_string());

    let reader = set.reader();
    let other = reader;
    std::mem::drop(reader);
    std::mem::drop(other);
}

#[test]
fn trait_debug() {
    use std::fmt::Write;

    let set: HashSet<_> = HashSet::new();
    set.extend([1, 2, 3, 4, 5].iter().copied());

    let mut sink = String::new();
    let _ = write!(sink, "{:?}", set.reader());

    assert!(sink.starts_with("HashSetReader { capacity: 16, length: 5, buckets: [["));
    assert!(sink.ends_with("]] }"));
}

}
