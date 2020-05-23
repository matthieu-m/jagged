//! A Reader of the HashMap.
//!
//! The `HashMapReader` is read-only, and reflects updates to the referred
//! `HashMap`.

use super::root::{borrow, fmt, hash};

use super::HashMapSnapshot;

use super::atomic::AcqRelUsize;
use super::entry::Entry;
use super::hashcore::HashHooks;
use super::hashcore::buckets_api::{BucketArray, BucketsSharedReader};
use super::hashcore::capacity::{Capacity, Size};

/// `HashMapReader`
///
/// A `HashMapReader` is an up-to-date read-only view of the `HashMap` it was
/// created from.
///
/// It always reflects updates to the underlying instance.
pub struct HashMapReader<'a, K, V, H> {
    buckets: &'a BucketArray<Entry<K, V>>,
    hooks: &'a H,
    size: &'a AcqRelUsize,
    capacity: Capacity,
}

impl<'a, K, V, H> HashMapReader<'a, K, V, H> {
    //  Creates a new instance.
    pub(crate) fn new(
        buckets: &'a BucketArray<Entry<K, V>>,
        hooks: &'a H,
        size: &'a AcqRelUsize,
        capacity: Capacity,
    )
        -> Self
    {
        Self { buckets, hooks, size, capacity }
    }

    /// Creates a `HashMapSnapshot`.
    ///
    /// A `HashMapSnapshot` is a read-only view of the `HashMapReader` instance it
    /// is created from which it does not reflect updates. Once created, it is
    /// immutable.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::hashmap::HashMap;
    /// let map: HashMap<_, _> = HashMap::new();
    /// let reader = map.reader();
    /// let snapshot = reader.snapshot();
    ///
    /// map.insert(1, false);
    ///
    /// assert_eq!(Some(&false), reader.get(&1));
    /// assert_eq!(None, snapshot.get(&1));
    /// ```
    pub fn snapshot(&self) -> HashMapSnapshot<'a, K, V, H> {
        HashMapSnapshot::new(self.shared_reader())
    }

    /// Returns whether the `HashMap` instance contains any element, or not.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::hashmap::HashMap;
    /// let map: HashMap<_, _> = HashMap::new();
    /// let reader = map.reader();
    /// assert!(reader.is_empty());
    ///
    /// map.insert(1, 2);
    /// assert!(!reader.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool { self.shared_reader().is_empty() }

    /// Returns the number of elements contained in the `HashMap` instance.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::hashmap::HashMap;
    /// let map: HashMap<_, _> = HashMap::new();
    /// let reader = map.reader();
    /// assert_eq!(0, reader.len());
    ///
    /// map.insert(1, 2);
    /// assert_eq!(1, reader.len());
    /// ```
    pub fn len(&self) -> usize { self.shared_reader().len() }

    /// Returns the maximum capacity achievable by the `HashMap` instance.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::hashmap::HashMap;
    /// let map: HashMap<i32, i32> = HashMap::new();
    /// let reader = map.reader();
    /// assert_eq!(512 * 1024, reader.max_capacity());
    /// ```
    pub fn max_capacity(&self) -> usize { self.shared_reader().max_capacity() / 2 }

    /// Returns the number of buckets currently used by the `HashMap` instance.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::hashmap::HashMap;
    /// let map: HashMap<_, _> = HashMap::new();
    /// let reader = map.reader();
    /// assert_eq!(0, reader.number_buckets());
    ///
    /// map.extend([(1, 1), (2, 2), (3, 3), (4, 4), (5, 5)].iter().copied());
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
    /// #   use jagged::hashmap::HashMap;
    /// let map: HashMap<i32, i32> = HashMap::new();
    /// let reader = map.reader();
    /// assert_eq!(20, reader.max_buckets());
    /// ```
    pub fn max_buckets(&self) -> usize { self.shared_reader().max_buckets() }

    //  Returns a SharedReader.
    fn shared_reader(&self) -> BucketsSharedReader<'a, Entry<K, V>, H> {
        let size = Size(self.size.load());
        //  Safety:
        //  -   `size` is less than the size of the hashmap.
        unsafe {
            BucketsSharedReader::new(self.buckets, self.hooks, size, self.capacity)
        }
    }
}

impl<'a, K, V, H: HashHooks> HashMapReader<'a, K, V, H> {
    /// Returns `true` if the map contains a value for the specified key.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::hashmap::HashMap;
    /// let map: HashMap<_, _> = HashMap::new();
    /// let reader = map.reader();
    /// assert!(!reader.contains_key(&1));
    ///
    /// map.insert(1, false);
    ///
    /// assert!(reader.contains_key(&1));
    /// assert!(!reader.contains_key(&0));
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
    /// let reader = map.reader();
    /// assert_eq!(None, reader.get(&1));
    ///
    /// map.insert(1, false);
    ///
    /// assert_eq!(Some(&false), reader.get(&1));
    /// assert_eq!(None, reader.get(&0));
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
    /// let reader = map.reader();
    /// assert_eq!(None, reader.get_key_value(&1));
    ///
    /// map.insert(1, false);
    ///
    /// assert_eq!(Some((&1, &false)), reader.get_key_value(&1));
    /// assert_eq!(None, reader.get_key_value(&0));
    /// ```
    pub fn get_key_value<Q>(&self, key: &Q) -> Option<(&K, &V)>
    where
        K: borrow::Borrow<Q>,
        Q: ?Sized + Eq + hash::Hash,
    {
        self.shared_reader().get(key).map(|e| (&e.key, &e.value))
    }
}

/// A `HashMapReader<K, V>` can be `Send` across threads whenever a `&[(K, V)]` can.
///
/// #   Example of Send.
///
/// With most types, it is possible to send a `HashMapReader` across threads.
///
/// ```
/// # use jagged::hashmap::HashMap;
/// fn ensure_send<T: Send>(_: T) {}
///
/// let map: HashMap<_, _> = HashMap::new();
/// map.insert("Hello".to_string(), "World".to_string());
///
/// ensure_send(map.reader());
/// ```
///
/// #   Example of Key not being Sync.
///
/// A non-Sync Key prevents the `HashMapReader` from being Send.
///
/// ```compile_fail
/// # use std::rc::Rc;
/// # use jagged::hashmap::HashMap;
/// fn ensure_send<T: Send>(_: T) {}
///
/// let map: HashMap<_, _> = HashMap::new();
/// map.insert(Rc::new(3), i32);
///
/// ensure_send(map.reader());
/// ```
///
/// #   Example of Value not being Sync.
///
/// A non-Sync Value prevents the `HashMapReader` from being Send.
///
/// ```compile_fail
/// # use std::rc::Rc;
/// # use jagged::hashmap::HashMap;
/// fn ensure_send<T: Send>(_: T) {}
///
/// let map: HashMap<_, _> = HashMap::new();
/// map.insert(i32, Rc::new(3));
///
/// ensure_send(map.reader());
/// ```
unsafe impl<'a, K: Sync, V: Sync, H: Sync> Send for HashMapReader<'a, K, V, H> {}

/// A `HashMapReader<K, V>` can be shared across threads whenver `&[(K, V)]` can.
///
/// #   Example of Sync.
///
/// With most types, it is possible to share a `HashMapReader` across threads.
///
/// ```
/// # use jagged::hashmap::HashMap;
/// fn ensure_sync<T: Sync>(_: T) {}
///
/// let map: HashMap<_, _> = HashMap::new();
/// map.insert("Hello".to_string(), "World".to_string());
///
/// ensure_sync(map.reader());
/// ```
///
/// #   Example of Key not being Sync.
///
/// A non-Sync Key prevents the `HashMapReader` from being Send.
///
/// ```compile_fail
/// # use std::rc::Rc;
/// # use jagged::hashmap::HashMap;
/// fn ensure_sync<T: Sync>(_: T) {}
///
/// let map: HashMap<_, _> = HashMap::new();
/// map.insert(Rc::new(3), i32);
///
/// ensure_send(map.reader());
/// ```
///
/// #   Example of Value not being Sync.
///
/// A non-Sync Value prevents the `HashMapReader` from being Send.
///
/// ```compile_fail
/// # use std::rc::Rc;
/// # use jagged::hashmap::HashMap;
/// fn ensure_sync<T: Sync>(_: T) {}
///
/// let map: HashMap<_, _> = HashMap::new();
/// map.insert(i32, Rc::new(3));
///
/// ensure_send(map.reader());
/// ```
unsafe impl<'a, K: Sync, V: Sync, H: Sync> Sync for HashMapReader<'a, K, V, H> {}

impl<'a, K, V, H> Clone for HashMapReader<'a, K, V, H> {
    fn clone(&self) -> Self { *self }
}

impl<'a, K, V, H> Copy for HashMapReader<'a, K, V, H> {}

impl<'a, K: fmt::Debug, V: fmt::Debug, H> fmt::Debug for HashMapReader<'a, K, V, H> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        self.shared_reader().debug("HashMapReader", f)
    }
}


#[cfg(test)]
mod tests {

use hashmap::HashMap;

#[test]
fn trait_clone() {
    #[derive(Eq, Hash, PartialEq)]
    struct NotClonable(u8);

    {
        let map: HashMap<_, _> = HashMap::new();
        map.insert(NotClonable(0), 2);

        let reader = map.reader();
        std::mem::drop(reader.clone());
    }
    {
        let map: HashMap<_, _> = HashMap::new();
        map.insert(2, NotClonable(0));

        let reader = map.reader();
        std::mem::drop(reader.clone());
    }
}

#[test]
fn trait_copy() {
    {
        let map: HashMap<_, _> = HashMap::new();
        map.insert("Hello, World".to_string(), 2);

        let reader = map.reader();
        let other = reader;
        std::mem::drop(reader);
        std::mem::drop(other);
    }
    {
        let map: HashMap<_, _> = HashMap::new();
        map.insert(2, "Hello, World".to_string());

        let reader = map.reader();
        let other = reader;
        std::mem::drop(reader);
        std::mem::drop(other);
    }
}

#[test]
fn trait_debug() {
    use std::fmt::Write;

    let map: HashMap<_, _> = HashMap::new();
    map.extend([(1, 1), (2, 2), (3, 3), (4, 4), (5, 5)].iter().copied());

    let mut sink = String::new();
    let _ = write!(sink, "{:?}", map.reader());

    assert!(sink.starts_with("HashMapReader { capacity: 16, length: 5, buckets: [["));
    assert!(sink.ends_with("]] }"));
}

}
