//! A Snapshot of the HashMap.
//!
//! The Snapshot is synchronization-free, and does not reflect updates to the referred HashMap.

use super::root::{borrow, fmt, hash, iter};

use super::entry::Entry;
use super::hashcore::buckets_api::BucketsSharedReader;
use super::hashcore::HashHooks;
use super::iterator::{KeyIterator, KeyValueIterator, ValueIterator};

/// `HashMapSnapshot`
///
/// A `HashMapSnapshot` is a snapshot of the state of the underlying `HashMap` at the moment the instance is created.
///
/// It never reflects further updates to the `HashMap` instance it was created from.
///
/// #   Iteration order
///
/// All iterators over the elements of a `HashMapSnapshot` are subject to the same limitations:
///
/// -   The order in which elements are iterated on is not the order in which they were inserted.
/// -   The order in which elements are iterated on is stable for one given instance of a `HashMap`.
/// -   The order in which elements are iterated on is only stable across instances and runs of the program if the hash
///     of elements is.
///
/// As an implementation detail, elements are iterated on in clusters corresponding to the underlying buckets. Although
/// unlikely to change, for performance reasons, it is best not to rely on such a property.
pub struct HashMapSnapshot<'a, K, V, H> {
    reader: BucketsSharedReader<'a, Entry<K, V>, H>,
}

impl<'a, K, V, H> HashMapSnapshot<'a, K, V, H> {
    //  Creates a new instance.
    pub(crate) fn new(reader: BucketsSharedReader<'a, Entry<K, V>, H>) -> Self {
        Self { reader }
    }

    /// Returns whether the `HashMap` instance contained any element, or not.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::hashmap::HashMap;
    /// let map: HashMap<_, _> = HashMap::new();
    /// let snapshot = map.snapshot();
    /// assert!(snapshot.is_empty());
    ///
    /// map.insert(1, false);
    ///
    /// //  Insert not reflected in previous instance.
    /// assert!(snapshot.is_empty());
    ///
    /// //  Insert reflected in new instance.
    /// let snapshot = map.snapshot();
    /// assert!(!snapshot.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.reader.is_empty()
    }

    /// Returns the number of elements contained in the `HashMap` instance.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::hashmap::HashMap;
    /// let map: HashMap<_, _> = HashMap::new();
    /// let snapshot = map.snapshot();
    /// assert_eq!(0, snapshot.len());
    ///
    /// map.insert(1, false);
    ///
    /// //  Insert not reflected in previous instance.
    /// assert_eq!(0, snapshot.len());
    ///
    /// //  Insert reflected in new instance.
    /// let snapshot = map.snapshot();
    /// assert_eq!(1, snapshot.len());
    /// ```
    pub fn len(&self) -> usize {
        self.reader.len()
    }

    /// Returns the maximum capacity achievable by the `HashMap` instance.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::hashmap::HashMap;
    /// let map: HashMap<i32, i32> = HashMap::new();
    /// let snapshot = map.snapshot();
    /// assert_eq!(512 * 1024, snapshot.max_capacity());
    /// ```
    pub fn max_capacity(&self) -> usize {
        self.reader.max_capacity()
    }

    /// Returns the number of buckets currently used.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::hashmap::HashMap;
    /// let map: HashMap<_, _> = HashMap::new();
    /// let snapshot = map.snapshot();
    /// assert_eq!(0, snapshot.number_buckets());
    ///
    /// map.extend([(1, 1), (2, 2), (3, 3), (4, 4), (5, 5)].iter().copied());
    ///
    /// //  Extend not reflected in previous instance.
    /// assert_eq!(0, snapshot.number_buckets());
    ///
    /// //  Extend reflected in new instance.
    /// let snapshot = map.snapshot();
    /// assert_eq!(4, snapshot.number_buckets());
    /// ```
    pub fn number_buckets(&self) -> usize {
        self.reader.number_buckets()
    }

    /// Returns the maximum number of buckets.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::hashmap::HashMap;
    /// let map: HashMap<i32, i32> = HashMap::new();
    /// let snapshot = map.snapshot();
    /// assert_eq!(20, snapshot.max_buckets());
    /// ```
    pub fn max_buckets(&self) -> usize {
        self.reader.max_buckets()
    }
}

impl<'a, K, V, H: HashHooks> HashMapSnapshot<'a, K, V, H> {
    /// Returns `true` if the map contains a value for the specified key.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::hashmap::HashMap;
    /// let map: HashMap<_, _> = HashMap::new();
    /// let snapshot = map.snapshot();
    /// assert!(!snapshot.contains_key(&1));
    ///
    /// map.insert(1, false);
    ///
    /// //  Insert not reflected in previous instance.
    /// assert!(!snapshot.contains_key(&1));
    ///
    /// //  Insert reflected in new instance.
    /// let snapshot = map.snapshot();
    /// assert!(snapshot.contains_key(&1));
    /// assert!(!snapshot.contains_key(&0));
    /// ```
    pub fn contains_key<Q>(&self, key: &Q) -> bool
    where
        K: borrow::Borrow<Q>,
        Q: ?Sized + Eq + hash::Hash,
    {
        self.reader.contains_key(key)
    }

    /// Returns a reference to the value corresponding to the key, if any.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::hashmap::HashMap;
    /// let map: HashMap<_, _> = HashMap::new();
    /// let snapshot = map.snapshot();
    /// assert_eq!(None, snapshot.get(&1));
    ///
    /// map.insert(1, false);
    ///
    /// //  Insert not reflected in previous instance.
    /// assert_eq!(None, snapshot.get(&1));
    ///
    /// //  Insert reflected in new instance.
    /// let snapshot = map.snapshot();
    /// assert_eq!(Some(&false), snapshot.get(&1));
    /// assert_eq!(None, snapshot.get(&0));
    /// ```
    pub fn get<Q>(&self, key: &Q) -> Option<&V>
    where
        K: borrow::Borrow<Q>,
        Q: ?Sized + Eq + hash::Hash,
    {
        self.reader.get(key).map(|e| &e.value)
    }

    /// Returns the key-value pair corresponding to the key, if any.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::hashmap::HashMap;
    /// let map: HashMap<_, _> = HashMap::new();
    /// let snapshot = map.snapshot();
    /// assert_eq!(None, snapshot.get_key_value(&1));
    ///
    /// map.insert(1, false);
    ///
    /// //  Insert not reflected in previous instance.
    /// assert_eq!(None, snapshot.get_key_value(&1));
    ///
    /// //  Insert reflected in new instance.
    /// let snapshot = map.snapshot();
    /// assert_eq!(Some((&1, &false)), snapshot.get_key_value(&1));
    /// assert_eq!(None, snapshot.get_key_value(&0));
    /// ```
    pub fn get_key_value<Q>(&self, key: &Q) -> Option<(&K, &V)>
    where
        K: borrow::Borrow<Q>,
        Q: ?Sized + Eq + hash::Hash,
    {
        self.reader.get(key).map(|e| (&e.key, &e.value))
    }

    /// Returns an iterator over the keys of the `HashMap`.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::hashmap::HashMap;
    /// let map: HashMap<_, _> = HashMap::new();
    /// map.extend([(1, false), (2, true), (3, false)].iter().copied());
    ///
    /// let snapshot = map.snapshot();
    /// let keys: Vec<_> = snapshot.keys().collect();
    /// assert_eq!(vec![&1, &2, &3], keys);
    /// ```
    pub fn keys(&self) -> KeyIterator<'a, K, V> {
        KeyIterator::create(self.reader.into_iter())
    }

    /// Returns an iterator over the values of the `HashMap`.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::hashmap::HashMap;
    /// let map: HashMap<_, _> = HashMap::new();
    /// map.extend([(1, false), (2, true), (3, false)].iter().copied());
    ///
    /// let snapshot = map.snapshot();
    /// let values: Vec<_> = snapshot.values().collect();
    /// assert_eq!(vec![&false, &true, &false], values);
    /// ```
    pub fn values(&self) -> ValueIterator<'a, K, V> {
        ValueIterator::create(self.reader.into_iter())
    }
}

/// A `HashMapSnapshot<K, V>` can be `Send` across threads whenever a
/// `&[(K, V)]` can.
///
/// #   Example of Send.
///
/// With most types, it is possible to send a `HashMapSnapshot` across threads.
///
/// ```
/// # use jagged::hashmap::HashMap;
/// fn ensure_send<T: Send>(_: T) {}
///
/// let map: HashMap<_, _> = HashMap::new();
/// map.insert("Hello".to_string(), "World".to_string());
///
/// ensure_send(map.snapshot());
/// ```
///
/// #   Example of Key not being Sync.
///
/// A non-Sync Key prevents the `HashMapSnapshot` from being Send.
///
/// ```compile_fail
/// # use std::rc::Rc;
/// # use jagged::hashmap::HashMap;
/// fn ensure_send<T: Send>(_: T) {}
///
/// let map: HashMap<_, _> = HashMap::new();
/// map.insert(Rc::new(3), i32);
///
/// ensure_send(map.snapshot());
/// ```
///
/// #   Example of Value not being Sync.
///
/// A non-Sync Value prevents the `HashMapSnapshot` from being Send.
///
/// ```compile_fail
/// # use std::rc::Rc;
/// # use jagged::hashmap::HashMap;
/// fn ensure_send<T: Send>(_: T) {}
///
/// let map: HashMap<_, _> = HashMap::new();
/// map.insert(i32, Rc::new(3));
///
/// ensure_send(map.snapshot());
/// ```
unsafe impl<'a, K: Sync, V: Sync, H: Sync> Send for HashMapSnapshot<'a, K, V, H> {}

/// A `HashMapSnapshot<K, V>` can be shared across threads whenever `&[(K, V)]` can.
///
/// #   Example of Sync.
///
/// With most types, it is possible to share a `HashMapSnapshot` across threads.
///
/// ```
/// # use jagged::hashmap::HashMap;
/// fn ensure_sync<T: Sync>(_: T) {}
///
/// let map: HashMap<_, _> = HashMap::new();
/// map.insert("Hello".to_string(), "World".to_string());
///
/// ensure_sync(map.snapshot());
/// ```
///
/// #   Example of Key not being Sync.
///
/// A non-Sync Key prevents the `HashMapSnapshot` from being Send.
///
/// ```compile_fail
/// # use std::rc::Rc;
/// # use jagged::hashmap::HashMap;
/// fn ensure_sync<T: Sync>(_: T) {}
///
/// let map: HashMap<_, _> = HashMap::new();
/// map.insert(Rc::new(3), i32);
///
/// ensure_send(map.snapshot());
/// ```
///
/// #   Example of Value not being Sync.
///
/// A non-Sync Value prevents the `HashMapSnapshot` from being Send.
///
/// ```compile_fail
/// # use std::rc::Rc;
/// # use jagged::hashmap::HashMap;
/// fn ensure_sync<T: Sync>(_: T) {}
///
/// let map: HashMap<_, _> = HashMap::new();
/// map.insert(i32, Rc::new(3));
///
/// ensure_send(map.snapshot());
/// ```
unsafe impl<'a, K: Sync, V: Sync, H: Sync> Sync for HashMapSnapshot<'a, K, V, H> {}

#[cfg(feature = "with-std")]
impl<'a, K, V, H> std::panic::UnwindSafe for HashMapSnapshot<'a, K, V, H> {}

#[cfg(feature = "with-std")]
impl<'a, K, V, H> std::panic::RefUnwindSafe for HashMapSnapshot<'a, K, V, H> {}

impl<'a, K, V, H> Clone for HashMapSnapshot<'a, K, V, H> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<'a, K, V, H> Copy for HashMapSnapshot<'a, K, V, H> {}

impl<'a, K: fmt::Debug, V: fmt::Debug, H> fmt::Debug for HashMapSnapshot<'a, K, V, H> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        self.reader.debug("HashMapSnapshot", f)
    }
}

impl<'a, K, V, H> Eq for HashMapSnapshot<'a, K, V, H>
where
    K: Eq + hash::Hash,
    V: Eq,
    H: hash::BuildHasher,
{
}

impl<'a, K, V, H, OH> PartialEq<HashMapSnapshot<'a, K, V, OH>> for HashMapSnapshot<'a, K, V, H>
where
    K: Eq + hash::Hash,
    V: PartialEq,
    OH: hash::BuildHasher,
{
    fn eq(&self, other: &HashMapSnapshot<'a, K, V, OH>) -> bool {
        self.reader.eq(&other.reader)
    }
}

impl<'a, K, V, H> iter::IntoIterator for HashMapSnapshot<'a, K, V, H> {
    type Item = (&'a K, &'a V);
    type IntoIter = KeyValueIterator<'a, K, V>;

    fn into_iter(self) -> KeyValueIterator<'a, K, V> {
        KeyValueIterator::create(self.reader.into_iter())
    }
}

impl<'a, 'b, K, V, H> iter::IntoIterator for &'b HashMapSnapshot<'a, K, V, H> {
    type Item = (&'a K, &'a V);
    type IntoIter = KeyValueIterator<'a, K, V>;

    fn into_iter(self) -> KeyValueIterator<'a, K, V> {
        KeyValueIterator::create(self.reader.into_iter())
    }
}

#[cfg(test)]
mod tests {

    use crate::hashmap::HashMap;

    #[test]
    fn trait_clone() {
        #![allow(clippy::clone_on_copy)]

        #[derive(Eq, Hash, PartialEq)]
        struct NotClonable(u8);

        {
            let map: HashMap<_, _> = HashMap::new();
            map.insert(NotClonable(0), 2);

            let snapshot = map.snapshot();
            let _ = snapshot.clone();
        }
        {
            let map: HashMap<_, _> = HashMap::new();
            map.insert(2, NotClonable(0));

            let snapshot = map.snapshot();
            let _ = snapshot.clone();
        }
    }

    #[test]
    fn trait_copy() {
        {
            let map: HashMap<_, _> = HashMap::new();
            map.insert("Hello, World".to_string(), 2);

            let snapshot = map.snapshot();
            let other = snapshot;
            let _ = snapshot;
            let _ = other;
        }
        {
            let map: HashMap<_, _> = HashMap::new();
            map.insert(2, "Hello, World".to_string());

            let snapshot = map.snapshot();
            let other = snapshot;
            let _ = snapshot;
            let _ = other;
        }
    }

    #[test]
    fn trait_debug() {
        use std::fmt::Write;

        let map: HashMap<_, _> = HashMap::new();
        map.extend([(1, 1), (2, 2), (3, 3), (4, 4), (5, 5)].iter().copied());

        let mut sink = String::new();
        let _ = write!(sink, "{:?}", map.snapshot());

        println!("{}", sink);

        assert!(sink.starts_with("HashMapSnapshot { capacity: 8, length: 5, buckets: [["));
        assert!(sink.ends_with("]] }"));
    }

    #[test]
    fn trait_partial_eq() {
        let left: HashMap<_, _> = HashMap::new();
        left.insert(1, 2.0);

        let right: HashMap<_, _> = HashMap::new();
        right.insert(1, 2.0);

        assert_eq!(left.snapshot(), right.snapshot());

        left.insert(2, 3.0);

        assert_ne!(left.snapshot(), right.snapshot());
    }

    #[test]
    fn trait_into_iterator() {
        let map: HashMap<_, _> = HashMap::new();
        map.insert(1, false);

        for kv in map.snapshot() {
            assert_eq!((&1, &false), kv);
        }

        for kv in &map.snapshot() {
            assert_eq!((&1, &false), kv);
        }
    }
}
