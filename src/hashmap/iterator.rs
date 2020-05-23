//! Various iterators over the HashMap.

use super::root::iter;

use super::entry::Entry;
use super::hashcore::buckets_api::ElementIterator;

/// An iterator over the keys of a `HashMap`.
pub struct KeyIterator<'a, K, V>(ElementIterator<'a, Entry<K, V>>);

impl<'a, K, V> KeyIterator<'a, K, V> {
    pub(crate) fn create(iterator: ElementIterator<'a, Entry<K, V>>) -> Self {
        Self(iterator)
    }
}

impl<'a, K, V> Clone for KeyIterator<'a, K, V> {
    fn clone(&self) -> Self { Self(self.0.clone()) }
}

impl<'a, K, V> iter::Iterator for KeyIterator<'a, K, V> {
    type Item = &'a K;

    fn next(&mut self) -> Option<&'a K> {
        self.0.next().map(|e| &e.key)
    }
}

/// An iterator over the values of a `HashMap`.
pub struct ValueIterator<'a, K, V>(ElementIterator<'a, Entry<K, V>>);

impl<'a, K, V> ValueIterator<'a, K, V> {
    pub(crate) fn create(iterator: ElementIterator<'a, Entry<K, V>>) -> Self {
        Self(iterator)
    }
}

impl<'a, K, V> Clone for ValueIterator<'a, K, V> {
    fn clone(&self) -> Self { Self(self.0.clone()) }
}

impl<'a, K, V> iter::Iterator for ValueIterator<'a, K, V> {
    type Item = &'a V;

    fn next(&mut self) -> Option<&'a V> {
        self.0.next().map(|e| &e.value)
    }
}

/// An iterator over the key-value pairs of a `HashMap`.
pub struct KeyValueIterator<'a, K, V>(ElementIterator<'a, Entry<K, V>>);

impl<'a, K, V> KeyValueIterator<'a, K, V> {
    pub(crate) fn create(iterator: ElementIterator<'a, Entry<K, V>>) -> Self {
        Self(iterator)
    }
}

impl<'a, K, V> Clone for KeyValueIterator<'a, K, V> {
    fn clone(&self) -> Self { Self(self.0.clone()) }
}

impl<'a, K, V> iter::Iterator for KeyValueIterator<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|e| (&e.key, &e.value))
    }
}
