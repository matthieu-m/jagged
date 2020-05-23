//! A Snapshot of the HashSet.
//!
//! The Snapshot is synchronization-free, and does not reflect updates to the
//! referred HashSet.

use super::root::{borrow, fmt, hash, iter};

use super::entry::Entry;
use super::hashcore::HashHooks;
use super::hashcore::buckets_api::{BucketsSharedReader, ElementIterator};

/// `HashSetSnapshot`
///
/// A `HashSetSnapshot` is a snapshot of the state of the underlying `HashSet` at
/// the moment the instance is created.
///
/// It never reflects further updates to the `HashSet` instance it was created
/// from.
///
/// #   Iteration order
///
/// All iterators over the elements of a `HashSetSnapshot` are subject to the
/// same limitations:
///
/// -   The order in which elements are iterated on is not the order in which
///     they were inserted.
/// -   The order in which elements are iterated on is stable for one given
///     instance of a `HashSet`.
/// -   The order in which elements are iterated on is only stable across
///     instances and runs of the program if the hash of elements is.
///
/// As an implementation detail, elements are iterated on in clusters
/// corresponding to the underlying buckets. Although unlikely to change, for
/// performance reasons, it is best not to rely on such a property.
pub struct HashSetSnapshot<'a, T, H> {
    reader: BucketsSharedReader<'a, Entry<T>, H>,
}

impl<'a, T, H> HashSetSnapshot<'a, T, H> {
    //  Creates a new instance.
    pub(crate) fn new(reader: BucketsSharedReader<'a, Entry<T>, H>) -> Self {
        Self { reader }
    }

    /// Returns whether the `HashSet` instance contained any element, or not.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::hashset::HashSet;
    /// let set: HashSet<_> = HashSet::new();
    /// let snapshot = set.snapshot();
    /// assert!(snapshot.is_empty());
    ///
    /// set.insert(1);
    ///
    /// //  Insert not reflected in previous instance.
    /// assert!(snapshot.is_empty());
    ///
    /// //  Insert reflected in new instance.
    /// let snapshot = set.snapshot();
    /// assert!(!snapshot.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool { self.reader.is_empty() }

    /// Returns the number of elements contained in the `HashSet` instance.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::hashset::HashSet;
    /// let set: HashSet<_> = HashSet::new();
    /// let snapshot = set.snapshot();
    /// assert_eq!(0, snapshot.len());
    ///
    /// set.insert(1);
    ///
    /// //  Insert not reflected in previous instance.
    /// assert_eq!(0, snapshot.len());
    ///
    /// //  Insert reflected in new instance.
    /// let snapshot = set.snapshot();
    /// assert_eq!(1, snapshot.len());
    /// ```
    pub fn len(&self) -> usize { self.reader.len() }

    /// Returns the maximum capacity achievable by the `HashSet` instance.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::hashset::HashSet;
    /// let set: HashSet<i32> = HashSet::new();
    /// let snapshot = set.snapshot();
    /// assert_eq!(512 * 1024, snapshot.max_capacity());
    /// ```
    pub fn max_capacity(&self) -> usize { self.reader.max_capacity() / 2 }

    /// Returns the number of buckets currently used.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::hashset::HashSet;
    /// let set: HashSet<_> = HashSet::new();
    /// let snapshot = set.snapshot();
    /// assert_eq!(0, snapshot.number_buckets());
    ///
    /// set.extend([1, 2, 3, 4, 5].iter().copied());
    ///
    /// //  Extend not reflected in previous instance.
    /// assert_eq!(0, snapshot.number_buckets());
    ///
    /// //  Extend reflected in new instance.
    /// let snapshot = set.snapshot();
    /// assert_eq!(4, snapshot.number_buckets());
    /// ```
    pub fn number_buckets(&self) -> usize { self.reader.number_buckets() }

    /// Returns the maximum number of buckets.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::hashset::HashSet;
    /// let set: HashSet<i32> = HashSet::new();
    /// let snapshot = set.snapshot();
    /// assert_eq!(20, snapshot.max_buckets());
    /// ```
    pub fn max_buckets(&self) -> usize { self.reader.max_buckets() }

    /// Returns an iterator which yields the values representing the difference
    /// with `other`, i.e., the values that in `self` but not in `other`.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::hashset::HashSet;
    /// let left: HashSet<_> = HashSet::new();
    /// left.extend([1, 2, 3].iter().copied());
    ///
    /// let right: HashSet<_> = HashSet::new();
    /// right.extend([1, 3, 4].iter().copied());
    ///
    /// let difference = left.snapshot().difference(right.snapshot());
    /// let difference: Vec<_> = difference.collect();
    ///
    /// assert_eq!(vec![&2], difference);
    /// ```
    pub fn difference<OH>(&self, other: HashSetSnapshot<'a, T, OH>)
        -> DifferenceIterator<'a, T, OH>
    where
        T: Eq + hash::Hash,
        OH: HashHooks,
    {
        DifferenceIterator::create(self.into_iter(), other)
    }

    /// Returns an iterator which yields the values representing the symmetric
    /// difference with `other`, i.e., the values that are in `self` or in
    /// `other` but not in both.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::hashset::HashSet;
    /// let left: HashSet<_> = HashSet::new();
    /// left.extend([1, 2, 3].iter().copied());
    ///
    /// let right: HashSet<_> = HashSet::new();
    /// right.extend([1, 3, 4].iter().copied());
    ///
    /// let difference = left.snapshot().symmetric_difference(right.snapshot());
    /// let difference: Vec<_> = difference.collect();
    ///
    /// assert_eq!(vec![&2, &4], difference);
    /// ```
    pub fn symmetric_difference<OH>(&self, other: HashSetSnapshot<'a, T, OH>)
        -> SymmetricDifferenceIterator<'a, T, H, OH>
    where
        T: Eq + hash::Hash,
        H: HashHooks,
        OH: HashHooks,
    {
        SymmetricDifferenceIterator::create(*self, other)
    }

    /// Returns an iterator which yields the values representing the intersection
    /// with `other`, i.e., the values that in `self` and in `other`.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::hashset::HashSet;
    /// let left: HashSet<_> = HashSet::new();
    /// left.extend([1, 2, 3].iter().copied());
    ///
    /// let right: HashSet<_> = HashSet::new();
    /// right.extend([1, 3, 4].iter().copied());
    ///
    /// let intersection = left.snapshot().intersection(right.snapshot());
    /// let intersection: Vec<_> = intersection.collect();
    ///
    /// assert_eq!(vec![&1, &3], intersection);
    /// ```
    pub fn intersection<OH>(&self, other: HashSetSnapshot<'a, T, OH>)
        -> IntersectionIterator<'a, T, OH>
    where
        T: Eq + hash::Hash,
        OH: HashHooks,
    {
        IntersectionIterator::create(self.into_iter(), other)
    }

    /// Returns an iterator which yields the values representing the union
    /// with `other`, i.e., the values that in `self` or in `other`, without
    /// duplicates.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::hashset::HashSet;
    /// let left: HashSet<_> = HashSet::new();
    /// left.extend([1, 2, 3].iter().copied());
    ///
    /// let right: HashSet<_> = HashSet::new();
    /// right.extend([1, 3, 4].iter().copied());
    ///
    /// let union = left.snapshot().union(right.snapshot());
    /// let union: Vec<_> = union.collect();
    ///
    /// assert_eq!(vec![&1, &2, &3, &4], union);
    /// ```
    pub fn union<OH>(&self, other: HashSetSnapshot<'a, T, OH>)
        -> UnionIterator<'a, T, H>
    where
        T: Eq + hash::Hash,
        H: HashHooks,
    {
        UnionIterator::create(*self, other.into_iter())
    }
}

impl<'a, T, H: HashHooks> HashSetSnapshot<'a, T, H> {
    /// Returns `true` if the set contains the specified value.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::hashset::HashSet;
    /// let set: HashSet<_> = HashSet::new();
    /// let snapshot = set.snapshot();
    /// assert!(!snapshot.contains(&1));
    ///
    /// set.insert(1);
    ///
    /// //  Insert not reflected in previous instance.
    /// assert!(!snapshot.contains(&1));
    ///
    /// //  Insert reflected in new instance.
    /// let snapshot = set.snapshot();
    /// assert!(snapshot.contains(&1));
    /// assert!(!snapshot.contains(&0));
    /// ```
    pub fn contains<Q>(&self, value: &Q) -> bool
    where
        T: borrow::Borrow<Q>,
        Q: ?Sized + Eq + hash::Hash,
    {
        self.reader.contains_key(value)
    }

    /// Returns a reference to the value, if any.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::hashset::HashSet;
    /// let set: HashSet<_> = HashSet::new();
    /// let snapshot = set.snapshot();
    /// assert_eq!(None, snapshot.get(&1));
    ///
    /// set.insert(1);
    ///
    /// //  Insert not reflected in previous instance.
    /// assert_eq!(None, snapshot.get(&1));
    ///
    /// //  Insert reflected in new instance.
    /// let snapshot = set.snapshot();
    /// assert_eq!(Some(&1), snapshot.get(&1));
    /// assert_eq!(None, snapshot.get(&0));
    /// ```
    pub fn get<Q>(&self, value: &Q) -> Option<&T>
    where
        T: borrow::Borrow<Q>,
        Q: ?Sized + Eq + hash::Hash,
    {
        self.reader.get(value).map(|e| &e.0)
    }

    /// Returns `true` if `self` is disjoint from `other`, i.e., their
    /// intersection is empty.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::hashset::HashSet;
    /// let odds: HashSet<_> = HashSet::new();
    /// odds.extend([1, 3, 5].iter().copied());
    ///
    /// let evens: HashSet<_> = HashSet::new();
    /// evens.extend([2, 4, 6].iter().copied());
    ///
    /// let one: HashSet<_> = HashSet::new();
    /// one.insert(1);
    ///
    /// assert!(odds.snapshot().is_disjoint(evens.snapshot()));
    /// assert!(!one.snapshot().is_disjoint(odds.snapshot()));
    /// ```
    pub fn is_disjoint<OH>(&self, other: HashSetSnapshot<'a, T, OH>) -> bool
    where
        T: Eq + hash::Hash,
        OH: HashHooks,
    {
        if self.len() > other.len() {
            other.is_disjoint(*self)
        } else {
            self.intersection(other).next().is_none()
        }
    }

    /// Returns `true` if `other` contains at least all the elements of `self`.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::hashset::HashSet;
    /// let odds: HashSet<_> = HashSet::new();
    /// odds.extend([1, 3, 5].iter().copied());
    ///
    /// let evens: HashSet<_> = HashSet::new();
    /// evens.extend([2, 4, 6].iter().copied());
    ///
    /// let one: HashSet<_> = HashSet::new();
    /// one.insert(1);
    ///
    /// assert!(!odds.snapshot().is_subset(evens.snapshot()));
    /// assert!(one.snapshot().is_subset(odds.snapshot()));
    /// ```
    pub fn is_subset<OH>(&self, other: HashSetSnapshot<'a, T, OH>) -> bool
    where
        T: Eq + hash::Hash,
        OH: HashHooks,
    {
        if self.len() > other.len() {
            other.is_superset(*self)
        } else {
            self.into_iter().all(|e| other.contains(e))
        }
    }

    /// Returns `true` if `self` contains at least all the elements of `other`.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::hashset::HashSet;
    /// let odds: HashSet<_> = HashSet::new();
    /// odds.extend([1, 3, 5].iter().copied());
    ///
    /// let evens: HashSet<_> = HashSet::new();
    /// evens.extend([2, 4, 6].iter().copied());
    ///
    /// let one: HashSet<_> = HashSet::new();
    /// one.insert(1);
    ///
    /// assert!(!odds.snapshot().is_superset(evens.snapshot()));
    /// assert!(odds.snapshot().is_superset(one.snapshot()));
    /// ```
    pub fn is_superset<OH>(&self, other: HashSetSnapshot<'a, T, OH>) -> bool
    where
        T: Eq + hash::Hash,
        OH: HashHooks,
    {
        if self.len() > other.len() {
            other.is_subset(*self)
        } else {
            other.into_iter().all(|e| self.contains(e))
        }
    }
}

/// A `HashSetSnapshot<T>` can be `Send` across threads whenever a
/// `&[T]` can.
///
/// #   Example of Send.
///
/// With most types, it is possible to send a `HashSetSnapshot` across threads.
///
/// ```
/// # use jagged::hashset::HashSet;
/// fn ensure_send<T: Send>(_: T) {}
///
/// let set: HashSet<_> = HashSet::new();
/// set.insert("Hello, World".to_string());
///
/// ensure_send(set.snapshot());
/// ```
///
/// #   Example of not Send.
///
/// A non-Sync Value prevents the `HashSetSnapshot` from being Send.
///
/// ```compile_fail
/// # use std::rc::Rc;
/// # use jagged::hashset::HashSet;
/// fn ensure_send<T: Send>(_: T) {}
///
/// let set: HashSet<_> = HashSet::new();
/// set.insert(Rc::new(3));
///
/// ensure_send(set.snapshot());
/// ```
/// ```
unsafe impl<'a, T: Sync, H: Sync> Send for HashSetSnapshot<'a, T, H> {}

/// A `HashSetSnapshot<T>` can be shared across threads whenever `&[T]` can.
///
/// #   Example of Sync.
///
/// With most types, it is possible to share a `HashSetSnapshot` across threads.
///
/// ```
/// # use jagged::hashset::HashSet;
/// fn ensure_sync<T: Sync>(_: T) {}
///
/// let set: HashSet<_> = HashSet::new();
/// set.insert("Hello, World".to_string());
///
/// ensure_sync(set.snapshot());
/// ```
///
/// #   Example of not Sync.
///
/// A non-Sync Value prevents the `HashSetSnapshot` from being Send.
///
/// ```compile_fail
/// # use std::rc::Rc;
/// # use jagged::hashset::HashSet;
/// fn ensure_sync<T: Sync>(_: T) {}
///
/// let set: HashSet<_> = HashSet::new();
/// set.insert(Rc::new(3));
///
/// ensure_send(set.snapshot());
/// ```
unsafe impl<'a, T: Sync, H: Sync> Sync for HashSetSnapshot<'a, T, H> {}

impl<'a, T, H> Clone for HashSetSnapshot<'a, T, H> {
    fn clone(&self) -> Self { *self }
}

impl<'a, T, H> Copy for HashSetSnapshot<'a, T, H> {}

impl<'a, T: fmt::Debug, H> fmt::Debug for HashSetSnapshot<'a, T, H> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        self.reader.debug("HashSetSnapshot", f)
    }
}

impl<'a, T, H> Eq for HashSetSnapshot<'a, T, H>
where
    T: Eq + hash::Hash,
    H: hash::BuildHasher,
{}

impl<'a, T, H, OH> PartialEq<HashSetSnapshot<'a, T, OH>> for HashSetSnapshot<'a, T, H>
where
    T: Eq + hash::Hash,
    OH: hash::BuildHasher,
{
    fn eq(&self, other: &HashSetSnapshot<'a, T, OH>) -> bool {
        self.reader.eq(&other.reader)
    }
}

impl<'a, T, H> iter::IntoIterator for HashSetSnapshot<'a, T, H> {
    type Item = &'a T;
    type IntoIter = ValueIterator<'a, T>;

    fn into_iter(self) -> ValueIterator<'a, T> {
        ValueIterator::create(self.reader.into_iter())
    }
}

impl<'a, 'b, T, H> iter::IntoIterator for &'b HashSetSnapshot<'a, T, H> {
    type Item = &'a T;
    type IntoIter = ValueIterator<'a, T>;

    fn into_iter(self) -> ValueIterator<'a, T> {
        ValueIterator::create(self.reader.into_iter())
    }
}

/// An iterator over the values of the HashSet.
pub struct ValueIterator<'a, T>(ElementIterator<'a, Entry<T>>);

impl<'a, T> ValueIterator<'a, T> {
    fn create(iterator: ElementIterator<'a, Entry<T>>) -> Self {
        Self(iterator)
    }
}

impl<'a, T> Clone for ValueIterator<'a, T> {
    fn clone(&self) -> Self { Self(self.0.clone()) }
}

impl<'a, T> iter::Iterator for ValueIterator<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|e| &e.0)
    }
}

/// An iterator returning the elements in the left-hand side set that are not
/// also present in the right-hand side.
pub struct DifferenceIterator<'a, T, H> {
    left: ValueIterator<'a, T>,
    right: HashSetSnapshot<'a, T, H>,
}

impl<'a, T, H> DifferenceIterator<'a, T, H> {
    fn create(
        left: ValueIterator<'a, T>,
        right: HashSetSnapshot<'a, T, H>,
    )
        -> Self
    {
        DifferenceIterator { left, right }
    }
}

impl<'a, T, H> Clone for DifferenceIterator<'a, T, H> {
    fn clone(&self) -> Self {
        DifferenceIterator {
            left: self.left.clone(),
            right: self.right.clone(),
        }
    }
}

impl<'a, T, H> iter::Iterator for DifferenceIterator<'a, T, H>
where
    T: Eq + hash::Hash,
    H: HashHooks,
{
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(e) = self.left.next() {
            if !self.right.contains(e) {
                return Some(e);
            }
        }
        None
    }
}

/// An iterator returing the elements that are either in the left-hand side or
/// the right-hand side, but not in both.
pub struct SymmetricDifferenceIterator<'a, T, H, OH> {
    chain: iter::Chain<DifferenceIterator<'a, T, OH>, DifferenceIterator<'a, T, H>>,
}

impl<'a, T, H, OH> SymmetricDifferenceIterator<'a, T, H, OH>
where
    T: Eq + hash::Hash,
    H: HashHooks,
    OH: HashHooks,
{
    fn create(
        left: HashSetSnapshot<'a, T, H>,
        right: HashSetSnapshot<'a, T, OH>,
    )
        -> Self
    {
        SymmetricDifferenceIterator {
            chain: left.difference(right).chain(right.difference(left))
        }
    }
}

impl<'a, T, H, OH> Clone for SymmetricDifferenceIterator<'a, T, H, OH> {
    fn clone(&self) -> Self {
        SymmetricDifferenceIterator { chain: self.chain.clone() }
    }
}

impl<'a, T, H, OH> iter::Iterator for SymmetricDifferenceIterator<'a, T, H, OH>
where
    T: Eq + hash::Hash,
    H: HashHooks,
    OH: HashHooks,
{
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        self.chain.next()
    }
}

/// An iterator returning the elements in the left-hand side set that are also
/// present in the right-hand side.
pub struct IntersectionIterator<'a, T, H> {
    left: ValueIterator<'a, T>,
    right: HashSetSnapshot<'a, T, H>,
}

impl<'a, T, H> IntersectionIterator<'a, T, H> {
    fn create(
        left: ValueIterator<'a, T>,
        right: HashSetSnapshot<'a, T, H>,
    )
        -> Self
    {
        IntersectionIterator { left, right }
    }
}

impl<'a, T, H> Clone for IntersectionIterator<'a, T, H> {
    fn clone(&self) -> Self {
        IntersectionIterator {
            left: self.left.clone(),
            right: self.right.clone(),
        }
    }
}

impl<'a, T, H> iter::Iterator for IntersectionIterator<'a, T, H>
where
    T: Eq + hash::Hash,
    H: HashHooks,
{
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(e) = self.left.next() {
            if self.right.contains(e) {
                return Some(e);
            }
        }
        None
    }
}

/// An iterator returing the elements that are either in the left-hand side or
/// the right-hand side, without duplicates.
pub struct UnionIterator<'a, T, H> {
    chain: iter::Chain<ValueIterator<'a, T>, DifferenceIterator<'a, T, H>>,
}

impl<'a, T, H> UnionIterator<'a, T, H>
where
    T: Eq + hash::Hash,
    H: HashHooks,
{
    fn create(
        left: HashSetSnapshot<'a, T, H>,
        right: ValueIterator<'a, T>,
    )
        -> Self
    {
        UnionIterator {
            chain: left.into_iter().chain(DifferenceIterator::create(right, left))
        }
    }
}

impl<'a, T, H> Clone for UnionIterator<'a, T, H> {
    fn clone(&self) -> Self {
        UnionIterator { chain: self.chain.clone() }
    }
}

impl<'a, T, H> iter::Iterator for UnionIterator<'a, T, H>
where
    T: Eq + hash::Hash,
    H: HashHooks,
{
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        self.chain.next()
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

    let snapshot = set.snapshot();
    std::mem::drop(snapshot.clone());
}

#[test]
fn trait_copy() {
    let set: HashSet<_> = HashSet::new();
    set.insert("Hello, World".to_string());

    let snapshot = set.snapshot();
    let other = snapshot;
    std::mem::drop(snapshot);
    std::mem::drop(other);
}

#[test]
fn trait_debug() {
    use std::fmt::Write;

    let set: HashSet<_> = HashSet::new();
    set.extend([1, 2, 3, 4, 5].iter().copied());

    let mut sink = String::new();
    let _ = write!(sink, "{:?}", set.snapshot());

    assert!(sink.starts_with("HashSetSnapshot { capacity: 16, length: 5, buckets: [["));
    assert!(sink.ends_with("]] }"));
}

#[test]
fn trait_partial_eq() {
    let left: HashSet<_> = HashSet::new();
    left.insert(1);

    let right: HashSet<_> = HashSet::new();
    right.insert(1);

    assert_eq!(left.snapshot(), right.snapshot());

    left.insert(2);

    assert_ne!(left.snapshot(), right.snapshot());
}

#[test]
fn trait_into_iterator() {
    let set: HashSet<_> = HashSet::new();
    set.insert(1);

    for e in set.snapshot() {
        assert_eq!(&1, e);
    }

    for e in &set.snapshot() {
        assert_eq!(&1, e);
    }
}

}
