//! A variety of iterators over HashSet.
//!
//! The most obvious iterator is of course the `ValueIterator`.
//!
//! Other iterators are the result of typical set operations such as
//! difference, symmetric_difference, intersection, and union.

pub use super::snapshot::{
    ValueIterator, DifferenceIterator, SymmetricDifferenceIterator,
    IntersectionIterator, UnionIterator,
};
