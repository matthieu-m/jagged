//! The Failure and Result types of this library.
//!
//! The collections in this library support faillible allocations. Any method which attempts to allocate memory, or add
//! an element, may fail. The cause of the error is then represented as a `Failure`.
//!
//! All faillible methods come in two versions:
//!
//! -   A faillible `try_xxx` version, which returns a `Result` with `Failure` as the error type.
//! -   A convenience `xxx` version, which invokes the `try_xxx` version and panics in case of error.

use super::root::{error, fmt, result};

/// Universal Failure type of this library.
#[derive(Clone, Copy, Debug, Hash, Eq, PartialEq, Ord, PartialOrd)]
pub enum Failure {
    /// The number of bytes to allocate cannot be calculated due to overflowing.
    BytesOverflow,
    /// The number of elements cannot be calculated due to overflowing.
    ElementsOverflow,
    /// No further Bucket can be allocated.
    OutOfBuckets,
    /// The allocator could not allocate memory.
    OutOfMemory,
}

impl error::Error for Failure {}

impl fmt::Display for Failure {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

/// Universal Result type of this library.
pub type Result<T> = result::Result<T, Failure>;

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn failure_display() {
        assert_eq!("BytesOverflow", format!("{}", Failure::BytesOverflow));
    }
}
