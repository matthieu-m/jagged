//! Internal Entry for HashSet

use super::root::fmt;

use super::hashcore::key::Key;

//  The actual element stored in HashSet.
pub struct Entry<T>(pub T);

impl<T: fmt::Debug> fmt::Debug for Entry<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self.0)
    }
}

impl<T: PartialEq> PartialEq for Entry<T> {
    fn eq(&self, other: &Self) -> bool {
        self.0.eq(&other.0)
    }
}

impl<T> Key for Entry<T> {
    type Key = T;

    fn key(&self) -> &T { &self.0 }
}
