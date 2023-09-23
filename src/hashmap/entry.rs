//! Internal Entry for HashMap

use super::root::fmt;

use super::hashcore::key::Key;

//  The actual element stored in HashMap.
pub struct Entry<K, V> {
    //  The key.
    pub key: K,
    //  The value.
    pub value: V,
}

impl<K: fmt::Debug, V: fmt::Debug> fmt::Debug for Entry<K, V> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?} => {:?}", self.key, self.value)
    }
}

impl<K: PartialEq, V: PartialEq> PartialEq for Entry<K, V> {
    fn eq(&self, other: &Self) -> bool {
        self.key.eq(&other.key) && self.value.eq(&other.value)
    }
}

impl<K, V> Key for Entry<K, V> {
    type Key = K;

    fn key(&self) -> &K {
        &self.key
    }
}
