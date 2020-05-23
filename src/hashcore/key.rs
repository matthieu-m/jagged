//! Abstraction over Map and Set.

pub trait Key {
    type Key;

    fn key(&self) -> &Self::Key;
}
