//! Abstraction over Map and Set.

pub trait Key {
    type Key;

    fn key(&self) -> &Self::Key;
}

macro_rules! impl_builtin {
    ($name:ident) => {
        impl Key for $name {
            type Key = Self;
            fn key(&self) -> &Self { self }
        }
    }
}

impl_builtin!(bool);
impl_builtin!(i8);
impl_builtin!(u8);
impl_builtin!(i16);
impl_builtin!(u16);
impl_builtin!(i32);
impl_builtin!(u32);
impl_builtin!(i64);
impl_builtin!(u64);
impl_builtin!(i128);
impl_builtin!(u128);

#[cfg(feature = "with-std")]
impl_builtin!(String);
