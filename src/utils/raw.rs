//! Raw memory, maybe uninitialized, suitable for concurrent access.

use super::root::{cell, mem, ptr};

//  Raw memory, suitably size for T.
//
//  A building block for the Jagged collection, it can be:
//  -   uninitialized.
//  -   modified concurrently.
//
//  Here be dragons...
pub struct Raw<T>(cell::UnsafeCell<mem::MaybeUninit<T>>);

impl<T> Raw<T> {
    //  Creates a new instance.
    pub fn new() -> Self { Raw(cell::UnsafeCell::new(mem::MaybeUninit::uninit())) }

    //  Gets a reference to the value.
    //
    //  #   Safety
    //
    //  -   Assumes that the value is initialized.
    pub unsafe fn get(&self) -> &T { &*self.as_ptr() }

    //  Gets a reference to the value.
    //
    //  #   Safety
    //
    //  -   Assumes that the value is initialized.
    pub unsafe fn get_mut(&mut self) -> &mut T { &mut *self.as_mut_ptr() }

    //  Gets a pointer to the value.
    //
    //  The value may not be initialized.
    pub fn as_ptr(&self) -> *const T { self.maybe().as_ptr() }

    //  Gets a mutable pointer to the value.
    //
    //  The value may not be initialized.
    pub fn as_mut_ptr(&mut self) -> *mut T { self.maybe_mut().as_mut_ptr() }

    //  Initializes the value.
    //
    //  #   Warning
    //
    //  Does not drop the former value, if any.
    pub fn write(&mut self, value: T) {
        //  Safety:
        //  -   Exclusive access, due to &mut self.
        unsafe { ptr::write(self.as_mut_ptr(), value) };
    }

    //  Drops the value within.
    //
    //  #   Safety
    //
    //  -   Assumes that the value is initialized.
    pub unsafe fn drop(&mut self) {
        ptr::drop_in_place(self.as_mut_ptr());
    }

    //  Gets a reference to the MaybeUninit field.
    fn maybe(&self) -> &mem::MaybeUninit<T> {
        //  Safety:
        //  -   Shared access, per &self.
        unsafe { &*self.0.get() }
    }

    //  Gets a mutable to the MaybeUninit field.
    fn maybe_mut(&mut self) -> &mut mem::MaybeUninit<T> {
        //  Safety:
        //  -   Exclusive access, per &mut self.
        unsafe { &mut *self.0.get() }
    }
}

impl<T> Default for Raw<T> {
    fn default() -> Self { Self::new() }
}
