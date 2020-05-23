//! Internal hashed element.

use super::atomic::RelaxedUsize;
use super::raw::Raw;

//  The generation of an element.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct Generation(pub usize);

//  The element stored internally.
pub struct Element<T> {
    generation: RelaxedUsize,
    raw: Raw<T>,
}

impl<T> Element<T> {
    //  Creates a new instance, marked as uninitialized.
    pub fn new() -> Self {
        Element { generation: RelaxedUsize::new(UNINTIALIZED), raw: Raw::default() }
    }

    //  Checks whether the element is initialized, or not.
    pub fn is_initialized(&self) -> bool { self.generation.load() != UNINTIALIZED }

    //  Gets the element, if its generation is less than or equal to the specified one.
    //
    //  #   Safety
    //
    //  -   Assumes that `current` is less than the current size of the collection.
    pub unsafe fn get(&self, current: Generation) -> Option<&T> {
        if current.0 >= self.generation.load() {
            //  Safety:
            //  -   Raw is initialized as `self.generation` is not UNINTIALIZED.
            //  -   Raw is finalized as `self.generation` is less than `current`.
            Some(self.raw.get())
        } else {
            None
        }
    }

    //  Gets the element.
    //
    //  #   Safety
    //
    //  -   Assumes the element is initialized.
    pub unsafe fn get_unchecked(&self) -> &T {
        debug_assert!(self.is_initialized());
        //  Safety:
        //  -   Raw is initialized as `self.generation` is not UNINTIALIZED.
        //  -   Raw is finalized.
        self.raw.get()
    }

    //  Stores the element, with its generation.
    //
    //  #   Safety
    //
    //  -   Assumes single writer.
    //  -   Assumes that `current` is exactly the current size of the collection.
    pub unsafe fn set(&self, current: Generation, element: T) {
        debug_assert!(!self.is_initialized());

        //  Safety
        //  -   Single writer.
        //  -   No other thread reads self.raw until self.generation is set.
        let raw: *mut Raw<T> = &self.raw as *const _ as *mut _;
        let raw: &mut Raw<T> = &mut *raw;

        raw.write(element);

        self.generation.store(current.0);
    }

    //  Drops the element, if any.
    pub fn drop(&mut self) {
        if self.is_initialized() {
            //  Safety:
            //  -   The element is initialized.
            unsafe { self.raw.drop() };
            self.generation.store(UNINTIALIZED);
        }
    }
}

impl<T> Default for Element<T> {
    fn default() -> Self { Self::new() }
}

//
//  Implementation Details
//

const UNINTIALIZED : usize = usize::MAX;

#[cfg(test)]
mod tests {

use super::*;

#[test]
fn default() {
    let element: Element<String> = Element::default();

    assert!(!element.is_initialized());
    assert_eq!(None, unsafe { element.get(Generation(UNINTIALIZED - 1)) });
}

#[test]
fn get_set_generation() {
    let element = Element::default();
    let generation = 3;

    unsafe { element.set(Generation(generation), 42) };

    assert_eq!(None, unsafe { element.get(Generation(0)) });
    assert_eq!(None, unsafe { element.get(Generation(generation - 1)) });
    assert_eq!(Some(&42), unsafe { element.get(Generation(generation)) });
    assert_eq!(Some(&42), unsafe { element.get(Generation(generation + 1)) });
}

#[test]
fn drop_initialized() {
    let element = Element::default();
    let generation = Generation(3);

    unsafe { element.set(generation, 42) };

    assert_eq!(Some(&42), unsafe { element.get(generation) });

    let mut element = element;
    element.drop();

    assert!(!element.is_initialized());
    assert_eq!(None, unsafe { element.get(Generation(UNINTIALIZED - 1)) });
}

#[test]
fn drop_uninitialized() {
    let mut element: Element<String> = Element::default();

    element.drop();

    assert!(!element.is_initialized());
    assert_eq!(None, unsafe { element.get(Generation(UNINTIALIZED - 1)) });
}

}
