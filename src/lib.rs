//! Share a reference in thread inner.
//!
//! # Examples
//! ```
//! use std::cell::Cell;
//!
//! use stack_cell_ref::CellRef;
//!
//! struct Foo {
//!     x: Cell<i32>,
//! }
//!
//! thread_local! {
//!     static S: CellRef<Foo> = CellRef::new();
//! }
//!
//! fn set_foo(x: i32) {
//!     S.with(|c| {
//!         c.read(|f| {
//!             f.unwrap().x.set(x);
//!         });
//!     });
//! }
//!
//! let foo = Foo { x: Cell::new(0) };
//!
//! S.with(|c| {
//!     c.with(&foo, || {
//!         set_foo(1);
//!     });
//!     assert_eq!(c.get_ptr(), None);
//! });
//! assert_eq!(foo.x.get(), 1);
//! ```
//!

#![no_std]

use core::cell::Cell;
use core::fmt::{Debug, Formatter};
use core::hash::{Hash, Hasher};
use core::ptr::NonNull;

/// A [`Cell`] that stores immutable references.
///
/// # Examples
/// ```
/// use stack_cell_ref::CellRef;
///
/// let cell = CellRef::new();
/// let foo = 1;
/// cell.with(&foo, || {
///     cell.read(|r| {
///         assert_eq!(*r.unwrap(), 1);
///     });
/// });
/// assert_eq!(cell.get_ptr(), None);
/// ```
#[repr(transparent)]
pub struct CellRef<T: ?Sized>(Cell<Option<NonNull<T>>>);

impl<T: ?Sized> CellRef<T> {
    /// Creates a new CellRef containing None.
    ///
    /// # Examples
    /// ```
    /// use stack_cell_ref::CellRef;
    ///
    /// let c = CellRef::<i32>::new();
    /// ```
    pub const fn new() -> Self {
        Self(Cell::new(None))
    }

    /// Returns the contained pointer.
    ///
    /// # Examples
    /// ```
    /// use stack_cell_ref::CellRef;
    ///
    /// let c = CellRef::<i32>::new();
    /// let none = c.get_ptr();
    /// ```
    pub fn get_ptr(&self) -> Option<NonNull<T>> {
        self.0.get()
    }

    /// Read the cell ref.
    ///
    /// # Examples
    /// ```
    /// use stack_cell_ref::CellRef;
    ///
    /// let cell = CellRef::new();
    /// let foo = 1;
    /// cell.with(&foo, || {
    ///     cell.read(|r| {
    ///         assert_eq!(*r.unwrap(), 1);
    ///         // ...
    ///     });
    /// });
    /// ```
    pub fn read<F: FnOnce(Option<&T>) -> R, R>(&self, f: F) -> R {
        // Safety: CellRef not Send/Sync
        f(unsafe { self.get_ptr().map(|r| r.as_ref()) })
    }

    /// Set the cell pointer then run fn.
    ///
    /// # Examples
    /// ```
    /// use std::ptr::NonNull;
    ///
    /// use stack_cell_ref::CellRef;
    ///
    /// let cell = CellRef::new();
    /// let foo = 1;
    /// cell.with(&foo, || {
    ///     assert_eq!(cell.get_ptr(), Some(NonNull::from(&foo)));
    ///     // ...
    /// });
    /// assert_eq!(cell.get_ptr(), None);
    /// ```
    pub fn with<F: FnOnce() -> R, R>(&self, r: &T, f: F) -> R {
        struct Guard<'s, T: ?Sized>(&'s Cell<Option<NonNull<T>>>, Option<NonNull<T>>);
        impl<'s, T: ?Sized> Drop for Guard<'s, T> {
            fn drop(&mut self) {
                self.0.set(self.1);
            }
        }

        let _guard = Guard(&self.0, self.0.replace(Some(NonNull::from(r))));
        f()
    }
}

impl<T: ?Sized> Default for CellRef<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Debug + ?Sized> Debug for CellRef<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        self.read(|s| Debug::fmt(&s, f))
    }
}

impl<T: PartialEq + ?Sized> PartialEq for CellRef<T> {
    fn eq(&self, other: &Self) -> bool {
        self.read(|s| other.read(|r| PartialEq::eq(&s, &r)))
    }

    fn ne(&self, other: &Self) -> bool {
        self.read(|s| other.read(|r| PartialEq::ne(&s, &r)))
    }
}

impl<T: Eq + ?Sized> Eq for CellRef<T> {}

impl<T: Hash + ?Sized> Hash for CellRef<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.read(|s| Hash::hash(&s, state));
    }
}
