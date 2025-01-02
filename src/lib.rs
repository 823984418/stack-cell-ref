//! Share a reference in thread inner.
//!
//! # Examples
//! ```
//! use std::cell::Cell;
//!
//! use stack_cell_ref::CellOptionRef;
//!
//! struct Foo {
//!     x: Cell<i32>,
//! }
//!
//! thread_local! {
//!     static S: CellOptionRef<Foo> = CellOptionRef::new();
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
//!     c.with(Some(&foo), || {
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
/// let cell = CellRef::new_with(&0);
/// let foo = 1;
/// cell.with(&foo, || {
///     cell.read(|r| {
///         assert_eq!(*r, 1);
///     });
/// });
/// assert_eq!(unsafe { *cell.get_ptr().as_ref() }, 0);
/// ```
#[repr(transparent)]
pub struct CellRef<T: ?Sized>(Cell<NonNull<T>>);

impl<T: ?Sized> CellRef<T> {
    /// Creates a new [`CellRef`] containing None.
    ///
    /// # Examples
    /// ```
    /// use stack_cell_ref::CellRef;
    ///
    /// let c = CellRef::<i32>::new_with(&0);
    /// ```
    pub const fn new_with(r: &T) -> Self {
        // TODO: use [`NonNull::from_ref`]
        // Safety: the r is non-null.
        unsafe { Self(Cell::new(NonNull::new_unchecked(r as *const T as *mut T))) }
    }

    /// Returns the contained pointer.
    ///
    /// # Examples
    /// ```
    /// use stack_cell_ref::CellRef;
    ///
    /// let c = CellRef::<i32>::new_with(&0);
    /// let ptr_to_zero = c.get_ptr();
    /// ```
    pub fn get_ptr(&self) -> NonNull<T> {
        self.0.get()
    }

    /// Read the cell ref.
    ///
    /// # Examples
    /// ```
    /// use stack_cell_ref::CellRef;
    ///
    /// let cell = CellRef::new_with(&0);
    /// let foo = 1;
    /// cell.with(&foo, || {
    ///     cell.read(|r| {
    ///         assert_eq!(*r, 1);
    ///         // ...
    ///     });
    /// });
    /// ```
    pub fn read<F: FnOnce(&T) -> R, R>(&self, f: F) -> R {
        // Safety: CellRef not Send/Sync
        f(unsafe { self.get_ptr().as_ref() })
    }

    /// Set the cell pointer then run fn.
    ///
    /// # Examples
    /// ```
    /// use std::ptr::NonNull;
    ///
    /// use stack_cell_ref::CellRef;
    ///
    /// let cell = CellRef::new_with(&0);
    /// let foo = 1;
    /// cell.with(&foo, || {
    ///     assert_eq!(cell.get_ptr(), NonNull::from(&foo));
    ///     // ...
    /// });
    /// assert_eq!(unsafe { *cell.get_ptr().as_ref() }, 0);
    /// ```
    pub fn with<F: FnOnce() -> R, R>(&self, r: &T, f: F) -> R {
        struct Guard<'s, T: ?Sized> {
            this: &'s CellRef<T>,
            ptr: NonNull<T>,
        }
        impl<'s, T: ?Sized> Drop for Guard<'s, T> {
            fn drop(&mut self) {
                self.this.0.set(self.ptr);
            }
        }

        let _guard = Guard {
            this: &self,
            ptr: self.0.replace(NonNull::from(r)),
        };
        f()
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

/// A [`Cell`] that stores option immutable references.
///
/// # Examples
/// ```
/// use stack_cell_ref::CellOptionRef;
///
/// let cell = CellOptionRef::new();
/// let foo = 1;
/// cell.with(Some(&foo), || {
///     cell.read(|r| {
///         assert_eq!(*r.unwrap(), 1);
///     });
/// });
/// assert_eq!(cell.get_ptr(), None);
/// ```
#[repr(transparent)]
pub struct CellOptionRef<T: ?Sized>(Cell<Option<NonNull<T>>>);

impl<T: ?Sized> CellOptionRef<T> {
    /// Creates a new [`CellOptionRef`] containing None.
    ///
    /// # Examples
    /// ```
    /// use stack_cell_ref::CellOptionRef;
    ///
    /// let c = CellOptionRef::<i32>::new();
    /// ```
    pub const fn new() -> Self {
        Self(Cell::new(None))
    }

    /// Returns the contained pointer.
    ///
    /// # Examples
    /// ```
    /// use stack_cell_ref::CellOptionRef;
    ///
    /// let c = CellOptionRef::<i32>::new();
    /// let none = c.get_ptr();
    /// ```
    pub fn get_ptr(&self) -> Option<NonNull<T>> {
        self.0.get()
    }

    /// Read the cell ref.
    ///
    /// # Examples
    /// ```
    /// use stack_cell_ref::CellOptionRef;
    ///
    /// let cell = CellOptionRef::new();
    /// let foo = 1;
    /// cell.with(Some(&foo), || {
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
    /// use stack_cell_ref::CellOptionRef;
    ///
    /// let cell = CellOptionRef::new();
    /// let foo = 1;
    /// cell.with(Some(&foo), || {
    ///     assert_eq!(cell.get_ptr(), Some(NonNull::from(&foo)));
    ///     // ...
    /// });
    /// assert_eq!(cell.get_ptr(), None);
    /// ```
    pub fn with<F: FnOnce() -> R, R>(&self, r: Option<&T>, f: F) -> R {
        struct Guard<'s, T: ?Sized> {
            this: &'s CellOptionRef<T>,
            ptr: Option<NonNull<T>>,
        }
        impl<'s, T: ?Sized> Drop for Guard<'s, T> {
            fn drop(&mut self) {
                self.this.0.set(self.ptr);
            }
        }

        let _guard = Guard {
            this: &self,
            ptr: self.0.replace(r.map(NonNull::from)),
        };
        f()
    }
}

impl<T: ?Sized> Default for CellOptionRef<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Debug + ?Sized> Debug for CellOptionRef<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        self.read(|s| Debug::fmt(&s, f))
    }
}

impl<T: PartialEq + ?Sized> PartialEq for CellOptionRef<T> {
    fn eq(&self, other: &Self) -> bool {
        self.read(|s| other.read(|r| PartialEq::eq(&s, &r)))
    }

    fn ne(&self, other: &Self) -> bool {
        self.read(|s| other.read(|r| PartialEq::ne(&s, &r)))
    }
}

impl<T: Eq + ?Sized> Eq for CellOptionRef<T> {}

impl<T: Hash + ?Sized> Hash for CellOptionRef<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.read(|s| Hash::hash(&s, state));
    }
}
