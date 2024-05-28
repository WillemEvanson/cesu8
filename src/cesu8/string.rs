#![cfg(feature = "alloc")]
use super::Cesu8Str;
use crate::internal::{InternalStr, InternalString};
use crate::{validate_cesu8_internal, EncodingError};

use core::borrow::Borrow;
use core::ops::{Deref, DerefMut};

use alloc::boxed::Box;
use alloc::collections::TryReserveError;
use alloc::vec::Vec;

/// A CESU-8 encoded, growable string.
#[repr(transparent)]
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Cesu8String {
    internal: InternalString,
}

impl Cesu8String {
    /// Creates a new empty `Cesu8String`.
    ///
    /// Given that the `Cesu8String` is empty, this will not allocate any
    /// initial buffer. While that means that this initial operations is very
    /// inexpensive, it may cause excessive allocation later when you add data.
    /// If you have an idea of how much data the `Cesu8String` will hold,
    /// consider the [`with_capacity`] method to prevent excessive
    /// re-allocation.
    ///
    /// [`with_capacity`]: Self::with_capacity
    #[inline]
    #[must_use]
    pub const fn new() -> Cesu8String {
        Cesu8String {
            internal: InternalString::new(),
        }
    }

    /// Creates a new empty `Cesu8String` with at least the specified
    /// capacity.
    ///
    /// `Cesu8String`s have an internal buffer to hold their data. The
    /// capacity is at length of that buffer, and can be queried with the
    /// [`capacity`] method. This method creates an empty `Cesu8String`, but
    /// one with an initial buffer that can hold at least `capacity` bytes. This
    /// is useful when you may be appending a bunch of data to the
    /// `Cesu8String`, reducing the number of reallocations it needs to do.
    ///
    /// [`capacity`]: Self::capacity
    ///
    /// If the given capacity is `0`, no allocation will occur, and this method
    /// is identical to the [`new`] method.
    ///
    /// [`new`]: Self::new
    #[inline]
    #[must_use]
    pub fn with_capacity(capacity: usize) -> Cesu8String {
        Cesu8String {
            internal: InternalString::with_capacity(capacity),
        }
    }

    /// Converts a vector of bytes into a `Cesu8String`.
    ///
    /// A string ([`Cesu8String`]) is made of bytes ([`u8`]), and a vector of
    /// bytes ([`Vec<u8>`]) is made of bytes, so this function converts between
    /// the two. Not all byte slices are valid `Cesu8String`s, however:
    /// `Cesu8String` requires that it is valid CESU-8. `from_cesu8` checks to
    /// ensure that the bytes are valid CESU-8, and then does the conversion.
    ///
    /// If you are sure that the byte slice is valid CESU-8, and you don't want
    /// to incur the overhead of the validity check, there is an unsafe version
    /// of this function, [`from_cesu8_unchecked`], which has the same behavior
    /// but skips the check.
    ///
    /// This method will take care to not to copy the vector, for efficiency's
    /// sake.
    ///
    /// If you need a [`&Cesu8Str`] instead of a `Cesu8String`, consider
    /// [`Cesu8Str::from_cesu8`].
    ///
    /// The inverse of this method is [`into_bytes`].
    ///
    /// [`from_cesu8_unchecked`]: Self::from_cesu8_unchecked
    /// [`&Cesu8Str`]: Cesu8Str
    /// [`into_bytes`]: Self::into_bytes
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if the slice is not CESU-8 with the index and length of
    /// the invalid byte. The vector you moved in is also included.
    #[inline]
    pub fn from_cesu8(vec: Vec<u8>) -> Result<Cesu8String, (EncodingError, Vec<u8>)> {
        match validate_cesu8_internal::<false>(&vec) {
            Ok(()) => unsafe {
                Ok(Cesu8String {
                    internal: InternalString::from_unchecked(vec),
                })
            },
            Err(e) => Err((e, vec)),
        }
    }

    /// Creates a new `Cesu8String` from a length, capacity, and pointer.
    ///
    /// # Safety
    ///
    /// This is highly unsafe, due to the number of invariants that aren't
    /// checked:
    /// * The memory at `buf` needs to have been previously allocationed by the
    ///   same allocator the standard library uess, with a required alignment of
    ///   exactly 1.
    /// * `length` needs to be less than or equal to `capacity`.
    /// * `capacity` needs to be the correct value.
    /// * The first `length` bytes at `buf` need to be valid CESU-8.
    ///
    /// Violating these may cause problems like correcting the allocator's
    /// internal data structures. For example, it is normally **not** safe to
    /// build a `Cesu8String` from a pointer to a C `char` array containing
    /// CESU-8 _unless_ you are certain that array was originally allocated by
    /// the Rust standard library's allocator.
    ///
    /// The ownership of `buf` is effectively transferred to the
    /// `Cesu8String` which may then deallocate, reallocate, or change the
    /// contents of memory pointed to by the pointer at will. Ensure that
    /// nothing elese uses the pointer after calling this function.
    #[inline]
    #[must_use]
    pub unsafe fn from_raw_parts(buf: *mut u8, length: usize, capacity: usize) -> Cesu8String {
        unsafe {
            Cesu8String {
                internal: InternalString::from_raw_parts(buf, length, capacity),
            }
        }
    }

    /// Converts a vector of bytes to a `Cesu8String` without checking that
    /// the string contains valid CESU-8.
    ///
    /// # Safety
    ///
    /// This function is unsafe because it does not check that the bytes passed
    /// to it are valid CESU-8. If this constraint is violated, it may cause
    /// memory unsafety issues with future users of the `Cesu8String`.
    #[inline]
    #[must_use]
    pub unsafe fn from_cesu8_unchecked(bytes: Vec<u8>) -> Cesu8String {
        Cesu8String {
            internal: InternalString::from_unchecked(bytes),
        }
    }

    /// Converts a `Cesu8String` into a byte vector.
    ///
    /// This consumes the `Cesu8String`, so we do not need to copy its contents.
    #[inline]
    #[must_use]
    pub fn into_bytes(self) -> Vec<u8> {
        self.internal.into_bytes()
    }

    /// Extracts a string slice containing the entire `Cesu8String`.
    #[inline]
    #[must_use]
    pub fn as_str(&self) -> &Cesu8Str {
        self
    }

    /// Converts a `Cesu8String` into a mutable string slice.
    #[inline]
    #[must_use]
    pub fn as_mut_str(&mut self) -> &mut Cesu8Str {
        self
    }

    /// Appends a given string slice onto the end of this `Cesu8String`.
    #[inline]
    pub fn push_str(&mut self, str: &Cesu8Str) {
        self.internal.push_str(&str.internal);
    }

    /// Returns this `Cesu8String`'s capacity, in bytes.
    #[inline]
    #[must_use]
    pub fn capacity(&self) -> usize {
        self.internal.capacity()
    }

    /// Reserves capacity for at least `additional` bytes more than the current
    /// length. The allocator may reserve more space to speculatively avoid
    /// frequent allocations. After calling `reserve`, capacity will be greater
    /// than or equal to `self.len() + additional`. Does nothing if the capacity
    /// is already sufficient.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity overflows [`usize`].
    #[inline]
    pub fn reserve(&mut self, additional: usize) {
        self.internal.reserve(additional);
    }

    /// Reserves the minimum capacity for at least `additional` bytes more than
    /// the current length. Unlike [`reserve`], this will not deliberately
    /// over-allocate to speculatively avoid allocations. After calling reserve
    /// `reserve_excat`, capacity will be greater than or equal to `self.len() +
    /// additional`. Does nothing if the capacity is already sufficient.
    ///
    /// [`reserve`]: Self::reserve
    ///
    /// # Panics
    ///
    /// Panics if the new capacity overflows [`usize`].
    #[inline]
    pub fn reserve_exact(&mut self, additional: usize) {
        self.internal.reserve_exact(additional);
    }

    /// Tries to reserve capacity for at least `additional` bytes more than the
    /// current length. The allocator may reserve more space to speculatively
    /// avoid frequent allocations. After calling `try_reserve`, capacity will
    /// be greater than or equal to `self.len() + additional` if it returns
    /// `OK(())`. Does nothing if capacity is already sufficient. This method
    /// preserves the contents even if an error occurs.
    ///
    /// # Errors
    ///
    /// If the capacity overflows, or the allocator reports a failure, then an
    /// error is returned.
    #[inline]
    pub fn try_reserve(&mut self, additional: usize) -> Result<(), TryReserveError> {
        self.internal.try_reserve(additional)
    }

    /// Tries to reserve the minimum capacity for at least `additional` bytes
    /// more than current length. Unlike [`try_reserve`], this will not
    /// deliberately over-allocate to speculatively avoid frequent allocations.
    /// After calling `try_reserve_exact`, capacity will be greater than or
    /// equal `self.len() + additional` if it returns `Ok(())`. Does nothing if
    /// the capacity is already sufficient.
    ///
    /// Not that the allocator may give the collection more space than it
    /// requests. Therefore, capacity can not be relied upon to be precisely
    /// minimal. Prefer [`try_reserve`] if future insertions are expected.
    ///
    /// [`try_reserve`]: Cesu8String::try_reserve
    ///
    /// # Errors
    ///
    /// If the capacity overflows, or the allocator reports a failure, then an
    /// error is returned.
    #[inline]
    pub fn try_reserve_exact(&mut self, additional: usize) -> Result<(), TryReserveError> {
        self.internal.try_reserve_exact(additional)
    }

    /// Shrinks the capacity of this `Cesu8String` to match its length.
    #[inline]
    pub fn shrink_to_fit(&mut self) {
        self.internal.shrink_to_fit();
    }

    /// Shrinks the capacity of this `Cesu8String` with a lower bound.
    ///
    /// The capacity will remaing at least as large as both the length and the
    /// supplied value.
    ///
    /// If the current capacity is less than the lower limit, this is a no-op.
    #[inline]
    pub fn shrink_to(&mut self, min_capacity: usize) {
        self.internal.shrink_to(min_capacity);
    }

    /// Appends the given [`char`] to the end of this `Cesu8String`.
    #[inline]
    pub fn push(&mut self, c: char) {
        self.internal.push::<false>(c);
    }

    /// Returns a byte slice of this `Cesu8String`'s contents.
    #[inline]
    #[must_use]
    pub fn as_bytes(&self) -> &[u8] {
        self.internal.as_bytes()
    }

    /// Shortens this `Cesu8String` to the specified length.
    ///
    /// If `new_len` is greater than the string's current length, this has no
    /// effect.
    ///
    /// Note that this method has no effect on the allocated capacity of the
    /// string.
    ///
    /// # Panics
    ///
    /// Panics if `new_len` does not lie on a [`char`] boundary.
    #[inline]
    pub fn truncate(&mut self, new_len: usize) {
        self.internal.truncate(new_len);
    }

    /// Removes the last character from the string buffer and returns it.
    ///
    /// Returns [`None`] if this `Cesu8String` is empty.
    #[inline]
    #[must_use]
    pub fn pop(&mut self) -> Option<char> {
        self.internal.pop()
    }

    /// Removes a [`char`] from this `Cesu8String` at a byte position and
    /// returns it.
    ///
    /// This is an *O*(*n*) operation, as it requires copy every element in the
    /// buffer.
    ///
    /// # Panics
    ///
    /// Panics if `idx` is large than or equal to the `Cesu8String`'s length, or
    /// if it does not lie on a [`char`] boundary.
    #[inline]
    pub fn remove(&mut self, idx: usize) -> char {
        self.internal.remove(idx)
    }

    /// Inserts a character into this `Cesu8String` at a byte position.
    ///
    /// This is an *O*(*n*) operation as it requires copying every element in
    /// the buffer.
    ///
    /// # Panics
    ///
    /// Panics if `idx` is larger than the `Cesu8String`'s length, or if it does
    /// not lie on a [`char`] boundary.
    #[inline]
    pub fn insert(&mut self, idx: usize, c: char) {
        self.internal.insert::<false>(idx, c);
    }

    /// Returns a mutable reference to the contents of this `Cesu8String`.
    ///     
    /// # Safety
    ///
    /// This function is unsafe because the returned `&mut Vec` allows writing
    /// bytes which are not valid Java CESU-8. If this constraint is violated,
    /// using the original `Cesu8String` after dropping the `&mut Vec` may
    /// violate memory safety, as `Cesu8String`s are expected to always contains
    /// valid Java CESU-8.
    #[inline]
    pub unsafe fn as_mut_vec(&mut self) -> &mut Vec<u8> {
        self.internal.as_mut_vec()
    }

    /// Returns the length of this `Cesu8String`, in bytes, nor [`char`]s or
    /// graphemes. In other words, it might not be what a human considers the
    /// length of the string.
    #[inline]
    #[must_use]
    pub fn len(&self) -> usize {
        self.internal.len()
    }

    /// Returns `true` if this `Cesu8String` has a length of zero, and `false`
    /// otherwise.
    #[inline]
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.internal.is_empty()
    }

    /// Truncates this `Cesu8String`, removing all contents.
    ///
    /// While this means the `Cesu8String` will have a length of zero, it does
    /// not touch its capacity.
    #[inline]
    pub fn clear(&mut self) {
        self.internal.clear();
    }

    /// Converts this `Cesu8String` into a <code>[Box]<[Cesu8Str]</code>.
    ///
    /// This will drop any excess capacity.
    #[inline]
    #[must_use]
    pub fn into_boxed_str(self) -> Box<Cesu8Str> {
        let x = self.internal.into_boxed_str();
        unsafe { Cesu8Str::from_boxed_internal_unchecked(x) }
    }

    /// Consumes and leaks the `Cesu8String`, returning a mutable reference to
    /// the contents, `&'a mut InternalStr`.
    ///
    /// The caller has free choice over the returned lifetime, including
    /// `'static`. Indeed, this function is ideally used for data that lives fro
    /// the remainder of the program's life, as dropping the returned reference
    /// will cause a memory leak.
    ///
    /// It does not reallocate or shrink the `Cesu8String`, so the leaked
    /// allocation may include unused capacity that is not part of the returned
    /// slice. If you don't want that, call [`into_boxed_str`], and then
    /// [`Box::leak`].
    ///
    /// [`into_boxed_str`]: Self::into_boxed_str
    #[inline]
    #[must_use]
    pub fn leak<'a>(self) -> &'a mut Cesu8Str {
        let str = self.internal.leak();
        unsafe { &mut *(str as *mut InternalStr as *mut Cesu8String) }
    }
}

impl Default for Cesu8String {
    fn default() -> Self {
        Self::new()
    }
}

impl Borrow<Cesu8Str> for Cesu8String {
    fn borrow(&self) -> &Cesu8Str {
        self
    }
}

impl Deref for Cesu8String {
    type Target = Cesu8Str;

    #[inline]
    fn deref(&self) -> &Self::Target {
        unsafe { Cesu8Str::from_cesu8_unchecked(self.internal.as_bytes()) }
    }
}

impl DerefMut for Cesu8String {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { Cesu8Str::from_cesu8_unchecked_mut(self.internal.as_bytes_mut()) }
    }
}

impl core::fmt::Debug for Cesu8String {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        core::fmt::Debug::fmt(&self.internal, f)
    }
}

impl core::fmt::Display for Cesu8String {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        core::fmt::Display::fmt(&self.internal, f)
    }
}
