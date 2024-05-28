#![cfg(feature = "alloc")]
use crate::encode_cesu8_raw;
use crate::internal::InternalStr;

use core::borrow::Borrow;
use core::ops::{Deref, DerefMut};

use alloc::boxed::Box;
use alloc::collections::TryReserveError;
use alloc::vec::Vec;

/// A CESU-8 encoded, growable string.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct InternalString {
    vec: Vec<u8>,
}

impl InternalString {
    /// Creates a new empty `InternalString`.
    ///
    /// Given that the `InternalString` is empty, this will not allocate any
    /// initial buffer. While that means that this initial operations is very
    /// inexpensive, it may cause excessive allocation later when you add data.
    /// If you have an idea of how much data the `InternalString` will hold,
    /// consider the [`with_capacity`] method to prevent excessive
    /// re-allocation.
    ///
    /// [`with_capacity`]: Self::with_capacity
    #[inline]
    #[must_use]
    pub(crate) const fn new() -> Self {
        Self { vec: Vec::new() }
    }

    /// Creates a new empty `InternalString` with at least the specified
    /// capacity.
    ///
    /// `InternalString`s have an internal buffer to hold their data. The
    /// capacity is at length of that buffer, and can be queried with the
    /// [`capacity`] method. This method creates an empty `InternalString`, but
    /// one with an initial buffer that can hold at least `capacity` bytes. This
    /// is useful when you may be appending a bunch of data to the
    /// `InternalString`, reducing the number of reallocations it needs to do.
    ///
    /// [`capacity`]: Self::capacity
    ///
    /// If the given capacity is `0`, no allocation will occur, and this method
    /// is identical to the [`new`] method.
    ///
    /// [`new`]: Self::new
    #[inline]
    #[must_use]
    pub(crate) fn with_capacity(capacity: usize) -> Self {
        Self {
            vec: Vec::with_capacity(capacity),
        }
    }

    /// Creates a new `InternalString` from a length, capacity, and pointer.
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
    /// build a `InternalString` from a pointer to a C `char` array containing
    /// CESU-8 _unless_ you are certain that array was originally allocated by
    /// the Rust standard library's allocator.
    ///
    /// The ownership of `buf` is effectively transferred to the
    /// `InternalString` which may then deallocate, reallocate, or change the
    /// contents of memory pointed to by the pointer at will. Ensure that
    /// nothing elese uses the pointer after calling this function.
    #[inline]
    #[must_use]
    pub(crate) unsafe fn from_raw_parts(buf: *mut u8, length: usize, capacity: usize) -> Self {
        unsafe {
            Self {
                vec: Vec::from_raw_parts(buf, length, capacity),
            }
        }
    }

    /// Converts a vector of bytes to an `InternalString` without checking that
    /// the string contains valid CESU-8.
    ///
    /// # Safety
    ///
    /// This function is unsafe because it does not check that the bytes passed
    /// to it are valid CESU-8. If this constraint is violated, it may cause
    /// memory unsafety issues with future users of the `InternalString`.
    #[inline]
    #[must_use]
    pub(crate) const unsafe fn from_unchecked(bytes: Vec<u8>) -> Self {
        Self { vec: bytes }
    }

    /// Converts an `InternalString` into a byte vector.
    ///
    /// This consumes the `InternalString`, so we do not need to copy its
    /// contents.
    #[inline]
    #[must_use]
    pub fn into_bytes(self) -> Vec<u8> {
        self.vec
    }

    /// Extracts a string slice containing the entire `InternalString`.
    #[inline]
    #[must_use]
    pub fn as_str(&self) -> &InternalStr {
        self
    }

    /// Appends a given string slice onto the end of this `InternalString`.
    #[inline]
    pub(crate) fn push_str(&mut self, str: &InternalStr) {
        self.vec.extend_from_slice(str.as_bytes());
    }

    /// Returns this `InternalString`'s capacity, in bytes.
    #[inline]
    #[must_use]
    pub(crate) fn capacity(&self) -> usize {
        self.vec.capacity()
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
    pub(crate) fn reserve(&mut self, additional: usize) {
        self.vec.reserve(additional);
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
    pub(crate) fn reserve_exact(&mut self, additional: usize) {
        self.vec.reserve_exact(additional);
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
    pub(crate) fn try_reserve(&mut self, additional: usize) -> Result<(), TryReserveError> {
        self.vec.try_reserve(additional)
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
    /// [`try_reserve`]: InternalString::try_reserve
    ///
    /// # Errors
    ///
    /// If the capacity overflows, or the allocator reports a failure, then an
    /// error is returned.
    #[inline]
    pub(crate) fn try_reserve_exact(&mut self, additional: usize) -> Result<(), TryReserveError> {
        self.vec.try_reserve_exact(additional)
    }

    /// Shrinks the capacity of this `InternalString` to match its length.
    #[inline]
    pub(crate) fn shrink_to_fit(&mut self) {
        self.vec.shrink_to_fit();
    }

    /// Shrinks the capacity of this `InternalString` with a lower bound.
    ///
    /// The capacity will remaing at least as large as both the length and the
    /// supplied value.
    ///
    /// If the current capacity is less than the lower limit, this is a no-op.
    #[inline]
    pub(crate) fn shrink_to(&mut self, min_capacity: usize) {
        self.vec.shrink_to(min_capacity);
    }

    /// Appends the given [`char`] to the end of this `InternalString`.
    #[inline]
    pub(crate) fn push<const JAVA: bool>(&mut self, c: char) {
        self.vec
            .extend_from_slice(encode_cesu8_raw::<JAVA>(c as u32, &mut [0; 4]));
    }

    /// Returns a byte slice of this `InternalString`'s contents.
    #[inline]
    #[must_use]
    pub(crate) fn as_bytes(&self) -> &[u8] {
        &self.vec
    }

    /// Shortens this `InternalString` to the specified length.
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
    pub(crate) fn truncate(&mut self, new_len: usize) {
        if new_len <= self.len() {
            assert!(self.is_char_boundary(new_len));
            self.vec.truncate(new_len);
        }
    }

    /// Removes the last character from the string buffer and returns it.
    ///
    /// Returns [`None`] if this `InternalString` is empty.
    #[inline]
    #[must_use]
    pub(crate) fn pop(&mut self) -> Option<char> {
        let (new_len, c) = self.char_indices().next_back()?;
        unsafe { self.vec.set_len(new_len) };
        Some(c)
    }

    /// Removes a [`char`] from this `InternalString` at a byte position and
    /// returns it.
    ///
    /// This is an *O*(*n*) operation, as it requires copy every element in the
    /// buffer.
    ///
    /// # Panics
    ///
    /// Panics if `idx` is large than or equal to the `InternalString`'s length,
    /// or if it does not lie on a [`char`] boundary.
    #[inline]
    pub(crate) fn remove(&mut self, idx: usize) -> char {
        let mut iter = self[idx..].chars();
        let initial_len = iter.as_bytes().len();
        let c = match iter.next() {
            Some(c) => c,
            None => panic!("cannot remove a char from the end of a string"),
        };
        let remaining_len = iter.as_bytes().len();
        let len = self.len();

        unsafe {
            core::ptr::copy(
                self.vec.as_ptr().add(len - remaining_len),
                self.vec.as_mut_ptr().add(len - initial_len),
                remaining_len,
            );
            self.vec.set_len(len - (initial_len - remaining_len));
        }
        c
    }

    /// Inserts a character into this `InternalString` at a byte position.
    ///
    /// This is an *O*(*n*) operation as it requires copying every element in
    /// the buffer.
    ///
    /// # Panics
    ///
    /// Panics if `idx` is larger than the `InternalString`'s length, or if it
    /// does not lie on a [`char`] boundary.
    #[inline]
    pub(crate) fn insert<const JAVA: bool>(&mut self, idx: usize, c: char) {
        assert!(self.is_char_boundary(idx));
        let mut bits = [0; 6];
        let bits = encode_cesu8_raw::<JAVA>(c as u32, &mut bits);

        unsafe {
            self.insert_bytes(idx, bits);
        }
    }

    #[inline]
    unsafe fn insert_bytes(&mut self, idx: usize, bytes: &[u8]) {
        let len = self.len();
        let amt = bytes.len();
        self.vec.reserve(amt);

        unsafe {
            core::ptr::copy(
                self.vec.as_ptr().add(idx),
                self.vec.as_mut_ptr().add(idx + amt),
                len - idx,
            );
            core::ptr::copy_nonoverlapping(bytes.as_ptr(), self.vec.as_mut_ptr().add(idx), amt);
            self.vec.set_len(len + amt);
        }
    }

    /// Returns a mutable reference to the contents of this `InternalString`.
    ///
    /// # Safety
    ///
    /// This function is unsafe because the returned `&mut Vec` allows writing
    /// bytes which are not valid Java CESU-8. If this constraint is violated,
    /// using the original `InternalString` after dropping the `&mut Vec` may
    /// violate memory safety, as `InternalString`s are expected to always
    /// contains valid Java CESU-8.
    #[inline]
    pub(crate) unsafe fn as_mut_vec(&mut self) -> &mut Vec<u8> {
        &mut self.vec
    }

    /// Returns the length of this `InternalString`, in bytes, nor [`char`]s or
    /// graphemes. In other words, it might not be what a human considers the
    /// length of the string.
    #[inline]
    #[must_use]
    pub(crate) fn len(&self) -> usize {
        self.vec.len()
    }

    /// Returns `true` if this `InternalString` has a length of zero, and
    /// `false` otherwise.
    #[inline]
    #[must_use]
    pub(crate) fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Truncates this `InternalString`, removing all contents.
    ///
    /// While this means the `InternalString` will have a length of zero, it
    /// does not touch its capacity.
    #[inline]
    pub(crate) fn clear(&mut self) {
        self.vec.clear();
    }

    /// Converts this `InternalString` into a <code>[Box]<[InternalStr]</code>.
    ///
    /// This will drop any excess capacity.
    #[inline]
    #[must_use]
    pub(crate) fn into_boxed_str(self) -> Box<InternalStr> {
        let slice = self.vec.into_boxed_slice();
        unsafe { InternalStr::from_boxed_unchecked(slice) }
    }

    /// Consumes and leaks the `InternalString`, returning a mutable reference
    /// to the contents, `&'a mut InternalStr`.
    ///
    /// The caller has free choice over the returned lifetime, including
    /// `'static`. Indeed, this function is ideally used for data that lives fro
    /// the remainder of the program's life, as dropping the returned reference
    /// will cause a memory leak.
    ///
    /// It does not reallocate or shrink the `InternalString`, so the leaked
    /// allocation may include unused capacity that is not part of the returned
    /// slice. If you don't want that, call [`into_boxed_str`], and then
    /// [`Box::leak`].
    ///
    /// [`into_boxed_str`]: Self::into_boxed_str
    #[inline]
    #[must_use]
    pub(crate) fn leak<'a>(self) -> &'a mut InternalStr {
        let slice = self.vec.leak();
        unsafe { InternalStr::from_unchecked_mut(slice) }
    }
}

impl Default for InternalString {
    fn default() -> Self {
        Self::new()
    }
}

impl Borrow<InternalStr> for InternalString {
    fn borrow(&self) -> &InternalStr {
        self
    }
}

impl Deref for InternalString {
    type Target = InternalStr;

    #[inline]
    fn deref(&self) -> &Self::Target {
        unsafe { InternalStr::from_unchecked(&self.vec) }
    }
}

impl DerefMut for InternalString {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { InternalStr::from_unchecked_mut(&mut self.vec) }
    }
}

impl core::fmt::Debug for InternalString {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        core::fmt::Debug::fmt(self.as_str(), f)
    }
}

impl core::fmt::Display for InternalString {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        core::fmt::Display::fmt(self.as_str(), f)
    }
}
