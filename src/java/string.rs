#![cfg(feature = "alloc")]
use super::JavaStr;
use crate::internal::{InternalStr, InternalString};
use crate::{validate_cesu8_internal, EncodingError};

use core::borrow::Borrow;
use core::ops::{Deref, DerefMut};

use alloc::boxed::Box;
use alloc::collections::TryReserveError;
use alloc::vec::Vec;

/// A Java CESU-8 encoded, growable string.
#[repr(transparent)]
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct JavaString {
    internal: InternalString,
}

impl JavaString {
    /// Creates a new empty `JavaString`.
    ///
    /// Given that the `JavaString` is empty, this will not allocate any
    /// initial buffer. While that means that this initial operations is very
    /// inexpensive, it may cause excessive allocation later when you add data.
    /// If you have an idea of how much data the `JavaString` will hold,
    /// consider the [`with_capacity`] method to prevent excessive
    /// re-allocation.
    ///
    /// [`with_capacity`]: Self::with_capacity
    #[inline]
    #[must_use]
    pub const fn new() -> JavaString {
        JavaString {
            internal: InternalString::new(),
        }
    }

    /// Creates a new empty `JavaString` with at least the specified
    /// capacity.
    ///
    /// `JavaString`s have an internal buffer to hold their data. The
    /// capacity is at length of that buffer, and can be queried with the
    /// [`capacity`] method. This method creates an empty `JavaString`, but
    /// one with an initial buffer that can hold at least `capacity` bytes. This
    /// is useful when you may be appending a bunch of data to the
    /// `JavaString`, reducing the number of reallocations it needs to do.
    ///
    /// [`capacity`]: Self::capacity
    ///
    /// If the given capacity is `0`, no allocation will occur, and this method
    /// is identical to the [`new`] method.
    ///
    /// [`new`]: Self::new
    #[inline]
    #[must_use]
    pub fn with_capacity(capacity: usize) -> JavaString {
        JavaString {
            internal: InternalString::with_capacity(capacity),
        }
    }

    /// Converts a vector of bytes into a `JavaString`.
    ///
    /// A string ([`JavaString`]) is made of bytes ([`u8`]), and a vector of
    /// bytes ([`Vec<u8>`]) is made of bytes, so this function converts between
    /// the two. Not all byte slices are valid `JavaString`s, however:
    /// `JavaString` requires that it is valid Java CESU-8. `from_java_cesu8`
    /// checks to ensure that the bytes are valid Java CESU-8, and then does
    /// the conversion.
    ///
    /// If you are sure that the byte slice is valid Java CESU-8, and you don't
    /// want to incur the overhead of the validity check, there is an unsafe
    /// version of this function, [`from_java_cesu8_unchecked`], which has
    /// the same behavior but skips the check.
    ///
    /// This method will take care to not to copy the vector, for efficiency's
    /// sake.
    ///
    /// If you need a [`&JavaStr`] instead of a `JavaString`, consider
    /// [`JavaStr::from_java_cesu8`].
    ///
    /// The inverse of this method is [`into_bytes`].
    ///
    /// [`from_java_cesu8_unchecked`]: Self::from_java_cesu8_unchecked
    /// [`&JavaStr`]: JavaStr
    /// [`into_bytes`]: Self::into_bytes
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if the slice is not Java CESU-8 with the index and
    /// length of the invalid byte. The vector you moved in is also
    /// included.
    #[inline]
    pub fn from_java_cesu8(vec: Vec<u8>) -> Result<JavaString, (EncodingError, Vec<u8>)> {
        match validate_cesu8_internal::<true>(&vec) {
            Ok(()) => unsafe {
                Ok(JavaString {
                    internal: InternalString::from_unchecked(vec),
                })
            },
            Err(e) => Err((e, vec)),
        }
    }

    /// Creates a new `JavaString` from a length, capacity, and pointer.
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
    /// * The first `length` bytes at `buf` need to be valid Java CESU-8.
    ///
    /// Violating these may cause problems like correcting the allocator's
    /// internal data structures. For example, it is normally **not** safe to
    /// build a `JavaString` from a pointer to a C `char` array containing
    /// Java CESU-8 _unless_ you are certain that array was originally allocated
    /// by the Rust standard library's allocator.
    ///
    /// The ownership of `buf` is effectively transferred to the
    /// `JavaString` which may then deallocate, reallocate, or change the
    /// contents of memory pointed to by the pointer at will. Ensure that
    /// nothing elese uses the pointer after calling this function.
    #[inline]
    #[must_use]
    pub unsafe fn from_raw_parts(buf: *mut u8, length: usize, capacity: usize) -> JavaString {
        unsafe {
            JavaString {
                internal: InternalString::from_raw_parts(buf, length, capacity),
            }
        }
    }

    /// Converts a vector of bytes to a `JavaString` without checking that
    /// the string contains valid Java CESU-8.
    ///
    /// # Safety
    ///
    /// This function is unsafe because it does not check that the bytes passed
    /// to it are valid Java CESU-8. If this constraint is violated, it may
    /// cause memory unsafety issues with future users of the `JavaString`.
    #[inline]
    #[must_use]
    pub const unsafe fn from_java_cesu8_unchecked(bytes: Vec<u8>) -> JavaString {
        JavaString {
            internal: InternalString::from_unchecked(bytes),
        }
    }

    /// Converts an internal string to a `JavaString` without checking that the
    /// string contains valid Java CESU-8.
    ///
    /// # Safety
    ///
    /// This function is unsafe because it does not check that the
    /// `InternalString` passed to it contains valid Java CESU-8. If this
    /// constraint is violated, it may cause memory unsafety issues with future
    /// users of the `JavaString`.
    #[inline]
    #[must_use]
    pub(crate) const unsafe fn from_internal_unchecked(internal: InternalString) -> JavaString {
        JavaString { internal }
    }

    /// Converts a `JavaString` into a byte vector.
    ///
    /// This consumes the `JavaString`, so we do not need to copy its contents.
    #[inline]
    #[must_use]
    pub fn into_bytes(self) -> Vec<u8> {
        self.internal.into_bytes()
    }

    /// Extracts a string slice containing the entire `JavaString`.
    #[inline]
    #[must_use]
    pub fn as_str(&self) -> &JavaStr {
        self
    }

    /// Converts a `JavaString` into a mutable string slice.
    #[inline]
    #[must_use]
    pub fn as_mut_str(&mut self) -> &mut JavaStr {
        self
    }

    /// Appends a given string slice onto the end of this `JavaString`.
    #[inline]
    pub fn push_str(&mut self, str: &JavaStr) {
        self.internal.push_str(&str.internal);
    }

    /// Returns this `JavaString`'s capacity, in bytes.
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
    /// [`try_reserve`]: JavaString::try_reserve
    ///
    /// # Errors
    ///
    /// If the capacity overflows, or the allocator reports a failure, then an
    /// error is returned.
    #[inline]
    pub fn try_reserve_exact(&mut self, additional: usize) -> Result<(), TryReserveError> {
        self.internal.try_reserve_exact(additional)
    }

    /// Shrinks the capacity of this `JavaString` to match its length.
    #[inline]
    pub fn shrink_to_fit(&mut self) {
        self.internal.shrink_to_fit();
    }

    /// Shrinks the capacity of this `JavaString` with a lower bound.
    ///
    /// The capacity will remaing at least as large as both the length and the
    /// supplied value.
    ///
    /// If the current capacity is less than the lower limit, this is a no-op.
    #[inline]
    pub fn shrink_to(&mut self, min_capacity: usize) {
        self.internal.shrink_to(min_capacity);
    }

    /// Appends the given [`char`] to the end of this `JavaString`.
    #[inline]
    pub fn push(&mut self, c: char) {
        self.internal.push::<true>(c);
    }

    /// Returns a byte slice of this `JavaString`'s contents.
    #[inline]
    #[must_use]
    pub fn as_bytes(&self) -> &[u8] {
        self.internal.as_bytes()
    }

    /// Shortens this `JavaString` to the specified length.
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
    /// Returns [`None`] if this `JavaString` is empty.
    #[inline]
    #[must_use]
    pub fn pop(&mut self) -> Option<char> {
        self.internal.pop()
    }

    /// Removes a [`char`] from this `JavaString` at a byte position and
    /// returns it.
    ///
    /// This is an *O*(*n*) operation, as it requires copy every element in the
    /// buffer.
    ///
    /// # Panics
    ///
    /// Panics if `idx` is large than or equal to the `JavaString`'s length, or
    /// if it does not lie on a [`char`] boundary.
    #[inline]
    pub fn remove(&mut self, idx: usize) -> char {
        self.internal.remove(idx)
    }

    /// Inserts a character into this `JavaString` at a byte position.
    ///
    /// This is an *O*(*n*) operation as it requires copying every element in
    /// the buffer.
    ///
    /// # Panics
    ///
    /// Panics if `idx` is larger than the `JavaString`'s length, or if it does
    /// not lie on a [`char`] boundary.
    #[inline]
    pub fn insert(&mut self, idx: usize, c: char) {
        self.internal.insert::<true>(idx, c);
    }

    /// Returns a mutable reference to the contents of this `JavaString`.
    ///     
    /// # Safety
    ///
    /// This function is unsafe because the returned `&mut Vec` allows writing
    /// bytes which are not valid Java Java CESU-8. If this constraint is
    /// violated, using the original `JavaString` after dropping the `&mut Vec`
    /// may violate memory safety, as `JavaString`s are expected to always
    /// contains valid Java Java CESU-8.
    #[inline]
    pub unsafe fn as_mut_vec(&mut self) -> &mut Vec<u8> {
        self.internal.as_mut_vec()
    }

    /// Returns the length of this `JavaString`, in bytes, nor [`char`]s or
    /// graphemes. In other words, it might not be what a human considers the
    /// length of the string.
    #[inline]
    #[must_use]
    pub fn len(&self) -> usize {
        self.internal.len()
    }

    /// Returns `true` if this `JavaString` has a length of zero, and `false`
    /// otherwise.
    #[inline]
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.internal.is_empty()
    }

    /// Truncates this `JavaString`, removing all contents.
    ///
    /// While this means the `JavaString` will have a length of zero, it does
    /// not touch its capacity.
    #[inline]
    pub fn clear(&mut self) {
        self.internal.clear();
    }

    /// Converts this `JavaString` into a <code>[Box]<[JavaStr]</code>.
    ///
    /// This will drop any excess capacity.
    #[inline]
    #[must_use]
    pub fn into_boxed_str(self) -> Box<JavaStr> {
        let x = self.internal.into_boxed_str();
        unsafe { JavaStr::from_boxed_internal_unchecked(x) }
    }

    /// Consumes and leaks the `JavaString`, returning a mutable reference to
    /// the contents, `&'a mut InternalStr`.
    ///
    /// The caller has free choice over the returned lifetime, including
    /// `'static`. Indeed, this function is ideally used for data that lives fro
    /// the remainder of the program's life, as dropping the returned reference
    /// will cause a memory leak.
    ///
    /// It does not reallocate or shrink the `JavaString`, so the leaked
    /// allocation may include unused capacity that is not part of the returned
    /// slice. If you don't want that, call [`into_boxed_str`], and then
    /// [`Box::leak`].
    ///
    /// [`into_boxed_str`]: Self::into_boxed_str
    #[inline]
    #[must_use]
    pub fn leak<'a>(self) -> &'a mut JavaStr {
        let str = self.internal.leak();
        unsafe { &mut *(str as *mut InternalStr as *mut JavaString) }
    }
}

impl Default for JavaString {
    fn default() -> Self {
        Self::new()
    }
}

impl Borrow<JavaStr> for JavaString {
    fn borrow(&self) -> &JavaStr {
        self
    }
}

impl Deref for JavaString {
    type Target = JavaStr;

    #[inline]
    fn deref(&self) -> &Self::Target {
        unsafe { JavaStr::from_java_cesu8_unchecked(self.internal.as_bytes()) }
    }
}

impl DerefMut for JavaString {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { JavaStr::from_java_cesu8_unchecked_mut(self.internal.as_bytes_mut()) }
    }
}

impl core::fmt::Debug for JavaString {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        core::fmt::Debug::fmt(&self.internal, f)
    }
}

impl core::fmt::Display for JavaString {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        core::fmt::Display::fmt(&self.internal, f)
    }
}
