use crate::internal::InternalStr;
use crate::{validate_cesu8_internal, EncodingError};

use super::iter::{Cesu8CharIndices, Cesu8Chars};

use core::ops::RangeBounds;

#[cfg(feature = "alloc")]
use super::Cesu8String;

#[cfg(feature = "alloc")]
use alloc::borrow::ToOwned;
#[cfg(feature = "alloc")]
use alloc::boxed::Box;

/// A CESU-8 encoded string slice.
#[repr(transparent)]
#[derive(PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Cesu8Str {
    pub(crate) internal: InternalStr,
}

impl Cesu8Str {
    /// Converts a slice of bytes to a `Cesu8Str`.
    ///
    /// A CESU-8 string slice ([`Cesu8Str`]) is made of bytes ([`u8`]), and a
    /// byte slice ([`[u8]`][byteslice]) is made of bytes, so this function
    /// converts betwen the two. Not all byte slices are valid string slices,
    /// however `Cesu8Str` requires that it is valid CESU-8. [`from_cesu8`]
    /// checks to ensure that the bytes are valid CESU-8, and then does the
    /// conversion.
    ///
    /// [byteslice]: slice
    /// [`from_cesu8`]: Self::from_cesu8
    ///
    /// If you are sure that the byte slice is valid CESU-8, and you don't want
    /// to incur the overhead of the validity check, there is an unsafe
    /// version of this function [`from_cesu8_unchecked`], which has the
    /// same behavior but skips the check.
    ///
    /// [`from_cesu8_unchecked`]: Self::from_cesu8_unchecked
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if the slice is not CESU-8 with
    /// a description as to why the provided slice is
    /// not CESU-8.
    #[inline]
    pub const fn from_cesu8(v: &[u8]) -> Result<&Cesu8Str, EncodingError> {
        match validate_cesu8_internal::<false>(v) {
            Ok(()) => Ok(unsafe { Cesu8Str::from_cesu8_unchecked(v) }),
            Err(e) => Err(e),
        }
    }

    /// Converts a mutable slice of bytes to a mutable `Cesu8Str`.
    ///
    /// A CESU-8 string slice ([`Cesu8Str`]) is made of bytes ([`u8`]), and a
    /// byte slice ([`[u8]`][byteslice]) is made of bytes, so this function
    /// converts betwen the two. Not all byte slices are valid string slices,
    /// however `Cesu8Str` requires that it is valid CESU-8. [`from_cesu8`]
    /// checks to ensure that the bytes are valid CESU-8, and then does the
    /// conversion.
    ///
    /// [byteslice]: slice
    /// [`from_cesu8`]: Self::from_cesu8
    ///
    /// If you are sure that the byte slice is valid CESU-8, and you don't want
    /// to incur the overhead of the validity check, there is an unsafe
    /// version of this function [`from_cesu8_unchecked_mut`], which has the
    /// same behavior but skips the check.
    ///
    /// [`from_cesu8_unchecked_mut`]: Self::from_cesu8_unchecked_mut
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if the slice is not CESU-8 with
    /// a description as to why the provided slice is
    /// not CESU-8.
    #[inline]
    pub fn from_cesu8_mut(v: &mut [u8]) -> Result<&mut Cesu8Str, EncodingError> {
        match validate_cesu8_internal::<false>(v) {
            Ok(()) => Ok(unsafe { Cesu8Str::from_cesu8_unchecked_mut(v) }),
            Err(e) => Err(e),
        }
    }

    /// Converts a slice of bytes to a `Cesu8Str` without checking that the
    /// string contains valid CESU-8.
    ///
    /// See the safe version, [`from_cesu8`], for more details.
    ///
    /// [`from_cesu8`]: Self::from_cesu8
    ///
    /// # Safety
    ///
    /// The bytes passed in must be valid CESU-8.
    #[inline]
    #[must_use]
    pub const unsafe fn from_cesu8_unchecked(v: &[u8]) -> &Cesu8Str {
        unsafe { &*(v as *const [u8] as *const Cesu8Str) }
    }

    /// Converts a mutable slice of bytes to a mutable `Cesu8Str` without
    /// checking that the string contains valid CESU-8.
    ///
    /// See the safe version, [`from_cesu8_mut`], for more details.
    ///
    /// [`from_cesu8_mut`]: Self::from_cesu8_mut
    ///
    /// # Safety
    ///
    /// The bytes passed in must be valid CESU-8.
    #[inline]
    #[must_use]
    pub unsafe fn from_cesu8_unchecked_mut(v: &mut [u8]) -> &mut Cesu8Str {
        unsafe { &mut *(v as *mut [u8] as *mut Cesu8Str) }
    }

    /// Converts a boxed slice of bytes to a boxed string slice without checking
    /// that the string contains valid CESU-8.
    ///
    /// # Safety
    ///
    /// The bytes passed in must be valid CESU-8.
    #[cfg(feature = "alloc")]
    #[inline]
    #[must_use]
    pub unsafe fn from_boxed_cesu8_unchecked(v: Box<[u8]>) -> Box<Cesu8Str> {
        unsafe { Box::from_raw(Box::into_raw(v) as *mut Cesu8Str) }
    }

    /// Converts an `InternalStr` to a `Cesu8Str` without checking that the
    /// string contains valid CESU-8.
    ///
    /// # Safety
    ///
    /// The string passed in must be valid CESU-8.
    #[inline]
    #[must_use]
    pub(crate) const unsafe fn from_internal_unchecked(v: &InternalStr) -> &Cesu8Str {
        unsafe { &*(v as *const InternalStr as *const Cesu8Str) }
    }

    /// Converts a mutable `InternalStr` to a mutable `Cesu8Str` without
    /// checking that the string contains valid CESU-8.
    ///
    /// # Safety
    ///
    /// The string passed in must be valid CESU-8.
    #[inline]
    #[must_use]
    pub(crate) unsafe fn from_internal_unchecked_mut(v: &mut InternalStr) -> &mut Cesu8Str {
        unsafe { &mut *(v as *mut InternalStr as *mut Cesu8Str) }
    }

    /// Converts an `InternalStr` into a boxed string slice without checking
    /// that the string contains valid CESU-8.
    ///
    /// # Safety
    ///
    /// The string passed in must be valid CESU-8.
    #[cfg(feature = "alloc")]
    #[inline]
    #[must_use]
    pub(crate) unsafe fn from_boxed_internal_unchecked(v: Box<InternalStr>) -> Box<Cesu8Str> {
        unsafe { Box::from_raw(Box::into_raw(v) as *mut Cesu8Str) }
    }

    /// Returns the length of `self`.
    ///
    /// This length is in bytes, not [`char`]s or graphemes. In other words, it
    /// might not be what a human considers the length of the string.
    #[inline]
    #[must_use]
    pub const fn len(&self) -> usize {
        self.internal.len()
    }

    /// Returns `true` if `self` has a length of zero bytes.
    #[inline]
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.internal.is_empty()
    }

    /// Checks that the `index`-th byte is the first byte in a CESU-8 code point
    /// sequence or the end of the string.
    ///
    /// The start and end of the string (when `index == self.len()`) are
    /// considered to be boundaries.
    ///
    /// Returns `false` if `index is greater than self.len()`.
    #[inline]
    #[must_use]
    pub fn is_char_boundary(&self, index: usize) -> bool {
        self.internal.is_char_boundary(index)
    }

    /// Converts a string slice to a byte slice.
    #[inline]
    #[must_use]
    pub const fn as_bytes(&self) -> &[u8] {
        self.internal.as_bytes()
    }

    /// Converts a mutable string slice to a mutable byte slice.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the content of the slice is valid CESU-8
    /// before the borrow ends and the underlying `Cesu8Str` is used.
    ///
    /// Use of a `Cesu8Str` whose contents are not valid CESU-8 is undefined
    /// behavior.
    #[inline]
    #[must_use]
    pub unsafe fn as_bytes_mut(&mut self) -> &mut [u8] {
        self.internal.as_bytes_mut()
    }

    /// Converts a string slice to a raw pointer.
    ///
    /// As string slices are a slice of bytes, the raw pointer points to a
    /// [`u8`]. This pointer will be pointing to the first bytes of the string
    /// slice.
    ///
    /// The caller must ensure that the returned pointer is never written to. If
    /// you need to mutate the contents of the string slice, use [`as_mut_ptr`].
    ///
    /// [`as_mut_ptr`]: Self::as_mut_ptr
    #[inline]
    #[must_use]
    pub const fn as_ptr(&self) -> *const u8 {
        self.internal.as_ptr()
    }

    /// Converts a mutable string slice to a raw pointer.
    ///
    /// As string slices are a slice of bytes, the raw pointer points to a
    /// [`u8`]. This pointer will be pointing to the first byte of the string
    /// slice.
    ///
    /// It is your responsibility to make sure that the string slice only gets
    /// modified in a way that it remains valid CESU-8.
    #[inline]
    #[must_use]
    pub fn as_mut_ptr(&mut self) -> *mut u8 {
        self.internal.as_mut_ptr()
    }

    /// Returns a subslice of `Cesu8Str`.
    ///
    /// This is the non-panicking alternative to indexing the `str`. Returns
    /// [`None`] whenever equivalent indexing operations would panic.
    #[inline]
    #[must_use]
    pub fn get<I: RangeBounds<usize>>(&self, index: I) -> Option<&Cesu8Str> {
        self.internal
            .get(index)
            .map(|internal| unsafe { Cesu8Str::from_internal_unchecked(internal) })
    }

    /// Returns a mutable subslice of `Cesu8Str`.
    ///
    /// This is the non-panicking alternative to indexing the `Cesu8Str`.
    /// Returns [`None`] whenver equivalent indexing operations would panic.
    #[inline]
    #[must_use]
    pub fn get_mut<I: RangeBounds<usize>>(&mut self, index: I) -> Option<&mut Cesu8Str> {
        self.internal
            .get_mut(index)
            .map(|internal| unsafe { Cesu8Str::from_internal_unchecked_mut(internal) })
    }

    /// Returns an unchecked subslice of `Cesu8Str`.
    ///
    /// This is the unchecked alternative to indexing the `Cesu8Str`.
    ///
    /// # Safety
    ///
    /// Callers of this function are responsible for ensuring that:
    /// * The starting index does not exceed the ending index;
    /// * The indices are within the bounds of the original slice;
    /// * The indices fall on CESU-8 sequence boundaries.
    ///
    /// Failing that, the returned string slice may reference invalid memory or
    /// violate the invariants communicated by the `Cesu8Str` type.
    #[inline]
    #[must_use]
    pub unsafe fn get_unchecked<I: RangeBounds<usize>>(&self, index: I) -> &Cesu8Str {
        unsafe { Cesu8Str::from_internal_unchecked(self.internal.get_unchecked(index)) }
    }

    /// Returns a mutable, unchecked subslice of `Cesu8Str`.
    ///
    /// This the unchecked alternative to indexing the `Cesu8Str`.
    ///
    /// # Safety
    ///
    /// Callers of this function are responsible for ensuring that:
    /// * The starting index does not exceed the ending index;
    /// * The indices are within the bounds of the original slice;
    /// * The indices fall on CESU-8 sequence boundaries.
    ///
    /// Failing that, the returned string slice may reference invalid memory or
    /// violate the invariants communicated by the `Cesu8Str` type.
    #[inline]
    #[must_use]
    pub unsafe fn get_unchecked_mut<I: RangeBounds<usize>>(&mut self, index: I) -> &mut Cesu8Str {
        unsafe { Cesu8Str::from_internal_unchecked_mut(self.internal.get_unchecked_mut(index)) }
    }

    /// Divide one string slice into two at an index.
    ///
    /// The argument, `mid`, should be a byte offset from the start of the
    /// string. It must also be on the boundary of a CESU-8 character.
    ///
    /// The two slices returned go from the string of the string slice to `mid`,
    /// and from `mid` to the end of the string slice.
    ///
    /// To get mutable string slices instead, see the [`split_at_mut`] method.
    ///
    /// [`split_at_mut`]: Self::split_at_mut
    #[inline]
    #[must_use]
    pub fn split_at(&self, mid: usize) -> (&Cesu8Str, &Cesu8Str) {
        let (left, right) = self.internal.split_at(mid);
        unsafe {
            (
                Cesu8Str::from_internal_unchecked(left),
                Cesu8Str::from_internal_unchecked(right),
            )
        }
    }

    /// Divide one mutable string slice into two at an index.
    ///
    /// The argument, `mid`, should be a byte offset from the start of the
    /// string. It must also be on the boundary of a CESU-8 character.
    ///
    /// The two slices returned go from the string of the string slice to `mid`,
    /// and from `mid` to the end of the string slice.
    ///
    /// To get immutable string slices instead, see the [`split_at`] method.
    ///
    /// [`split_at`]: Self::split_at
    #[inline]
    #[must_use]
    pub fn split_at_mut(&mut self, mid: usize) -> (&mut Cesu8Str, &mut Cesu8Str) {
        let (left, right) = self.internal.split_at_mut(mid);
        unsafe {
            (
                Cesu8Str::from_internal_unchecked_mut(left),
                Cesu8Str::from_internal_unchecked_mut(right),
            )
        }
    }

    /// Divide one string slice into two at an index.
    ///
    /// The argument, `mid`, should be a valid byte offset from the start of the
    /// string. It must also be on the boundary of a CESU-8 code point. The
    /// method returns `None` if that's not the case.
    ///
    /// The two slices returned go from the start of the string slice to `mid`,
    /// and from `mid` to the end of the string slice.
    ///
    /// To get mutable string slices instead, see the [`split_at_mut_checked`]
    /// method.
    ///
    /// [`split_at_mut_checked`]: Self::split_at_mut_checked
    #[inline]
    #[must_use]
    pub fn split_at_checked(&self, mid: usize) -> Option<(&Cesu8Str, &Cesu8Str)> {
        let (left, right) = self.internal.split_at_checked(mid)?;
        Some(unsafe {
            (
                Cesu8Str::from_internal_unchecked(left),
                Cesu8Str::from_internal_unchecked(right),
            )
        })
    }

    /// Divide one mutable string slice into two at an index.
    ///
    /// The argument, `mid`, should be a valid byte offset from the start of the
    /// string. It must also be on the boundary of a CESU-8 code point. The
    /// method returns `None` if that's not the case.
    ///
    /// The two slices returned go from the start of the string slice to `mid`,
    /// and from `mid` to the end of the string slice.
    ///
    /// To get immutable string slices instead, see the [`split_at_checked`]
    /// method.
    ///
    /// [`split_at_checked`]: Self::split_at_checked
    #[inline]
    #[must_use]
    pub fn split_at_mut_checked(&mut self, mid: usize) -> Option<(&mut Cesu8Str, &mut Cesu8Str)> {
        let (left, right) = self.internal.split_at_mut_checked(mid)?;
        Some(unsafe {
            (
                Cesu8Str::from_internal_unchecked_mut(left),
                Cesu8Str::from_internal_unchecked_mut(right),
            )
        })
    }

    /// Divide a string into two at an index.
    ///
    /// The two slices returned go from the start of the string slice to `mid`,
    /// and from `mid` to the end of the string slice.
    ///
    /// To get mutable string slices instead, see the [`split_at_mut_unchecked`]
    /// method.
    ///
    /// [`split_at_mut_unchecked`]: Self::split_at_mut_unchecked
    ///
    /// # Safety
    ///
    /// The caller must ensure that `mid` is a valid byte offset from the start
    /// of the string and falls on the boundary of a CESU-8 character.
    #[inline]
    #[must_use]
    pub unsafe fn split_at_unchecked(&self, mid: usize) -> (&Cesu8Str, &Cesu8Str) {
        let (left, right) = self.internal.split_at_unchecked(mid);
        unsafe {
            (
                Cesu8Str::from_internal_unchecked(left),
                Cesu8Str::from_internal_unchecked(right),
            )
        }
    }

    /// Divide a mutable string into two at an index.
    ///
    /// The two slices returned go from the start of the string slice to `mid`,
    /// and from `mid` to the end of the string slice.
    ///
    /// To get immutable string slices instead, see the [`split_at_unchecked`]
    /// method.
    ///
    /// [`split_at_unchecked`]: Self::split_at_unchecked
    ///
    /// # Safety
    ///
    /// The caller must ensure that `mid` is a valid byte offset from the start
    /// of the string and falls on the boundary of a CESU-8 character.
    #[inline]
    #[must_use]
    pub unsafe fn split_at_mut_unchecked(&mut self, mid: usize) -> (&mut Cesu8Str, &mut Cesu8Str) {
        let (left, right) = self.internal.split_at_mut_unchecked(mid);
        unsafe {
            (
                Cesu8Str::from_internal_unchecked_mut(left),
                Cesu8Str::from_internal_unchecked_mut(right),
            )
        }
    }

    /// Returns an iterator over the [`char`]s of a string slice.
    ///
    /// As an `Cesu8Str` consists of valid CESU-8, we can iterate through a
    /// string by [`char`]. This method returns such an iterator.
    ///
    /// It's important to remember that [`char`] represents a Unicode Scalar
    /// Value, and might not match your idea of what a 'character' is. Iteration
    /// over grapheme clusters may be what you actually want. This functionality
    /// is not provided by this crate.
    #[inline]
    pub fn chars(&self) -> Cesu8Chars {
        Cesu8Chars {
            iter: self.internal.chars(),
        }
    }

    /// Returns an iterator over the [`char`]s of a string slice, and their
    /// positions.
    ///
    /// As an `Cesu8Str` consists of valid CESU-8, we can iterate through a
    /// string by [`char`]. This method returns an iterator of both these
    /// [`char`]s, as well as their byte positions.
    ///
    /// The iterator yields tuples. The position is first,
    /// the [`char`] is second.
    #[inline]
    pub fn char_indices(&self) -> Cesu8CharIndices {
        Cesu8CharIndices {
            iter: self.internal.char_indices(),
        }
    }

    /// Checks if all characters in this string are within the ASCII range.
    #[inline]
    #[must_use]
    pub const fn is_ascii(&self) -> bool {
        self.internal.is_ascii()
    }
}

#[cfg(feature = "alloc")]
impl ToOwned for Cesu8Str {
    type Owned = Cesu8String;

    #[inline]
    fn to_owned(&self) -> Self::Owned {
        let vec = self.as_bytes().to_owned();
        unsafe { Cesu8String::from_cesu8_unchecked(vec) }
    }
}

impl AsRef<[u8]> for Cesu8Str {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        self.as_bytes()
    }
}

impl core::fmt::Debug for Cesu8Str {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        core::fmt::Debug::fmt(&self.internal, f)
    }
}

impl core::fmt::Display for Cesu8Str {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        core::fmt::Display::fmt(&self.internal, f)
    }
}
