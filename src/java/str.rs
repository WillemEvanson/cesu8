use crate::internal::InternalStr;
use crate::{validate_cesu8_internal, EncodingError};

use super::iter::{JavaCharIndices, JavaChars};

use core::ops::RangeBounds;

#[cfg(feature = "alloc")]
use super::JavaString;

#[cfg(feature = "alloc")]
use alloc::borrow::ToOwned;
#[cfg(feature = "alloc")]
use alloc::boxed::Box;

/// A Java CESU-8 encoded string slice.
#[repr(transparent)]
#[derive(PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct JavaStr {
    pub(crate) internal: InternalStr,
}

impl JavaStr {
    /// Converts a slice of bytes to a `JavaStr`.
    ///
    /// A Java CESU-8 string slice ([`JavaStr`]) is made of bytes ([`u8`]), and
    /// a byte slice ([`[u8]`][byteslice]) is made of bytes, so this
    /// function converts betwen the two. Not all byte slices are valid
    /// string slices, however `JavaStr` requires that it is valid Java
    /// CESU-8. [`from_java_cesu8`] checks to ensure that the bytes are
    /// valid Java CESU-8, and then does the conversion.
    ///
    /// [byteslice]: slice
    /// [`from_java_cesu8`]: Self::from_java_cesu8
    ///
    /// If you are sure that the byte slice is valid Java CESU-8, and you don't
    /// want to incur the overhead of the validity check, there is an unsafe
    /// version of this function [`from_java_cesu8_unchecked`], which has the
    /// same behavior but skips the check.
    ///
    /// [`from_java_cesu8_unchecked`]: Self::from_java_cesu8_unchecked
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if the slice is not Java CESU-8 with
    /// a description as to why the provided slice is
    /// not Java CESU-8.
    #[inline]
    pub fn from_java_cesu8(v: &[u8]) -> Result<&JavaStr, EncodingError> {
        match validate_cesu8_internal::<true>(v) {
            Ok(()) => Ok(unsafe { JavaStr::from_java_cesu8_unchecked(v) }),
            Err(e) => Err(e),
        }
    }

    /// Converts a mutable slice of bytes to a mutable `JavaStr`.
    ///
    /// A Java CESU-8 string slice ([`JavaStr`]) is made of bytes ([`u8`]), and
    /// a byte slice ([`[u8]`][byteslice]) is made of bytes, so this
    /// function converts betwen the two. Not all byte slices are valid
    /// string slices, however `JavaStr` requires that it is valid Java
    /// CESU-8. [`from_java_cesu8`] checks to ensure that the bytes are
    /// valid Java CESU-8, and then does the conversion.
    ///
    /// [byteslice]: slice
    /// [`from_java_cesu8`]: Self::from_java_cesu8
    ///
    /// If you are sure that the byte slice is valid Java CESU-8, and you don't
    /// want to incur the overhead of the validity check, there is an unsafe
    /// version of this function [`from_java_cesu8_unchecked_mut`], which has
    /// the same behavior but skips the check.
    ///
    /// [`from_java_cesu8_unchecked_mut`]: Self::from_java_cesu8_unchecked_mut
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if the slice is not Java CESU-8 with
    /// a description as to why the provided slice is
    /// not Java CESU-8.
    #[inline]
    pub fn from_java_cesu8_mut(v: &mut [u8]) -> Result<&mut JavaStr, EncodingError> {
        match validate_cesu8_internal::<true>(v) {
            Ok(()) => Ok(unsafe { JavaStr::from_java_cesu8_unchecked_mut(v) }),
            Err(e) => Err(e),
        }
    }

    /// Converts a slice of bytes to a `JavaStr` without checking that the
    /// string contains valid Java CESU-8.
    ///
    /// See the safe version, [`from_java_cesu8`], for more details.
    ///
    /// [`from_java_cesu8`]: Self::from_java_cesu8
    ///
    /// # Safety
    ///
    /// The bytes passed in must be valid Java CESU-8.
    #[inline]
    #[must_use]
    pub const unsafe fn from_java_cesu8_unchecked(v: &[u8]) -> &JavaStr {
        unsafe { &*(v as *const [u8] as *const JavaStr) }
    }

    /// Converts a mutable slice of bytes to a mutable `JavaStr` without
    /// checking that the string contains valid Java CESU-8.
    ///
    /// See the safe version, [`from_java_cesu8_mut`], for more details.
    ///
    /// [`from_java_cesu8_mut`]: Self::from_java_cesu8_mut
    ///
    /// # Safety
    ///
    /// The bytes passed in must be valid Java CESU-8.
    #[inline]
    #[must_use]
    pub unsafe fn from_java_cesu8_unchecked_mut(v: &mut [u8]) -> &mut JavaStr {
        unsafe { &mut *(v as *mut [u8] as *mut JavaStr) }
    }

    /// Converts a boxed slice of bytes to a boxed string slice without checking
    /// that the string contains valid Java CESU-8.
    ///
    /// # Safety
    ///
    /// The bytes passed in must be valid Java CESU-8.
    #[cfg(feature = "alloc")]
    #[inline]
    #[must_use]
    pub unsafe fn from_boxed_java_cesu8_unchecked(v: Box<[u8]>) -> Box<JavaStr> {
        unsafe { Box::from_raw(Box::into_raw(v) as *mut JavaStr) }
    }

    /// Converts an `InternalStr` to a `JavaStr` without checking that the
    /// string contains valid Java CESU-8.
    ///
    /// # Safety
    ///
    /// The string passed in must be valid Java CESU-8.
    #[inline]
    #[must_use]
    pub(crate) const unsafe fn from_internal_unchecked(v: &InternalStr) -> &JavaStr {
        unsafe { &*(v as *const InternalStr as *const JavaStr) }
    }

    /// Converts a mutable `InternalStr` to a mutable `JavaStr` without
    /// checking that the string contains valid Java CESU-8.
    ///
    /// # Safety
    ///
    /// The string passed in must be valid Java CESU-8.
    #[inline]
    #[must_use]
    pub(crate) unsafe fn from_internal_unchecked_mut(v: &mut InternalStr) -> &mut JavaStr {
        unsafe { &mut *(v as *mut InternalStr as *mut JavaStr) }
    }

    /// Converts an `InternalStr` into a boxed string slice without checking
    /// that the string contains valid Java CESU-8.
    ///
    /// # Safety
    ///
    /// The string passed in must be valid Java CESU-8.
    #[cfg(feature = "alloc")]
    #[inline]
    #[must_use]
    pub(crate) unsafe fn from_boxed_internal_unchecked(v: Box<InternalStr>) -> Box<JavaStr> {
        unsafe { Box::from_raw(Box::into_raw(v) as *mut JavaStr) }
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

    /// Checks that the `index`-th byte is the first byte in a Java CESU-8 code
    /// point sequence or the end of the string.
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
    /// The caller must ensure that the content of the slice is valid Java
    /// CESU-8 before the borrow ends and the underlying `JavaStr` is used.
    ///
    /// Use of a `JavaStr` whose contents are not valid Java CESU-8 is undefined
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
    /// modified in a way that it remains valid Java CESU-8.
    #[inline]
    #[must_use]
    pub fn as_mut_ptr(&mut self) -> *mut u8 {
        self.internal.as_mut_ptr()
    }

    /// Returns a subslice of `JavaStr`.
    ///
    /// This is the non-panicking alternative to indexing the `str`. Returns
    /// [`None`] whenever equivalent indexing operations would panic.
    #[inline]
    #[must_use]
    pub fn get<I: RangeBounds<usize>>(&self, index: I) -> Option<&JavaStr> {
        self.internal
            .get(index)
            .map(|internal| unsafe { JavaStr::from_internal_unchecked(internal) })
    }

    /// Returns a mutable subslice of `JavaStr`.
    ///
    /// This is the non-panicking alternative to indexing the `JavaStr`.
    /// Returns [`None`] whenver equivalent indexing operations would panic.
    #[inline]
    #[must_use]
    pub fn get_mut<I: RangeBounds<usize>>(&mut self, index: I) -> Option<&mut JavaStr> {
        self.internal
            .get_mut(index)
            .map(|internal| unsafe { JavaStr::from_internal_unchecked_mut(internal) })
    }

    /// Returns an unchecked subslice of `JavaStr`.
    ///
    /// This is the unchecked alternative to indexing the `JavaStr`.
    ///
    /// # Safety
    ///
    /// Callers of this function are responsible for ensuring that:
    /// * The starting index does not exceed the ending index;
    /// * The indices are within the bounds of the original slice;
    /// * The indices fall on Java CESU-8 sequence boundaries.
    ///
    /// Failing that, the returned string slice may reference invalid memory or
    /// violate the invariants communicated by the `JavaStr` type.
    #[inline]
    #[must_use]
    pub unsafe fn get_unchecked<I: RangeBounds<usize>>(&self, index: I) -> &JavaStr {
        unsafe { JavaStr::from_internal_unchecked(self.internal.get_unchecked(index)) }
    }

    /// Returns a mutable, unchecked subslice of `JavaStr`.
    ///
    /// This the unchecked alternative to indexing the `JavaStr`.
    ///
    /// # Safety
    ///
    /// Callers of this function are responsible for ensuring that:
    /// * The starting index does not exceed the ending index;
    /// * The indices are within the bounds of the original slice;
    /// * The indices fall on Java CESU-8 sequence boundaries.
    ///
    /// Failing that, the returned string slice may reference invalid memory or
    /// violate the invariants communicated by the `JavaStr` type.
    #[inline]
    #[must_use]
    pub unsafe fn get_unchecked_mut<I: RangeBounds<usize>>(&mut self, index: I) -> &mut JavaStr {
        unsafe { JavaStr::from_internal_unchecked_mut(self.internal.get_unchecked_mut(index)) }
    }

    /// Divide one string slice into two at an index.
    ///
    /// The argument, `mid`, should be a byte offset from the start of the
    /// string. It must also be on the boundary of a Java CESU-8 character.
    ///
    /// The two slices returned go from the string of the string slice to `mid`,
    /// and from `mid` to the end of the string slice.
    ///
    /// To get mutable string slices instead, see the [`split_at_mut`] method.
    ///
    /// [`split_at_mut`]: Self::split_at_mut
    #[inline]
    #[must_use]
    pub fn split_at(&self, mid: usize) -> (&JavaStr, &JavaStr) {
        let (left, right) = self.internal.split_at(mid);
        unsafe {
            (
                JavaStr::from_internal_unchecked(left),
                JavaStr::from_internal_unchecked(right),
            )
        }
    }

    /// Divide one mutable string slice into two at an index.
    ///
    /// The argument, `mid`, should be a byte offset from the start of the
    /// string. It must also be on the boundary of a Java CESU-8 character.
    ///
    /// The two slices returned go from the string of the string slice to `mid`,
    /// and from `mid` to the end of the string slice.
    ///
    /// To get immutable string slices instead, see the [`split_at`] method.
    ///
    /// [`split_at`]: Self::split_at
    #[inline]
    #[must_use]
    pub fn split_at_mut(&mut self, mid: usize) -> (&mut JavaStr, &mut JavaStr) {
        let (left, right) = self.internal.split_at_mut(mid);
        unsafe {
            (
                JavaStr::from_internal_unchecked_mut(left),
                JavaStr::from_internal_unchecked_mut(right),
            )
        }
    }

    /// Divide one string slice into two at an index.
    ///
    /// The argument, `mid`, should be a valid byte offset from the start of the
    /// string. It must also be on the boundary of a Java CESU-8 code point. The
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
    pub fn split_at_checked(&self, mid: usize) -> Option<(&JavaStr, &JavaStr)> {
        let (left, right) = self.internal.split_at_checked(mid)?;
        Some(unsafe {
            (
                JavaStr::from_internal_unchecked(left),
                JavaStr::from_internal_unchecked(right),
            )
        })
    }

    /// Divide one mutable string slice into two at an index.
    ///
    /// The argument, `mid`, should be a valid byte offset from the start of the
    /// string. It must also be on the boundary of a Java CESU-8 code point. The
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
    pub fn split_at_mut_checked(&mut self, mid: usize) -> Option<(&mut JavaStr, &mut JavaStr)> {
        let (left, right) = self.internal.split_at_mut_checked(mid)?;
        Some(unsafe {
            (
                JavaStr::from_internal_unchecked_mut(left),
                JavaStr::from_internal_unchecked_mut(right),
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
    /// of the string and falls on the boundary of a Java CESU-8 character.
    #[inline]
    #[must_use]
    pub unsafe fn split_at_unchecked(&self, mid: usize) -> (&JavaStr, &JavaStr) {
        let (left, right) = self.internal.split_at_unchecked(mid);
        unsafe {
            (
                JavaStr::from_internal_unchecked(left),
                JavaStr::from_internal_unchecked(right),
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
    /// of the string and falls on the boundary of a Java CESU-8 character.
    #[inline]
    #[must_use]
    pub unsafe fn split_at_mut_unchecked(&mut self, mid: usize) -> (&mut JavaStr, &mut JavaStr) {
        let (left, right) = self.internal.split_at_mut_unchecked(mid);
        unsafe {
            (
                JavaStr::from_internal_unchecked_mut(left),
                JavaStr::from_internal_unchecked_mut(right),
            )
        }
    }

    /// Returns an iterator over the [`char`]s of a string slice.
    ///
    /// As an `JavaStr` consists of valid Java CESU-8, we can iterate through a
    /// string by [`char`]. This method returns such an iterator.
    ///
    /// It's important to remember that [`char`] represents a Unicode Scalar
    /// Value, and might not match your idea of what a 'character' is. Iteration
    /// over grapheme clusters may be what you actually want. This functionality
    /// is not provided by this crate.
    #[inline]
    pub fn chars(&self) -> JavaChars {
        JavaChars {
            iter: self.internal.chars(),
        }
    }

    /// Returns an iterator over the [`char`]s of a string slice, and their
    /// positions.
    ///
    /// As an `JavaStr` consists of valid Java CESU-8, we can iterate through a
    /// string by [`char`]. This method returns an iterator of both these
    /// [`char`]s, as well as their byte positions.
    ///
    /// The iterator yields tuples. The position is first,
    /// the [`char`] is second.
    #[inline]
    pub fn char_indices(&self) -> JavaCharIndices {
        JavaCharIndices {
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
impl ToOwned for JavaStr {
    type Owned = JavaString;

    #[inline]
    fn to_owned(&self) -> Self::Owned {
        let vec = self.as_bytes().to_owned();
        unsafe { JavaString::from_java_cesu8_unchecked(vec) }
    }
}

impl AsRef<[u8]> for JavaStr {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        self.as_bytes()
    }
}

impl core::fmt::Debug for JavaStr {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        core::fmt::Debug::fmt(&self.internal, f)
    }
}

impl core::fmt::Display for JavaStr {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        core::fmt::Display::fmt(&self.internal, f)
    }
}
