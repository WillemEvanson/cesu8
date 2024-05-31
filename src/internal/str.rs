use crate::internal::{InternalCharIndices, InternalChars};

use core::fmt::Write;
use core::ops::{
    Index, IndexMut, Range, RangeBounds, RangeFrom, RangeFull, RangeInclusive, RangeTo,
    RangeToInclusive,
};

#[cfg(feature = "alloc")]
use super::InternalString;

#[cfg(feature = "alloc")]
use alloc::borrow::ToOwned;
#[cfg(feature = "alloc")]
use alloc::boxed::Box;

/// A CESU-8 encoded string slice.
#[repr(transparent)]
#[derive(PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct InternalStr {
    bytes: [u8],
}

impl InternalStr {
    /// Converts a slice of bytes to a `InternalStr` without checking that the
    /// string contains valid CESU-8.
    ///
    /// An `InternalStr` does not validate its contents. It defines operations
    /// that can be made on any string following the CESU-8 format. Java's
    /// variant makes one change, nul bytes are encoded in two bytes. This
    /// library does not check that the characters are valid, merely that the
    /// format of the string is valid.
    ///
    /// # Safety
    ///
    /// The bytes passed in must be valid CESU-8.
    #[inline]
    #[must_use]
    pub(crate) const unsafe fn from_unchecked(v: &[u8]) -> &Self {
        unsafe { &*(v as *const [u8] as *const Self) }
    }

    /// Converts a mutable slice of bytes to a mutable `InternalStr` without
    /// checking that the string contains valid CESU-8.
    ///
    /// # Safety
    ///
    /// The bytes passed in must be valid CESU-8.
    #[inline]
    #[must_use]
    pub(crate) unsafe fn from_unchecked_mut(v: &mut [u8]) -> &mut Self {
        unsafe { &mut *(v as *mut [u8] as *mut Self) }
    }

    /// Converts a boxed slice of bytes to a boxed string slice without checking
    /// that the string contains valid CESU-8.
    ///
    /// # Safety
    ///
    /// The bytes passed in must be valid.
    #[cfg(feature = "alloc")]
    #[inline]
    #[must_use]
    pub(crate) unsafe fn from_boxed_unchecked(v: Box<[u8]>) -> Box<Self> {
        unsafe { Box::from_raw(Box::into_raw(v) as *mut Self) }
    }

    /// Returns the length of `self`.
    ///
    /// This length is in bytes, not [`char`]s or graphemes. In other words, it
    /// might not be what a human considers the length of the string.
    #[inline]
    #[must_use]
    pub(crate) const fn len(&self) -> usize {
        self.bytes.len()
    }

    /// Returns `true` if `self` has a length of zero bytes.
    #[inline]
    #[must_use]
    pub(crate) const fn is_empty(&self) -> bool {
        self.bytes.is_empty()
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
    pub(crate) fn is_char_boundary(&self, index: usize) -> bool {
        // 0 is always ok. This is a fast path so that it can optimze out the check
        // easily and skip reading string data for that case.
        if index == 0 {
            return true;
        }

        match self.bytes.get(index) {
            None => index == self.len(),
            Some(&b) => {
                if b < 128 || b & 0b111_00000 == 0b110_00000 {
                    // 1 or 2-byte characters
                    return true;
                } else if b & 0b1111_0000 == 0b1110_0000 {
                    // 3 or 6-byte characters

                    // SAFETY: Since this is a valid string, we know that there
                    // must be at least two more bytes.
                    let next = unsafe { self.bytes.get(index + 1).unwrap_unchecked() };
                    if b == 0b1110_1101 && next & 0b1111_0000 == 0b1011_0000 {
                        // Second code-point in a surrogate pair
                        return false;
                    }
                    return true;
                }
                false
            }
        }
    }

    /// Converts a string slice to a byte slice.
    #[inline]
    #[must_use]
    pub(crate) const fn as_bytes(&self) -> &[u8] {
        unsafe { core::mem::transmute(self) }
    }

    /// Converts a mutable string slice to a mutable byte slice.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the content of the slice is valid CESU-8
    /// before the borrow ends and the underlying `InternalStr` is used.
    ///
    /// Use of a `InternalStr` whose contents are not valid CESU-8 is undefined
    /// behavior.
    #[inline]
    #[must_use]
    pub(crate) unsafe fn as_bytes_mut(&mut self) -> &mut [u8] {
        unsafe { &mut *(self as *mut InternalStr as *mut [u8]) }
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
    pub(crate) const fn as_ptr(&self) -> *const u8 {
        self as *const InternalStr as *mut u8
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
    pub(crate) fn as_mut_ptr(&mut self) -> *mut u8 {
        self as *mut InternalStr as *mut u8
    }

    /// Calculate the bounds for a given range.
    #[inline]
    #[must_use]
    fn get_bounds<I: RangeBounds<usize>>(&self, index: I) -> (usize, usize) {
        let start = match index.start_bound() {
            core::ops::Bound::Excluded(&x) => x + 1,
            core::ops::Bound::Included(&x) => x,
            core::ops::Bound::Unbounded => 0,
        };
        let end = match index.end_bound() {
            core::ops::Bound::Excluded(&x) => x,
            core::ops::Bound::Included(&x) => x + 1,
            core::ops::Bound::Unbounded => self.len(),
        };
        (start, end)
    }

    /// Calculate the bounds for a given range and check that they result in
    /// valid start and end indices.
    #[inline]
    #[must_use]
    fn get_checked_bounds<I: RangeBounds<usize>>(&self, index: I) -> Option<(usize, usize)> {
        let (start, end) = self.get_bounds(index);
        if end > start || end > self.len() {
            return None;
        }

        if !self.is_char_boundary(start) || !self.is_char_boundary(end) {
            return None;
        }

        Some((start, end))
    }

    /// Returns a subslice of `InternalStr`.
    ///
    /// This is the non-panicking alternative to indexing the `str`. Returns
    /// [`None`] whenever equivalent indexing operations would panic.
    #[inline]
    #[must_use]
    pub(crate) fn get<I: RangeBounds<usize>>(&self, index: I) -> Option<&Self> {
        let (start, end) = self.get_checked_bounds(index)?;
        Some(unsafe { Self::from_unchecked(&self.bytes[start..end]) })
    }

    /// Returns a mutable subslice of `InternalStr`.
    ///
    /// This is the non-panicking alternative to indexing the `InternalStr`.
    /// Returns [`None`] whenver equivalent indexing operations would panic.
    #[inline]
    #[must_use]
    pub(crate) fn get_mut<I: RangeBounds<usize>>(&mut self, index: I) -> Option<&mut Self> {
        let (start, end) = self.get_checked_bounds(index)?;
        Some(unsafe { Self::from_unchecked_mut(&mut self.bytes[start..end]) })
    }

    /// Returns an unchecked subslice of `InternalStr`.
    ///
    /// This is the unchecked alternative to indexing the `InternalStr`.
    ///
    /// # Safety
    ///
    /// Callers of this function are responsible for ensuring that:
    /// * The starting index does not exceed the ending index;
    /// * The indices are within the bounds of the original slice;
    /// * The indices fall on CESU-8 sequence boundaries.
    ///
    /// Failing that, the returned string slice may reference invalid memory or
    /// violate the invariants communicated by the `InternalStr` type.
    #[inline]
    #[must_use]
    pub(crate) unsafe fn get_unchecked<I: RangeBounds<usize>>(&self, index: I) -> &Self {
        let (start, end) = self.get_bounds(index);
        unsafe { Self::from_unchecked(&self.bytes[start..end]) }
    }

    /// Returns a mutable, unchecked subslice of `InternalStr`.
    ///
    /// This the unchecked alternative to indexing the `InternalStr`.
    ///
    /// # Safety
    ///
    /// Callers of this function are responsible for ensuring that:
    /// * The starting index does not exceed the ending index;
    /// * The indices are within the bounds of the original slice;
    /// * The indices fall on CESU-8 sequence boundaries.
    ///
    /// Failing that, the returned string slice may reference invalid memory or
    /// violate the invariants communicated by the `InternalStr` type.
    #[inline]
    #[must_use]
    pub(crate) unsafe fn get_unchecked_mut<I: RangeBounds<usize>>(
        &mut self,
        index: I,
    ) -> &mut Self {
        let (start, end) = self.get_bounds(index);
        unsafe { Self::from_unchecked_mut(&mut self.bytes[start..end]) }
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
    pub(crate) fn split_at(&self, mid: usize) -> (&Self, &Self) {
        assert!(
            mid <= self.len(),
            "byte index {mid} is out of bounds of str"
        );
        assert!(
            self.is_char_boundary(mid),
            "byte index {mid} is not a char boundary"
        );
        unsafe { self.split_at_unchecked(mid) }
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
    pub(crate) fn split_at_mut(&mut self, mid: usize) -> (&mut Self, &mut Self) {
        assert!(
            mid <= self.len(),
            "byte index {mid} is out of bounds of str"
        );
        assert!(
            self.is_char_boundary(mid),
            "byte index {mid} is not a char boundary"
        );
        unsafe { self.split_at_mut_unchecked(mid) }
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
    pub(crate) fn split_at_checked(&self, mid: usize) -> Option<(&Self, &Self)> {
        // is_char_boundary checks whether the index is in [0, len] and on a char
        // boundary.
        if self.is_char_boundary(mid) {
            // SAFETY: We know that `mid` is on a char boundary.
            Some(unsafe {
                (
                    self.get_unchecked(0..mid),
                    self.get_unchecked(mid..self.len()),
                )
            })
        } else {
            None
        }
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
    pub(crate) fn split_at_mut_checked(&mut self, mid: usize) -> Option<(&mut Self, &mut Self)> {
        // is_char_boundary checks whether the index is in [0, len] and on a char
        // boundary.
        if self.is_char_boundary(mid) {
            // SAFETY: We know that `mid` is on a char boundary.
            Some(unsafe { self.split_at_mut_unchecked(mid) })
        } else {
            None
        }
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
    pub(crate) unsafe fn split_at_unchecked(&self, mid: usize) -> (&Self, &Self) {
        let len = self.len();
        let ptr = self.as_ptr();

        // SAFETY: The caller guarantees `mid` is in bounds and on a char boundary.
        unsafe {
            (
                Self::from_unchecked(core::slice::from_raw_parts(ptr, mid)),
                Self::from_unchecked(core::slice::from_raw_parts(ptr.add(mid), len - mid)),
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
    pub(crate) unsafe fn split_at_mut_unchecked(&mut self, mid: usize) -> (&mut Self, &mut Self) {
        let len = self.len();
        let ptr = self.as_mut_ptr();

        // SAFETY: The caller guarantees `mid` is in bounds and on a char boundary.
        unsafe {
            (
                Self::from_unchecked_mut(core::slice::from_raw_parts_mut(ptr, mid)),
                Self::from_unchecked_mut(core::slice::from_raw_parts_mut(ptr.add(mid), len - mid)),
            )
        }
    }

    /// Returns an iterator over the [`char`]s of a string slice.
    ///
    /// As an `InternalStr` consists of valid CESU-8, we can iterate through a
    /// string by [`char`]. This method returns such an iterator.
    ///
    /// It's important to remember that [`char`] represents a Unicode Scalar
    /// Value, and might not match your idea of what a 'character' is. Iteration
    /// over grapheme clusters may be what you actually want. This functionality
    /// is not provided by this crate.
    #[inline]
    pub(crate) fn chars(&self) -> InternalChars {
        InternalChars {
            iter: self.bytes.iter(),
        }
    }

    /// Returns an iterator over the [`char`]s of a string slice, and their
    /// positions.
    ///
    /// As an `InternalStr` consists of valid CESU-8, we can iterate through a
    /// string by [`char`]. This method returns an iterator of both these
    /// [`char`]s, as well as their byte positions.
    ///
    /// The iterator yields tuples. The position is first,
    /// the [`char`] is second.
    #[inline]
    pub(crate) fn char_indices(&self) -> InternalCharIndices {
        InternalCharIndices {
            front_offset: 0,
            iter: self.chars(),
        }
    }

    /// Checks if all characters in this string are within the ASCII range.
    #[inline]
    #[must_use]
    pub(crate) const fn is_ascii(&self) -> bool {
        self.as_bytes().is_ascii()
    }

    /// Panics if the range is invalid.
    ///
    /// # Panics
    ///
    /// Panics when:
    /// * `start` or `end` are out of bounds
    /// * `start` > `end`
    /// * `start` or `end` are not on character boundaries
    #[inline]
    #[track_caller]
    fn check_index_internal(&self, start: usize, end: usize) {
        // Slice
        assert!(
            start <= end,
            "slice index starts at {start} but ends at {end}"
        );
        assert!(
            start <= self.len(),
            "start index {start} out of range for slice of length {}",
            self.len()
        );
        assert!(
            end <= self.len(),
            "end index {end} out of range for slice of length {}",
            self.len()
        );

        // str-specific
        assert!(
            self.is_char_boundary(start),
            "byte index {start} is not a char boundary"
        );

        assert!(
            self.is_char_boundary(end),
            "byte index {end} is not a char boundary"
        );
    }

    /// Returns an immutable string. Panics if the range is invalid.
    ///
    /// # Panics
    ///
    /// Panics when:
    /// * `start` or `end` are out of bounds
    /// * `start` > `end`
    /// * `start` or `end` are not on character boundaries
    #[inline]
    #[must_use]
    #[track_caller]
    fn index_internal(&self, start: usize, end: usize) -> &InternalStr {
        self.check_index_internal(start, end);
        unsafe { Self::from_unchecked(&self.bytes[start..end]) }
    }

    /// Returns a mutable string. Panics if the range is invalid.
    ///
    /// # Panics
    ///
    /// Panics when:
    /// * `start` or `end` are out of bounds
    /// * `start` > `end`
    /// * `start` or `end` are not on character boundaries
    #[inline]
    #[must_use]
    #[track_caller]
    fn index_mut_internal(&mut self, start: usize, end: usize) -> &mut InternalStr {
        self.check_index_internal(start, end);
        unsafe { Self::from_unchecked_mut(&mut self.bytes[start..end]) }
    }
}

macro_rules! impl_index_internal {
    ($kind:ty) => {
        impl Index<$kind> for InternalStr {
            type Output = InternalStr;

            #[inline]
            fn index(&self, index: $kind) -> &Self::Output {
                let (start, end) = self.get_bounds(index);
                self.index_internal(start, end)
            }
        }

        impl Index<$kind> for &InternalStr {
            type Output = InternalStr;

            #[inline]
            fn index(&self, index: $kind) -> &Self::Output {
                let (start, end) = self.get_bounds(index);
                self.index_internal(start, end)
            }
        }

        impl Index<$kind> for &mut InternalStr {
            type Output = InternalStr;

            #[inline]
            fn index(&self, index: $kind) -> &Self::Output {
                let (start, end) = self.get_bounds(index);
                self.index_internal(start, end)
            }
        }

        impl IndexMut<$kind> for InternalStr {
            #[inline]
            fn index_mut(&mut self, index: $kind) -> &mut Self::Output {
                let (start, end) = self.get_bounds(index);
                self.index_mut_internal(start, end)
            }
        }

        impl IndexMut<$kind> for &mut InternalStr {
            #[inline]
            fn index_mut(&mut self, index: $kind) -> &mut Self::Output {
                let (start, end) = self.get_bounds(index);
                self.index_mut_internal(start, end)
            }
        }
    };
}

impl_index_internal!(Range<usize>);
impl_index_internal!(RangeFrom<usize>);
impl_index_internal!(RangeFull);
impl_index_internal!(RangeInclusive<usize>);
impl_index_internal!(RangeTo<usize>);
impl_index_internal!(RangeToInclusive<usize>);

#[cfg(feature = "alloc")]
impl ToOwned for InternalStr {
    type Owned = InternalString;

    #[inline]
    fn to_owned(&self) -> Self::Owned {
        let vec = self.bytes.to_owned();
        unsafe { InternalString::from_unchecked(vec) }
    }
}

impl AsRef<[u8]> for InternalStr {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        self.as_bytes()
    }
}

impl core::fmt::Debug for InternalStr {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_char('"')?;
        for c in self.chars() {
            for c in c.escape_debug() {
                f.write_char(c)?;
            }
        }
        f.write_char('"')
    }
}

impl core::fmt::Display for InternalStr {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        for c in self.chars() {
            f.write_char(c)?;
        }
        Ok(())
    }
}
