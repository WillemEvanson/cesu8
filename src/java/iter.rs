use core::iter::FusedIterator;

use crate::internal::{InternalCharIndices, InternalChars};

use super::JavaStr;

/// An iterator over the [`char`]s of a Java CESU-8 string slice.
///
/// This struct is created by the `chars` method on the `JavaStr`. See its
/// documentation for more detail.
///
/// [`chars`]: JavaStr::chars
#[derive(Debug, Clone)]
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct JavaChars<'a> {
    pub(crate) iter: InternalChars<'a>,
}

impl<'a> JavaChars<'a> {
    /// Views the underlying string as a subslice of the original string.
    #[inline]
    #[must_use]
    pub fn as_str(&self) -> &JavaStr {
        // SAFETY: The bytes come from a JavaStr, so they must be in a valid format.
        unsafe { JavaStr::from_java_cesu8_unchecked(self.iter.as_bytes()) }
    }
}

impl Iterator for JavaChars<'_> {
    type Item = char;

    #[inline]
    #[must_use]
    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }

    #[inline]
    fn last(self) -> Option<char> {
        self.iter.last()
    }
}

impl DoubleEndedIterator for JavaChars<'_> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.iter.next_back()
    }
}

impl FusedIterator for JavaChars<'_> {}

/// An iterator over the [`char`]s of a Java CESU-8 string slice, and their
/// positions.
///
/// This struct is created by the `char_indices` method on a `JavaStr`. See its
/// documentation for more detail.
#[derive(Debug, Clone)]
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct JavaCharIndices<'a> {
    pub(crate) iter: InternalCharIndices<'a>,
}

impl<'a> JavaCharIndices<'a> {
    /// Returns the byte position of the next character, or
    /// the length of the underlying string if there are no
    /// more characters.
    #[inline]
    #[must_use]
    pub fn offset(&self) -> usize {
        self.iter.offset()
    }

    /// Views the underlying string as a subslice of the original string.
    #[inline]
    #[must_use]
    pub fn as_str(&self) -> &JavaStr {
        // SAFETY: The bytes come from a JavaStr, so they must be in a valid format.
        unsafe { JavaStr::from_java_cesu8_unchecked(self.iter.as_bytes()) }
    }
}

impl Iterator for JavaCharIndices<'_> {
    type Item = (usize, char);

    #[inline]
    fn next(&mut self) -> Option<(usize, char)> {
        self.iter.next()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }

    #[inline]
    fn last(self) -> Option<Self::Item> {
        self.iter.last()
    }
}

impl DoubleEndedIterator for JavaCharIndices<'_> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.iter.next_back()
    }
}

impl FusedIterator for JavaCharIndices<'_> {}
