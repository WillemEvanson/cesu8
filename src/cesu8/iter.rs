use core::iter::FusedIterator;

use crate::internal::{InternalCharIndices, InternalChars};

use super::Cesu8Str;

/// An iterator over the [`char`]s of a CESU-8 string slice.
///
/// This struct is created by the `chars` method on the `Cesu8Str`. See its
/// documentation for more detail.
///
/// [`chars`]: Cesu8Str::chars
#[derive(Debug, Clone)]
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct Cesu8Chars<'a> {
    pub(crate) iter: InternalChars<'a>,
}

impl<'a> Cesu8Chars<'a> {
    /// Views the underlying string as a subslice of the original string.
    #[inline]
    #[must_use]
    pub fn as_str(&self) -> &Cesu8Str {
        // SAFETY: The bytes come from a Cesu8Str, so they must be in a valid format.
        unsafe { Cesu8Str::from_cesu8_unchecked(self.iter.as_bytes()) }
    }
}

impl Iterator for Cesu8Chars<'_> {
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

impl DoubleEndedIterator for Cesu8Chars<'_> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.iter.next_back()
    }
}

impl FusedIterator for Cesu8Chars<'_> {}

/// An iterator over the [`char`]s of a CESU-8 string slice,
/// and their positions.
///
/// This struct is created by the `char_indices` method on a `Cesu8Str`. See its
/// documentation for more detail.
#[derive(Debug, Clone)]
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct Cesu8CharIndices<'a> {
    pub(crate) iter: InternalCharIndices<'a>,
}

impl<'a> Cesu8CharIndices<'a> {
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
    pub fn as_str(&self) -> &Cesu8Str {
        // SAFETY: The bytes come from a Cesu8Str, so they must be in a valid format.
        unsafe { Cesu8Str::from_cesu8_unchecked(self.iter.as_bytes()) }
    }
}

impl Iterator for Cesu8CharIndices<'_> {
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

impl DoubleEndedIterator for Cesu8CharIndices<'_> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.iter.next_back()
    }
}

impl FusedIterator for Cesu8CharIndices<'_> {}
