use core::iter::FusedIterator;

use crate::{next_code_point, next_code_point_reverse};

/// An iterator over the [`char`]s of a CESU-8 string slice.
///
/// This iterator works for both [`Cesu8Str`] and [`JavaStr`] because they use
/// the same underlying format, however Java strings have more validation
/// requirements.
///
/// This struct is created by the `chars` method on either the `Cesu8Str` or
/// `JavaStr`. See its documentation for more detail.
#[derive(Clone)]
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub(crate) struct InternalChars<'a> {
    pub(crate) iter: core::slice::Iter<'a, u8>,
}

impl<'a> InternalChars<'a> {
    /// Returns the underlying bytes of the iterated string. These bytes will be
    /// in a valid format and will always start on a character boundary.
    #[inline]
    #[must_use]
    pub fn as_bytes(&self) -> &[u8] {
        self.iter.as_slice()
    }
}

impl Iterator for InternalChars<'_> {
    type Item = char;

    #[inline]
    #[must_use]
    fn next(&mut self) -> Option<Self::Item> {
        unsafe { next_code_point(&mut self.iter).map(|c| char::from_u32_unchecked(c)) }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.iter.len();
        // `(len + 5` can't overflow, because we know that
        // `slice::Iter` belongs to a slice in memory which has a
        // maximum length of `isize::MAX` (which is well below
        // `usize::MAX`).
        ((len + 5) / 6, Some(len))
    }

    #[inline]
    fn last(mut self) -> Option<char> {
        self.next_back()
    }
}

impl DoubleEndedIterator for InternalChars<'_> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        unsafe { next_code_point_reverse(&mut self.iter).map(|c| char::from_u32_unchecked(c)) }
    }
}

impl FusedIterator for InternalChars<'_> {}

impl core::fmt::Debug for InternalChars<'_> {
    #[inline]
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "Chars(")?;
        f.debug_list().entries(self.clone()).finish()?;
        write!(f, ")")?;
        Ok(())
    }
}

/// An iterator over the [`char`]s of a CESU-8 string slice,
/// and their positions.
///
/// This struct is created by the `char_indices` method on
/// either the `Cesu8Str` or `JavaStr`. See its
/// documentation for more detail.
#[must_use]
#[derive(Debug, Clone)]
pub(crate) struct InternalCharIndices<'a> {
    pub(crate) front_offset: usize,
    pub(crate) iter: InternalChars<'a>,
}

impl<'a> InternalCharIndices<'a> {
    /// Returns the byte position of the next character, or
    /// the length of the underlying string if there are no
    /// more characters.
    #[inline]
    #[must_use]
    pub(crate) fn offset(&self) -> usize {
        self.front_offset
    }

    /// Returns the underlying bytes of the iterated string. These bytes will be
    /// in a valid format and will always start on a character boundary.
    #[inline]
    #[must_use]
    pub(crate) fn as_bytes(&self) -> &[u8] {
        self.iter.as_bytes()
    }
}

impl Iterator for InternalCharIndices<'_> {
    type Item = (usize, char);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let pre_len = self.iter.iter.len();
        match self.iter.next() {
            None => None,
            Some(ch) => {
                let index = self.front_offset;
                let len = self.iter.iter.len();
                self.front_offset += pre_len - len;
                Some((index, ch))
            }
        }
    }

    #[inline]
    fn count(self) -> usize {
        self.iter.count()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }

    #[inline]
    fn last(mut self) -> Option<Self::Item> {
        self.next_back()
    }
}

impl DoubleEndedIterator for InternalCharIndices<'_> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.iter.next_back().map(|c| {
            let index = self.front_offset + self.iter.iter.len();
            (index, c)
        })
    }
}

impl FusedIterator for InternalCharIndices<'_> {}
