//! A library implementing the [CESU-8 compatibility encoding scheme](https://www.unicode.org/reports/tr26/tr26-4.html).
//! This is a non-standard variant of UTF-8 that is used internally by some
//! systems that need to represent UTF-16 data as 8-bit characters.
//!
//! The use of this encoding is discouraged by the Unicode Consortium. It's OK
//! for working with existing APIs, but it should not be used for data
//! trasmission or storage.
//!
//! ### Java and U+0000
//!
//! Java uses the CESU-8 encoding as described above, but with one difference:
//! the null character U+0000 is represented as an overlong UTF-8 sequence `C0
//! 80`. This is supported by [`JavaStr`] and [`JavaString`].
//!
//! [`JavaStr`]: java::JavaStr
//! [`JavaString`]: java::JavaString
//!
//! ### Surrogate pairs and UTF-8
//!
//! The UTF-16 encoding uses "surrogate pairs" to represent Unicode code points
//! in the range from U+10000 to U+10FFFF. These are 16-bit numbers in the range
//! 0xD800 to 0xDFFF.
//!
//! CESU-8 encodes these surrogate pairs as a 6-byte seqence consisting of two
//! sets of three bytes.
//!
//! # Crate features
//!
//! **Alloc** - Enables all allocation related features. This will allow usage
//! of `Cesu8String` and `JavaString`, which offer a similiar API to the
//! standard library's `String`.
#![no_std]

#[cfg(feature = "alloc")]
extern crate alloc;

pub mod cesu8;
pub mod java;

mod index;
mod internal;

use core::num::NonZeroU8;

#[cfg(feature = "alloc")]
use alloc::borrow::Cow;
#[cfg(feature = "alloc")]
use alloc::string::String;

/// Errors which can occur when attempting to interpret a sequence of [`u8`] as
/// a string.
///
/// As such, the `from_slice` function for both [`Cesu8Str`] and [`JavaStr`]
/// make use of this error.
///
/// [`Cesu8Str`]: cesu8::Cesu8Str
/// [`JavaStr`]: java::JavaStr
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct EncodingError {
    error_len: Option<NonZeroU8>,
    valid_up_to: usize,
}

impl EncodingError {
    /// Returns the index in the given string up to which valid CESU-8 or Java
    /// CESU-8 was verified.
    ///
    /// It is the maximum index such that `from_slice` of either [`Cesu8Str`] or
    /// [`JavaStr`] would return `Ok(_)`.
    ///
    /// [`Cesu8Str`]: cesu8::Cesu8Str
    /// [`JavaStr`]: java::JavaStr
    #[inline]
    #[must_use]
    pub fn valid_up_to(&self) -> usize {
        self.valid_up_to
    }

    /// Provides more information about the failure:
    /// * `None`: the end of the input was reached unexpectedly.
    ///   `self.valid_up_to()` is 1 to 3 bytes from the end of the input. If a
    ///   byte stream (such as a file or network socket) is being decoded
    ///   incrementally, this could be a valid `char` whose UTF-8 byte sequence
    ///   is spanning multiple chunks.
    /// * `Some(len)`: an unexpected byte was encountered. The length provided
    ///   is that of the invalid byte seqence that starts at the index given by
    ///   `valid_up_to()`.
    #[inline]
    #[must_use]
    pub fn error_len(&self) -> Option<NonZeroU8> {
        self.error_len
    }
}

impl core::fmt::Display for EncodingError {
    #[inline]
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        if let Some(len) = self.error_len {
            write!(
                f,
                "invalid cesu-8 sequence of {} bytes from index {}",
                len, self.valid_up_to
            )
        } else {
            write!(
                f,
                "incomplete utf-8 byte sequence from index {}",
                self.valid_up_to
            )
        }
    }
}

/// A possible error value when converting a `JavaString` from a CESU-8 byte
/// vector.
///
/// This type is the error type for the [`from_cesu8`] and [`from_java_cesu8`]
/// on [`Cesu8String`] and [`JavaString`]. It is designed in such a way to
/// carefully avoid reallocations: the [`into_bytes`] method will give back the
/// byte vector that was used in the conversion attempt.
///
/// [`from_cesu8`]: cesu8::Cesu8String::from_cesu8
/// [`from_java_cesu8`]: java::JavaString::from_java_cesu8
/// [`Cesu8String`]: cesu8::Cesu8String
/// [`JavaString`]: java::JavaString
/// [`into_bytes`]: FromVecError::into_bytes
///
/// The [`EncodingError`] type represents an error that may occur when
/// converting a slice of [`u8`]s to either a [`&Cesu8Str`] or a [`&JavaStr`].
/// In this sense, it's an analogue to `FromCesu8Error`, and you can get one
/// from a `FromCesu8Error` through the [`encoding_error`] method.
///
/// [`&Cesu8Str`]: cesu8::Cesu8Str
/// [`&JavaStr`]: java::JavaStr
/// [`encoding_error`]: FromVecError::encoding_error
#[cfg(feature = "alloc")]
#[derive(Debug, PartialEq, Eq)]
pub struct FromVecError {
    bytes: alloc::vec::Vec<u8>,
    error: EncodingError,
}

#[cfg(feature = "alloc")]
impl FromVecError {
    /// Returns a slice of [`u8`]s that were attempted to convert to either a
    /// `Cesu8String` or a `JavaString`.
    #[inline]
    #[must_use]
    pub fn as_bytes(&self) -> &[u8] {
        &self.bytes
    }

    /// Returns the bytes that were attempted to convert to either a
    /// `Cesu8String` or a `JavaString`.
    ///
    /// This method is carefully constructed to avoid allocation. It will
    /// consume the error, moving out the bytes, so that a copy of the bytes
    /// does not need to be made.
    ///
    /// [`Cesu8Str`]: cesu8::Cesu8String
    /// [`JavaStr`]: java::JavaString
    #[inline]
    #[must_use]
    pub fn into_bytes(self) -> alloc::vec::Vec<u8> {
        self.bytes
    }

    /// Fetch a `EncodingError` to get more details about the conversion
    /// failure.
    ///
    /// The [`EncodingError`] type represents an error that may occur when
    /// converting a slice of [`u8`]s to either a [`Cesu8String`] or a
    /// [`JavaString`]. In this sense, it's an analogue to `FromCesu8Error`. See
    /// its documentation for more details on using it.
    ///
    /// [`Cesu8String`]: cesu8::Cesu8String
    /// [`JavaString`]: java::JavaString
    #[inline]
    #[must_use]
    pub const fn encoding_error(&self) -> EncodingError {
        self.error
    }
}

/// Converts bytes in CESU-8 format into UTF-8 format.
#[cfg(feature = "alloc")]
#[inline]
fn from_cesu8<const JAVA: bool>(str: &internal::InternalStr) -> Cow<'_, str> {
    let mut index = 0;
    let mut last_index = 0;
    let mut string = None;

    // Fast forward to next supplementary character
    let v = str.as_bytes();
    while let Some(&byte) = v.get(index) {
        // Check if byte marks the beginning of a supplementary character.
        if byte == 0b1110_1101 {
            let second = unsafe { *v.get(index + 1).unwrap_unchecked() };
            if second & 0b1111_0000 == 0b1010_0000 {
                let string = string.get_or_insert_with(String::new);
                unsafe { string.as_mut_vec().extend_from_slice(&v[last_index..index]) };

                let mut iter = v[index..].iter();
                let code_point = unsafe { next_code_point(&mut iter).unwrap_unchecked() };

                string.push(unsafe { char::from_u32_unchecked(code_point) });

                index += 6;
                last_index = index;
            } else {
                index += 3;
            }
        } else if JAVA && byte == 0xC0 {
            if let Some(0x80) = v.get(index + 1) {
                let string = string.get_or_insert_with(String::new);
                unsafe { string.as_mut_vec().extend_from_slice(&v[last_index..index]) };

                string.push('\0');

                index += 2;
                last_index = index;
            }
        } else {
            index += 1;
        }
    }

    if let Some(mut string) = string {
        unsafe { string.as_mut_vec().extend_from_slice(&v[last_index..index]) };
        Cow::Owned(string)
    } else {
        Cow::Borrowed(unsafe { core::str::from_utf8_unchecked(v) })
    }
}

/// Converts bytes in UTF-8 format into CESU-8 format.
#[cfg(feature = "alloc")]
#[inline]
fn from_utf8<const JAVA: bool>(str: &str) -> Cow<'_, internal::InternalStr> {
    let mut index = 0;
    let mut last_index = 0;
    let mut string = None;

    let v = str.as_bytes();
    while let Some(&byte) = v.get(index) {
        if byte & 0b1111_1000 == 0b1111_0000 {
            let string =
                string.get_or_insert_with(|| internal::InternalString::with_capacity(index + 6));

            unsafe {
                let c = core::str::from_utf8_unchecked(&v[index..])
                    .chars()
                    .next()
                    .unwrap_unchecked();

                let vec = string.as_mut_vec();
                vec.extend_from_slice(&v[last_index..index]);

                // Add character in CESU-8 encoding
                vec.extend_from_slice(encode_cesu8_raw::<JAVA>(c as u32, &mut [0; 6]));
            }

            index += 4;
            last_index = index;
        } else if JAVA && byte == 0 {
            let string =
                string.get_or_insert_with(|| internal::InternalString::with_capacity(index + 2));

            unsafe {
                let vec = string.as_mut_vec();
                vec.extend_from_slice(&v[last_index..index]);
                // Add nul character in Java CESU-8 encoding.
                vec.extend_from_slice(&[0xC0, 0x80]);
            }

            index += 1;
            last_index = index;
        } else {
            index += 1;
        }
    }

    if let Some(mut string) = string {
        unsafe { string.as_mut_vec().extend_from_slice(&v[last_index..index]) };
        Cow::Owned(string)
    } else {
        Cow::Borrowed(unsafe { internal::InternalStr::from_unchecked(v) })
    }
}

/// Checks whether a slice of bytes contains valid CESU-8 data. When passed
/// `check_java`, additionally ensure that the string conforms to the Java
/// String specification.
#[inline]
const fn validate_cesu8_internal<const CHECK_JAVA: bool>(v: &[u8]) -> Result<(), EncodingError> {
    const OVERLONG: [u32; 4] = [0x00, 0x80, 0x800, 0x10000];

    let mut index = 0;
    let len = v.len();

    while index < len {
        macro_rules! err {
            ($error_len:expr) => {
                return Err(EncodingError {
                    error_len: NonZeroU8::new($error_len),
                    valid_up_to: index,
                })
            };
        }

        // Check if the character is multi-byte.
        let first = v[index];
        let (len, code_point) = if first < 128 {
            // 1-byte characters - always ascii

            (1, first as u32)
        } else if first & 0b1110_0000 == 0b1100_0000 {
            // 2-byte characters
            if index + 1 >= len {
                err!(1);
            }
            let second = v[index + 1];
            if second & 0b1100_0000 != 0b1000_0000 {
                err!(2);
            }

            (2, ((first as u32 & 0x1F) << 6) | (second as u32 & 0x3F))
        } else if first & 0b1111_0000 == 0b1110_0000 {
            // 3-byte characters
            if index + 2 >= len {
                err!(1);
            }

            let second = v[index + 1];
            let third = v[index + 2];
            // This is safe, even though the three-byte encoding seems like it supports
            // values overlapping this range. This is because any value that would end up in
            // this range and yet be encoded in three-bytes is an unpaired supplementary
            // character, which is not a valid Unicode character.
            if !(first == 0b1110_1101 && second & 0b1111_0000 == 0b1010_0000) {
                // No surrogate pair
                if second & 0b1100_0000 != 0b1000_0000 {
                    err!(2);
                }
                if third & 0b1100_0000 != 0b1000_0000 {
                    err!(3);
                }

                (
                    3,
                    ((first as u32 & 0x0F) << 12)
                        | ((second as u32 & 0x3F) << 6)
                        | (third as u32 & 0x3F),
                )
            } else {
                // Surrogate pair
                if index + 5 >= len {
                    err!(1);
                }
                let fourth = v[index + 3];
                let fifth = v[index + 4];
                let sixth = v[index + 5];

                if second & 0b1111_0000 != 0b1010_0000 {
                    err!(2);
                }
                if third & 0b1100_0000 != 0b1000_0000 {
                    err!(3);
                }

                if fourth != 0b1110_1101 {
                    err!(4);
                }
                if fifth & 0b1111_0000 != 0b1011_0000 {
                    err!(5);
                }
                if sixth & 0b1100_0000 != 0b1000_0000 {
                    err!(6);
                }

                (
                    6,
                    0x10000
                        + (((second as u32 & 0x0F) << 16)
                            | ((third as u32 & 0x3F) << 10)
                            | ((fifth as u32 & 0x0F) << 6)
                            | (sixth as u32 & 0x3F)),
                )
            }
        } else {
            err!(1);
        };

        if code_point > 0x10FFFF {
            err!(len as u8);
        }

        let idx = if len != 6 { len - 1 } else { 3 };

        // Check for overlong encoding, and if validating Java CESU-8, exclude
        let overlong = if CHECK_JAVA && code_point == 0x00 {
            len != 2
        } else {
            code_point < OVERLONG[idx]
        };

        let surrogate = (code_point >> 11) == 0x1B;
        if overlong || surrogate {
            err!(len as u8);
        }

        index += len;
    }

    Ok(())
}

/// Reads the next code point out of a byte iterator (assuming a CESU-8-like
/// encoding).
///
/// This method can be used for both standard CESU-8 and Java CESU-8 because
/// this method does not care about what is encoded inside the code-points, and
/// Java CESU-8 only adds additional stipulations regarding how to encode the
/// NUL character.
///
/// # Safety
///
/// The byte iterator passed in must provide CESU-8.
#[allow(clippy::cast_lossless)]
#[inline]
unsafe fn next_code_point<'a, I: Iterator<Item = &'a u8>>(bytes: &mut I) -> Option<u32> {
    let first = *bytes.next()?;
    if first < 128 {
        // 1-byte characters
        Some(first as u32)
    } else if first & 0b1110_0000 == 0b1100_0000 {
        // 2-byte characters
        let second = *bytes.next().unwrap_unchecked();
        Some(((first as u32 & 0x1F) << 6) | (second as u32 & 0x3F))
    } else {
        let second = *bytes.next().unwrap_unchecked();
        let third = *bytes.next().unwrap_unchecked();

        // This is safe, even though the three-byte encoding seems like it supports
        // values overlapping this range. This is because any value that would end up in
        // this range and yet be encoded in three-bytes is an unpaired supplementary
        // character, which is not a valid Unicode character.
        if first != 0b1110_1101 || second & 0b1111_0000 != 0b1010_0000 {
            // 3-byte characters - no surrogate pair
            Some(
                ((first as u32 & 0x0F) << 12)
                    | ((second as u32 & 0x3F) << 6)
                    | (third as u32 & 0x3F),
            )
        } else {
            // 6-byte characters - surrogate pair
            let _fourth = *bytes.next().unwrap_unchecked();
            let fifth = *bytes.next().unwrap_unchecked();
            let sixth = *bytes.next().unwrap_unchecked();

            Some(
                0x10000
                    + (((second as u32 & 0x0F) << 16)
                        | ((third as u32 & 0x3F) << 10)
                        | ((fifth as u32 & 0x0F) << 6)
                        | (sixth as u32 & 0x3F)),
            )
        }
    }
}

/// Reads the next code point of a reversed byte iterator (assuming a
/// CESU-8-like encoding).
///
/// This method can be used for both standard CESU-8 and Java CESU-8 because
/// this method does not care about what is encoded inside the code-points, and
/// Java CESU-8 only adds additional stipulations regarding how to encode the
/// NUL character.
///
/// # Safety
///
/// The byte iterator passed in must provide CESU-8.
#[allow(clippy::cast_lossless)]
#[inline]
unsafe fn next_code_point_reverse<'a, I: DoubleEndedIterator<Item = &'a u8>>(
    bytes: &mut I,
) -> Option<u32> {
    let first = *bytes.next_back()?;
    if first < 128 {
        // 1-byte characters
        Some(first as u32)
    } else {
        // Multi-byte characters
        let second = *bytes.next_back().unwrap_unchecked();
        if second & 0b1110_0000 == 0b1100_0000 {
            // 2-byte characters
            Some(((second as u32 & 0x1F) << 6) | (first as u32 & 0x3F))
        } else {
            let third = *bytes.next_back().unwrap_unchecked();
            if second & 0b1111_0000 != 0b1011_0000 || third != 0b1110_1101 {
                // 3-byte characters - no surrogate pair
                Some(
                    ((third as u32 & 0x0F) << 12)
                        | ((second as u32 & 0x3F) << 6)
                        | (first as u32 & 0x3F),
                )
            } else {
                // 6-byte characters - surrogate pair
                let fourth = *bytes.next_back().unwrap_unchecked();
                let fifth = *bytes.next_back().unwrap_unchecked();
                let _sixth = *bytes.next_back().unwrap_unchecked();

                Some(
                    0x10000
                        + (((fifth as u32 & 0x0F) << 16)
                            | ((fourth as u32 & 0x3F) << 10)
                            | ((second as u32 & 0x0F) << 6)
                            | (first as u32 & 0x3F)),
                )
            }
        }
    }
}

/// Compute the length of a character when encoded in the CESU-8 format.
#[inline]
#[must_use]
pub(crate) const fn len_cesu8<const JAVA: bool>(code: u32) -> usize {
    if code < 0x80 && !(JAVA && code == 0) {
        1
    } else if code < 0x800 {
        2
    } else if code < 0x10000 {
        3
    } else {
        6
    }
}

/// Encodes a raw u32 value as CESU-8 into the provided byte buffer, then
/// returns the subslice of the buffer that contains the encoded character.
#[inline]
pub(crate) fn encode_cesu8_raw<const JAVA: bool>(code: u32, dst: &mut [u8]) -> &mut [u8] {
    let len = len_cesu8::<JAVA>(code);
    match (len, &mut dst[..]) {
        (1, [a, ..]) => *a = code as u8,
        (2, [a, b, ..]) => {
            *a = 0b1100_0000 | (code >> 6 & 0x1F) as u8;
            *b = 0b1000_0000 | (code & 0x3F) as u8;
        }
        (3, [a, b, c, ..]) => {
            *a = 0b1110_0000 | (code >> 12 & 0x0F) as u8;
            *b = 0b1000_0000 | (code >> 6 & 0x3F) as u8;
            *c = 0b1000_0000 | (code & 0x3F) as u8;
        }
        (6, [a, b, c, d, e, f, ..]) => {
            *a = 0b1110_1101;
            *b = 0b1010_0000 | ((code - 0x1_0000) >> 16 & 0x0F) as u8;
            *c = 0b1000_0000 | (code >> 10 & 0x3F) as u8;
            *d = 0b1110_1101;
            *e = 0b1011_0000 | (code >> 6 & 0x0F) as u8;
            *f = 0b1000_0000 | (code & 0x3F) as u8;
        }
        _ => panic!(
            "encode_cesu8: need {len} bytes to encode U+{code:X}, but the buffer has {}",
            dst.len()
        ),
    };
    &mut dst[..len]
}
