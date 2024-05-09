mod iter;
mod str;
mod string;

pub use iter::{JavaCharIndices, JavaChars};
pub use str::JavaStr;

#[cfg(feature = "alloc")]
pub use string::JavaString;

#[cfg(feature = "alloc")]
use alloc::borrow::Cow;

/// Computes the length of a character when encoded in the Java CESU-8 format.
#[inline]
#[must_use]
pub const fn len_java(c: char) -> usize {
    super::len_cesu8::<true>(c as u32)
}

/// Encodes a character as Java CESU-8 into the provided byte buffer, then
/// returns the subslice of the buffer that contains the encoded character.
#[inline]
pub fn encode_java(c: char, dst: &mut [u8]) -> &mut [u8] {
    super::encode_cesu8_raw::<true>(c as u32, dst)
}

/// Encodes a

/// Converts a `JavaStr` into a `str`. We avoid copying unless necessary. In
/// the case where there are no surrogate pairs, then no allocation will happen.
///
/// It is theoretically possible to convert a `JavaStr` into a UTF-8 string
/// without allocation in any case, as the length of a Java CESU-8 string is
/// always greater than or equal to the length of a UTF-8 string. This library
/// does not currently provide this option.
#[cfg(feature = "alloc")]
#[inline]
#[must_use]
pub fn from_java_cesu8(str: &JavaStr) -> Cow<'_, str> {
    unsafe { super::from_cesu8::<true>(&str.internal) }
}

/// Converts a `str` into a `JavaStr`. We avoid copying unless necessary. In
/// the case where there are no four-byte encodings, then no allocation will
/// happen.
#[cfg(feature = "alloc")]
#[inline]
#[must_use]
pub fn from_utf8(str: &str) -> Cow<'_, JavaStr> {
    unsafe { core::mem::transmute(super::from_utf8::<true>(str)) }
}
