mod iter;
mod str;

#[cfg(feature = "alloc")]
mod string;

pub use iter::{Cesu8CharIndices, Cesu8Chars};
pub use str::Cesu8Str;

#[cfg(feature = "alloc")]
pub use string::Cesu8String;

#[cfg(feature = "alloc")]
use alloc::borrow::Cow;

/// Computes the length of a character when encoded in the CESU-8 format.
#[inline]
#[must_use]
pub const fn len_cesu8(c: char) -> usize {
    super::len_cesu8::<false>(c as u32)
}

/// Encodes a character as CESU-8 into the provided byte buffer, then returns
/// the subslice of the buffer that contains the encoded character.
#[inline]
pub fn encode_cesu8(c: char, dst: &mut [u8]) -> &mut [u8] {
    super::encode_cesu8_raw::<false>(c as u32, dst)
}

/// Converts a `Cesu8Str` into a `str`. We avoid copying unless necessary. In
/// the case where there are no surrogate pairs, then no allocation will happen.
///
/// It is theoretically possible to convert a `Cesu8Str` into a UTF-8 string
/// without allocation in any case, as the length of a CESU-8 string is always
/// greater than or equal to the length of a UTF-8 string. This library does not
/// currently provide this option.
#[cfg(feature = "alloc")]
#[inline]
#[must_use]
pub fn from_cesu8(str: &Cesu8Str) -> Cow<'_, str> {
    super::from_cesu8::<false>(&str.internal)
}

/// Converts a `str` into a `Cesu8Str`. We avoid copying unless necessary. In
/// the case where there are no four-byte encodings, then no allocation will
/// happen.
#[cfg(feature = "alloc")]
#[inline]
#[must_use]
pub fn from_utf8(str: &str) -> Cow<'_, Cesu8Str> {
    match super::from_utf8::<true>(str) {
        Cow::Owned(string) => Cow::Owned(unsafe { Cesu8String::from_internal_unchecked(string) }),
        Cow::Borrowed(str) => Cow::Borrowed(unsafe { Cesu8Str::from_internal_unchecked(str) }),
    }
}

pub mod macros {
    /// Builds a `CesuStr` literal at compile time from a string literal.
    #[macro_export]
    macro_rules! cesu8_str {
        ($str:tt) => {{
            const _CESU8_STR_MACRO_STR: &str = $str;
            const _CESU8_STR_MACRO_LEN: usize =
                $crate::cesu8::macros::required_cesu8_len(_CESU8_STR_MACRO_STR);
            const _CESU8_STR_MACRO_BUF: [u8; _CESU8_STR_MACRO_LEN] =
                $crate::cesu8::macros::create_cesu8_array(_CESU8_STR_MACRO_STR);
            unsafe { $crate::cesu8::Cesu8Str::from_cesu8_unchecked(&_CESU8_STR_MACRO_BUF) }
        }};
    }

    /// Calculate the amount of bytes required to encode `str` in CESU-8.
    #[inline]
    #[must_use]
    pub const fn required_cesu8_len(str: &str) -> usize {
        crate::required_len::<false>(str)
    }

    /// Creates a buffer of CESU-8 encoded bytes from `str`.
    #[inline]
    #[must_use]
    pub const fn create_cesu8_array<const N: usize>(str: &str) -> [u8; N] {
        crate::create_array::<false, N>(str)
    }
}

#[cfg(test)]
mod tests {
    use crate::validate_cesu8_internal;

    use super::encode_cesu8;

    #[test]
    fn valid_roundtrip() {
        let mut buf = [0; 6];
        for i in 0..u32::MAX {
            if let Some(c) = char::from_u32(i) {
                let check = encode_cesu8(c, &mut buf);
                validate_cesu8_internal::<false>(check).unwrap();
            }
        }
    }
}
