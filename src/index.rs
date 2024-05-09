use core::ops::{
    Index, IndexMut, Range, RangeFrom, RangeFull, RangeInclusive, RangeTo, RangeToInclusive,
};

use crate::cesu8::Cesu8Str;
use crate::java::JavaStr;

#[cfg(feature = "alloc")]
use crate::cesu8::Cesu8String;
#[cfg(feature = "alloc")]
use crate::java::JavaString;

macro_rules! impl_index {
    ($kind:ty, $str:ty, $string:ty) => {
        impl Index<$kind> for $str {
            type Output = $str;

            #[inline]
            fn index(&self, index: $kind) -> &Self::Output {
                let internal = self.internal.index(index);
                unsafe { <$str>::from_internal_unchecked(internal) }
            }
        }

        impl Index<$kind> for &$str {
            type Output = $str;

            #[inline]
            fn index(&self, index: $kind) -> &Self::Output {
                let internal = self.internal.index(index);
                unsafe { <$str>::from_internal_unchecked(internal) }
            }
        }

        impl Index<$kind> for &mut $str {
            type Output = $str;

            #[inline]
            fn index(&self, index: $kind) -> &Self::Output {
                let internal = self.internal.index(index);
                unsafe { <$str>::from_internal_unchecked(internal) }
            }
        }

        impl IndexMut<$kind> for $str {
            #[inline]
            fn index_mut(&mut self, index: $kind) -> &mut Self::Output {
                let internal = self.internal.index_mut(index);
                unsafe { <$str>::from_internal_unchecked_mut(internal) }
            }
        }

        impl IndexMut<$kind> for &mut $str {
            #[inline]
            fn index_mut(&mut self, index: $kind) -> &mut Self::Output {
                let internal = self.internal.index_mut(index);
                unsafe { <$str>::from_internal_unchecked_mut(internal) }
            }
        }

        #[cfg(feature = "alloc")]
        impl Index<$kind> for $string {
            type Output = $str;

            #[inline]
            fn index(&self, index: $kind) -> &Self::Output {
                self.as_str().index(index)
            }
        }

        #[cfg(feature = "alloc")]
        impl Index<$kind> for &$string {
            type Output = $str;

            #[inline]
            fn index(&self, index: $kind) -> &Self::Output {
                self.as_str().index(index)
            }
        }

        #[cfg(feature = "alloc")]
        impl Index<$kind> for &mut $string {
            type Output = $str;

            #[inline]
            fn index(&self, index: $kind) -> &Self::Output {
                self.as_str().index(index)
            }
        }

        #[cfg(feature = "alloc")]
        impl IndexMut<$kind> for $string {
            #[inline]
            fn index_mut(&mut self, index: $kind) -> &mut Self::Output {
                self.as_mut_str().index_mut(index)
            }
        }

        #[cfg(feature = "alloc")]
        impl IndexMut<$kind> for &mut $string {
            #[inline]
            fn index_mut(&mut self, index: $kind) -> &mut Self::Output {
                self.as_mut_str().index_mut(index)
            }
        }
    };
}

impl_index!(Range<usize>, Cesu8Str, Cesu8String);
impl_index!(RangeFrom<usize>, Cesu8Str, Cesu8String);
impl_index!(RangeFull, Cesu8Str, Cesu8String);
impl_index!(RangeInclusive<usize>, Cesu8Str, Cesu8String);
impl_index!(RangeTo<usize>, Cesu8Str, Cesu8String);
impl_index!(RangeToInclusive<usize>, Cesu8Str, Cesu8String);

impl_index!(Range<usize>, JavaStr, JavaString);
impl_index!(RangeFrom<usize>, JavaStr, JavaString);
impl_index!(RangeFull, JavaStr, JavaString);
impl_index!(RangeInclusive<usize>, JavaStr, JavaString);
impl_index!(RangeTo<usize>, JavaStr, JavaString);
impl_index!(RangeToInclusive<usize>, JavaStr, JavaString);
