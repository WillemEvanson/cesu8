mod iter;
mod str;
mod string;

pub(crate) use iter::{InternalCharIndices, InternalChars};
pub(crate) use str::InternalStr;

#[cfg(feature = "alloc")]
pub(crate) use string::InternalString;
