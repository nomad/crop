use std::fmt::{self, Debug};
use std::ops::AddAssign;
use std::str;

use crate::tree::{Leaf, Summarize};

#[cfg(not(test))]
const TEXT_CHUNK_MAX_BYTES: usize = 1024;

#[cfg(test)]
const TEXT_CHUNK_MAX_BYTES: usize = 4;

// TODO: remove `Clone` impl
#[derive(Clone)]
pub(super) struct TextChunk {
    pub(super) text: String,
}

impl TextChunk {
    pub(super) const fn max_bytes() -> usize {
        TEXT_CHUNK_MAX_BYTES
    }
}

impl From<String> for TextChunk {
    #[inline]
    fn from(text: String) -> Self {
        debug_assert!(
            text.len() <= TEXT_CHUNK_MAX_BYTES
                || !text.is_char_boundary(TEXT_CHUNK_MAX_BYTES)
        );
        Self { text }
    }
}

impl Debug for TextChunk {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self.text)
    }
}

impl std::borrow::Borrow<TextSlice> for TextChunk {
    #[inline]
    fn borrow(&self) -> &TextSlice {
        (&*self.text).into()
    }
}

impl Summarize for TextChunk {
    type Summary = TextSummary;

    #[inline]
    fn summarize(&self) -> Self::Summary {
        TextSummary { bytes: self.text.len() }
    }
}

impl Leaf for TextChunk {
    type Slice = TextSlice;
}

#[derive(Debug)]
pub(super) struct TextSlice {
    pub(super) text: str,
}

impl From<&str> for &TextSlice {
    #[inline]
    fn from(text: &str) -> Self {
        // Safety: it's safe.
        unsafe { &*(text as *const str as *const TextSlice) }
    }
}

impl Summarize for TextSlice {
    type Summary = TextSummary;

    #[inline]
    fn summarize(&self) -> Self::Summary {
        TextSummary { bytes: self.text.len() }
    }
}

impl ToOwned for TextSlice {
    type Owned = TextChunk;

    #[inline]
    fn to_owned(&self) -> Self::Owned {
        TextChunk::from(self.text.to_owned())
    }
}

#[derive(Clone, Default, Debug)]
pub(super) struct TextSummary {
    pub(super) bytes: usize,
}

impl<'a> AddAssign<&'a Self> for TextSummary {
    fn add_assign(&mut self, rhs: &'a Self) {
        self.bytes += rhs.bytes;
    }
}

pub(super) struct TextChunkIter<'a> {
    str: &'a str,
}

impl<'a> TextChunkIter<'a> {
    pub(super) fn new(str: &'a str) -> Self {
        Self { str }
    }
}

impl<'a> Iterator for TextChunkIter<'a> {
    type Item = TextChunk;

    fn next(&mut self) -> Option<Self::Item> {
        match self.str.len() {
            0 => None,

            n if n >= TEXT_CHUNK_MAX_BYTES => {
                let mut bytes = TEXT_CHUNK_MAX_BYTES;

                while !self.str.is_char_boundary(bytes) {
                    bytes += 1;
                }

                let text = self.str[..bytes].to_owned();
                self.str = &self.str[bytes..];
                Some(TextChunk { text })
            },

            _ => {
                let text = self.str.to_owned();
                self.str = "";
                Some(TextChunk { text })
            },
        }
    }
}

impl<'a> ExactSizeIterator for TextChunkIter<'a> {
    fn len(&self) -> usize {
        2
    }
}
