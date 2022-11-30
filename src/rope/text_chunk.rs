use std::fmt::{self, Debug};
use std::ops::AddAssign;
use std::str;

use crate::tree::{Leaf, Summarize};

#[cfg(not(test))]
const TEXT_CHUNK_MAX_BYTES: usize = 1024;

#[cfg(test)]
const TEXT_CHUNK_MAX_BYTES: usize = 4;

#[derive(Default)]
pub(super) struct TextChunk {
    text: String,
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
    #[inline]
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
        TextSummary {
            bytes: self.text.len(),
            line_breaks: str_indices::lines_lf::count_breaks(&self.text),
        }
    }
}

impl Leaf for TextChunk {
    type Slice = TextSlice;
}

#[derive(Debug, PartialEq)]
pub(super) struct TextSlice {
    text: str,
}

impl From<&str> for &TextSlice {
    #[inline]
    fn from(text: &str) -> Self {
        // Safety: it's safe.
        unsafe { &*(text as *const str as *const TextSlice) }
    }
}

impl std::ops::Deref for TextSlice {
    type Target = str;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.text
    }
}

impl Summarize for TextSlice {
    type Summary = TextSummary;

    #[inline]
    fn summarize(&self) -> Self::Summary {
        TextSummary {
            bytes: self.text.len(),
            line_breaks: str_indices::lines_lf::count_breaks(&self.text),
        }
    }
}

impl ToOwned for TextSlice {
    type Owned = TextChunk;

    #[inline]
    fn to_owned(&self) -> Self::Owned {
        TextChunk::from(self.text.to_owned())
    }
}

#[derive(Copy, Clone, Default, Debug, PartialEq)]
pub(super) struct TextSummary {
    pub(super) bytes: usize,
    pub(super) line_breaks: usize,
}

impl<'a> AddAssign<&'a Self> for TextSummary {
    #[inline]
    fn add_assign(&mut self, rhs: &'a Self) {
        self.bytes += rhs.bytes;
        self.line_breaks += rhs.line_breaks;
    }
}

pub(super) struct TextChunkIter<'a> {
    str: &'a str,
}

impl<'a> TextChunkIter<'a> {
    #[inline]
    pub(super) fn new(str: &'a str) -> Self {
        Self { str }
    }
}

impl<'a> Iterator for TextChunkIter<'a> {
    type Item = TextChunk;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        match self.str.len() {
            0 => None,

            n if n >= TEXT_CHUNK_MAX_BYTES => {
                let mut bytes = TEXT_CHUNK_MAX_BYTES;

                while !self.str.is_char_boundary(bytes) {
                    bytes += 1;
                }

                // Increase by one more byte if we'd be splitting a `\r\n`
                // pair.
                if (self.str.as_bytes()[bytes - 1] == b'\r')
                    && (self.str.len() > bytes + 1)
                    && (self.str.as_bytes()[bytes] == b'\n')
                {
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
    #[inline]
    fn len(&self) -> usize {
        if self.str.len() > TEXT_CHUNK_MAX_BYTES {
            2
        } else {
            1
        }
    }
}
