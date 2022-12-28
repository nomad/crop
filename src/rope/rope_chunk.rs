use std::fmt::{self, Debug};
use std::ops::AddAssign;
use std::str;

use super::metrics::ByteMetric;
use crate::tree::{Leaf, Summarize};

#[cfg(all(not(test), not(feature = "integration_tests")))]
const ROPE_CHUNK_MAX_BYTES: usize = 1024;

#[cfg(any(test, feature = "integration_tests"))]
const ROPE_CHUNK_MAX_BYTES: usize = 4;

const ROPE_CHUNK_MIN_BYTES: usize = ROPE_CHUNK_MAX_BYTES / 2;

#[derive(Clone)]
pub(super) struct RopeChunk {
    pub(super) text: String,
}

impl Default for RopeChunk {
    #[inline]
    fn default() -> Self {
        Self { text: String::with_capacity(Self::max_bytes() + 3) }
    }
}

impl RopeChunk {
    pub(super) const fn max_bytes() -> usize {
        ROPE_CHUNK_MAX_BYTES
    }

    pub(super) const fn min_bytes() -> usize {
        ROPE_CHUNK_MIN_BYTES
    }
}

impl Debug for RopeChunk {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self.text)
    }
}

impl std::borrow::Borrow<ChunkSlice> for RopeChunk {
    #[inline]
    fn borrow(&self) -> &ChunkSlice {
        (&*self.text).into()
    }
}

impl std::ops::Deref for RopeChunk {
    type Target = String;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.text
    }
}

impl std::ops::DerefMut for RopeChunk {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.text
    }
}

impl Summarize for RopeChunk {
    type Summary = ChunkSummary;

    #[inline]
    fn summarize(&self) -> Self::Summary {
        ChunkSummary {
            bytes: self.text.len(),
            line_breaks: str_indices::lines_lf::count_breaks(&self.text),
        }
    }
}

impl Leaf for RopeChunk {
    const MIN_LEAF_SIZE: ByteMetric = ByteMetric(RopeChunk::min_bytes());
    type BaseMetric = ByteMetric;
    type Slice = ChunkSlice;
}

#[derive(Debug, PartialEq)]
pub(super) struct ChunkSlice {
    text: str,
}

impl Default for &ChunkSlice {
    #[inline]
    fn default() -> Self {
        "".into()
    }
}

impl From<&str> for &ChunkSlice {
    #[inline]
    fn from(text: &str) -> Self {
        // Safety: it's safe.
        unsafe { &*(text as *const str as *const ChunkSlice) }
    }
}

impl std::ops::Deref for ChunkSlice {
    type Target = str;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.text
    }
}

impl Summarize for ChunkSlice {
    type Summary = ChunkSummary;

    #[inline]
    fn summarize(&self) -> Self::Summary {
        ChunkSummary {
            bytes: self.text.len(),
            line_breaks: str_indices::lines_lf::count_breaks(&self.text),
        }
    }
}

impl ToOwned for ChunkSlice {
    type Owned = RopeChunk;

    #[inline]
    fn to_owned(&self) -> Self::Owned {
        RopeChunk { text: self.text.to_owned() }
    }
}

#[derive(Copy, Clone, Default, Debug, PartialEq)]
pub(super) struct ChunkSummary {
    pub(super) bytes: usize,
    pub(super) line_breaks: usize,
}

impl<'a> AddAssign<&'a Self> for ChunkSummary {
    #[inline]
    fn add_assign(&mut self, rhs: &'a Self) {
        self.bytes += rhs.bytes;
        self.line_breaks += rhs.line_breaks;
    }
}

pub(super) struct RopeChunkIter<'a> {
    str: &'a str,
}

impl<'a> RopeChunkIter<'a> {
    #[inline]
    pub(super) fn new(str: &'a str) -> Self {
        Self { str }
    }
}

impl<'a> Iterator for RopeChunkIter<'a> {
    type Item = RopeChunk;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        match self.str.len() {
            0 => None,

            n if n >= ROPE_CHUNK_MAX_BYTES => {
                let mut bytes = ROPE_CHUNK_MAX_BYTES;

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
                Some(RopeChunk { text })
            },

            _ => {
                let text = self.str.to_owned();
                self.str = "";
                Some(RopeChunk { text })
            },
        }
    }
}

impl<'a> ExactSizeIterator for RopeChunkIter<'a> {
    #[inline]
    fn len(&self) -> usize {
        if self.str.len() > ROPE_CHUNK_MAX_BYTES {
            2
        } else {
            1
        }
    }
}
