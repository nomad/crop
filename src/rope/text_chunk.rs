use std::fmt;
use std::ops::AddAssign;
use std::str;

use crate::tree::Summarize;

#[cfg(not(test))]
const TEXT_CHUNK_MAX_BYTES: usize = 1024;

#[cfg(test)]
const TEXT_CHUNK_MAX_BYTES: usize = 4;

pub(super) struct TextChunk {
    text: Vec<u8>,
}

impl fmt::Debug for TextChunk {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // Yes, this is not actually safe right now.
        write!(f, "{:?}", unsafe { str::from_utf8_unchecked(&self.text) })
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

impl Summarize for TextChunk {
    type Summary = TextSummary;

    fn summarize(&self) -> Self::Summary {
        TextSummary { bytes: self.text.len() }
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
                let bytes =
                    self.str[..TEXT_CHUNK_MAX_BYTES].as_bytes().to_owned();
                self.str = &self.str[TEXT_CHUNK_MAX_BYTES..];
                Some(TextChunk { text: bytes })
            },

            _ => {
                let bytes = self.str.as_bytes().to_owned();
                self.str = "";
                Some(TextChunk { text: bytes })
            },
        }
    }
}

impl<'a> ExactSizeIterator for TextChunkIter<'a> {
    fn len(&self) -> usize {
        2
    }
}
