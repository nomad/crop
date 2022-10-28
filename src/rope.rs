use std::fmt;
use std::ops::AddAssign;
use std::str;

use crate::{Summarize, Tree};

const ROPE_FANOUT: usize = 8;

#[cfg(not(test))]
const TEXT_CHUNK_MAX_BYTES: usize = 1024;

#[cfg(test)]
const TEXT_CHUNK_MAX_BYTES: usize = 4;

struct TextChunk {
    text: Vec<u8>,
}

impl fmt::Debug for TextChunk {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // Yes, this is not actually safe right now.
        write!(f, "{:?}", unsafe { str::from_utf8_unchecked(&self.text) })
    }
}

#[derive(Clone, Default, Debug)]
struct TextSummary {
    byte_len: usize,
}

impl<'a> AddAssign<&'a Self> for TextSummary {
    fn add_assign(&mut self, rhs: &'a Self) {
        self.byte_len += rhs.byte_len;
    }
}

impl Summarize for TextChunk {
    type Summary = TextSummary;

    fn summarize(&self) -> Self::Summary {
        TextSummary { byte_len: self.text.len() }
    }
}

struct TextChunkIter<'a> {
    str: &'a str,
}

impl<'a> TextChunkIter<'a> {
    fn new(str: &'a str) -> Self {
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

#[derive(Debug)]
pub struct Rope {
    root: Tree<ROPE_FANOUT, TextChunk>,
}

impl Rope {
    pub fn byte_len(&self) -> usize {
        self.root.summarize().byte_len
    }

    #[allow(clippy::should_implement_trait)]
    pub fn from_str(text: &str) -> Self {
        Rope { root: Tree::from_leaves(TextChunkIter::new(text)) }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn easy() {
        let r = Rope::from_str("Hello there");
        assert_eq!(11, r.byte_len());

        println!("{:#?}", r.root);
        panic!("")

        // let r = Rope::from_str("🐕‍🦺");
        // assert_eq!(11, r.byte_len());

        // panic!("{r:?}");
    }
}
