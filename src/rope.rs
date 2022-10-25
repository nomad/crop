use std::borrow::Cow;
use std::fmt;
use std::iter::Sum;
use std::ops::AddAssign;
use std::str;

use crate::{Summarize, Tree};

const ROPE_FANOUT: usize = 4;

#[cfg(not(test))]
const TEXT_CHUNK_MAX_BYTES: usize = 1024;

#[cfg(test)]
const TEXT_CHUNK_MAX_BYTES: usize = 4;

struct TextChunk {
    text: [u8; TEXT_CHUNK_MAX_BYTES],
    initialized: usize,
}

impl fmt::Debug for TextChunk {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // Yes, this is not actually safe right now.
        write!(f, "{:?}", unsafe {
            str::from_utf8_unchecked(&self.text[..self.initialized])
        })
    }
}

impl TextChunk {
    /// # Panics
    ///
    /// This function will panic if the byte length of `s` is bigger than
    /// `TEXT_CHUNK_MAX_BYTES`;
    fn from_bytes(bytes: &[u8]) -> Self {
        assert!(bytes.len() <= TEXT_CHUNK_MAX_BYTES);
        let mut text = [0u8; TEXT_CHUNK_MAX_BYTES];
        let (left, _) = text.split_at_mut(bytes.len());
        left.copy_from_slice(bytes);
        TextChunk { text, initialized: bytes.len() }
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

impl<'a> Sum<Cow<'a, TextSummary>> for TextSummary {
    fn sum<I>(mut iter: I) -> Self
    where
        I: Iterator<Item = Cow<'a, TextSummary>>,
    {
        let mut res = match iter.next() {
            Some(first) => first.into_owned(),
            None => return Self::default(),
        };
        for summary in iter {
            res += &*summary;
        }
        res
    }
}

impl Summarize for TextChunk {
    type Summary = TextSummary;

    fn summarize(&self) -> Self::Summary {
        TextSummary { byte_len: self.initialized }
    }
}

#[derive(Debug)]
pub struct Rope {
    text: Tree<ROPE_FANOUT, TextChunk>,
}

impl Rope {
    pub fn byte_len(&self) -> usize {
        self.text.summarize().byte_len
    }

    #[allow(clippy::should_implement_trait)]
    pub fn from_str(text: &str) -> Self {
        let text = Tree::from_leaves(str_to_text_chunks(text));
        Rope { text }
    }
}

fn str_to_text_chunks(s: &str) -> Vec<TextChunk> {
    let mut chunks = Vec::<TextChunk>::with_capacity(usize::div_ceil(
        s.len(),
        TEXT_CHUNK_MAX_BYTES,
    ));

    let mut bytes = s.bytes().array_chunks::<TEXT_CHUNK_MAX_BYTES>();

    while let Some(chunk) = bytes.next() {
        chunks
            .push(TextChunk { text: chunk, initialized: TEXT_CHUNK_MAX_BYTES })
    }

    if let Some(last) = bytes.into_remainder() {
        chunks.push(TextChunk::from_bytes(last.as_slice()));
    }

    chunks
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn easy() {
        let r = Rope::from_str("Hello there");
        assert_eq!(11, r.byte_len());

        println!("{:#?}", r.text);
        panic!("")

        // let r = Rope::from_str("🐕‍🦺");
        // assert_eq!(11, r.byte_len());

        // panic!("{r:?}");
    }
}
