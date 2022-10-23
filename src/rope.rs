use std::borrow::Cow;
use std::iter::Sum;
use std::ops::AddAssign;

use crate::{Summarize, Tree};

const ROPE_FANOUT: usize = 4;

#[cfg(not(test))]
const TEXT_CHUNK_MAX_BYTES: usize = 1024;

#[cfg(test)]
const TEXT_CHUNK_MAX_BYTES: usize = 4;

#[derive(Debug)]
struct TextChunk {
    text: [u8; TEXT_CHUNK_MAX_BYTES],
    initialized: usize,
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

pub struct Rope {
    text: Tree<ROPE_FANOUT, TextChunk>,
}

impl Rope {
    pub fn byte_len(&self) -> usize {
        self.text.summarize().byte_len
    }

    #[allow(clippy::should_implement_trait)]
    pub fn from_str(text: &str) -> Self {
        todo!()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // #[test]
    fn easy() {
        let r = Rope::from_str("Hello there");
        assert_eq!(11, r.byte_len());
    }
}
