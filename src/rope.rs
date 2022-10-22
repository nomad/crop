use std::mem::MaybeUninit;
use std::ops::AddAssign;

use crate::{Summarize, Tree};

const TEXT_CHUNK_MAX_BYTES: usize = 1024;

#[derive(Debug)]
struct TextChunk {
    text: [MaybeUninit<u8>; TEXT_CHUNK_MAX_BYTES],
    initialized: usize,
}

#[derive(Clone, Default)]
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
        TextSummary { byte_len: self.initialized }
    }
}

pub struct Rope {
    text: Tree<TextChunk>,
}

impl Rope {
    pub fn byte_len(&self) -> usize {
        self.text.summarize().byte_len
    }

    #[allow(clippy::should_implement_trait)]
    pub fn from_str(s: &str) -> Self {
        todo!()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn easy() {
        let r = Rope::from_str("Hello there");
        assert_eq!(11, r.byte_len());
    }
}
