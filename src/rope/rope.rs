use std::ops::RangeBounds;

use super::{TextChunk, TextChunkIter, ROPE_FANOUT};
use crate::tree::Tree;
use crate::RopeSlice;

#[derive(Debug)]
pub struct Rope {
    root: Tree<ROPE_FANOUT, TextChunk>,
}

impl Rope {
    pub fn byte_len(&self) -> usize {
        self.root.summary().bytes
    }

    pub fn byte_slice<R>(&self, byte_range: R) -> RopeSlice<'_>
    where
        R: RangeBounds<usize>,
    {
        // Slice the rope's tree using the ByteMetric.

        // let interval = todo!();
        // RopeSlice { tree_slice: self.root.slice(interval) }

        todo!()
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
