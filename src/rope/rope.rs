use std::fmt::{self, Debug};
use std::ops::RangeBounds;

use super::metrics::ByteMetric;
use super::utils;
use super::{Chunks, TextChunk, TextChunkIter};
use crate::tree::Tree;
use crate::RopeSlice;

pub(super) const ROPE_FANOUT: usize = 8;

pub struct Rope {
    root: Tree<ROPE_FANOUT, TextChunk>,
}

impl Debug for Rope {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str("Rope(\"")?;
        for chunk in self.chunks() {
            f.write_str(chunk)?;
        }
        f.write_str("\")")
    }
}

impl Rope {
    /// TODO: docs
    pub fn byte_len(&self) -> usize {
        self.root.summary().bytes
    }

    /// TODO: docs
    pub fn byte_slice<R>(&self, byte_range: R) -> RopeSlice<'_>
    where
        R: RangeBounds<usize>,
    {
        let (start, end) =
            utils::range_bound_to_tuple(byte_range, 0, self.byte_len());

        RopeSlice::from(self.root.slice(ByteMetric(start)..ByteMetric(end)))
    }

    fn chunks(&self) -> Chunks<'_> {
        Chunks { chunks: self.root.leaves() }
    }

    /// TODO: docs
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
