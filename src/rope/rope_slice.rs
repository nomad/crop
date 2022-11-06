use std::fmt::{self, Debug};
use std::ops::RangeBounds;

use super::metrics::ByteMetric;
use super::utils::*;
use super::{Chunks, TextChunk, ROPE_FANOUT};
use crate::tree::TreeSlice;

pub struct RopeSlice<'a> {
    pub(super) tree_slice: TreeSlice<'a, ROPE_FANOUT, TextChunk>,
}

impl<'a> Debug for RopeSlice<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str("RopeSlice(\"")?;
        for chunk in self.chunks() {
            f.write_str(chunk)?;
        }
        f.write_str("\")")
    }
}

impl<'a> RopeSlice<'a> {
    pub fn byte_len(&self) -> usize {
        self.tree_slice.summary().bytes
    }

    /// TODO: docs
    pub fn byte_slice<R>(&self, byte_range: R) -> RopeSlice<'_>
    where
        R: RangeBounds<usize>,
    {
        let (start, end) = range_to_tuple(byte_range, 0, self.byte_len());
        Self::from(self.tree_slice.slice(ByteMetric(start)..ByteMetric(end)))
    }

    fn chunks(&self) -> Chunks<'_> {
        Chunks { chunks: self.tree_slice.leaves() }
    }

    #[allow(clippy::should_implement_trait)]
    pub(super) fn from(slice: TreeSlice<'a, ROPE_FANOUT, TextChunk>) -> Self {
        Self { tree_slice: slice }
    }
}
