use std::fmt::{self, Debug};

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

    fn chunks(&self) -> Chunks<'_> {
        Chunks { chunks: self.tree_slice.leaves() }
    }

    #[allow(clippy::should_implement_trait)]
    pub(super) fn from(slice: TreeSlice<'a, ROPE_FANOUT, TextChunk>) -> Self {
        Self { tree_slice: slice }
    }
}
