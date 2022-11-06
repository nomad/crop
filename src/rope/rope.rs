use std::fmt::{self, Debug};
use std::ops::RangeBounds;

use super::metrics::ByteMetric;
use super::utils::*;
use super::{Chunks, TextChunk, TextChunkIter};
use crate::tree::Tree;
use crate::RopeSlice;

#[cfg(not(test))]
pub(super) const ROPE_FANOUT: usize = 8;

#[cfg(test)]
pub(super) const ROPE_FANOUT: usize = 2;

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
        let (start, end) = range_to_tuple(byte_range, 0, self.byte_len());
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

    #[test]
    fn slice() {
        let r = Rope::from_str("Hello there");

        let s = r.byte_slice(..);
        assert_eq!(11, s.byte_len());

        let s = s.byte_slice(0..5);
        assert_eq!(5, s.byte_len());

        let r = Rope::from_str(
            "Hello there this is a really long line that I'm gonna use to \
             test this fucking slicing methods that we got going on well \
             hope this shit works 'cause if it doesn't I'm gonna fucking \
             lose it ok bye :)",
        );

        let s = r.byte_slice(14..79);
        assert_eq!(65, s.byte_len());

        let s = r.byte_slice(0..11);
        assert_eq!(11, s.byte_len());

        let s = r.byte_slice(0..=10);
        assert_eq!(11, s.byte_len());
    }
}
