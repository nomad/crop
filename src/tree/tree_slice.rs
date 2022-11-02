use std::ops::RangeBounds;

use super::{Inode, LeafCoordinates, Leaves, Metric, Node, Summarize};

#[derive(Clone)]
pub struct TreeSlice<'a, const FANOUT: usize, Leaf: Summarize> {
    kind: SliceKind<'a, FANOUT, Leaf>,
    summary: Leaf::Summary,
}

#[derive(Clone)]
enum SliceKind<'a, const N: usize, Leaf: Summarize> {
    /// The slice was fully contained in a single leaf.
    SingleLeaf(&'a Leaf),

    /// The slice spans multiple leaves.
    SubTree {
        /// The deepest internal node in the tree that still fully contains the
        /// interval from which this slice was derived.
        inode: &'a Inode<N, Leaf>,

        /// TODO: docs
        start_leaf: (LeafCoordinates<N>, Option<Leaf>),

        /// TODO: docs
        end_leaf: (LeafCoordinates<N>, Option<Leaf>),
    },
}

impl<'a, const FANOUT: usize, Leaf: Summarize> TreeSlice<'a, FANOUT, Leaf> {
    pub fn leaves(&self) -> Leaves<'_, Leaf> {
        todo!()
    }

    pub(super) fn single_leaf(leaf: &'a Leaf) -> TreeSlice<'a, FANOUT, Leaf> {
        Self { kind: SliceKind::SingleLeaf(leaf), summary: leaf.summarize() }
    }

    pub fn slice<M, R>(&self, interval: R) -> TreeSlice<'a, FANOUT, Leaf>
    where
        R: RangeBounds<M>,
        M: Metric<Leaf>,
    {
        todo!()
    }

    pub fn summary(&self) -> &Leaf::Summary {
        &self.summary
    }
}
