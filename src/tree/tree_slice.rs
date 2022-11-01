use std::ops::RangeBounds;

use super::{Leaves, Metric, Node, Summarize};

#[derive(Copy, Clone)]
pub struct TreeSlice<'a, const FANOUT: usize, Leaf: Summarize> {
    /// The deepest node in the tree that still fully contains the interval
    /// from which this slice was derived.
    node: &'a Node<FANOUT, Leaf>,

    /// A offset in `node` after which this slice begins.
    offset: Leaf::Summary,

    /// This slice's summary.
    summary: Leaf::Summary,
}

impl<'a, const FANOUT: usize, Leaf: Summarize> TreeSlice<'a, FANOUT, Leaf> {
    pub fn leaves(&self) -> Leaves<'_, Leaf> {
        todo!()
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
