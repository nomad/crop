use super::{Node, Summarize};

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
    pub fn summary(&self) -> &Leaf::Summary {
        &self.summary
    }
}
