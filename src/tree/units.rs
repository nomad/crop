use std::sync::Arc;

use crate::tree::{Inode, Leaf, Metric, Node, Tree, TreeSlice};

/// An iterator over consecutive units of a particular metric.
pub struct Units<'a, const FANOUT: usize, L: Leaf, M: Metric<L>> {
    root: &'a Arc<Node<FANOUT, L>>,

    /// TODO: docs
    metric: std::marker::PhantomData<M>,
}

impl<'a, const FANOUT: usize, L: Leaf, M: Metric<L>> Clone
    for Units<'a, FANOUT, L, M>
{
    #[inline]
    fn clone(&self) -> Self {
        todo!()
    }
}

impl<'a, const FANOUT: usize, L: Leaf, M: Metric<L>> From<&'a Tree<FANOUT, L>>
    for Units<'a, FANOUT, L, M>
{
    #[inline]
    fn from(tree: &'a Tree<FANOUT, L>) -> Units<'a, FANOUT, L, M> {
        todo!()
    }
}

impl<'a, const FANOUT: usize, L: Leaf, M: Metric<L>>
    From<&'a TreeSlice<'a, FANOUT, L>> for Units<'a, FANOUT, L, M>
{
    #[inline]
    fn from(
        tree_slice: &'a TreeSlice<'a, FANOUT, L>,
    ) -> Units<'a, FANOUT, L, M> {
        todo!()
    }
}

impl<'a, const FANOUT: usize, L: Leaf, M: Metric<L>> Units<'a, FANOUT, L, M> {}

impl<'a, const FANOUT: usize, L: Leaf, M: Metric<L>> Iterator
    for Units<'a, FANOUT, L, M>
{
    type Item = TreeSlice<'a, FANOUT, L>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        todo!()
    }
}

impl<'a, const FANOUT: usize, L: Leaf, M: Metric<L>> DoubleEndedIterator
    for Units<'a, FANOUT, L, M>
{
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        todo!()
    }
}

impl<'a, const FANOUT: usize, L: Leaf, M: Metric<L>> std::iter::FusedIterator
    for Units<'a, FANOUT, L, M>
{
}
