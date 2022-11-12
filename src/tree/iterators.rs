use super::{Leaf, Metric, Node, TreeSlice};

/// An iterator over the leaves of trees or tree slices.
///
/// This iterator is created via the `leaves` method on
/// [`Tree`](super::Tree::leaves) and [`TreeSlice`](super::TreeSlice::leaves).
pub struct Leaves<'a, L: Leaf> {
    leaves: Vec<&'a L::Slice>,
    start: usize,
    end: usize,
}

impl<'a, L: Leaf> Clone for Leaves<'a, L> {
    #[inline]
    fn clone(&self) -> Self {
        Self { leaves: self.leaves.clone(), start: self.start, end: self.end }
    }
}

impl<'a, L: Leaf> Leaves<'a, L> {
    pub(super) fn new() -> Self {
        Self { leaves: Vec::new(), start: 0, end: 0 }
    }

    pub(super) fn push_leaf(&mut self, leaf: &'a L::Slice) {
        self.leaves.push(leaf);
        self.end += 1;
    }

    pub(super) fn push_node_subtree<const N: usize>(
        &mut self,
        node: &'a Node<N, L>,
    ) {
        match node {
            Node::Internal(inode) => {
                for child in inode.children() {
                    self.push_node_subtree(&**child);
                }
            },

            Node::Leaf(leaf) => self.push_leaf(leaf.value().borrow()),
        }
    }
}

impl<'a, L: Leaf> Iterator for Leaves<'a, L> {
    type Item = &'a L::Slice;

    fn next(&mut self) -> Option<Self::Item> {
        if self.start == self.end {
            None
        } else {
            let leaf = &self.leaves[self.start];
            self.start += 1;
            Some(leaf)
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.end - self.start;
        (remaining, Some(remaining))
    }
}

impl<'a, L: Leaf> DoubleEndedIterator for Leaves<'a, L> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.start == self.end {
            None
        } else {
            self.end -= 1;
            Some(&self.leaves[self.end])
        }
    }
}

impl<'a, L: Leaf> ExactSizeIterator for Leaves<'a, L> {}

impl<'a, L: Leaf> std::iter::FusedIterator for Leaves<'a, L> {}

/// An iterator over consecutive units of a particular metric.
///
/// This iterator will chop down a tree or a tree slice by hacking at it using
/// a metric.
#[derive(Clone)]
pub struct Chops<'a, const FANOUT: usize, L: Leaf, M: Metric<L>> {
    _tmp1: &'a (),
    _tmp2: L,
    _tmp3: M,
}

impl<'a, const FANOUT: usize, L: Leaf + 'a, M: Metric<L>> Iterator
    for Chops<'a, FANOUT, L, M>
{
    type Item = TreeSlice<'a, FANOUT, L>;

    fn next(&mut self) -> Option<Self::Item> {
        todo!()
    }
}
