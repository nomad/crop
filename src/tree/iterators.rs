use super::{Metric, Node, Summarize, TreeSlice};

/// An iterator over the leaves of trees or tree slices.
///
/// This iterator is created via the `leaves` method on
/// [`Tree`](super::Tree::leaves) and [`TreeSlice`](super::TreeSlice::leaves).
#[derive(Clone)]
pub struct Leaves<'a, Leaf: Summarize> {
    leaves: Vec<&'a Leaf>,
    start: usize,
    end: usize,
}

impl<'a, Leaf: Summarize> Leaves<'a, Leaf> {
    pub(super) fn new() -> Self {
        Self { leaves: Vec::new(), start: 0, end: 0 }
    }

    pub(super) fn push_leaf(&mut self, leaf: &'a Leaf) {
        self.leaves.push(leaf);
        self.end += 1;
    }

    pub(super) fn push_node_subtree<const N: usize>(
        &mut self,
        node: &'a Node<N, Leaf>,
    ) {
        match node {
            Node::Internal(inode) => {
                for child in inode.children() {
                    self.push_node_subtree(&**child);
                }
            },

            Node::Leaf(leaf) => self.push_leaf(leaf.value()),
        }
    }
}

impl<'a, Leaf: Summarize> Iterator for Leaves<'a, Leaf> {
    type Item = &'a Leaf;

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

impl<'a, Leaf: Summarize> DoubleEndedIterator for Leaves<'a, Leaf> {
    fn next_back(&mut self) -> Option<&'a Leaf> {
        if self.start == self.end {
            None
        } else {
            self.end -= 1;
            Some(&self.leaves[self.end])
        }
    }
}

impl<'a, Leaf: Summarize> ExactSizeIterator for Leaves<'a, Leaf> {}

impl<'a, Leaf: Summarize> std::iter::FusedIterator for Leaves<'a, Leaf> {}

/// An iterator over consecutive units of a particular metric.
///
/// This iterator will chop down a tree or a tree slice by hacking at it using
/// a metric.
#[derive(Clone)]
pub struct Chops<
    'a,
    const FANOUT: usize,
    Leaf: Summarize,
    Advance: Metric<Leaf>,
> {
    _tmp1: &'a (),
    _tmp2: Leaf,
    _tmp3: Advance,
}

impl<'a, const FANOUT: usize, Leaf: Summarize + 'a, Advance: Metric<Leaf>>
    Iterator for Chops<'a, FANOUT, Leaf, Advance>
{
    type Item = TreeSlice<'a, FANOUT, Leaf>;

    fn next(&mut self) -> Option<Self::Item> {
        todo!()
    }
}
