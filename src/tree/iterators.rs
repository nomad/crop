use super::{Node, Summarize};

pub struct Leaves<'a, Leaf: Summarize> {
    leaves: Vec<&'a Leaf>,
    current: usize,
    iterating_forward: bool,
}

impl<'a, Leaf: Summarize> Leaves<'a, Leaf> {
    pub fn new() -> Self {
        Self { leaves: Vec::new(), current: 0, iterating_forward: true }
    }

    pub(super) fn push_leaf(&mut self, leaf: &'a Leaf) {
        self.leaves.push(leaf)
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

    /// Reverses the direction of the iterator.
    pub fn reverse(mut self) -> Self {
        self.iterating_forward = !self.iterating_forward;
        self
    }
}

impl<'a, Leaf: Summarize> Iterator for Leaves<'a, Leaf> {
    type Item = &'a Leaf;

    fn next(&mut self) -> Option<Self::Item> {
        if self.iterating_forward {
            if self.current == self.leaves.len() {
                None
            } else {
                let leaf = &self.leaves[self.current];
                self.current += 1;
                Some(leaf)
            }
        } else {
            if self.current == 0 {
                None
            } else {
                let leaf = &self.leaves[self.current];
                self.current -= 1;
                Some(leaf)
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = if self.iterating_forward {
            self.leaves.len() - self.current
        } else {
            self.current
        };
        (len, Some(len))
    }
}

impl<'a, Leaf: Summarize> ExactSizeIterator for Leaves<'a, Leaf> {}

impl<'a, Leaf: Summarize> std::iter::FusedIterator for Leaves<'a, Leaf> {}
