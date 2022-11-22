use std::sync::Arc;

use crate::tree::tree_slice::SliceSpan;
use crate::tree::{Inode, Leaf, Node, Tree, TreeSlice};

/// An iterator over the leaves of trees or tree slices.
///
/// This iterator is created via the `leaves` method on
/// [`Tree`](super::Tree::leaves) and [`TreeSlice`](super::TreeSlice::leaves).
pub struct Leaves<'a, const FANOUT: usize, L: Leaf> {
    /// The first slice to yield. If we're iterating over the leaves of a tree
    /// this is `Some` only if the tree's root is a leaf. It's always `Some` if
    /// iterating over a tree slice.
    start: Option<&'a L::Slice>,

    /// Whether [start](Self::start) has already been yielded in a previous
    /// call to either [`next`](Leaves::next()) or
    /// [`next_back`](Leaves::next_back()).
    start_been_yielded: bool,

    /// TODO: docs
    root_nodes: &'a [Arc<Node<FANOUT, L>>],

    /// TODO: docs
    end: Option<&'a L::Slice>,

    /// TODO: docs
    end_been_yielded: bool,

    /// TODO: docs
    forward_root_idx: isize,

    /// TODO: docs
    forward_path: Vec<(&'a Inode<FANOUT, L>, usize)>,

    /// TODO: docs
    forward_leaves: &'a [Arc<Node<FANOUT, L>>],

    /// TODO: docs
    forward_leaf_idx: usize,

    /// TODO: docs
    _backward_root_idx: usize,

    /// TODO: docs
    backward_path: Vec<(&'a Inode<FANOUT, L>, usize)>,

    /// TODO: docs
    _backward_leaves: &'a [Arc<Node<FANOUT, L>>],

    /// TODO: docs
    _backward_leaf_idx: usize,
}

impl<'a, const FANOUT: usize, L: Leaf> Clone for Leaves<'a, FANOUT, L> {
    #[inline]
    fn clone(&self) -> Self {
        Self {
            forward_path: self.forward_path.clone(),
            backward_path: self.backward_path.clone(),
            ..*self
        }
    }
}

impl<'a, const FANOUT: usize, L: Leaf> From<&'a Tree<FANOUT, L>>
    for Leaves<'a, FANOUT, L>
{
    #[inline]
    fn from(tree: &'a Tree<FANOUT, L>) -> Leaves<'a, FANOUT, L> {
        let (start, start_been_yielded, root_nodes) = match &*tree.root {
            Node::Leaf(leaf) => (Some(leaf.value().borrow()), false, &[][..]),
            Node::Internal(inode) => (None, true, inode.children()),
        };

        Leaves {
            start,
            start_been_yielded,
            root_nodes,
            end: None,
            end_been_yielded: true,
            forward_root_idx: -1,
            forward_path: Vec::new(),
            forward_leaves: &[],
            forward_leaf_idx: 0,
            _backward_root_idx: root_nodes.len(),
            backward_path: Vec::new(),
            _backward_leaves: &[],
            _backward_leaf_idx: 0,
        }
    }
}

impl<'a, const FANOUT: usize, L: Leaf> From<&'a TreeSlice<'a, FANOUT, L>>
    for Leaves<'a, FANOUT, L>
{
    #[inline]
    fn from(
        tree_slice: &'a TreeSlice<'a, FANOUT, L>,
    ) -> Leaves<'a, FANOUT, L> {
        let (start, start_been_yielded, root_nodes, end, end_been_yielded) =
            match &tree_slice.span {
                SliceSpan::Empty => (None, true, &[][..], None, true),

                SliceSpan::Single(slice) => {
                    (Some(*slice), false, &[][..], None, true)
                },

                SliceSpan::Multi { start, internals, end } => {
                    (Some(start.0), false, &**internals, Some(end.0), false)
                },
            };

        Leaves {
            start,
            start_been_yielded,
            root_nodes,
            end,
            end_been_yielded,
            forward_path: Vec::new(),
            forward_root_idx: -1,
            forward_leaves: &[],
            forward_leaf_idx: 0,
            _backward_root_idx: root_nodes.len(),
            backward_path: Vec::new(),
            _backward_leaves: &[],
            _backward_leaf_idx: 0,
        }
    }
}

impl<'a, const FANOUT: usize, L: Leaf> Iterator for Leaves<'a, FANOUT, L> {
    type Item = &'a L::Slice;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if !self.start_been_yielded {
            self.start_been_yielded = true;
            if self.start.is_some() {
                return self.start;
            }
        }

        if self.forward_leaf_idx == self.forward_leaves.len() {
            // If we've exhausted the current leaves we look for the next
            // bunch.
            match next_leaves_forward(
                self.root_nodes,
                &mut self.forward_root_idx,
                &mut self.forward_path,
            ) {
                Some(leaves) => {
                    self.forward_leaves = leaves;
                    self.forward_leaf_idx = 0;
                },
                None => {
                    // If these were the last leaves we return the final slice
                    // and we're done.
                    if !self.end_been_yielded {
                        self.end_been_yielded = true;
                        return self.end;
                    } else {
                        return None;
                    }
                },
            }
        }

        // Safety: the implementation of [`next_leaves_forward`] guarantees
        // that all the nodes in the `forward_leaves` slice are leaf nodes.
        let leaf = unsafe {
            self.forward_leaves[self.forward_leaf_idx].as_leaf_unchecked()
        }
        .value()
        .borrow();

        // Increase the current leaf index for the next iteration.
        self.forward_leaf_idx += 1;

        Some(leaf)
    }
}

fn next_leaves_forward<'a, const N: usize, L: Leaf>(
    root_nodes: &'a [Arc<Node<N, L>>],
    root_idx: &mut isize,
    path: &mut Vec<(&'a Inode<N, L>, usize)>,
) -> Option<&'a [Arc<Node<N, L>>]> {
    let mut inode = loop {
        match path.last_mut() {
            Some(&mut (inode, ref mut visited)) => {
                *visited += 1;

                if inode.children().len() == *visited {
                    path.pop();
                } else {
                    // Safety: the last internal node in `path` is always *2*
                    // levels above a leaf, so all its children are internal
                    // nodes 1 level above a leaf.
                    break unsafe {
                        inode.children()[*visited].as_internal_unchecked()
                    };
                }
            },

            None => {
                // If there's nothing left in the path it means we've gone
                // through all the leaves under the current root.
                if root_nodes.len() == (*root_idx + 1) as usize {
                    // If this was the last root we're done.
                    return None;
                } else {
                    *root_idx += 1;
                    match &*root_nodes[*root_idx as usize] {
                        Node::Internal(inode) => {
                            break inode;
                        },
                        Node::Leaf(_) => {
                            // The next root is itself a leaf. We return a
                            // slice containing only this node.
                            return Some(
                                &root_nodes[*root_idx as usize
                                    ..*root_idx as usize + 1],
                            );
                        },
                    }
                }
            },
        }
    };

    loop {
        match &*inode.children()[0] {
            Node::Internal(i) => {
                path.push((inode, 0));
                inode = i;
            },
            Node::Leaf(_) => {
                return Some(inode.children());
            },
        }
    }
}

impl<'a, const FANOUT: usize, L: Leaf> DoubleEndedIterator
    for Leaves<'a, FANOUT, L>
{
    fn next_back(&mut self) -> Option<Self::Item> {
        if !self.end_been_yielded {
            self.end_been_yielded = true;
            if self.end.is_some() {
                return self.end;
            }
        }
        todo!()
    }
}

impl<'a, const FANOUT: usize, L: Leaf> std::iter::FusedIterator
    for Leaves<'a, FANOUT, L>
{
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn leaves_1() {
        for n in 1..100 {
            let tree = Tree::<2, usize>::from_leaves(0..n);
            let mut leaves = tree.leaves();
            let mut i = 0;
            while let Some(leaf) = leaves.next() {
                assert_eq!(i, *leaf);
                i += 1;
            }
            assert_eq!(i, n);
            assert_eq!(None, leaves.next());
            assert_eq!(None, leaves.next());
        }
    }

    #[ignore]
    #[test]
    fn leaves_2() {
        let tree = Tree::<2, usize>::from_leaves(0..3);
        let mut leaves = tree.leaves();

        assert_eq!(Some(&2), leaves.next_back());
        assert_eq!(Some(&1), leaves.next_back());
        assert_eq!(Some(&0), leaves.next_back());
        assert_eq!(None, leaves.next_back());
        assert_eq!(None, leaves.next_back());
    }
}
