use std::sync::Arc;

use crate::tree::tree_slice::SliceSpan;
use crate::tree::{Inode, Leaf, Node, Tree, TreeSlice};

/// An iterator over the leaves of trees or tree slices.
///
/// This iterator is created via the `leaves` method on
/// [`Tree`](super::Tree::leaves) and [`TreeSlice`](super::TreeSlice::leaves).
pub struct Leaves<'a, const FANOUT: usize, L: Leaf> {
    /// The first slice to yield. When iterating over the leaves of a tree this
    /// is `Some` only if the tree's root is a leaf, while it's always `Some`
    /// if iterating over a tree slice.
    start: Option<&'a L::Slice>,

    /// Whether [start](Self::start) has already been yielded in a previous
    /// call to either [`next`](Leaves::next()) or
    /// [`next_back`](Leaves::next_back()).
    start_been_yielded: bool,

    /// A slice of top level nodes containing the majority (possibly all) of
    /// the leaves that this iterator will yield in their subtrees. It's equal
    /// to the root's children when iterating over a tree (when the root is an
    /// internal node), and to the `internals` of a multi slice span when
    /// iterating over a tree slice.
    root_nodes: &'a [Arc<Node<FANOUT, L>>],

    /// The last slice to yield. It's `Some` only when iterating over tree
    /// slices.
    end: Option<&'a L::Slice>,

    /// Whether [end](Self::end) has already been yielded in a previous
    /// call to either [`next`](Leaves::next()) or
    /// [`next_back`](Leaves::next_back()).
    end_been_yielded: bool,

    /// An index into `root_nodes` representing the root node that we're
    /// currently in. It's an isize instead of a usize because it starts
    /// off as -1.
    forward_root_idx: isize,

    /// A path of internal nodes starting from the current root node going down
    /// to the tree. The second element in each tuple is an index representing
    /// the inode's children we're currently in.
    forward_path: Vec<(&'a Inode<FANOUT, L>, usize)>,

    /// The current leaves, usually the result of calling the
    /// [`children()`](Inode::children) method on an internal node. All the
    /// nodes in the slice are guaranteed to be leaf nodes.
    forward_leaves: &'a [Arc<Node<FANOUT, L>>],

    /// An index into `forward_leaves` representing the next leaf to yield.
    forward_leaf_idx: usize,

    /// Same as `forward_root_idx` for backward iteration (used in
    /// `next_back`).
    backward_root_idx: usize,

    /// Same as `forward_path` for backward iteration (used in `next_back`).
    backward_path: Vec<(&'a Inode<FANOUT, L>, usize)>,

    /// Same as `forward_leaves` for backward iteration (used in `next_back`).
    backward_leaves: &'a [Arc<Node<FANOUT, L>>],

    /// Same as `forward_leaf_idx` for backward iteration (used in
    /// `next_back`), except it represents the index of the *previous* yielded
    /// leaf, not the next one.
    backward_leaf_idx: usize,

    /// The total number of leaves this iterator will yield.
    total_leaves: usize,

    /// The number of leaves yielded by calling `next`.
    yielded_forward: usize,

    /// The number of leaves yielded by calling `next_back`.
    yielded_backward: usize,
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
            backward_root_idx: root_nodes.len(),
            backward_path: Vec::new(),
            backward_leaves: &[],
            backward_leaf_idx: 0,
            total_leaves: tree.root.leaves(),
            yielded_forward: 0,
            yielded_backward: 0,
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
        let (
            start,
            start_been_yielded,
            root_nodes,
            end,
            end_been_yielded,
            total_leaves,
        ) = match &tree_slice.span {
            SliceSpan::Empty => (None, true, &[][..], None, true, 0),

            SliceSpan::Single(slice) => {
                (Some(*slice), false, &[][..], None, true, 1)
            },

            SliceSpan::Multi { start, internals, end } => {
                let total =
                    internals.iter().map(|n| n.leaves()).sum::<usize>() + 2;
                (Some(start.0), false, &**internals, Some(end.0), false, total)
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
            backward_root_idx: root_nodes.len(),
            backward_path: Vec::new(),
            backward_leaves: &[],
            backward_leaf_idx: 0,
            total_leaves,
            yielded_forward: 0,
            yielded_backward: 0,
        }
    }
}

impl<'a, const FANOUT: usize, L: Leaf> Iterator for Leaves<'a, FANOUT, L> {
    type Item = &'a L::Slice;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.yielded_forward + self.yielded_backward == self.total_leaves {
            return None;
        }

        if !self.start_been_yielded {
            self.start_been_yielded = true;
            if self.start.is_some() {
                self.yielded_forward += 1;
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
                        self.yielded_forward += 1;
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

        self.yielded_forward += 1;

        Some(leaf)
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let exact =
            self.total_leaves - self.yielded_forward - self.yielded_backward;

        (exact, Some(exact))
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
        if self.yielded_forward + self.yielded_backward == self.total_leaves {
            return None;
        }

        if !self.end_been_yielded {
            self.end_been_yielded = true;
            if self.end.is_some() {
                self.yielded_backward += 1;
                return self.end;
            }
        }

        if self.backward_leaf_idx == 0 {
            // If we've exhausted the current leaves we look for the previous
            // bunch.
            match next_leaves_backward(
                self.root_nodes,
                &mut self.backward_root_idx,
                &mut self.backward_path,
            ) {
                Some(leaves) => {
                    self.backward_leaves = leaves;
                    self.backward_leaf_idx = leaves.len();
                },
                None => {
                    // If these were the first leaves we return the initial
                    // slice and we're done.
                    if !self.start_been_yielded {
                        self.start_been_yielded = true;
                        self.yielded_backward += 1;
                        return self.start;
                    } else {
                        return None;
                    }
                },
            }
        }

        // Safety: the implementation of [`next_leaves_backward`] guarantees
        // that all the nodes in the `backward_leaves` slice are leaf nodes.
        let leaf = unsafe {
            self.backward_leaves[self.backward_leaf_idx - 1]
                .as_leaf_unchecked()
        }
        .value()
        .borrow();

        // Decrease the current leaf index for the next iteration.
        self.backward_leaf_idx -= 1;

        self.yielded_backward += 1;

        Some(leaf)
    }
}

fn next_leaves_backward<'a, const N: usize, L: Leaf>(
    root_nodes: &'a [Arc<Node<N, L>>],
    root_idx: &mut usize,
    path: &mut Vec<(&'a Inode<N, L>, usize)>,
) -> Option<&'a [Arc<Node<N, L>>]> {
    let mut inode = loop {
        match path.last_mut() {
            Some(&mut (inode, ref mut visited)) => {
                if *visited == 0 {
                    path.pop();
                } else {
                    *visited -= 1;

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
                if *root_idx == 0 {
                    // If this was the first root we're done.
                    return None;
                } else {
                    *root_idx -= 1;
                    match &*root_nodes[*root_idx as usize] {
                        Node::Internal(inode) => {
                            break inode;
                        },
                        Node::Leaf(_) => {
                            // The previous root is itself a leaf. We return a
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
        match &*inode.children()[inode.children().len() - 1] {
            Node::Internal(i) => {
                path.push((inode, inode.children().len() - 1));
                inode = i;
            },
            Node::Leaf(_) => {
                return Some(inode.children());
            },
        }
    }
}

impl<'a, const FANOUT: usize, L: Leaf> ExactSizeIterator
    for Leaves<'a, FANOUT, L>
{
}

impl<'a, const FANOUT: usize, L: Leaf> std::iter::FusedIterator
    for Leaves<'a, FANOUT, L>
{
}

#[cfg(test)]
mod tests {
    use rand::{thread_rng, Rng};

    use super::*;

    #[test]
    fn leaves_forward() {
        for n in 1..256 {
            let tree = Tree::<2, usize>::from_leaves(0..n);
            let mut leaves = tree.leaves();
            let mut i = 0;
            while let Some(leaf) = leaves.next() {
                assert_eq!(i, *leaf);
                i += 1;
                assert_eq!(n - i, leaves.len());
            }
            assert_eq!(i, n);
            assert_eq!(None, leaves.next());
            assert_eq!(None, leaves.next());
        }
    }

    #[test]
    fn leaves_backward() {
        for n in 1..256 {
            let tree = Tree::<2, usize>::from_leaves(0..n);
            let mut leaves = tree.leaves();
            let mut i = n;
            while let Some(leaf) = leaves.next_back() {
                i -= 1;
                assert_eq!(i, *leaf);
                assert_eq!(i, leaves.len());
            }
            assert_eq!(i, 0);
            assert_eq!(None, leaves.next_back());
            assert_eq!(None, leaves.next_back());
        }
    }

    #[test]
    fn leaves_both_ways() {
        let mut rng = thread_rng();

        for n in 1..256 {
            let tree = Tree::<2, usize>::from_leaves(0..n);
            let mut leaves = tree.leaves();
            let i = rng.gen_range(0..=n);
            for j in 0..i {
                assert_eq!(j, *leaves.next().unwrap());
            }
            for j in (i..n).rev() {
                assert_eq!(j, *leaves.next_back().unwrap());
            }
            assert_eq!(None, leaves.next());
            assert_eq!(None, leaves.next_back());
        }
    }
}
