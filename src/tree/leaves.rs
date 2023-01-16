use std::sync::Arc;

use crate::tree::{Inode, Leaf, Metric, Node, Tree, TreeSlice};

/// An iterator over the leaves of trees or tree slices.
///
/// This iterator is created via the `leaves` method on
/// [`Tree`](super::Tree::leaves) and [`TreeSlice`](super::TreeSlice::leaves).
pub struct Leaves<'a, const FANOUT: usize, L: Leaf> {
    /// TODO: docs
    root: &'a Node<FANOUT, L>,

    /// TODO: docs
    before: L::BaseMetric,

    /// TODO: docs
    after: L::BaseMetric,

    /// TODO: docs
    first_slice: Option<&'a L::Slice>,

    /// TODO: docs
    last_slice: Option<&'a L::Slice>,

    /// TODO: docs
    first_been_yielded: bool,

    /// TODO: docs
    last_been_yielded: bool,

    /// The current leaves, usually the result of calling the
    /// [`children()`](Inode::children) method on an internal node. All the
    /// nodes in the slice are guaranteed to be leaf nodes.
    forward_leaves: &'a [Arc<Node<FANOUT, L>>],

    /// An index into `forward_leaves` representing the next leaf to yield.
    forward_leaf_idx: usize,

    /// A path of internal nodes starting from the current root node going down
    /// to the tree. The second element in each tuple is an index representing
    /// the inode's children we're currently in.
    forward_path: Vec<(&'a Inode<FANOUT, L>, usize)>,

    /// Same as `forward_leaves` for backward iteration (used in `next_back`).
    backward_leaves: &'a [Arc<Node<FANOUT, L>>],

    /// Same as `forward_leaf_idx` for backward iteration (used in
    /// `next_back`), except it represents the index of the *previous* yielded
    /// leaf, not the next one.
    backward_leaf_idx: usize,

    /// Same as `forward_path` for backward iteration (used in `next_back`).
    backward_path: Vec<(&'a Inode<FANOUT, L>, usize)>,

    /// TODO: docs.
    yielded: usize,

    /// TODO: docs.
    total: usize,
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
        Self {
            root: &*tree.root,
            before: L::BaseMetric::zero(),
            after: L::BaseMetric::zero(),
            first_slice: None,
            last_slice: None,
            first_been_yielded: false,
            last_been_yielded: false,
            forward_leaves: &[],
            forward_leaf_idx: 0,
            forward_path: Vec::new(),
            backward_leaves: &[],
            backward_leaf_idx: 0,
            backward_path: Vec::new(),
            yielded: 0,
            total: tree.root.num_leaves(),
        }
    }
}

impl<'a, const FANOUT: usize, L: Leaf> From<&'a TreeSlice<'a, FANOUT, L>>
    for Leaves<'a, FANOUT, L>
{
    #[inline]
    fn from(slice: &'a TreeSlice<'a, FANOUT, L>) -> Leaves<'a, FANOUT, L> {
        let root = &*slice.root;

        let before = slice.before;

        let after = L::BaseMetric::measure(root.summary())
            - L::BaseMetric::measure(slice.summary())
            - before;

        Self {
            root,
            before,
            after,
            first_slice: Some(slice.start_slice),
            last_slice: Some(slice.end_slice),
            first_been_yielded: false,
            last_been_yielded: false,
            forward_leaves: &[],
            forward_leaf_idx: 0,
            forward_path: Vec::new(),
            backward_leaves: &[],
            backward_leaf_idx: 0,
            backward_path: Vec::new(),
            yielded: 0,
            total: slice.num_leaves(),
        }
    }
}

impl<'a, const FANOUT: usize, L: Leaf> Iterator for Leaves<'a, FANOUT, L> {
    type Item = &'a L::Slice;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        // TODO: explain this
        if self.yielded == self.total {
            return None;
        }
        // TODO: explain this
        else if !self.first_been_yielded {
            let (first, forward_leaves) = first_slice_forward(
                self.root,
                self.before,
                &mut self.forward_path,
                &mut self.first_slice,
            );
            self.yielded += 1;
            self.forward_leaves = forward_leaves;
            self.first_been_yielded = true;
            return Some(first);
        }
        // TODO: explain this
        else if self.yielded + 1 == self.total && self.last_slice.is_some() {
            let last = self.last_slice.unwrap();
            self.yielded += 1;
            return Some(last);
        }

        if self.forward_leaf_idx == self.forward_leaves.len() {
            self.forward_leaves = next_leaves_forward(&mut self.forward_path);
            self.forward_leaf_idx = 0;
        }

        // Safety: the implementation of [`next_leaves_forward`] guarantees
        // that all the nodes in the `forward_leaves` slice are leaf nodes.
        let leaf = unsafe {
            self.forward_leaves[self.forward_leaf_idx].as_leaf_unchecked()
        };

        // Increase the current leaf index for the next iteration.
        self.forward_leaf_idx += 1;

        self.yielded += 1;

        Some(leaf.as_slice())
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.total - self.yielded;
        (remaining, Some(remaining))
    }
}

impl<'a, const FANOUT: usize, L: Leaf> DoubleEndedIterator
    for Leaves<'a, FANOUT, L>
{
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        // TODO: explain this
        if self.yielded == self.total {
            return None;
        }
        // TODO: explain this
        else if !self.last_been_yielded {
            let (last, backward_leaves) = first_slice_backward(
                self.root,
                self.after,
                &mut self.backward_path,
                &mut self.last_slice,
            );
            self.yielded += 1;
            self.backward_leaves = backward_leaves;
            self.backward_leaf_idx = self.backward_leaves.len();
            self.last_been_yielded = true;
            return Some(last);
        }
        // TODO: explain this
        else if self.yielded + 1 == self.total && self.first_slice.is_some()
        {
            let first = self.first_slice.unwrap();
            self.yielded += 1;
            return Some(first);
        }

        if self.backward_leaf_idx == 0 {
            self.backward_leaves =
                next_leaves_backward(&mut self.backward_path);
            self.backward_leaf_idx = self.backward_leaves.len();
        }

        // Safety: the implementation of [`next_leaves_backward`] guarantees
        // that all the nodes in the `backward_leaves` slice are leaf nodes.
        let leaf = unsafe {
            self.backward_leaves[self.backward_leaf_idx - 1]
                .as_leaf_unchecked()
        };

        // Decrease the current leaf index for the next iteration.
        self.backward_leaf_idx -= 1;

        self.yielded += 1;

        Some(leaf.as_slice())
    }
}

#[inline]
fn first_slice_forward<'a, const N: usize, L: Leaf>(
    root: &'a Node<N, L>,
    offset: L::BaseMetric,
    path: &mut Vec<(&'a Inode<N, L>, usize)>,
    first_slice: &mut Option<&'a L::Slice>,
) -> (&'a L::Slice, &'a [Arc<Node<N, L>>]) {
    // This function should only be called the first time `Leaves::next` is
    // executed, at which point `forward_path` should be empty.
    debug_assert!(path.is_empty());

    // If we're iterating over the leaves of a TreeSlice the first slice should
    // be present, if not then we're iterating over the leaves of a Tree, in
    // which case the offset should be zero.
    debug_assert!(first_slice.is_some() || offset == L::BaseMetric::zero());

    let mut inode = match root {
        Node::Internal(inode) => inode,
        Node::Leaf(leaf) => {
            return (first_slice.take().unwrap_or(leaf.as_slice()), &[]);
        },
    };

    let mut measured = L::BaseMetric::zero();

    'outer: loop {
        match &*inode.children()[0] {
            Node::Internal(_) => {
                for (idx, inod) in inode
                    .children()
                    .iter()
                    // Safety: the first child is an internal node, so all its
                    // siblings are internal nodes as well.
                    .map(|n| unsafe { n.as_internal_unchecked() })
                    .enumerate()
                {
                    let this = L::BaseMetric::measure(inod.summary());
                    if measured + this > offset {
                        path.push((inode, idx));
                        inode = inod;
                        continue 'outer;
                    } else {
                        measured += this;
                    }
                }

                unreachable!();
            },

            Node::Leaf(_) => {
                for (idx, leaf) in inode
                    .children()
                    .iter()
                    // Safety: the first child is a leaf node, so all its
                    // siblings are leaf nodes as well.
                    .map(|n| unsafe { n.as_leaf_unchecked() })
                    .enumerate()
                {
                    measured += L::BaseMetric::measure(leaf.summary());
                    if measured > offset {
                        return (
                            first_slice.take().unwrap_or(leaf.as_slice()),
                            &inode.children()[idx + 1..],
                        );
                    }
                }

                unreachable!();
            },
        }
    }
}

#[inline]
fn first_slice_backward<'a, const N: usize, L: Leaf>(
    root: &'a Node<N, L>,
    offset: L::BaseMetric,
    path: &mut Vec<(&'a Inode<N, L>, usize)>,
    last_slice: &mut Option<&'a L::Slice>,
) -> (&'a L::Slice, &'a [Arc<Node<N, L>>]) {
    // This function should only be called the first time `Leaves::next_back`
    // is executed, at which point `backward_path` should be empty.
    debug_assert!(path.is_empty());

    // If we're iterating over the leaves of a TreeSlice the last slice should
    // be present, if not then we're iterating over the leaves of a Tree, in
    // which case the offset should be zero.
    debug_assert!(last_slice.is_some() || offset == L::BaseMetric::zero());

    let mut inode = match root {
        Node::Internal(inode) => inode,
        Node::Leaf(leaf) => {
            return (last_slice.take().unwrap_or(leaf.as_slice()), &[]);
        },
    };

    let mut measured = L::BaseMetric::zero();

    'outer: loop {
        match &*inode.children()[inode.children().len() - 1] {
            Node::Internal(_) => {
                for (idx, inod) in inode
                    .children()
                    .iter()
                    // Safety: the last child is an internal node, so all its
                    // siblings are internal nodes as well.
                    .map(|n| unsafe { n.as_internal_unchecked() })
                    .enumerate()
                    .rev()
                {
                    let this = L::BaseMetric::measure(inod.summary());
                    if measured + this > offset {
                        path.push((inode, idx));
                        inode = inod;
                        continue 'outer;
                    } else {
                        measured += this;
                    }
                }

                unreachable!();
            },

            Node::Leaf(_) => {
                for (idx, leaf) in inode
                    .children()
                    .iter()
                    // Safety: the last child is a leaf node, so all its
                    // siblings are leaf nodes as well.
                    .map(|n| unsafe { n.as_leaf_unchecked() })
                    .enumerate()
                    .rev()
                {
                    measured += L::BaseMetric::measure(leaf.summary());
                    if measured > offset {
                        return (
                            last_slice.take().unwrap_or(leaf.as_slice()),
                            &inode.children()[..idx],
                        );
                    }
                }

                unreachable!();
            },
        }
    }
}

#[inline]
fn next_leaves_forward<'a, const N: usize, L: Leaf>(
    path: &mut Vec<(&'a Inode<N, L>, usize)>,
) -> &'a [Arc<Node<N, L>>] {
    let mut inode = loop {
        let idx_last = path.len() - 1;
        let &mut (inode, ref mut visited) = &mut path[idx_last];
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
    };

    loop {
        match &*inode.children()[0] {
            Node::Internal(inod) => {
                path.push((inode, 0));
                inode = inod;
            },
            Node::Leaf(_) => {
                return inode.children();
            },
        }
    }
}

#[inline]
fn next_leaves_backward<'a, const N: usize, L: Leaf>(
    path: &mut Vec<(&'a Inode<N, L>, usize)>,
) -> &'a [Arc<Node<N, L>>] {
    let mut inode = loop {
        let idx_last = path.len() - 1;
        let &mut (inode, ref mut visited) = &mut path[idx_last];
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
    };

    loop {
        match &*inode.children()[inode.children().len() - 1] {
            Node::Internal(inod) => {
                path.push((inode, inode.children().len() - 1));
                inode = inod;
            },
            Node::Leaf(_) => {
                return inode.children();
            },
        }
    }
}

impl<'a, const FANOUT: usize, L: Leaf> ExactSizeIterator
    for Leaves<'a, FANOUT, L>
{
    #[inline]
    fn len(&self) -> usize {
        self.total - self.yielded
    }
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
