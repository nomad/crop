use std::sync::Arc;

use crate::tree::{Inode, Leaf, Metric, Node, Tree, TreeSlice};

/// An iterator over the leaves of `Tree`s and `TreeSlice`s.
pub struct Leaves<'a, const FANOUT: usize, L: Leaf> {
    /*
      Just like the `Units` iterator, this iterator is also implemented using
      two independent iterators advancing in opposite directions.
    */
    #[rustfmt::skip]

    /// Iterates over the leaves from front to back.
    forward: LeavesForward<'a, FANOUT, L>,

    /// Iterates over the leaves from back to front.
    backward: LeavesBackward<'a, FANOUT, L>,

    /// The number of leaves which are yet to be yielded.
    leaves_remaining: usize,
}

impl<'a, const FANOUT: usize, L: Leaf> Clone for Leaves<'a, FANOUT, L> {
    #[inline]
    fn clone(&self) -> Self {
        Self {
            forward: self.forward.clone(),
            backward: self.backward.clone(),
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
            forward: LeavesForward::from(tree),
            backward: LeavesBackward::from(tree),
            leaves_remaining: tree.root.num_leaves(),
        }
    }
}

impl<'a, const FANOUT: usize, L: Leaf> From<&'a TreeSlice<'a, FANOUT, L>>
    for Leaves<'a, FANOUT, L>
{
    #[inline]
    fn from(slice: &'a TreeSlice<'a, FANOUT, L>) -> Leaves<'a, FANOUT, L> {
        Self {
            forward: LeavesForward::from(slice),
            backward: LeavesBackward::from(slice),
            leaves_remaining: slice.leaf_count(),
        }
    }
}

impl<'a, const FANOUT: usize, L: Leaf> Iterator for Leaves<'a, FANOUT, L> {
    type Item = (&'a L::Slice, &'a L::Summary);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.leaves_remaining == 0 {
            None
        } else {
            self.leaves_remaining -= 1;
            self.forward.next()
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let exact = self.len();
        (exact, Some(exact))
    }
}

impl<'a, const FANOUT: usize, L: Leaf> DoubleEndedIterator
    for Leaves<'a, FANOUT, L>
{
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.leaves_remaining == 0 {
            None
        } else {
            self.leaves_remaining -= 1;
            self.backward.previous()
        }
    }
}

impl<'a, const FANOUT: usize, L: Leaf> ExactSizeIterator
    for Leaves<'a, FANOUT, L>
{
    #[inline]
    fn len(&self) -> usize {
        self.leaves_remaining
    }
}

impl<'a, const FANOUT: usize, L: Leaf> std::iter::FusedIterator
    for Leaves<'a, FANOUT, L>
{
}

struct LeavesForward<'a, const N: usize, L: Leaf> {
    /// Whether `Self` has been initialized by calling
    /// [`initialize`](LeavesForward::initialize).
    is_initialized: bool,

    /// The root of the `Tree` or `TreeSlice` we're iterating over.
    root: &'a Node<N, L>,

    /// The path from the root down to (but not including) the internal node
    /// containing `leaves`. It follows that the depth of the last node (if
    /// there is one) is 2.
    path: Vec<(&'a Inode<N, L>, usize)>,

    /// TODO: docs
    leaves: &'a [Arc<Node<N, L>>],

    /// TODO: docs
    next_leaf_idx: usize,

    /// The first slice in the yielding range and its summary. It's only set if
    /// we're iterating over a `TreeSlice`.
    first_slice: Option<(&'a L::Slice, &'a L::Summary)>,

    /// The last slice in the yielding range and its summary. It's only set if
    /// we're iterating over a `TreeSlice`.
    last_slice: Option<(&'a L::Slice, &'a L::Summary)>,

    /// TODO: docs
    base_offset: L::BaseMetric,

    /// TODO: docs
    whole_yielded: usize,

    /// TODO: docs
    whole_total: usize,
}

impl<'a, const N: usize, L: Leaf> Clone for LeavesForward<'a, N, L> {
    #[inline]
    fn clone(&self) -> Self {
        Self { path: self.path.clone(), ..*self }
    }
}

impl<'a, const N: usize, L: Leaf> From<&'a Tree<N, L>>
    for LeavesForward<'a, N, L>
{
    #[inline]
    fn from(tree: &'a Tree<N, L>) -> LeavesForward<'a, N, L> {
        // TODO: explain why `yielded` starts off  as `1`.
        Self {
            is_initialized: false,
            base_offset: L::BaseMetric::zero(),
            first_slice: None,
            last_slice: None,
            root: &**tree.root(),
            path: Vec::with_capacity(tree.root().depth().saturating_sub(1)),
            leaves: &[],
            next_leaf_idx: 0,
            whole_yielded: 1,
            whole_total: tree.root().num_leaves(),
        }
    }
}

impl<'a, const FANOUT: usize, L: Leaf> From<&'a TreeSlice<'a, FANOUT, L>>
    for LeavesForward<'a, FANOUT, L>
{
    #[inline]
    fn from(
        slice: &'a TreeSlice<'a, FANOUT, L>,
    ) -> LeavesForward<'a, FANOUT, L> {
        Self {
            is_initialized: false,
            base_offset: slice.offset,
            first_slice: Some((slice.start_slice, &slice.start_summary)),
            last_slice: Some((slice.end_slice, &slice.end_summary)),
            root: &**slice.root(),
            path: Vec::with_capacity(slice.root().depth().saturating_sub(1)),
            leaves: &[],
            next_leaf_idx: 0,
            whole_yielded: 0,
            whole_total: slice.leaf_count().saturating_sub(2),
        }
    }
}

impl<'a, const N: usize, L: Leaf> LeavesForward<'a, N, L> {
    #[inline]
    fn initialize(
        &mut self,
    ) -> ((&'a L::Slice, &'a L::Summary), &'a [Arc<Node<N, L>>]) {
        debug_assert!(!self.is_initialized);

        self.is_initialized = true;

        let mut inode = match self.root {
            Node::Internal(inode) => inode,

            Node::Leaf(leaf) => {
                let first = self
                    .first_slice
                    .take()
                    .unwrap_or((leaf.as_slice(), leaf.summary()));

                return (first, &[]);
            },
        };

        let mut offset = L::BaseMetric::zero();

        'outer: loop {
            match &**inode.first() {
                Node::Internal(_) => {
                    for (idx, i) in inode
                        .children()
                        .iter()
                        .map(|n| {
                            // Safety: the first child is an internal node, so
                            // all its siblings are internal nodes as well.
                            unsafe { n.as_internal_unchecked() }
                        })
                        .enumerate()
                    {
                        let this = i.base_measure();

                        if offset + this > self.base_offset {
                            self.path.push((inode, idx));
                            inode = i;
                            continue 'outer;
                        } else {
                            offset += this;
                        }
                    }

                    unreachable!();
                },

                Node::Leaf(_) => {
                    for (idx, leaf) in inode
                        .children()
                        .iter()
                        .map(|n| {
                            // Safety: the first child is a leaf node, so all
                            // its siblings are leaf nodes as well.
                            unsafe { n.as_leaf_unchecked() }
                        })
                        .enumerate()
                    {
                        offset += leaf.base_measure();

                        if offset > self.base_offset {
                            let first = self
                                .first_slice
                                .take()
                                .unwrap_or((leaf.as_slice(), leaf.summary()));

                            let n = std::cmp::min(
                                inode.children().len() - idx - 1,
                                self.whole_total - self.whole_yielded,
                            );

                            return (
                                first,
                                &inode.children()[idx + 1..(idx + 1 + n)],
                            );
                        }
                    }

                    unreachable!();
                },
            }
        }
    }

    #[inline]
    fn next_bunch(&mut self) -> &'a [Arc<Node<N, L>>] {
        let mut inode = loop {
            let &mut (inode, ref mut visited) = self.path.last_mut().unwrap();

            *visited += 1;

            if *visited == inode.children().len() {
                self.path.pop();
            } else {
                let inode = &inode.children()[*visited];

                // Safety: the last internal node in `path` is always *2*
                // levels above a leaf, so all its children are internal
                // nodes 1 level above a leaf.
                break unsafe { inode.as_internal_unchecked() };
            }
        };

        loop {
            match &**inode.first() {
                Node::Internal(i) => {
                    self.path.push((inode, 0));
                    inode = i;
                },

                Node::Leaf(_) => {
                    let n = std::cmp::min(
                        inode.children().len(),
                        self.whole_total - self.whole_yielded,
                    );

                    return &inode.children()[..n];
                },
            }
        }
    }

    #[inline]
    fn next(&mut self) -> Option<(&'a L::Slice, &'a L::Summary)> {
        if !self.is_initialized {
            let (first, first_bunch) = self.initialize();
            self.leaves = first_bunch;
            return Some(first);
        }

        if self.next_leaf_idx < self.leaves.len() {
            let lnode = &self.leaves[self.next_leaf_idx];
            let lnode = unsafe { lnode.as_leaf_unchecked() };
            self.next_leaf_idx += 1;
            self.whole_yielded += 1;
            Some((lnode.as_slice(), lnode.summary()))
        } else if self.whole_yielded < self.whole_total {
            self.leaves = self.next_bunch();
            let lnode = &self.leaves[0];
            let lnode = unsafe { lnode.as_leaf_unchecked() };
            self.next_leaf_idx = 1;
            self.whole_yielded += 1;
            Some((lnode.as_slice(), lnode.summary()))
        } else if self.last_slice.is_some() {
            self.last_slice.take()
        } else {
            None
        }
    }
}

struct LeavesBackward<'a, const N: usize, L: Leaf> {
    /// TODO: docs
    is_initialized: bool,

    /// TODO: docs
    base_offset: L::BaseMetric,

    /// TODO: docs
    first_slice: Option<(&'a L::Slice, &'a L::Summary)>,

    /// TODO: docs
    last_slice: Option<(&'a L::Slice, &'a L::Summary)>,

    /// TODO: docs
    root: &'a Node<N, L>,

    /// TODO: docs
    path: Vec<(&'a Inode<N, L>, usize)>,

    /// TODO: docs
    leaves: &'a [Arc<Node<N, L>>],

    /// TODO: docs
    last_leaf_idx: usize,

    /// TODO: docs
    whole_yielded: usize,

    /// TODO: docs
    whole_total: usize,
}

impl<'a, const N: usize, L: Leaf> Clone for LeavesBackward<'a, N, L> {
    #[inline]
    fn clone(&self) -> Self {
        Self { path: self.path.clone(), ..*self }
    }
}

impl<'a, const N: usize, L: Leaf> From<&'a Tree<N, L>>
    for LeavesBackward<'a, N, L>
{
    #[inline]
    fn from(tree: &'a Tree<N, L>) -> LeavesBackward<'a, N, L> {
        Self {
            is_initialized: false,
            base_offset: L::BaseMetric::zero(),
            first_slice: None,
            last_slice: None,
            root: &**tree.root(),
            path: Vec::with_capacity(tree.root().depth().saturating_sub(1)),
            leaves: &[],
            last_leaf_idx: 0,
            whole_yielded: 1,
            whole_total: tree.root().num_leaves(),
        }
    }
}

impl<'a, const FANOUT: usize, L: Leaf> From<&'a TreeSlice<'a, FANOUT, L>>
    for LeavesBackward<'a, FANOUT, L>
{
    #[inline]
    fn from(
        slice: &'a TreeSlice<'a, FANOUT, L>,
    ) -> LeavesBackward<'a, FANOUT, L> {
        let base_offset =
            slice.root().base_measure() - slice.offset - slice.base_measure();

        Self {
            is_initialized: false,
            base_offset,
            first_slice: Some((slice.start_slice, &slice.start_summary)),
            last_slice: Some((slice.end_slice, &slice.end_summary)),
            root: &**slice.root(),
            path: Vec::with_capacity(slice.root().depth().saturating_sub(1)),
            leaves: &[],
            last_leaf_idx: 0,
            whole_yielded: 0,
            whole_total: slice.leaf_count().saturating_sub(2),
        }
    }
}

impl<'a, const N: usize, L: Leaf> LeavesBackward<'a, N, L> {
    #[inline]
    fn initialize(
        &mut self,
    ) -> ((&'a L::Slice, &'a L::Summary), &'a [Arc<Node<N, L>>]) {
        debug_assert!(!self.is_initialized);

        self.is_initialized = true;

        let mut inode = match self.root {
            Node::Internal(inode) => inode,

            Node::Leaf(leaf) => {
                let last = self
                    .last_slice
                    .take()
                    .unwrap_or((leaf.as_slice(), leaf.summary()));

                return (last, &[]);
            },
        };

        let mut offset = L::BaseMetric::zero();

        'outer: loop {
            match &**inode.last() {
                Node::Internal(_) => {
                    for (idx, i) in inode
                        .children()
                        .iter()
                        .map(|n| {
                            // Safety: the last child is an internal node, so
                            // all its siblings are internal nodes as well.
                            unsafe { n.as_internal_unchecked() }
                        })
                        .enumerate()
                        .rev()
                    {
                        let this = i.base_measure();

                        if offset + this > self.base_offset {
                            self.path.push((inode, idx));
                            inode = i;
                            continue 'outer;
                        } else {
                            offset += this;
                        }
                    }

                    unreachable!();
                },

                Node::Leaf(_) => {
                    for (idx, leaf) in inode
                        .children()
                        .iter()
                        .map(|n| {
                            // Safety: the last child is a leaf node, so all
                            // its siblings are leaf nodes as well.
                            unsafe { n.as_leaf_unchecked() }
                        })
                        .enumerate()
                        .rev()
                    {
                        offset += leaf.base_measure();

                        if offset > self.base_offset {
                            let last = self
                                .last_slice
                                .take()
                                .unwrap_or((leaf.as_slice(), leaf.summary()));

                            let n = std::cmp::min(
                                idx,
                                self.whole_total - self.whole_yielded,
                            );

                            return (last, &inode.children()[(idx - n)..idx]);
                        }
                    }

                    unreachable!();
                },
            }
        }
    }

    #[inline]
    fn previous_bunch(&mut self) -> &'a [Arc<Node<N, L>>] {
        let mut inode = loop {
            let &mut (inode, ref mut visited) = self.path.last_mut().unwrap();

            if *visited == 0 {
                self.path.pop();
            } else {
                *visited -= 1;

                let inode = &inode.children()[*visited];

                // Safety: the last internal node in `path` is always *2*
                // levels above a leaf, so all its children are internal
                // nodes 1 level above a leaf.
                break unsafe { inode.as_internal_unchecked() };
            }
        };

        loop {
            match &**inode.last() {
                Node::Internal(i) => {
                    self.path.push((inode, inode.children().len() - 1));
                    inode = i;
                },

                Node::Leaf(_) => {
                    let n = std::cmp::min(
                        inode.children().len(),
                        self.whole_total - self.whole_yielded,
                    );

                    return &inode.children()[(inode.children().len() - n)..];
                },
            }
        }
    }

    #[inline]
    fn previous(&mut self) -> Option<(&'a L::Slice, &'a L::Summary)> {
        if !self.is_initialized {
            let (last, last_bunch) = self.initialize();
            self.leaves = last_bunch;
            self.last_leaf_idx = self.leaves.len();
            return Some(last);
        }

        if self.last_leaf_idx > 0 {
            self.last_leaf_idx -= 1;
            let lnode = &self.leaves[self.last_leaf_idx];
            let lnode = unsafe { lnode.as_leaf_unchecked() };
            self.whole_yielded += 1;
            Some((lnode.as_slice(), lnode.summary()))
        } else if self.whole_yielded < self.whole_total {
            self.leaves = self.previous_bunch();
            self.last_leaf_idx = self.leaves.len() - 1;
            let lnode = &self.leaves[self.last_leaf_idx];
            let lnode = unsafe { lnode.as_leaf_unchecked() };
            self.whole_yielded += 1;
            Some((lnode.as_slice(), lnode.summary()))
        } else if self.first_slice.is_some() {
            self.first_slice.take()
        } else {
            None
        }
    }
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
            while let Some((leaf, _)) = leaves.next() {
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
            while let Some((leaf, _)) = leaves.next_back() {
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
                assert_eq!(j, *leaves.next().unwrap().0);
            }
            for j in (i..n).rev() {
                assert_eq!(j, *leaves.next_back().unwrap().0);
            }
            assert_eq!(None, leaves.next());
            assert_eq!(None, leaves.next_back());
        }
    }
}
