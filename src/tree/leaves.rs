use alloc::vec::Vec;

use super::{Arc, Inode, Leaf, Metric, Node, Tree, TreeSlice};

/// An iterator over the leaves of `Tree`s and `TreeSlice`s.
//
// This iterator is implemented using two independent iterators advancing in
// opposite directions.
pub struct Leaves<'a, const ARITY: usize, L: Leaf> {
    /// Iterates over the leaves from front to back.
    forward: LeavesForward<'a, ARITY, L>,

    /// Iterates over the leaves from back to front.
    backward: LeavesBackward<'a, ARITY, L>,

    /// The number of leaves that have been yielded so far.
    leaves_yielded: usize,

    /// The total number of leaves this iterator will yield.
    leaves_total: usize,
}

impl<const ARITY: usize, L: Leaf> Clone for Leaves<'_, ARITY, L> {
    #[inline]
    fn clone(&self) -> Self {
        Self {
            forward: self.forward.clone(),
            backward: self.backward.clone(),
            ..*self
        }
    }
}

impl<'a, const ARITY: usize, L: Leaf> From<&'a Tree<ARITY, L>>
    for Leaves<'a, ARITY, L>
{
    #[inline]
    fn from(tree: &'a Tree<ARITY, L>) -> Leaves<'a, ARITY, L> {
        Self {
            forward: LeavesForward::from(tree),
            backward: LeavesBackward::from(tree),
            leaves_yielded: 0,
            leaves_total: tree.leaf_count(),
        }
    }
}

impl<'a, const ARITY: usize, L: Leaf> From<&TreeSlice<'a, ARITY, L>>
    for Leaves<'a, ARITY, L>
{
    #[inline]
    fn from(slice: &TreeSlice<'a, ARITY, L>) -> Leaves<'a, ARITY, L> {
        Self {
            forward: LeavesForward::from(slice),
            backward: LeavesBackward::from(slice),
            leaves_yielded: 0,
            leaves_total: slice.leaf_count(),
        }
    }
}

impl<'a, const ARITY: usize, L: Leaf> Iterator for Leaves<'a, ARITY, L> {
    type Item = L::Slice<'a>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.leaves_yielded == self.leaves_total {
            None
        } else {
            self.leaves_yielded += 1;
            self.forward.next()
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let exact = self.len();
        (exact, Some(exact))
    }
}

impl<const ARITY: usize, L: Leaf> DoubleEndedIterator
    for Leaves<'_, ARITY, L>
{
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.leaves_yielded == self.leaves_total {
            None
        } else {
            self.leaves_yielded += 1;
            self.backward.previous()
        }
    }
}

impl<const ARITY: usize, L: Leaf> ExactSizeIterator for Leaves<'_, ARITY, L> {
    #[inline]
    fn len(&self) -> usize {
        self.leaves_total - self.leaves_yielded
    }
}

impl<const ARITY: usize, L: Leaf> core::iter::FusedIterator
    for Leaves<'_, ARITY, L>
{
}

#[derive(Debug)]
struct LeavesForward<'a, const N: usize, L: Leaf> {
    /// Whether `Self` has been initialized by calling
    /// [`initialize`](Self::initialize()).
    is_initialized: bool,

    /// The root of the `Tree` or `TreeSlice` we're iterating over.
    root: &'a Node<N, L>,

    /// The path from the root down to (but not including) the internal node
    /// containing `leaves`. It follows that the depth of the last node (if
    /// there is one) is 2.
    path: Vec<(&'a Inode<N, L>, usize)>,

    /// The current leaves. All the nodes in the slice are guaranteed to be
    /// leaf nodes.
    leaves: &'a [Arc<Node<N, L>>],

    /// The index of the next leaf in [`leaves`](Self::leaves) that'll be
    /// yielded by [`next`](Self::next()).
    next_leaf_idx: usize,

    /// The first slice in the yielding range and its summary. It's only set if
    /// we're iterating over a `TreeSlice`.
    first_slice: Option<L::Slice<'a>>,

    /// The last slice in the yielding range and its summary. It's only set if
    /// we're iterating over a `TreeSlice`.
    last_slice: Option<L::Slice<'a>>,

    /// The base offset of [`first_slice`](Self::first_slice), or zero if we're
    /// iterating over a `Tree`.
    base_offset: L::BaseMetric,

    /// The number of whole leaf slices yielded so far. All leaf slices are
    /// considered whole except for the first and last leaf slices of
    /// `TreeSlice`s.
    whole_yielded: usize,

    /// The number of whole leaf slices this iterator will yield.
    whole_total: usize,
}

impl<const N: usize, L: Leaf> Clone for LeavesForward<'_, N, L> {
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
        Self {
            is_initialized: false,
            base_offset: L::BaseMetric::zero(),
            first_slice: None,
            last_slice: None,
            root: &**tree.root(),
            path: Vec::with_capacity(tree.root().depth().saturating_sub(1)),
            leaves: &[],
            next_leaf_idx: 0,
            // NOTE: `whole_yielded` starts off as 1 because `Self::next()`
            // doesn't increase this counter the first time it's called.
            whole_yielded: 1,
            whole_total: tree.root().leaf_count(),
        }
    }
}

impl<'a, const ARITY: usize, L: Leaf> From<&TreeSlice<'a, ARITY, L>>
    for LeavesForward<'a, ARITY, L>
{
    #[inline]
    fn from(slice: &TreeSlice<'a, ARITY, L>) -> LeavesForward<'a, ARITY, L> {
        Self {
            is_initialized: false,
            base_offset: L::BaseMetric::measure(&slice.offset),
            first_slice: Some(slice.start_slice),
            last_slice: Some(slice.end_slice),
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
    #[allow(clippy::type_complexity)]
    #[inline]
    fn initialize(&mut self) -> (L::Slice<'a>, &'a [Arc<Node<N, L>>]) {
        debug_assert!(!self.is_initialized);

        self.is_initialized = true;

        let mut inode = match self.root {
            Node::Internal(inode) => inode,

            Node::Leaf(leaf) => {
                let first = self.first_slice.take().unwrap_or(leaf.as_slice());

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
                            // The first child is an internal node, so all its
                            // siblings are internal nodes as well.
                            n.get_internal()
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
                            // The first child is a leaf node, so all its
                            // siblings are leaf nodes as well.
                            n.get_leaf()
                        })
                        .enumerate()
                    {
                        offset += leaf.base_measure();

                        if offset > self.base_offset {
                            let first = self
                                .first_slice
                                .take()
                                .unwrap_or(leaf.as_slice());

                            let n = core::cmp::min(
                                inode.len() - idx - 1,
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

            if *visited == inode.len() {
                self.path.pop();
            } else {
                let inode = inode.child(*visited);

                // The last internal node in `path` is always *2* levels above
                // a leaf, so all its children are internal nodes 1 level above
                // a leaf.
                break inode.get_internal();
            }
        };

        loop {
            match &**inode.first() {
                Node::Internal(i) => {
                    self.path.push((inode, 0));
                    inode = i;
                },

                Node::Leaf(_) => {
                    let n = core::cmp::min(
                        inode.len(),
                        self.whole_total - self.whole_yielded,
                    );

                    return &inode.children()[..n];
                },
            }
        }
    }

    #[inline]
    fn next(&mut self) -> Option<L::Slice<'a>> {
        if !self.is_initialized {
            let (first, first_bunch) = self.initialize();
            self.leaves = first_bunch;
            return Some(first);
        }

        if self.next_leaf_idx < self.leaves.len() {
            // All the nodes in `leaves` are guaranteed to be leaf nodes.
            let lnode = &self.leaves[self.next_leaf_idx].get_leaf();
            self.next_leaf_idx += 1;
            self.whole_yielded += 1;
            Some(lnode.as_slice())
        } else if self.whole_yielded < self.whole_total {
            self.leaves = self.next_bunch();
            // Same as above.
            let lnode = &self.leaves[0].get_leaf();
            self.next_leaf_idx = 1;
            self.whole_yielded += 1;
            Some(lnode.as_slice())
        } else if self.last_slice.is_some() {
            self.last_slice.take()
        } else {
            None
        }
    }
}

#[derive(Debug)]
struct LeavesBackward<'a, const N: usize, L: Leaf> {
    /// Whether `Self` has been initialized by calling
    /// [`initialize`](Self::initialize()).
    is_initialized: bool,

    /// The root of the `Tree` or `TreeSlice` we're iterating over.
    root: &'a Node<N, L>,

    /// The path from the root down to (but not including) the internal node
    /// containing `leaves`. It follows that the depth of the last node (if
    /// there is one) is 2.
    path: Vec<(&'a Inode<N, L>, usize)>,

    /// The current leaves. All the nodes in the slice are guaranteed to be
    /// leaf nodes.
    leaves: &'a [Arc<Node<N, L>>],

    /// The index of the last leaf in [`leaves`](Self::leaves) that was yielded
    /// by [`previous`](Self::previous()).
    last_leaf_idx: usize,

    /// The first slice in the yielding range and its summary. It's only set if
    /// we're iterating over a `TreeSlice`.
    first_slice: Option<L::Slice<'a>>,

    /// The last slice in the yielding range and its summary. It's only set if
    /// we're iterating over a `TreeSlice`.
    last_slice: Option<L::Slice<'a>>,

    /// The base measure between the end of [`last_slice`](Self::last_slice)
    /// and the end of the subtree under [`root`](Self::root), or zero if we're
    /// iterating over a `Tree`.
    base_offset: L::BaseMetric,

    /// The number of whole leaf slices yielded so far. All leaf slices are
    /// considered whole except for the first and last leaf slices of
    /// `TreeSlice`s.
    whole_yielded: usize,

    /// The number of whole leaf slices this iterator will yield.
    whole_total: usize,
}

impl<const N: usize, L: Leaf> Clone for LeavesBackward<'_, N, L> {
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
            // NOTE: `whole_yielded` starts off as 1 because `Self::previous()`
            // doesn't increase this counter the first time it's called.
            whole_yielded: 1,
            whole_total: tree.root().leaf_count(),
        }
    }
}

impl<'a, const ARITY: usize, L: Leaf> From<&TreeSlice<'a, ARITY, L>>
    for LeavesBackward<'a, ARITY, L>
{
    #[inline]
    fn from(slice: &TreeSlice<'a, ARITY, L>) -> LeavesBackward<'a, ARITY, L> {
        let base_offset = slice.root().base_measure()
            - L::BaseMetric::measure(&slice.offset)
            - slice.base_measure();

        Self {
            is_initialized: false,
            base_offset,
            first_slice: Some(slice.start_slice),
            last_slice: Some(slice.end_slice),
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
    #[allow(clippy::type_complexity)]
    #[inline]
    fn initialize(&mut self) -> (L::Slice<'a>, &'a [Arc<Node<N, L>>]) {
        debug_assert!(!self.is_initialized);

        self.is_initialized = true;

        let mut inode = match self.root {
            Node::Internal(inode) => inode,

            Node::Leaf(leaf) => {
                let last = self.last_slice.take().unwrap_or(leaf.as_slice());

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
                            // The last child is an internal node, so all its
                            // siblings are internal nodes as well.
                            n.get_internal()
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
                            // The last child is a leaf node, so all its
                            // siblings are leaf nodes as well.
                            n.get_leaf()
                        })
                        .enumerate()
                        .rev()
                    {
                        offset += leaf.base_measure();

                        if offset > self.base_offset {
                            let last = self
                                .last_slice
                                .take()
                                .unwrap_or(leaf.as_slice());

                            let n = core::cmp::min(
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

                let inode = inode.child(*visited);

                // The last internal node in `path` is always *2* levels above
                // a leaf, so all its children are internal nodes 1 level above
                // a leaf.
                break inode.get_internal();
            }
        };

        loop {
            match &**inode.last() {
                Node::Internal(i) => {
                    self.path.push((inode, inode.len() - 1));
                    inode = i;
                },

                Node::Leaf(_) => {
                    let n = core::cmp::min(
                        inode.len(),
                        self.whole_total - self.whole_yielded,
                    );

                    return &inode.children()[(inode.len() - n)..];
                },
            }
        }
    }

    #[inline]
    fn previous(&mut self) -> Option<L::Slice<'a>> {
        if !self.is_initialized {
            let (last, last_bunch) = self.initialize();
            self.leaves = last_bunch;
            self.last_leaf_idx = self.leaves.len();
            return Some(last);
        }

        if self.last_leaf_idx > 0 {
            self.last_leaf_idx -= 1;
            // All the nodes in `leaves` are guaranteed to be leaf nodes.
            let lnode = &self.leaves[self.last_leaf_idx].get_leaf();
            self.whole_yielded += 1;
            Some(lnode.as_slice())
        } else if self.whole_yielded < self.whole_total {
            self.leaves = self.previous_bunch();
            self.last_leaf_idx = self.leaves.len() - 1;
            // Same as above.
            let lnode = &self.leaves[self.last_leaf_idx].get_leaf();
            self.whole_yielded += 1;
            Some(lnode.as_slice())
        } else if self.first_slice.is_some() {
            self.first_slice.take()
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use rand::{Rng, rng};

    use super::*;

    const MAX: usize = if cfg!(miri) { 8 } else { 256 };

    #[test]
    fn leaves_forward() {
        for n in 1..MAX {
            let tree = Tree::<4, usize>::from_leaves(0..n);
            let mut leaves = tree.leaves();
            let mut i = 0;
            while let Some(leaf) = leaves.next() {
                assert_eq!(i, *leaf.0);
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
        for n in 1..MAX {
            let tree = Tree::<4, usize>::from_leaves(0..n);
            let mut leaves = tree.leaves();
            let mut i = n;
            while let Some(leaf) = leaves.next_back() {
                i -= 1;
                assert_eq!(i, *leaf.0);
                assert_eq!(i, leaves.len());
            }
            assert_eq!(i, 0);
            assert_eq!(None, leaves.next_back());
            assert_eq!(None, leaves.next_back());
        }
    }

    #[test]
    fn leaves_both_ways() {
        let mut rng = rng();

        for n in 1..MAX {
            let tree = Tree::<4, usize>::from_leaves(0..n);
            let mut leaves = tree.leaves();
            let i = rng.random_range(0..=n);
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
