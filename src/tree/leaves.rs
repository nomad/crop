use alloc::vec::Vec;

use super::{Arc, Inode, Leaf, LeafSlice, Metric, Node, Tree, TreeSlice};

/// An iterator over the leaves of `Tree`s and `TreeSlice`s.
//
// This iterator is implemented using two independent iterators advancing in
// opposite directions.
pub struct Leaves<'a, const ARITY: usize, L: Leaf> {
    /// Iterates over the leaves from front to back.
    forward: LeavesForward<'a, ARITY, L>,

    /// Iterates over the leaves from back to front.
    backward: LeavesBackward<'a, ARITY, L>,
}

impl<const ARITY: usize, L: Leaf> Clone for Leaves<'_, ARITY, L> {
    #[inline]
    fn clone(&self) -> Self {
        Self { forward: self.forward.clone(), backward: self.backward.clone() }
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
        }
    }
}

impl<'a, const ARITY: usize, L: Leaf> Iterator for Leaves<'a, ARITY, L> {
    type Item = L::Slice<'a>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.measure_yielded() == self.measure_total() {
            None
        } else {
            self.forward.next()
        }
    }
}

impl<const ARITY: usize, L: Leaf> DoubleEndedIterator
    for Leaves<'_, ARITY, L>
{
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.measure_yielded() == self.measure_total() {
            None
        } else {
            self.backward.previous()
        }
    }
}

impl<const ARITY: usize, L: Leaf> core::iter::FusedIterator
    for Leaves<'_, ARITY, L>
{
}

impl<const ARITY: usize, L: Leaf> Leaves<'_, ARITY, L> {
    /// Returns the total base measure of all the leaves in the tree or slice
    /// being iterated over.
    #[inline]
    fn measure_total(&self) -> L::BaseMetric {
        debug_assert_eq!(
            self.forward.measure_total,
            self.backward.measure_total
        );
        self.forward.measure_total
    }

    /// Returns the base measure of all the leaf slices yielded so far.
    #[inline]
    fn measure_yielded(&self) -> L::BaseMetric {
        self.forward.measure_yielded + self.backward.measure_yielded
    }
}

struct LeavesForward<'a, const N: usize, L: Leaf> {
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

    /// The total base measure of all the leaves in the tree or slice being
    /// iterated over.
    measure_total: L::BaseMetric,

    /// The base measure of all the leaf slices yielded so far.
    measure_yielded: L::BaseMetric,
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
            base_offset: L::BaseMetric::zero(),
            first_slice: None,
            last_slice: None,
            root: &**tree.root(),
            path: Vec::with_capacity(tree.root().depth().saturating_sub(1)),
            leaves: &[],
            next_leaf_idx: 0,
            measure_yielded: L::BaseMetric::zero(),
            measure_total: tree.base_measure(),
        }
    }
}

impl<'a, const ARITY: usize, L: Leaf> From<&TreeSlice<'a, ARITY, L>>
    for LeavesForward<'a, ARITY, L>
{
    #[inline]
    fn from(slice: &TreeSlice<'a, ARITY, L>) -> LeavesForward<'a, ARITY, L> {
        Self {
            base_offset: slice.offset,
            first_slice: Some(slice.start_slice),
            last_slice: Some(slice.end_slice),
            root: &**slice.root(),
            path: Vec::with_capacity(slice.root().depth().saturating_sub(1)),
            leaves: &[],
            next_leaf_idx: 0,
            measure_yielded: L::BaseMetric::zero(),
            measure_total: slice.base_measure(),
        }
    }
}

impl<'a, const N: usize, L: Leaf> LeavesForward<'a, N, L> {
    #[inline]
    fn advance_to_next_bunch(&mut self) {
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
                    self.leaves = inode.children();
                    self.next_leaf_idx = 0;
                    return;
                },
            }
        }
    }

    #[inline]
    fn initialize(&mut self) -> (L::Slice<'a>, &'a [Arc<Node<N, L>>]) {
        debug_assert!(self.measure_yielded.is_zero());

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

                Node::Leaf(first) => {
                    return match self.first_slice.take() {
                        Some(first_slice) => {
                            // The index of the first slice in the parent.
                            let first_slice_idx = inode
                                .children()
                                .iter()
                                .take_while(|child| {
                                    offset += child.base_measure();
                                    offset <= self.base_offset
                                })
                                .count();

                            (
                                first_slice,
                                &inode.children()[first_slice_idx + 1..],
                            )
                        },
                        None => (first.as_slice(), &inode.children()[1..]),
                    };
                },
            }
        }
    }

    #[inline]
    fn next(&mut self) -> Option<L::Slice<'a>> {
        if self.measure_yielded == self.measure_total {
            return None;
        }

        if self.measure_yielded.is_zero() {
            let (first, rest) = self.initialize();
            self.measure_yielded = first.base_measure();
            self.leaves = rest;
            return Some(first);
        }

        if self.next_leaf_idx == self.leaves.len() {
            self.advance_to_next_bunch();
        }

        let next_leaf = &self.leaves[self.next_leaf_idx].get_leaf();
        self.next_leaf_idx += 1;
        self.measure_yielded += next_leaf.base_measure();

        // If we're iterating over a `TreeSlice`, make sure we're not yielding
        // past its end_slice.
        if self.measure_yielded > self.measure_total {
            self.measure_yielded = self.measure_total;
            self.last_slice.take()
        } else {
            Some(next_leaf.as_slice())
        }
    }
}

struct LeavesBackward<'a, const N: usize, L: Leaf> {
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

    /// The total base measure of all the leaves in the tree or slice being
    /// iterated over.
    measure_total: L::BaseMetric,

    /// The base measure of all the leaf slices yielded so far.
    measure_yielded: L::BaseMetric,
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
            base_offset: L::BaseMetric::zero(),
            first_slice: None,
            last_slice: None,
            root: &**tree.root(),
            path: Vec::with_capacity(tree.root().depth().saturating_sub(1)),
            leaves: &[],
            last_leaf_idx: 0,
            measure_yielded: L::BaseMetric::zero(),
            measure_total: tree.base_measure(),
        }
    }
}

impl<'a, const ARITY: usize, L: Leaf> From<&TreeSlice<'a, ARITY, L>>
    for LeavesBackward<'a, ARITY, L>
{
    #[inline]
    fn from(slice: &TreeSlice<'a, ARITY, L>) -> LeavesBackward<'a, ARITY, L> {
        let base_offset =
            slice.root().base_measure() - slice.offset - slice.base_measure();

        Self {
            base_offset,
            first_slice: Some(slice.start_slice),
            last_slice: Some(slice.end_slice),
            root: &**slice.root(),
            path: Vec::with_capacity(slice.root().depth().saturating_sub(1)),
            leaves: &[],
            last_leaf_idx: 0,
            measure_yielded: L::BaseMetric::zero(),
            measure_total: slice.base_measure(),
        }
    }
}

impl<'a, const N: usize, L: Leaf> LeavesBackward<'a, N, L> {
    #[inline]
    fn advance_to_previous_bunch(&mut self) {
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
                    self.leaves = inode.children();
                    self.last_leaf_idx = inode.len();
                    return;
                },
            }
        }
    }

    #[inline]
    fn initialize(&mut self) -> (&'a [Arc<Node<N, L>>], L::Slice<'a>) {
        debug_assert!(self.measure_yielded.is_zero());

        let mut inode = match self.root {
            Node::Internal(inode) => inode,

            Node::Leaf(leaf) => {
                let last = self.last_slice.take().unwrap_or(leaf.as_slice());
                return (&[], last);
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

                Node::Leaf(last) => {
                    return match self.last_slice.take() {
                        Some(last_slice) => {
                            // The index of the last slice in the parent.
                            let last_slice_idx = inode.len()
                                - 1
                                - inode
                                    .children()
                                    .iter()
                                    .rev()
                                    .take_while(|child| {
                                        offset += child.base_measure();
                                        offset <= self.base_offset
                                    })
                                    .count();

                            (&inode.children()[..last_slice_idx], last_slice)
                        },
                        None => (
                            &inode.children()[..inode.len() - 1],
                            last.as_slice(),
                        ),
                    };
                },
            }
        }
    }

    #[inline]
    fn previous(&mut self) -> Option<L::Slice<'a>> {
        if self.measure_yielded == self.measure_total {
            return None;
        }

        if self.measure_yielded.is_zero() {
            let (rest, last) = self.initialize();
            self.measure_yielded = last.base_measure();
            self.leaves = rest;
            self.last_leaf_idx = rest.len();
            return Some(last);
        }

        if self.last_leaf_idx == 0 {
            self.advance_to_previous_bunch();
        }

        self.last_leaf_idx -= 1;
        let next_leaf = &self.leaves[self.last_leaf_idx].get_leaf();
        self.measure_yielded += next_leaf.base_measure();

        // If we're iterating over a `TreeSlice`, make sure we're not yielding
        // past its start_slice.
        if self.measure_yielded > self.measure_total {
            self.measure_yielded = self.measure_total;
            self.first_slice.take()
        } else {
            Some(next_leaf.as_slice())
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
            for leaf in leaves.by_ref() {
                assert_eq!(i, *leaf.0);
                i += 1;
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
