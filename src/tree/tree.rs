use std::ops::Range;
use std::sync::Arc;

use super::{Inode, Leaf, Leaves, Lnode, Metric, Node, TreeSlice, Units};

/// TODO: docs
#[derive(Default)]
pub struct Tree<const FANOUT: usize, L: Leaf> {
    pub(super) root: Arc<Node<FANOUT, L>>,
}

impl<const N: usize, L: Leaf> Clone for Tree<N, L> {
    #[inline]
    fn clone(&self) -> Self {
        Tree { root: Arc::clone(&self.root) }
    }
}

impl<const N: usize, L: Leaf> std::fmt::Debug for Tree<N, L> {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        if !f.alternate() {
            f.debug_struct("Tree").field("root", &self.root).finish()
        } else {
            write!(f, "{:#?}", self.root)
        }
    }
}

impl<'a, const FANOUT: usize, L: Leaf> From<TreeSlice<'a, FANOUT, L>>
    for Tree<FANOUT, L>
{
    #[inline]
    fn from(slice: TreeSlice<'a, FANOUT, L>) -> Tree<FANOUT, L> {
        let root = if slice.base_measure() == slice.root().base_measure() {
            // If the TreeSlice and its root have the same base measure it
            // means the TreeSlice spanned the whole Tree from which it was
            // created and we can simply clone the root.
            Arc::clone(slice.root())
        } else if slice.leaf_count() == 1 {
            debug_assert!(slice.root().is_leaf());

            Arc::new(Node::Leaf(Lnode::new(
                slice.start_slice.to_owned(),
                slice.summary,
            )))
        } else if slice.leaf_count() == 2 {
            let (first, second) = L::balance_slices(
                (slice.start_slice, &slice.start_summary),
                (slice.end_slice, &slice.end_summary),
            );

            let first = Arc::new(Node::Leaf(Lnode::from(first)));

            if let Some(second) = second {
                let second = Arc::new(Node::Leaf(Lnode::from(second)));
                let root = Inode::from_children([first, second]);
                Arc::new(Node::Internal(root))
            } else {
                first
            }
        } else {
            // println!(
            //     "{:?}..{:?} of {:?}",
            //     slice.before,
            //     slice.before + slice.base_measure(),
            //     slice.root.base_measure()
            // );
            from_treeslice::into_tree_root(slice)
        };

        Tree { root }
    }
}

impl<const FANOUT: usize, L: Leaf> Tree<FANOUT, L> {
    /// Checks that all the internal nodes in the Tree contain between `FANOUT
    /// / 2` and `FANOUT` children. The root is the only internal node that's
    /// allowed to have as few as 2 children. Doesn't do any checks on leaf
    /// nodes.
    #[doc(hidden)]
    pub fn assert_invariants(&self) {
        if let Node::Internal(root) = &*self.root {
            assert!(
                root.children().len() >= 2 && root.children().len() <= FANOUT
            );

            for child in root.children() {
                child.assert_invariants()
            }
        }
    }

    #[inline]
    pub fn convert_measure<M1, M2>(&self, from: M1) -> M2
    where
        M1: Metric<L>,
        M2: Metric<L>,
    {
        // TODO: doesn't work for `LineMetric`

        debug_assert!(
            from <= M1::measure(self.summary()),
            "Trying to get the leaf at {:?}, but this tree is only {:?} long",
            from,
            M1::measure(self.summary()),
        );

        self.root.convert_measure(from)
    }

    /// # Panics
    ///
    /// This function will panic if the iterator is empty.
    #[inline]
    pub fn from_leaves<I>(leaves: I) -> Self
    where
        I: IntoIterator<Item = L>,
        I::IntoIter: ExactSizeIterator,
    {
        Self {
            root: Arc::new(Node::from_leaves(
                leaves.into_iter().map(Lnode::from),
            )),
        }
    }

    /// Returns the leaf at `measure` (0-indexed) together with its `M` offset.
    ///
    /// Note: this function doesn't do any bounds checks. Those are expected to
    /// be performed by the caller.
    #[inline]
    pub fn leaf_at_measure<M>(&self, measure: M) -> (&L::Slice, M)
    where
        M: Metric<L>,
    {
        // TODO: doesn't work for `LineMetric`

        debug_assert!(
            measure <= M::measure(self.summary()),
            "Trying to get the leaf at {:?}, but this tree is only {:?} long",
            measure,
            M::measure(self.summary()),
        );

        self.root.leaf_at_measure(measure)
    }

    #[inline]
    pub fn base_measure(&self) -> L::BaseMetric {
        self.measure::<L::BaseMetric>()
    }

    #[inline]
    pub fn measure<M: Metric<L>>(&self) -> M {
        M::measure(self.summary())
    }

    /// Returns an iterator over the leaves of this tree.
    #[inline]
    pub fn leaves(&self) -> Leaves<'_, FANOUT, L> {
        Leaves::from(self)
    }

    #[inline]
    pub(super) fn root(&self) -> &Arc<Node<FANOUT, L>> {
        &self.root
    }

    /// TODO: docs
    #[inline]
    pub fn slice<M>(&self, range: Range<M>) -> TreeSlice<'_, FANOUT, L>
    where
        M: Metric<L>,
        for<'d> &'d L::Slice: Default,
    {
        debug_assert!(M::zero() <= range.start);
        debug_assert!(range.start <= range.end);

        // TODO: doesn't work for `LineMetric`

        debug_assert!(range.end <= M::measure(self.summary()));

        TreeSlice::from_range_in_root(&self.root, range)
    }

    /// TODO: docs
    #[inline]
    pub fn summary(&self) -> &L::Summary {
        self.root.summary()
    }

    /// TODO: docs
    #[inline]
    pub fn units<M>(&self) -> Units<'_, FANOUT, L, M>
    where
        M: Metric<L>,
        for<'d> &'d L::Slice: Default,
    {
        Units::from(self)
    }
}

mod from_treeslice {
    //! Functions used to convert `TreeSlice`s into `Tree`s.

    use super::*;

    /// This is the only public function this module exports and it converts a
    /// `TreeSlice` into the root of an equivalent `Tree`.
    ///
    /// Note: the cases `tree_slice.num_leaves = 1 | 2` should be handled
    /// separately before calling this function.
    ///
    /// Note: this function can panic if the minimum number of children for an
    /// internal node is less than 2.
    #[inline]
    pub(super) fn into_tree_root<'a, const N: usize, L: Leaf>(
        slice: TreeSlice<'a, N, L>,
    ) -> Arc<Node<N, L>> {
        // println!("{slice:#?}");

        let (root, invalid_start, invalid_end) = tree_slice_cut(slice);

        let mut root = Arc::new(Node::Internal(root));

        // println!("START: {root:#?}");
        // println!("INVALID START: {invalid_start}");
        // println!("INVALID END: {invalid_end}");

        {
            // TODO: use `Arc::get_mut_unchecked` once it's stable.
            //
            // Safety (unwrap_unchecked): the `Arc` containing the root was
            // just created so there are no other copies.
            //
            // Safety (as_mut_internal_unchecked): `root` was just enclosed in
            // a `Node::Internal` variant.
            let inode = unsafe {
                Arc::get_mut(&mut root)
                    .unwrap_unchecked()
                    .as_mut_internal_unchecked()
            };

            if invalid_start > 0 {
                balance_left_side(inode);
                pull_up_singular(&mut root);
            }
        }

        {
            // TODO: use `Arc::get_mut_unchecked` once it's stable.
            //
            // Safety (unwrap_unchecked): see above.
            //
            // Safety (as_mut_internal_unchecked): for the root to become a
            // leaf node after the previous call to `pull_up_singular` the
            // TreeSlice would've had to span 2 leaves, and that case case
            // should have already been handled before calling this function.
            let inode = unsafe {
                Arc::get_mut(&mut root)
                    .unwrap_unchecked()
                    .as_mut_internal_unchecked()
            };

            if invalid_end > 0 {
                balance_right_side(inode);
                pull_up_singular(&mut root);
            }
        }

        // println!("FINAL ROOT: {root:#?}");

        root
    }

    /// TODO: docs
    #[inline]
    fn tree_slice_cut<const N: usize, L: Leaf>(
        slice: TreeSlice<'_, N, L>,
    ) -> (Inode<N, L>, usize, usize) {
        debug_assert!(slice.leaf_count() > 2);

        let mut root = Inode::empty();
        let mut invalid_nodes_start = 0;
        let mut invalid_nodes_end = 0;

        let mut offset = L::BaseMetric::zero();

        let mut children = {
            // Safety: the slice's leaf count is > 1 so its root has to be an
            // internal node.
            let root = unsafe { slice.root().as_internal_unchecked() };
            root.children().iter()
        };

        while let Some(child) = children.next() {
            let this = child.base_measure();

            if offset + this > slice.before {
                if slice.before == L::BaseMetric::zero() {
                    root.push(Arc::clone(child));
                } else {
                    let (first, _) = cut_start_rec(
                        child,
                        slice.before - offset,
                        slice.start_slice,
                        slice.start_summary.clone(),
                        &mut invalid_nodes_start,
                    );

                    root.push(first);
                }

                offset += this;
                break;
            } else {
                offset += this;
            }
        }

        let end = slice.before + slice.base_measure();

        while let Some(child) = children.next() {
            let this = child.base_measure();

            if offset + this >= end {
                if end == slice.root().base_measure() {
                    root.push(Arc::clone(child));
                } else {
                    let (last, _) = cut_end_rec(
                        child,
                        end - offset,
                        slice.end_slice,
                        slice.end_summary.clone(),
                        &mut invalid_nodes_end,
                    );

                    root.push(last);
                }

                break;
            } else {
                root.push(Arc::clone(child));
                offset += this;
            }
        }

        // println!("start has {invalid_nodes_start} invalid nodes");
        // println!("end has {invalid_nodes_end} invalid nodes");

        (root, invalid_nodes_start, invalid_nodes_end)
    }

    // TODO: don't give up that easily when `should_rebalance` is true. Most of
    // the time you're gonna have another node to use to rebalance the two. In
    // that case you can rebalance right away and return a None.
    #[inline]
    fn cut_start_rec<const N: usize, L: Leaf>(
        node: &Arc<Node<N, L>>,
        take_from: L::BaseMetric,
        start_slice: &L::Slice,
        start_summary: L::Summary,
        invalid_nodes: &mut usize,
    ) -> (Arc<Node<N, L>>, bool) {
        match &**node {
            Node::Internal(inode) => {
                let mut i = Inode::empty();

                let mut offset = L::BaseMetric::zero();

                let mut children = inode.children().iter();

                while let Some(child) = children.next() {
                    let this = child.base_measure();

                    if offset + this > take_from {
                        let (first_child, first_not_valid) = cut_start_rec(
                            child,
                            take_from - offset,
                            start_slice,
                            start_summary,
                            invalid_nodes,
                        );

                        i.push(first_child);

                        for child in children {
                            i.push(Arc::clone(child));
                        }

                        let this_not_valid = if first_not_valid {
                            if i.children().len() >= 2 {
                                *invalid_nodes -= 1;
                                i.balance_first_child_with_second()
                            } else {
                                true
                            }
                        } else {
                            !i.has_enough_children()
                        };

                        if this_not_valid {
                            *invalid_nodes += 1;
                        }

                        return (Arc::new(Node::Internal(i)), this_not_valid);
                    } else {
                        offset += this;
                    }
                }

                unreachable!();
            },

            Node::Leaf(_) => {
                let leaf = start_slice.to_owned();
                let lnode = Lnode::new(leaf, start_summary);
                let this_not_valid = !lnode.is_big_enough();

                if this_not_valid {
                    *invalid_nodes += 1;
                }

                (Arc::new(Node::Leaf(lnode)), this_not_valid)
            },
        }
    }

    #[inline]
    fn cut_end_rec<const N: usize, L: Leaf>(
        node: &Arc<Node<N, L>>,
        take_up_to: L::BaseMetric,
        end_slice: &L::Slice,
        end_summary: L::Summary,
        invalid_nodes: &mut usize,
    ) -> (Arc<Node<N, L>>, bool) {
        // println!("cutting up to {take_up_to:?} of {node:#?}");
        // println!("");

        match &**node {
            Node::Internal(inode) => {
                let mut i = Inode::empty();

                let mut offset = L::BaseMetric::zero();

                for child in inode.children() {
                    let this = child.base_measure();

                    if offset + this >= take_up_to {
                        let (last_child, last_not_valid) = cut_end_rec(
                            child,
                            take_up_to - offset,
                            end_slice,
                            end_summary,
                            invalid_nodes,
                        );

                        i.push(last_child);

                        let this_not_valid = if last_not_valid {
                            if i.children().len() >= 2 {
                                *invalid_nodes -= 1;
                                i.balance_last_child_with_penultimate()
                            } else {
                                true
                            }
                        } else {
                            !i.has_enough_children()
                        };

                        if this_not_valid {
                            *invalid_nodes += 1;
                        }

                        return (Arc::new(Node::Internal(i)), this_not_valid);
                    } else {
                        i.push(Arc::clone(child));
                        offset += this;
                    }
                }

                unreachable!();
            },

            Node::Leaf(_) => {
                let leaf = end_slice.to_owned();
                let lnode = Lnode::new(leaf, end_summary);
                let this_not_valid = !lnode.is_big_enough();

                if this_not_valid {
                    *invalid_nodes = 1;
                }

                (Arc::new(Node::Leaf(lnode)), this_not_valid)
            },
        }
    }

    #[inline]
    fn balance_left_side<const N: usize, L: Leaf>(
        inode: &mut Inode<N, L>,
    ) -> bool {
        let mut parent_should_rebalance =
            inode.balance_first_child_with_second();

        if let Node::Internal(first_child) = Arc::make_mut(inode.first_mut()) {
            let this_should_rebalance = balance_left_side(first_child);

            if this_should_rebalance {
                // NOTE: It's possible that after rebalancing, this inode was
                // left with only 1 child. When this is the case all of this
                // inode's parents will also have a single child, and the root
                // will be fixed by calling `pull_up_singular`.
                if inode.children().len() == 1 {
                    return false;
                }

                // NOTE: if the first call to `merge_distribute_first_second`
                // returned `true` it means the first and second children of
                // this inode were rebalanced, leaving the first child with at
                // least `Inode::min_children + 1` children, so calling
                // `balance_left_side` on the first child could not have
                // returrned `true`.
                //
                // Since it did, it must mean `parent_should_rebalance` was
                // false, which means we can use a simple `=` assignment
                // instead of `|=`.
                debug_assert!(!parent_should_rebalance);

                parent_should_rebalance =
                    inode.balance_first_child_with_second();
            }
        }

        parent_should_rebalance
    }

    #[inline]
    fn balance_right_side<const N: usize, L: Leaf>(
        inode: &mut Inode<N, L>,
    ) -> bool {
        let mut parent_should_rebalance =
            inode.balance_last_child_with_penultimate();

        if let Node::Internal(last_child) = Arc::make_mut(inode.last_mut()) {
            let this_should_rebalance = balance_right_side(last_child);

            if this_should_rebalance {
                // NOTE: see comment in `balance_left_side`.
                if inode.children().len() == 1 {
                    return false;
                }

                // NOTE: see other comment in `balance_left_side`.
                debug_assert!(!parent_should_rebalance);

                parent_should_rebalance =
                    inode.balance_last_child_with_penultimate();
            }
        }

        parent_should_rebalance
    }

    #[inline]
    fn pull_up_singular<const N: usize, L: Leaf>(root: &mut Arc<Node<N, L>>) {
        loop {
            // NOTE: if an internal node has a single child, the `Arc`
            // enclosing that node should have been created somewhere in this
            // module, which means its reference count is 1, which means it's
            // ok to unwrap after calling `get_mut`.
            if let Node::Internal(i) = Arc::get_mut(root).unwrap() {
                if i.children().len() == 1 {
                    let first = i.children.drain(..).next().unwrap();
                    *root = first;
                } else {
                    break;
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::ops::{AddAssign, SubAssign};

    use super::*;
    use crate::tree::Summarize;

    #[derive(Copy, Clone, Default, Debug, Eq, PartialEq)]
    pub struct Count {
        count: usize,
        leaves: usize,
    }

    impl<'a> AddAssign<&'a Self> for Count {
        fn add_assign(&mut self, rhs: &'a Self) {
            self.count += rhs.count;
            self.leaves += rhs.leaves;
        }
    }

    impl<'a> SubAssign<&'a Self> for Count {
        fn sub_assign(&mut self, rhs: &'a Self) {
            self.count -= rhs.count;
            self.leaves -= rhs.leaves;
        }
    }

    impl Summarize for usize {
        type Summary = Count;

        fn summarize(&self) -> Self::Summary {
            Count { count: *self, leaves: 1 }
        }
    }

    type LeavesMetric = usize;

    impl Metric<usize> for LeavesMetric {
        fn zero() -> Self {
            0
        }

        fn one() -> Self {
            1
        }

        fn measure(count: &Count) -> Self {
            count.leaves
        }
    }

    impl Leaf for usize {
        type BaseMetric = LeavesMetric;
        type Slice = Self;
    }

    #[test]
    fn easy() {
        let tree = Tree::<4, usize>::from_leaves(0..20);
        assert_eq!(190, tree.summary().count);
    }

    // #[test]
    // fn slice() {
    //     let tree = Tree::<4, usize>::from_leaves(0..20);
    //     assert_eq!(10, tree.slice(1..5).summary().count);
    // }
}
