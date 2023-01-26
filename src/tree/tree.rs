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

    // TODO: don't give up that easily when `should_rebalance` is true. Most of
    // the time you're gonna have another node to use to rebalance the two. In
    // that case you can rebalance right away and return a None.
    #[inline]
    fn cut_start_rec<const N: usize, L: Leaf>(
        node: &Arc<Node<N, L>>,
        take_from: L::BaseMetric,
        start_slice: &L::Slice,
        start_summary: L::Summary,
    ) -> (Arc<Node<N, L>>, bool) {
        match &**node {
            Node::Internal(inode) => {
                let mut offset = L::BaseMetric::zero();

                let mut i = Inode::empty();

                let mut children = inode.children().iter();

                let mut should_rebalance = false;

                while let Some(child) = children.next() {
                    let this = child.base_measure();

                    if offset + this > take_from {
                        let (first_child, rebalance) = cut_start_rec(
                            child,
                            take_from - offset,
                            start_slice,
                            start_summary,
                        );

                        should_rebalance |= rebalance;

                        i.push(first_child);

                        for child in children {
                            i.push(Arc::clone(child));
                        }

                        break;
                    } else {
                        offset += this;
                    }
                }

                should_rebalance |= !i.has_enough_children();
                (Arc::new(Node::Internal(i)), should_rebalance)
            },

            Node::Leaf(_) => {
                let leaf = start_slice.to_owned();
                let lnode = Lnode::new(leaf, start_summary);
                let should_rebalance = !lnode.is_big_enough();
                (Arc::new(Node::Leaf(lnode)), should_rebalance)
            },
        }
    }

    #[inline]
    fn cut_end_rec<const N: usize, L: Leaf>(
        node: &Arc<Node<N, L>>,
        take_up_to: L::BaseMetric,
        end_slice: &L::Slice,
        end_summary: L::Summary,
    ) -> (Arc<Node<N, L>>, bool) {
        match &**node {
            Node::Internal(inode) => {
                let mut offset = L::BaseMetric::zero();

                let mut i = Inode::empty();

                let mut children = inode.children().iter();

                let mut should_rebalance = false;

                while let Some(child) = children.next() {
                    let this = child.base_measure();

                    if offset + this >= take_up_to {
                        let (last_child, rebalance) = cut_end_rec(
                            child,
                            take_up_to - offset,
                            end_slice,
                            end_summary,
                        );

                        should_rebalance |= rebalance;

                        i.push(last_child);

                        break;
                    } else {
                        i.push(Arc::clone(child));
                        offset += this;
                    }
                }

                should_rebalance |= !i.has_enough_children();
                (Arc::new(Node::Internal(i)), should_rebalance)
            },

            Node::Leaf(_) => {
                let leaf = end_slice.to_owned();
                let should_rebalance = !leaf.is_big_enough(&end_summary);
                let lnode = Lnode::new(leaf, end_summary);
                (Arc::new(Node::Leaf(lnode)), should_rebalance)
            },
        }
    }

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
        tree_slice: TreeSlice<'a, N, L>,
    ) -> Arc<Node<N, L>> {
        let (root, balance_left, balance_right) =
            remove_before_and_after(tree_slice);

        let mut root = Arc::new(Node::Internal(root));

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

            if balance_left {
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

            if balance_right {
                balance_right_side(inode);
                pull_up_singular(&mut root);
            }
        }

        root
    }

    /// TODO: docs
    #[inline]
    fn remove_before_and_after<'a, const N: usize, L: Leaf>(
        slice: TreeSlice<'a, N, L>,
    ) -> (Inode<N, L>, bool, bool) {
        let mut inode = Inode::empty();

        let mut measured = L::BaseMetric::zero();

        let mut found_start = false;

        let start = slice.before;

        let end = start + slice.base_measure();

        // Safety: if the TreeSlice's root was a leaf it would only have had a
        // single leaf, but this function can only be called if the TreeSlice
        // spans 3+ leaves.
        let root = unsafe { slice.root.as_internal_unchecked() };

        let mut balance_left = true;

        let mut balance_right = true;

        for node in root.children() {
            let this = node.base_measure();

            if !found_start {
                if measured + this > start {
                    if start > L::BaseMetric::zero() {
                        let (first, balance) = cut_start_rec(
                            node,
                            start - measured,
                            slice.start_slice,
                            slice.start_summary.clone(),
                        );
                        inode.push(first);
                        balance_left = balance;
                    } else {
                        inode.push(Arc::clone(node));
                        balance_left = false;
                    }
                    found_start = true;
                }
                measured += this;
            } else if measured + this >= end {
                if end < slice.root().base_measure() {
                    let (last, balance) = cut_end_rec(
                        node,
                        end - measured,
                        slice.end_slice,
                        slice.end_summary.clone(),
                    );
                    inode.push(last);
                    balance_right = balance;
                } else {
                    inode.push(Arc::clone(node));
                    balance_right = false;
                }
                break;
            } else {
                inode.push(Arc::clone(node));
                measured += this;
            }
        }

        // println!("should balance start: {balance_left}");
        // println!("should balance end: {balance_right}");

        (inode, balance_left, balance_right)
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
