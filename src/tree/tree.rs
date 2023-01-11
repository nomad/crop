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
    fn from(tree_slice: TreeSlice<'a, FANOUT, L>) -> Tree<FANOUT, L> {
        let root = if L::BaseMetric::measure(tree_slice.summary())
            == L::BaseMetric::measure(tree_slice.root.summary())
        {
            // If the TreeSlice and its root have the same base measure it
            // means the TreeSlice spanned the whole Tree from which it was
            // created from and we can simply clone the root.
            Arc::clone(tree_slice.root)
        } else {
            match tree_slice.num_leaves {
                1 => {
                    debug_assert!(tree_slice.root.is_leaf());

                    Arc::new(Node::Leaf(Lnode::new(
                        tree_slice.start_slice.to_owned(),
                        tree_slice.summary,
                    )))
                },

                2 => {
                    let (first, second) = L::balance_slices(
                        (tree_slice.start_slice, &tree_slice.start_summary),
                        (tree_slice.end_slice, &tree_slice.end_summary),
                    );

                    let first = Arc::new(Node::Leaf(Lnode::from(first)));

                    if let Some(second) = second {
                        let second = Arc::new(Node::Leaf(Lnode::from(second)));
                        let root = Inode::from_children([first, second]);
                        Arc::new(Node::Internal(root))
                    } else {
                        first
                    }
                },

                _ => from_treeslice::into_tree_root(tree_slice),
            }
        };

        let tree = Tree { root };

        // #[cfg(debug_assertions)]
        // tree.assert_invariants();

        tree
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

    /// Returns an iterator over the leaves of this tree.
    #[inline]
    pub fn leaves(&self) -> Leaves<'_, FANOUT, L> {
        Leaves::from(self)
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
        tree_slice: TreeSlice<'a, N, L>,
    ) -> (Inode<N, L>, bool, bool) {
        let mut inode = Inode::empty();

        let mut measured = L::BaseMetric::zero();

        let mut found_start = false;

        let start = L::BaseMetric::measure(&tree_slice.before);

        let end = start + L::BaseMetric::measure(tree_slice.summary());

        // Safety: if the TreeSlice's root was a leaf it would only have had a
        // single leaf, but this function can only be called if the TreeSlice
        // spans 3+ leaves.
        let root = unsafe { tree_slice.root.as_internal_unchecked() };

        let mut balance_left = true;

        let mut balance_right = true;

        for node in root.children() {
            let size = L::BaseMetric::measure(node.summary());

            if !found_start {
                if measured + size > start {
                    if start > L::BaseMetric::zero() {
                        inode.push(something_start_rec(
                            &**node,
                            start - measured,
                            tree_slice.start_slice,
                            tree_slice.start_summary.clone(),
                        ));
                    } else {
                        inode.push(Arc::clone(node));
                        balance_left = false;
                    }
                    found_start = true;
                }
                measured += size;
            } else if measured + size >= end {
                if end < L::BaseMetric::measure(tree_slice.root.summary()) {
                    inode.push(something_end_rec(
                        &**node,
                        end - measured,
                        tree_slice.end_slice,
                        tree_slice.end_summary.clone(),
                    ));
                } else {
                    inode.push(Arc::clone(node));
                    balance_right = false;
                }
                break;
            } else {
                inode.push(Arc::clone(node));
                measured += size;
            }
        }

        (inode, balance_left, balance_right)
    }

    #[inline]
    fn something_start_rec<'a, const N: usize, L: Leaf>(
        node: &Node<N, L>,
        from: L::BaseMetric,
        start_slice: &'a L::Slice,
        start_summary: L::Summary,
    ) -> Arc<Node<N, L>> {
        match node {
            Node::Internal(inode) => {
                let mut measured = L::BaseMetric::zero();

                let mut i = Inode::empty();

                let mut children = inode.children().iter();

                while let Some(child) = children.next() {
                    let this = L::BaseMetric::measure(child.summary());

                    if measured + this > from {
                        i.push(something_start_rec(
                            child,
                            from - measured,
                            start_slice,
                            start_summary,
                        ));

                        for child in children {
                            i.push(Arc::clone(child));
                        }

                        break;
                    } else {
                        measured += this;
                    }
                }

                Arc::new(Node::Internal(i))
            },

            Node::Leaf(_) => Arc::new(Node::Leaf(Lnode::new(
                start_slice.to_owned(),
                start_summary,
            ))),
        }
    }

    #[inline]
    fn something_end_rec<'a, const N: usize, L: Leaf>(
        node: &Node<N, L>,
        up_to: L::BaseMetric,
        end_slice: &'a L::Slice,
        end_summary: L::Summary,
    ) -> Arc<Node<N, L>> {
        match node {
            Node::Internal(inode) => {
                let mut measured = L::BaseMetric::zero();

                let mut i = Inode::empty();

                let mut children = inode.children().iter();

                while let Some(child) = children.next() {
                    let this = L::BaseMetric::measure(child.summary());

                    if measured + this >= up_to {
                        i.push(something_end_rec(
                            child,
                            up_to - measured,
                            end_slice,
                            end_summary,
                        ));

                        break;
                    } else {
                        i.push(Arc::clone(child));
                        measured += this;
                    }
                }

                Arc::new(Node::Internal(i))
            },

            Node::Leaf(_) => Arc::new(Node::Leaf(Lnode::new(
                end_slice.to_owned(),
                end_summary,
            ))),
        }
    }

    #[inline]
    fn balance_left_side<const N: usize, L: Leaf>(
        inode: &mut Inode<N, L>,
    ) -> bool {
        let mut parent_should_rebalance = merge_distribute_first_second(inode);

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

                parent_should_rebalance = merge_distribute_first_second(inode);
            }
        }

        parent_should_rebalance
    }

    #[inline]
    fn balance_right_side<const N: usize, L: Leaf>(
        inode: &mut Inode<N, L>,
    ) -> bool {
        let mut parent_should_rebalance =
            merge_distribute_penultimate_last(inode);

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
                    merge_distribute_penultimate_last(inode);
            }
        }

        parent_should_rebalance
    }

    #[inline]
    fn merge_distribute_first_second<const N: usize, L: Leaf>(
        inode: &mut Inode<N, L>,
    ) -> bool {
        let (first, second) = inode.two_mut(0, 1);

        match Arc::make_mut(first) {
            Node::Internal(first) => {
                if first.children().len() >= Inode::<N, L>::min_children() {
                    return false;
                }

                // Safety: the first child is an internal node, so the second
                // child is also an internal node.
                let sec = unsafe { second.as_internal_unchecked() };

                // If the first and second children can be combined we can
                // avoid calling `Arc::make_mut` on the second child, we can
                // instead pop it and append its children to the first node.
                if first.children().len() + sec.children().len()
                    <= Inode::<N, L>::max_children()
                {
                    first.extend_from_other(sec);
                    inode.pop(1);
                }
                // If not, we move the minimum number of nodes needed to make
                // the first child valid from the second to the first child.
                // This is guaranteed to leave the second node valid because..
                else {
                    let second = unsafe { second.as_internal_unchecked() };

                    let to_move =
                        Inode::<N, L>::min_children() - first.children().len();

                    let (move_to_first, keep_in_second) =
                        second.children().split_at(to_move);

                    first.extend(move_to_first.iter().map(Arc::clone));

                    let new_second =
                        Arc::new(Node::Internal(Inode::from_children(
                            keep_in_second.iter().map(Arc::clone),
                        )));

                    inode.swap(1, new_second);

                    return false;
                }
            },

            Node::Leaf(first) => {
                if first.is_big_enough() {
                    return false;
                }

                // Safety: the first child is a leaf node, so the second child
                // is also a leaf node.
                let sec = unsafe { second.as_leaf_unchecked() };

                let (frt, sec) = L::balance_slices(
                    (first.as_slice(), first.summary()),
                    (sec.as_slice(), sec.summary()),
                );

                *first = Lnode::from(frt);

                if let Some(sec) = sec {
                    inode.swap(1, Arc::new(Node::Leaf(Lnode::from(sec))));
                    return false;
                } else {
                    inode.pop(1);
                }
            },
        }

        // The parent should only rebalance if after removing the second child
        // this inode has less than the minimum number of children.
        inode.children().len() < Inode::<N, L>::min_children()
    }

    #[inline]
    fn merge_distribute_penultimate_last<const N: usize, L: Leaf>(
        inode: &mut Inode<N, L>,
    ) -> bool {
        let last_idx = inode.children().len() - 1;

        let (penultimate, last) = inode.two_mut(last_idx - 1, last_idx);

        match Arc::make_mut(last) {
            Node::Internal(last) => {
                if last.children().len() >= Inode::<N, L>::min_children() {
                    return false;
                }

                // Safety: the last child is an internal node, so the
                // penultimate child is also an internal node.
                let pen = unsafe { penultimate.as_internal_unchecked() };

                // If the penultimate and last children can be combined we can
                // avoid calling `Arc::make_mut` on the penultimate child, we
                // can instead pop it and append its children to the last node.
                if last.children().len() + pen.children().len()
                    <= Inode::<N, L>::max_children()
                {
                    last.prepend_from_other(pen);
                    inode.pop(last_idx - 1);
                }
                // If not, we move the minimum number of nodes needed to make
                // the first child valid from the penultimate to the first
                // child. This is guaranteed to leave the penultimate node
                // valid because..
                else {
                    let penultimate =
                        unsafe { penultimate.as_internal_unchecked() };

                    let to_move =
                        Inode::<N, L>::min_children() - last.children().len();

                    let (keep_in_penultimate, move_to_last) = penultimate
                        .children()
                        .split_at(penultimate.children().len() - to_move);

                    let new_penultimate =
                        Arc::new(Node::Internal(Inode::from_children(
                            keep_in_penultimate.iter().map(Arc::clone),
                        )));

                    last.prepend(move_to_last.iter().map(Arc::clone));

                    inode.swap(last_idx - 1, new_penultimate);

                    return false;
                }
            },

            Node::Leaf(last) => {
                if last.is_big_enough() {
                    return false;
                }

                // Safety: the first child is a leaf node, so the second child
                // is also a leaf node.
                let pen = unsafe { penultimate.as_leaf_unchecked() };

                // TODO: refactor all this, this is garbage.

                let (left, right) = L::balance_slices(
                    (pen.as_slice(), pen.summary()),
                    (last.as_slice(), last.summary()),
                );

                if let Some(right) = right {
                    *last = Lnode::from(right);
                    inode.swap(
                        last_idx - 1,
                        Arc::new(Node::Leaf(Lnode::from(left))),
                    );
                    return false;
                } else {
                    *last = Lnode::from(left);
                    inode.pop(last_idx - 1);
                }
            },
        }

        // The parent should only rebalance if after removing the penultimate
        // child this inode has less than the minimum number of children.
        inode.children().len() < Inode::<N, L>::min_children()
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
