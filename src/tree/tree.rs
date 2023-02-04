use std::ops::Range;
use std::sync::Arc;

use super::*;

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
        M1: SlicingMetric<L>,
        M2: Metric<L>,
    {
        debug_assert!(
            from <= self.measure::<M1>() + M1::one(),
            "Trying to convert {:?} into {}, but this Tree is only {:?} long",
            from,
            std::any::type_name::<M2>(),
            self.measure::<M1>(),
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
        M: SlicingMetric<L>,
        L::BaseMetric: SlicingMetric<L>,
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

    /// Converts a `TreeSlice` into the root of an equivalent `Tree`.
    ///
    /// NOTE: can only be called if the slice has a leaf count of at least 3.
    /// Leaf counts of 1 or 2 should be handled before calling this function.
    #[inline]
    pub(super) fn into_tree_root<const N: usize, L: Leaf>(
        slice: TreeSlice<'_, N, L>,
    ) -> Arc<Node<N, L>> {
        debug_assert!(slice.leaf_count() >= 3);

        let (root, invalid_in_first, invalid_in_last) = cut_tree_slice(slice);

        let mut root = Arc::new(Node::Internal(root));

        if invalid_in_first > 0 {
            {
                // Safety : `root` was just enclosed in a `Node::Internal`
                // variant.
                let root = unsafe {
                    Arc::get_mut(&mut root)
                        .unwrap()
                        .as_mut_internal_unchecked()
                };

                balance_first_rec(root);
            }

            pull_up_singular(&mut root);
        }

        if invalid_in_last > 0 {
            {
                // Safety (as_mut_internal_unchecked): for the root to become a
                // leaf node after the previous call to `pull_up_singular` the
                // TreeSlice would've had to span 2 leaves, and that case case
                // should have already been handled before calling this
                // function.
                let root = unsafe {
                    Arc::get_mut(&mut root)
                        .unwrap()
                        .as_mut_internal_unchecked()
                };

                balance_last_rec(root);
            }

            pull_up_singular(&mut root);
        }

        root
    }

    /// Returns a `(Root, InvalidFirst, InvalidLast)` tuple where:
    ///
    /// - `Root`: the internal node obtained by removing all the nodes before
    /// `slice.before` and after `slice.before + slice.base_measure`,
    ///
    /// - `Invalid{First,Last}`: the number of invalid nodes contained in the
    /// subtree of the first and last child, respectively.
    ///
    /// NOTE: this function can only be called if the slice has a leaf count of
    /// at least 3.
    ///
    /// NOTE: `Root` is guaranteed to have the same depth as the root of the
    /// slice.
    ///
    /// NOTE: `Root` is guaranteed to have at least 2 children.
    ///
    /// NOTE: both `InvalidFirst` and `InvalidLast` are guaranteed to be less
    /// than or equal to the depth of `Root`.
    ///
    /// NOTE: the `Arc` enclosing the first and last children all the way to
    /// the bottom of the inode are guaranteed to have a strong count of 1, so
    /// it's ok to call `Arc::get_mut` on them. The nodes in the middle will
    /// usually be `Arc::clone`d from the slice.
    #[inline]
    fn cut_tree_slice<const N: usize, L: Leaf>(
        slice: TreeSlice<'_, N, L>,
    ) -> (Inode<N, L>, usize, usize) {
        debug_assert!(slice.leaf_count() >= 3);

        let mut root = Inode::empty();
        let mut invalid_first = 0;
        let mut invalid_last = 0;

        let mut offset = L::BaseMetric::zero();

        let mut children = {
            // Safety: the slice's leaf count is > 1 so its root has to be an
            // internal node.
            let root = unsafe { slice.root().as_internal_unchecked() };
            root.children().iter()
        };

        let start = L::BaseMetric::measure(&slice.offset);

        while let Some(child) = children.next() {
            let this = child.base_measure();

            if offset + this > start {
                if start == L::BaseMetric::zero() {
                    root.push(Arc::clone(child));
                } else {
                    let first = cut_first_rec(
                        child,
                        start - offset,
                        slice.start_slice,
                        slice.start_summary.clone(),
                        &mut invalid_first,
                    );

                    root.push(first);
                }

                offset += this;
                break;
            } else {
                offset += this;
            }
        }

        let end = start + slice.base_measure();

        while let Some(child) = children.next() {
            let this = child.base_measure();

            if offset + this >= end {
                if end == slice.root().base_measure() {
                    root.push(Arc::clone(child));
                } else {
                    let last = cut_last_rec(
                        child,
                        end - offset,
                        slice.end_slice,
                        slice.end_summary.clone(),
                        &mut invalid_last,
                    );

                    root.push(last);
                }

                break;
            } else {
                root.push(Arc::clone(child));
                offset += this;
            }
        }

        (root, invalid_first, invalid_last)
    }

    #[inline]
    fn cut_first_rec<const N: usize, L: Leaf>(
        node: &Arc<Node<N, L>>,
        take_from: L::BaseMetric,
        start_slice: &L::Slice,
        start_summary: L::Summary,
        invalid_nodes: &mut usize,
    ) -> Arc<Node<N, L>> {
        match &**node {
            Node::Internal(i) => {
                let mut inode = Inode::empty();

                let mut offset = L::BaseMetric::zero();

                let mut children = i.children().iter();

                while let Some(child) = children.next() {
                    let this = child.base_measure();

                    if offset + this > take_from {
                        let first = cut_first_rec(
                            child,
                            take_from - offset,
                            start_slice,
                            start_summary,
                            invalid_nodes,
                        );

                        let first_is_valid = first.is_valid();

                        inode.push(first);

                        for child in children {
                            inode.push(Arc::clone(child));
                        }

                        if !first_is_valid && inode.children().len() > 1 {
                            inode.balance_first_child_with_second();
                            *invalid_nodes -= 1;
                        }

                        if !inode.has_enough_children() {
                            *invalid_nodes += 1;
                        }

                        return Arc::new(Node::Internal(inode));
                    } else {
                        offset += this;
                    }
                }

                unreachable!();
            },

            Node::Leaf(_) => {
                let lnode = Lnode::new(start_slice.to_owned(), start_summary);

                if !lnode.is_big_enough() {
                    *invalid_nodes += 1;
                }

                Arc::new(Node::Leaf(lnode))
            },
        }
    }

    #[inline]
    fn cut_last_rec<const N: usize, L: Leaf>(
        node: &Arc<Node<N, L>>,
        take_up_to: L::BaseMetric,
        end_slice: &L::Slice,
        end_summary: L::Summary,
        invalid_nodes: &mut usize,
    ) -> Arc<Node<N, L>> {
        match &**node {
            Node::Internal(i) => {
                let mut inode = Inode::empty();

                let mut offset = L::BaseMetric::zero();

                for child in i.children() {
                    let this = child.base_measure();

                    if offset + this >= take_up_to {
                        let last = cut_last_rec(
                            child,
                            take_up_to - offset,
                            end_slice,
                            end_summary,
                            invalid_nodes,
                        );

                        let last_is_valid = last.is_valid();

                        inode.push(last);

                        if !last_is_valid && inode.children().len() > 1 {
                            inode.balance_last_child_with_penultimate();
                            *invalid_nodes -= 1;
                        }

                        if !inode.has_enough_children() {
                            *invalid_nodes += 1;
                        }

                        return Arc::new(Node::Internal(inode));
                    } else {
                        inode.push(Arc::clone(child));
                        offset += this;
                    }
                }

                unreachable!();
            },

            Node::Leaf(_) => {
                let lnode = Lnode::new(end_slice.to_owned(), end_summary);

                if !lnode.is_big_enough() {
                    *invalid_nodes = 1;
                }

                Arc::new(Node::Leaf(lnode))
            },
        }
    }

    /// Recursively balances the first child all the way down to the deepest
    /// inode.
    ///
    /// # Panics
    ///
    /// Panics if the `Arc` enclosing the first child has a strong counter > 1.
    #[inline]
    fn balance_first_rec<const N: usize, L: Leaf>(inode: &mut Inode<N, L>) {
        inode.balance_first_child_with_second();

        if let Node::Internal(first) = Arc::get_mut(inode.first_mut()).unwrap()
        {
            balance_first_rec(first);

            if !first.has_enough_children() && inode.children().len() > 1 {
                inode.balance_first_child_with_second();
            }
        }
    }

    /// Recursively balances the last child all the way down to the deepest
    /// inode.
    ///
    /// # Panics
    ///
    /// Panics if the `Arc` enclosing the last child has a strong counter > 1.
    #[inline]
    fn balance_last_rec<const N: usize, L: Leaf>(inode: &mut Inode<N, L>) {
        inode.balance_last_child_with_penultimate();

        if let Node::Internal(last) = Arc::get_mut(inode.last_mut()).unwrap() {
            balance_last_rec(last);

            if !last.has_enough_children() && inode.children().len() > 1 {
                inode.balance_last_child_with_penultimate();
            }
        }
    }

    /// Continuously replaces the root with its first child as long as the root
    /// is an internal node with a single child.
    ///
    /// # Panics
    ///
    /// Panics if the `Arc` enclosing the root has a strong counter > 1.
    #[inline]
    fn pull_up_singular<const N: usize, L: Leaf>(root: &mut Arc<Node<N, L>>) {
        while let Node::Internal(i) = Arc::get_mut(root).unwrap() {
            if i.children().len() == 1 {
                let child = unsafe {
                    i.children
                        .drain(..)
                        .next()
                        // SAFETY: there is exactly 1 child.
                        .unwrap_unchecked()
                };
                *root = child;
            } else {
                break;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::ops::{Add, AddAssign, Sub, SubAssign};

    use super::*;
    use crate::tree::Summarize;

    #[derive(Copy, Clone, Default, Debug, Eq, PartialEq)]
    pub struct Count {
        count: usize,
        leaves: usize,
    }

    impl Add<&Self> for Count {
        type Output = Self;

        #[inline]
        fn add(self, rhs: &Self) -> Self {
            Count {
                count: self.count + rhs.count,
                leaves: self.leaves + rhs.leaves,
            }
        }
    }

    impl Sub<&Self> for Count {
        type Output = Self;

        #[inline]
        fn sub(self, rhs: &Self) -> Self {
            Count {
                count: self.count - rhs.count,
                leaves: self.leaves - rhs.leaves,
            }
        }
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
