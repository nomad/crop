use std::ops::Range;
use std::sync::Arc;

use super::*;

/// A self-balancing tree with metadata stored in each node.
#[derive(Default)]
pub struct Tree<const FANOUT: usize, L: Leaf> {
    pub(super) root: Arc<Node<FANOUT, L>>,
}

impl<const FANOUT: usize, L: Leaf> Clone for Tree<FANOUT, L> {
    #[inline]
    fn clone(&self) -> Self {
        Tree { root: Arc::clone(&self.root) }
    }
}

impl<const FANOUT: usize, L: Leaf> std::fmt::Debug for Tree<FANOUT, L> {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        if !f.alternate() {
            f.debug_struct("Tree").field("root", &self.root).finish()
        } else {
            write!(f, "{:#?}", self.root)
        }
    }
}

impl<const FANOUT: usize, L: BalancedLeaf> From<TreeSlice<'_, FANOUT, L>>
    for Tree<FANOUT, L>
{
    #[inline]
    fn from(slice: TreeSlice<'_, FANOUT, L>) -> Tree<FANOUT, L> {
        let root = if slice.base_measure() == slice.root().base_measure() {
            // If the TreeSlice and its root have the same base measure it
            // means the TreeSlice spanned the whole Tree from which it was
            // created and we can simply clone the root.
            Arc::clone(slice.root())
        } else if slice.leaf_count() == 1 {
            debug_assert!(slice.root().is_leaf());

            Arc::new(Node::Leaf(Lnode::new(
                slice.first_slice.to_owned(),
                slice.summary,
            )))
        } else if slice.leaf_count() == 2 {
            let (first, second) = L::balance_slices(
                (slice.first_slice, &slice.first_summary),
                (slice.last_slice, &slice.last_summary),
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
    #[doc(hidden)]
    pub fn assert_invariants(&self) {
        match &*self.root {
            Node::Internal(root) => {
                // The root is the only inode that can have as few as 2
                // children.
                assert!(root.len() >= 2 && root.len() <= FANOUT);

                for child in root.children() {
                    child.assert_invariants()
                }
            },

            Node::Leaf(leaf) => leaf.assert_invariants(),
        }
    }

    /// Returns the base measure of this `Tree` obtained by summing up the
    /// base measures of all its leaves.
    #[inline]
    pub fn base_measure(&self) -> L::BaseMetric {
        self.measure::<L::BaseMetric>()
    }

    /// Returns the `M2`-measure of all the leaves before `up_to` plus the
    /// `M2`-measure of the left sub-slice of the leaf at `up_to`.
    ///
    /// NOTE: this function doesn't do any bounds checks.
    #[inline]
    pub fn convert_measure<M1, M2>(&self, up_to: M1) -> M2
    where
        M1: SlicingMetric<L>,
        M2: Metric<L>,
    {
        debug_assert!(up_to <= self.measure::<M1>() + M1::one(),);
        self.root.convert_measure(up_to)
    }

    /// Creates a new `Tree` from a sequence of leaves.
    ///
    /// NOTE: if the iterator doesn't yield any items the `Tree` will contain a
    /// single leaf with its default value.
    #[inline]
    pub fn from_leaves<I>(leaves: I) -> Self
    where
        I: IntoIterator<Item = L>,
        L: Default,
    {
        let mut leaves =
            leaves.into_iter().map(Lnode::from).map(Node::Leaf).map(Arc::new);

        let Some(first) = leaves.next() else { return Self::default() };

        let Some(second) = leaves.next() else { return Self { root: first } };

        let leaves = {
            let (lo, hi) = leaves.size_hint();
            let mut l = Vec::with_capacity(2 + hi.unwrap_or(lo));
            l.push(first);
            l.push(second);
            l.extend(leaves);
            l
        };

        let root = Inode::from_nodes(leaves);

        Self { root: Arc::new(Node::Internal(root)) }
    }

    /// Returns the leaf containing the `measure`-th unit of the `M`-metric,
    /// plus the `M`-measure of all the leaves before it.
    ///
    /// NOTE: this function doesn't do any bounds checks.
    #[inline]
    pub fn leaf_at_measure<M>(&self, measure: M) -> (&L::Slice, M)
    where
        M: Metric<L>,
    {
        debug_assert!(measure <= self.measure::<M>() + M::one());

        self.root.leaf_at_measure(measure)
    }

    #[inline]
    pub fn leaf_count(&self) -> usize {
        self.root.leaf_count()
    }

    /// Returns an iterator over the leaves of this `Tree`.
    #[inline]
    pub fn leaves(&self) -> Leaves<'_, FANOUT, L> {
        Leaves::from(self)
    }

    /// Returns the `M`-measure of this `Tree` obtaining by summing up the
    /// `M`-measures of all its leaves.
    #[inline]
    pub fn measure<M: Metric<L>>(&self) -> M {
        M::measure(self.summary())
    }

    /// TODO: docs
    #[inline]
    pub fn replace<M>(&mut self, range: Range<M>, slice: &L::Slice)
    where
        M: Metric<L>,
        L: ReplaceableLeaf<M> + Clone,
    {
        if let Some(extras) =
            tree_replace::some_name(&mut self.root, range, slice)
        {
            debug_assert!(extras
                .iter()
                .all(|n| n.depth() == self.root.depth()));

            let old_root = {
                let dummy = unsafe {
                    std::mem::transmute::<_, Arc<Node<FANOUT, L>>>(&())
                };

                std::mem::replace(&mut self.root, dummy)
            };

            let new_root = Arc::new(Node::Internal(Inode::from_nodes(
                std::iter::once(old_root).exact_chain(extras),
            )));

            let dummy = std::mem::replace(&mut self.root, new_root);

            std::mem::forget(dummy);
        }
    }

    #[inline]
    pub(super) fn root(&self) -> &Arc<Node<FANOUT, L>> {
        &self.root
    }

    /// Returns a slice of the `Tree` in the range of the given metric.
    #[inline]
    pub fn slice<M>(&self, range: Range<M>) -> TreeSlice<'_, FANOUT, L>
    where
        M: SlicingMetric<L>,
        L::BaseMetric: SlicingMetric<L>,
        for<'d> &'d L::Slice: Default,
    {
        debug_assert!(M::zero() <= range.start);
        debug_assert!(range.start <= range.end);
        debug_assert!(range.end <= self.measure::<M>() + M::one());

        TreeSlice::from_range_in_root(&self.root, range)
    }

    #[inline]
    pub fn summary(&self) -> &L::Summary {
        self.root.summary()
    }

    /// Returns an iterator over the `M`-units of this `Tree`.
    #[inline]
    pub fn units<M>(&self) -> Units<'_, FANOUT, L, M>
    where
        M: Metric<L>,
        for<'d> &'d L::Slice: Default,
    {
        Units::from(self)
    }
}

mod tree_replace {
    //! This module handles the logic used in [`Tree::replace()`].

    use super::*;

    /// This is recursive.
    ///
    /// TODO: docs
    #[inline]
    pub(super) fn some_name<const N: usize, M, L>(
        node: &mut Arc<Node<N, L>>,
        mut range: Range<M>,
        slice: &L::Slice,
    ) -> Option<Vec<Arc<Node<N, L>>>>
    where
        M: Metric<L>,
        L: ReplaceableLeaf<M> + Clone,
    {
        let Node::Internal(inode) = Arc::make_mut(node) else {
            return do_stuff_with_deepest(node, range, slice)
        };

        // The index of the child containing the entire replacement range.
        let mut child_idx = 0;

        let mut extras = None;

        let mut offset = M::zero();

        for (idx, child) in inode.children().iter().enumerate() {
            let child_measure = child.measure::<M>();

            offset += child_measure;

            if offset >= range.start {
                if offset >= range.end {
                    child_idx = idx;

                    extras = inode.with_child_mut(idx, |child| {
                        offset -= child_measure;
                        range.start -= offset;
                        range.end -= offset;
                        some_name(child, range, slice)
                    });

                    break;
                } else {
                    return do_stuff_with_deepest(node, range, slice);
                };
            }
        }

        let child = inode.child(child_idx);

        // Case 1: there are some extra child nodes to insert *after* the child
        // containing the replacement range.
        if let Some(extras) = extras {
            debug_assert!(extras
                .iter()
                .all(|n| n.depth() == inode.depth() - 1));

            inode.insert_children(child_idx + 1, extras).map(|extras| {
                extras.map(Node::Internal).map(Arc::new).collect()
            })
        }
        // Case 2: the child stayed at the same depth but it's now underfilled
        // and needs to be rebalanced with another child.
        else if child.depth() == inode.depth() - 1 && child.is_underfilled()
        {
            if child_idx > 0 {
                inode.balance_two_children(child_idx - 1, child_idx);
            } else {
                inode.balance_two_children(0, 1);
            }

            Node::replace_with_single_child(node);

            None
        }
        // Case 3: the child is now at a lower depth than its siblings and
        // needs to be appended/prepended to another child.
        else if child.depth() < inode.depth() - 1 {
            debug_assert!(inode.depth() >= 2);

            let child = inode.remove(child_idx);

            if child_idx > 0 {
                let extra = inode.with_child_mut(child_idx - 1, |previous| {
                    let previous = Arc::make_mut(previous);

                    // SAFETY: the inode's depth is >= 2 so its children are
                    // also inodes.
                    let previous =
                        unsafe { previous.as_mut_internal_unchecked() };

                    previous.append_at_depth(child)
                });

                if let Some(extra) = extra {
                    inode.insert(child_idx, Arc::new(Node::Internal(extra)));
                }
            } else {
                let extra = inode.with_child_mut(0, |first| {
                    let first = Arc::make_mut(first);

                    // SAFETY: the inode's depth is >= 2 so its children are
                    // also inodes.
                    let first = unsafe { first.as_mut_internal_unchecked() };

                    first.prepend_at_depth(child)
                });

                if let Some(extra) = extra {
                    inode.insert(0, Arc::new(Node::Internal(extra)));
                }
            }

            None
        }
        // Case 4: none of the above, the child is well balanced and we can
        // simply return.
        else {
            debug_assert!(child.depth() == inode.depth() - 1);
            debug_assert!(!child.is_underfilled());

            None
        }
    }

    /// This is not recursive. The only the code that handles the first final
    /// branches are.
    ///
    /// Returns a vector of nodes that should be pushed back onto the Tree
    /// after this node.
    ///
    /// TODO: docs
    #[inline]
    fn do_stuff_with_deepest<const N: usize, M, L>(
        node: &mut Arc<Node<N, L>>,
        range: Range<M>,
        slice: &L::Slice,
    ) -> Option<Vec<Arc<Node<N, L>>>>
    where
        M: Metric<L>,
        L: ReplaceableLeaf<M> + Clone,
    {
        let inode = match Arc::make_mut(node) {
            Node::Internal(inode) => inode,

            Node::Leaf(leaf) => {
                return leaf.replace(range, slice).map(|extras| {
                    extras.map(Node::Leaf).map(Arc::new).collect()
                });
            },
        };

        // The index of the child containing the start of the replacement
        // range.
        let mut start_idx = 0;

        // The index of the child containing the end of the replacement range.
        let mut end_idx = 0;

        let mut extra_leaves = None;

        let mut start_should_rebalance = false;

        let mut end_should_rebalance = false;

        let mut offset = M::zero();

        let mut indexes = 0..inode.len();

        for (idx, child) in indexes.by_ref().map(|idx| (idx, inode.child(idx)))
        {
            let child_measure = child.measure::<M>();

            offset += child_measure;

            if offset >= range.start {
                start_idx = idx;

                extra_leaves = inode.with_child_mut(start_idx, |child| {
                    replace_first_rec(
                        Arc::make_mut(child),
                        range.start + child_measure - offset,
                        slice,
                        &mut start_should_rebalance,
                    )
                });

                break;
            }
        }

        let mut extra_leaves = extra_leaves.map(|leaves| {
            let l = leaves.collect::<Vec<_>>();
            debug_assert!(l.iter().all(|l| l.is_leaf()));
            l
        });

        for (idx, child) in indexes.map(|idx| (idx, inode.child(idx))) {
            let child_measure = child.measure::<M>();

            offset += child_measure;

            if offset >= range.end {
                end_idx = idx;

                inode.with_child_mut(end_idx, |child| {
                    replace_last_rec(
                        Arc::make_mut(child),
                        range.end + child_measure - offset,
                        &mut extra_leaves,
                        &mut end_should_rebalance,
                    )
                });

                break;
            }
        }

        if start_should_rebalance || end_should_rebalance {
            debug_assert!(extra_leaves.is_none());

            inode.drain(start_idx + 1..end_idx);

            // balance_start_end(&mut inode, start_idx);

            Node::replace_with_single_child(node);

            return None;
        }

        let mut extra_leaves = if let Some(leaves) = extra_leaves {
            debug_assert!(!leaves.is_empty());
            leaves
        } else {
            inode.drain(start_idx + 1..end_idx);
            return None;
        };

        inode.replace_range_with_leaves_back(
            start_idx + 1..end_idx,
            &mut extra_leaves,
        );

        if extra_leaves.is_empty() {
            return None;
        }

        let extras = if inode.depth() == 1 {
            extra_leaves
        } else {
            let mut extra_leaves = extra_leaves.into_iter();

            let target_depth = inode.depth() - 1;

            let max_leaves_for_depth =
                Inode::<N, L>::max_leaves_for_depth(target_depth);

            let min_leaves_for_depth =
                Inode::<N, L>::min_leaves_for_depth(target_depth);

            let mut extras = Vec::new();

            while extra_leaves.len() >= min_leaves_for_depth {
                let extra = Inode::from_nodes(
                    extra_leaves.by_ref().take(max_leaves_for_depth),
                );

                debug_assert_eq!(extra.depth(), target_depth);

                extras.push(Arc::new(Node::Internal(extra)))
            }

            if extra_leaves.len() > 0 {
                debug_assert!(end_idx > 0);

                inode.with_child_mut(start_idx, |n| {
                    let mut previous_inode = {
                        let n = extras.last_mut().unwrap_or(n);
                        let n = Arc::make_mut(n);
                        unsafe { n.as_mut_internal_unchecked() }
                    };

                    if extra_leaves.len() >= Inode::<N, L>::min_children() {
                        let last = Arc::new(Node::Internal(
                            Inode::from_nodes(extra_leaves),
                        ));

                        debug_assert!(last.depth() < target_depth);

                        if let Some(last) =
                            previous_inode.append_at_depth(last)
                        {
                            debug_assert_eq!(last.depth(), target_depth);
                            extras.push(Arc::new(Node::Internal(last)));
                        }
                    } else {
                        // We have `L < min_children` leaves to insert in the
                        // previous inode.
                        for leaf in extra_leaves {
                            if let Some(extra) =
                                previous_inode.append_at_depth(leaf)
                            {
                                debug_assert_eq!(extra.depth(), target_depth);
                                extras.push(Arc::new(Node::Internal(extra)));

                                previous_inode = {
                                    let n = extras.last_mut().unwrap();
                                    let n = Arc::make_mut(n);
                                    unsafe { n.as_mut_internal_unchecked() }
                                };
                            }
                        }
                    }
                })
            }

            extras
        };

        debug_assert!(extras.iter().all(|n| n.depth() == inode.depth() - 1));

        inode
            .insert_children(start_idx + 1, extras)
            .map(|extras| extras.map(Node::Internal).map(Arc::new).collect())
    }

    /// TODO: docs
    #[inline]
    fn replace_first_rec<const N: usize, M, L>(
        node: &mut Node<N, L>,
        replace_from: M,
        slice: &L::Slice,
        should_rebalance: &mut bool,
    ) -> Option<impl ExactSizeIterator<Item = Arc<Node<N, L>>>>
    where
        M: Metric<L>,
        L: ReplaceableLeaf<M> + Clone,
    {
        let inode = match node {
            Node::Internal(inode) => inode,

            Node::Leaf(leaf) => {
                // NOTE: the end of the range is wrong for metrics other than
                // the BaseMetric because there might be some `M`-remainder
                // that is not part of the range. This is not a problem for now
                // because `Rope::replace()` uses the ByteMetric.
                //
                // TODO: make `Leaf::replace()` generic over a `RangeBounds<M>`
                // instead of `Range<M>`?
                let range = replace_from..leaf.measure::<M>();

                return if let Some(extra_leaves) = leaf.replace(range, slice) {
                    Some(extra_leaves.map(Node::Leaf).map(Arc::new))
                } else {
                    *should_rebalance |= leaf.is_underfilled();
                    None
                };
            },
        };

        // The index of the child containing the start of the replacement
        // range.
        let mut start_idx = 0;

        let mut extra_leaves = None;

        let mut offset = M::zero();

        for (idx, child) in inode.children().iter().enumerate() {
            let child_measure = child.measure::<M>();

            offset += child_measure;

            if offset >= replace_from {
                start_idx = idx;

                extra_leaves = inode.with_child_mut(start_idx, |child| {
                    replace_first_rec(
                        Arc::make_mut(child),
                        replace_from + child_measure - offset,
                        slice,
                        should_rebalance,
                    )
                });

                break;
            }
        }

        let extra_leaves = if let Some(mut extra_leaves) = extra_leaves {
            inode.replace_range_with_leaves(
                start_idx + 1..inode.len(),
                &mut extra_leaves,
            );

            (extra_leaves.len() > 0).then_some(extra_leaves)
        } else {
            inode.drain(start_idx + 1..);
            None
        };

        *should_rebalance |= inode.is_underfilled();

        extra_leaves
    }

    /// TODO: docs
    #[inline]
    fn replace_last_rec<const N: usize, M, L>(
        node: &mut Node<N, L>,
        replace_up_to: M,
        extra_leaves: &mut Option<Vec<Arc<Node<N, L>>>>,
        should_rebalance: &mut bool,
    ) where
        M: Metric<L>,
        L: ReplaceableLeaf<M> + Clone,
    {
        let inode = match node {
            Node::Internal(inode) => inode,

            Node::Leaf(leaf) => {
                leaf.remove(replace_up_to);

                if leaf.is_underfilled() {
                    if let Some(leaves) = extra_leaves {
                        let mut last = leaves.pop().unwrap();
                        debug_assert!(last.is_leaf());

                        let l = {
                            let l = Arc::get_mut(&mut last).unwrap();
                            unsafe { l.as_mut_leaf_unchecked() }
                        };

                        l.balance(leaf);

                        if leaf.is_empty() {
                            std::mem::swap(leaf, l)
                        } else {
                            leaves.push(last)
                        }

                        debug_assert!(!leaf.is_underfilled());

                        if leaves.is_empty() {
                            *extra_leaves = None;
                        }
                    }
                }

                *should_rebalance = leaf.is_underfilled();
                return;
            },
        };

        let mut end_idx = 0;

        let mut offset = inode.measure::<M>();

        for (idx, child) in inode.children().iter().enumerate().rev() {
            let child_measure = child.measure::<M>();

            offset -= child_measure;

            if offset < replace_up_to {
                end_idx = idx;

                inode.with_child_mut(end_idx, |child| {
                    replace_last_rec(
                        Arc::make_mut(child),
                        replace_up_to - offset,
                        extra_leaves,
                        should_rebalance,
                    )
                });

                break;
            }
        }

        if let Some(leaves) = extra_leaves {
            inode.replace_range_with_leaves_back(0..end_idx, leaves);
            if leaves.is_empty() {
                *extra_leaves = None;
            }
        } else {
            inode.drain(..end_idx);
        }

        *should_rebalance |= inode.is_underfilled();
    }
}

mod from_treeslice {
    //! This module handles the logic used to convert `TreeSlice`s into
    //! `Tree`s.

    use super::*;

    /// Converts a `TreeSlice` into the root of an equivalent `Tree`.
    ///
    /// NOTE: can only be called if the slice has a leaf count of at least 3.
    /// Leaf counts of 1 or 2 should be handled before calling this function.
    #[inline]
    pub(super) fn into_tree_root<const N: usize, L: BalancedLeaf>(
        slice: TreeSlice<'_, N, L>,
    ) -> Arc<Node<N, L>> {
        debug_assert!(slice.leaf_count() >= 3);

        let (root, invalid_in_first, invalid_in_last) = cut_tree_slice(slice);

        let mut root = Arc::new(Node::Internal(root));

        if invalid_in_first > 0 {
            {
                // Safety : `root` was just enclosed in a `Node::Internal`
                // variant.
                let mut inode = unsafe {
                    Arc::get_mut(&mut root)
                        .unwrap()
                        .as_mut_internal_unchecked()
                };

                loop {
                    inode.balance_first_child_with_second();

                    if let Node::Internal(first) =
                        Arc::get_mut(inode.first_mut()).unwrap()
                    {
                        inode = first;
                    } else {
                        break;
                    }
                }
            }

            Node::replace_with_single_child(&mut root);
        }

        if invalid_in_last > 0 {
            {
                // Safety (as_mut_internal_unchecked): for the root to become a
                // leaf node after the previous call to `pull_up_singular` the
                // TreeSlice would've had to span 2 leaves, and that case case
                // should have already been handled before calling this
                // function.
                let mut inode = unsafe {
                    Arc::get_mut(&mut root)
                        .unwrap()
                        .as_mut_internal_unchecked()
                };

                loop {
                    inode.balance_last_child_with_penultimate();

                    if let Node::Internal(last) =
                        Arc::get_mut(inode.last_mut()).unwrap()
                    {
                        inode = last;
                    } else {
                        break;
                    }
                }
            }

            Node::replace_with_single_child(&mut root);
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
    fn cut_tree_slice<const N: usize, L: BalancedLeaf>(
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

        for child in children.by_ref() {
            let this = child.base_measure();

            if offset + this > start {
                if start == L::BaseMetric::zero() {
                    root.push(Arc::clone(child));
                } else {
                    let first = cut_first_rec(
                        child,
                        start - offset,
                        slice.first_slice,
                        slice.first_summary.clone(),
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

        for child in children {
            let this = child.base_measure();

            if offset + this >= end {
                if end == slice.root().base_measure() {
                    root.push(Arc::clone(child));
                } else {
                    let last = cut_last_rec(
                        child,
                        end - offset,
                        slice.last_slice,
                        slice.last_summary.clone(),
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
    fn cut_first_rec<const N: usize, L: BalancedLeaf>(
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

                for child in children.by_ref() {
                    let this = child.base_measure();

                    if offset + this > take_from {
                        let first = cut_first_rec(
                            child,
                            take_from - offset,
                            start_slice,
                            start_summary,
                            invalid_nodes,
                        );

                        let first_is_underfilled = first.is_underfilled();

                        inode.push(first);

                        for child in children {
                            inode.push(Arc::clone(child));
                        }

                        if first_is_underfilled && inode.len() > 1 {
                            inode.balance_first_child_with_second();
                            *invalid_nodes -= 1;
                        }

                        if inode.is_underfilled() {
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

                if lnode.is_underfilled() {
                    *invalid_nodes += 1;
                }

                Arc::new(Node::Leaf(lnode))
            },
        }
    }

    #[inline]
    fn cut_last_rec<const N: usize, L: BalancedLeaf>(
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

                        let last_is_underfilled = last.is_underfilled();

                        inode.push(last);

                        if last_is_underfilled && inode.len() > 1 {
                            inode.balance_last_child_with_penultimate();
                            *invalid_nodes -= 1;
                        }

                        if inode.is_underfilled() {
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

                if lnode.is_underfilled() {
                    *invalid_nodes = 1;
                }

                Arc::new(Node::Leaf(lnode))
            },
        }
    }
}

pub(crate) use iter_chain::ExactChain;

mod iter_chain {
    //! Implements the `Chain` iterator, which is just like
    //! [`std::iter::Chain`] except it implements `ExactSizeIterator` when
    //! the first and second iterators are both `ExactSizeIterator`.
    //!
    //! See [1] or [2] for why this is needed.
    //!
    //! [1]: https://github.com/rust-lang/rust/issues/34433
    //! [2]: https://github.com/rust-lang/rust/pull/66531

    pub(crate) struct Chain<T, U> {
        chain: std::iter::Chain<T, U>,
        yielded: usize,
        total: usize,
    }

    pub(crate) trait ExactChain<I>:
        ExactSizeIterator<Item = I>
    {
        fn exact_chain<U>(self, other: U) -> Chain<Self, U::IntoIter>
        where
            Self: Sized,
            U: IntoIterator<Item = I>,
            U::IntoIter: ExactSizeIterator;
    }

    impl<I, T> ExactChain<I> for T
    where
        T: ExactSizeIterator<Item = I>,
    {
        #[inline]
        fn exact_chain<U>(self, other: U) -> Chain<Self, U::IntoIter>
        where
            Self: Sized,
            U: IntoIterator<Item = I>,
            U::IntoIter: ExactSizeIterator,
        {
            let other = other.into_iter();
            Chain {
                yielded: 0,
                total: self.len() + other.len(),
                chain: self.chain(other),
            }
        }
    }

    impl<T, I1, I2> Iterator for Chain<I1, I2>
    where
        I1: ExactSizeIterator<Item = T>,
        I2: ExactSizeIterator<Item = T>,
    {
        type Item = T;

        #[inline]
        fn next(&mut self) -> Option<Self::Item> {
            let item = self.chain.next()?;
            self.yielded += 1;
            Some(item)
        }

        #[inline]
        fn size_hint(&self) -> (usize, Option<usize>) {
            let exact = self.len();
            (exact, Some(exact))
        }
    }

    impl<T, I1, I2> ExactSizeIterator for Chain<I1, I2>
    where
        I1: ExactSizeIterator<Item = T>,
        I2: ExactSizeIterator<Item = T>,
    {
        #[inline]
        fn len(&self) -> usize {
            self.total - self.yielded
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

    impl AddAssign<&Self> for Count {
        fn add_assign(&mut self, rhs: &Self) {
            self.count += rhs.count;
            self.leaves += rhs.leaves;
        }
    }

    impl SubAssign<&Self> for Count {
        fn sub_assign(&mut self, rhs: &Self) {
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
