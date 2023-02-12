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

impl<const FANOUT: usize, L: Leaf> From<TreeSlice<'_, FANOUT, L>>
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
            return from_treeslice::into_tree_root(slice);
        };

        #[cfg(debug_assertions)]
        (Tree { root: Arc::clone(&root) }).assert_invariants();

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
                assert!(
                    root.children().len() >= 2
                        && root.children().len() <= FANOUT
                );

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

    /// Creates a new `Tree` from a collection of leaves.
    ///
    /// NOTE: if the iterator yields 0 items the `Tree` will contain a single
    /// leaf with `L`'s default value.
    #[inline]
    pub fn from_leaves<I>(leaves: I) -> Self
    where
        I: IntoIterator<Item = L>,
        L: Default,
    {
        Self {
            root: Self::root_from_leaves(leaves.into_iter())
                .unwrap_or_default(),
        }
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

    /// TODO: move this away?
    ///
    /// Continuously replaces the root with its first child as long as the root
    /// is an internal node with a single child.
    ///
    /// # Panics
    ///
    /// Panics if the `Arc` enclosing the root has a strong counter > 1.
    #[inline]
    pub(super) fn pull_up_root(&mut self) {
        let root = &mut self.root;

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

    /// TODO: docs
    #[inline]
    pub fn replace<'a, M, I>(&mut self, range: Range<M>, slices: I)
    where
        L: ReplaceableLeaf<M>,
        M: Metric<L>,
        I: IntoIterator<Item = &'a L::Slice>,
        L::Slice: 'a,
        for<'d> &'d L::Slice: Default,
    {
        let root = Arc::make_mut(&mut self.root);

        if let Some(extra) =
            tree_replace::some_name(root, range, slices.into_iter())
        {
            debug_assert!(extra.iter().all(|n| n.depth() == root.depth()));

            let old_root =
                std::mem::replace(root, Node::Internal(Inode::empty()));

            *root = Node::Internal(Inode::from_equally_deep_nodes(
                std::iter::once(Arc::new(old_root)).exact_chain(extra),
            ));
        }

        #[cfg(debug_assertions)]
        self.assert_invariants();
    }

    #[inline]
    pub(super) fn root(&self) -> &Arc<Node<FANOUT, L>> {
        &self.root
    }

    /// TODO:
    /// move this back to `Tree::from_leaves` once we don't use it in
    /// tree_replace
    /// TODO: docs
    #[inline]
    fn root_from_leaves<I>(mut leaves: I) -> Option<Arc<Node<FANOUT, L>>>
    where
        I: Iterator<Item = L>,
    {
        let first = leaves.next()?;
        let first = Arc::new(Node::Leaf(Lnode::from(first)));

        let Some(second) = leaves.next() else { return Some(first) };
        let second = Arc::new(Node::Leaf(Lnode::from(second)));

        let nodes = {
            let (lo, hi) = leaves.size_hint();
            let mut n = Vec::with_capacity(2 + hi.unwrap_or(lo));
            n.push(first);
            n.push(second);
            n.extend(leaves.map(Lnode::from).map(Node::Leaf).map(Arc::new));
            n
        };

        let mut root = Inode::from_equally_deep_nodes(nodes);

        // TODO: if the last chunk had >= min_bytes we could avoid doing all of
        // this.
        root.balance_right_side();
        let mut tree = Self { root: Arc::new(Node::Internal(root)) };
        tree.pull_up_root();
        Some(tree.root)
        //
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
    pub(super) fn some_name<'a, const N: usize, L, M, I>(
        node: &mut Node<N, L>,
        mut range: Range<M>,
        mut slices: I,
    ) -> Option<Vec<Arc<Node<N, L>>>>
    where
        L: ReplaceableLeaf<M>,
        M: Metric<L>,
        I: Iterator<Item = &'a L::Slice>,
        L::Slice: 'a,
        for<'d> &'d L::Slice: Default,
    {
        match node {
            Node::Internal(inode) => {
                // The index of the child containing the entire replacement
                // range.
                let mut child_idx = 0;

                let mut split = None;

                let mut offset = M::zero();

                for (idx, child) in inode.children().iter().enumerate() {
                    let child_measure = child.measure::<M>();

                    offset += child_measure;

                    if offset >= range.start {
                        if offset >= range.end {
                            child_idx = idx;

                            split = inode.with_child_mut(idx, |child| {
                                offset -= child_measure;
                                range.start -= offset;
                                range.end -= offset;
                                some_name(Arc::make_mut(child), range, slices)
                            });

                            break;
                        } else {
                            return do_stuff_with_deepest(
                                inode, range, slices,
                            );
                        };
                    }
                }

                if let Some(extra) = split {
                    debug_assert!(extra
                        .iter()
                        .all(|n| n.depth()
                            == inode.children()[child_idx].depth()));

                    let total_children = inode.children().len() + extra.len();

                    let max_children = Inode::<N, L>::max_children();

                    if total_children <= max_children {
                        for node in extra {
                            child_idx += 1;
                            inode.insert(child_idx, node)
                        }
                        return None;
                    }

                    let last =
                        inode.split_off(child_idx + 1).collect::<Vec<_>>();

                    let children = std::mem::take(&mut inode.children)
                        .into_iter()
                        .exact_chain(extra)
                        .exact_chain(last);

                    let mut inodes = ChildSegmenter::new(children);

                    *inode = inodes.next().unwrap();

                    let extra = inodes
                        .map(Node::Internal)
                        .map(Arc::new)
                        .collect::<Vec<_>>();

                    debug_assert!(!extra.is_empty());

                    Some(extra)
                } else {
                    // TODO: check to see if the children at child_idx needs to
                    // be rebalances/removed/whatever.
                    None
                }
            },

            Node::Leaf(leaf) => {
                let replace_with = slices.next().unwrap_or_default();

                let extra_leaf = leaf.replace(range, replace_with);

                let mut leaves = slices
                    .map(std::borrow::ToOwned::to_owned)
                    .map(Lnode::from)
                    .map(Node::Leaf)
                    .map(Arc::new);

                if let Some(leaf) = extra_leaf {
                    let (lo, hi) = leaves.size_hint();
                    let mut extra = Vec::with_capacity(1 + hi.unwrap_or(lo));
                    extra.extend(leaves);
                    extra.push(Arc::new(Node::Leaf(leaf)));
                    Some(extra)
                } else if let Some(leaf) = leaves.next() {
                    let (lo, hi) = leaves.size_hint();
                    let mut extra = Vec::with_capacity(1 + hi.unwrap_or(lo));
                    extra.push(leaf);
                    extra.extend(leaves);
                    Some(extra)
                } else {
                    None
                }
            },
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
    fn do_stuff_with_deepest<'a, const N: usize, L, M, I>(
        inode: &mut Inode<N, L>,
        range: Range<M>,
        mut slices: I,
    ) -> Option<Vec<Arc<Node<N, L>>>>
    where
        L: ReplaceableLeaf<M>,
        M: Metric<L>,
        I: Iterator<Item = &'a L::Slice>,
        L::Slice: 'a,
        for<'d> &'d L::Slice: Default,
    {
        // The index of the child containing the start of the replacement
        // range.
        let mut start_idx = 0;

        let mut split_first = None;

        let mut offset = M::zero();

        let mut child_indexes = 0..inode.children().len();

        for (idx, child) in
            child_indexes.by_ref().map(|idx| (idx, &inode.children[idx]))
        {
            let child_measure = child.measure::<M>();

            offset += child_measure;

            if offset >= range.start {
                start_idx = idx;

                split_first = inode.with_child_mut(start_idx, |child| {
                    replace_first_rec(
                        Arc::make_mut(child),
                        range.start + child_measure - offset,
                        &mut slices,
                    )
                });

                break;
            }
        }

        // The index of the child containing the end of the replacement range.
        let mut end_idx = 0;

        let mut split_last = None;

        let mut slices = {
            // We collect into a Vec to satisfy the trait bounds of
            // `replace_last_rec`.
            let s = slices.collect::<Vec<_>>();
            s.into_iter()
        };

        for (idx, child) in
            child_indexes.map(|idx| (idx, &inode.children[idx]))
        {
            let child_measure = child.measure::<M>();

            offset += child_measure;

            if offset >= range.end {
                end_idx = idx;

                split_last = inode.with_child_mut(end_idx, |child| {
                    replace_last_rec(
                        Arc::make_mut(child),
                        range.end + child_measure - offset,
                        &mut slices,
                    )
                });

                break;
            }
        }

        if let Some(split_first) = split_first {
            if split_first.depth() + 1 == inode.depth() {
                if start_idx + 1 < end_idx {
                    start_idx += 1;
                    inode.swap_child(start_idx, split_first);
                } else {
                    end_idx += 1;
                    inode.insert(start_idx, split_first);
                }
            } else {
                todo!();
            }
        }

        if let Some(split_last) = split_last {
            if split_last.depth() + 1 == inode.depth() {
                inode.insert(end_idx + 1, split_last);
            } else {
                todo!();
            }
        }

        let leaf_count = (inode.depth() - 1) ^ N;

        let mut leaves = slices.map(std::borrow::ToOwned::to_owned);

        for idx in start_idx + 1..end_idx {
            if let Some(node) =
                Tree::root_from_leaves(leaves.by_ref().take(leaf_count))
            {
                if node.depth() + 1 == inode.depth() {
                    inode.swap_child(idx, node);
                } else {
                    todo!();
                }
            } else {
                inode.remove(idx)
            }
        }

        while let Some(node) =
            Tree::root_from_leaves(leaves.by_ref().take(leaf_count))
        {
            if node.depth() + 1 == inode.depth() {
                inode.insert(end_idx, node);
                end_idx += 1;
            } else {
                todo!();
            }
        }

        if inode.is_overfull() {
            let min_children = Inode::<N, L>::min_children();
            let split_offset = inode.children().len() - min_children;
            let split = Inode::from_children(inode.split_off(split_offset));
            Some(vec![Arc::new(Node::Internal(split))])
        } else {
            None
        }
    }

    /// TODO: docs
    #[inline]
    fn replace_first_rec<'a, const N: usize, L, M, I>(
        node: &mut Node<N, L>,
        replace_from: M,
        slices: &mut I,
    ) -> Option<Arc<Node<N, L>>>
    where
        L: ReplaceableLeaf<M>,
        M: Metric<L>,
        I: Iterator<Item = &'a L::Slice>,
        L::Slice: 'a,
        for<'d> &'d L::Slice: Default,
    {
        match node {
            Node::Internal(inode) => {
                let mut offset = M::zero();

                for (idx, child) in inode.children().iter().enumerate() {
                    let child_measure = child.measure::<M>();

                    if offset + child_measure >= replace_from {
                        let extra = inode.with_child_mut(idx, |child| {
                            replace_first_rec(
                                Arc::make_mut(child),
                                replace_from - offset,
                                slices,
                            )
                        });

                        // If the child was the last in the inode there's
                        // nothing left to do.
                        if idx + 1 == inode.children().len() {
                            return extra;
                        }

                        // TODO: prepend_at_depth `extra` on the next node.

                        for idx in idx + 1..inode.children().len() {
                            let leaf_count = (inode.depth() - 1) ^ N;

                            let replacement = Tree::root_from_leaves(
                                slices
                                    .take(leaf_count)
                                    .map(std::borrow::ToOwned::to_owned),
                            );

                            if let Some(replacement) = replacement {
                                if replacement.depth() + 1 == inode.depth() {
                                    inode.swap_child(idx, replacement);
                                } else {
                                    // prepend at depth on the next or return
                                    // it.
                                    todo!();
                                }
                            } else {
                                // inode.drain(idx..inode.children().len());
                                return None;
                            }
                        }

                        todo!();
                    } else {
                        offset += child_measure;
                    }
                }

                unreachable!();
            },

            Node::Leaf(leaf) => {
                let replace_with = slices.next().unwrap_or_default();

                // NOTE: the end of the range is wrong for metrics other than
                // the BaseMetric because there might be some `M`-remainder
                // that is not part of the range. This is not a problem for now
                // because `Rope::replace()` uses the ByteMetric.
                //
                // TODO: make `Leaf::replace()` generic over a `RangeBounds<M>`
                // instead of `Range<M>`?
                leaf.replace(replace_from..leaf.measure::<M>(), replace_with)
                    .map(|e| Arc::new(Node::Leaf(e)))
            },
        }
    }

    /// TODO: docs
    #[inline]
    fn replace_last_rec<'a, const N: usize, I, L, M>(
        node: &mut Node<N, L>,
        replace_up_to: M,
        slices: &mut I,
    ) -> Option<Arc<Node<N, L>>>
    where
        L: ReplaceableLeaf<M>,
        M: Metric<L>,
        I: Iterator<Item = &'a L::Slice>
            + DoubleEndedIterator
            + ExactSizeIterator,
        L::Slice: 'a,
        for<'d> &'d L::Slice: Default,
    {
        match node {
            Node::Internal(inode) => {
                let mut offset = M::zero();

                for (idx, child) in inode.children().iter().enumerate() {
                    let child_measure = child.measure::<M>();

                    if offset + child_measure >= replace_up_to {
                        inode.with_child_mut(idx, |child| {
                            replace_last_rec(
                                Arc::make_mut(child),
                                replace_up_to - offset,
                                slices,
                            )
                        });

                        todo!();
                    } else {
                        offset += child_measure;
                        // TODO: we gotta do some shit here.
                    }
                }

                unreachable!();
            },

            Node::Leaf(leaf) => {
                let replace_with = slices.next_back().unwrap_or_default();

                leaf.replace(M::zero()..replace_up_to, replace_with)
                    .map(|e| Arc::new(Node::Leaf(e)))
            },
        }
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
    pub(super) fn into_tree_root<const N: usize, L: Leaf>(
        slice: TreeSlice<'_, N, L>,
    ) -> Tree<N, L> {
        debug_assert!(slice.leaf_count() >= 3);

        let (root, invalid_in_first, invalid_in_last) = cut_tree_slice(slice);

        let mut tree = Tree { root: Arc::new(Node::Internal(root)) };

        if invalid_in_first > 0 {
            {
                // Safety : `root` was just enclosed in a `Node::Internal`
                // variant.
                let root = unsafe {
                    Arc::get_mut(&mut tree.root)
                        .unwrap()
                        .as_mut_internal_unchecked()
                };

                root.balance_left_side();
            }

            tree.pull_up_root();
        }

        if invalid_in_last > 0 {
            {
                // Safety (as_mut_internal_unchecked): for the root to become a
                // leaf node after the previous call to `pull_up_singular` the
                // TreeSlice would've had to span 2 leaves, and that case case
                // should have already been handled before calling this
                // function.
                let root = unsafe {
                    Arc::get_mut(&mut tree.root)
                        .unwrap()
                        .as_mut_internal_unchecked()
                };

                root.balance_right_side();
            }

            tree.pull_up_root();
        }

        #[cfg(debug_assertions)]
        tree.assert_invariants();

        tree
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
}

use iter_chain::ExactChain;

mod iter_chain {
    //! Implements `Chain` which is just like
    //! [`std::iter::Chain`] except it implements `ExactSizeIterator` when
    //! the first and second iterators are both are `ExactSizeIterator`.
    //!
    //! See [1] or [2] for why this is needed.
    //!
    //! [1]: https://github.com/rust-lang/rust/issues/34433
    //! [2]: https://github.com/rust-lang/rust/pull/66531

    pub(super) struct Chain<T, U> {
        chain: std::iter::Chain<T, U>,
        yielded: usize,
        total: usize,
    }

    pub(super) trait ExactChain<I>:
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
