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

        let root = Inode::from_equally_deep_nodes(leaves);

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
            if i.len() == 1 {
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
    pub fn replace<M>(&mut self, range: Range<M>, slice: &L::Slice)
    where
        M: Metric<L>,
        L: ReplaceableLeaf<M> + Clone,
    {
        let root = Arc::make_mut(&mut self.root);

        if let Some(extras) = tree_replace::some_name(root, range, slice) {
            debug_assert!(extras.iter().all(|n| n.depth() == root.depth()));

            let old_root =
                std::mem::replace(root, Node::Internal(Inode::empty()));

            *root = Node::Internal(Inode::from_equally_deep_nodes(
                std::iter::once(Arc::new(old_root)).exact_chain(extras),
            ));
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
        node: &mut Node<N, L>,
        mut range: Range<M>,
        slice: &L::Slice,
    ) -> Option<Vec<Arc<Node<N, L>>>>
    where
        M: Metric<L>,
        L: ReplaceableLeaf<M> + Clone,
    {
        let inode = match node {
            Node::Internal(inode) => inode,

            Node::Leaf(leaf) => {
                let extras = leaf.replace(range, slice)?;
                return Some(extras.map(Node::Leaf).map(Arc::new).collect());
            },
        };

        // The index of the child containing the entire replacement range.
        let mut child_idx = 0;

        let mut extras = None;

        let mut offset = M::zero();

        for (idx, child) in inode.children().iter().enumerate() {
            let child_measure = child.measure::<M>();

            offset += child_measure;

            if offset >= range.start {
                child_idx = idx;

                extras = if offset >= range.end {
                    inode.with_child_mut(idx, |child| {
                        offset -= child_measure;
                        range.start -= offset;
                        range.end -= offset;
                        some_name(Arc::make_mut(child), range, slice)
                    })
                } else {
                    do_stuff_with_deepest(inode, range, slice)
                };

                break;
            }
        }

        if let Some(extras) = extras {
            collapse_stuff(inode, child_idx + 1, extras)
        } else if inode.children[child_idx].is_underfilled() {
            // TODO: rebalance child_idx with either previous or next
            // node.
            None
        } else {
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
        inode: &mut Inode<N, L>,
        range: Range<M>,
        slice: &L::Slice,
    ) -> Option<Vec<Arc<Node<N, L>>>>
    where
        M: Metric<L>,
        L: ReplaceableLeaf<M> + Clone,
    {
        // The index of the child containing the start of the replacement
        // range.
        let mut start_idx = 0;

        // The index of the child containing the end of the replacement range.
        let mut end_idx = 0;

        let mut extra_leaves = None;

        let mut offset = M::zero();

        let mut child_indexes = 0..inode.len();

        for (idx, child) in
            child_indexes.by_ref().map(|idx| (idx, &inode.children[idx]))
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
                    )
                });

                break;
            }
        }

        for (idx, child) in
            child_indexes.map(|idx| (idx, &inode.children[idx]))
        {
            let child_measure = child.measure::<M>();

            offset += child_measure;

            if offset >= range.end {
                end_idx = idx;

                inode.with_child_mut(end_idx, |child| {
                    replace_last_rec(
                        Arc::make_mut(child),
                        range.end + child_measure - offset,
                        &mut extra_leaves,
                    )
                });

                break;
            }
        }

        replace_or_remove_stuff_leaves(
            inode,
            start_idx + 1..end_idx,
            &mut extra_leaves,
        );

        // TODO: handle start, end being underfilled

        let extras = extra_leaves.map(|mut extra_leaves| {
            if inode.depth() == 1 {
                extra_leaves.collect()
            } else {
                let mut extras = Vec::new();

                let target_depth = inode.depth() - 1;
                let max_leaves_for_depth = N ^ target_depth;

                while extra_leaves.len() > max_leaves_for_depth {
                    let extra = Inode::from_equally_deep_nodes(
                        extra_leaves.by_ref().take(max_leaves_for_depth),
                    );

                    debug_assert_eq!(extra.depth(), target_depth);

                    extras.push(Arc::new(Node::Internal(extra)));
                }

                if extra_leaves.len() > 0 {
                    let last = if extra_leaves.len() == 1 {
                        extra_leaves.next().unwrap()
                    } else {
                        Arc::new(Node::Internal(
                            Inode::from_equally_deep_nodes(extra_leaves),
                        ))
                    };

                    if last.depth() == target_depth {
                        extras.push(last)
                    } else {
                        let previous_inode = extras
                            .last_mut()
                            .unwrap_or(&mut inode.children_mut()[end_idx - 1]);

                        let previous_inode = Arc::make_mut(previous_inode);

                        let previous_inode = unsafe {
                            previous_inode.as_mut_internal_unchecked()
                        };

                        debug_assert_eq!(previous_inode.depth(), target_depth);

                        if let Some(extra) =
                            previous_inode.append_at_depth(last)
                        {
                            extras.push(Arc::new(Node::Internal(extra)));
                        }
                    }
                }

                extras
            }
        });

        if let Some(extras) = extras {
            collapse_stuff(inode, end_idx, extras)
        } else {
            None
        }
    }

    /// TODO: docs
    #[inline]
    fn replace_or_remove<const N: usize, L: Leaf, I>(
        inode: &mut Inode<N, L>,
        child_range: Range<usize>,
        replace_with: &mut Option<I>,
    ) where
        I: Iterator<Item = Arc<Node<N, L>>>,
    {
        let range_end = child_range.end;

        if let Some(replacements) = replace_with {
            for child_idx in child_range {
                if let Some(replacement) = replacements.next() {
                    inode.swap(child_idx, replacement);
                } else {
                    *replace_with = None;
                    inode.remove(child_idx);
                    for child_idx in child_idx + 1..range_end {
                        inode.remove(child_idx);
                    }
                    break;
                }
            }
        } else {
            for child_idx in child_range {
                inode.remove(child_idx);
            }
        }
    }

    /// TODO: docs
    #[inline]
    fn collapse_stuff<const N: usize, L: Leaf>(
        inode: &mut Inode<N, L>,
        mut insert_after: usize,
        children: Vec<Arc<Node<N, L>>>,
    ) -> Option<Vec<Arc<Node<N, L>>>> {
        debug_assert!(children
            .iter()
            .all(|n| n.depth() == inode.first().depth()));

        if inode.len() + children.len() <= Inode::<N, L>::max_children() {
            // TODO: split, extend, push?
            for node in children {
                inode.insert(insert_after, node);
                insert_after += 1;
            }
            return None;
        }

        let last = inode.split_off(insert_after).collect::<Vec<_>>();

        let children = std::mem::take(&mut inode.children)
            .into_iter()
            .exact_chain(children)
            .exact_chain(last);

        let mut inodes = ChildSegmenter::new(children);

        *inode = inodes.next().unwrap();

        Some(inodes.map(Node::Internal).map(Arc::new).collect())
    }

    /// TODO: docs
    #[inline]
    fn replace_first_rec<const N: usize, M, L>(
        node: &mut Node<N, L>,
        replace_from: M,
        slice: &L::Slice,
    ) -> Option<
        impl Iterator<Item = Arc<Node<N, L>>>
            + ExactSizeIterator
            + DoubleEndedIterator,
    >
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
                let extras = leaf.replace(range, slice)?;
                return Some(extras.map(Node::Leaf).map(Arc::new));
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
                    )
                });

                break;
            }
        }

        replace_or_remove_stuff_leaves(
            inode,
            start_idx + 1..inode.len(),
            &mut extra_leaves,
        );

        extra_leaves
    }

    /// TODO: docs
    #[inline]
    fn replace_or_remove_stuff_leaves<const N: usize, L: Leaf, I>(
        inode: &mut Inode<N, L>,
        child_range: Range<usize>,
        replace_with_leaves: &mut Option<I>,
    ) where
        L: Clone,
        I: Iterator<Item = Arc<Node<N, L>>> + ExactSizeIterator,
    {
        if inode.depth() == 1 {
            replace_or_remove(inode, child_range, replace_with_leaves)
        } else if let Some(replacements) = replace_with_leaves.as_mut() {
            let target_depth = inode.depth() - 1;
            let max_leaves_for_depth = N ^ target_depth;

            for child_idx in child_range {
                let replacement = Inode::from_equally_deep_nodes(
                    replacements.by_ref().take(max_leaves_for_depth),
                );

                if replacement.depth() == target_depth {
                    inode.swap(
                        child_idx,
                        Arc::new(Node::Internal(replacement)),
                    );
                } else {
                    if replacement.is_underfilled() {
                        // TODO
                    }

                    let replacement = Arc::new(Node::Internal(replacement));

                    let previous_child = Arc::make_mut(
                        &mut inode.children_mut()[child_idx - 1],
                    );

                    let previous_child =
                        unsafe { previous_child.as_mut_internal_unchecked() };

                    if let Some(replacement) =
                        previous_child.append_at_depth(replacement)
                    {
                        inode.swap(
                            child_idx,
                            Arc::new(Node::Internal(replacement)),
                        );
                    } else {
                        inode.remove(child_idx);
                    }

                    for child_idx in child_idx + 1..inode.len() {
                        inode.remove(child_idx);
                    }

                    *replace_with_leaves = None;

                    return;
                }
            }
        } else {
            for child_idx in child_range {
                inode.remove(child_idx);
            }
        }
    }

    /// TODO: docs
    #[inline]
    fn replace_last_rec<const N: usize, M, L, I>(
        node: &mut Node<N, L>,
        replace_up_to: M,
        extras: &mut Option<I>,
    ) where
        M: Metric<L>,
        L: ReplaceableLeaf<M> + Clone,
        I: Iterator<Item = Arc<Node<N, L>>>
            + DoubleEndedIterator
            + ExactSizeIterator,
    {
        let inode = match node {
            Node::Internal(inode) => inode,

            Node::Leaf(leaf) => {
                leaf.remove(replace_up_to);
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
                        replace_up_to + offset - child_measure,
                        extras,
                    )
                });

                break;
            }
        }

        let range = 0..end_idx;

        if inode.depth() == 1 {
            // replace_or_remove(inode, range, &mut extra_leaves)
            todo!();
        } else if let Some(leaves) = extras {
            let target_depth = inode.depth() - 1;
            let max_leaves_for_depth = N ^ target_depth;

            for child_idx in range.rev() {
                let replacement = Inode::from_equally_deep_nodes(
                    leaves.by_ref().rev().take(max_leaves_for_depth).rev(),
                );

                if replacement.depth() == target_depth {
                    inode.swap(
                        child_idx,
                        Arc::new(Node::Internal(replacement)),
                    );
                } else {
                    if replacement.is_underfilled() {
                        // TODO
                    }

                    let replacement = Arc::new(Node::Internal(replacement));

                    let next_child = Arc::make_mut(
                        &mut inode.children_mut()[child_idx + 1],
                    );

                    let next_child =
                        unsafe { next_child.as_mut_internal_unchecked() };

                    if let Some(replacement) =
                        next_child.prepend_at_depth(replacement)
                    {
                        inode.swap(
                            child_idx,
                            Arc::new(Node::Internal(replacement)),
                        );
                    } else {
                        inode.remove(child_idx);
                    }

                    for child_idx in 0..child_idx {
                        inode.remove(child_idx);
                    }

                    *extras = None;

                    return;
                }
            }
        } else {
            for child_idx in range {
                inode.remove(child_idx);
            }
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

                        let first_is_underfilled = first.is_underfilled();

                        inode.push(first);

                        for child in children {
                            inode.push(Arc::clone(child));
                        }

                        if first_is_underfilled && inode.len() > 1 {
                            inode.balance_first_child_with_second();
                            *invalid_nodes -= 1;
                        }

                        if !inode.is_underfilled() {
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

                        let last_is_underfilled = last.is_underfilled();

                        inode.push(last);

                        if last_is_underfilled && inode.len() > 1 {
                            inode.balance_last_child_with_penultimate();
                            *invalid_nodes -= 1;
                        }

                        if !inode.is_underfilled() {
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
    //! Implements the `Chain` iterator, which is just like
    //! [`std::iter::Chain`] except it implements `ExactSizeIterator` when
    //! the first and second iterators are both `ExactSizeIterator`.
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
