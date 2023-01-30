use std::sync::Arc;

use super::*;

/// An iterator over the units of a metric.
#[derive(Clone)]
pub struct Units<'a, const FANOUT: usize, L: Leaf, M: Metric<L>> {
    /*
      This iterator is implemented using two separate iterators, one for
      iterating forward (used in the `Iterator` impl), and the other for
      iterating backward (used in the `DoubleEndedIterator` impl).

      These two iterators are completely independent and don't know about each
      other, which could cause them to overlap if alternating between calling
      `Units::next()` and `Units::next_back()`.

      To prevent this we also store the yielded and total base measures,
      increasing the yielded measure as we go. Once those two are equal this
      iterator will stop yielding any more items.
    */
    #[rustfmt::skip]

    /// Iterates over the `M`-units from front to back.
    forward: UnitsForward<'a, FANOUT, L, M>,

    /// Iterates over the `M`-units from back to front.
    backward: UnitsBackward<'a, FANOUT, L, M>,

    /// The base measure of all the `TreeSlice`s which are yet to be yielded.
    remaining: L::BaseMetric,
}

impl<'a, const FANOUT: usize, L: Leaf, M: Metric<L>> From<&'a Tree<FANOUT, L>>
    for Units<'a, FANOUT, L, M>
where
    for<'d> &'d L::Slice: Default,
{
    #[inline]
    fn from(tree: &'a Tree<FANOUT, L>) -> Units<'a, FANOUT, L, M> {
        Self {
            forward: UnitsForward::from(tree),
            backward: UnitsBackward::from(tree),
            remaining: tree.base_measure(),
        }
    }
}

impl<'a, const FANOUT: usize, L: Leaf, M: Metric<L>>
    From<&'a TreeSlice<'a, FANOUT, L>> for Units<'a, FANOUT, L, M>
where
    for<'d> &'d L::Slice: Default,
{
    #[inline]
    fn from(
        tree_slice: &'a TreeSlice<'a, FANOUT, L>,
    ) -> Units<'a, FANOUT, L, M> {
        Self {
            forward: UnitsForward::from(tree_slice),
            backward: UnitsBackward::from(tree_slice),
            remaining: tree_slice.base_measure(),
        }
    }
}

impl<'a, const FANOUT: usize, L: Leaf, M: UnitMetric<L>> Iterator
    for Units<'a, FANOUT, L, M>
{
    type Item = TreeSlice<'a, FANOUT, L>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.remaining == L::BaseMetric::zero() {
            None
        } else {
            let (tree_slice, advance) = self.forward.next();
            self.remaining -= advance;
            tree_slice
        }
    }
}

impl<'a, const FANOUT: usize, L: Leaf, M: DoubleEndedUnitMetric<L>>
    DoubleEndedIterator for Units<'a, FANOUT, L, M>
{
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.remaining == L::BaseMetric::zero() {
            None
        } else {
            let (tree_slice, advance) = self.backward.previous();
            self.remaining -= advance;
            tree_slice
        }
    }
}

impl<'a, const FANOUT: usize, L: Leaf, M: UnitMetric<L>>
    std::iter::FusedIterator for Units<'a, FANOUT, L, M>
{
}

#[derive(Debug)]
struct UnitsForward<'a, const N: usize, L: Leaf, M: Metric<L>> {
    /// Whether `Self` has been initialized by calling
    /// [`initialize`](UnitsForward::initialize()).
    is_initialized: bool,

    /// The path from the root node down to `leaf_node`. All the nodes in the
    /// stack are guaranteed to be internal nodes.
    stack: Vec<(&'a Arc<Node<N, L>>, usize)>,

    /// The current leaf node.
    leaf_node: &'a Arc<Node<N, L>>,

    /// How much of `leaf_node`'s base measure has already been yielded.
    yielded_in_leaf: L::BaseMetric,

    /// The `start_slice` field of the next `TreeSlice` that'll be returned by
    /// [`next`](Self::next()).
    start_slice: &'a L::Slice,

    /// The `start_summary` field of the next `TreeSlice` that'll be returned
    /// by [`next`](Self::next()).
    start_summary: L::Summary,

    /// The first slice in the yielding range and its summary. It's only set if
    /// we're iterating over a `TreeSlice`.
    first_slice: Option<(&'a L::Slice, &'a L::Summary)>,

    /// The last slice in the yielding range and its summary. It's only set if
    /// we're iterating over a `TreeSlice`.
    last_slice: Option<(&'a L::Slice, &'a L::Summary)>,

    /// The start of the yielding range as an offset into the root.
    base_start: L::BaseMetric,

    /// The base units which are yet to be yielded.
    base_yielded: L::BaseMetric,

    /// The base units which are yet to be yielded.
    base_total: L::BaseMetric,

    /// The `M`-units which are yet to be yielded.
    units_yielded: M,

    /// The `M`-units which are yet to be yielded.
    units_total: M,
}

impl<'a, const N: usize, L: Leaf, M: Metric<L>> Clone
    for UnitsForward<'a, N, L, M>
{
    #[inline]
    fn clone(&self) -> Self {
        Self {
            stack: self.stack.clone(),
            start_summary: self.start_summary.clone(),
            ..*self
        }
    }
}

impl<'a, const FANOUT: usize, L: Leaf, M: Metric<L>> From<&'a Tree<FANOUT, L>>
    for UnitsForward<'a, FANOUT, L, M>
where
    for<'d> &'d L::Slice: Default,
{
    #[inline]
    fn from(tree: &'a Tree<FANOUT, L>) -> UnitsForward<'a, FANOUT, L, M> {
        Self {
            is_initialized: false,
            stack: Vec::with_capacity(tree.root().depth()),
            leaf_node: tree.root(),
            yielded_in_leaf: L::BaseMetric::zero(),
            start_slice: <&L::Slice>::default(),
            start_summary: L::Summary::default(),
            first_slice: None,
            last_slice: None,
            base_start: L::BaseMetric::zero(),
            base_yielded: L::BaseMetric::zero(),
            base_total: tree.base_measure(),
            units_yielded: M::zero(),
            units_total: tree.measure::<M>(),
        }
    }
}

impl<'a, const FANOUT: usize, L: Leaf, M: Metric<L>>
    From<&'a TreeSlice<'a, FANOUT, L>> for UnitsForward<'a, FANOUT, L, M>
where
    for<'d> &'d L::Slice: Default,
{
    #[inline]
    fn from(
        tree_slice: &'a TreeSlice<'a, FANOUT, L>,
    ) -> UnitsForward<'a, FANOUT, L, M> {
        Self {
            is_initialized: false,
            stack: Vec::with_capacity(tree_slice.root().depth()),
            leaf_node: tree_slice.root(),
            yielded_in_leaf: L::BaseMetric::zero(),
            start_slice: <&L::Slice>::default(),
            start_summary: L::Summary::default(),
            first_slice: Some((
                tree_slice.start_slice,
                &tree_slice.start_summary,
            )),
            last_slice: Some((tree_slice.end_slice, &tree_slice.end_summary)),
            base_start: tree_slice.offset,
            base_yielded: L::BaseMetric::zero(),
            base_total: tree_slice.base_measure(),
            units_yielded: M::zero(),
            units_total: tree_slice.measure::<M>(),
        }
    }
}

impl<'a, const N: usize, L: Leaf, M: UnitMetric<L>> UnitsForward<'a, N, L, M> {
    /// Initializes `Self` by populating the stack with the path from the root
    /// down to the internal node containing the leaf node at `base_offset`,
    /// which is set to `leaf_node`.
    ///
    /// Also sets `yielded_in_leaf`, `end_slice` and `end_summary`.
    #[inline]
    fn initialize(&mut self) {
        debug_assert!(!self.is_initialized);

        self.is_initialized = true;

        // The leaf node is actually the root at this point.
        let mut node = self.leaf_node;

        let mut offset = L::BaseMetric::zero();

        'outer: loop {
            match &**node {
                Node::Internal(inode) => {
                    for (idx, child) in inode.children().iter().enumerate() {
                        let child_measure = child.base_measure();

                        if offset + child_measure > self.base_start {
                            self.stack.push((node, idx));
                            node = child;
                            continue 'outer;
                        } else {
                            offset += child_measure;
                        }
                    }

                    unreachable!();
                },

                Node::Leaf(leaf) => {
                    self.leaf_node = node;

                    match self.first_slice.take() {
                        Some((slice, summary)) => {
                            self.yielded_in_leaf = leaf.base_measure()
                                - L::BaseMetric::measure(summary);

                            self.start_slice = slice;
                            self.start_summary = summary.clone();
                        },

                        None => {
                            self.start_slice = leaf.as_slice();
                            self.start_summary = leaf.summary().clone();
                        },
                    }

                    return;
                },
            }
        }
    }

    /// Returns the next leaf in the iterating range after the current
    /// `leaf_node` together with its summary, **without** checking if there is
    /// one.
    #[inline]
    fn next_leaf(&mut self) -> (&'a L::Slice, &'a L::Summary) {
        debug_assert!(self.base_total > self.base_yielded);

        let mut node = loop {
            let &mut (node, ref mut child_idx) =
                self.stack.last_mut().unwrap();

            // Safety: every node in the stack is an internal node.
            let inode = unsafe { node.as_internal_unchecked() };

            *child_idx += 1;

            if *child_idx < inode.children().len() {
                break &inode.children()[*child_idx];
            } else {
                self.stack.pop();
            }
        };

        loop {
            match &**node {
                Node::Internal(inode) => {
                    self.stack.push((node, 0));
                    node = inode.first();
                    continue;
                },

                Node::Leaf(leaf) => {
                    self.leaf_node = node;

                    let (slice, summary) = {
                        let contains_last_slice = leaf.base_measure()
                            > self.base_total - self.base_yielded;

                        if contains_last_slice {
                            self.last_slice.take().unwrap()
                        } else {
                            (leaf.as_slice(), leaf.summary())
                        }
                    };

                    return (slice, summary);
                },
            }
        }
    }

    /// Yields the next unit in the current `self.leaf_node`. To do this
    /// correctly `self.start_slice` needs to contain at least one `M`-unit.
    #[inline]
    fn next_unit_in_leaf(&mut self) -> (TreeSlice<'a, N, L>, L::Summary) {
        debug_assert!(M::measure(&self.start_summary) > M::zero());
        debug_assert!(self.units_total > self.units_yielded);

        let (slice, summary, advance, rest, rest_summary) =
            M::first_unit(self.start_slice, &self.start_summary);

        let offset = self.yielded_in_leaf;

        self.yielded_in_leaf += L::BaseMetric::measure(&advance);
        self.start_slice = rest;
        self.start_summary = rest_summary;

        (
            TreeSlice {
                root: self.leaf_node,
                offset,
                start_slice: slice,
                start_summary: summary.clone(),
                end_slice: slice,
                end_summary: summary.clone(),
                summary,
                leaf_count: 1,
            },
            advance,
        )
    }

    /// Traverses the stack to find the next leaf node with a non-zero
    /// `M`-measure.
    ///
    /// Returns a `(Leaf, Inode, Base, Summary, Count)` tuple where:
    ///
    /// - `Leaf` is that leaf node;
    ///
    /// - `Inode` is the deepest internal node containing both the current
    /// `self.leaf_node` and `Leaf` in its subtree;
    ///
    /// - `Base` is the sum of the base measures of all the nodes between the
    /// start of `Inode` and the current `self.leaf_node`;
    ///
    /// - `Summary` and `Count` are the sum of the summaries and leaf counts of
    /// all the nodes between (but not including) `self.leaf_node` and `Leaf`.
    ///
    /// Note: it assumes that such a leaf node exists. If that's not the case
    /// this function may panic or return a leaf node outside of the valid
    /// range for this iterator.
    ///
    /// Note: after calling this function the stack will contain the path from
    /// the root down to the internal node containing `Leaf`, and
    /// `self.leaf_node` will be set to `Leaf`.
    ///
    /// Invariants: `Leaf` is guaranteed to have an `M`-measure of at least
    /// `M::one()`.
    #[inline]
    fn next_leaf_with_measure(
        &mut self,
    ) -> (&'a Lnode<L>, &'a Arc<Node<N, L>>, L::BaseMetric, L::Summary, usize)
    {
        debug_assert!(self.units_total > self.units_yielded);

        let mut before = L::BaseMetric::zero();
        let mut summary = L::Summary::default();
        let mut leaf_count = 0;

        // Step 1: pop nodes off the stack until we find a node with some
        // `M`-units that we haven't yielded yet.

        'outer: loop {
            let (node, child_idx) = self.stack.pop().unwrap();

            // Safety: every node in the stack is an internal node.
            let inode = unsafe { node.as_internal_unchecked() };

            for child in &inode.children()[..child_idx] {
                before += child.base_measure();
            }

            for (idx, child) in
                inode.children()[child_idx + 1..].iter().enumerate()
            {
                if child.measure::<M>() > M::zero() {
                    self.stack.push((node, child_idx + 1 + idx));
                    break 'outer;
                } else {
                    summary += child.summary();
                    leaf_count += child.num_leaves();
                }
            }
        }

        let &(inode, child_idx) = self.stack.last().unwrap();

        // Step 2: push nodes on the stack until we get to the first leaf node
        // with a positive `M`-measure. Once we get there we're done.

        // Safety: every node in the stack is an internal node.
        let mut node =
            unsafe { &inode.as_internal_unchecked().children()[child_idx] };

        'outer: loop {
            match &**node {
                Node::Internal(inode) => {
                    for (idx, child) in inode.children().iter().enumerate() {
                        if child.measure::<M>() > M::zero() {
                            self.stack.push((node, idx));
                            node = child;
                            continue 'outer;
                        } else {
                            summary += child.summary();
                            leaf_count += child.num_leaves();
                        }
                    }

                    unreachable!();
                },

                Node::Leaf(leaf) => {
                    debug_assert!(leaf.measure::<M>() > M::zero());

                    self.leaf_node = node;
                    return (leaf, inode, before, summary, leaf_count);
                },
            }
        }
    }

    /// Returns the leaf node befire the current `leaf_node`, **without**
    /// checking if there is one in the valid range of this iterator.
    ///
    /// Invariants: the returned [`Node`] is guaranteed to be a leaf node.
    #[inline]
    fn previous_leaf(&self) -> &'a Arc<Node<N, L>> {
        let mut stack_idx = self.stack.len() - 1;

        let mut node = loop {
            let (node, child_idx) = self.stack[stack_idx];

            // Safety: every node in the stack is an internal node.
            let inode = unsafe { node.as_internal_unchecked() };

            if child_idx > 0 {
                break &inode.children()[child_idx - 1];
            } else {
                stack_idx -= 1;
            }
        };

        loop {
            match &**node {
                Node::Internal(inode) => {
                    node = inode.last();
                    continue;
                },

                Node::Leaf(_) => break node,
            }
        }
    }

    /// Yields the next unit in the iterating range. This is the function that
    /// gets called in the general case, i.e. when the next unit is not the
    /// last and it's not contained in `self.leaf_node`. The root of the
    /// returned `TreeSlice` is a node in the stack so it's guaranteed to be an
    /// internal node.
    ///
    /// Note: this uses [`next_leaf_with_measure`][1] internally so it should
    /// only be called when `self.units_yielded < self.units_total`.
    ///
    /// [1]: UnitsForward::next_leaf_with_measure()
    #[inline]
    fn next_unit_in_range(&mut self) -> (TreeSlice<'a, N, L>, L::Summary) {
        debug_assert_eq!(M::measure(&self.start_summary), M::zero());
        debug_assert!(self.units_total > self.units_yielded);

        // A previous call to `next_unit_in_leaf` might've left the start slice
        // empty.
        if L::BaseMetric::measure(&self.start_summary) == L::BaseMetric::zero()
        {
            let (next_slice, next_summary) = self.next_leaf();
            self.yielded_in_leaf = L::BaseMetric::zero();
            self.start_slice = next_slice;
            self.start_summary = next_summary.clone();

            if M::measure(&self.start_summary) > M::zero() {
                return self.next_unit_in_leaf();
            }
        }

        let start_slice = self.start_slice;
        let start_summary = self.start_summary.clone();

        let (leaf, mut root, mut offset, mut summary, mut leaf_count) =
            self.next_leaf_with_measure();

        offset += self.yielded_in_leaf;
        summary += &start_summary;
        leaf_count += 1;

        let (slice, slice_summary) = {
            let contains_last_slice = L::BaseMetric::measure(&summary)
                + leaf.base_measure()
                > self.base_total - self.base_yielded;

            if contains_last_slice {
                self.last_slice.take().unwrap()
            } else {
                (leaf.as_slice(), leaf.summary())
            }
        };

        let (mut end_slice, mut end_summary, mut advance, rest, rest_summary) =
            M::first_unit(slice, slice_summary);

        self.yielded_in_leaf = L::BaseMetric::measure(&advance);
        self.start_slice = rest;
        self.start_summary = rest_summary;

        advance += &summary;

        if L::BaseMetric::measure(&end_summary) > L::BaseMetric::zero() {
            summary += &end_summary;
            leaf_count += 1;
        } else {
            let previous_leaf = self.previous_leaf();

            if leaf_count == 1 {
                root = previous_leaf;

                offset =
                    root.base_measure() - L::BaseMetric::measure(&summary);

                end_slice = start_slice;

                end_summary = start_summary.clone();
            } else {
                let start = self.base_start + self.base_yielded;

                let range = start..(start + L::BaseMetric::measure(&summary));

                let (deepest, range) =
                    tree_slice::deepest_node_containing_range(
                        self.stack[0].0,
                        range,
                    );

                root = deepest;

                offset = range.start;

                // Safety: `previous_leaf` is guaranteed to be a leaf node by
                // `Self::previous_leaf()`.
                let previous_leaf =
                    unsafe { previous_leaf.as_leaf_unchecked() };

                end_slice = previous_leaf.as_slice();

                end_summary = previous_leaf.summary().clone();
            }
        }

        (
            TreeSlice {
                root,
                offset,
                summary,
                end_slice,
                end_summary,
                start_slice,
                start_summary,
                leaf_count,
            },
            advance,
        )
    }

    /// Very similar to [`next_leaf_with_measure`](1), except it doesn't
    /// mutate any state and instead of returning the next leaf node with a
    /// non-zero `M`-measure it returns the leaf node containing
    /// [`last_slice`](2), or the last leaf node in the root if that's not set.
    ///
    /// Note: it assumes that leaf node is different than the current
    /// [`leaf_node`](3). That case should be handled by the caller.
    ///
    /// [1]: UnitsForward::next_leaf_with_measure()
    /// [2]: UnitsForward::last_slice
    /// [3]: UnitsForward::leaf_node
    #[inline]
    fn last_leaf(
        &self,
    ) -> (&'a Lnode<L>, &'a Arc<Node<N, L>>, L::BaseMetric, L::Summary, usize)
    {
        // Step 1: find the index of deepest node in the stack that fully
        // contains `range`.

        let mut range = (self.base_start + self.base_yielded)
            ..(self.base_start + self.base_total);

        let root_idx = {
            let mut root_idx = self.stack.len() - 1;

            'outer: for (stack_idx, &(node, child_idx)) in
                self.stack.iter().enumerate()
            {
                // Safety: every node in the stack is an internal node.
                let inode = unsafe { node.as_internal_unchecked() };

                let mut measured = L::BaseMetric::zero();

                for child in &inode.children()[..child_idx] {
                    measured += child.base_measure();
                }

                for child in &inode.children()[child_idx..] {
                    let child_measure = child.base_measure();

                    if measured <= range.start
                        && measured + child_measure >= range.end
                    {
                        range.start -= measured;
                        range.end -= measured;
                        continue 'outer;
                    } else {
                        measured += child_measure;
                    }
                }

                // If none of this inode's children fully contains the range
                // then this is the root.
                root_idx = stack_idx;

                break;
            }

            root_idx
        };

        // Step 2: traverse down the stack starting from the node after the
        // root, increasing `after`, `summary` and `leaf_count` as you go.

        let mut before = L::BaseMetric::zero();
        let mut summary = L::Summary::default();
        let mut leaf_count = 0;

        for &(node, child_idx) in &self.stack[root_idx + 1..] {
            // Safety: every node in the stack is an internal node.
            let inode = unsafe { node.as_internal_unchecked() };

            for child in &inode.children()[..child_idx] {
                before += child.base_measure();
            }

            for child in &inode.children()[child_idx + 1..] {
                summary += child.summary();
                leaf_count += child.num_leaves();
            }
        }

        let (root, child_idx) = self.stack[root_idx];

        // Safety: every node in the stack is an internal node.
        let inode = unsafe { root.as_internal_unchecked() };

        let mut offset = L::BaseMetric::zero();

        for child in &inode.children()[..child_idx] {
            let child_measure = child.base_measure();
            offset += child_measure;
            before += child_measure;
        }

        offset += inode.children()[child_idx].base_measure();

        // This will be the child of the root node that contains the last
        // slice.
        let mut node = inode.first();

        for child in &inode.children()[child_idx + 1..] {
            let child_measure = child.base_measure();

            if offset + child_measure >= range.end {
                node = child;
                break;
            } else {
                offset += child_measure;
                summary += child.summary();
                leaf_count += child.num_leaves();
            }
        }

        'outer: loop {
            match &**node {
                Node::Internal(inode) => {
                    for child in inode.children() {
                        let child_measure = child.base_measure();

                        if offset + child_measure >= range.end {
                            node = child;
                            continue 'outer;
                        } else {
                            offset += child_measure;
                            summary += child.summary();
                            leaf_count += child.num_leaves();
                        }
                    }

                    unreachable!();
                },

                Node::Leaf(leaf) => {
                    return (leaf, root, before, summary, leaf_count);
                },
            }
        }
    }

    /// This is the analogous of [`UnitsBackward::remainder()`] when iterating
    /// forward. Check the doc comment of that function as most of it applies
    /// 1:1 to this.
    #[inline]
    fn remainder(&mut self) -> (TreeSlice<'a, N, L>, L::Summary) {
        debug_assert_eq!(self.units_total, self.units_yielded);
        debug_assert!(self.base_total > self.base_yielded);

        if L::BaseMetric::measure(&self.start_summary) == L::BaseMetric::zero()
        {
            let (next_slice, next_summary) = self.next_leaf();
            self.yielded_in_leaf = L::BaseMetric::zero();
            self.start_slice = next_slice;
            self.start_summary = next_summary.clone();
        }

        // First, check if the leaf node is the root. If it is we're done.
        if self.base_total - self.base_yielded
            == L::BaseMetric::measure(&self.start_summary)
        {
            let summary = std::mem::take(&mut self.start_summary);

            let advance = summary.clone();

            return (
                TreeSlice {
                    root: self.leaf_node,
                    offset: self.yielded_in_leaf,
                    start_slice: self.start_slice,
                    start_summary: summary.clone(),
                    end_slice: self.start_slice,
                    end_summary: summary.clone(),
                    summary,
                    leaf_count: 1,
                },
                advance,
            );
        }

        let start_slice = self.start_slice;
        let start_summary = std::mem::take(&mut self.start_summary);

        let (last_leaf, root, before, mut summary, leaf_count) =
            self.last_leaf();

        summary += &start_summary;

        let (end_slice, end_summary) = match self.last_slice.take() {
            Some((slice, summary)) => (slice, summary.clone()),
            None => (last_leaf.as_slice(), last_leaf.summary().clone()),
        };

        summary += &end_summary;

        let offset = before + self.yielded_in_leaf;

        let advance = summary.clone();

        (
            TreeSlice {
                root,
                offset,
                summary,
                start_slice,
                start_summary,
                end_slice,
                end_summary,
                // +2 to account for the leaves containing the first and last
                // slices.
                leaf_count: leaf_count + 2,
            },
            advance,
        )
    }

    #[inline]
    fn next(&mut self) -> (Option<TreeSlice<'a, N, L>>, L::BaseMetric) {
        if !self.is_initialized {
            self.initialize();
        }

        let (tree_slice, advance) =
            if M::measure(&self.start_summary) > M::zero() {
                self.next_unit_in_leaf()
            } else if self.units_total > self.units_yielded {
                self.next_unit_in_range()
            } else if self.base_total > self.base_yielded {
                let (remainder, advance) = self.remainder();

                debug_assert_eq!(M::measure(&advance), M::zero());

                debug_assert_eq!(
                    L::BaseMetric::measure(&advance),
                    self.base_total - self.base_yielded
                );

                self.base_yielded = self.base_total;

                return (Some(remainder), L::BaseMetric::measure(&advance));
            } else {
                return (None, L::BaseMetric::zero());
            };

        debug_assert_eq!(M::measure(&advance), M::one());

        self.base_yielded += L::BaseMetric::measure(&advance);
        self.units_yielded += M::one();

        (Some(tree_slice), L::BaseMetric::measure(&advance))
    }
}

#[derive(Debug)]
struct UnitsBackward<'a, const N: usize, L: Leaf, M: Metric<L>> {
    /// Whether `Self` has been initialized by calling
    /// [`initialize`](Self::initialize()).
    is_initialized: bool,

    /// The path from the root node down to `leaf_node`. All the nodes in the
    /// stack are guaranteed to be internal node.
    stack: Vec<(&'a Arc<Node<N, L>>, usize)>,

    /// The current leaf node.
    leaf_node: &'a Arc<Node<N, L>>,

    /// How much of `leaf_node`'s base measure has already been yielded.
    yielded_in_leaf: L::BaseMetric,

    /// The `end_slice` field of the next `TreeSlice` that'll be returned by
    /// calling [`previous`](Self::previous()).
    end_slice: &'a L::Slice,

    /// The `end_summary` field of the next `TreeSlice` that's returned by
    /// calling [`previous`](Self::previous()).
    end_summary: L::Summary,

    /// The first slice in the yielding range and its summary. It's only set if
    /// we're iterating over a `TreeSlice`. If it's set it will be `.take()`n
    /// when calling [`first`](Self::first()).
    first_slice: Option<(&'a L::Slice, &'a L::Summary)>,

    /// The last slice in the yielding range and its summary. It's only set if
    /// we're iterating over a `TreeSlice`. If it's set it will be `.take()`n
    /// when initializing.
    last_slice: Option<(&'a L::Slice, &'a L::Summary)>,

    /// The base units which are yet to be yielded.
    base_remaining: L::BaseMetric,

    /// The `M`-units which are yet to be yielded.
    units_remaining: M,

    /// The start of the yielding range as an offset into the root.
    base_start: L::BaseMetric,
}

impl<'a, const N: usize, L: Leaf, M: Metric<L>> Clone
    for UnitsBackward<'a, N, L, M>
{
    #[inline]
    fn clone(&self) -> Self {
        Self {
            stack: self.stack.clone(),
            end_summary: self.end_summary.clone(),
            ..*self
        }
    }
}

impl<'a, const FANOUT: usize, L: Leaf, M: Metric<L>> From<&'a Tree<FANOUT, L>>
    for UnitsBackward<'a, FANOUT, L, M>
where
    for<'d> &'d L::Slice: Default,
{
    #[inline]
    fn from(tree: &'a Tree<FANOUT, L>) -> UnitsBackward<'a, FANOUT, L, M> {
        Self {
            is_initialized: false,
            stack: Vec::with_capacity(tree.root().depth()),
            leaf_node: tree.root(),
            yielded_in_leaf: L::BaseMetric::zero(),
            end_slice: <&L::Slice>::default(),
            end_summary: L::Summary::default(),
            first_slice: None,
            last_slice: None,
            base_remaining: tree.base_measure(),
            units_remaining: tree.root().measure::<M>(),
            base_start: L::BaseMetric::zero(),
        }
    }
}

impl<'a, const FANOUT: usize, L: Leaf, M: Metric<L>>
    From<&'a TreeSlice<'a, FANOUT, L>> for UnitsBackward<'a, FANOUT, L, M>
where
    for<'d> &'d L::Slice: Default,
{
    #[inline]
    fn from(
        tree_slice: &'a TreeSlice<'a, FANOUT, L>,
    ) -> UnitsBackward<'a, FANOUT, L, M> {
        // println!("{tree_slice:#?}");

        Self {
            is_initialized: false,
            stack: Vec::with_capacity(tree_slice.root().depth()),
            leaf_node: tree_slice.root(),
            yielded_in_leaf: L::BaseMetric::zero(),
            end_slice: <&L::Slice>::default(),
            end_summary: L::Summary::default(),
            first_slice: Some((
                tree_slice.start_slice,
                &tree_slice.start_summary,
            )),
            last_slice: Some((tree_slice.end_slice, &tree_slice.end_summary)),
            base_remaining: tree_slice.base_measure(),
            units_remaining: tree_slice.measure::<M>(),
            base_start: tree_slice.offset,
        }
    }
}

impl<'a, const N: usize, L: Leaf, M: DoubleEndedUnitMetric<L>>
    UnitsBackward<'a, N, L, M>
{
    /// Initializes `Self` by populating the stack with the path from the root
    /// down to the internal node containing the leaf node at
    /// `base_offset + base_total`, which is set to `leaf_node`.
    ///
    /// Also sets `yielded_in_leaf`, `end_slice` and `end_summary`.
    #[inline]
    fn initialize(&mut self) {
        debug_assert!(!self.is_initialized);

        self.is_initialized = true;

        // The leaf node is actually the root at this point.
        let mut node = self.leaf_node;

        let last_slice_offset = self.base_start + self.base_remaining;

        let mut offset = L::BaseMetric::zero();

        'outer: loop {
            match &**node {
                Node::Internal(inode) => {
                    for (idx, child) in inode.children().iter().enumerate() {
                        let child_measure = child.base_measure();

                        if offset + child_measure >= last_slice_offset {
                            self.stack.push((node, idx));
                            node = child;
                            continue 'outer;
                        } else {
                            offset += child_measure;
                        }
                    }

                    unreachable!();
                },

                Node::Leaf(leaf) => {
                    self.leaf_node = node;

                    match self.last_slice.take() {
                        Some((slice, summary)) => {
                            self.yielded_in_leaf = leaf.base_measure()
                                - L::BaseMetric::measure(summary);

                            self.end_slice = slice;
                            self.end_summary = summary.clone();
                        },

                        None => {
                            self.end_slice = leaf.as_slice();
                            self.end_summary = leaf.summary().clone();
                        },
                    };

                    return;
                },
            }
        }
    }

    /// Very similar to [`previous_leaf_with_measure`](1), except it doesn't
    /// mutate any state and instead of returning the previous leaf node with a
    /// non-zero `M`-measure it returns the leaf node containing
    /// [`first_slice`](2), or the first leaf node in the root if that's not
    /// set.
    ///
    /// Note: it assumes that leaf node is different than the current
    /// [`leaf_node`](3). That case should be handled by the caller.
    ///
    /// [1]: UnitsBackward::previous_leaf_with_measure()
    /// [2]: UnitsBackward::first_slice
    /// [3]: UnitsBackward::leaf_node
    #[inline]
    fn first_leaf(
        &self,
    ) -> (&'a Lnode<L>, &'a Arc<Node<N, L>>, L::BaseMetric, L::Summary, usize)
    {
        // Step 1: find the index of deepest node in the stack that fully
        // contains `range`.

        let mut range =
            self.base_start..(self.base_start + self.base_remaining);

        let root_idx = {
            let mut root_idx = self.stack.len() - 1;

            'outer: for (stack_idx, &(node, child_idx)) in
                self.stack.iter().enumerate()
            {
                // Safety: every node in the stack is an internal node.
                let inode = unsafe { node.as_internal_unchecked() };

                let mut offset = L::BaseMetric::zero();

                for child in &inode.children()[..=child_idx] {
                    let child_measure = child.base_measure();

                    if offset <= range.start
                        && offset + child_measure >= range.end
                    {
                        range.start -= offset;
                        range.end -= offset;
                        continue 'outer;
                    } else {
                        offset += child_measure;
                    }
                }

                // If none of this inode's children fully contains the range
                // then this is the root.
                root_idx = stack_idx;

                break;
            }

            root_idx
        };

        // Step 2: traverse down the stack starting from the node after the
        // root, increasing `after`, `summary` and `leaf_count` as you go.

        let mut after = L::BaseMetric::zero();
        let mut summary = L::Summary::default();
        let mut leaf_count = 0;

        for &(node, child_idx) in &self.stack[root_idx + 1..] {
            // Safety: every node in the stack is an internal node.
            let inode = unsafe { node.as_internal_unchecked() };

            for child in &inode.children()[..child_idx] {
                summary += child.summary();
                leaf_count += child.num_leaves();
            }

            for child in &inode.children()[child_idx + 1..] {
                after += child.base_measure();
            }
        }

        let (root, child_idx) = self.stack[root_idx];

        // Safety: every node in the stack is an internal node.
        let inode = unsafe { root.as_internal_unchecked() };

        for child in &inode.children()[child_idx + 1..] {
            after += child.base_measure();
        }

        // This will be the child of the root node that contains the first
        // slice.
        let mut node = inode.first();

        let mut offset = L::BaseMetric::zero();

        let mut children = inode.children()[..child_idx].iter();

        while let Some(child) = children.next() {
            let child_measure = child.base_measure();

            if offset + child_measure > range.start {
                for child in children {
                    summary += child.summary();
                    leaf_count += child.num_leaves();
                }
                node = child;
                break;
            } else {
                offset += child_measure;
            }
        }

        'outer: loop {
            match &**node {
                Node::Internal(inode) => {
                    let mut children = inode.children().iter();

                    while let Some(child) = children.next() {
                        let child_measure = child.base_measure();

                        if offset + child_measure > range.start {
                            for child in children {
                                summary += child.summary();
                                leaf_count += child.num_leaves();
                            }
                            node = child;
                            continue 'outer;
                        } else {
                            offset += child_measure;
                        }
                    }

                    unreachable!();
                },

                Node::Leaf(leaf) => {
                    return (leaf, root, after, summary, leaf_count);
                },
            }
        }
    }

    /// Yields the first unit in the range. This should be called when:
    ///
    /// - `units_total == M::zero()`, in which case this will yield the whole
    /// iterating range;
    ///
    /// - `units_yielded == units_total - M::one()`, i.e. when there's one
    /// final unit to yield.
    ///
    /// In both cases the next call to [`previous`](UnitsBackward::previous())
    /// will return `None`.
    #[inline]
    fn first(&mut self) -> (TreeSlice<'a, N, L>, L::Summary) {
        debug_assert!(self.base_remaining > L::BaseMetric::zero());

        let (_, _, end_slice, end_summary, mut advance) =
            M::last_unit(self.end_slice, &self.end_summary);

        // println!(
        //     "last unit of {:?} returned {end_slice:?} with advance \
        //      {advance:?}",
        //     self.end_slice
        // );

        // First, check if the current leaf node is the root. If it is we're
        // done.
        if self.base_remaining == L::BaseMetric::measure(&advance) {
            return (
                TreeSlice {
                    root: self.leaf_node,
                    offset: L::BaseMetric::zero(),
                    summary: end_summary.clone(),
                    start_slice: end_slice,
                    start_summary: end_summary.clone(),
                    end_slice,
                    end_summary,
                    leaf_count: 1,
                },
                advance,
            );
        }

        if L::BaseMetric::measure(&end_summary) == L::BaseMetric::zero() {
            todo!();
        }

        let (first_leaf, root, after, mut summary, leaf_count) =
            self.first_leaf();

        advance += &summary;

        summary += &end_summary;

        let (start_slice, start_summary) = match self.first_slice.take() {
            Some((slice, summary)) => (slice, summary.clone()),
            None => (first_leaf.as_slice(), first_leaf.summary().clone()),
        };

        advance += &start_summary;

        summary += &start_summary;

        let offset = root.base_measure()
            - after
            - self.yielded_in_leaf
            - L::BaseMetric::measure(&advance);

        (
            TreeSlice {
                root,
                offset,
                start_slice,
                start_summary,
                end_slice,
                end_summary,
                summary,
                // +2 to account for the leaves containing the first and last
                // slices.
                leaf_count: leaf_count + 2,
            },
            advance,
        )
    }

    /// Yields the previous unit in the current `self.leaf_node`. To do this
    /// correctly `self.end_slice` needs to contain at least two `M`-units.
    #[inline]
    fn previous_unit_in_leaf(&mut self) -> (TreeSlice<'a, N, L>, L::Summary) {
        debug_assert!(M::measure(&self.end_summary) > M::one());
        debug_assert!(self.units_remaining > M::zero());

        let (rest, rest_summary, slice, summary, advance) =
            M::last_unit(self.end_slice, &self.end_summary);

        debug_assert!(
            L::BaseMetric::measure(&rest_summary) > L::BaseMetric::zero()
        );

        let offset = L::BaseMetric::measure(&rest_summary);

        self.yielded_in_leaf += L::BaseMetric::measure(&advance);
        self.end_slice = rest;
        self.end_summary = rest_summary;

        (
            TreeSlice {
                root: self.leaf_node,
                offset,
                summary: summary.clone(),
                end_slice: slice,
                end_summary: summary.clone(),
                start_slice: slice,
                start_summary: summary,
                leaf_count: 1,
            },
            advance,
        )
    }

    /// Traverses the stack to find the previous leaf node with a non-zero
    /// `M`-measure.
    ///
    /// Returns a `(Leaf, Inode, Base, Summary, Count)` tuple where:
    ///
    /// - `Leaf` is that leaf node;
    ///
    /// - `Inode` is the deepest internal node containing both `Leaf` and the
    /// current `self.leaf_node` in its subtree;
    ///
    /// - `Base` is the base measure between the current `self.leaf_node` and
    ///   the end of `Inode`;
    ///
    /// - `Summary` and `Count` are the sum of the summaries and leaf counts of
    /// all the nodes between (but not including) `Leaf` and `self.leaf_node`.
    ///
    /// Note: it assumes that such a leaf node exists. If that's not the case
    /// this function may panic or return a leaf node outside of the valid
    /// range for this iterator.
    ///
    /// Note: after calling this function the stack will contain the path from
    /// the root down to the internal node containing `Leaf`, and
    /// `self.leaf_node` will be set to `Leaf`.
    ///
    /// Invariants: `Leaf` is guaranteed to have an `M`-measure of at least
    /// `M::one()`.
    #[inline]
    fn previous_leaf_with_measure(
        &mut self,
    ) -> (&'a Lnode<L>, &'a Arc<Node<N, L>>, L::BaseMetric, L::Summary, usize)
    {
        debug_assert!(self.units_remaining > M::zero());

        let mut after = L::BaseMetric::zero();
        let mut summary = L::Summary::default();
        let mut leaf_count = 0;

        // Step 1: pop nodes off the stack until we find a node with some
        // `M`-units that we haven't yielded yet.

        'outer: loop {
            let (node, child_idx) = self.stack.pop().unwrap();

            // Safety: every node in the stack is an internal node.
            let inode = unsafe { node.as_internal_unchecked() };

            for child in &inode.children()[child_idx + 1..] {
                after += child.base_measure();
            }

            for (idx, child) in
                inode.children()[..child_idx].iter().enumerate().rev()
            {
                if child.measure::<M>() > M::zero() {
                    self.stack.push((node, idx));
                    break 'outer;
                } else {
                    summary += child.summary();
                    leaf_count += child.num_leaves();
                }
            }
        }

        let &(inode, child_idx) = self.stack.last().unwrap();

        // Step 2: push nodes on the stack until we get to the first leaf node
        // with a positive `M`-measure. Once we get there we're done.

        // Safety: every node in the stack is an internal node.
        let mut node =
            unsafe { &inode.as_internal_unchecked().children()[child_idx] };

        'outer: loop {
            match &**node {
                Node::Internal(inode) => {
                    for (idx, child) in
                        inode.children().iter().enumerate().rev()
                    {
                        if child.measure::<M>() > M::zero() {
                            self.stack.push((node, idx));
                            node = child;
                            continue 'outer;
                        } else {
                            summary += child.summary();
                            leaf_count += child.num_leaves();
                        }
                    }

                    unreachable!();
                },

                Node::Leaf(leaf) => {
                    debug_assert!(leaf.measure::<M>() > M::zero());

                    self.leaf_node = node;
                    return (leaf, inode, after, summary, leaf_count);
                },
            }
        }
    }

    /// Returns the leaf node after the current `leaf_node`, **without**
    /// checking if there is one in the valid range of this iterator.
    ///
    /// Invariants: the returned [`Node`] is guaranteed to be a leaf node.
    #[inline]
    fn next_leaf(&self) -> &'a Arc<Node<N, L>> {
        let mut stack_idx = self.stack.len() - 1;

        let mut node = loop {
            let (node, mut child_idx) = self.stack[stack_idx];

            // Safety: every node in the stack is an internal node.
            let inode = unsafe { node.as_internal_unchecked() };

            child_idx += 1;

            if child_idx < inode.children().len() {
                break &inode.children()[child_idx];
            } else {
                stack_idx -= 1;
            }
        };

        loop {
            match &**node {
                Node::Internal(inode) => {
                    node = inode.first();
                    continue;
                },

                Node::Leaf(_) => break node,
            }
        }
    }

    /// Yields the previous unit in the iterating range. This is the function
    /// that gets called in the general case, i.e. when the next unit is not
    /// the first, the last and it's not contained in `self.leaf_node`. The
    /// root of the returned `TreeSlice` is a node in the stack so it's
    /// guaranteed to be an internal node.
    ///
    /// Note: this uses [`previous_leaf_with_measure`][1] internally so it
    /// should only be called when `self.units_yielded < self.units_total`.
    ///
    /// [1]: UnitsBackward::previous_leaf_with_measure()
    #[inline]
    fn previous_unit_in_range(&mut self) -> (TreeSlice<'a, N, L>, L::Summary) {
        debug_assert!(self.units_remaining > M::zero());

        let (_, _, mut end_slice, mut end_summary, mut advance) =
            M::last_unit(self.end_slice, &self.end_summary);

        if L::BaseMetric::measure(&end_summary) == L::BaseMetric::zero() {
            todo!();
        }

        let (leaf, mut root, after, mut summary, mut leaf_count) =
            self.previous_leaf_with_measure();

        advance += &summary;

        summary += &end_summary;

        leaf_count += 1;

        let (slice, slice_summary) = {
            let contains_first_slice = L::BaseMetric::measure(&summary)
                + leaf.base_measure()
                > self.base_remaining;

            if contains_first_slice {
                self.first_slice.take().unwrap()
            } else {
                (leaf.as_slice(), leaf.summary())
            }
        };

        let (
            rest,
            rest_summary,
            mut start_slice,
            mut start_summary,
            start_advance,
        ) = M::remainder(slice, slice_summary);

        advance += &start_advance;

        let mut offset = root.base_measure()
            - after
            - self.yielded_in_leaf
            - L::BaseMetric::measure(&advance);

        self.yielded_in_leaf = L::BaseMetric::measure(&start_advance);
        self.end_slice = rest;
        self.end_summary = rest_summary;

        if L::BaseMetric::measure(&start_summary) > L::BaseMetric::zero() {
            summary += &start_summary;
            leaf_count += 1;
        } else {
            let next_leaf = self.next_leaf();

            if leaf_count == 1 {
                root = next_leaf;

                offset = L::BaseMetric::zero();

                start_slice = end_slice;

                start_summary = end_summary.clone();
            } else {
                let end = self.base_start + self.base_remaining;

                let range = (end - L::BaseMetric::measure(&summary))..(end);

                let (deepest, range) =
                    tree_slice::deepest_node_containing_range(
                        self.stack[0].0,
                        range,
                    );

                root = deepest;

                offset = range.start;

                // Safety: `next_leaf` is guaranteed to be a leaf node by
                // `Self::next_leaf()`.
                let next_leaf = unsafe { next_leaf.as_leaf_unchecked() };

                start_slice = next_leaf.as_slice();

                start_summary = next_leaf.summary().clone();
            }
        }

        (
            TreeSlice {
                root,
                offset,
                summary,
                end_slice,
                end_summary,
                start_slice,
                start_summary,
                leaf_count,
            },
            advance,
        )
    }

    /// Yields the remainder of the yielding range when dividing by `M`-units,
    /// i.e. the TreeSlice in the `units_total..base_total` range. This should
    /// only be called once the first time [`next`][1] is called.
    ///
    /// For example let's consider the string "a\nb\nc". Its `LineMetric` is
    /// 2, but the 2nd unit of that metric ends at "..b\n", even though the
    /// last line (i.e. the first line this iterator yields) should be "c".
    ///
    /// This is because there's some text in the `LineMetric(2)..ByteMetric(5)`
    /// range. Calling this function will yield the `TreeSlice` in that range,
    /// but only if its base measure is positive (hence the `Option`). For
    /// example if the string was "a\n\b\n" the range would be
    /// `LineMetric(2)..ByteMetric(4)`, which doesn't contain any text. In that
    /// case this function would return `None`.
    ///
    /// It also follows that if `M` is the `BaseMetric` this function will
    /// always return `None`.
    ///
    /// [1]: UnitsBackward::next()
    #[inline]
    fn remainder(&mut self) -> Option<(TreeSlice<'a, N, L>, L::Summary)> {
        debug_assert!(self.base_remaining > L::BaseMetric::zero());

        if M::measure(&self.end_summary) > M::zero() {
            let (rest, rest_summary, slice, summary, advance) =
                M::remainder(self.end_slice, &self.end_summary);

            if L::BaseMetric::measure(&advance) > L::BaseMetric::zero() {
                let offset = L::BaseMetric::measure(&rest_summary);

                self.yielded_in_leaf += L::BaseMetric::measure(&advance);
                self.end_slice = rest;
                self.end_summary = rest_summary;

                Some((
                    TreeSlice {
                        root: self.leaf_node,
                        offset,
                        start_slice: slice,
                        start_summary: summary.clone(),
                        end_slice: slice,
                        end_summary: summary.clone(),
                        summary,
                        leaf_count: 1,
                    },
                    advance,
                ))
            } else {
                None
            }
        } else if self.units_remaining > M::zero() {
            Some(self.previous_unit_in_range())
        } else {
            Some(self.first())
        }
    }

    #[inline]
    fn previous(&mut self) -> (Option<TreeSlice<'a, N, L>>, L::BaseMetric) {
        if !self.is_initialized {
            self.initialize();

            if self.base_remaining > L::BaseMetric::zero() {
                if let Some((remainder, advance)) = self.remainder() {
                    debug_assert_eq!(M::measure(&advance), M::zero());

                    self.base_remaining -= L::BaseMetric::measure(&advance);

                    return (
                        Some(remainder),
                        L::BaseMetric::measure(&advance),
                    );
                }
            }
        }

        let (tree_slice, advance) =
            // .
            if M::measure(&self.end_summary) > M::one() {
                self.previous_unit_in_leaf()
            } else if self.units_remaining > M::one() {
                self.previous_unit_in_range()
            } else if self.base_remaining > L::BaseMetric::zero() {
                self.first()
            } else {
                return (None, L::BaseMetric::zero());
            };

        debug_assert_eq!(M::measure(&advance), M::one());

        self.base_remaining -= L::BaseMetric::measure(&advance);
        self.units_remaining -= M::one();

        (Some(tree_slice), L::BaseMetric::measure(&advance))
    }
}
