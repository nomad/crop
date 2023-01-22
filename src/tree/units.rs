use std::sync::Arc;

use super::tree_slice;
use crate::tree::{Inode, Leaf, Lnode, Metric, Node, Tree, TreeSlice};

/// An iterator over consecutive units of a particular metric.
#[derive(Clone)]
pub struct Units<'a, const FANOUT: usize, L: Leaf, M: Metric<L>> {
    /*
      Hello
    */
    #[rustfmt::skip]

    /// TODO: docs
    forward: UnitsForward<'a, FANOUT, L, M>,

    /// TODO: docs
    backward: UnitsBackward<'a, FANOUT, L, M>,

    /// The base measure of all the `TreeSlice`s yielded so far.
    yielded: L::BaseMetric,

    /// The base measure of all the `TreeSlice`s this iterator will yield.
    total: L::BaseMetric,
}

impl<'a, const FANOUT: usize, L: Leaf, M: Metric<L>> From<&'a Tree<FANOUT, L>>
    for Units<'a, FANOUT, L, M>
where
    for<'d> &'d L::Slice: Default,
{
    #[inline]
    fn from(tree: &'a Tree<FANOUT, L>) -> Units<'a, FANOUT, L, M> {
        Self {
            forward: UnitsForward::new(tree.root(), None),
            backward: UnitsBackward::new(tree.root(), None),
            yielded: L::BaseMetric::zero(),
            total: tree.base_measure(),
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
        let opts = (
            tree_slice.before,
            tree_slice.base_measure(),
            tree_slice.measure::<M>(),
            (tree_slice.start_slice, &tree_slice.start_summary),
            (tree_slice.end_slice, &tree_slice.end_summary),
        );

        Self {
            forward: UnitsForward::new(tree_slice.root(), Some(opts)),
            backward: UnitsBackward::new(tree_slice.root(), Some(opts)),
            yielded: L::BaseMetric::zero(),
            total: tree_slice.base_measure(),
        }
    }
}

impl<'a, const FANOUT: usize, L: Leaf, M: Metric<L>> Iterator
    for Units<'a, FANOUT, L, M>
{
    type Item = TreeSlice<'a, FANOUT, L>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.yielded == self.total {
            None
        } else {
            let tree_slice = self.forward.next()?;
            self.yielded += tree_slice.base_measure();
            Some(tree_slice)
        }
    }
}

impl<'a, const FANOUT: usize, L: Leaf, M: Metric<L>> DoubleEndedIterator
    for Units<'a, FANOUT, L, M>
{
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.yielded == self.total {
            None
        } else {
            let tree_slice = self.backward.previous()?;
            self.yielded += tree_slice.base_measure();
            Some(tree_slice)
        }
    }
}

impl<'a, const FANOUT: usize, L: Leaf, M: Metric<L>> std::iter::FusedIterator
    for Units<'a, FANOUT, L, M>
{
}

#[derive(Debug)]
struct UnitsForward<'a, const N: usize, L: Leaf, M: Metric<L>> {
    /// Whether `Self` has been initialized by calling
    /// [`initialize`](UnitsForward::initialize).
    is_initialized: bool,

    /// All the nodes in the stack are guaranteed to be internal nodes.
    stack: Vec<(&'a Arc<Node<N, L>>, usize)>,

    /// Guaranteed to be a leaf.
    leaf_node: &'a Arc<Node<N, L>>,

    /// TODO: docs,
    yielded_in_leaf: L::Summary,

    /// TODO: docs
    start_slice: &'a L::Slice,

    /// TODO: docs
    start_summary: L::Summary,

    /// TODO: docs
    first_slice: Option<(&'a L::Slice, &'a L::Summary)>,

    /// TODO: docs
    last_slice: Option<(&'a L::Slice, &'a L::Summary)>,

    /// TODO: docs
    base_offset: L::BaseMetric,

    /// TODO: docs
    base_yielded: L::BaseMetric,

    /// TODO: docs
    base_total: L::BaseMetric,

    /// TODO: docs
    units_yielded: M,

    /// TODO: docs
    units_total: M,
}

impl<'a, const N: usize, L: Leaf, M: Metric<L>> Clone
    for UnitsForward<'a, N, L, M>
{
    #[inline]
    fn clone(&self) -> Self {
        Self {
            stack: self.stack.clone(),
            yielded_in_leaf: self.yielded_in_leaf.clone(),
            start_summary: self.start_summary.clone(),
            ..*self
        }
    }
}

impl<'a, const N: usize, L: Leaf, M: Metric<L>> UnitsForward<'a, N, L, M> {
    /// TODO: docs
    #[inline]
    fn new(
        root: &'a Arc<Node<N, L>>,
        opt: Option<(
            L::BaseMetric,
            L::BaseMetric,
            M,
            (&'a L::Slice, &'a L::Summary),
            (&'a L::Slice, &'a L::Summary),
        )>,
    ) -> Self
    where
        for<'d> &'d L::Slice: Default,
    {
        let (base_offset, base_total, units_total, first_slice, last_slice) =
            match opt {
                Some((base_offset, base_total, units_total, start, end)) => (
                    base_offset,
                    base_total,
                    units_total,
                    Some(start),
                    Some(end),
                ),

                None => (
                    L::BaseMetric::zero(),
                    root.base_measure(),
                    root.measure::<M>(),
                    None,
                    None,
                ),
            };

        Self {
            is_initialized: false,
            stack: Vec::with_capacity(root.depth()),
            leaf_node: root,
            yielded_in_leaf: L::Summary::default(),
            start_slice: <&L::Slice>::default(),
            start_summary: L::Summary::default(),
            first_slice,
            last_slice,
            base_offset,
            base_total,
            base_yielded: L::BaseMetric::zero(),
            units_total,
            units_yielded: M::zero(),
        }
    }

    /// TODO: docs
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

                        if offset + child_measure > self.base_offset {
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
                            self.yielded_in_leaf = leaf.summary().clone();
                            self.yielded_in_leaf -= summary;

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

    /// Returns the last node in the stack together with a mutable reference to
    /// its current child index.
    #[inline]
    fn last_mut(&mut self) -> (&'a Arc<Node<N, L>>, &mut usize) {
        debug_assert!(!self.stack.is_empty());
        let last_idx = self.stack.len() - 1;
        let &mut (root, ref mut child_idx) = &mut self.stack[last_idx];
        (root, child_idx)
    }

    /// Like [`last_mut`](Self::last_mut), except the node is returned as an
    /// internal node.
    #[inline]
    fn last_as_internal_mut(&mut self) -> (&'a Inode<N, L>, &mut usize) {
        let (last, child_idx) = self.last_mut();
        // Safety: every node in the stack is an internal node.
        (unsafe { last.as_internal_unchecked() }, child_idx)
    }

    /// TODO: docs
    #[inline]
    fn next_leaf(&mut self) -> (&'a L::Slice, L::Summary) {
        debug_assert!(self.base_yielded < self.base_total);

        let mut node = loop {
            let (inode, child_idx) = self.last_as_internal_mut();

            *child_idx += 1;

            if *child_idx < inode.children().len() {
                break &inode.children()[*child_idx];
            } else if self.stack.len() > 1 {
                self.stack.pop();
            } else {
                // If we get here it means there's not a next leaf, but
                // `base_yielded + consider_extra_yielded < base_total`, so
                // there must be a next leaf.
                unreachable!();
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

                    let (slice, summary) = if self.base_yielded
                        + leaf.base_measure()
                        <= self.base_total
                    {
                        (leaf.as_slice(), leaf.summary().clone())
                    } else {
                        // TODO: explain why we can unwrap here
                        let (slice, summary) = self.last_slice.take().unwrap();
                        (slice, summary.clone())
                    };

                    return (slice, summary);
                },
            }
        }
    }

    /// TODO: docs
    #[inline]
    fn next_unit_in_leaf(&mut self) -> TreeSlice<'a, N, L> {
        debug_assert!(M::measure(&self.start_summary) > M::zero());
        debug_assert!(self.units_yielded < self.units_total);

        let yielded = L::BaseMetric::measure(&self.yielded_in_leaf);

        let (start_slice, start_summary, rest_slice, rest_summary) =
            M::split(self.start_slice, M::one(), &self.start_summary);

        self.yielded_in_leaf += &start_summary;
        self.start_slice = rest_slice;
        self.start_summary = rest_summary;

        self.base_yielded += L::BaseMetric::measure(&start_summary);
        self.units_yielded += M::one();

        TreeSlice {
            root: self.leaf_node,
            before: yielded,
            summary: start_summary.clone(),
            end_slice: start_slice,
            end_summary: start_summary.clone(),
            start_slice,
            start_summary,
            num_leaves: 1,
        }
    }

    /// TODO: docs
    #[inline]
    fn next_unit_in_stack(&mut self) -> TreeSlice<'a, N, L> {
        debug_assert_eq!(M::measure(&self.start_summary), M::zero());
        debug_assert!(self.units_yielded < self.units_total);

        // A previous call to `next_unit_in_leaf` might've left the start slice
        // empty.
        if L::BaseMetric::measure(&self.start_summary) == L::BaseMetric::zero()
        {
            let (next_slice, next_summary) = self.next_leaf();
            self.yielded_in_leaf = L::Summary::default();
            self.start_slice = next_slice;
            self.start_summary = next_summary;

            if M::measure(&self.start_summary) > M::zero() {
                return self.next_unit_in_leaf();
            }
        }

        let start_slice = self.start_slice;
        let start_summary = self.start_summary.clone();

        let mut yielded = self.yielded_in_leaf.clone();
        let mut summary = start_summary.clone();
        let mut num_leaves = 1;

        // 1: find the root.

        'outer: loop {
            let (node, mut child_idx) = self.stack.pop().unwrap();

            // Safety: every node in the stack is an internal node.
            let inode = unsafe { node.as_internal_unchecked() };

            for child in &inode.children()[..child_idx] {
                yielded += child.summary();
            }

            if inode.measure::<M>() > M::measure(&yielded) {
                // This is the root and it needs to be pushed back onto the
                // stack.

                child_idx += 1;

                for child in &inode.children()[child_idx..] {
                    if child.measure::<M>() > M::zero() {
                        self.stack.push((node, child_idx));
                        break 'outer;
                    } else {
                        child_idx += 1;
                        summary += child.summary();
                        num_leaves += child.num_leaves();
                    }
                }

                unreachable!();
            } else {
                for child in &inode.children()[child_idx + 1..] {
                    summary += child.summary();
                    num_leaves += child.num_leaves();
                }
            }
        }

        // 2.

        let (root, child_idx) = self.last_mut();

        // Safety: every node in the stack is an internal node.
        let mut node =
            unsafe { &root.as_internal_unchecked().children()[*child_idx] };

        let (leaf_slice, leaf_summary) = 'outer: loop {
            match &**node {
                Node::Internal(inode) => {
                    for (idx, child) in inode.children().iter().enumerate() {
                        if child.measure::<M>() != M::zero() {
                            self.stack.push((node, idx));
                            node = child;
                            continue 'outer;
                        } else {
                            summary += child.summary();
                            num_leaves += child.num_leaves();
                        }
                    }
                },

                Node::Leaf(leaf) => {
                    self.leaf_node = node;

                    let (slice, summary) = if self.base_yielded
                        + L::BaseMetric::measure(&summary)
                        + leaf.base_measure()
                        <= self.base_total
                    {
                        (leaf.as_slice(), leaf.summary())
                    } else {
                        self.last_slice.take().unwrap()
                    };

                    break (slice, summary);
                },
            }
        };

        debug_assert!(M::measure(leaf_summary) >= M::one());

        // 3.

        let (left_slice, left_summary, right_slice, right_summary) =
            M::split(leaf_slice, M::one(), leaf_summary);

        summary += &left_summary;
        num_leaves += 1;

        self.base_yielded += L::BaseMetric::measure(&summary);
        self.units_yielded += M::one();

        if L::BaseMetric::measure(&right_summary) > L::BaseMetric::zero() {
            self.yielded_in_leaf = left_summary.clone();
            self.start_slice = right_slice;
            self.start_summary = right_summary;
        } else if self.base_yielded < self.base_total {
            let (next_slice, next_summary) = self.next_leaf();
            self.yielded_in_leaf = L::Summary::default();
            self.start_slice = next_slice;
            self.start_summary = next_summary;
        }

        TreeSlice {
            root,
            before: L::BaseMetric::measure(&yielded),
            summary,
            end_slice: left_slice,
            end_summary: left_summary,
            start_slice,
            start_summary,
            num_leaves,
        }
    }

    /// TODO: docs
    #[inline]
    fn yield_last(&mut self) -> TreeSlice<'a, N, L> {
        debug_assert_eq!(self.units_yielded, self.units_total);
        debug_assert!(self.base_yielded < self.base_total);

        let (mut yielded, start_slice, start_summary) =
            if L::BaseMetric::measure(&self.start_summary)
                == L::BaseMetric::zero()
            {
                let (next_slice, next_summary) = self.next_leaf();
                (L::BaseMetric::zero(), next_slice, next_summary)
            } else {
                (
                    L::BaseMetric::measure(&self.yielded_in_leaf),
                    self.start_slice,
                    std::mem::take(&mut self.start_summary),
                )
            };

        let mut summary = start_summary.clone();
        let mut num_leaves = 1;

        // First, check if the leaf node is the root. If it is we're done.
        if self.base_yielded + L::BaseMetric::measure(&start_summary)
            == self.base_total
        {
            return TreeSlice {
                root: self.leaf_node,
                before: yielded,
                summary,
                end_slice: start_slice,
                end_summary: start_summary.clone(),
                start_slice,
                start_summary,
                num_leaves,
            };
        }

        // 1: find the root in the stack.
        //
        // The root is the deepest node in the stack that fully contains the
        // `(base_offset + base_yielded)..(base_offset + base_total)` range.

        let mut range = (self.base_offset + self.base_yielded)
            ..(self.base_offset + self.base_total);

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

        // Keep the old code to increase `summary`, `num_leaves`, `yielded`,
        // except it starts from `root_idx + 1` instead of `root_idx`.
        //
        // At the root_idx level do the same until `child_idx`, skip
        // `child_idx`, then check which child contain the end_slice from
        // `(child_idx + 1)..`.

        // 2: increase `yielded`, `summary`, `num_leaves`.

        for &(node, child_idx) in &self.stack[root_idx + 1..] {
            // Safety: every node in the stack is an internal node.
            let inode = unsafe { node.as_internal_unchecked() };

            for child in &inode.children()[..child_idx] {
                yielded += child.base_measure();
            }

            for child in &inode.children()[child_idx + 1..] {
                summary += child.summary();
                num_leaves += child.num_leaves();
            }
        }

        let (root, child_idx) = self.stack[root_idx];

        // Safety: every node in the stack is an internal node.
        let inode = unsafe { root.as_internal_unchecked() };

        let mut measured = L::BaseMetric::zero();

        for child in &inode.children()[..child_idx] {
            let child_measure = child.base_measure();
            measured += child_measure;
            yielded += child_measure;
        }

        measured += inode.children()[child_idx].base_measure();

        // This is the children of the root node that contains the ending
        // slice.
        let mut node = inode.first();

        for child in &inode.children()[child_idx + 1..] {
            let child_measure = child.base_measure();

            if measured + child_measure >= range.end {
                node = child;
                break;
            } else {
                summary += child.summary();
                num_leaves += child.num_leaves();
                measured += child_measure;
            }
        }

        let (end_slice, end_summary) = 'outer: loop {
            match &**node {
                Node::Internal(inode) => {
                    for child in inode.children() {
                        let child_measure = child.base_measure();

                        if measured + child_measure >= range.end {
                            node = child;
                            continue 'outer;
                        } else {
                            summary += child.summary();
                            num_leaves += child.num_leaves();
                            measured += child_measure;
                        }
                    }

                    unreachable!();
                },

                Node::Leaf(leaf) => {
                    break (match self.last_slice.take() {
                        Some(last) => last,
                        None => (leaf.as_slice(), leaf.summary()),
                    })
                },
            }
        };

        summary += end_summary;
        num_leaves += 1;

        self.base_yielded += L::BaseMetric::measure(&summary);

        debug_assert_eq!(self.base_yielded, self.base_total);

        TreeSlice {
            root,
            before: yielded,
            summary,
            start_slice,
            start_summary,
            end_slice,
            end_summary: end_summary.clone(),
            num_leaves,
        }
    }

    #[inline]
    fn next(&mut self) -> Option<TreeSlice<'a, N, L>> {
        if !self.is_initialized {
            self.initialize();
        }

        if M::measure(&self.start_summary) > M::zero() {
            Some(self.next_unit_in_leaf())
        } else if self.units_yielded < self.units_total {
            Some(self.next_unit_in_stack())
        } else if self.base_yielded < self.base_total {
            Some(self.yield_last())
        } else {
            None
        }
    }
}

#[derive(Debug)]
struct UnitsBackward<'a, const N: usize, L: Leaf, M: Metric<L>> {
    /// Whether `Self` has been initialized by calling
    /// [`initialize`](Self::initialize()).
    is_initialized: bool,

    /// The path from the root node down to `leaf_node`.
    stack: Vec<(&'a Arc<Node<N, L>>, usize)>,

    /// The current leaf node.
    leaf_node: &'a Arc<Node<N, L>>,

    /// How much of `leaf_node`'s summary has already been yielded.
    yielded_in_leaf: L::Summary,

    /// The `end_slice` field of the next `TreeSlice` that's returned by
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

    /// The start of the yielding range as an offset into the root.
    base_offset: L::BaseMetric,

    /// How many base units have been yielded so far. It gets increased every
    /// time [`previous`](Self::previous()) gets called.
    base_yielded: L::BaseMetric,

    /// The total number of base units contained in the yielding range. It
    /// follows that the yielding range is `base_offset..(base_offset +
    /// base_total)` in the root.
    base_total: L::BaseMetric,

    /// How many `M`-units have been yielded so far. It gets increased (usually
    /// by `M::one()` unless we're calling [`remainder`][1]), every time
    /// [`previous`][2] gets called.
    ///
    /// [1]: Self::remainder()
    /// [2]: Self::previous()
    units_yielded: M,

    /// The total number of `M`-units contained in the yielding range.
    units_total: M,
}

impl<'a, const N: usize, L: Leaf, M: Metric<L>> Clone
    for UnitsBackward<'a, N, L, M>
{
    #[inline]
    fn clone(&self) -> Self {
        Self {
            stack: self.stack.clone(),
            yielded_in_leaf: self.yielded_in_leaf.clone(),
            end_summary: self.end_summary.clone(),
            ..*self
        }
    }
}

impl<'a, const N: usize, L: Leaf, M: Metric<L>> UnitsBackward<'a, N, L, M> {
    /*
       NOTE: this implementation should be a pretty close port of
       `UnitsForward` and yet iterating backwards over `large.txt` takes almost
       twice as much as iterating forward (while for `tiny.txt` this is only
       5-10% slower which is expected).

       TODO: figure out why.
    */

    /// Initializes a new [`UnitsBackward`].
    ///
    /// Note: check out the doc comment for [`UnitsForward::new()`] as it
    /// applies 1:1 to this.
    #[inline]
    fn new(
        root: &'a Arc<Node<N, L>>,
        opts: Option<(
            L::BaseMetric,
            L::BaseMetric,
            M,
            (&'a L::Slice, &'a L::Summary),
            (&'a L::Slice, &'a L::Summary),
        )>,
    ) -> Self
    where
        for<'d> &'d L::Slice: Default,
    {
        let (base_offset, base_total, units_total, first_slice, last_slice) =
            match opts {
                Some((base_offset, base_total, units_total, start, end)) => (
                    base_offset,
                    base_total,
                    units_total,
                    Some(start),
                    Some(end),
                ),

                None => (
                    L::BaseMetric::zero(),
                    root.base_measure(),
                    root.measure::<M>(),
                    None,
                    None,
                ),
            };

        Self {
            is_initialized: false,
            stack: Vec::with_capacity(root.depth()),
            leaf_node: root,
            yielded_in_leaf: L::Summary::default(),
            end_slice: <&L::Slice>::default(),
            end_summary: L::Summary::default(),
            first_slice,
            last_slice,
            base_offset,
            base_total,
            base_yielded: L::BaseMetric::zero(),
            units_total,
            units_yielded: M::zero(),
        }
    }

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

        let last_slice_offset = self.base_offset + self.base_total;

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
                            self.yielded_in_leaf = leaf.summary().clone();
                            self.yielded_in_leaf -= summary;

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
    /// mutate any state and instead of returning previous the leaf node with a
    /// non-zero `M`-measure it returns the leaf node containing
    /// [`first_slice`](2), or the first leaf node in the root if that's not
    /// set.
    ///
    /// Note: it assumes that leaf node is different than [`leaf_node`](3).
    /// That case should be handled by the caller.
    ///
    /// [1]: UnitsBackward::previous_leaf_with_measure()
    /// [2]: UnitsBackward::first_slice()
    /// [3]: UnitsBackward::leaf_node()
    #[inline]
    fn first_leaf(
        &self,
    ) -> (&'a Lnode<L>, &'a Arc<Node<N, L>>, L::BaseMetric, L::Summary, usize)
    {
        // Step 1: find the index of deepest node in the stack that fully
        // contains the `base_offset..(base_offset + self.base_total -
        // self.base_yielded)` range.

        let mut range = self.base_offset
            ..(self.base_offset + self.base_total - self.base_yielded);

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

        // Step 2: traverse down the stack starting from the node following the
        // root increase `after`, `summary` and `leaf_count` as you go.

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
    /// should return `None`. #[inline]
    fn first(&mut self) -> TreeSlice<'a, N, L> {
        debug_assert!(
            self.units_total == M::zero()
                || self.units_yielded + M::one() == self.units_total
        );
        debug_assert!(self.base_yielded < self.base_total);

        // First, check if the current leaf node is the root. If it is we're
        // done.
        if self.base_yielded + L::BaseMetric::measure(&self.end_summary)
            == self.base_total
        {
            let summary = std::mem::take(&mut self.end_summary);

            self.base_yielded += L::BaseMetric::measure(&summary);

            return TreeSlice {
                root: self.leaf_node,
                before: L::BaseMetric::zero(),
                start_slice: self.end_slice,
                start_summary: summary.clone(),
                end_slice: self.end_slice,
                end_summary: summary.clone(),
                summary,
                num_leaves: 1,
            };
        }

        let end_slice = self.end_slice;
        let end_summary = std::mem::take(&mut self.end_summary);

        let (first_leaf, root, after, mut summary, leaf_count) =
            self.first_leaf();

        summary += &end_summary;

        let (start_slice, start_summary) = match self.first_slice.take() {
            Some((slice, summary)) => (slice, summary.clone()),
            None => (first_leaf.as_slice(), first_leaf.summary().clone()),
        };

        summary += &start_summary;

        let before = root.base_measure()
            - after
            - L::BaseMetric::measure(&self.yielded_in_leaf)
            - L::BaseMetric::measure(&summary);

        self.base_yielded += L::BaseMetric::measure(&summary);

        TreeSlice {
            root,
            before,
            start_slice,
            start_summary,
            end_slice,
            end_summary,
            summary,
            // +2 to account for the leaves containing the first and last
            // slices.
            num_leaves: leaf_count + 2,
        }
    }

    /// Yields the previous unit in the current `self.leaf_node`. To do this
    /// correcly we actually need `self.end_slice` to measure in at at least 2
    /// units.
    #[inline]
    fn previous_unit_in_leaf(&mut self) -> TreeSlice<'a, N, L> {
        debug_assert!(M::measure(&self.end_summary) > M::one());
        debug_assert!(self.units_yielded < self.units_total);

        let (left_slice, left_summary, right_slice, right_summary) = M::split(
            self.end_slice,
            M::measure(&self.end_summary) - M::one(),
            &self.end_summary,
        );

        let offset = L::BaseMetric::measure(&left_summary);

        self.yielded_in_leaf += &right_summary;
        self.end_slice = left_slice;
        self.end_summary = left_summary;

        self.base_yielded += L::BaseMetric::measure(&right_summary);
        self.units_yielded += M::one();

        TreeSlice {
            root: self.leaf_node,
            before: offset,
            summary: right_summary.clone(),
            end_slice: right_slice,
            end_summary: right_summary.clone(),
            start_slice: right_slice,
            start_summary: right_summary,
            num_leaves: 1,
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
    /// Invariants: [`Leaf`] is guaranteed to have an `M`-measure of at least
    /// `M::one()`.
    #[inline]
    fn previous_leaf_with_measure(
        &mut self,
    ) -> (&'a Lnode<L>, &'a Arc<Node<N, L>>, L::BaseMetric, L::Summary, usize)
    {
        debug_assert!(self.units_yielded < self.units_total);

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

    /// Yields the next unit in the iterating range. This is the general
    /// function that gets called when the next unit is not the first, the last
    /// and it's not contained in `self.leaf_node`. The root of the returned
    /// `TreeSlice` is a node in the stack so it's guaranteed to be an internal
    /// node.
    ///
    /// Note: this uses [`previous_leaf_with_measure`][0] internally so it should
    /// only be called when `self.units_yielded < self.units_total`.
    ///
    /// [0]: UnitsBackward::previous_leaf_with_measure()
    #[inline]
    fn previous_unit_in_range(&mut self) -> TreeSlice<'a, N, L> {
        debug_assert!(self.units_yielded < self.units_total);

        let (leaf, root, after, mut summary, mut leaf_count) =
            self.previous_leaf_with_measure();

        let end_slice = self.end_slice;
        let end_summary = self.end_summary.clone();

        summary += &end_summary;
        leaf_count += 1;

        let (slice, slice_summary) = {
            let contains_first_slice = (self.base_offset + self.base_total
                - self.base_yielded
                - L::BaseMetric::measure(&summary)
                - leaf.base_measure())
                < self.base_offset;

            if contains_first_slice {
                self.first_slice.take().unwrap()
            } else {
                (leaf.as_slice(), leaf.summary())
            }
        };

        let (left_slice, left_summary, right_slice, right_summary) =
            M::split(slice, M::measure(&slice_summary), slice_summary);

        if L::BaseMetric::measure(&right_summary) > L::BaseMetric::zero() {
            summary += &right_summary;
            leaf_count += 1;

            let offset = root.base_measure()
                - after
                - L::BaseMetric::measure(&self.yielded_in_leaf)
                - L::BaseMetric::measure(&summary);

            self.yielded_in_leaf = right_summary.clone();
            self.end_slice = left_slice;
            self.end_summary = left_summary;

            self.base_yielded += L::BaseMetric::measure(&summary);
            self.units_yielded += M::measure(&summary);

            TreeSlice {
                root,
                before: offset,
                summary,
                start_slice: right_slice,
                start_summary: right_summary,
                end_slice,
                end_summary,
                num_leaves: leaf_count,
            }
        } else {
            self.yielded_in_leaf = L::Summary::default();
            self.end_slice = slice;
            self.end_summary = slice_summary.clone();

            self.base_yielded += L::BaseMetric::measure(&summary);
            self.units_yielded += M::measure(&summary);

            let next_leaf = self.next_leaf();

            if leaf_count == 1 {
                return TreeSlice {
                    root: next_leaf,
                    before: L::BaseMetric::zero(),
                    summary,
                    start_slice: end_slice,
                    start_summary: end_summary.clone(),
                    end_slice,
                    end_summary,
                    num_leaves: 1,
                };
            }

            let (root, before) = {
                let start =
                    self.base_offset + self.base_total - self.base_yielded;

                let (root, range) = (
                    self.stack[0].0,
                    start..(start + L::BaseMetric::measure(&summary)),
                );

                // TODO: is there a faster way to do this using the stack?
                let (root, range) =
                    tree_slice::deepest_node_containing_range(root, range);

                (root, range.start)
            };

            // Safety: `next_leaf` is guaranteed to be a leaf node by
            // `Self::next_leaf()`.
            let next_leaf = unsafe { next_leaf.as_leaf_unchecked() };

            TreeSlice {
                root,
                before,
                summary,
                start_slice: next_leaf.as_slice(),
                start_summary: next_leaf.summary().clone(),
                end_slice,
                end_summary,
                num_leaves: leaf_count,
            }
        }
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
    /// It also follows that if `M` is the `BaseMetric` this function should
    /// always return `None`.
    ///
    /// Note: this uses [`next_something`][2] internally so it actually assumes
    /// `units_total > M::one()`. If there are zero units in the yielding range
    /// [`yield_first`][3] should be called instead.
    ///
    /// [1]: UnitsBackwards::next()
    /// [2]: UnitsBackwards::next_something()
    /// [3]: UnitsBackwards::yield_first()
    #[inline]
    fn remainder(&mut self) -> Option<TreeSlice<'a, N, L>> {
        debug_assert_eq!(self.base_yielded, L::BaseMetric::zero());
        debug_assert!(self.base_total > L::BaseMetric::zero());
        debug_assert!(self.units_total > M::zero());

        if M::measure(&self.end_summary) > M::zero() {
            let (left_slice, left_summary, right_slice, right_summary) =
                M::split(
                    self.end_slice,
                    M::measure(&self.end_summary),
                    &self.end_summary,
                );

            if L::BaseMetric::measure(&right_summary) > L::BaseMetric::zero() {
                let offset = L::BaseMetric::measure(&left_summary);

                self.yielded_in_leaf += &right_summary;
                self.end_slice = left_slice;
                self.end_summary = left_summary;

                self.base_yielded += L::BaseMetric::measure(&right_summary);

                Some(TreeSlice {
                    root: self.leaf_node,
                    before: offset,
                    summary: right_summary.clone(),
                    end_slice: right_slice,
                    end_summary: right_summary.clone(),
                    start_slice: right_slice,
                    start_summary: right_summary,
                    num_leaves: 1,
                })
            } else {
                None
            }
        } else {
            Some(self.previous_unit_in_range())
        }
    }

    #[inline]
    fn previous(&mut self) -> Option<TreeSlice<'a, N, L>> {
        if !self.is_initialized {
            self.initialize();

            if self.base_total > L::BaseMetric::zero()
                && self.units_total > M::zero()
            {
                if let Some(rem) = self.remainder() {
                    debug_assert_eq!(rem.measure::<M>(), M::zero());
                    return Some(rem);
                }
            }
        }

        if M::measure(&self.end_summary) > M::one() {
            Some(self.previous_unit_in_leaf())
        } else if self.units_yielded + M::one() < self.units_total {
            Some(self.previous_unit_in_range())
        } else if self.base_yielded < self.base_total {
            Some(self.first())
        } else {
            None
        }
    }
}
