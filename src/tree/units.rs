use std::sync::Arc;

use crate::tree::{Leaf, Lnode, Metric, Node, Tree, TreeSlice};

/// An iterator over consecutive units of a particular metric.
pub struct Units<'a, const FANOUT: usize, L: Leaf, M: Metric<L>> {
    /// TODO: docs
    forward: UnitsForward<'a, FANOUT, L, M>,

    /// TODO: docs
    backward: UnitsBackward<'a, FANOUT, L, M>,

    /// TODO: docs
    yielded: L::BaseMetric,

    /// TODO: docs
    total: L::BaseMetric,
}

impl<'a, const FANOUT: usize, L: Leaf, M: Metric<L>> Clone
    for Units<'a, FANOUT, L, M>
{
    #[inline]
    fn clone(&self) -> Self {
        Self {
            forward: self.forward.clone(),
            backward: self.backward.clone(),
            ..*self
        }
    }
}

impl<'a, const FANOUT: usize, L: Leaf, M: Metric<L>> From<&'a Tree<FANOUT, L>>
    for Units<'a, FANOUT, L, M>
where
    for<'d> &'d L::Slice: Default,
{
    #[inline]
    fn from(tree: &'a Tree<FANOUT, L>) -> Units<'a, FANOUT, L, M> {
        Self {
            forward: UnitsForward::new(
                tree.root(),
                None,
                M::measure(tree.summary()),
            ),
            backward: UnitsBackward::new(tree.root(), None),
            yielded: L::BaseMetric::zero(),
            total: L::BaseMetric::measure(tree.summary()),
        }
    }
}

impl<'a, const FANOUT: usize, L: Leaf, M: Metric<L>>
    From<&'a TreeSlice<'a, FANOUT, L>> for Units<'a, FANOUT, L, M>
{
    #[inline]
    fn from(
        tree_slice: &'a TreeSlice<'a, FANOUT, L>,
    ) -> Units<'a, FANOUT, L, M> {
        // TODO: this doesn't yet work.

        todo!();

        // let front = UnitsFront::new(
        //     tree_slice.root(),
        //     None,
        //     M::measure(tree_slice.summary()),
        // );

        // Self {
        //     front,

        //     initialized_back: false,
        //     stack_back: Vec::with_capacity(stack_capacity),
        //     end_slice: tree_slice.end_slice(),
        //     end_summary: tree_slice.end_summary().clone(),

        //     yielded: L::BaseMetric::zero(),
        //     total: L::BaseMetric::measure(tree_slice.summary()),

        //     i: 0,
        // }
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
            let tree_slice = self.forward.next();
            self.yielded += L::BaseMetric::measure(tree_slice.summary());
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
            let tree_slice = self.backward.next();
            self.yielded += L::BaseMetric::measure(tree_slice.summary());
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
    /// TODO: docs
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
    yielded: M,

    /// TODO: docs
    total: M,
}

impl<'a, const N: usize, L: Leaf, M: Metric<L>> Clone
    for UnitsForward<'a, N, L, M>
{
    #[inline]
    fn clone(&self) -> Self {
        Self {
            stack: self.stack.clone(),
            start_summary: self.start_summary.clone(),
            yielded_in_leaf: self.yielded_in_leaf.clone(),
            ..*self
        }
    }
}

impl<'a, const N: usize, L: Leaf, M: Metric<L>> UnitsForward<'a, N, L, M> {
    #[inline]
    fn new(
        root: &'a Arc<Node<N, L>>,
        start: Option<(&'a L::Slice, L::Summary)>,
        total: M,
    ) -> Self
    where
        for<'d> &'d L::Slice: Default,
    {
        let (start_slice, start_summary) = start.unwrap_or_default();

        Self {
            is_initialized: false,
            stack: Vec::with_capacity(root.depth()),
            leaf_node: root,
            yielded_in_leaf: L::Summary::default(),
            start_slice,
            start_summary,
            yielded: M::zero(),
            total,
        }
    }

    /// TODO: docs
    #[inline]
    fn initialize(&mut self) {
        debug_assert!(!self.is_initialized);

        self.is_initialized = true;

        let mut node = self.leaf_node;

        loop {
            match &**node {
                Node::Internal(inode) => {
                    self.push(node, 0);
                    node = inode.first();
                    continue;
                },

                Node::Leaf(leaf) => {
                    self.leaf_node = node;

                    // If the base measure of `start_summary` is zero it means
                    // Self was created from a Tree, in which case the start
                    // slice should be this leaf. If it's > 0 it was created
                    // from a TreeSlice, and we can leave `start_slice` and
                    // `start_summary` untouched.
                    if L::BaseMetric::measure(&self.start_summary)
                        == L::BaseMetric::zero()
                    {
                        self.start_slice = leaf.as_slice();
                        self.start_summary = leaf.summary().clone();
                    } else {
                        // To handle this correctly we'd have to land to the
                        // leaf containing the start_slice, which we don't
                        // because we always go to the first leaf.
                        todo!();
                    }

                    return;
                },
            }
        }
    }

    #[inline]
    fn last_mut(&mut self) -> (&'a Arc<Node<N, L>>, &mut usize) {
        debug_assert!(!self.stack.is_empty());

        let last_idx = self.stack.len() - 1;

        let &mut (root, ref mut visited) = &mut self.stack[last_idx];

        (root, visited)
    }

    #[inline]
    fn push(&mut self, node: &'a Arc<Node<N, L>>, child_idx: usize) {
        debug_assert!(node.is_internal() || node.is_leaf() && child_idx == 0);
        self.stack.push((node, child_idx));
    }

    #[inline]
    fn pop(&mut self) -> Option<(&'a Arc<Node<N, L>>, usize)> {
        self.stack.pop()
    }

    /// TODO: docs
    #[inline]
    fn next_leaf(&mut self) -> Option<&'a Lnode<L>> {
        let mut node = loop {
            let (node, visited) = self.last_mut();

            // Safety: TODO
            let inode = unsafe { node.as_internal_unchecked() };

            *visited += 1;

            if *visited < inode.children().len() {
                break &inode.children()[*visited];
            } else if self.stack.len() > 1 {
                self.pop();
            } else {
                return None;
            }
        };

        loop {
            match &**node {
                Node::Internal(inode) => {
                    self.push(node, 0);
                    node = inode.first();
                    continue;
                },

                Node::Leaf(leaf) => {
                    self.leaf_node = node;
                    return Some(leaf);
                },
            }
        }
    }

    /// TODO: docs
    #[inline]
    fn next_unit_in_leaf(&mut self) -> TreeSlice<'a, N, L> {
        debug_assert!(M::measure(&self.start_summary) > M::zero());
        debug_assert!(self.yielded <= self.total);

        let root = self.leaf_node;

        let yielded = self.yielded_in_leaf.clone();

        let (start_slice, start_summary, rest_slice, rest_summary) =
            M::split(self.start_slice, M::one(), &self.start_summary);

        if L::BaseMetric::measure(&rest_summary) > L::BaseMetric::zero() {
            self.yielded_in_leaf += &start_summary;
            self.start_slice = rest_slice;
            self.start_summary = rest_summary;
        } else if let Some(leaf) = self.next_leaf() {
            self.yielded_in_leaf = L::Summary::default();
            self.start_slice = leaf.as_slice();
            self.start_summary = leaf.summary().clone();
        }

        TreeSlice {
            root,
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
        debug_assert!(M::measure(&self.start_summary) == M::zero());
        debug_assert!(self.yielded <= self.total);

        let start_slice = self.start_slice;
        let start_summary = self.start_summary.clone();

        let mut yielded = self.yielded_in_leaf.clone();

        let mut summary = start_summary.clone();

        let mut num_leaves = 1;

        // 1: find the root.

        'outer: loop {
            let (node, mut child_idx) = self.pop().unwrap();

            // Safety: all the nodes in the stack except for the last one are
            // guaranteed to be internal nodes, and the last node has been
            // popped at the start of this function.
            let inode = unsafe { node.as_internal_unchecked() };

            for child in &inode.children()[..child_idx] {
                yielded += child.summary();
            }

            if M::measure(inode.summary()) > M::measure(&yielded) {
                // This is the root and it needs to be pushed back onto the
                // stack.

                child_idx += 1;

                for child in &inode.children()[child_idx..] {
                    if M::measure(child.summary()) > M::zero() {
                        self.push(node, child_idx);
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

        let (root, visited) = self.last_mut();

        let mut node =
            unsafe { &root.as_internal_unchecked().children()[*visited] };

        let leaf = 'outer: loop {
            match &**node {
                Node::Internal(inode) => {
                    for (idx, child) in inode.children().iter().enumerate() {
                        let (child_summary, child_leaves) = match &**child {
                            Node::Internal(i) => (i.summary(), i.num_leaves()),
                            Node::Leaf(l) => (l.summary(), 1),
                        };

                        if M::measure(child_summary) != M::zero() {
                            self.push(node, idx);
                            node = child;
                            continue 'outer;
                        } else {
                            summary += child_summary;
                            num_leaves += child_leaves;
                        }
                    }
                },

                Node::Leaf(leaf) => {
                    self.leaf_node = node;
                    break leaf;
                },
            }
        };

        // 3.

        let (end_slice, end_summary, rest_slice, rest_summary) =
            M::split(leaf.as_slice(), M::one(), leaf.summary());

        if L::BaseMetric::measure(&rest_summary) > L::BaseMetric::zero() {
            self.yielded_in_leaf = end_summary.clone();
            self.start_slice = rest_slice;
            self.start_summary = rest_summary;
        } else if let Some(leaf) = self.next_leaf() {
            self.yielded_in_leaf = L::Summary::default();
            self.start_slice = leaf.as_slice();
            self.start_summary = leaf.summary().clone();
        }

        summary += &end_summary;
        num_leaves += 1;

        TreeSlice {
            root,
            before: yielded,
            summary,
            end_slice,
            end_summary,
            start_slice,
            start_summary,
            num_leaves,
        }
    }

    /// TODO: docs
    #[inline]
    fn yield_remaining(&mut self) -> TreeSlice<'a, N, L> {
        debug_assert!(M::measure(&self.start_summary) == M::zero());
        debug_assert!(self.yielded > self.total);

        let start_slice = self.start_slice;
        let start_summary = self.start_summary.clone();

        let mut yielded = self.yielded_in_leaf.clone();

        let mut summary = start_summary.clone();

        let mut num_leaves = 1;

        // 1: find the root in the stack.

        let root_idx = {
            let mut root_idx = self.stack.len();

            for (idx, &(node, visited)) in self.stack.iter().enumerate() {
                // Safety: all nodes in the stack except for the last one
                // are guaranteed to be internal nodes, and the last node has
                // been popped at the start of this function.
                let inode = unsafe { node.as_internal_unchecked() };

                if visited < inode.children().len() - 1 {
                    root_idx = idx;
                    break;
                }
            }

            root_idx
        };

        if root_idx == self.stack.len() {
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

        // 2: increase `yielded`, `summary`, `num_leaves`.

        for _ in root_idx..(self.stack.len() - 1) {
            let (node, visited) = self.pop().unwrap();

            // Safety: same as above.
            let inode = unsafe { node.as_internal_unchecked() };

            for child in &inode.children()[..visited] {
                yielded += child.summary();
            }

            for child in &inode.children()[visited + 1..] {
                summary += child.summary();
                num_leaves += child.num_leaves();
            }
        }

        let (root, visited) = self.last_mut();

        // Safety: same as above.
        let inode = unsafe { root.as_internal_unchecked() };

        for child in &inode.children()[..*visited] {
            yielded += child.summary();
        }

        for child in &inode.children()[*visited + 1..] {
            debug_assert_eq!(M::measure(child.summary()), M::zero());

            summary += child.summary();
            num_leaves += child.num_leaves();
        }

        // 3: get to the last leaf.

        let last_leaf = {
            let mut last = inode.last();

            loop {
                match &**last {
                    Node::Internal(inode) => {
                        last = inode.last();
                    },
                    Node::Leaf(leaf) => {
                        break leaf;
                    },
                }
            }
        };

        TreeSlice {
            root,
            before: yielded,
            summary,
            start_slice,
            start_summary,
            num_leaves,
            end_slice: last_leaf.as_slice(),
            end_summary: last_leaf.summary.clone(),
        }
    }

    #[inline]
    fn next(&mut self) -> TreeSlice<'a, N, L> {
        if !self.is_initialized {
            self.initialize();
        }

        debug_assert!(
            L::BaseMetric::measure(&self.start_summary)
                > L::BaseMetric::zero()
        );

        self.yielded += M::one();

        // TreeSlice spans leaf root.
        if M::measure(&self.start_summary) > M::zero() {
            self.next_unit_in_leaf()
        }
        // All units have been yielded but the range has not been
        // exhausted, it means there's a final TreeSlice to yield
        // containing the rest.
        else if self.yielded > self.total {
            self.yield_remaining()
        }
        // This is the general case.
        else {
            self.next_unit_in_stack()
        }
    }
}

#[derive(Debug)]
struct UnitsBackward<'a, const N: usize, L: Leaf, M: Metric<L>> {
    /// TODO: docs
    is_initialized: bool,

    /// TODO: docs
    stack: Vec<(&'a Arc<Node<N, L>>, usize, L::Summary)>,

    /// TODO: docs
    end_slice: &'a L::Slice,

    /// TODO: docs
    end_summary: L::Summary,

    /// TODO: docs
    yielded: M,
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

impl<'a, const N: usize, L: Leaf, M: Metric<L>> UnitsBackward<'a, N, L, M> {
    #[inline]
    fn new(
        root: &'a Arc<Node<N, L>>,
        end: Option<(&'a L::Slice, L::Summary)>,
    ) -> Self
    where
        for<'d> &'d L::Slice: Default,
    {
        let (end_slice, end_summary) = end.unwrap_or_default();

        let mut stack = Vec::with_capacity(root.depth());
        stack.push((root, 0, L::Summary::default()));

        Self {
            is_initialized: false,
            stack,
            end_slice,
            end_summary,
            yielded: M::zero(),
        }
    }

    #[inline]
    fn initialize(&mut self) {}

    #[inline]
    fn next(&mut self) -> TreeSlice<'a, N, L> {
        if !self.is_initialized {
            self.initialize();
        }

        debug_assert!(
            L::BaseMetric::measure(&self.end_summary) > L::BaseMetric::zero()
        );

        todo!();
    }
}
