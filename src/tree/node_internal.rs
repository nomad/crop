use std::sync::Arc;

use super::{Leaf, Lnode, Metric, Node};

/// Invariants: guaranteed to contain at least one child node.
#[derive(Clone)]
pub(super) struct Inode<const N: usize, L: Leaf> {
    pub(super) children: Vec<Arc<Node<N, L>>>,
    depth: usize,
    num_leaves: usize,
    summary: L::Summary,
}

impl<const N: usize, L: Leaf> std::fmt::Debug for Inode<N, L> {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        if !f.alternate() {
            f.debug_struct("Inode")
                .field("children", &self.children)
                .field("depth", &self.depth)
                .field("num_leaves", &self.num_leaves)
                .field("summary", &self.summary)
                .finish()
        } else {
            pretty_print_inode(self, &mut String::new(), "", 0, f)
        }
    }
}

impl<const N: usize, L: Leaf> Default for Inode<N, L> {
    #[inline]
    fn default() -> Self {
        Self {
            children: Vec::with_capacity(N),
            depth: 1,
            num_leaves: 0,
            summary: Default::default(),
        }
    }
}

impl<const N: usize, L: Leaf> Inode<N, L> {
    pub(super) fn assert_invariants(&self) {
        assert!(
            self.children().len() >= Self::min_children(),
            "An internal node of depth {} was supposed to contain at least \
             {} children but actually contains {}",
            self.depth(),
            Self::min_children(),
            self.children().len()
        );

        assert!(
            self.children().len() <= Self::max_children(),
            "An internal node of depth {} was supposed to contain at most {} \
             children but actually contains {}",
            self.depth(),
            Self::max_children(),
            self.children().len()
        );

        let actual_leaves =
            self.children().iter().map(|c| c.num_leaves()).sum::<usize>();

        assert_eq!(
            self.num_leaves,
            actual_leaves,
            "An internal node of depth {} thought it contained {} leaves in \
             its subtree, but actually contains {}",
            self.depth(),
            self.num_leaves,
            actual_leaves
        );

        for child in self.children() {
            assert_eq!(
                self.depth(),
                child.depth() + 1,
                "An internal node at depth {} contains a node of depth {}",
                self.depth(),
                child.depth()
            );
        }
    }

    /// Rebalances the first child of this internal node with its second child.
    ///
    /// Returns whether the node has now less than the minimum number of
    /// children:
    ///
    /// - `true`: a child was removed and this internal node needs to be
    /// rebalanced with another internal node of the same depth to become valid
    /// again;
    ///
    /// - `false`: we're good.
    ///
    /// Note: the second child is assumed to:
    ///
    /// a) exist (so the minimum number of children has to be >= 2, which means
    /// the fanout has to be >= 4);
    ///
    /// b) be valid, i.e. calling [`Node::is_valid()`] on the second child is
    /// assumed to return `true`.
    ///
    /// Note: when the first and second children are leaves the leaf count may
    /// decrease by 1.
    #[inline]
    pub(super) fn balance_first_child_with_second(&mut self) -> bool {
        debug_assert!(self.children().len() >= 2);

        let (first, second) = self.two_mut(0, 1);

        debug_assert!(second.is_valid());

        // TODO: explain why we call `make_mut` on the first child but not the
        // second.
        match (Arc::make_mut(first), &**second) {
            (Node::Internal(first), Node::Internal(second)) => {
                // Do nothing.
                if first.has_enough_children() {
                    false
                }
                // Move all the second child's children over to the first
                // child, then remove the second child.
                else if first.children().len() + second.children().len()
                    <= Self::max_children()
                {
                    first
                        .children
                        .extend(second.children.iter().map(Arc::clone));

                    first.num_leaves += second.num_leaves;

                    first.summary += second.summary();

                    self.children.remove(1);

                    self.children.len() < Self::min_children()
                }
                // Move the minimum number of children from the second child
                // over to the first child, keeping both.
                else {
                    let to_first =
                        Self::min_children() - first.children().len();

                    let (to_first, keep_second) =
                        second.children().split_at(to_first);

                    for child in to_first {
                        first.push(Arc::clone(child));
                    }

                    let second =
                        Arc::new(Node::Internal(Self::from_children(
                            keep_second.iter().map(Arc::clone),
                        )));

                    self.children[1] = second;

                    debug_assert!(self.children[0].is_valid());
                    debug_assert!(self.children[1].is_valid());

                    false
                }
            },

            (Node::Leaf(first), Node::Leaf(second)) => {
                if first.is_big_enough() {
                    false
                } else {
                    let (left, right) = L::balance_slices(
                        (first.as_slice(), first.summary()),
                        (second.as_slice(), second.summary()),
                    );

                    *first = Lnode::from(left);

                    if let Some(second) = right {
                        let second = Arc::new(Node::Leaf(Lnode::from(second)));
                        self.children[1] = second;
                        false
                    } else {
                        self.num_leaves -= 1;
                        self.children.remove(1);
                        self.children.len() < Self::min_children()
                    }
                }
            },

            _ => {
                // Safety: the first and second children are siblings so they
                // must be of the same kind.
                unsafe { std::hint::unreachable_unchecked() }
            },
        }
    }

    /// Rebalances the last child of this internal node with its penultimate
    /// (i.e. second to last) child.
    ///
    /// Returns whether the node has now less than the minimum number of
    /// children:
    ///
    /// - `true`: a child was removed and this internal node needs to be
    /// rebalanced with another internal node of the same depth to become valid
    /// again;
    ///
    /// - `false`: we're good.
    ///
    /// Note: the penultimate child is assumed to:
    ///
    /// a) exist (so the minimum number of children has to be >= 2, which means
    /// the fanout has to be >= 4);
    ///
    /// b) be valid, i.e. calling [`Node::is_valid()`] on the penultimate child
    /// is assumed to return `true`.
    ///
    /// Note: when the last and penultimate children are leaves the leaf count
    /// may decrease by 1.
    #[inline]
    pub(super) fn balance_last_child_with_penultimate(&mut self) -> bool {
        debug_assert!(self.children().len() >= 2);

        let last_idx = self.children.len() - 1;

        let (penultimate, last) = self.two_mut(last_idx - 1, last_idx);

        debug_assert!(penultimate.is_valid());

        // TODO: explain why we call `make_mut` on the last child but not the
        // penulimate.
        match (&**penultimate, Arc::make_mut(last)) {
            (Node::Internal(penultimate), Node::Internal(last)) => {
                // Do nothing.
                if last.has_enough_children() {
                    false
                }
                // TODO: try to do the opposite, move last to penultimate.
                //
                // Move all the penultimate child's children over to the last
                // child, then remove the penultimate child.
                else if penultimate.children().len() + last.children().len()
                    <= Self::max_children()
                {
                    for (idx, child) in penultimate.children.iter().enumerate()
                    {
                        last.children.insert(idx, Arc::clone(child));
                    }

                    last.num_leaves += penultimate.num_leaves;

                    last.summary += penultimate.summary();

                    self.children.remove(last_idx - 1);

                    self.children.len() < Self::min_children()
                }
                // Move the minimum number of children from the second child
                // over to the first child, keeping both.
                else {
                    let to_last = Self::min_children() - last.children().len();

                    let (keep_penultimate, to_last) = penultimate
                        .children()
                        .split_at(penultimate.children.len() - to_last);

                    for (idx, child) in to_last.iter().enumerate() {
                        last.insert(idx, Arc::clone(child));
                    }

                    let penultimate =
                        Arc::new(Node::Internal(Self::from_children(
                            keep_penultimate.iter().map(Arc::clone),
                        )));

                    self.children[last_idx - 1] = penultimate;

                    debug_assert!(self.children[last_idx - 1].is_valid());
                    debug_assert!(self.children[last_idx].is_valid());

                    false
                }
            },

            (Node::Leaf(penultimate), Node::Leaf(last)) => {
                if last.is_big_enough() {
                    false
                } else {
                    let (left, right) = L::balance_slices(
                        (penultimate.as_slice(), penultimate.summary()),
                        (last.as_slice(), last.summary()),
                    );

                    if let Some(right) = right {
                        *last = Lnode::from(right);

                        let penultimate =
                            Arc::new(Node::Leaf(Lnode::from(left)));

                        self.children[last_idx - 1] = penultimate;

                        false
                    } else {
                        *last = Lnode::from(left);
                        self.num_leaves -= 1;
                        self.children.remove(last_idx - 1);
                        self.children.len() < Self::min_children()
                    }
                }
            },

            _ => {
                // Safety: the penultimate and last children are siblings so
                // they must be of the same kind.
                unsafe { std::hint::unreachable_unchecked() }
            },
        }
    }

    #[inline]
    pub(super) fn children(&self) -> &[Arc<Node<N, L>>] {
        &self.children
    }

    #[inline]
    pub(super) fn has_enough_children(&self) -> bool {
        self.children().len() >= Self::min_children()
    }

    #[inline]
    pub(super) fn two_mut(
        &mut self,
        first_idx: usize,
        second_idx: usize,
    ) -> (&mut Arc<Node<N, L>>, &mut Arc<Node<N, L>>) {
        debug_assert!(first_idx < second_idx);
        debug_assert!(second_idx < self.children.len());

        let split_at = first_idx + 1;
        let (first, second) = self.children.split_at_mut(split_at);
        (&mut first[first_idx], &mut second[second_idx - split_at])
    }

    #[inline]
    pub(super) fn insert(&mut self, idx: usize, child: Arc<Node<N, L>>) {
        debug_assert!(!self.is_full());
        debug_assert_eq!(child.depth() + 1, self.depth());

        self.num_leaves += child.num_leaves();
        self.summary += child.summary();
        self.children.insert(idx, child);
    }

    #[inline]
    pub(super) fn depth(&self) -> usize {
        self.depth
    }

    #[inline]
    pub(super) fn empty() -> Self {
        Self::default()
    }

    /// Returns a reference to the first child of this internal node.
    #[inline]
    pub(super) fn first(&self) -> &Arc<Node<N, L>> {
        &self.children[0]
    }

    /// Returns a mutable reference to the first child of this internal node.
    #[inline]
    pub(super) fn first_mut(&mut self) -> &mut Arc<Node<N, L>> {
        &mut self.children[0]
    }

    /// Returns a reference to the last child of this internal node.
    #[allow(dead_code)]
    #[inline]
    pub(super) fn last(&self) -> &Arc<Node<N, L>> {
        let last_idx = self.children.len() - 1;
        &self.children[last_idx]
    }

    /// Returns a mutable reference to the last child of this internal node.
    #[inline]
    pub(super) fn last_mut(&mut self) -> &mut Arc<Node<N, L>> {
        let last_idx = self.children.len() - 1;
        &mut self.children[last_idx]
    }

    #[allow(dead_code)]
    #[inline]
    pub fn base_measure(&self) -> L::BaseMetric {
        self.measure::<L::BaseMetric>()
    }

    #[inline]
    pub fn measure<M: Metric<L>>(&self) -> M {
        M::measure(self.summary())
    }

    #[inline]
    pub(super) const fn max_children() -> usize {
        N
    }

    #[inline]
    pub(super) const fn min_children() -> usize {
        N / 2
    }

    #[inline]
    pub(super) fn num_leaves(&self) -> usize {
        self.num_leaves
    }

    #[inline]
    fn is_empty(&self) -> bool {
        self.children.len() == 0
    }

    #[inline]
    fn is_full(&self) -> bool {
        self.children.len() == N
    }

    /// Adds a node to the children, updating self's summary with the summary
    /// coming from the new node.
    #[inline]
    pub(super) fn push(&mut self, child: Arc<Node<N, L>>) {
        if self.is_empty() {
            self.depth = child.depth() + 1;
        }

        debug_assert!(!self.is_full());
        debug_assert_eq!(child.depth() + 1, self.depth());

        self.num_leaves += child.num_leaves();
        self.summary += child.summary();
        self.children.push(child);
    }

    /// # Panics
    ///
    /// This function will panic if the iterator yields more than `N` items.
    #[inline]
    pub(super) fn from_children<I>(children: I) -> Self
    where
        I: IntoIterator<Item = Arc<Node<N, L>>>,
    {
        let children = children.into_iter().collect::<Vec<Arc<Node<N, L>>>>();

        debug_assert!(!children.is_empty());
        debug_assert!(children.len() <= N);

        let depth = children[0].depth() + 1;

        let mut num_leaves = children[0].num_leaves();
        let mut summary = children[0].summary().clone();

        for child in &children[1..] {
            num_leaves += child.num_leaves();
            summary += child.summary();
        }

        Self { children, depth, num_leaves, summary }
    }

    #[inline]
    pub(super) fn from_leaves<I>(leaves: I) -> Self
    where
        I: IntoIterator<Item = Lnode<L>>,
    {
        let mut nodes = leaves
            .into_iter()
            .map(Node::Leaf)
            .map(Arc::new)
            .collect::<Vec<_>>();

        while nodes.len() > N {
            let capacity = nodes.len() / N + ((nodes.len() % N != 0) as usize);
            let mut new_nodes = Vec::with_capacity(capacity);

            let mut iter = nodes.into_iter();
            loop {
                match iter.next_chunk::<N>() {
                    Ok(chunk) => {
                        let inode = Self::from_children(chunk);
                        new_nodes.push(Arc::new(Node::Internal(inode)));
                    },

                    Err(last_chunk) => {
                        if last_chunk.len() > 0 {
                            let inode = Self::from_children(last_chunk);
                            new_nodes.push(Arc::new(Node::Internal(inode)));
                        }
                        break;
                    },
                }
            }

            nodes = new_nodes;
        }

        Self::from_children(nodes)
    }

    #[inline]
    pub(super) fn summary(&self) -> &L::Summary {
        &self.summary
    }
}

/// Recursively prints a tree-like representation of this node.
///
/// Called by the `Debug` impl of [`Inode`] when using the pretty-print
/// modifier (i.e. `{:#?}`).
#[inline]
fn pretty_print_inode<const N: usize, L: Leaf>(
    inode: &Inode<N, L>,
    shifts: &mut String,
    ident: &str,
    last_shift_byte_len: usize,
    f: &mut std::fmt::Formatter,
) -> std::fmt::Result {
    writeln!(
        f,
        "{}{}{:?}",
        &shifts[..shifts.len() - last_shift_byte_len],
        ident,
        inode.summary()
    )?;

    for (i, child) in inode.children().iter().enumerate() {
        let is_last = i + 1 == inode.children.len();
        let ident = if is_last { "└── " } else { "├── " };
        match &**child {
            Node::Internal(inode) => {
                let shift = if is_last { "    " } else { "│   " };
                shifts.push_str(shift);
                pretty_print_inode(inode, shifts, ident, shift.len(), f)?;
                shifts.truncate(shifts.len() - shift.len());
            },
            Node::Leaf(leaf) => {
                writeln!(f, "{}{}{:#?}", &shifts, ident, &leaf)?;
            },
        }
    }

    Ok(())
}
