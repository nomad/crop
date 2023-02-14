use std::sync::Arc;

use super::{Leaf, Lnode, Metric, Node};

#[derive(Clone)]
pub(super) struct Inode<const N: usize, L: Leaf> {
    pub(super) children: Vec<Arc<Node<N, L>>>,
    summary: L::Summary,
    depth: usize,
    leaf_count: usize,
}

impl<const N: usize, L: Leaf> std::fmt::Debug for Inode<N, L> {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        if !f.alternate() {
            f.debug_struct("Inode")
                .field("children", &self.children)
                .field("summary", &self.summary)
                .field("depth", &self.depth)
                .field("leaf_count", &self.leaf_count)
                .finish()
        } else {
            pretty_print_inode(self, &mut String::new(), "", 0, f)
        }
    }
}

impl<const N: usize, L: Leaf> Inode<N, L> {
    /// TODO: docs
    #[inline]
    pub(super) fn append_at_depth(
        &mut self,
        mut node: Arc<Node<N, L>>,
    ) -> Option<Self>
    where
        L: Clone,
    {
        debug_assert!(node.depth() < self.depth());

        if self.depth() > node.depth() + 1 {
            let extra = self.with_child_mut(self.len() - 1, |last| {
                let last = Arc::make_mut(last);
                // SAFETY: TODO
                let last = unsafe { last.as_mut_internal_unchecked() };
                last.append_at_depth(node)
            })?;

            node = Arc::new(Node::Internal(extra));
        }

        debug_assert_eq!(self.depth(), node.depth() + 1);

        if !self.is_full() {
            self.push(node);
            None
        } else {
            let mut other =
                Self::from_children(self.split_off(Self::min_children() + 1));
            other.push(node);
            debug_assert_eq!(Self::min_children(), other.len());
            Some(other)
        }
    }

    pub(super) fn assert_invariants(&self) {
        assert!(
            self.len() >= Self::min_children(),
            "An internal node of depth {} was supposed to contain at least \
             {} children but actually contains {}",
            self.depth(),
            Self::min_children(),
            self.len()
        );

        assert!(
            self.len() <= Self::max_children(),
            "An internal node of depth {} was supposed to contain at most {} \
             children but actually contains {}",
            self.depth(),
            Self::max_children(),
            self.len()
        );

        let actual_leaves =
            self.children().iter().map(|c| c.leaf_count()).sum::<usize>();

        assert_eq!(
            self.leaf_count,
            actual_leaves,
            "An internal node of depth {} thought it contained {} leaves in \
             its subtree, but actually contains {}",
            self.depth(),
            self.leaf_count,
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

    /// Balances the first child using the contents of the second child,
    /// possibly merging them together if necessary.
    ///
    /// NOTE: when the first and second children are leaves this inode's
    /// [`leaf_count()`] may decrease by 1.
    ///
    /// # Panics
    ///
    /// Panics if:
    ///
    /// - this inode has only one child (the second child is assumed to exist);
    ///
    /// - the `Arc` enclosing the first child has a strong counter > 1. This
    /// function assumes that there are zero `Arc::clone`s of the first child.
    #[inline]
    pub(super) fn balance_first_child_with_second(&mut self) {
        debug_assert!(self.len() >= 2);

        // Check for early returns.
        if !self.first().is_underfilled() {
            return;
        }

        let (first, second) = self.two_mut(0, 1);

        match (Arc::get_mut(first).unwrap(), &**second) {
            (Node::Internal(first), Node::Internal(second)) => {
                // Move all the second child's children over to the first
                // child, then remove the second child.
                if first.len() + second.len() <= Self::max_children() {
                    first
                        .children
                        .extend(second.children.iter().map(Arc::clone));

                    first.leaf_count += second.leaf_count;

                    first.summary += second.summary();

                    self.children.remove(1);
                }
                // Move the minimum number of children from the second child
                // over to the first child, keeping both.
                else {
                    let to_first = Self::min_children() - first.len();

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

                    debug_assert!(!self.children[0].is_underfilled());
                    debug_assert!(!self.children[1].is_underfilled());
                }
            },

            (Node::Leaf(first), Node::Leaf(second)) => {
                let (left, right) = L::balance_slices(
                    (first.as_slice(), first.summary()),
                    (second.as_slice(), second.summary()),
                );

                *first = Lnode::from(left);

                if let Some(second) = right {
                    let second = Arc::new(Node::Leaf(Lnode::from(second)));
                    self.children[1] = second;
                } else {
                    self.leaf_count -= 1;
                    self.children.remove(1);
                }
            },

            _ => {
                // SAFETY: the first and second children are siblings so they
                // must be of the same kind.
                unsafe { std::hint::unreachable_unchecked() }
            },
        }
    }

    /// Balances the last child using the contents of the penultimate (i.e.
    /// second to last) child, possibly merging them together if necessary.
    ///
    /// NOTE: when the penultimate and last children are leaves this inode's
    /// [`leaf_count()`] may decrease by 1.
    ///
    /// # Panics
    ///
    /// Panics if:
    ///
    /// - this inode has only one child (the penultimate child is assumed to
    /// exist);
    ///
    /// - the `Arc` enclosing the last child has a strong counter > 1. This
    /// function assumes that there are zero `Arc::clone`s of the last child.
    #[inline]
    pub(super) fn balance_last_child_with_penultimate(&mut self) {
        debug_assert!(self.len() >= 2);

        // Check for early returns.
        if !self.last().is_underfilled() {
            return;
        }

        let last_idx = self.len() - 1;

        let (penultimate, last) = self.two_mut(last_idx - 1, last_idx);

        match (&**penultimate, Arc::get_mut(last).unwrap()) {
            (Node::Internal(penultimate), Node::Internal(last)) => {
                // Move all the penultimate child's children over to the last
                // child, then remove the penultimate child.
                if penultimate.len() + last.len() <= Self::max_children() {
                    for (idx, child) in penultimate.children.iter().enumerate()
                    {
                        last.children.insert(idx, Arc::clone(child));
                    }

                    last.leaf_count += penultimate.leaf_count;

                    last.summary += penultimate.summary();

                    self.children.remove(last_idx - 1);
                }
                // Move the minimum number of children from the second child
                // over to the first child, keeping both.
                else {
                    let to_last = Self::min_children() - last.len();

                    let (keep_penultimate, to_last) = penultimate
                        .children()
                        .split_at(penultimate.len() - to_last);

                    for (idx, child) in to_last.iter().enumerate() {
                        last.insert(idx, Arc::clone(child));
                    }

                    let penultimate =
                        Arc::new(Node::Internal(Self::from_children(
                            keep_penultimate.iter().map(Arc::clone),
                        )));

                    self.children[last_idx - 1] = penultimate;

                    debug_assert!(
                        !self.children[last_idx - 1].is_underfilled()
                    );
                    debug_assert!(!self.children[last_idx].is_underfilled());
                }
            },

            (Node::Leaf(penultimate), Node::Leaf(last)) => {
                let (left, right) = L::balance_slices(
                    (penultimate.as_slice(), penultimate.summary()),
                    (last.as_slice(), last.summary()),
                );

                if let Some(right) = right {
                    *last = Lnode::from(right);

                    let penultimate = Arc::new(Node::Leaf(Lnode::from(left)));

                    self.children[last_idx - 1] = penultimate;
                } else {
                    *last = Lnode::from(left);
                    self.leaf_count -= 1;
                    self.children.remove(last_idx - 1);
                }
            },

            _ => {
                // SAFETY: the penultimate and last children are siblings so
                // they must be of the same kind.
                unsafe { std::hint::unreachable_unchecked() }
            },
        }
    }

    /// Recursively balances the first child all the way down to the deepest
    /// inode.
    ///
    /// # Panics
    ///
    /// Panics if the `Arc` enclosing the first child has a strong counter > 1.
    pub(super) fn balance_left_side(&mut self) {
        self.balance_first_child_with_second();

        if let Node::Internal(first) = Arc::get_mut(self.first_mut()).unwrap()
        {
            first.balance_left_side();

            if !first.is_underfilled() && self.len() > 1 {
                self.balance_first_child_with_second();
            }
        }
    }

    /// Recursively balances the last child all the way down to the deepest
    /// inode.
    ///
    /// # Panics
    ///
    /// Panics if the `Arc` enclosing the last child has a strong counter > 1.
    pub(super) fn balance_right_side(&mut self) {
        self.balance_last_child_with_penultimate();

        if let Node::Internal(last) = Arc::get_mut(self.last_mut()).unwrap() {
            last.balance_right_side();

            if !last.is_underfilled() && self.len() > 1 {
                self.balance_last_child_with_penultimate();
            }
        }
    }

    #[inline]
    pub fn base_measure(&self) -> L::BaseMetric {
        self.measure::<L::BaseMetric>()
    }

    #[inline]
    pub(super) fn children(&self) -> &[Arc<Node<N, L>>] {
        &self.children
    }

    #[inline]
    pub(super) fn depth(&self) -> usize {
        self.depth
    }

    #[inline]
    pub(super) fn empty() -> Self {
        Self {
            children: Vec::with_capacity(N),
            depth: 1,
            leaf_count: 0,
            summary: Default::default(),
        }
    }

    #[inline]
    pub(super) fn first(&self) -> &Arc<Node<N, L>> {
        &self.children[0]
    }

    #[inline]
    pub(super) fn first_mut(&mut self) -> &mut Arc<Node<N, L>> {
        &mut self.children[0]
    }

    /// Creates a new internal node from its children.
    ///
    /// NOTE: this function assumes that `children` yields less than
    /// `Self::max_children()` nodes and that all the nodes have the same
    /// depth.
    ///
    /// # Panics
    ///
    /// Will panic if `children` yields zero nodes.
    #[inline]
    pub(super) fn from_children<I>(children: I) -> Self
    where
        I: IntoIterator<Item = Arc<Node<N, L>>>,
    {
        let children = children.into_iter().collect::<Vec<Arc<Node<N, L>>>>();

        debug_assert!(!children.is_empty());
        debug_assert!(children.len() <= N);

        let depth = children[0].depth() + 1;

        let mut leaf_count = children[0].leaf_count();
        let mut summary = children[0].summary().clone();

        for child in &children[1..] {
            leaf_count += child.leaf_count();
            summary += child.summary();
        }

        Self { children, depth, leaf_count, summary }
    }

    /// TODO: docs
    #[inline]
    fn collapse_nodes<I>(nodes: I) -> Vec<Arc<Node<N, L>>>
    where
        I: ExactSizeIterator<Item = Arc<Node<N, L>>>,
    {
        // TODO: check if this performs in the same way
        // ChildSegmenter::new(nodes).map(Node::Internal).map(Arc::new).collect()

        let mut segmenter = ChildSegmenter::new(nodes);

        let mut new_nodes = Vec::with_capacity(segmenter.len());

        while let Some(inode) = segmenter.next() {
            new_nodes.push(Arc::new(Node::Internal(inode)));
        }

        new_nodes
    }

    /// TODO: docs
    #[inline]
    pub(super) fn from_equally_deep_nodes<I>(nodes: I) -> Self
    where
        I: IntoIterator<Item = Arc<Node<N, L>>>,
        I::IntoIter: ExactSizeIterator,
    {
        let nodes = nodes.into_iter();

        let mut nodes = if nodes.len() > Self::max_children() {
            Self::collapse_nodes(nodes)
        } else {
            return Self::from_children(nodes);
        };

        while nodes.len() > Self::max_children() {
            nodes = Self::collapse_nodes(nodes.into_iter());
        }

        Self::from_children(nodes)
    }

    #[inline]
    pub(super) fn is_underfilled(&self) -> bool {
        self.len() >= Self::min_children()
    }

    #[inline]
    pub(super) fn insert(
        &mut self,
        child_offset: usize,
        child: Arc<Node<N, L>>,
    ) {
        // debug_assert!(!self.is_full());
        debug_assert_eq!(child.depth() + 1, self.depth());

        self.leaf_count += child.leaf_count();
        self.summary += child.summary();
        self.children.insert(child_offset, child);
    }

    #[inline]
    pub(super) fn is_empty(&self) -> bool {
        self.len() == 0
    }

    #[inline]
    pub(super) fn is_full(&self) -> bool {
        self.len() == N
    }

    #[inline]
    pub(super) fn is_overfull(&self) -> bool {
        self.len() > N
    }

    /// Returns a reference to the last child of this internal node.
    #[allow(dead_code)]
    #[inline]
    pub(super) fn last(&self) -> &Arc<Node<N, L>> {
        let last_idx = self.len() - 1;
        &self.children[last_idx]
    }

    /// Returns a mutable reference to the last child of this internal node.
    #[inline]
    pub(super) fn last_mut(&mut self) -> &mut Arc<Node<N, L>> {
        let last_idx = self.len() - 1;
        &mut self.children[last_idx]
    }

    #[inline]
    pub(super) fn len(&self) -> usize {
        self.children.len()
    }

    #[inline]
    pub(super) fn leaf_count(&self) -> usize {
        self.leaf_count
    }

    #[inline]
    pub(super) const fn max_children() -> usize {
        N
    }

    #[inline]
    pub fn measure<M: Metric<L>>(&self) -> M {
        M::measure(self.summary())
    }

    #[inline]
    pub(super) const fn min_children() -> usize {
        N / 2
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

        self.leaf_count += child.leaf_count();
        self.summary += child.summary();
        self.children.push(child);
    }

    #[inline]
    pub(super) fn remove(&mut self, child_idx: usize) {
        let child = self.children.remove(child_idx);
        self.summary -= child.summary();
        self.leaf_count -= child.leaf_count();
    }

    /// TODO: docs
    #[inline]
    pub(super) fn split_off(
        &mut self,
        child_offset: usize,
    ) -> std::vec::Drain<'_, Arc<Node<N, L>>> {
        debug_assert!(child_offset <= self.len());

        for child in &self.children[child_offset..] {
            self.summary -= child.summary();
            self.leaf_count -= child.leaf_count();
        }

        self.children.drain(child_offset..)
    }

    #[inline]
    pub(super) fn summary(&self) -> &L::Summary {
        &self.summary
    }

    /// TODO: docs
    #[inline]
    pub(super) fn swap(
        &mut self,
        child_idx: usize,
        new_child: Arc<Node<N, L>>,
    ) -> Arc<Node<N, L>> {
        debug_assert!(child_idx < self.len());
        debug_assert_eq!(new_child.depth() + 1, self.depth());

        let to_swap = &self.children[child_idx];
        self.summary -= to_swap.summary();
        self.leaf_count -= to_swap.leaf_count();

        self.summary += new_child.summary();
        self.leaf_count += new_child.leaf_count();
        std::mem::replace(&mut self.children[child_idx], new_child)
    }

    /// Returns mutable references to the child nodes at `first_idx` and
    /// `second_idx`, respectively.
    ///
    /// # Panics
    ///
    /// Will panic if `first_idx >= second_idx`  and if
    /// `second_idx >= self.len()`.
    #[inline]
    fn two_mut(
        &mut self,
        first_idx: usize,
        second_idx: usize,
    ) -> (&mut Arc<Node<N, L>>, &mut Arc<Node<N, L>>) {
        debug_assert!(first_idx < second_idx);
        debug_assert!(second_idx < self.len());

        let split_at = first_idx + 1;
        let (first, second) = self.children.split_at_mut(split_at);
        (&mut first[first_idx], &mut second[second_idx - split_at])
    }

    /// TODO: docs
    #[inline]
    pub(super) fn with_child_mut<F, T>(
        &mut self,
        child_idx: usize,
        fun: F,
    ) -> T
    where
        F: FnOnce(&mut Arc<Node<N, L>>) -> T,
    {
        let child = &mut self.children[child_idx];
        self.summary -= child.summary();
        self.leaf_count -= child.leaf_count();

        let ret = fun(child);

        if child.base_measure() > L::BaseMetric::zero() {
            self.summary += child.summary();
            self.leaf_count += child.leaf_count();
        } else {
            self.children.remove(child_idx);
        }

        ret
    }
}

/// TODO: docs
pub(super) struct ChildSegmenter<const N: usize, L, Children>
where
    L: Leaf,
    Children: ExactSizeIterator<Item = Arc<Node<N, L>>>,
{
    children: Children,
}

impl<const N: usize, L, Children> ChildSegmenter<N, L, Children>
where
    L: Leaf,
    Children: ExactSizeIterator<Item = Arc<Node<N, L>>>,
{
    #[inline]
    pub(super) fn new(children: Children) -> Self {
        debug_assert!(children.len() >= Inode::<N, L>::min_children());
        Self { children }
    }
}

impl<const N: usize, L, Children> Iterator for ChildSegmenter<N, L, Children>
where
    L: Leaf,
    Children: ExactSizeIterator<Item = Arc<Node<N, L>>>,
{
    type Item = Inode<N, L>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let min_children = Inode::<N, L>::min_children();
        let max_children = Inode::<N, L>::max_children();
        let remaining = self.children.len();

        debug_assert!(remaining == 0 || remaining >= min_children);

        let take = if remaining == 0 {
            return None;
        } else if remaining > max_children {
            if remaining - max_children >= min_children {
                max_children
            } else {
                remaining - min_children
            }
        } else {
            remaining
        };

        debug_assert!(take >= min_children && take <= max_children);

        debug_assert!(remaining >= take);

        Some(Inode::from_children(self.children.by_ref().take(take)))
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let exact = self.len();
        (exact, Some(exact))
    }
}

impl<const N: usize, L, Children> ExactSizeIterator
    for ChildSegmenter<N, L, Children>
where
    L: Leaf,
    Children: ExactSizeIterator<Item = Arc<Node<N, L>>>,
{
    #[inline]
    fn len(&self) -> usize {
        let remaining = self.children.len();
        let max_children = Inode::<N, L>::max_children();
        remaining / max_children + ((remaining % max_children != 0) as usize)
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
        let is_last = i + 1 == inode.len();
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
