use std::sync::Arc;

use super::{Leaf, Lnode, Node};

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

    #[inline]
    pub(super) fn children(&self) -> &[Arc<Node<N, L>>] {
        &self.children
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
    pub(super) fn drain(
        &mut self,
        index_range: std::ops::Range<usize>,
    ) -> std::vec::Drain<'_, Arc<Node<N, L>>> {
        for index in index_range.clone() {
            let node = &*self.children[index];
            self.num_leaves -= node.num_leaves();
            self.summary -= node.summary();
        }

        self.children.drain(index_range)
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
    pub(super) fn prepend<I>(&mut self, nodes: I)
    where
        I: IntoIterator<Item = Arc<Node<N, L>>>,
    {
        for (idx, node) in nodes.into_iter().enumerate() {
            self.insert(idx, node);
        }
    }

    #[inline]
    pub(super) fn extend<I>(&mut self, nodes: I)
    where
        I: IntoIterator<Item = Arc<Node<N, L>>>,
    {
        for node in nodes.into_iter() {
            self.push(node);
        }
    }

    #[inline]
    pub(super) fn depth(&self) -> usize {
        self.depth
    }

    #[inline]
    pub(super) fn empty() -> Self {
        Self::default()
    }

    #[inline]
    pub(super) fn extend_from_other(&mut self, other: &Self) {
        debug_assert_eq!(self.depth(), other.depth());
        self.num_leaves += other.num_leaves;
        self.summary += other.summary();
        self.children.extend(other.children().iter().map(Arc::clone));
    }

    #[inline]
    pub(super) fn prepend_from_other(&mut self, other: &Self) {
        debug_assert_eq!(self.depth(), other.depth());
        self.num_leaves += other.num_leaves();
        self.summary += other.summary();

        for (idx, child) in other.children().iter().map(Arc::clone).enumerate()
        {
            self.children.insert(idx, child);
        }
    }

    #[inline]
    pub(super) fn pop(&mut self, index: usize) -> Arc<Node<N, L>> {
        let node = &*self.children[index];
        self.num_leaves -= node.num_leaves();
        self.summary -= node.summary();
        self.children.remove(index)
    }

    /// Returns a mutable reference to the first child of this internal node.
    #[inline]
    pub(super) fn first_mut(&mut self) -> &mut Arc<Node<N, L>> {
        &mut self.children[0]
    }

    /// Returns a mutable reference to the last child of this internal node.
    #[inline]
    pub(super) fn last_mut(&mut self) -> &mut Arc<Node<N, L>> {
        let last_idx = self.children.len() - 1;
        &mut self.children[last_idx]
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
    pub(super) fn swap(
        &mut self,
        index: usize,
        child: Arc<Node<N, L>>,
    ) -> Arc<Node<N, L>> {
        debug_assert!(index < self.children.len());
        debug_assert_eq!(self.depth(), child.depth() + 1);

        self.num_leaves += child.num_leaves();
        self.summary += child.summary();

        let old = std::mem::replace(&mut self.children[index], child);

        self.num_leaves -= old.num_leaves();
        self.summary -= old.summary();

        old
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
