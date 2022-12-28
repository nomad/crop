use std::ops::Range;
use std::sync::Arc;

use super::{Leaf, Lnode, Metric, Node, Tree};

/// Invariants: guaranteed to contain at least one child node.
#[derive(Clone)]
pub(super) struct Inode<const N: usize, L: Leaf> {
    children: Vec<Arc<Node<N, L>>>,
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
        Self::default()
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
    fn is_full(&self) -> bool {
        self.children.len() == N
    }

    #[inline]
    pub(super) fn push(&mut self, child: Arc<Node<N, L>>) {
        // TODO: uncomment this.
        // debug_assert!(!self.is_full());
        // debug_assert_eq!(child.depth() + 1, self.depth());

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

    //fn is_full(&self) -> bool {
    //    self.children.len() == N
    //}

    ///// Adds a node to the children, updating self's summary with the summary
    ///// coming from the new node.
    /////
    ///// # Panics
    /////
    ///// This function will panic if the node is already full.
    //fn push_node(&mut self, node: Node<N, Leaf>) {
    //    assert!(!self.is_full());
    //    self.summary += node.summary();
    //    self.children.push(Arc::new(node));
    //}

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
