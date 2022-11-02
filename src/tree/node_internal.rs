use std::fmt::{self, Debug};
use std::sync::Arc;

use super::{Node, Summarize};

/// Invariants: guaranteed to contain at least one child node.
pub(super) struct Inode<const N: usize, Leaf: Summarize> {
    children: Vec<Arc<Node<N, Leaf>>>,
    summary: Leaf::Summary,
    depth: usize,
}

impl<const N: usize, Leaf: Summarize> Debug for Inode<N, Leaf> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if !f.alternate() {
            f.debug_struct("Inode")
                .field("children", &self.children)
                .field("summary", &self.summary)
                .finish()
        } else {
            pretty_print_inode(self, &mut String::new(), "", 0, f)
        }
    }
}

impl<const N: usize, Leaf: Summarize> Default for Inode<N, Leaf> {
    fn default() -> Self {
        Self {
            children: Vec::with_capacity(N),
            summary: Default::default(),
            depth: 1,
        }
    }
}

impl<const N: usize, Leaf: Summarize> Inode<N, Leaf> {
    pub(super) fn children(&self) -> &[Arc<Node<N, Leaf>>] {
        &self.children
    }

    pub(super) fn depth(&self) -> usize {
        self.depth
    }

    /// # Panics
    ///
    /// This function will panic if the iterator yields more than `N` items.
    fn from_children<I>(children: I) -> Self
    where
        I: IntoIterator<Item = Arc<Node<N, Leaf>>>,
        I::IntoIter: ExactSizeIterator,
    {
        let children = children.into_iter();

        let len = children.len();

        assert!(len <= N);

        let mut inode = Self::default();

        for child in children {
            inode.summary += child.summary();
            inode.children.push(child);
        }

        inode.depth = inode.children[0].depth() + 1;

        inode
    }

    pub(super) fn from_leaves<I>(leaves: I) -> Self
    where
        I: IntoIterator<Item = Leaf>,
    {
        let mut nodes = leaves
            .into_iter()
            .map(super::Leaf::from_value)
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

    fn is_full(&self) -> bool {
        self.children.len() == N
    }

    /// # Panics
    ///
    /// This function will panic if the coordinate are not valid.
    pub(super) fn leaf_at_coordinate(
        &self,
        coordinates: &LeafCoordinates<N>,
    ) -> &'_ Leaf {
        let mut node = &*self.children()[coordinates.vec[0]];

        for &idx in &coordinates.vec[1..] {
            node = &*node.as_inode().unwrap().children()[idx];
        }

        node.as_leaf().unwrap().value()
    }

    /// Adds a node to the children, updating self's summary with the summary
    /// coming from the new node.
    ///
    /// # Panics
    ///
    /// This function will panic if the node is already full.
    fn push_node(&mut self, node: Node<N, Leaf>) {
        assert!(!self.is_full());
        self.summary += node.summary();
        self.children.push(Arc::new(node));
    }

    pub(super) fn summary(&self) -> &Leaf::Summary {
        &self.summary
    }
}

/// Path to follow to go from an internal node down to one of the leaves in its
/// subtree.
#[derive(Clone)]
pub(super) struct LeafCoordinates<const N: usize> {
    /// # Invariants
    ///
    /// - `vec` always contains at least one item.
    /// - all the items in the vector are < `N`.
    vec: Vec<usize>,
}

/// Recursively prints a tree-like representation of this node. Called by the
/// `Debug` impl of [`Inode`] when using the pretty-print modifier (i.e.
/// `{:#?}`).
fn pretty_print_inode<const N: usize, Leaf: Summarize>(
    inode: &Inode<N, Leaf>,
    shifts: &mut String,
    ident: &str,
    last_shift_byte_len: usize,
    f: &mut fmt::Formatter,
) -> fmt::Result {
    writeln!(
        f,
        "{}{}{:?}",
        &shifts[..shifts.len() - last_shift_byte_len],
        ident,
        &inode.summary
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
