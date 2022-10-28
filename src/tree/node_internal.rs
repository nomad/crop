use std::fmt::{self, Debug};
use std::sync::Arc;

use super::{Node, Summarize};

/// Invariants: guaranteed to contain at least one child node.
pub(super) struct Inode<const N: usize, Leaf: Summarize> {
    children: Vec<Arc<Node<N, Leaf>>>,
    summary: Leaf::Summary,
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
        Self { children: Vec::with_capacity(N), summary: Default::default() }
    }
}

impl<const N: usize, Leaf: Summarize> Inode<N, Leaf> {
    fn children(&self) -> &[Arc<Node<N, Leaf>>] {
        &self.children
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

        inode
    }

    pub(super) fn from_leaves<I>(leaves: I) -> Self
    where
        I: IntoIterator<Item = Leaf>,
    {
        let mut iter = leaves
            .into_iter()
            .map(super::Leaf::from_value)
            .map(Node::<N, Leaf>::Leaf)
            .map(Arc::new);

        let mut root = Self::default();

        let mut subtrees = vec![&mut root];

        loop {
            match iter.next_chunk::<N>() {
                Ok(nodes) => {
                    let inode = Self::from_children(nodes);
                    sumthin(&mut subtrees, Node::Internal(inode));
                },

                Err(last_chunk) => {
                    if last_chunk.len() > 0 {
                        let inode = Self::from_children(last_chunk);
                        sumthin(&mut subtrees, Node::Internal(inode));
                    }
                    break;
                },
            }
        }

        // TODO: pull up singular nodes

        root
    }

    fn is_full(&self) -> bool {
        self.children.len() == N
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

/// TODO: docs
fn sumthin<const N: usize, Leaf: Summarize>(
    subtrees: &mut Vec<&mut Inode<N, Leaf>>,
    node: Node<N, Leaf>,
) {
    let root = subtrees.last_mut().unwrap();

    if !root.is_full() {
        root.push_node(node);
    } else {
        todo!()
    }
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

// Failed APIs
impl<const N: usize, Leaf: Summarize> Inode<N, Leaf> {
    /// TODO: docs
    ///
    /// Note: All the nodes are expected to have the same height.
    pub(super) fn from_nodes<I>(nodes: I) -> Self
    where
        I: IntoIterator<Item = Node<N, Leaf>>,
        I::IntoIter: ExactSizeIterator,
    {
        use std::mem::MaybeUninit;

        let nodes = nodes.into_iter();

        // Use a vec of nodes. Pop nodes off FANOUT at a time.

        let mut nodes = nodes
            .into_iter()
            .map(Arc::new)
            .map(MaybeUninit::new)
            .collect::<Vec<_>>();

        //let mut iter = nodes.into_iter().array_chunks::<N>();

        //while let Some(children) = iter.next() {
        //    //
        //}

        // while nodes.len() > N {
        //     // TODO: this allocates a `new_nodes` at every iteration. Can
        //     // we reuse `nodes`?

        //     let mut new_nodes =
        //         Vec::with_capacity(usize::div_ceil(nodes.len(), N));

        //     let mut iter = nodes.into_iter().array_chunks::<N>();

        //     while let Some(children) = iter.next() {
        //         let summary = children
        //             .iter()
        //             .map(|node| unsafe { node.assume_init_ref().summary() })
        //             .sum::<Leaf::Summary>();

        //         new_nodes.push(MaybeUninit::new(Arc::new(Node::Internal(
        //             Inode { summary, children, initialized: N },
        //         ))));
        //     }

        //     if let Some(last) = iter.into_remainder() {
        //         if last.len() > 0 {
        //             let last = last.into_iter().collect();

        //             // Safety: all the nodes in this last chunk are initialized
        //             // and `last` contains at most `FANOUT - 1` elements.
        //             let inode =
        //                 unsafe { Self::from_children_incomplete(last) };

        //             new_nodes.push(MaybeUninit::new(Arc::new(
        //                 Node::Internal(inode),
        //             )));
        //         }
        //     }

        //     nodes = new_nodes;
        // }

        // Safety: all the nodes are initialized and nodes.len() <= FANOUT.
        // unsafe { Self::from_children_incomplete(nodes) }
        Self::default()
    }

    // /// TODO: docs
    // pub(super) fn from_equally_deep_nodes<I>(nodes: I) -> Self
    // where
    //     I: IntoIterator<Item = Node<N, Leaf>>,
    // {
    //     let mut children: Vec<MaybeUninit<Arc<Node<N, Leaf>>>> =
    //         Vec::with_capacity(N);

    //     let mut rightmost_level_n_children = 0;

    //     let mut ciao = 0;
    //     let mut iter = nodes.into_iter().map(Arc::new).map(MaybeUninit::new);

    //     while let Ok(nodes) = iter.next_chunk::<N>() {
    //         if children.len() > N {
    //             panic!(
    //                 "panicked w/ {} at iteration {ciao}",
    //                 rightmost_level_n_children
    //             );
    //         }

    //         if rightmost_level_n_children == N {
    //             let nodes =
    //                 children.drain(children.len() - N..).collect::<Vec<_>>();

    //             let summary = nodes
    //                 .iter()
    //                 .map(|node| unsafe { node.assume_init_ref().summary() })
    //                 .sum::<Leaf::Summary>();

    //             let nodes = nodes.try_into().unwrap();

    //             let node = MaybeUninit::new(Arc::new(Node::Internal(Inode {
    //                 summary,
    //                 children: nodes,
    //                 initialized: N,
    //             })));

    //             children.push(node);

    //             rightmost_level_n_children = 0;
    //         }

    //         let summary = children
    //             .iter()
    //             .map(|node| unsafe { node.assume_init_ref().summary() })
    //             .sum::<Leaf::Summary>();

    //         let node = MaybeUninit::new(Arc::new(Node::Internal(Inode {
    //             summary,
    //             children: nodes,
    //             initialized: N,
    //         })));

    //         children.push(node);

    //         rightmost_level_n_children += 1;
    //         ciao += 1;
    //     }

    //     panic!("{:#?}", unsafe {
    //         Self::from_m_less_than_n_children(children)
    //     });

    //     let last_chunk =
    //         unsafe { iter.next_chunk::<N>().unwrap_err_unchecked() }
    //             .into_iter()
    //             .collect::<Vec<_>>();

    //     if !last_chunk.is_empty() {
    //         // Safety: TODO
    //         let inode =
    //             unsafe { Self::from_m_less_than_n_children(last_chunk) };

    //         if children.is_empty() {
    //             return inode;
    //         } else {
    //             let node = MaybeUninit::new(Arc::new(Node::Internal(inode)));

    //             // TODO: push node to children.
    //         }
    //     }

    //     assert!(!children.is_empty());

    //     // TODO: make all nodes in children the same height

    //     // Safety: TODO
    //     unsafe { Self::from_m_less_than_n_children(children) }
    // }
}
