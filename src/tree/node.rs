use std::sync::Arc;

use super::{Inode, Leaf, Lnode, Metric, TreeSlice};

#[derive(Clone)]
pub(super) enum Node<const N: usize, L: Leaf> {
    Internal(Inode<N, L>),
    Leaf(Lnode<L>),
}

impl<const N: usize, L: Leaf + Default> Default for Node<N, L> {
    #[inline]
    fn default() -> Self {
        Node::Leaf(Lnode::default())
    }
}

impl<const N: usize, L: Leaf> std::fmt::Debug for Node<N, L> {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        if !f.alternate() {
            match self {
                Self::Internal(inode) => {
                    f.debug_tuple("Internal").field(&inode).finish()
                },
                Self::Leaf(leaf) => {
                    f.debug_tuple("Leaf").field(&leaf).finish()
                },
            }
        } else {
            match self {
                Self::Internal(inode) => write!(f, "{:#?}", inode),
                Self::Leaf(leaf) => write!(f, "{:#?}", leaf),
            }
        }
    }
}

impl<'a, const N: usize, L: Leaf> From<TreeSlice<'a, N, L>> for Node<N, L> {
    #[inline]
    fn from(tree_slice: TreeSlice<'a, N, L>) -> Node<N, L> {
        match tree_slice.num_leaves {
            1 => {
                debug_assert!(tree_slice.root.is_leaf());

                Self::Leaf(Lnode {
                    value: tree_slice.start_slice.to_owned(),
                    summary: tree_slice.summary,
                })
            },

            2 => {
                let (first, second) = balance_slices(
                    tree_slice.start_slice,
                    &tree_slice.start_summary,
                    tree_slice.end_slice,
                    &tree_slice.end_summary,
                );

                if let Some(second) = second {
                    let mut inode = Inode::empty();

                    inode.push(Arc::new(Node::Leaf(first)));
                    inode.push(Arc::new(Node::Leaf(second)));

                    Self::Internal(inode)
                } else {
                    Self::Leaf(first)
                }
            },

            _ => {
                let mut node = Node::Internal(Inode::empty());

                tree_slice_add_nodes_rec(
                    &mut node,
                    tree_slice.root,
                    &tree_slice,
                    L::BaseMetric::measure(&tree_slice.before),
                    &mut L::BaseMetric::zero(),
                    &mut 0,
                );

                node
            },
        }
    }
}

impl<const N: usize, L: Leaf> Node<N, L> {
    #[inline]
    pub(super) unsafe fn as_internal_unchecked(&self) -> &Inode<N, L> {
        debug_assert!(
            self.is_internal(),
            "A node was expected to be an internal node but it's a leaf. This \
            is a logic bug in crop. Please file an issue at \
            https://github.com/noib3/crop."
        );

        match self {
            Node::Leaf(_) => std::hint::unreachable_unchecked(),
            Node::Internal(inode) => inode,
        }
    }

    #[inline]
    pub(super) unsafe fn as_leaf_unchecked(&self) -> &Lnode<L> {
        debug_assert!(
            self.is_leaf(),
            "A node was expected to be a leaf but it's an internal node. This \
            is a logic bug in crop. Please file an issue at \
            https://github.com/noib3/crop."
        );

        match self {
            Node::Leaf(leaf) => leaf,
            Node::Internal(_) => std::hint::unreachable_unchecked(),
        }
    }

    #[inline]
    pub fn convert_measure<M1, M2>(&self, from: M1) -> M2
    where
        M1: Metric<L>,
        M2: Metric<L>,
    {
        debug_assert!(from < M1::measure(self.summary()));

        let mut m1 = M1::zero();
        let mut m2 = M2::zero();

        let mut node = self;

        'outer: loop {
            match node {
                Node::Internal(inode) => {
                    for child in inode.children() {
                        let this = M1::measure(child.summary());
                        if m1 + this > from {
                            node = &**child;
                            continue 'outer;
                        } else {
                            m1 += this;
                            m2 += M2::measure(child.summary());
                        }
                    }
                    unreachable!(
                        "Didn't I tell you to do bounds checks before \
                         callign this function?"
                    );
                },

                Node::Leaf(leaf) => {
                    let (_, left_summary, _, _) =
                        M1::split(leaf.as_slice(), from - m1, leaf.summary());

                    m2 += M2::measure(&left_summary);

                    return m2;
                },
            }
        }
    }

    #[inline]
    pub(super) fn depth(&self) -> usize {
        match self {
            Node::Internal(inode) => inode.depth(),
            Node::Leaf(_) => 0,
        }
    }

    #[inline]
    pub fn from_leaves<I>(leaves: I) -> Self
    where
        I: IntoIterator<Item = Lnode<L>>,
        I::IntoIter: ExactSizeIterator,
    {
        let mut leaves = leaves.into_iter();

        if leaves.len() == 0 {
            panic!(
                "Cannot construct a Node<{}, {}> from an empty iterator",
                N,
                std::any::type_name::<L>(),
            )
        }

        if leaves.len() == 1 {
            return Self::Leaf(leaves.next().unwrap());
        }

        Self::Internal(Inode::from_leaves(leaves))
    }

    /// Note: doesn't do bounds checks.
    #[inline]
    pub fn leaf_at_measure<M>(&self, measure: M) -> (&L::Slice, M)
    where
        M: Metric<L>,
    {
        debug_assert!(measure < M::measure(self.summary()));

        let mut measured = M::zero();

        let mut node = self;

        'outer: loop {
            match node {
                Node::Internal(inode) => {
                    for child in inode.children() {
                        let this = M::measure(child.summary());
                        if measure < measured + this {
                            node = &**child;
                            continue 'outer;
                        } else {
                            measured += this;
                        }
                    }
                    unreachable!(
                        "Didn't I tell you to do bounds checks before \
                         callign this function?"
                    );
                },

                Node::Leaf(leaf) => {
                    return (leaf.as_slice(), measured);
                },
            }
        }
    }

    #[inline]
    pub(super) fn num_leaves(&self) -> usize {
        match self {
            Node::Internal(inode) => inode.num_leaves(),
            Node::Leaf(_) => 1,
        }
    }

    #[inline]
    pub(super) fn is_internal(&self) -> bool {
        matches!(self, Node::Internal(_))
    }

    #[inline]
    pub(super) fn is_leaf(&self) -> bool {
        matches!(self, Node::Leaf(_))
    }

    #[inline]
    pub(super) fn summary(&self) -> &L::Summary {
        match self {
            Node::Internal(inode) => inode.summary(),
            Node::Leaf(leaf) => leaf.summary(),
        }
    }
}

/// Recursively traverses the nodes spanned by the TreeSlice adding them to
/// `out`, rebalancing the first/last leaf slice with the second/penultimate
/// leaf if necessary.
///
/// Does not handle the cases `tree_slice.num_leaves = 1 | 2`, those are
/// expected to be special cased and handled by the caller.
#[inline]
fn tree_slice_add_nodes_rec<'a, const N: usize, L: Leaf>(
    out: &mut Node<N, L>,
    node: &Arc<Node<N, L>>,
    tree_slice: &TreeSlice<'a, N, L>,
    before: L::BaseMetric,
    measured: &mut L::BaseMetric,
    leaves_visited: &mut usize,
) {
    match &**node {
        Node::Internal(inode) => {
            for child in inode.children() {
                match *leaves_visited {
                    n if n == tree_slice.num_leaves => return,

                    0 => {
                        let measure = L::BaseMetric::measure(child.summary());

                        if *measured + measure > before {
                            // This child contains the starting leaf, so
                            // recurse down.
                            tree_slice_add_nodes_rec(
                                out,
                                child,
                                tree_slice,
                                before,
                                measured,
                                leaves_visited,
                            );
                        } else {
                            // This child comes before the starting leaf.
                            *measured += measure;
                        }
                    },

                    n if n == 1
                        || n + child.num_leaves()
                            >= tree_slice.num_leaves - 1 =>
                    {
                        // This node contains either the second or penultimate
                        // leaf, so we recurse down to get to that leaf.
                        tree_slice_add_nodes_rec(
                            out,
                            child,
                            tree_slice,
                            before,
                            measured,
                            leaves_visited,
                        );
                    },

                    _ => {
                        // Finally, this node is fully contained in the
                        // TreeSlice.
                        add_to_node(out, Arc::clone(child));
                        *leaves_visited += child.num_leaves();
                    },
                }
            }
        },

        Node::Leaf(leaf) => {
            match *leaves_visited {
                n if n == tree_slice.num_leaves => return,

                0 => {
                    let measure = L::BaseMetric::measure(leaf.summary());

                    if *measured + measure > before {
                        // This is the leaf that the starting slice was sliced
                        // from. At this point we stop using `measured` to
                        // index and start using `leaves_visited` instead.
                        *leaves_visited = 1;
                    } else {
                        // This leaf comes before the starting slice.
                        *measured += measure;
                    }
                },

                1 => {
                    // This is the second leaf.

                    let (first, second) = balance_slices(
                        tree_slice.start_slice,
                        &tree_slice.start_summary,
                        leaf.as_slice(),
                        leaf.summary(),
                    );

                    if tree_slice.num_leaves == 3 {
                        // If the TreeSlice spans exactly 3 leaves this is also
                        // the penultimate leaf.

                        *leaves_visited = 3;

                        if let Some(second) = second {
                            add_to_node(out, Arc::new(Node::Leaf(first)));

                            let (second, third) = balance_slices(
                                second.as_slice(),
                                second.summary(),
                                tree_slice.end_slice,
                                &tree_slice.end_summary,
                            );

                            add_to_node(out, Arc::new(Node::Leaf(second)));

                            if let Some(third) = third {
                                add_to_node(out, Arc::new(Node::Leaf(third)));
                            }
                        } else {
                            let (first, second) = balance_slices(
                                first.as_slice(),
                                first.summary(),
                                tree_slice.end_slice,
                                &tree_slice.end_summary,
                            );

                            add_to_node(out, Arc::new(Node::Leaf(first)));

                            if let Some(second) = second {
                                add_to_node(out, Arc::new(Node::Leaf(second)));
                            }
                        }
                    } else {
                        debug_assert!(tree_slice.num_leaves > 3);

                        *leaves_visited = 2;

                        add_to_node(out, Arc::new(Node::Leaf(first)));

                        if let Some(second) = second {
                            add_to_node(out, Arc::new(Node::Leaf(second)));
                        }
                    }
                },

                n if n + 1 == tree_slice.num_leaves - 1 => {
                    // This is the penultimate leaf.

                    *leaves_visited = tree_slice.num_leaves;

                    let (penultimate, last) = balance_slices(
                        leaf.as_slice(),
                        leaf.summary(),
                        tree_slice.end_slice,
                        &tree_slice.end_summary,
                    );

                    add_to_node(out, Arc::new(Node::Leaf(penultimate)));

                    if let Some(last) = last {
                        add_to_node(out, Arc::new(Node::Leaf(last)));
                    }
                },

                _ => {
                    // Finally, this leaf is fully contained in the TreeSlice.
                    add_to_node(out, Arc::clone(node));
                    *leaves_visited += 1;
                },
            }
        },
    }
}

#[inline]
fn add_to_node<const N: usize, L: Leaf>(
    lhs: &mut Node<N, L>,
    rhs: Arc<Node<N, L>>,
) {
    match lhs {
        Node::Internal(inode) => inode.push(rhs),

        Node::Leaf(_) => {
            let mut inode = Inode::default();
            inode.push(Arc::new(lhs.clone()));
            inode.push(rhs);
            *lhs = Node::Internal(inode);
        },
    }
}

#[inline]
fn balance_slices<L: Leaf>(
    first_slice: &L::Slice,
    first_summary: &L::Summary,
    second_slice: &L::Slice,
    second_summary: &L::Summary,
) -> (Lnode<L>, Option<Lnode<L>>) {
    (
        Lnode {
            value: first_slice.to_owned(),
            summary: first_summary.to_owned(),
        },
        Some(Lnode {
            value: second_slice.to_owned(),
            summary: second_summary.to_owned(),
        }),
    )
    // let first_size = L::BaseMetric::measure(first_summary);
    // let second_size = L::BaseMetric::measure(second_summary);

    // match (first_size >= L::MIN_LEAF_SIZE, second_size >= L::MIN_LEAF_SIZE) {
    //     (true, true) => (
    //         Lnode {
    //             value: first_slice.to_owned(),
    //             summary: first_summary.to_owned(),
    //         },
    //         Some(Lnode {
    //             value: second_slice.to_owned(),
    //             summary: second_summary.to_owned(),
    //         }),
    //     ),

    //     (true, false) => (
    //         Lnode {
    //             value: first_slice.to_owned(),
    //             summary: first_summary.to_owned(),
    //         },
    //         Some(Lnode {
    //             value: second_slice.to_owned(),
    //             summary: second_summary.to_owned(),
    //         }),
    //     ),

    //     (false, true) => (
    //         Lnode {
    //             value: first_slice.to_owned(),
    //             summary: first_summary.to_owned(),
    //         },
    //         Some(Lnode {
    //             value: second_slice.to_owned(),
    //             summary: second_summary.to_owned(),
    //         }),
    //     ),

    //     (false, false) => (
    //         Lnode {
    //             value: first_slice.to_owned(),
    //             summary: first_summary.to_owned(),
    //         },
    //         Some(Lnode {
    //             value: second_slice.to_owned(),
    //             summary: second_summary.to_owned(),
    //         }),
    //     ),
    // }
}
