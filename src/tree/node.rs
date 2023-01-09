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
        from_treeslice::into_node(tree_slice)
        // let mut inode = Inode::empty();

        // build_inode_from_nodes_in_tree_slice_rec(
        //     &mut inode,
        //     tree_slice.root,
        //     &tree_slice,
        //     L::BaseMetric::measure(&tree_slice.before),
        //     &mut L::BaseMetric::zero(),
        //     &mut 0,
        // );

        // if inode.children().len() == 1 {
        //     debug_assert_eq!(1, inode.depth());
        //     let leaf = inode.children.into_iter().next().unwrap();
        //     debug_assert!(leaf.is_leaf());
        //     Self::clone(&*leaf)
        // } else {
        //     Self::Internal(inode)
        // }
    }
}

impl<const N: usize, L: Leaf> Node<N, L> {
    #[cfg(integration_tests)]
    pub(super) fn assert_invariants(&self) {
        if let Node::Internal(inode) = self {
            inode.assert_invariants();

            for child in inode.children() {
                child.assert_invariants()
            }
        }
    }

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

/// Recursively traverses the nodes spanned by the TreeSlice and appends them
/// to `out`, rebalancing the first/last leaf slice with the second/penultimate
/// leaf if necessary.
///
/// Does not handle the cases `tree_slice.num_leaves = 1 | 2`, those are
/// expected to be special cased and handled by the caller.
#[inline]
fn build_inode_from_nodes_in_tree_slice_rec<'a, const N: usize, L: Leaf>(
    out: &mut Inode<N, L>,
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
                            build_inode_from_nodes_in_tree_slice_rec(
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
                        build_inode_from_nodes_in_tree_slice_rec(
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
                        out.append(Arc::clone(child));
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

                    debug_assert_eq!(0, out.children().len());

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
                            out.push(Arc::new(Node::Leaf(first)));

                            let (second, third) = balance_slices(
                                second.as_slice(),
                                second.summary(),
                                tree_slice.end_slice,
                                &tree_slice.end_summary,
                            );

                            out.append(Arc::new(Node::Leaf(second)));

                            if let Some(third) = third {
                                out.append(Arc::new(Node::Leaf(third)));
                            }
                        } else {
                            let (first, second) = balance_slices(
                                first.as_slice(),
                                first.summary(),
                                tree_slice.end_slice,
                                &tree_slice.end_summary,
                            );

                            out.push(Arc::new(Node::Leaf(first)));

                            if let Some(second) = second {
                                out.append(Arc::new(Node::Leaf(second)));
                            }
                        }
                    } else {
                        debug_assert!(tree_slice.num_leaves > 3);

                        *leaves_visited = 2;

                        out.push(Arc::new(Node::Leaf(first)));

                        if let Some(second) = second {
                            out.append(Arc::new(Node::Leaf(second)));
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

                    out.append(Arc::new(Node::Leaf(penultimate)));

                    if let Some(last) = last {
                        out.append(Arc::new(Node::Leaf(last)));
                    }
                },

                _ => {
                    // Finally, this leaf is fully contained in the TreeSlice.
                    out.append(Arc::clone(node));
                    *leaves_visited += 1;
                },
            }
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

mod from_treeslice {
    //! Functions used to convert `TreeSlice`s into `Node`s.

    use super::*;

    /// This is the only public function this module exports and it converts a
    /// `TreeSlice` into a balanced `Node`.
    #[inline]
    pub(super) fn into_node<'a, const N: usize, L: Leaf>(
        tree_slice: TreeSlice<'a, N, L>,
    ) -> Node<N, L> {
        match tree_slice.num_leaves {
            1 => {
                debug_assert!(tree_slice.root.is_leaf());

                Node::Leaf(Lnode {
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
                    Node::Internal(inode)
                } else {
                    Node::Leaf(first)
                }
            },

            _ => {
                let inode = slice_before_after(tree_slice);

                Node::Internal(inode)
            },
        }
    }

    /// TODO: docs
    #[inline]
    fn slice_before_after<'a, const N: usize, L: Leaf>(
        tree_slice: TreeSlice<'a, N, L>,
    ) -> Inode<N, L> {
        let mut inode = Inode::empty();

        let mut measured = L::BaseMetric::zero();

        let mut found_start = false;

        let start = L::BaseMetric::measure(&tree_slice.before);

        let end = start + L::BaseMetric::measure(tree_slice.summary());

        // Safety: if the TreeSlice's root was a leaf it would only have had a
        // single leaf, but this function can only be called if the TreeSlice
        // spans 3+ leaves.
        let root = unsafe { tree_slice.root.as_internal_unchecked() };

        for node in root.children() {
            let size = L::BaseMetric::measure(node.summary());

            if !found_start {
                if measured + size > start {
                    inode.push(something_start_rec(
                        &**node,
                        start - measured,
                        tree_slice.start_slice,
                        tree_slice.start_summary.clone(),
                    ));
                    found_start = true;
                }
                measured += size;
            } else if measured + size >= end {
                inode.push(something_end_rec(
                    &**node,
                    end - measured,
                    tree_slice.end_slice,
                    tree_slice.end_summary.clone(),
                ));
                break;
            } else {
                inode.push(Arc::clone(node));
                measured += size;
            }
        }

        inode
    }

    #[inline]
    fn something_start_rec<'a, const N: usize, L: Leaf>(
        node: &Node<N, L>,
        from: L::BaseMetric,
        start_slice: &'a L::Slice,
        start_summary: L::Summary,
    ) -> Arc<Node<N, L>> {
        match node {
            Node::Internal(inode) => {
                let mut measured = L::BaseMetric::zero();

                let mut i = Inode::empty();

                let mut children = inode.children().iter();

                while let Some(child) = children.next() {
                    let this = L::BaseMetric::measure(child.summary());

                    if measured + this > from {
                        i.push(something_start_rec(
                            child,
                            from - measured,
                            start_slice,
                            start_summary,
                        ));

                        for child in children {
                            i.push(Arc::clone(child));
                        }

                        break;
                    } else {
                        measured += this;
                    }
                }

                Arc::new(Node::Internal(i))
            },

            Node::Leaf(_) => Arc::new(Node::Leaf(Lnode {
                value: start_slice.to_owned(),
                summary: start_summary,
            })),
        }
    }

    #[inline]
    fn something_end_rec<'a, const N: usize, L: Leaf>(
        node: &Node<N, L>,
        up_to: L::BaseMetric,
        end_slice: &'a L::Slice,
        end_summary: L::Summary,
    ) -> Arc<Node<N, L>> {
        match node {
            Node::Internal(inode) => {
                let mut measured = L::BaseMetric::zero();

                let mut i = Inode::empty();

                let mut children = inode.children().iter();

                while let Some(child) = children.next() {
                    let this = L::BaseMetric::measure(child.summary());

                    if measured + this >= up_to {
                        i.push(something_end_rec(
                            child,
                            up_to - measured,
                            end_slice,
                            end_summary,
                        ));

                        break;
                    } else {
                        i.push(Arc::clone(child));
                        measured += this;
                    }
                }

                Arc::new(Node::Internal(i))
            },

            Node::Leaf(_) => Arc::new(Node::Leaf(Lnode {
                value: end_slice.to_owned(),
                summary: end_summary,
            })),
        }
    }
}
