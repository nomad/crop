use std::sync::Arc;

use super::{Inode, Leaf, Lnode, Metric, Summarize, TreeSlice};

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
                // TODO: rebalance leaves if necessary

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

                stufff_rec(
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

/// Does not handle the cases `tree_slice.num_leaves = 1 | 2`, those are
/// expected to be special cased and handled by the caller.
#[inline]
fn stufff_rec<'a, const N: usize, L: Leaf>(
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
                    0 => {
                        let measure = L::BaseMetric::measure(child.summary());

                        if *measured + measure > before {
                            stufff_rec(
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
                        // leaf. In which case we recurse down to get to that
                        // leaf.
                        stufff_rec(
                            out,
                            child,
                            tree_slice,
                            before,
                            measured,
                            leaves_visited,
                        );
                    },

                    n if n == tree_slice.num_leaves => {
                        return;
                    },

                    _ => {
                        // Finally, this is a fully contained in the slice
                        // that's between (and not including) the second and
                        // penultimate node.
                        add_to_node(out, Arc::clone(child));
                        *leaves_visited += child.num_leaves();
                    },
                }
            }
        },

        Node::Leaf(leaf) => {
            match *leaves_visited {
                0 => {
                    let measure = L::BaseMetric::measure(leaf.summary());

                    if *measured + measure > before {
                        *leaves_visited = 1;
                    } else {
                        // This leaf comes before the starting slice.
                        *measured += measure;
                    }
                },

                1 => {
                    let (first, second) = balance_slices(
                        tree_slice.start_slice,
                        &tree_slice.start_summary,
                        leaf.as_slice(),
                        leaf.summary(),
                    );

                    if tree_slice.num_leaves == 3 {
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

                        // TODO: explain why we can unwrap
                        add_to_node(
                            out,
                            Arc::new(Node::Leaf(second.unwrap())),
                        );
                    }
                },

                n if n + 1 == tree_slice.num_leaves - 1 => {
                    *leaves_visited = tree_slice.num_leaves;

                    // This is the penultimate leaf.

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

                n if n == tree_slice.num_leaves => return,

                _ => {
                    // This is a leaf fully contained in the tree slice.
                    add_to_node(out, Arc::clone(node));
                    *leaves_visited += 1;
                },
            }
        },
    }
}

#[inline]
fn stuff_rec<const N: usize, L: Leaf>(
    node: &Arc<Node<N, L>>,
    adding_to: &mut Node<N, L>,
    before: L::BaseMetric,
    leaves_in_slice: usize,
    start_slice: &L::Slice,
    end_slice: &L::Slice,
    measured: &mut L::BaseMetric,
    visited_leaves: &mut usize,
    found_start: &mut bool,
    looking_for_start: &mut bool,
) {
    match &**node {
        Node::Internal(inode) => {
            for child in inode.children() {
                if *visited_leaves == leaves_in_slice {
                    return;
                }

                if !*found_start {
                    debug_assert_eq!(*visited_leaves, 0);

                    let measure = L::BaseMetric::measure(child.summary());

                    if *measured + measure > before {
                        stuff_rec(
                            child,
                            adding_to,
                            before,
                            leaves_in_slice,
                            start_slice,
                            end_slice,
                            measured,
                            visited_leaves,
                            found_start,
                            looking_for_start,
                        );
                    } else {
                        // This child comes before the starting leaf.
                        *measured += measure;
                    }
                } else if *looking_for_start {
                    // Always recurse if looking for start bc we need to get to
                    // a leaf.
                    debug_assert_eq!(*visited_leaves, 1);
                    stuff_rec(
                        child,
                        adding_to,
                        before,
                        leaves_in_slice,
                        start_slice,
                        end_slice,
                        measured,
                        visited_leaves,
                        found_start,
                        looking_for_start,
                    );
                } else {
                    debug_assert!(*visited_leaves > 0);
                    debug_assert!(*visited_leaves < leaves_in_slice);

                    if *visited_leaves + child.num_leaves()
                        >= leaves_in_slice - 1
                    {
                        stuff_rec(
                            child,
                            adding_to,
                            before,
                            leaves_in_slice,
                            start_slice,
                            end_slice,
                            measured,
                            visited_leaves,
                            found_start,
                            looking_for_start,
                        );
                    } else {
                        add_to_node(adding_to, Arc::clone(child));
                        *visited_leaves += child.num_leaves();
                    }
                }
            }
        },

        Node::Leaf(leaf) => {
            if *visited_leaves == leaves_in_slice {
                return;
            }

            if !*found_start {
                debug_assert_eq!(*visited_leaves, 0);

                let measure = L::BaseMetric::measure(leaf.summary());

                if *measured + measure > before {
                    // This leaf contains the start slice.
                    //
                    // TODO: avoid calling `summarize` again.

                    *found_start = true;

                    *visited_leaves = 1;

                    let start_summary = start_slice.summarize();

                    if L::BaseMetric::measure(&start_summary)
                        >= L::MIN_LEAF_SIZE
                    {
                        *adding_to = Node::Leaf(Lnode {
                            value: start_slice.to_owned(),
                            summary: start_summary,
                        });
                    } else {
                        *looking_for_start = true;
                    }
                } else {
                    // This leaf comes before the start slice.
                    *measured += measure;
                }
            } else if *looking_for_start {
                // We visited the first leaf but it wasn't big enough to become
                // a node on its own.

                // TODO: handle case w/ 3 leaves where this is also the
                // penultimate slice.

                debug_assert_eq!(*visited_leaves, 1);

                debug_assert!(
                    L::BaseMetric::measure(&start_slice.summarize())
                        < L::MIN_LEAF_SIZE
                );

                let mut start_summary = start_slice.summarize();

                let add_to_first =
                    L::MIN_LEAF_SIZE - L::BaseMetric::measure(&start_summary);

                // This leaf comes before the start slice.
                let (
                    add_to_first,
                    first_summary,
                    keep_in_second,
                    second_summary,
                ) = L::BaseMetric::split(
                    leaf.as_slice(),
                    add_to_first,
                    leaf.summary(),
                );

                let mut first = start_slice.to_owned();
                first.append_slice(add_to_first);

                start_summary += &first_summary;

                *adding_to =
                    Node::Leaf(Lnode { value: first, summary: start_summary });

                let second = Arc::new(Node::Leaf(Lnode {
                    value: keep_in_second.to_owned(),
                    summary: second_summary,
                }));

                add_to_node(adding_to, second);

                *looking_for_start = false;
                *visited_leaves = 2;
            } else if *visited_leaves + 2 == leaves_in_slice {
                // TODO: explain why the +2

                // This is the penultimate leaf.

                let mut end_summary = end_slice.summarize();

                let end_size = L::BaseMetric::measure(&end_summary);

                if end_size >= L::MIN_LEAF_SIZE {
                    add_to_node(adding_to, Arc::clone(node));

                    let last = Arc::new(Node::Leaf(Lnode {
                        value: end_slice.to_owned(),
                        summary: end_summary,
                    }));

                    add_to_node(adding_to, last);
                } else {
                    let (
                        keep_in_penultimate,
                        penultimate_summary,
                        add_to_last,
                        last_summary,
                    ) = L::BaseMetric::split(
                        leaf.as_slice(),
                        L::MIN_LEAF_SIZE - end_size,
                        leaf.summary(),
                    );

                    add_to_node(
                        adding_to,
                        Arc::new(Node::Leaf(Lnode {
                            value: keep_in_penultimate.to_owned(),
                            summary: penultimate_summary,
                        })),
                    );

                    let mut last = add_to_last.to_owned();
                    last.append_slice(end_slice);

                    end_summary += &last_summary;

                    add_to_node(
                        adding_to,
                        Arc::new(Node::Leaf(Lnode {
                            value: last,
                            summary: end_summary,
                        })),
                    );
                }

                *visited_leaves = leaves_in_slice;
            } else {
                // This is a leaf fully contained in the tree slice.
                debug_assert!(*visited_leaves > 0);
                debug_assert!(*visited_leaves < leaves_in_slice);

                add_to_node(adding_to, Arc::clone(node));
                *visited_leaves += 1;
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
