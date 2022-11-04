use std::ops::Range;

use super::{Inode, LeafCoordinates, Leaves, Metric, Node, Summarize};

#[derive(Clone)]
pub struct TreeSlice<'a, const FANOUT: usize, Leaf: Summarize> {
    kind: SliceKind<'a, FANOUT, Leaf>,
    summary: Leaf::Summary,
}

#[derive(Clone)]
enum SliceKind<'a, const N: usize, Leaf: Summarize> {
    /// The slice is fully contained in a single leaf.
    SingleLeaf(&'a Leaf),

    /// The slice spans multiple leaves.
    SubTree {
        /// The deepest internal node in the tree that still fully contains the
        /// interval from which this slice was derived.
        inode: &'a Inode<N, Leaf>,

        /// TODO: docs, use super::Leaf so that we also store the summary?
        start_leaf: (LeafCoordinates<N>, Option<&'a Leaf>),

        /// TODO: docs
        end_leaf: (LeafCoordinates<N>, Option<&'a Leaf>),
    },
}

impl<'a, const FANOUT: usize, Leaf: Summarize> TreeSlice<'a, FANOUT, Leaf> {
    /// TODO: docs
    pub fn leaves(&self) -> Leaves<'_, Leaf> {
        todo!()
    }

    /// TODO: docs
    pub(super) fn new_single_leaf(
        leaf: &'a Leaf,
    ) -> TreeSlice<'a, FANOUT, Leaf> {
        Self { kind: SliceKind::SingleLeaf(leaf), summary: leaf.summarize() }
    }

    /// TODO: docs
    pub(super) fn new_from_range_in_inode<M>(
        inode: &'a Node<FANOUT, Leaf>,
        range: Range<M>,
    ) -> Self
    where
        M: Metric<Leaf>,
    {
        println!("{:#?}", inode);
        println!("range: {range:?}");

        let (summary, start_leaf, end_leaf) =
            inode_get_summary_start_end_in_range(inode, range);

        let inode = inode.as_inode().unwrap();

        Self {
            kind: SliceKind::SubTree { inode, start_leaf, end_leaf },
            summary,
        }
    }

    /// TODO: docs
    pub fn slice<M>(&self, interval: Range<M>) -> TreeSlice<'a, FANOUT, Leaf>
    where
        M: Metric<Leaf>,
    {
        todo!()
    }

    /// TODO: docs
    pub fn summary(&self) -> &Leaf::Summary {
        &self.summary
    }
}

pub(super) enum Diocane<'a, const N: usize, L: Summarize, M: Metric<L>> {
    Leaf(&'a L),
    Inode(&'a Node<N, L>, Range<M>),
}

/// TODO: docs
pub(super) fn deepest_node_containing_range<const N: usize, L, M>(
    mut node: &Node<N, L>,
    mut range: Range<M>,
) -> Diocane<'_, N, L, M>
where
    L: Summarize,
    M: Metric<L>,
{
    let zero = M::zero();

    assert!(zero <= range.start);
    assert!(range.start <= range.end);
    assert!(range.end <= M::measure(node.summary()));

    'outer: loop {
        match node {
            Node::Leaf(leaf) => {
                // If the leaf's size is perfectly equal to the width of the
                // range we return the leaf's value. If not then the range is
                // strictly smaller than the leaf and the latter *must* be
                // sliceable by `M` (hence the unwrap).
                //
                // TODO: better panic message if `M::slice` returns a None?
                let size = M::measure(leaf.summary());
                let value = if size == range.end - range.start {
                    leaf.value()
                } else {
                    M::slice(leaf.value(), range).unwrap()
                };
                return Diocane::Leaf(value);
            },

            Node::Internal(inode) => {
                let mut measured = zero;
                for child in inode.children() {
                    let size = M::measure(child.summary());
                    if range.start > measured && range.end <= measured + size {
                        range.start -= measured;
                        range.end -= measured;
                        node = &*child;
                        continue 'outer;
                    } else {
                        measured += size;
                    }
                }
                // If none of the inode's children fully contained the range
                // then the inode itself must be the deepest node that fully
                // contains the range, so we're done.
                return Diocane::Inode(node, range);
            },
        }
    }
}

/// TODO: docs
///
/// # Panics
///
/// - `range` is not fully contained in `inode`.
pub(super) fn inode_get_summary_start_end_in_range<const N: usize, L, M>(
    inode: &Node<N, L>,
    range: Range<M>,
) -> (
    L::Summary,
    (LeafCoordinates<N>, Option<&'_ L>),
    (LeafCoordinates<N>, Option<&'_ L>),
)
where
    L: Summarize,
    M: Metric<L>,
{
    let zero = M::zero();

    assert!(zero <= range.start);
    assert!(range.start <= range.end);
    assert!(range.end <= M::measure(inode.summary()));

    let mut summary = L::Summary::default();

    let mut start_coord = LeafCoordinates::<N>::new();
    let mut end_coord = LeafCoordinates::<N>::new();

    let mut start_leaf = None;
    let mut end_leaf = None;

    let mut measured = zero;

    // TODO: logic

    println!("#######################");
    println!("{inode:#?}");
    println!("range: {range:?}");
    println!("#######################");

    let mut node = inode;

    'outer: loop {
        match node {
            Node::Leaf(leaf) => {
                if range.start > measured {
                    let start = range.start;
                    let end = M::measure(leaf.summary());
                    let leaf = M::slice(leaf.value(), start..end).unwrap();
                    summary += &leaf.summarize();
                    start_leaf = Some(leaf);
                } else {
                    summary += leaf.summary();
                }
                break;
            },

            Node::Internal(inode) => {
                for (idx, child) in inode.children().iter().enumerate() {
                    let size = M::measure(child.summary());

                    println!("measured: {measured:?}");
                    println!("size: {size:?}");

                    if measured + size >= range.start {
                        println!("looping again with {child:#?}");
                        node = &*child;
                        start_coord.push(idx);
                        continue 'outer;
                    } else {
                        summary += child.summary();
                        measured += size;
                    }
                }
                panic!("")
            },
        }
    }

    println!("start: {start_coord:?}");
    println!("summary: {summary:?}");
    println!("-----------------------");

    'outer: loop {
        match node {
            Node::Leaf(leaf) => {
                let size = M::measure(leaf.summary());
                if measured + size > range.end {
                    let start = M::zero();
                    let end = range.end - measured;
                    let leaf = M::slice(leaf.value(), start..end).unwrap();
                    summary += &leaf.summarize();
                    end_leaf = Some(leaf);
                } else {
                    summary += leaf.summary();
                }
                break;
            },

            Node::Internal(inode) => {
                for (idx, child) in inode.children().iter().enumerate() {
                    let size = M::measure(child.summary());

                    println!("measured: {measured:?}");
                    println!("size: {size:?}");

                    if measured + size >= range.end {
                        println!("looping again with {child:#?}");
                        node = &*child;
                        end_coord.push(idx);
                        continue 'outer;
                    } else {
                        summary += child.summary();
                        measured += size;
                    }
                }
                panic!("")
            },
        }
    }

    (summary, (start_coord, start_leaf), (end_coord, end_leaf))
}
