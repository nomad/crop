//! A B-tree implementation.

use std::borrow::Cow;
use std::fmt;
use std::iter::Sum;
use std::mem::{self, MaybeUninit};
use std::ops::AddAssign;
use std::sync::Arc;

pub trait Summarize: fmt::Debug {
    type Summary: fmt::Debug
        + Clone
        + Default
        + for<'a> AddAssign<&'a Self::Summary>
        + for<'a> Sum<Cow<'a, Self::Summary>>;

    fn summarize(&self) -> Self::Summary;
}

#[derive(Debug)]
pub struct Tree<const FANOUT: usize, Leaf: Summarize> {
    root: Arc<Node<FANOUT, Leaf>>,
}

#[derive(Debug)]
enum Node<const FANOUT: usize, Chunk: Summarize> {
    Internal(Inode<FANOUT, Chunk>),
    Leaf(Leaf<Chunk>),
}

struct Inode<const FANOUT: usize, Chunk: Summarize> {
    summary: Chunk::Summary,
    children: [MaybeUninit<Arc<Node<FANOUT, Chunk>>>; FANOUT],
    initialized: usize,
}

#[derive(Debug)]
struct Leaf<Chunk: Summarize> {
    summary: Chunk::Summary,
    chunk: Chunk,
}

impl<const FANOUT: usize, Chunk: Summarize> Tree<FANOUT, Chunk> {
    pub fn summarize(&self) -> Cow<'_, Chunk::Summary> {
        self.root.summarize()
    }
}

impl<const FANOUT: usize, Chunk: Summarize> Tree<FANOUT, Chunk> {
    /// # Panics
    ///
    /// This function will panic if the iterator is empty.
    pub fn from_leaves<I>(leaves: I) -> Self
    where
        I: IntoIterator<Item = Chunk>,
        I::IntoIter: ExactSizeIterator,
    {
        let mut leaves = leaves.into_iter();

        if leaves.len() == 0 {
            panic!(
                "Cannot construct a Tree<{}> from an empty iterator",
                std::any::type_name::<Chunk>()
            )
        }

        if leaves.len() == 1 {
            // Safety: there is exactly one leaf.
            let chunk = unsafe { leaves.next().unwrap_unchecked() };
            return Tree {
                root: Arc::new(Node::Leaf(Leaf::from_chunk(chunk))),
            };
        }

        let inode =
            Inode::from_nodes(leaves.map(Leaf::from_chunk).map(Node::Leaf));

        Tree { root: Arc::new(Node::Internal(inode)) }
    }
}

impl<const FANOUT: usize, Chunk: Summarize> Node<FANOUT, Chunk> {
    fn summarize(&self) -> Cow<'_, Chunk::Summary> {
        match self {
            Node::Internal(inode) => {
                let mut nodes = inode.initialized().into_iter();

                match (nodes.next(), nodes.next()) {
                    (Some(first), Some(second)) => {
                        let mut summary = first.summarize().into_owned();
                        summary += &*second.summarize();
                        for node in nodes {
                            summary += &*node.summarize();
                        }
                        Cow::Owned(summary)
                    },

                    (Some(first), None) => first.summarize(),

                    (None, Some(_)) => unreachable!(),

                    (None, None) => Cow::Owned(Chunk::Summary::default()),
                }
            },

            Node::Leaf(leaf) => Cow::Borrowed(&leaf.summary),
        }
    }
}

impl<const FANOUT: usize, Chunk: Summarize> Inode<FANOUT, Chunk> {
    /// Note: All the nodes are expected to have the same height.
    pub fn from_nodes<I>(nodes: I) -> Self
    where
        I: IntoIterator<Item = Node<FANOUT, Chunk>>,
        I::IntoIter: ExactSizeIterator,
    {
        let nodes: Box<
            dyn ExactSizeIterator<Item = Arc<Node<FANOUT, Chunk>>>,
        > = Box::new(nodes.into_iter().map(Arc::new));

        let mut nodes = nodes.into_iter().collect::<Vec<_>>();

        while nodes.len() > FANOUT {
            let mut ciao = Vec::<Arc<Node<FANOUT, Chunk>>>::new();

            let (n_nodes, remainder) =
                (nodes.len() / FANOUT, nodes.len() % FANOUT);

            let mut iter = nodes.into_iter();

            for _ in 0..n_nodes {
                // Safety: `n_nodes` is the integer part of `nodes.len() / N`,
                // so nodes is guaranteed to have at least `n_nodes * N`
                // elements.
                let children =
                    unsafe { iter.next_chunk::<FANOUT>().unwrap_unchecked() };

                let summary = children
                    .iter()
                    .map(|node| node.summarize())
                    .sum::<Chunk::Summary>();

                let children = children
                    .into_iter()
                    .map(MaybeUninit::new)
                    .collect::<Vec<_>>();

                ciao.push(Arc::new(Node::Internal(Inode {
                    summary,
                    initialized: FANOUT,
                    // Safety: `children` as exactly `N` elements.
                    children: unsafe {
                        children.try_into().unwrap_unchecked()
                    },
                })))
            }

            if remainder != 0 {
                let mut summary = Chunk::Summary::default();

                // Safety: `iter` had exactly `remainder < N` elements
                // left, so this final call to `next_chunk` will return an
                // `Err` containing the last `remainder` elements.
                let last = unsafe {
                    iter.next_chunk::<FANOUT>().unwrap_err_unchecked()
                };

                let mut last = last
                    .into_iter()
                    .map(|node| {
                        summary += &*node.summarize();
                        MaybeUninit::new(node)
                    })
                    .collect::<Vec<_>>();

                for _ in 0..FANOUT - remainder {
                    last.push(MaybeUninit::uninit());
                }

                ciao.push(Arc::new(Node::Internal(Inode {
                    summary,
                    initialized: remainder,
                    // Safety: `children` as exactly `N` elements.
                    children: unsafe { last.try_into().unwrap_unchecked() },
                })))
            }

            nodes = ciao;
        }

        let summary =
            nodes.iter().map(|node| node.summarize()).sum::<Chunk::Summary>();

        let initialized = nodes.len();

        let mut children =
            nodes.into_iter().map(MaybeUninit::new).collect::<Vec<_>>();

        if initialized < FANOUT {
            for _ in initialized..FANOUT {
                children.push(MaybeUninit::uninit());
            }
        }

        Inode {
            summary,
            initialized,
            // Safety: `children` has exactly `N` elements.
            children: unsafe { children.try_into().unwrap_unchecked() },
        }
    }

    //fn from_m_less_than_n_nodes(nodes: Vec<Arc<Node<Chunk>>>) -> Self {
    //    let m = nodes.len();

    //    assert!(m < N);

    //    let mut children =
    //        nodes.into_iter().map(MaybeUninit::new).collect::<Vec<_>>();

    //    for _ in m..N {
    //        children.push(MaybeUninit::uninit());
    //    }

    //    unsafe { Self::from_n_nodes_unchecked(children) }
    //}

    ///// Safety:
    /////
    ///// * `nodes.len()` has to be exactly equal to `N`.
    //unsafe fn from_n_nodes_unchecked(nodes: Vec<Arc<Node<N, Chunk>>>) -> Self {
    //    todo!()
    //}

    pub fn initialized(&self) -> &[Arc<Node<FANOUT, Chunk>>] {
        unsafe { mem::transmute(&self.children[..self.initialized]) }
    }
}

impl<const FANOUT: usize, Chunk: Summarize> fmt::Debug
    for Inode<FANOUT, Chunk>
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("Inode")
            .field("summary", &self.summary)
            .field("children", &self.initialized())
            .field("initialized", &self.initialized)
            .finish()
    }
}

impl<Chunk: Summarize> Leaf<Chunk> {
    pub fn from_chunk(chunk: Chunk) -> Self {
        Self { summary: chunk.summarize(), chunk }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Clone, Default, Debug)]
    pub struct Count(usize);

    impl<'a> AddAssign<&'a Self> for Count {
        fn add_assign(&mut self, rhs: &'a Self) {
            self.0 += rhs.0;
        }
    }

    impl<'a> Sum<Cow<'a, Count>> for Count {
        fn sum<I>(mut iter: I) -> Self
        where
            I: Iterator<Item = Cow<'a, Count>>,
        {
            let mut res = match iter.next() {
                Some(first) => first.into_owned(),
                None => return Self::default(),
            };
            for summary in iter {
                res += &*summary;
            }
            res
        }
    }

    impl Summarize for usize {
        type Summary = Count;

        fn summarize(&self) -> Self::Summary {
            Count(*self)
        }
    }

    #[test]
    fn easy() {
        let tree = Tree::<4, usize>::from_leaves(0..20);
        panic!("tree: {:?}", tree);
    }
}
