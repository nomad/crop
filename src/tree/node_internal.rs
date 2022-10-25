use std::fmt;
use std::mem::{self, MaybeUninit};
use std::sync::Arc;

use super::{Node, Summarize};

pub(super) struct Inode<const FANOUT: usize, Chunk: Summarize> {
    children: [MaybeUninit<Arc<Node<FANOUT, Chunk>>>; FANOUT],
    initialized: usize,
    summary: Chunk::Summary,
}

impl<const FANOUT: usize, Chunk: Summarize> fmt::Debug
    for Inode<FANOUT, Chunk>
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if !f.alternate() {
            f.debug_struct("Inode")
                .field("children", &self.children())
                .field("initialized", &self.initialized)
                .field("summary", &self.summary)
                .finish()
        } else {
            pretty_print_inode(self, &mut String::new(), "", 0, f)
        }
    }
}

impl<const FANOUT: usize, Chunk: Summarize> Inode<FANOUT, Chunk> {
    fn len(&self) -> usize {
        self.initialized
    }

    /// Note: All the nodes are expected to have the same height.
    pub(super) fn from_nodes<I>(nodes: I) -> Self
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

    pub fn children(&self) -> &[Arc<Node<FANOUT, Chunk>>] {
        unsafe { mem::transmute(&self.children[..self.initialized]) }
    }
}

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
