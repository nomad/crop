use std::borrow::Cow;
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

    pub(super) fn children(&self) -> &[Arc<Node<FANOUT, Chunk>>] {
        // Safety: the first `initialized` elements are guaranteed to be
        // initialized and `MaybeUninit<T>` has the same memory layout as `T`.
        unsafe { mem::transmute(&self.children[..self.initialized]) }
    }

    pub(super) fn summarize(&self) -> Cow<'_, Chunk::Summary> {
        let mut children = self.children().into_iter();

        match (children.next(), children.next()) {
            (Some(first), Some(second)) => {
                let mut summary = first.summarize().into_owned();
                summary += &*second.summarize();
                for node in children {
                    summary += &*node.summarize();
                }
                Cow::Owned(summary)
            },

            (Some(first), None) => first.summarize(),

            (None, Some(_)) => unreachable!(),

            (None, None) => Cow::Owned(Chunk::Summary::default()),
        }
    }

    /// TODO: docs
    ///
    /// Note: All the nodes are expected to have the same height.
    pub(super) fn from_nodes<I>(nodes: I) -> Self
    where
        I: IntoIterator<Item = Node<FANOUT, Chunk>>,
        I::IntoIter: ExactSizeIterator,
    {
        let mut nodes = nodes
            .into_iter()
            .map(Arc::new)
            .map(MaybeUninit::new)
            .collect::<Vec<_>>();

        while nodes.len() > FANOUT {
            // TODO: this allocates a `new_nodes` at every iteration. Can
            // we reuse `nodes`?

            let mut new_nodes =
                Vec::with_capacity(usize::div_ceil(nodes.len(), FANOUT));

            let mut iter = nodes.into_iter().array_chunks::<FANOUT>();

            while let Some(children) = iter.next() {
                let summary = children
                    .iter()
                    .map(|node| unsafe { node.assume_init_ref().summarize() })
                    .sum::<Chunk::Summary>();

                new_nodes.push(MaybeUninit::new(Arc::new(Node::Internal(
                    Inode { summary, children, initialized: FANOUT },
                ))));
            }

            if let Some(last) = iter.into_remainder() {
                if last.len() > 0 {
                    let last = last.into_iter().collect();

                    // Safety: all the nodes in this last chunk are initialized
                    // and `last` contains at most `FANOUT - 1` elements.
                    let inode =
                        unsafe { Self::from_m_less_than_n_children(last) };

                    new_nodes.push(MaybeUninit::new(Arc::new(
                        Node::Internal(inode),
                    )));
                }
            }

            nodes = new_nodes;
        }

        // Safety: all the nodes are initialized and nodes.len() <= FANOUT.
        unsafe { Self::from_m_less_than_n_children(nodes) }
    }

    /// TODO: docs
    ///
    /// # Panics
    ///
    /// - `children.len()` has to be less than or equal to `FANOUT`.
    ///
    /// # Safety
    ///
    /// - all the children have to be initialized.
    ///
    /// Note: All the children are expected to have the same height.
    unsafe fn from_m_less_than_n_children(
        mut children: Vec<MaybeUninit<Arc<Node<FANOUT, Chunk>>>>,
    ) -> Self {
        assert!(children.len() <= FANOUT);

        let initialized = children.len();

        let summary = children
            .iter()
            .map(|node| node.assume_init_ref().summarize())
            .sum::<Chunk::Summary>();

        for _ in initialized..FANOUT {
            children.push(MaybeUninit::uninit());
        }

        Self {
            summary,
            initialized,
            // Safety: `children` has exactly `FANOUT` elements.
            children: children.try_into().unwrap_unchecked(),
        }
    }
}

/// TODO: docs
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
