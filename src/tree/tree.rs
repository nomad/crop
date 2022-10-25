//! A B-tree implementation.

use std::borrow::Cow;
use std::fmt;
use std::iter::Sum;
use std::ops::AddAssign;
use std::sync::Arc;

use super::{Inode, Leaf, Node};

pub trait Summarize: fmt::Debug {
    type Summary: fmt::Debug
        + Clone
        + for<'a> AddAssign<&'a Self::Summary>
        + for<'a> Sum<Cow<'a, Self::Summary>>;

    fn summarize(&self) -> Self::Summary;
}

pub struct Tree<const FANOUT: usize, Leaf: Summarize> {
    root: Arc<Node<FANOUT, Leaf>>,
}

impl<const FANOUT: usize, Chunk: Summarize> fmt::Debug
    for Tree<FANOUT, Chunk>
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if !f.alternate() {
            f.debug_struct("Tree").field("root", &self.root).finish()
        } else {
            let punctuation =
                if self.root.is_internal() { " —" } else { ":" };

            write!(f, "root{} {:#?}", punctuation, self.root)
        }
    }
}

impl<const FANOUT: usize, Chunk: Summarize> Tree<FANOUT, Chunk> {
    pub fn summarize(&self) -> Cow<'_, Chunk::Summary> {
        self.root.summarize()
    }

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
        let _tree = Tree::<4, usize>::from_leaves(0..20);
    }

    #[test]
    fn pretty_print() {
        let tree = Tree::<2, usize>::from_leaves(0..10);
        println!("{:#?}", tree);
        panic!("")
    }
}
