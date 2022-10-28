//! A B-tree implementation.

use std::fmt::{self, Debug};
use std::ops::AddAssign;
use std::sync::Arc;

use super::{Inode, Node};

pub trait Summarize: Debug {
    type Summary: Debug
        + Clone
        + Default
        + for<'a> AddAssign<&'a Self::Summary>;

    fn summarize(&self) -> Self::Summary;
}

pub struct Tree<const FANOUT: usize, Leaf: Summarize> {
    root: Arc<Node<FANOUT, Leaf>>,
}

impl<const N: usize, Leaf: Summarize> Debug for Tree<N, Leaf> {
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

impl<const FANOUT: usize, Leaf: Summarize> Tree<FANOUT, Leaf> {
    /// # Panics
    ///
    /// This function will panic if the iterator is empty.
    pub fn from_leaves<I>(leaves: I) -> Self
    where
        I: IntoIterator<Item = Leaf>,
        I::IntoIter: ExactSizeIterator,
    {
        let mut leaves = leaves.into_iter();

        if leaves.len() == 0 {
            panic!(
                "Cannot construct a Tree<{}, {}> from an empty iterator",
                FANOUT,
                std::any::type_name::<Leaf>(),
            )
        }

        if leaves.len() == 1 {
            let leaf = super::Leaf::from_value(leaves.next().unwrap());
            return Tree { root: Arc::new(Node::Leaf(leaf)) };
        }

        Tree { root: Arc::new(Node::Internal(Inode::from_leaves(leaves))) }
    }

    pub fn summarize(&self) -> &Leaf::Summary {
        self.root.summary()
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

    impl Summarize for usize {
        type Summary = Count;

        fn summarize(&self) -> Self::Summary {
            Count(*self)
        }
    }

    #[test]
    fn easy() {
        // let _tree = Tree::<4, usize>::from_leaves(0..20);
    }

    #[test]
    fn pretty_print() {
        // let tree = Tree::<2, usize>::from_leaves(0..20);
        let tree = Tree::<2, usize>::from_leaves(0..4);
        println!("{:#?}", tree);
        panic!("")
    }
}
