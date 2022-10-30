use std::fmt::{self, Debug};
use std::ops::{AddAssign, Bound, RangeBounds};
use std::sync::Arc;

use super::{Inode, Metric, Node, TreeSlice};

pub trait Summarize: Debug {
    type Summary: Debug
        + Default
        + Clone
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

    pub fn slice<M, R>(&self, interval: R) -> TreeSlice<'_, FANOUT, Leaf>
    where
        R: RangeBounds<M>,
        M: Metric<Leaf>,
    {
        let start = match interval.start_bound() {
            Bound::Excluded(s) => todo!(),
            Bound::Included(s) => todo!(),
            Bound::Unbounded => 0usize,
        };

        let end = match interval.end_bound() {
            Bound::Excluded(s) => todo!(),
            Bound::Included(s) => todo!(),
            Bound::Unbounded => M::measure(self.summary()),
        };

        assert!(start <= end);
        assert!(end <= M::measure(self.summary()));

        // let mut n_start = start;
        // let mut n_end = end;

        let mut measured = 0;
        let mut node = &*self.root;

        'outer: loop {
            match node {
                Node::Leaf(leaf) => todo!(),

                Node::Internal(inode) => {
                    for child in inode.children() {
                        let measure = M::measure(child.summary());

                        if measured <= start && measured + measure >= end {
                            node = &*child;
                            continue 'outer;
                        } else {
                            measured += measure;
                        }
                    }

                    break;
                },
            }
        }

        todo!()
    }

    pub fn summary(&self) -> &Leaf::Summary {
        self.root.summary()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Copy, Clone, Default, Debug, Eq, PartialEq)]
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

    impl Metric<usize> for usize {
        fn measure(summary: &Count) -> usize {
            summary.0
        }

        fn to_base_units(x: usize) -> usize {
            todo!()
        }

        fn from_base_units(x: usize) -> usize {
            todo!()
        }
    }

    #[test]
    fn easy() {
        let tree = Tree::<4, usize>::from_leaves(0..20);
        assert_eq!(Count(190), *tree.summary());
    }

    #[test]
    fn pretty_print() {
        let tree = Tree::<2, usize>::from_leaves(0..10);
        println!("{:#?}", tree);
        panic!("")
    }

    #[test]
    fn slice() {
        let tree = Tree::<2, usize>::from_leaves(0..10);
        let slice = tree.slice(1..=2);
        assert_eq!(Count(3), *slice.summary());
    }
}
