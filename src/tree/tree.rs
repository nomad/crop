use std::fmt::{self, Debug};
use std::ops::{AddAssign, Range};
use std::sync::Arc;

use super::{Inode, Leaves, Metric, Node, TreeSlice};

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

    /// TODO: docs
    pub fn slice<M>(&self, interval: Range<M>) -> TreeSlice<'_, FANOUT, Leaf>
    where
        M: Metric<Leaf>,
    {
        assert!(interval.start <= interval.end);
        assert!(interval.end <= M::measure(self.summary()));

        let mut measured = M::zero();
        let mut node = &*self.root;

        'outer: loop {
            match node {
                Node::Leaf(leaf) => {
                    let leaf = if (measured + M::measure(leaf.summary()))
                        == interval.end - interval.start
                    {
                        leaf.value()
                    } else {
                        // TODO: this range is wrong.
                        let start = &(interval.start - measured);
                        let end = &(interval.end - measured);
                        M::slice(leaf.value(), start..end).unwrap()
                    };

                    return TreeSlice::single_leaf(leaf);
                },

                Node::Internal(inode) => {
                    for child in inode.children() {
                        let size = M::measure(child.summary());

                        // If the `[measured, measured + size)` interval is
                        // fully contained in `interval` it means `child` fully
                        // contains the final slice => loop again with this
                        // child as `node.
                        if measured <= interval.start
                            && measured + size >= interval.end
                        {
                            node = &*child;
                            continue 'outer;
                        } else {
                            measured += size;
                        }
                    }

                    // If none of this inode's children fully contained
                    // `interval` then this is the deepest node that fully
                    // contains the final slice, so we're done.
                    break;
                },
            }
        }

        todo!()
    }

    /// Returns an iterator over the leaves of this tree.
    pub fn leaves(&self) -> Leaves<'_, Leaf> {
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

    // impl Metric<usize> for usize {
    //     fn measure(summary: &Count) -> usize {
    //         summary.0
    //     }

    //     fn to_base_units(x: usize) -> usize {
    //         todo!()
    //     }

    //     fn from_base_units(x: usize) -> usize {
    //         todo!()
    //     }
    // }

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
        // let slice = tree.slice(1..=2);
        // assert_eq!(Count(3), *slice.summary());
    }
}
