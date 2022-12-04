use std::sync::Arc;

use crate::tree::{Leaf, Node, Tree, TreeSlice};

/// An iterator over the leaves of trees or tree slices.
///
/// This iterator is created via the `leaves` method on
/// [`Tree`](super::Tree::leaves) and [`TreeSlice`](super::TreeSlice::leaves).
pub struct Leaves<'a, const FANOUT: usize, L: Leaf> {
    root: &'a Arc<Node<FANOUT, L>>,
}

impl<'a, const FANOUT: usize, L: Leaf> Clone for Leaves<'a, FANOUT, L> {
    #[inline]
    fn clone(&self) -> Self {
        todo!()
    }
}

impl<'a, const FANOUT: usize, L: Leaf> From<&'a Tree<FANOUT, L>>
    for Leaves<'a, FANOUT, L>
{
    #[inline]
    fn from(tree: &'a Tree<FANOUT, L>) -> Leaves<'a, FANOUT, L> {
        todo!()
    }
}

impl<'a, const FANOUT: usize, L: Leaf> From<&'a TreeSlice<'a, FANOUT, L>>
    for Leaves<'a, FANOUT, L>
{
    #[inline]
    fn from(
        tree_slice: &'a TreeSlice<'a, FANOUT, L>,
    ) -> Leaves<'a, FANOUT, L> {
        todo!()
    }
}

impl<'a, const FANOUT: usize, L: Leaf> Iterator for Leaves<'a, FANOUT, L> {
    type Item = &'a L::Slice;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        todo!()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        todo!()
    }
}

impl<'a, const FANOUT: usize, L: Leaf> DoubleEndedIterator
    for Leaves<'a, FANOUT, L>
{
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        todo!()
    }
}

impl<'a, const FANOUT: usize, L: Leaf> ExactSizeIterator
    for Leaves<'a, FANOUT, L>
{
}

impl<'a, const FANOUT: usize, L: Leaf> std::iter::FusedIterator
    for Leaves<'a, FANOUT, L>
{
}

#[cfg(test)]
mod tests {
    use rand::{thread_rng, Rng};

    use super::*;

    #[test]
    fn leaves_forward() {
        for n in 1..256 {
            let tree = Tree::<2, usize>::from_leaves(0..n);
            let mut leaves = tree.leaves();
            let mut i = 0;
            while let Some(leaf) = leaves.next() {
                assert_eq!(i, *leaf);
                i += 1;
                assert_eq!(n - i, leaves.len());
            }
            assert_eq!(i, n);
            assert_eq!(None, leaves.next());
            assert_eq!(None, leaves.next());
        }
    }

    #[test]
    fn leaves_backward() {
        for n in 1..256 {
            let tree = Tree::<2, usize>::from_leaves(0..n);
            let mut leaves = tree.leaves();
            let mut i = n;
            while let Some(leaf) = leaves.next_back() {
                i -= 1;
                assert_eq!(i, *leaf);
                assert_eq!(i, leaves.len());
            }
            assert_eq!(i, 0);
            assert_eq!(None, leaves.next_back());
            assert_eq!(None, leaves.next_back());
        }
    }

    #[test]
    fn leaves_both_ways() {
        let mut rng = thread_rng();

        for n in 1..256 {
            let tree = Tree::<2, usize>::from_leaves(0..n);
            let mut leaves = tree.leaves();
            let i = rng.gen_range(0..=n);
            for j in 0..i {
                assert_eq!(j, *leaves.next().unwrap());
            }
            for j in (i..n).rev() {
                assert_eq!(j, *leaves.next_back().unwrap());
            }
            assert_eq!(None, leaves.next());
            assert_eq!(None, leaves.next_back());
        }
    }
}
