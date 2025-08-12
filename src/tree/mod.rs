mod inode;
mod leaves;
mod node;
mod tiny_arc;
mod traits;
mod tree;
mod tree_builder;
mod tree_slice;
mod units;

use inode::Inode;
use iter_chain::ExactChain;
pub use leaves::Leaves;
use node::Node;
use tiny_arc::Arc;
pub use traits::*;
pub use tree::Tree;
pub use tree_builder::TreeBuilder;
pub use tree_slice::TreeSlice;
pub use units::Units;

mod iter_chain {
    //! This module contains a `Chain` iterator similar to
    //! [`core::iter::Chain`] except it implements `ExactSizeIterator` when
    //! the iterators being chained are both `ExactSizeIterator`.
    //!
    //! See [1] or [2] for why this is needed.
    //!
    //! [1]: https://github.com/rust-lang/rust/issues/34433
    //! [2]: https://github.com/rust-lang/rust/pull/66531

    pub(crate) struct Chain<T, U> {
        chain: core::iter::Chain<T, U>,
        yielded: usize,
        total: usize,
    }

    pub(crate) trait ExactChain<I>:
        ExactSizeIterator<Item = I>
    {
        fn exact_chain<U>(self, other: U) -> Chain<Self, U::IntoIter>
        where
            Self: Sized,
            U: IntoIterator<Item = I>,
            U::IntoIter: ExactSizeIterator;
    }

    impl<I, T> ExactChain<I> for T
    where
        T: ExactSizeIterator<Item = I>,
    {
        #[inline]
        fn exact_chain<U>(self, other: U) -> Chain<Self, U::IntoIter>
        where
            Self: Sized,
            U: IntoIterator<Item = I>,
            U::IntoIter: ExactSizeIterator,
        {
            let other = other.into_iter();
            Chain {
                yielded: 0,
                total: self.len() + other.len(),
                chain: self.chain(other),
            }
        }
    }

    impl<T, I1, I2> Iterator for Chain<I1, I2>
    where
        I1: ExactSizeIterator<Item = T>,
        I2: ExactSizeIterator<Item = T>,
    {
        type Item = T;

        #[inline]
        fn next(&mut self) -> Option<Self::Item> {
            let item = self.chain.next()?;
            self.yielded += 1;
            Some(item)
        }

        #[inline]
        fn size_hint(&self) -> (usize, Option<usize>) {
            let exact = self.len();
            (exact, Some(exact))
        }
    }

    impl<T, I1, I2> ExactSizeIterator for Chain<I1, I2>
    where
        I1: ExactSizeIterator<Item = T>,
        I2: ExactSizeIterator<Item = T>,
    {
        #[inline]
        fn len(&self) -> usize {
            self.total - self.yielded
        }
    }
}
