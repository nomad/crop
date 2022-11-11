#![feature(iter_next_chunk)]

mod rope;
pub mod tree;

pub mod iter {
    //! Iterators over [`Rope`](crate::Rope)s.

    pub use crate::rope::iterators::*;
}

pub use rope::{Rope, RopeSlice};
