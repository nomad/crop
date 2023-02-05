#![allow(clippy::explicit_auto_deref)]
#![allow(clippy::module_inception)]
#![deny(rustdoc::broken_intra_doc_links)]

mod rope;
mod tree;

pub mod iter {
    //! Iterators over [`Rope`](crate::Rope)s and
    //! [`RopeSlice`](crate::RopeSlice)s.

    pub use crate::rope::iterators::*;
}

pub use rope::{Rope, RopeBuilder, RopeSlice};
