//! crop is an implementation of a UTF-8 text rope, a data structure designed
//! to be used in applications that need to handle frequent edits to
//! arbitrarily large buffers, such as text editors.
//!
//! crop's `Rope` is backed by a
//! [B-tree](https://en.wikipedia.org/wiki/B-tree), ensuring that the time
//! complexity of inserting, deleting or replacing a piece of text is always
//! logarithmic in the size of the `Rope`.
//!
//! The crate has a relatively straightforward API. There are 3 structs to be
//! aware of:
//!
//! - [`Rope`]: the star of the crate;
//! - [`RopeSlice`]: an immutable slice of a `Rope`;
//! - [`RopeBuilder`]: an incremental `Rope` builder.
//!
//! plus the [`iter`] module which contains iterators over `Rope`s and
//! `RopeSlice`s. That's it.
//!
//! # Example usage
//!
//! ```no_run
//! # use std::fs::{File};
//! # use std::io::{BufWriter, Write};
//! # use std::thread;
//! # use crop::{RopeBuilder, RopeSlice};
//! // A `Rope` can be created either directly from a string or incrementally
//! // using the `RopeBuilder`.
//!
//! let mut builder = RopeBuilder::new();
//!
//! builder
//!     .append("I am a 🦀\n")
//!     .append("Who walks the shore\n")
//!     .append("And pinches toes all day.\n")
//!     .append("\n")
//!     .append("If I were you\n")
//!     .append("I'd wear some 👟\n")
//!     .append("And not get in my way.\n");
//!
//! let mut rope = builder.build();
//!
//! // `Rope`s can be sliced to obtain `RopeSlice`s.
//! //
//! // A `RopeSlice` is to a `Rope` as a `&str` is to a `String`: the former in
//! // each pair are borrowed references of the latter.
//!
//! // A `Rope` can be sliced using either byte offsets:
//!
//! let byte_slice: RopeSlice = rope.byte_slice(..32);
//!
//! assert_eq!(byte_slice, "I am a 🦀\nWho walks the shore\n");
//!
//! // or line offsets:
//!
//! let line_slice: RopeSlice = rope.line_slice(..2);
//!
//! assert_eq!(line_slice, byte_slice);
//!
//! // We can also get a `RopeSlice` by asking the `Rope` for a specific line
//! // index:
//!
//! assert_eq!(rope.line(5), "I'd wear some 👟");
//!
//! // We can modify that line by getting its start/end byte offsets:
//!
//! let start: usize = rope.byte_of_line(5);
//!
//! let end: usize = rope.byte_of_line(6);
//!
//! // and replacing that byte range with some other text:
//!
//! rope.replace(start..end, "I'd rock some 👠\n");
//!
//! assert_eq!(rope.line(5), "I'd rock some 👠");
//!
//! // `Rope`s use `Arc`s to share data between threads, so cloning them is
//! // extremely cheap.
//!
//! let snapshot = rope.clone();
//!
//! // This allows to save a `Rope` to disk in a background thread while
//! // keeping the main thread responsive.
//!
//! thread::spawn(move || {
//!     let mut file =
//!         BufWriter::new(File::create("my_little_poem.txt").unwrap());
//!
//!     // The text content is stored in the leaves of the B-tree, where each
//!     // chunk can store up to 1KB of data.
//!     //
//!     // We can iterate over the leaves using the `Chunks` iterator which
//!     // yields the chunks of the `Rope` as string slices.
//!
//!     for chunk in snapshot.chunks() {
//!         file.write_all(chunk.as_bytes()).unwrap();
//!     }
//! })
//! .join()
//! .unwrap();
//! ```
//!
//! # On offsets and indexes
//!
//! Some functions like [`Rope::byte()`] or [`Rope::line()`] take byte or line
//! **indexes** as parameters, while others like [`Rope::insert()`],
//! [`Rope::replace()`] or [`Rope::is_char_boundary()`] expect byte or line
//! **offsets**.
//!
//! These two terms may sound very similar to each other, but in this context
//! they mean slightly different things.
//!
//! An index is a 0-based number used to target **one specific** byte or line.
//! For example, in the word `"bar"` the byte representing the letter `'b'` has
//! an index of 0, `'a'`'s index is 1 and `'r'`'s index is 2. The maximum value
//! for an index is **one less** than the length of the string.
//!
//! Hopefully nothing surprising so far.
//!
//! On the other hand, an offset doesn't refer to an item, it refers to the
//! **boundary** between two adjacent items. For example, if we want to insert
//! another `'a'` between the `'a'` and the `'r'` of the word `"bar"` we need
//! to use a byte offset of 2. The maximum value for an offset is **equal to**
//! the length of the string.
//!
//! # Feature flags
//!
//! The following feature flags can be used to tweak crop's behavior and
//! enable additional APIs:
//!
//! - `simd` (enabled by default): enables SIMD on supported platforms;
//!
//! - `graphemes` (disabled by default): enables a few grapheme-oriented APIs
//!   on `Rope`s and `RopeSlice`s such as the
//!   [`Graphemes`](crate::iter::Graphemes) iterator and others;
//!
//! - `utf16-metric` (disabled by default): makes the `Rope` and `RopeSlice`
//!   track the UTF-16 code units they'd have if their content was stored as
//!   UTF-16 instead of UTF-8, allowing them to efficiently convert UTF-16
//!   code unit offsets to and from byte offsets in logarithmic time.

#![cfg_attr(not(any(test, feature = "std")), no_std)]
#![allow(clippy::explicit_auto_deref)]
#![allow(clippy::module_inception)]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![deny(missing_docs)]
#![deny(rustdoc::broken_intra_doc_links)]
#![deny(rustdoc::private_intra_doc_links)]
#![warn(clippy::std_instead_of_core)]
#![warn(clippy::std_instead_of_alloc)]
#![warn(clippy::alloc_instead_of_core)]

extern crate alloc;

pub mod iter {
    //! Iterators over [`Rope`](crate::Rope)s and
    //! [`RopeSlice`](crate::RopeSlice)s.

    pub use crate::rope::iterators::*;
}

mod rope;

#[doc(hidden)]
pub mod tree;

// These are not part of the public API, we only export them to be able to run
// doctests.
#[doc(hidden)]
pub use rope::{
    gap_buffer::GapBuffer,
    gap_slice::GapSlice,
    metrics::ChunkSummary,
};
pub use rope::{Rope, RopeBuilder, RopeSlice};

#[inline]
pub(crate) fn range_bounds_to_start_end<T, B>(
    range: B,
    lo: usize,
    hi: usize,
) -> (usize, usize)
where
    B: core::ops::RangeBounds<T>,
    T: core::ops::Add<usize, Output = usize> + Into<usize> + Copy,
{
    use core::ops::Bound;

    let start = match range.start_bound() {
        Bound::Included(&n) => n.into(),
        Bound::Excluded(&n) => n + 1,
        Bound::Unbounded => lo,
    };

    let end = match range.end_bound() {
        Bound::Included(&n) => n + 1,
        Bound::Excluded(&n) => n.into(),
        Bound::Unbounded => hi,
    };

    (start, end)
}
