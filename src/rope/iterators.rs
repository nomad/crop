use super::metrics::LineMetric;
use super::{Rope, RopeSlice, TextChunk};
use crate::tree::{Leaves, Units};

/// TODO: docs
#[derive(Clone)]
pub struct Chunks<'a> {
    leaves: Leaves<'a, { Rope::fanout() }, TextChunk>,
}

impl<'a> From<&'a Rope> for Chunks<'a> {
    #[inline]
    fn from(rope: &'a Rope) -> Self {
        Self { leaves: rope.root().leaves() }
    }
}

impl<'a, 'b: 'a> From<&'a RopeSlice<'b>> for Chunks<'a> {
    #[inline]
    fn from(slice: &'a RopeSlice<'b>) -> Self {
        Self { leaves: slice.tree_slice().leaves() }
    }
}

impl<'a> Iterator for Chunks<'a> {
    type Item = &'a str;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.leaves.next().map(std::ops::Deref::deref)
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let exact = self.leaves.len();
        (exact, Some(exact))
    }
}

impl<'a> DoubleEndedIterator for Chunks<'a> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.leaves.next_back().map(std::ops::Deref::deref)
    }
}

impl<'a> ExactSizeIterator for Chunks<'a> {}

impl<'a> std::iter::FusedIterator for Chunks<'a> {}

/// TODO: docs
#[derive(Clone)]
pub struct Bytes<'a> {
    /// TODO: docs
    chunks: Chunks<'a>,

    /// TODO: docs
    current_forward: &'a [u8],

    /// TODO: docs
    forward_byte_idx: usize,

    /// TODO: docs
    current_backward: &'a [u8],

    /// TODO: docs
    backward_byte_idx: usize,

    /// TODO: docs
    yielded_forward: usize,

    /// TODO: docs
    yielded_backward: usize,

    /// TODO: docs
    total_bytes: usize,
}

impl<'a> From<&'a Rope> for Bytes<'a> {
    #[inline]
    fn from(rope: &'a Rope) -> Self {
        Self {
            chunks: rope.chunks(),
            current_forward: &[],
            forward_byte_idx: 0,
            yielded_forward: 0,
            current_backward: &[],
            backward_byte_idx: 0,
            yielded_backward: 0,
            total_bytes: rope.byte_len(),
        }
    }
}

impl<'a, 'b: 'a> From<&'a RopeSlice<'b>> for Bytes<'a> {
    #[inline]
    fn from(slice: &'a RopeSlice<'b>) -> Self {
        Self {
            chunks: slice.chunks(),
            current_forward: &[],
            forward_byte_idx: 0,
            yielded_forward: 0,
            current_backward: &[],
            backward_byte_idx: 0,
            yielded_backward: 0,
            total_bytes: slice.byte_len(),
        }
    }
}

impl<'a> Iterator for Bytes<'a> {
    type Item = u8;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.yielded_forward + self.yielded_backward == self.total_bytes {
            return None;
        }

        if self.forward_byte_idx == self.current_forward.len() {
            self.current_forward = match self.chunks.next() {
                Some(chunk) => {
                    // NOTE: make sure  there are never empty chunks or this
                    // will make the byte indexing below fail.
                    chunk.as_bytes()
                },

                None => {
                    // There are no more chunks to get but there may be some
                    // bytes yet to yielded on the backward chunk.
                    if self.backward_byte_idx == 0 {
                        return None;
                    } else {
                        // Return the first byte of the backward chunk, make
                        // it one byte smaller and return.

                        let byte = self.current_backward[0];
                        self.current_backward = &self.current_backward[1..];

                        // After making the backward chunk 1 byte smaller we
                        // have to decrease the backward byte idx by one to
                        // keep those in sync.
                        self.backward_byte_idx -= 1;

                        self.yielded_forward += 1;
                        return Some(byte);
                    }
                },
            };
            self.forward_byte_idx = 0;
        }

        let byte = self.current_forward[self.forward_byte_idx];
        self.forward_byte_idx += 1;
        self.yielded_forward += 1;
        Some(byte)
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let exact =
            self.total_bytes - self.yielded_forward - self.yielded_backward;
        (exact, Some(exact))
    }
}

impl<'a> DoubleEndedIterator for Bytes<'a> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.yielded_forward + self.yielded_backward == self.total_bytes {
            return None;
        }

        if self.backward_byte_idx == 0 {
            self.current_backward = match self.chunks.next_back() {
                Some(chunk) => {
                    // NOTE: make sure  there are never empty chunks or this
                    // will make the byte indexing below fail.
                    chunk.as_bytes()
                },

                None => {
                    // There are no more chunks to get but there may be some
                    // bytes yet to yielded on the forward chunk.
                    if self.forward_byte_idx == self.current_forward.len() {
                        return None;
                    } else {
                        // Return the last byte of the forward chunk, make
                        // it one byte smaller and return.
                        let byte = self.current_forward
                            [self.current_forward.len() - 1];

                        self.current_forward = &self.current_forward
                            [..self.current_forward.len() - 1];

                        self.yielded_backward += 1;

                        return Some(byte);
                    }
                },
            };
            self.backward_byte_idx = self.current_backward.len();
        }

        let byte = self.current_backward[self.backward_byte_idx - 1];
        self.backward_byte_idx -= 1;
        self.yielded_backward += 1;
        Some(byte)
    }
}

impl<'a> ExactSizeIterator for Bytes<'a> {}

impl<'a> std::iter::FusedIterator for Bytes<'a> {}

/// TODO: docs
#[derive(Clone)]
pub struct Chars<'a> {
    /// TODO: docs
    chunks: Chunks<'a>,

    /// TODO: docs
    current_forward: &'a str,

    /// Note: this is the number of *bytes* already yielded in `current`, not
    /// chars.
    forward_byte_idx: usize,

    /// TODO: docs
    current_backward: &'a str,

    /// TODO: docs
    backward_byte_idx: usize,

    /// TODO: docs
    yielded_forward: usize,

    /// TODO: docs
    yielded_backward: usize,

    /// TODO: docs
    total_bytes: usize,
}

impl<'a> From<&'a Rope> for Chars<'a> {
    #[inline]
    fn from(rope: &'a Rope) -> Self {
        Self {
            chunks: rope.chunks(),
            current_forward: "",
            forward_byte_idx: 0,
            current_backward: "",
            backward_byte_idx: 0,
            yielded_forward: 0,
            yielded_backward: 0,
            total_bytes: rope.byte_len(),
        }
    }
}

impl<'a, 'b: 'a> From<&'a RopeSlice<'b>> for Chars<'a> {
    #[inline]
    fn from(slice: &'a RopeSlice<'b>) -> Self {
        Self {
            chunks: slice.chunks(),
            current_forward: "",
            forward_byte_idx: 0,
            current_backward: "",
            backward_byte_idx: 0,
            yielded_forward: 0,
            yielded_backward: 0,
            total_bytes: slice.byte_len(),
        }
    }
}

impl<'a> Iterator for Chars<'a> {
    type Item = char;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.yielded_forward + self.yielded_backward == self.total_bytes {
            return None;
        }

        if self.forward_byte_idx == self.current_forward.len() {
            self.current_forward = match self.chunks.next() {
                Some(chunk) => {
                    // NOTE: make sure there are never empty chunks or this
                    // will make the byte indexing below fail.
                    chunk
                },

                None => {
                    // NOTE: see `Bytes::next` for relevant comments.

                    if self.backward_byte_idx == 0 {
                        return None;
                    } else {
                        debug_assert!(self
                            .current_backward
                            .chars()
                            .next()
                            .is_some());

                        let char = unsafe {
                            self.current_backward
                                .chars()
                                .next()
                                // Safety: `backward_byte_idx > 0`, so
                                // there are still chars to yield in this
                                // chunk.
                                .unwrap_unchecked()
                        };

                        let len = char.len_utf8();

                        self.current_backward = &self.current_backward[len..];
                        self.backward_byte_idx -= len;
                        self.yielded_forward += len;
                        return Some(char);
                    }
                },
            };
            self.forward_byte_idx = 0;
        }

        debug_assert!(self.current_forward[self.forward_byte_idx..]
            .chars()
            .next()
            .is_some());

        let char = unsafe {
            self.current_forward[self.forward_byte_idx..]
                .chars()
                .next()
                // Safety: `forward_byte_idx < current_forward.len()`, so there
                // are still chars to yield in this chunk.
                .unwrap_unchecked()
        };

        let len = char.len_utf8();
        self.forward_byte_idx += len;
        self.yielded_forward += len;

        Some(char)
    }
}

impl<'a> DoubleEndedIterator for Chars<'a> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.yielded_forward + self.yielded_backward == self.total_bytes {
            return None;
        }

        if self.backward_byte_idx == 0 {
            self.current_backward = match self.chunks.next_back() {
                Some(chunk) => {
                    // NOTE: make sure there are never empty chunks or this
                    // will make the byte indexing below fail.
                    chunk
                },

                None => {
                    // NOTE: see `Bytes::next_back` for relevant comments.

                    if self.forward_byte_idx == self.current_forward.len() {
                        return None;
                    } else {
                        debug_assert!(self
                            .current_forward
                            .chars()
                            .next_back()
                            .is_some());

                        let char = unsafe {
                            self.current_forward
                                .chars()
                                .next_back()
                                // Safety: `forward_byte_idx <
                                // current_forward.len()`, so there are still
                                // chars to yield in this chunk.
                                .unwrap_unchecked()
                        };

                        let len = char.len_utf8();

                        self.current_forward = &self.current_forward
                            [..self.current_forward.len() - len];

                        self.yielded_backward += len;

                        return Some(char);
                    }
                },
            };
            self.backward_byte_idx = self.current_backward.len();
        }

        debug_assert!(self.current_backward[..self.backward_byte_idx]
            .chars()
            .next_back()
            .is_some());

        let char = unsafe {
            self.current_backward[..self.backward_byte_idx]
                .chars()
                .next_back()
                // Safety: `backward_byte_idx > 0`, so there are still chars to
                // yield in this chunk.
                .unwrap_unchecked()
        };

        let len = char.len_utf8();
        self.backward_byte_idx -= len;
        self.yielded_backward += len;

        Some(char)
    }
}

impl<'a> std::iter::FusedIterator for Chars<'a> {}

/// TODO: docs
#[derive(Clone)]
pub struct Lines<'a> {
    units: Units<'a, { Rope::fanout() }, TextChunk, LineMetric>,
}

impl<'a> From<&'a Rope> for Lines<'a> {
    #[inline]
    fn from(rope: &'a Rope) -> Self {
        Self { units: rope.root().units::<LineMetric>() }
    }
}

impl<'a, 'b: 'a> From<&'a RopeSlice<'b>> for Lines<'a> {
    #[inline]
    fn from(slice: &'a RopeSlice<'b>) -> Self {
        Self { units: slice.tree_slice().units::<LineMetric>() }
    }
}

impl<'a> Iterator for Lines<'a> {
    type Item = RopeSlice<'a>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.units.next().map(RopeSlice::new)
    }
}

#[cfg(feature = "graphemes")]
pub use graphemes::Graphemes;

#[cfg(feature = "graphemes")]
mod graphemes {
    use std::borrow::Cow;

    use unicode_segmentation;

    use super::*;

    /// TODO: docs
    #[derive(Clone)]
    pub struct Graphemes<'a> {
        chunks: Chunks<'a>,
    }

    impl<'a> From<&'a Rope> for Graphemes<'a> {
        #[inline]
        fn from(rope: &'a Rope) -> Self {
            Self { chunks: rope.chunks() }
        }
    }

    impl<'a, 'b: 'a> From<&'a RopeSlice<'b>> for Graphemes<'a> {
        #[inline]
        fn from(slice: &'a RopeSlice<'b>) -> Self {
            Self { chunks: slice.chunks() }
        }
    }

    impl<'a> Iterator for Graphemes<'a> {
        type Item = Cow<'a, str>;

        #[inline]
        fn next(&mut self) -> Option<Self::Item> {
            todo!()
        }
    }

    impl<'a> std::iter::FusedIterator for Graphemes<'a> {}
}

impl<'a> std::iter::FusedIterator for Lines<'a> {}

#[cfg(test)]
mod tests {
    use rand::{thread_rng, Rng};

    use crate::Rope;

    const TINY: &str = include_str!("../../benches/tiny.txt");
    const SMALL: &str = include_str!("../../benches/small.txt");
    const MEDIUM: &str = include_str!("../../benches/medium.txt");
    const LARGE: &str = include_str!("../../benches/large.txt");

    /// A cursed version of a lorem ipsum paragraph taken from [this online
    /// tool][1] with mixed line breaks (LF and CRLF).
    ///
    /// [1]: https://jeff.cis.cabrillo.edu/tools/homoglyphs
    const CURSED_LIPSUM: &str = "Ḽơᶉëᶆ ȋṕšᶙṁ\nḍỡḽǭᵳ ʂǐť ӓṁệẗ,\r\n \
                                 ĉṓɲṩḙċťᶒțûɾ \nấɖḯƥĭ\r\nṩčįɳġ ḝłįʈ, șế\r\nᶑ \
                                 ᶁⱺ ẽḭŭŝḿꝋď\n ṫĕᶆᶈṓɍ ỉñḉīḑȋᵭṵńť \nṷŧ ḹẩḇőꝛế \
                                 éȶ đꝍꞎ\r\nôꝛȇ ᵯáꞡ\r\nᶇā ąⱡ\nîɋṹẵ.";

    #[test]
    fn empty_rope() {
        let r = Rope::from("");
        assert_eq!(0, r.bytes().count());
        assert_eq!(0, r.chars().count());
        assert_eq!(0, r.lines().count());
    }

    #[test]
    fn bytes_forward() {
        let r = Rope::from(LARGE);
        let mut i = 0;
        for (b_rope, b_str) in r.bytes().zip(LARGE.bytes()) {
            assert_eq!(b_rope, b_str);
            i += 1;
        }
        assert_eq!(i, r.byte_len());
    }

    #[test]
    fn bytes_backward() {
        let r = Rope::from(LARGE);
        let mut i = 0;
        for (b_rope, b_str) in r.bytes().rev().zip(LARGE.bytes().rev()) {
            assert_eq!(b_rope, b_str);
            i += 1;
        }
        assert_eq!(i, r.byte_len());
    }

    #[test]
    fn bytes_both_ways() {
        let rope = Rope::from(LARGE);

        let i = thread_rng().gen_range(0..=LARGE.len());

        println!("i: {i}");

        // Go forward for the first `i` bytes, then backward.

        let mut slice_bytes = LARGE.bytes();
        let mut rope_bytes = rope.bytes();

        for _ in 0..i {
            let rope_b = rope_bytes.next().unwrap();
            let slice_b = slice_bytes.next().unwrap();
            assert_eq!(rope_b, slice_b);
        }

        for _ in i..LARGE.len() {
            let rope_b = rope_bytes.next_back().unwrap();
            let slice_b = slice_bytes.next_back().unwrap();
            assert_eq!(rope_b, slice_b);
        }

        assert_eq!(None, rope_bytes.next());
        assert_eq!(None, rope_bytes.next_back());

        // Now the opposite, go backward for the first `i` bytes, then forward.

        let mut slice_bytes = LARGE.bytes();
        let mut rope_bytes = rope.bytes();

        for _ in 0..i {
            let rope_b = rope_bytes.next_back().unwrap();
            let slice_b = slice_bytes.next_back().unwrap();
            assert_eq!(rope_b, slice_b);
        }

        for _ in i..LARGE.len() {
            let rope_b = rope_bytes.next().unwrap();
            let slice_b = slice_bytes.next().unwrap();
            assert_eq!(rope_b, slice_b);
        }

        assert_eq!(None, rope_bytes.next());
        assert_eq!(None, rope_bytes.next_back());
    }

    #[test]
    fn bytes_cursed() {
        let s = CURSED_LIPSUM;
        let r = Rope::from(s);

        assert_eq!(r.bytes().count(), s.bytes().count());
        assert_eq!(r.byte_slice(..).bytes().count(), s.bytes().count());

        for (b1, b2) in r.bytes().zip(s.bytes()) {
            assert_eq!(b1, b2);
        }

        for (b1, b2) in r.bytes().rev().zip(s.bytes().rev()) {
            assert_eq!(b1, b2);
        }
    }

    #[test]
    fn chars_forward() {
        let r = Rope::from(LARGE);
        let mut i = 0;
        for (c_rope, c_str) in r.chars().zip(LARGE.chars()) {
            assert_eq!(c_rope, c_str);
            i += 1;
        }
        assert_eq!(i, LARGE.chars().count());
    }

    #[test]
    fn chars_backward() {
        let r = Rope::from(LARGE);
        let mut i = 0;
        for (c_rope, c_str) in r.chars().rev().zip(LARGE.chars().rev()) {
            assert_eq!(c_rope, c_str);
            i += 1;
        }
        assert_eq!(i, LARGE.chars().count());
    }

    #[test]
    fn chars_both_ways() {
        let rope = Rope::from(LARGE);

        let total_chars = LARGE.chars().count();
        let i = thread_rng().gen_range(0..=total_chars);

        println!("i: {i}");

        // Go forward for the first `i` chars, then backward.

        let mut slice_chars = LARGE.chars();
        let mut rope_chars = rope.chars();

        for _ in 0..i {
            let rope_c = rope_chars.next().unwrap();
            let slice_c = slice_chars.next().unwrap();
            assert_eq!(rope_c, slice_c);
        }

        for _ in i..total_chars {
            let rope_c = rope_chars.next_back().unwrap();
            let slice_c = slice_chars.next_back().unwrap();
            assert_eq!(rope_c, slice_c);
        }

        assert_eq!(None, rope_chars.next());
        assert_eq!(None, rope_chars.next_back());

        // Now the opposite, go backward for the first `i` chars, then forward.

        let mut slice_chars = LARGE.chars();
        let mut rope_chars = rope.chars();

        for _ in 0..i {
            let rope_c = rope_chars.next_back().unwrap();
            let slice_c = slice_chars.next_back().unwrap();
            assert_eq!(rope_c, slice_c);
        }

        for _ in i..total_chars {
            let rope_c = rope_chars.next().unwrap();
            let slice_c = slice_chars.next().unwrap();
            assert_eq!(rope_c, slice_c);
        }

        assert_eq!(None, rope_chars.next());
        assert_eq!(None, rope_chars.next_back());
    }

    #[test]
    fn chars_cursed() {
        let s = CURSED_LIPSUM;
        let r = Rope::from(s);

        assert_eq!(r.chars().count(), s.chars().count());
        assert_eq!(r.byte_slice(..).chars().count(), s.chars().count());

        for (c1, c2) in r.chars().zip(s.chars()) {
            assert_eq!(c1, c2);
        }

        for (c1, c2) in r.chars().rev().zip(s.chars().rev()) {
            assert_eq!(c1, c2);
        }
    }

    #[test]
    fn lines_0() {
        // Note: all these ropes should fit in a single leaf node assuming a
        // `TEXT_CHUNK_MAX_BYTES` of 4 in test mode.

        let r = Rope::from("abc");
        assert_eq!(1, r.lines().count());
        assert_eq!(1, r.byte_slice(..).lines().count());

        let r = Rope::from("a\nb");
        assert_eq!(2, r.lines().count());
        assert_eq!(2, r.byte_slice(..).lines().count());

        let r = Rope::from("a\nb\n");
        assert_eq!(2, r.lines().count());
        assert_eq!(2, r.byte_slice(..).lines().count());

        let r = Rope::from("\n\n\n");
        assert_eq!(3, r.lines().count());
        assert_eq!(3, r.byte_slice(..).lines().count());

        let r = Rope::from("\n\n\n\n");
        assert_eq!(4, r.lines().count());
        assert_eq!(4, r.byte_slice(..).lines().count());

        let r = Rope::from("\n\n\na");
        assert_eq!(4, r.lines().count());
        assert_eq!(4, r.byte_slice(..).lines().count());
    }

    #[test]
    fn lines_1() {
        let s = "\n\n\r\n\r\n\n\r\n\n";

        let rope = Rope::from(s);
        let slice = rope.byte_slice(..);

        assert_eq!(rope.lines().count(), s.lines().count());
        assert_eq!(slice.lines().count(), s.lines().count());

        for ((rope_line, slice_line), s_line) in
            rope.lines().zip(slice.lines()).zip(s.lines())
        {
            assert_eq!(rope_line, s_line);
            assert_eq!(slice_line, s_line);
        }
    }

    #[test]
    fn lines_2() {
        let s = "this is\na line\r\nwith mixed\nline breaks\n";

        let rope = Rope::from(s);
        let slice = rope.byte_slice(..);

        assert_eq!(rope.lines().count(), s.lines().count());
        assert_eq!(slice.lines().count(), s.lines().count());

        for ((rope_line, slice_line), s_line) in
            rope.lines().zip(slice.lines()).zip(s.lines())
        {
            assert_eq!(rope_line, s_line);
            assert_eq!(slice_line, s_line);
        }
    }

    #[test]
    fn lines_3() {
        let s = "This is a piece\nof text that's not \ngonna fit\nin\none \
                 chunk\nand it also\r\nhas mixed\r\n line breaks\n and no \
                 trailing\nline breaks.";

        let rope = Rope::from(s);
        let slice = rope.byte_slice(..);

        assert_eq!(rope.lines().count(), s.lines().count());
        assert_eq!(slice.lines().count(), s.lines().count());

        for ((rope_line, slice_line), s_line) in
            rope.lines().zip(slice.lines()).zip(s.lines())
        {
            assert_eq!(rope_line, s_line);
            assert_eq!(slice_line, s_line);
        }
    }

    #[test]
    fn lines_4() {
        for s in [TINY, SMALL, MEDIUM, LARGE] {
            let rope = Rope::from(s);
            let slice = rope.byte_slice(..);

            assert_eq!(rope.lines().count(), s.lines().count());
            assert_eq!(slice.lines().count(), s.lines().count());

            for ((rope_line, slice_line), s_line) in
                rope.lines().zip(slice.lines()).zip(s.lines())
            {
                assert_eq!(rope_line, s_line);
                assert_eq!(slice_line, s_line);
            }
        }
    }

    #[test]
    fn lines_cursed() {
        let s = CURSED_LIPSUM;
        let r = Rope::from(s);

        assert_eq!(r.lines().count(), s.lines().count());
        assert_eq!(r.byte_slice(..).lines().count(), s.lines().count());

        for (l1, l2) in r.lines().zip(s.lines()) {
            assert_eq!(l1, l2);
        }

        // TODO: uncomment this once we can iterate through lines from the
        // back.
        //
        // for (l1, l2) in r.lines().rev().zip(s.lines().rev()) {
        //     assert_eq!(l1, l2);
        // }
    }
}
