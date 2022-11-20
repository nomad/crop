use super::metrics::LineMetric;
use super::{Rope, RopeSlice, TextChunk};
use crate::tree::{Leaves, Units};

/// TODO: docs
#[derive(Clone)]
pub(super) struct Chunks<'a> {
    pub(super) chunks: Leaves<'a, { Rope::fanout() }, TextChunk>,
}

impl<'a> Iterator for Chunks<'a> {
    type Item = &'a str;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.chunks.next().map(std::ops::Deref::deref)
    }
}

/// TODO: docs
#[derive(Clone)]
pub struct Bytes<'a> {
    chunks: Chunks<'a>,
    current: &'a [u8],
    yielded_in_current: usize,
    total_yielded: usize,
    total_bytes: usize,
}

impl<'a> From<&'a Rope> for Bytes<'a> {
    #[inline]
    fn from(rope: &'a Rope) -> Self {
        let mut chunks = rope.chunks();
        let current = chunks.next().unwrap_or("").as_bytes();
        Self {
            chunks,
            current,
            yielded_in_current: 0,
            total_yielded: 0,
            total_bytes: rope.byte_len(),
        }
    }
}

impl<'a, 'b: 'a> From<&'a RopeSlice<'b>> for Bytes<'a> {
    #[inline]
    fn from(slice: &'a RopeSlice<'b>) -> Self {
        let mut chunks = slice.chunks();
        let current = chunks.next().unwrap_or_default().as_bytes();
        Self {
            chunks,
            current,
            yielded_in_current: 0,
            total_yielded: 0,
            total_bytes: slice.byte_len(),
        }
    }
}

impl<'a> Iterator for Bytes<'a> {
    type Item = u8;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.yielded_in_current == self.current.len() {
            // NOTE: make sure there are never empty chunks or this will make
            // the byte indexing below fail.
            self.current = self.chunks.next()?.as_bytes();
            self.yielded_in_current = 0;
        }

        let byte = self.current[self.yielded_in_current];
        self.yielded_in_current += 1;
        self.total_yielded += 1;
        Some(byte)
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.total_bytes - self.total_yielded;
        (remaining, Some(remaining))
    }
}

impl<'a> ExactSizeIterator for Bytes<'a> {}

/// TODO: docs
#[derive(Clone)]
pub struct Chars<'a> {
    chunks: Chunks<'a>,
    current: &'a str,
    /// Note: this is the number of *bytes* already yielded in `current`, not
    /// chars.
    yielded_in_current: usize,
}

impl<'a> From<&'a Rope> for Chars<'a> {
    #[inline]
    fn from(rope: &'a Rope) -> Self {
        let mut chunks = rope.chunks();
        let current = chunks.next().unwrap_or("");
        Self { chunks, current, yielded_in_current: 0 }
    }
}

impl<'a, 'b: 'a> From<&'a RopeSlice<'b>> for Chars<'a> {
    #[inline]
    fn from(slice: &'a RopeSlice<'b>) -> Self {
        let mut chunks = slice.chunks();
        let current = chunks.next().unwrap_or("");
        Self { chunks, current, yielded_in_current: 0 }
    }
}

impl<'a> Iterator for Chars<'a> {
    type Item = char;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.yielded_in_current == self.current.len() {
            // NOTE: make sure there are never empty chunks or this will make
            // the byte indexing below fail.
            self.current = self.chunks.next()?;
            self.yielded_in_current = 0;
        }

        let char = unsafe {
            self.current[self.yielded_in_current..]
                .chars()
                .next()
                // Safety: `yielded_in_current < current.len()`, so there are
                // still chars to yield in this chunk.
                .unwrap_unchecked()
        };
        self.yielded_in_current += char.len_utf8();
        Some(char)
    }
}

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

#[cfg(test)]
mod tests {
    use crate::Rope;

    const TINY: &str = include_str!("../../benches/tiny.txt");
    const SMALL: &str = include_str!("../../benches/small.txt");
    const MEDIUM: &str = include_str!("../../benches/medium.txt");
    const LARGE: &str = include_str!("../../benches/large.txt");

    #[test]
    fn bytes_0() {
        let r = Rope::from(LARGE);
        let mut i = 0;
        for (b_rope, b_str) in r.bytes().zip(LARGE.bytes()) {
            assert_eq!(b_rope, b_str);
            i += 1;
        }
        assert_eq!(i, r.byte_len());
    }

    #[test]
    fn bytes_1() {
        let r = Rope::from("Hello world this is my dog -> 🐕‍🦺");
        assert_eq!(41, r.bytes().count());
        assert_eq!(33, r.chars().count());
    }

    #[test]
    fn lines_1() {
        // Note: all these ropes should fit in a single chunk, no internal
        // nodes.

        let r = Rope::from("abc");
        assert_eq!(1, r.lines().count());
        assert_eq!(1, r.byte_slice(..).lines().count());

        let r = Rope::from("a\nb");
        assert_eq!(2, r.lines().count());
        assert_eq!(2, r.byte_slice(..).lines().count());

        let r = Rope::from("a\nb\n");
        assert_eq!(2, r.lines().count());
        assert_eq!(2, r.byte_slice(..).lines().count());

        let r = Rope::from("\n\n\n\n");
        assert_eq!(4, r.lines().count());
        assert_eq!(4, r.byte_slice(..).lines().count());

        let r = Rope::from("\n\n\n");
        assert_eq!(3, r.lines().count());
        assert_eq!(3, r.byte_slice(..).lines().count());

        let r = Rope::from("\n\n\na");
        assert_eq!(4, r.lines().count());
        assert_eq!(4, r.byte_slice(..).lines().count());
    }

    #[test]
    fn lines_2() {
        let s = "Donec ut suscipit risus. Vivamus dictum auctor \
                 vehicula\nurna tristique commodo. Sed sapien risus\nvelit.\n";

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
                 chunk\nand it also\r\nhas mixed\r\n line breaks\n and a \
                 trailing\nline break.\n";

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
}
