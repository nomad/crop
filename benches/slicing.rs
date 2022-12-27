use std::ops::Range;

use criterion::{criterion_group, criterion_main, Criterion};

const TINY: &str = include_str!("tiny.txt");
const SMALL: &str = include_str!("small.txt");
const MEDIUM: &str = include_str!("medium.txt");
const LARGE: &str = include_str!("large.txt");

trait Rope {
    type RopeSlice<'a>: Copy
    where
        Self: 'a;

    fn from_str(s: &str) -> Self;

    fn len(&self) -> usize;

    fn slice(&self, range: Range<usize>) -> Self::RopeSlice<'_>;

    fn from_slice(s: Self::RopeSlice<'_>) -> Self;
}

impl Rope for crop::Rope {
    type RopeSlice<'a> = crop::RopeSlice<'a>;

    #[inline]
    fn from_str(s: &str) -> Self {
        Self::from(s)
    }

    #[inline]
    fn len(&self) -> usize {
        self.byte_len()
    }

    #[inline]
    fn slice(&self, range: Range<usize>) -> Self::RopeSlice<'_> {
        self.byte_slice(range)
    }

    #[inline]
    fn from_slice(s: Self::RopeSlice<'_>) -> Self {
        Self::from(s)
    }
}

impl Rope for ropey::Rope {
    type RopeSlice<'a> = ropey::RopeSlice<'a>;

    #[inline]
    fn from_str(s: &str) -> Self {
        Self::from_str(s)
    }

    #[inline]
    fn len(&self) -> usize {
        self.len_chars()
    }

    #[inline]
    fn slice(&self, range: Range<usize>) -> Self::RopeSlice<'_> {
        self.slice(range)
    }

    #[inline]
    fn from_slice(s: Self::RopeSlice<'_>) -> Self {
        Self::from(s)
    }
}

struct SliceRanges {
    step: usize,
    start: usize,
    end: usize,
    done: bool,
}

impl SliceRanges {
    #[inline]
    fn new(max: usize) -> Self {
        let mut step = max / 200;
        if step == 0 {
            step = 1;
        }

        Self { step, start: 0, end: max, done: false }
    }
}

impl Iterator for SliceRanges {
    type Item = Range<usize>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.start > self.end {
            return None;
        }

        let range = self.start..self.end;

        self.start += self.step;
        self.end -= self.step;

        if self.start > self.end && !self.done {
            self.start = self.end;
            self.done = true;
        }

        Some(range)
    }
}

/// Benchmarks the creation of RopeSlices taken from a valid range in their
/// Rope.
#[inline]
fn bench_slicing<R: Rope>(c: &mut Criterion, group_name: &str) {
    #[inline]
    fn shrinking_slices<R: Rope>(r: &R) {
        for range in SliceRanges::new(r.len()) {
            let _ = r.slice(range);
        }
    }

    let mut group = c.benchmark_group(group_name);

    group.bench_function("tiny", |b| {
        let r = R::from_str(TINY);
        b.iter(|| shrinking_slices(&r))
    });

    group.bench_function("small", |b| {
        let r = R::from_str(SMALL);
        b.iter(|| shrinking_slices(&r))
    });

    group.bench_function("medium", |b| {
        let r = R::from_str(MEDIUM);
        b.iter(|| shrinking_slices(&r))
    });

    group.bench_function("large", |b| {
        let r = R::from_str(LARGE);
        b.iter(|| shrinking_slices(&r))
    });
}

/// Benchmarks the implementations of Rope::from_slice.
#[inline]
fn bench_from_slice<R: Rope>(c: &mut Criterion, group_name: &str) {
    let mut group = c.benchmark_group(group_name);

    #[inline]
    fn make_slices<R: Rope>(r: &R) -> Vec<R::RopeSlice<'_>> {
        SliceRanges::new(r.len()).map(|range| r.slice(range)).collect()
    }

    group.bench_function("tiny", |b| {
        let r = R::from_str(TINY);
        let slices = make_slices(&r);
        b.iter(|| {
            for slice in &slices {
                let _ = R::from_slice(*slice);
            }
        })
    });

    group.bench_function("small", |b| {
        let r = R::from_str(SMALL);
        let slices = make_slices(&r);
        b.iter(|| {
            for slice in &slices {
                let _ = R::from_slice(*slice);
            }
        })
    });

    group.bench_function("medium", |b| {
        let r = R::from_str(MEDIUM);
        let slices = make_slices(&r);
        b.iter(|| {
            for slice in &slices {
                let _ = R::from_slice(*slice);
            }
        })
    });

    group.bench_function("large", |b| {
        let r = R::from_str(LARGE);
        let slices = make_slices(&r);
        b.iter(|| {
            for slice in &slices {
                let _ = R::from_slice(*slice);
            }
        })
    });
}

#[inline]
fn crop_byte_slice(c: &mut Criterion) {
    bench_slicing::<crop::Rope>(c, "crop_byte_slice")
}

#[inline]
fn crop_from_slice(c: &mut Criterion) {
    bench_from_slice::<crop::Rope>(c, "crop_from_slice")
}

#[inline]
fn ropey_byte_slice(c: &mut Criterion) {
    bench_slicing::<ropey::Rope>(c, "ropey_byte_slice")
}

#[inline]
fn ropey_from_slice(c: &mut Criterion) {
    bench_from_slice::<ropey::Rope>(c, "ropey_from_slice")
}

criterion_group!(
    benches,
    crop_byte_slice,
    crop_from_slice,
    ropey_byte_slice,
    ropey_from_slice,
);
criterion_main!(benches);
