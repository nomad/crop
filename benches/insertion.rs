use criterion::{criterion_group, criterion_main, Criterion};
use rand::random;

const TINY: &str = include_str!("tiny.txt");
const SMALL: &str = include_str!("small.txt");
const MEDIUM: &str = include_str!("medium.txt");
const LARGE: &str = include_str!("large.txt");

trait Rope {
    fn from_str(s: &str) -> Self;

    fn len(&self) -> usize;

    fn insert(&mut self, text: &str, at_offset: usize);
}

impl Rope for crop::Rope {
    #[inline]
    fn from_str(s: &str) -> Self {
        Self::from(s)
    }

    #[inline]
    fn len(&self) -> usize {
        self.byte_len()
    }

    #[inline]
    fn insert(&mut self, text: &str, at_offset: usize) {
        crop::Rope::insert(self, at_offset, text)
    }
}

impl Rope for ropey::Rope {
    #[inline]
    fn from_str(s: &str) -> Self {
        Self::from_str(s)
    }

    #[inline]
    fn len(&self) -> usize {
        self.len_chars()
    }

    #[inline]
    fn insert(&mut self, text: &str, at_offset: usize) {
        ropey::Rope::insert(self, at_offset, text)
    }
}

impl Rope for xi_rope::Rope {
    #[inline]
    fn from_str(s: &str) -> Self {
        Self::from(s)
    }

    #[inline]
    fn len(&self) -> usize {
        self.len()
    }

    #[inline]
    fn insert(&mut self, text: &str, at_offset: usize) {
        self.edit(at_offset..at_offset, text);
    }
}

#[inline]
fn bench<R: Rope>(c: &mut Criterion, fun: fn(&mut R), group_name: &str) {
    let mut group = c.benchmark_group(group_name);

    group.bench_function("tiny", |b| {
        let mut r = R::from_str(TINY);
        b.iter(|| fun(&mut r))
    });

    group.bench_function("small", |b| {
        let mut r = R::from_str(SMALL);
        b.iter(|| fun(&mut r))
    });

    group.bench_function("medium", |b| {
        let mut r = R::from_str(MEDIUM);
        b.iter(|| fun(&mut r))
    });

    group.bench_function("large", |b| {
        let mut r = R::from_str(LARGE);
        b.iter(|| fun(&mut r))
    });
}

#[inline]
fn insert_at_random<R: Rope>(r: &mut R, text: &str) {
    let offset = random::<usize>() % (r.len() + 1);
    r.insert(text, offset);
}

#[inline]
fn insert_char_at_random<R: Rope>(r: &mut R) {
    insert_at_random(r, "a");
}

#[inline]
fn insert_sentence_at_random<R: Rope>(r: &mut R) {
    insert_at_random(r, "Lorem ipsum dolor sit amet.");
}

#[inline]
fn insert_paragraphs_at_random<R: Rope>(r: &mut R) {
    insert_at_random(r, SMALL);
}

#[inline]
fn crop_insert_char_at_random(c: &mut Criterion) {
    bench(
        c,
        insert_char_at_random::<crop::Rope>,
        "crop_insert_char_at_random",
    );
}

#[inline]
fn ropey_insert_char_at_random(c: &mut Criterion) {
    bench(
        c,
        insert_char_at_random::<ropey::Rope>,
        "ropey_insert_char_at_random",
    );
}

#[inline]
fn xi_rope_insert_char_at_random(c: &mut Criterion) {
    bench(
        c,
        insert_char_at_random::<xi_rope::Rope>,
        "xi_rope_insert_char_at_random",
    );
}

#[inline]
fn crop_insert_sentence_at_random(c: &mut Criterion) {
    bench(
        c,
        insert_sentence_at_random::<crop::Rope>,
        "crop_insert_sentence_at_random",
    );
}

#[inline]
fn ropey_insert_sentence_at_random(c: &mut Criterion) {
    bench(
        c,
        insert_sentence_at_random::<ropey::Rope>,
        "ropey_insert_sentence_at_random",
    );
}

#[inline]
fn xi_rope_insert_sentence_at_random(c: &mut Criterion) {
    bench(
        c,
        insert_sentence_at_random::<xi_rope::Rope>,
        "xi_rope_insert_sentence_at_random",
    );
}

#[inline]
fn crop_insert_paragraphs_at_random(c: &mut Criterion) {
    bench(
        c,
        insert_paragraphs_at_random::<crop::Rope>,
        "crop_insert_paragraphs_at_random",
    );
}

#[inline]
fn ropey_insert_paragraphs_at_random(c: &mut Criterion) {
    bench(
        c,
        insert_paragraphs_at_random::<ropey::Rope>,
        "ropey_insert_paragraphs_at_random",
    );
}

#[inline]
fn xi_rope_insert_paragraphs_at_random(c: &mut Criterion) {
    bench(
        c,
        insert_paragraphs_at_random::<xi_rope::Rope>,
        "xi_rope_insert_paragraphs_at_random",
    );
}

criterion_group!(
    benches,
    crop_insert_char_at_random,
    ropey_insert_char_at_random,
    xi_rope_insert_char_at_random,
    crop_insert_sentence_at_random,
    ropey_insert_sentence_at_random,
    xi_rope_insert_sentence_at_random,
    crop_insert_paragraphs_at_random,
    ropey_insert_paragraphs_at_random,
    xi_rope_insert_paragraphs_at_random,
);

criterion_main!(benches);
