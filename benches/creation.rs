use criterion::{black_box, criterion_group, criterion_main, Criterion};

const TINY: &str = include_str!("tiny.txt");
const SMALL: &str = include_str!("small.txt");
const MEDIUM: &str = include_str!("medium.txt");
const LARGE: &str = include_str!("large.txt");

trait Rope {
    fn from_str(s: &str) -> Self;
}

trait RopeBuilder {
    type Rope: Rope;

    fn new() -> Self;

    fn append(self, s: &str) -> Self;

    fn build(self) -> Self::Rope;
}

impl Rope for crop::Rope {
    #[inline]
    fn from_str(s: &str) -> Self {
        Self::from(s)
    }
}

impl Rope for ropey::Rope {
    #[inline]
    fn from_str(s: &str) -> Self {
        Self::from_str(s)
    }
}

impl Rope for xi_rope::Rope {
    #[inline]
    fn from_str(s: &str) -> Self {
        Self::from(s)
    }
}

impl RopeBuilder for crop::RopeBuilder {
    type Rope = crop::Rope;

    #[inline]
    fn new() -> Self {
        crop::RopeBuilder::new()
    }

    #[inline]
    fn append(self, s: &str) -> Self {
        crop::RopeBuilder::append(self, s)
    }

    #[inline]
    fn build(self) -> Self::Rope {
        self.build()
    }
}

impl RopeBuilder for ropey::RopeBuilder {
    type Rope = ropey::Rope;

    #[inline]
    fn new() -> Self {
        ropey::RopeBuilder::new()
    }

    #[inline]
    fn append(mut self, s: &str) -> Self {
        ropey::RopeBuilder::append(&mut self, s);
        self
    }

    #[inline]
    fn build(self) -> Self::Rope {
        self.finish()
    }
}

type XiRopeBuilder = xi_rope::tree::TreeBuilder<xi_rope::RopeInfo>;

impl RopeBuilder for XiRopeBuilder {
    type Rope = xi_rope::Rope;

    #[inline]
    fn new() -> Self {
        XiRopeBuilder::new()
    }

    #[inline]
    fn append(mut self, s: &str) -> Self {
        self.push_str(s);
        self
    }

    #[inline]
    fn build(self) -> Self::Rope {
        self.build()
    }
}

#[inline]
fn bench(c: &mut Criterion, fun: fn(&str), group_name: &str) {
    let mut group = c.benchmark_group(group_name);

    group.bench_function("tiny", |b| b.iter(|| fun(TINY)));
    group.bench_function("small", |b| b.iter(|| fun(SMALL)));
    group.bench_function("medium", |b| b.iter(|| fun(MEDIUM)));
    group.bench_function("large", |b| b.iter(|| fun(LARGE)));
}

#[inline]
fn from_str<R: Rope>(s: &str) {
    let _ = R::from_str(black_box(s));
}

#[inline]
fn rope_builder<B: RopeBuilder>(s: &str) {
    let mut b = B::new();
    for line in s.lines() {
        b = b.append(line);
    }
    let _ = b.build();
}

#[inline]
fn crop_from_str(c: &mut Criterion) {
    bench(c, from_str::<crop::Rope>, "crop_from_str");
}

#[inline]
fn ropey_from_str(c: &mut Criterion) {
    bench(c, from_str::<ropey::Rope>, "ropey_from_str");
}

#[inline]
fn xi_rope_from_str(c: &mut Criterion) {
    bench(c, from_str::<xi_rope::Rope>, "xi_rope_from_str");
}

#[inline]
fn crop_builder(c: &mut Criterion) {
    bench(c, rope_builder::<crop::RopeBuilder>, "crop_builder");
}

#[inline]
fn ropey_builder(c: &mut Criterion) {
    bench(c, rope_builder::<ropey::RopeBuilder>, "ropey_builder");
}

#[inline]
fn xi_rope_builder(c: &mut Criterion) {
    bench(c, rope_builder::<XiRopeBuilder>, "xi_rope_builder");
}

criterion_group!(
    benches,
    crop_from_str,
    ropey_from_str,
    xi_rope_from_str,
    crop_builder,
    ropey_builder,
    xi_rope_builder
);

criterion_main!(benches);
