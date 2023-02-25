mod common;

use common::{LARGE, MEDIUM, SMALL, TINY};
use criterion::{criterion_group, criterion_main, Criterion};
use crop::{iter::Graphemes, Rope};

const TINY: &str = include_str!("../tests/common/tiny.txt");
const SMALL: &str = include_str!("../tests/common/small.txt");
const MEDIUM: &str = include_str!("../tests/common/medium.txt");
const LARGE: &str = include_str!("../tests/common/large.txt");

fn iter_graphemes(c: &mut Criterion) {
    let mut group = c.benchmark_group("iter_graphemes");

    group.bench_function("create", |bench| {
        let r = Rope::from(LARGE);
        bench.iter(|| {
            let _ = r.graphemes();
        })
    });

    group.bench_function("forward_tiny", |bench| {
        let r = Rope::from(TINY);
        let mut iter = r.graphemes().cycle();
        bench.iter(|| {
            let _ = iter.next();
        });
    });

    group.bench_function("forward_small", |bench| {
        let r = Rope::from(SMALL);
        let mut iter = r.graphemes().cycle();
        bench.iter(|| {
            let _ = iter.next();
        });
    });

    group.bench_function("forward_medium", |bench| {
        let r = Rope::from(MEDIUM);
        let mut iter = r.graphemes().cycle();
        bench.iter(|| {
            let _ = iter.next();
        });
    });

    group.bench_function("forward_large", |bench| {
        let r = Rope::from(LARGE);
        let mut iter = r.graphemes().cycle();
        bench.iter(|| {
            let _ = iter.next();
        });
    });

    group.bench_function("backward_tiny", |bench| {
        let r = Rope::from(TINY);
        let mut iter = r.graphemes().rev().cycle();
        bench.iter(|| {
            let _ = iter.next();
        });
    });

    group.bench_function("backward_small", |bench| {
        let r = Rope::from(SMALL);
        let mut iter = r.graphemes().rev().cycle();
        bench.iter(|| {
            let _ = iter.next();
        });
    });

    group.bench_function("backward_medium", |bench| {
        let r = Rope::from(MEDIUM);
        let mut iter = r.graphemes().rev().cycle();
        bench.iter(|| {
            let _ = iter.next();
        });
    });

    group.bench_function("backward_large", |bench| {
        let r = Rope::from(LARGE);
        let mut iter = r.graphemes().rev().cycle();
        bench.iter(|| {
            let _ = iter.next();
        });
    });
}

criterion_group!(benches, iter_graphemes);
criterion_main!(benches);
