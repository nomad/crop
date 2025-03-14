mod common;

use common::{LARGE, MEDIUM, SMALL, TINY};
use criterion::{criterion_group, criterion_main, Criterion};
use crop::Rope;

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
