use criterion::{criterion_group, criterion_main, Criterion};
use crop::Rope;

const TINY: &str = include_str!("tiny.txt");
const LARGE: &str = include_str!("large.txt");

fn iter(c: &mut Criterion) {
    let mut group = c.benchmark_group("iter");

    group.bench_function("bytes", |bench| {
        let r = Rope::from(LARGE);
        let mut iter = r.bytes().cycle();
        bench.iter(|| {
            iter.next();
        })
    });

    group.bench_function("chars", |bench| {
        let r = Rope::from(LARGE);
        let mut iter = r.chars().cycle();
        bench.iter(|| {
            iter.next();
        })
    });
}

fn iter_lines_forward(c: &mut Criterion) {
    let mut group = c.benchmark_group("iter_lines_forward");

    group.bench_function("lines_tiny", |bench| {
        let r = Rope::from(TINY);
        let r = r.byte_slice(..);
        let mut iter = r.lines().cycle();
        bench.iter(|| {
            iter.next();
        })
    });

    group.bench_function("lines_large", |bench| {
        let r = Rope::from(LARGE);
        let r = r.byte_slice(..);
        let mut iter = r.lines().cycle();
        bench.iter(|| {
            iter.next();
        })
    });
}

criterion_group!(benches, iter, iter_lines_forward);
criterion_main!(benches);
