use criterion::{criterion_group, criterion_main, Criterion};
use crop::Rope;

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

criterion_group!(benches, iter);
criterion_main!(benches);
