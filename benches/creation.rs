use criterion::measurement::WallTime;
use criterion::{criterion_group, criterion_main, BenchmarkGroup, Criterion};
use crop::{Rope, RopeBuilder};

const TINY: &str = include_str!("../tests/common/tiny.txt");
const SMALL: &str = include_str!("../tests/common/small.txt");
const MEDIUM: &str = include_str!("../tests/common/medium.txt");
const LARGE: &str = include_str!("../tests/common/large.txt");

fn bench<F: Fn(&str)>(group: &mut BenchmarkGroup<WallTime>, to_bench: F) {
    group.bench_function("tiny", |bench| bench.iter(|| to_bench(TINY)));
    group.bench_function("small", |bench| bench.iter(|| to_bench(SMALL)));
    group.bench_function("medium", |bench| bench.iter(|| to_bench(MEDIUM)));
    group.bench_function("large", |bench| bench.iter(|| to_bench(LARGE)));
}

fn from_str(c: &mut Criterion) {
    let mut group = c.benchmark_group("from_str");

    bench(&mut group, |s| {
        let _ = Rope::from(s);
    });
}

fn rope_builder(c: &mut Criterion) {
    let mut group = c.benchmark_group("rope_builder");

    bench(&mut group, |s| {
        let mut builder = RopeBuilder::new();
        for line in s.lines() {
            builder.append(line);
        }
        let _ = builder.build();
    });
}

criterion_group!(benches, from_str, rope_builder);
criterion_main!(benches);
