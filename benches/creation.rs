mod common;

use common::{LARGE, MEDIUM, SMALL, TINY};
use criterion::measurement::WallTime;
use criterion::{BenchmarkGroup, Criterion, criterion_group, criterion_main};
use crop::{Rope, RopeBuilder};

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
