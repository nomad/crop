mod common;

use common::{LARGE, MEDIUM, PercentRanges, SMALL, TINY};
use criterion::{
    BatchSize,
    Bencher,
    Criterion,
    criterion_group,
    criterion_main,
};
use crop::Rope;

fn byte_slice(c: &mut Criterion) {
    #[inline(always)]
    fn bench(bench: &mut Bencher, s: &str) {
        let r = Rope::from(s);
        let mut ranges = PercentRanges::new(r.byte_len()).cycle();
        let setup = || ranges.next().unwrap();
        let routine = |range| r.byte_slice(range);
        bench.iter_batched(setup, routine, BatchSize::SmallInput);
    }

    let mut group = c.benchmark_group("byte_slice");

    group.bench_function("tiny", |b| bench(b, TINY));
    group.bench_function("small", |b| bench(b, SMALL));
    group.bench_function("medium", |b| bench(b, MEDIUM));
    group.bench_function("large", |b| bench(b, LARGE));
}

fn line_slice(c: &mut Criterion) {
    #[inline(always)]
    fn bench(bench: &mut Bencher, s: &str) {
        let r = Rope::from(s);
        let mut ranges = PercentRanges::new(r.line_len()).cycle();
        let setup = || ranges.next().unwrap();
        let routine = |range| r.line_slice(range);
        bench.iter_batched(setup, routine, BatchSize::SmallInput);
    }

    let mut group = c.benchmark_group("line_slice");

    group.bench_function("tiny", |b| bench(b, TINY));
    group.bench_function("small", |b| bench(b, SMALL));
    group.bench_function("medium", |b| bench(b, MEDIUM));
    group.bench_function("large", |b| bench(b, LARGE));
}

fn rope_from_slice(c: &mut Criterion) {
    #[inline(always)]
    fn bench(bench: &mut Bencher, s: &str) {
        let r = Rope::from(s);
        let mut ranges = PercentRanges::new(r.byte_len()).cycle();
        let setup = || {
            let range = ranges.next().unwrap();
            r.byte_slice(range)
        };
        let routine = Rope::from;
        bench.iter_batched(setup, routine, BatchSize::SmallInput);
    }

    let mut group = c.benchmark_group("rope_from_slice");

    group.bench_function("tiny", |b| bench(b, TINY));
    group.bench_function("small", |b| bench(b, SMALL));
    group.bench_function("medium", |b| bench(b, MEDIUM));
    group.bench_function("large", |b| bench(b, LARGE));
}

criterion_group!(benches, byte_slice, line_slice, rope_from_slice);
criterion_main!(benches);
