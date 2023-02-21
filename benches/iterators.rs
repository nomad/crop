use criterion::{criterion_group, criterion_main, Criterion};
use crop::{iter::*, Rope};

const TINY: &str = include_str!("../tests/common/tiny.txt");
const SMALL: &str = include_str!("../tests/common/small.txt");
const MEDIUM: &str = include_str!("../tests/common/medium.txt");
const LARGE: &str = include_str!("../tests/common/large.txt");

#[macro_export]
macro_rules! iter_bench {
    ($fun:ident, $iterator:ty, $group_name:literal) => {
        fn $fun(c: &mut Criterion) {
            let mut group = c.benchmark_group($group_name);

            group.bench_function("create", |bench| {
                let r = Rope::from(LARGE);
                bench.iter(|| {
                    let _ = <$iterator>::from(&r);
                })
            });

            group.bench_function("forward_tiny", |bench| {
                let r = Rope::from(TINY);
                let mut iter = <$iterator>::from(&r).cycle();
                bench.iter(|| {
                    let _ = iter.next();
                });
            });

            group.bench_function("forward_small", |bench| {
                let r = Rope::from(SMALL);
                let mut iter = <$iterator>::from(&r).cycle();
                bench.iter(|| {
                    let _ = iter.next();
                });
            });

            group.bench_function("forward_medium", |bench| {
                let r = Rope::from(MEDIUM);
                let mut iter = <$iterator>::from(&r).cycle();
                bench.iter(|| {
                    let _ = iter.next();
                });
            });

            group.bench_function("forward_large", |bench| {
                let r = Rope::from(LARGE);
                let mut iter = <$iterator>::from(&r).cycle();
                bench.iter(|| {
                    let _ = iter.next();
                });
            });

            group.bench_function("backward_tiny", |bench| {
                let r = Rope::from(TINY);
                let mut iter = <$iterator>::from(&r).rev().cycle();
                bench.iter(|| {
                    let _ = iter.next();
                });
            });

            group.bench_function("backward_small", |bench| {
                let r = Rope::from(SMALL);
                let mut iter = <$iterator>::from(&r).rev().cycle();
                bench.iter(|| {
                    let _ = iter.next();
                });
            });

            group.bench_function("backward_medium", |bench| {
                let r = Rope::from(MEDIUM);
                let mut iter = <$iterator>::from(&r).rev().cycle();
                bench.iter(|| {
                    let _ = iter.next();
                });
            });

            group.bench_function("backward_large", |bench| {
                let r = Rope::from(LARGE);
                let mut iter = <$iterator>::from(&r).rev().cycle();
                bench.iter(|| {
                    let _ = iter.next();
                });
            });
        }
    };
}

iter_bench!(chunks, Chunks, "iter_chunks");
iter_bench!(bytes, Bytes, "iter_bytes");
iter_bench!(chars, Chars, "iter_chars");
iter_bench!(lines, Lines, "iter_lines");
iter_bench!(raw_lines, RawLines, "iter_raw_lines");

criterion_group!(benches, chunks, bytes, chars, lines, raw_lines);
criterion_main!(benches);
