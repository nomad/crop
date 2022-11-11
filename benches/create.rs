use criterion::{black_box, criterion_group, criterion_main, Criterion};
use crop::Rope;

const TINY: &str = include_str!("tiny.txt");
const MEDIUM: &str = include_str!("medium.txt");
const SMALL: &str = include_str!("small.txt");
const LARGE: &str = include_str!("large.txt");

fn from_str(c: &mut Criterion) {
    let mut group = c.benchmark_group("from_str");

    group.bench_function("tiny", |bench| {
        bench.iter(|| {
            let _ = Rope::from(black_box(TINY));
        })
    });

    group.bench_function("medium", |bench| {
        bench.iter(|| {
            let _ = Rope::from(black_box(MEDIUM));
        })
    });

    group.bench_function("small", |bench| {
        bench.iter(|| {
            let _ = Rope::from(black_box(SMALL));
        })
    });

    group.bench_function("large", |bench| {
        bench.iter(|| {
            let _ = Rope::from(black_box(LARGE));
        })
    });
}

criterion_group!(benches, from_str);
criterion_main!(benches);
