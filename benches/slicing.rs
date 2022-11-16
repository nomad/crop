use criterion::{criterion_group, criterion_main, Criterion};
use crop::Rope;

const LARGE: &str = include_str!("large.txt");

fn byte_slice(c: &mut Criterion) {
    let mut group = c.benchmark_group("byte_slice");

    group.bench_function("large", |bench| {
        let r = Rope::from(LARGE);
        bench.iter(|| {
            let s = r.byte_slice(4389..17568);
            let _ = s.byte_slice(879..=9534);
        })
    });
}

criterion_group!(benches, byte_slice);
criterion_main!(benches);
