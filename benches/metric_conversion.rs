mod common;

use common::{LARGE, MEDIUM, SMALL, TINY};
use criterion::{criterion_group, criterion_main, Bencher, Criterion};
use crop::Rope;

fn line_of_byte(c: &mut Criterion) {
    #[inline(always)]
    fn bench(bench: &mut Bencher, s: &str) {
        let r = Rope::from(s);
        let mut byte_offsets = (0..=r.byte_len()).cycle();
        bench.iter(|| {
            let _ = r.line_of_byte(byte_offsets.next().unwrap());
        });
    }

    let mut group = c.benchmark_group("line_of_byte");

    group.bench_function("tiny", |b| bench(b, TINY));
    group.bench_function("small", |b| bench(b, SMALL));
    group.bench_function("medium", |b| bench(b, MEDIUM));
    group.bench_function("large", |b| bench(b, LARGE));
}

fn byte_of_line(c: &mut Criterion) {
    #[inline(always)]
    fn bench(bench: &mut Bencher, s: &str) {
        let r = Rope::from(s);
        let mut line_offsets = (0..=r.line_len()).cycle();
        bench.iter(|| {
            let _ = r.byte_of_line(line_offsets.next().unwrap());
        });
    }

    let mut group = c.benchmark_group("byte_of_line");

    group.bench_function("tiny", |b| bench(b, TINY));
    group.bench_function("small", |b| bench(b, SMALL));
    group.bench_function("medium", |b| bench(b, MEDIUM));
    group.bench_function("large", |b| bench(b, LARGE));
}

criterion_group!(benches, byte_of_line, line_of_byte);
criterion_main!(benches);
