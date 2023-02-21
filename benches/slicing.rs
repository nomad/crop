use criterion::{criterion_group, criterion_main, BatchSize, Criterion};
use crop::Rope;
use rand::{rngs::ThreadRng, Rng};

const TINY: &str = include_str!("../tests/common/tiny.txt");
const SMALL: &str = include_str!("../tests/common/small.txt");
const MEDIUM: &str = include_str!("../tests/common/medium.txt");
const LARGE: &str = include_str!("../tests/common/large.txt");

fn byte_slice(c: &mut Criterion) {
    let mut group = c.benchmark_group("byte_slice");

    let random_byte_range = |rng: &mut ThreadRng, r: &Rope| {
        let start = rng.gen_range(0..=r.byte_len());
        let end = rng.gen_range(start..=r.byte_len());
        start..end
    };

    group.bench_function("tiny", |bench| {
        let mut rng = rand::thread_rng();
        let r = Rope::from(TINY);
        let setup = || random_byte_range(&mut rng, &r);
        let routine = |range| r.byte_slice(range);
        bench.iter_batched(setup, routine, BatchSize::SmallInput);
    });

    group.bench_function("small", |bench| {
        let mut rng = rand::thread_rng();
        let r = Rope::from(SMALL);
        let setup = || random_byte_range(&mut rng, &r);
        let routine = |range| r.byte_slice(range);
        bench.iter_batched(setup, routine, BatchSize::SmallInput);
    });

    group.bench_function("medium", |bench| {
        let mut rng = rand::thread_rng();
        let r = Rope::from(MEDIUM);
        let setup = || random_byte_range(&mut rng, &r);
        let routine = |range| r.byte_slice(range);
        bench.iter_batched(setup, routine, BatchSize::SmallInput);
    });

    group.bench_function("large", |bench| {
        let mut rng = rand::thread_rng();
        let r = Rope::from(LARGE);
        let setup = || random_byte_range(&mut rng, &r);
        let routine = |range| r.byte_slice(range);
        bench.iter_batched(setup, routine, BatchSize::SmallInput);
    });
}

fn line_slice(c: &mut Criterion) {
    let mut group = c.benchmark_group("line_slice");

    let random_line_range = |rng: &mut ThreadRng, r: &Rope| {
        let start = rng.gen_range(0..=r.line_len());
        let end = rng.gen_range(start..=r.line_len());
        start..end
    };

    group.bench_function("tiny", |bench| {
        let mut rng = rand::thread_rng();
        let r = Rope::from(TINY);
        let setup = || random_line_range(&mut rng, &r);
        let routine = |range| r.line_slice(range);
        bench.iter_batched(setup, routine, BatchSize::SmallInput);
    });

    group.bench_function("small", |bench| {
        let mut rng = rand::thread_rng();
        let r = Rope::from(SMALL);
        let setup = || random_line_range(&mut rng, &r);
        let routine = |range| r.line_slice(range);
        bench.iter_batched(setup, routine, BatchSize::SmallInput);
    });

    group.bench_function("medium", |bench| {
        let mut rng = rand::thread_rng();
        let r = Rope::from(MEDIUM);
        let setup = || random_line_range(&mut rng, &r);
        let routine = |range| r.line_slice(range);
        bench.iter_batched(setup, routine, BatchSize::SmallInput);
    });

    group.bench_function("large", |bench| {
        let mut rng = rand::thread_rng();
        let r = Rope::from(LARGE);
        let setup = || random_line_range(&mut rng, &r);
        let routine = |range| r.line_slice(range);
        bench.iter_batched(setup, routine, BatchSize::SmallInput);
    });
}

fn rope_from_slice(c: &mut Criterion) {
    let mut group = c.benchmark_group("rope_from_slice");

    let random_byte_range = |rng: &mut ThreadRng, r: &Rope| {
        let start = rng.gen_range(0..=r.byte_len());
        let end = rng.gen_range(start..=r.byte_len());
        start..end
    };

    group.bench_function("tiny", |bench| {
        let mut rng = rand::thread_rng();
        let r = Rope::from(TINY);
        let setup = || {
            let range = random_byte_range(&mut rng, &r);
            r.byte_slice(range)
        };
        let routine = Rope::from;
        bench.iter_batched(setup, routine, BatchSize::SmallInput);
    });

    group.bench_function("small", |bench| {
        let mut rng = rand::thread_rng();
        let r = Rope::from(SMALL);
        let setup = || {
            let range = random_byte_range(&mut rng, &r);
            r.byte_slice(range)
        };
        let routine = Rope::from;
        bench.iter_batched(setup, routine, BatchSize::SmallInput);
    });

    group.bench_function("medium", |bench| {
        let mut rng = rand::thread_rng();
        let r = Rope::from(MEDIUM);
        let setup = || {
            let range = random_byte_range(&mut rng, &r);
            r.byte_slice(range)
        };
        let routine = Rope::from;
        bench.iter_batched(setup, routine, BatchSize::SmallInput);
    });

    group.bench_function("large", |bench| {
        let mut rng = rand::thread_rng();
        let r = Rope::from(LARGE);
        let setup = || {
            let range = random_byte_range(&mut rng, &r);
            r.byte_slice(range)
        };
        let routine = Rope::from;
        bench.iter_batched(setup, routine, BatchSize::SmallInput);
    });
}

criterion_group!(benches, byte_slice, line_slice, rope_from_slice);
criterion_main!(benches);
