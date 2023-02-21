use criterion::measurement::WallTime;
use criterion::{criterion_group, criterion_main, BenchmarkGroup, Criterion};
use crop::Rope;
use rand::Rng;

const TINY: &str = include_str!("../tests/common/tiny.txt");
const SMALL: &str = include_str!("../tests/common/small.txt");
const MEDIUM: &str = include_str!("../tests/common/medium.txt");
const LARGE: &str = include_str!("../tests/common/large.txt");

fn bench_insert(group: &mut BenchmarkGroup<WallTime>, insert: &str) {
    group.bench_function("tiny", |bench| {
        let mut rng = rand::thread_rng();
        let mut r = Rope::from(TINY);
        bench.iter(|| {
            let at = rng.gen_range(0..=r.byte_len());
            r.insert(at, insert);
        });
    });

    group.bench_function("small", |bench| {
        let mut rng = rand::thread_rng();
        let mut r = Rope::from(SMALL);
        bench.iter(|| {
            let at = rng.gen_range(0..=r.byte_len());
            r.insert(at, insert);
        });
    });

    group.bench_function("medium", |bench| {
        let mut rng = rand::thread_rng();
        let mut r = Rope::from(MEDIUM);
        bench.iter(|| {
            let at = rng.gen_range(0..=r.byte_len());
            r.insert(at, insert);
        });
    });

    group.bench_function("large", |bench| {
        let mut rng = rand::thread_rng();
        let mut r = Rope::from(LARGE);
        bench.iter(|| {
            let at = rng.gen_range(0..=r.byte_len());
            r.insert(at, insert);
        });
    });
}

fn insert_char(c: &mut Criterion) {
    let mut group = c.benchmark_group("insert_char");
    bench_insert(&mut group, "a");
}

fn insert_sentence(c: &mut Criterion) {
    let mut group = c.benchmark_group("insert_sentence");
    bench_insert(
        &mut group,
        "Lorem ipsum dolor sit amet, consectetur adipiscing elit.",
    );
}

fn insert_large(c: &mut Criterion) {
    let mut group = c.benchmark_group("insert_large");
    bench_insert(&mut group, SMALL);
}

fn insert_char_with_clone_around(c: &mut Criterion) {
    let mut group = c.benchmark_group("insert_char_with_clone_around");

    group.bench_function("large", |bench| {
        let mut rng = rand::thread_rng();
        let mut r = Rope::from(LARGE);
        let orig = r.clone();
        let mut insertions = 0;
        bench.iter(|| {
            let at = rng.gen_range(0..=r.byte_len());
            r.insert(at, "a");
            insertions += 1;
            if insertions == 64 {
                insertions = 0;
                r = orig.clone();
            }
        })
    });
}

fn bench_delete(group: &mut BenchmarkGroup<WallTime>, delete_bytes: usize) {
    group.bench_function("tiny", |bench| {
        let mut rng = rand::thread_rng();
        let mut r = Rope::from(TINY);
        let orig_len = r.byte_len();
        bench.iter(|| {
            let len = r.byte_len();
            let start = rng.gen_range(0..=len);
            let end = (start + delete_bytes).min(len);
            r.delete(start..end);

            if r.byte_len() < orig_len / 4 {
                r = Rope::from(TINY);
            }
        });
    });

    group.bench_function("small", |bench| {
        let mut rng = rand::thread_rng();
        let mut r = Rope::from(SMALL);
        let orig_len = r.byte_len();
        bench.iter(|| {
            let len = r.byte_len();
            let start = rng.gen_range(0..=len);
            let end = (start + delete_bytes).min(len);
            r.delete(start..end);

            if r.byte_len() < orig_len / 4 {
                r = Rope::from(SMALL);
            }
        });
    });

    group.bench_function("medium", |bench| {
        let mut rng = rand::thread_rng();
        let mut r = Rope::from(MEDIUM);
        let orig_len = r.byte_len();
        bench.iter(|| {
            let len = r.byte_len();
            let start = rng.gen_range(0..=len);
            let end = (start + delete_bytes).min(len);
            r.delete(start..end);

            if r.byte_len() < orig_len / 4 {
                r = Rope::from(MEDIUM);
            }
        });
    });

    group.bench_function("large", |bench| {
        let mut rng = rand::thread_rng();
        let mut r = Rope::from(LARGE);
        let orig_len = r.byte_len();
        bench.iter(|| {
            let len = r.byte_len();
            let start = rng.gen_range(0..=len);
            let end = (start + delete_bytes).min(len);
            r.delete(start..end);

            if r.byte_len() < orig_len / 4 {
                r = Rope::from(TINY);
            }
        });
    });
}

fn delete_char(c: &mut Criterion) {
    let mut group = c.benchmark_group("delete_char");
    bench_delete(&mut group, "a".len());
}

fn delete_sentence(c: &mut Criterion) {
    let mut group = c.benchmark_group("delete_sentence");
    bench_delete(
        &mut group,
        "Lorem ipsum dolor sit amet, consectetur adipiscing elit.".len(),
    );
}

fn delete_large(c: &mut Criterion) {
    let mut group = c.benchmark_group("delete_large");
    bench_delete(&mut group, SMALL.len());
}

fn delete_char_with_clone_around(c: &mut Criterion) {
    let mut group = c.benchmark_group("delete_char_with_clone_around");

    group.bench_function("large", |bench| {
        let mut rng = rand::thread_rng();
        let mut r = Rope::from(LARGE);
        let orig = r.clone();
        let mut deletions = 0;
        bench.iter(|| {
            let len = r.byte_len();
            let start = rng.gen_range(0..=len);
            let end = (start + 1).min(len);
            r.delete(start..end);
            deletions += 1;
            if deletions == 64 {
                deletions = 0;
                r = orig.clone();
            }
        })
    });
}

fn bench_replace(group: &mut BenchmarkGroup<WallTime>, replace: &str) {
    group.bench_function("tiny", |bench| {
        let mut rng = rand::thread_rng();
        let mut r = Rope::from(TINY);
        bench.iter(|| {
            let len = r.byte_len();
            let start = rng.gen_range(0..=len);
            let end = (start + replace.len()).min(len);
            r.replace(start..end, replace);
        });
    });

    group.bench_function("small", |bench| {
        let mut rng = rand::thread_rng();
        let mut r = Rope::from(SMALL);
        bench.iter(|| {
            let len = r.byte_len();
            let start = rng.gen_range(0..=len);
            let end = (start + replace.len()).min(len);
            r.replace(start..end, replace);
        });
    });

    group.bench_function("medium", |bench| {
        let mut rng = rand::thread_rng();
        let mut r = Rope::from(MEDIUM);
        bench.iter(|| {
            let len = r.byte_len();
            let start = rng.gen_range(0..=len);
            let end = (start + replace.len()).min(len);
            r.replace(start..end, replace);
        });
    });

    group.bench_function("large", |bench| {
        let mut rng = rand::thread_rng();
        let mut r = Rope::from(LARGE);
        bench.iter(|| {
            let len = r.byte_len();
            let start = rng.gen_range(0..=len);
            let end = (start + replace.len()).min(len);
            r.replace(start..end, replace);
        });
    });
}

fn replace_char(c: &mut Criterion) {
    let mut group = c.benchmark_group("replace_char");
    bench_replace(&mut group, "a");
}

fn replace_sentence(c: &mut Criterion) {
    let mut group = c.benchmark_group("replace_sentence");
    bench_replace(
        &mut group,
        "Lorem ipsum dolor sit amet, consectetur adipiscing elit.",
    );
}

fn replace_large(c: &mut Criterion) {
    let mut group = c.benchmark_group("replace_large");
    bench_replace(&mut group, SMALL);
}

criterion_group!(
    benches,
    insert_char,
    insert_sentence,
    insert_large,
    insert_char_with_clone_around,
    delete_char,
    delete_sentence,
    delete_large,
    delete_char_with_clone_around,
    replace_char,
    replace_sentence,
    replace_large,
);

criterion_main!(benches);
