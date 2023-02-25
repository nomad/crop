mod common;

use common::{PercentRanges, LARGE, MEDIUM, SMALL, TINY};
use criterion::measurement::WallTime;
use criterion::{
    criterion_group,
    criterion_main,
    Bencher,
    BenchmarkGroup,
    Criterion,
};
use crop::Rope;

fn bench_insert(group: &mut BenchmarkGroup<WallTime>, insert: &str) {
    #[inline(always)]
    fn bench(bench: &mut Bencher, s: &str, insert: &str) {
        let mut r = Rope::from(s);
        let mut ranges = PercentRanges::new(r.byte_len()).cycle();
        let mut i = 0;
        bench.iter(|| {
            let range = ranges.next().unwrap();
            let at = if i % 2 == 0 { range.start } else { range.end };
            r.insert(at, insert);
            i += 1;
        });
    }

    group.bench_function("tiny", |b| bench(b, TINY, insert));
    group.bench_function("small", |b| bench(b, SMALL, insert));
    group.bench_function("medium", |b| bench(b, MEDIUM, insert));
    group.bench_function("large", |b| bench(b, LARGE, insert));
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
        let mut r = Rope::from(LARGE);
        let mut ranges = PercentRanges::new(r.byte_len()).cycle();
        let orig = r.clone();
        let mut insertions = 0;
        bench.iter(|| {
            let range = ranges.next().unwrap();
            let at = if insertions % 2 == 0 { range.start } else { range.end };
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
    #[inline(always)]
    fn bench(bench: &mut Bencher, s: &str, delete_bytes: usize) {
        let mut r = Rope::from(s);
        let mut ranges = PercentRanges::new(r.byte_len()).cycle();
        let mut i = 0;
        let orig_len = r.byte_len();
        bench.iter(|| {
            let range = ranges.next().unwrap();
            let start = (if i % 2 == 0 { range.start } else { range.end })
                .min(r.byte_len());
            let end = (start + delete_bytes).min(r.byte_len());
            r.delete(start..end);
            i += 1;

            if r.byte_len() < orig_len / 4 {
                r = Rope::from(s);
                ranges = PercentRanges::new(r.byte_len()).cycle();
            }
        });
    }

    group.bench_function("tiny", |b| bench(b, TINY, delete_bytes));
    group.bench_function("small", |b| bench(b, SMALL, delete_bytes));
    group.bench_function("medium", |b| bench(b, MEDIUM, delete_bytes));
    group.bench_function("large", |b| bench(b, LARGE, delete_bytes));
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
        let mut r = Rope::from(LARGE);
        let mut ranges = PercentRanges::new(r.byte_len()).cycle();
        let orig = r.clone();
        let mut deletions = 0;
        bench.iter(|| {
            let range = ranges.next().unwrap();
            let start =
                (if deletions % 2 == 0 { range.start } else { range.end })
                    .min(r.byte_len());
            let end = (start + 1).min(r.byte_len());
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
    #[inline(always)]
    fn bench(bench: &mut Bencher, s: &str, replace: &str) {
        let mut r = Rope::from(s);
        let mut ranges = PercentRanges::new(r.byte_len()).cycle();
        let mut i = 0;
        bench.iter(|| {
            let range = ranges.next().unwrap();
            let start = if i % 2 == 0 { range.start } else { range.end };
            let end = (start + replace.len()).min(r.byte_len());
            r.replace(start..end, replace);
            i += 1;
        });
    }

    group.bench_function("tiny", |b| bench(b, TINY, replace));
    group.bench_function("small", |b| bench(b, SMALL, replace));
    group.bench_function("medium", |b| bench(b, MEDIUM, replace));
    group.bench_function("large", |b| bench(b, LARGE, replace));
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
