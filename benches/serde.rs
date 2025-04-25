mod common;

use common::{LARGE, MEDIUM, SMALL, TINY};
use criterion::measurement::WallTime;
use criterion::{
    BatchSize,
    BenchmarkGroup,
    BenchmarkId,
    Criterion,
    criterion_group,
    criterion_main,
};
use crop::Rope;

trait DataFormat {
    const GROUP_NAME: &str;

    type Serialized: Clone;

    fn serialize_rope(&self, rope: &Rope) -> Self::Serialized;

    fn deserialize_rope(&self, serialized: Self::Serialized) -> Rope;

    fn bench(&self, c: &mut Criterion) {
        let mut group = c.benchmark_group(Self::GROUP_NAME);
        self.bench_serialization(&mut group);
        self.bench_deserialization(&mut group);
        group.finish();
    }

    fn bench_serialization(&self, group: &mut BenchmarkGroup<'_, WallTime>) {
        for (rope, rope_name) in test_vectors() {
            let bench_id = BenchmarkId::new("ser", rope_name);
            group.bench_function(bench_id, |b| {
                b.iter(|| self.serialize_rope(&rope));
            });
        }
    }

    fn bench_deserialization(&self, group: &mut BenchmarkGroup<'_, WallTime>) {
        for (rope, rope_name) in test_vectors() {
            let serialized = self.serialize_rope(&rope);
            let bench_id = BenchmarkId::new("de", rope_name);
            group.bench_function(bench_id, |b| {
                let setup = || serialized.clone();
                let routine = |serialized| self.deserialize_rope(serialized);
                b.iter_batched(setup, routine, BatchSize::SmallInput);
            });
        }
    }
}

fn test_vectors() -> impl Iterator<Item = (Rope, &'static str)> {
    [
        (Rope::from(TINY), "tiny"),
        (Rope::from(SMALL), "small"),
        (Rope::from(MEDIUM), "medium"),
        (Rope::from(LARGE), "large"),
    ]
    .into_iter()
}

struct Json;

impl DataFormat for Json {
    const GROUP_NAME: &str = "serde_json";

    type Serialized = String;

    fn serialize_rope(&self, rope: &Rope) -> Self::Serialized {
        // serde_json::to_string(rope).unwrap()
        todo!();
    }

    fn deserialize_rope(&self, serialized: Self::Serialized) -> Rope {
        // serde_json::from_str(&serialized).unwrap()
        todo!();
    }
}

fn json(c: &mut Criterion) {
    Json.bench(c);
}

criterion_group!(benches, json);
criterion_main!(benches);
