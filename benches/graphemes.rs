#![allow(dead_code)]

use criterion::{criterion_group, criterion_main, Criterion};
use crop::{iter::Graphemes, Rope};

mod iterators;

const TINY: &str = include_str!("../tests/common/tiny.txt");
const SMALL: &str = include_str!("../tests/common/small.txt");
const MEDIUM: &str = include_str!("../tests/common/medium.txt");
const LARGE: &str = include_str!("../tests/common/large.txt");

iter_bench!(iter_graphemes, Graphemes, "iter_graphemes");

criterion_group!(benches, iter_graphemes);
criterion_main!(benches);
