use super::{TextChunk, TextSummary};
use crate::tree::Metric;

pub struct ByteMetric {}

impl Metric<TextChunk> for ByteMetric {
    fn measure(summary: &TextSummary) -> usize {
        summary.bytes
    }

    fn to_base_units(x: usize) -> usize {
        todo!()
    }

    fn from_base_units(x: usize) -> usize {
        todo!()
    }
}
