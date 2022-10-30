use super::Summarize;

pub trait Metric<T: Summarize> {
    fn measure(summary: &T::Summary) -> usize;

    fn to_base_units(x: usize) -> usize;

    fn from_base_units(x: usize) -> usize;
}
