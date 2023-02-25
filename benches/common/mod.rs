use std::ops::Range;

pub const TINY: &str = include_str!("../../tests/common/tiny.txt");
pub const SMALL: &str = include_str!("../../tests/common/small.txt");
pub const MEDIUM: &str = include_str!("../../tests/common/medium.txt");
pub const LARGE: &str = include_str!("../../tests/common/large.txt");

#[derive(Debug, Clone)]
pub struct PercentRanges {
    start: usize,
    end: usize,
    half_percent: usize,
}

impl PercentRanges {
    #[allow(dead_code)]
    #[inline(always)]
    pub fn new(max: usize) -> Self {
        Self { start: 0, end: max, half_percent: (max / 200).max(1) }
    }
}

impl Iterator for PercentRanges {
    type Item = Range<usize>;

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        if self.start == self.end {
            return None;
        }

        let range = self.start..self.end;

        self.end -= self.half_percent;

        self.start = std::cmp::min(self.start + self.half_percent, self.end);

        Some(range)
    }
}
