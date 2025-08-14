use core::fmt::Debug;
use core::ops::{Add, AddAssign, RangeBounds, Sub, SubAssign};

pub trait Summary: Debug + Clone + AddAssign + SubAssign {
    /// The leaf type this summary is for.
    type Leaf: Leaf<Summary = Self> + ?Sized;

    fn empty() -> Self;

    #[inline]
    fn base_measure(&self) -> <Self::Leaf as Leaf>::BaseMetric {
        self.measure()
    }

    #[inline]
    fn is_empty(&self) -> bool {
        self.base_measure().is_zero()
    }

    #[inline]
    fn measure<M: Metric<Self>>(&self) -> M {
        M::measure(self)
    }
}

pub trait Leaf: Debug {
    type BaseMetric: Metric<Self::Summary>;

    type Slice<'a>: LeafSlice<'a, Leaf = Self>
    where
        Self: 'a;

    type Summary: Summary<Leaf = Self>;

    fn as_slice(&self) -> Self::Slice<'_>;

    fn summarize(&self) -> Self::Summary;

    #[inline]
    fn base_measure(&self) -> Self::BaseMetric {
        self.measure::<Self::BaseMetric>()
    }

    #[inline]
    fn is_empty(&self) -> bool {
        self.base_measure().is_zero()
    }

    #[inline]
    fn measure<M: Metric<Self::Summary>>(&self) -> M {
        M::measure_leaf(self)
    }
}

pub trait LeafSlice<'a>: Copy + Debug
where
    Self: 'a,
{
    type Leaf: Leaf<Slice<'a> = Self> + ?Sized;

    fn summarize(&self) -> <Self::Leaf as Leaf>::Summary;

    #[inline]
    fn base_measure(&self) -> <Self::Leaf as Leaf>::BaseMetric {
        self.measure()
    }

    #[inline]
    fn is_empty(&self) -> bool {
        self.base_measure().is_zero()
    }

    #[inline]
    fn measure<M: Metric<<Self::Leaf as Leaf>::Summary>>(&self) -> M {
        M::measure_slice(self)
    }
}

pub trait BalancedLeaf: Leaf + for<'a> From<Self::Slice<'a>> {
    /// Returns whether the leaf node is too small to be on its own and should
    /// be rebalanced with another leaf.
    fn is_underfilled(&self) -> bool;

    /// Balance two leaves.
    ///
    /// The `right` leaf can be left empty if the two leaves can be combined
    /// into a single one.
    fn balance_leaves(left: &mut Self, right: &mut Self);
}

pub trait ReplaceableLeaf<M: Metric<Self::Summary>>: BalancedLeaf {
    type Replacement<'a>;

    type ExtraLeaves: ExactSizeIterator<Item = Self>;

    /// Replace the contents of the leaf in the range with the given
    /// replacement.
    ///
    /// If that would cause the leaf to be too big the function can return an
    /// iterator over the leaves to insert right after this leaf. Note that in
    /// this case both this leaf and all the leaves yielded by the iterator are
    /// assumed to not be underfilled.
    fn replace<R>(
        &mut self,
        range: R,
        replace_with: Self::Replacement<'_>,
    ) -> Option<Self::ExtraLeaves>
    where
        R: RangeBounds<M>;

    fn remove_up_to(&mut self, up_to: M);
}

pub trait Metric<S: Summary>:
    Debug
    + Copy
    + Ord
    + Add<Output = Self>
    + AddAssign
    + Sub<Output = Self>
    + SubAssign
{
    /// The identity element of this metric with respect to addition.
    ///
    /// Given an implementor `M` of this trait, for all instances `m` of `M`
    /// it should hold `m == m + M::zero()`.
    fn zero() -> Self;

    /// The smallest value larger than [`zero`](Self::zero()) this metric can
    /// measure.
    fn one() -> Self;

    /// Returns the measure of the leaf's summary according to this metric.
    fn measure(summary: &S) -> Self;

    #[inline]
    fn is_zero(self) -> bool {
        self == Self::zero()
    }

    #[inline]
    fn measure_leaf(leaf: &S::Leaf) -> Self {
        Self::measure(&leaf.summarize())
    }

    #[inline]
    fn measure_slice(leaf_slice: &<S::Leaf as Leaf>::Slice<'_>) -> Self {
        Self::measure(&leaf_slice.summarize())
    }
}

/// Trait for metrics that can be converted from another metric.
pub trait FromMetric<M: Metric<S>, S: Summary>: Metric<S> {
    fn measure_up_to(leaf: &S::Leaf, up_to: M) -> Self;
}

impl<S: Summary, M: Metric<S>> FromMetric<Self, S> for M {
    #[inline]
    fn measure_up_to(_: &S::Leaf, up_to: Self) -> Self {
        up_to
    }
}

/// Metrics that can be used to slice `Tree`s and `TreeSlice`s.
pub trait SlicingMetric<L: Leaf>: Metric<L::Summary> {
    fn slice_up_to<'a>(slice: L::Slice<'a>, up_to: Self) -> L::Slice<'a>;

    fn slice_from<'a>(slice: L::Slice<'a>, from: Self) -> L::Slice<'a>;
}

/// Allows iterating forward over the units of this metric.
pub trait UnitMetric<L: Leaf>: Metric<L::Summary> {
    /// Returns a `(first_slice, rest_slice, advance)` tuple, where `advance`
    /// is equal to `first_slice`'s base length **plus** the length of any
    /// content between the end of `first_slice` and the start of `rest_slice`
    /// that's not included in either of them.
    ///
    /// It follows that if `slice == first_slice ++ rest_slice` (where `++`
    /// denotes concatenation), the `advance` should be equal to
    /// `first_slice`'s base length.
    fn first_unit<'a>(
        slice: L::Slice<'a>,
    ) -> (L::Slice<'a>, L::Slice<'a>, L::BaseMetric);
}

/// Allows iterating backward over the units of this metric.
pub trait DoubleEndedUnitMetric<L: Leaf>: UnitMetric<L> {
    /// Returns a `(rest_slice, last_slice, advance)` tuple, where `advance` is
    /// equal to `last_slice`'s base length **plus** the length of any content
    /// between the end of `last_slice` and the end of the original `slice`.
    ///
    /// It follows that if `slice == rest_slice ++ last_slice` (where `++`
    /// denotes concatenation) the `advance` should be equal to `last_slice`'s
    /// base length.
    fn last_unit<'a>(
        slice: L::Slice<'a>,
    ) -> (L::Slice<'a>, L::Slice<'a>, L::BaseMetric);

    /// It's possible for a leaf slice to contain some content that extends
    /// past the end of its last `M`-unit. This is referred to as "the
    /// remainder of the leaf divided by `M`".
    ///
    /// Returns a `(rest_slice, remainder)` tuple. Note that unlike
    /// [`last_unit`](Self::last_unit()), this function does not allow an
    /// `advance` to be returned. Instead `rest_slice` and `remainder` should
    /// always concatenate up the original `slice`.
    ///
    /// The remainder can be empty if the last `M`-unit coincides with the end
    /// of the leaf slice.
    fn remainder<'a>(slice: L::Slice<'a>) -> (L::Slice<'a>, L::Slice<'a>);
}
