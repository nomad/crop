# Changelog

## [Unreleased]


## [0.2.0] - Mar 26 2023

### Performance

- the leaves of the B-tree are now gap buffers instead of simple `String`s,
  which improves the performance of consecutive edits applied to the same
  cursor position. This alone resulted in a 8-15% improvement in the
  [crdt-benchmarks](https://github.com/josephg/crdt-benchmarks), and together
  with other tweaks it makes `v0.2` 80-90% faster than `v0.1` on those
  editing traces;

- [`RopeBuilder::append()`](https://docs.rs/crop/0.2.0/crop/struct.RopeBuilder.html#method.append)
  is around 20% faster;

### Breaking changes

- the [`Chunks`](https://docs.rs/crop/0.2.0/crop/iter/struct.Chunks.html)
  iterator no longer implements `ExactSizeIterator`;

[Unreleased]: https://github.com/noib3/crop/compare/v0.2.0...HEAD
[0.2.0]: https://github.com/noib3/crop/compare/v0.1.0...v0.2.0
