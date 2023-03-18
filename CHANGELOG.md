# Changelog

## [Unreleased]

### Performance

- the leaves of the B-tree are now gap buffers instead of simple `String`s,
  which improves the performance of consecutive edits applied to the same
  cursor position;

- [`RopeBuilder::append()`](https://docs.rs/crop/0.2.0/crop/struct.RopeBuilder.html#method.append)
  is around 20% faster;

### Breaking changes

- the [`Chunks`](https://docs.rs/crop/0.2.0/crop/iter/struct.Chunks.html)
  iterator no longer implements `ExactSizeIterator`;

[Unreleased]: https://github.com/noib3/crop/compare/v0.1.0...HEAD
