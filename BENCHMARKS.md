# Benchmarks

I've benchmarked crop against [Ropey](https://github.com/cessen/ropey) and
[xi_rope](https://github.com/xi-editor/xi-editor/tree/master/rust/rope)
across 4 different use cases:

- [creating](#creation) a rope from a string or using a builder;
- [slicing](#slices) the rope and converting it back to an owned `Rope`;
- [iterating](#iterators) over its chunks, bytes, `char`s, and lines;
- [editing](#edits) the rope by inserting/deleting/replacing some text.

using 4 different input texts to track the change in performance as the size of
the underlying buffer increases:

- [tiny.txt](): 669 bytes, 9 lines;
- [small.txt](): 1.5 KB, 20 lines;
- [medium.txt](): 219 KB, 3086 lines;
- [large.txt](): 1.5 MB, 21596 lines.

The code used to run the benchmarks can be found
[here](https://github.com/noib3/rope_benches).

All the benchmarks were run on a 2018 MacBook Pro with a (not so) mighty 2.2
GHz 6-Core Intel Core i7.

## Creation

## Slices

## Iterators

| `cargo bench iter_chunks` | `cargo bench iter_bytes` |
| :--: | :--: |
| ![Chunks](../rope-benches/graphs/iter_lines.png) | ![Bytes](../rope-benches/graphs/iter_lines.png)|

| `cargo bench iter_chars` | `cargo bench iter_lines` |
| :--: | :--: |
| ![Chars](../rope-benches/graphs/iter_lines.png) | ![Lines](../rope-benches/graphs/iter_lines.png)|

## Edits
