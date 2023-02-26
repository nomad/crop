# Benchmarks

I've benchmarked crop against [Ropey](https://github.com/cessen/ropey) and
[xi_rope](https://github.com/xi-editor/xi-editor/tree/master/rust/rope)
on 4 different use cases:

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

| `cargo bench from_str` | `cargo bench builder` |
|           :--:         |          :--:         |
| ![from_str][from_str]  | ![builder][builder]   |

## Slices

Unlike crop and Ropey, xi_rope doesn't have a proper `RopeSlice` type and
slicing a `Rope` results in a newly allocated `Rope` so it hasn't been included
in the `from_slice` benchmark.

| `cargo bench byte_slice` | `cargo bench line_slice` |
| :--: | :--: |
| ![byte_slice][byte_slice] | ![line_slice][line_slice] |

|       `cargo bench from_slice`      |      |
|                :--:                 | :--: |
| ![rope_from_slice][rope_from_slice] | &emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&nbsp; |

## Iterators

| `cargo bench iter_chunks` | `cargo bench iter_bytes` |
| :--: | :--: |
| ![Chunks](../rope-benches/graphs/iter_lines.png) | ![Bytes](../rope-benches/graphs/iter_lines.png)|

| `cargo bench iter_chars` | `cargo bench iter_lines` |
| :--: | :--: |
| ![Chars](../rope-benches/graphs/iter_lines.png) | ![Lines](../rope-benches/graphs/iter_lines.png)|

## Edits

[from_str]: https://user-images.githubusercontent.com/59321248/221392148-b93aca81-035e-4d2d-92c0-535e28a5a410.png
[builder]: https://user-images.githubusercontent.com/59321248/221392170-21bea58f-e61e-4361-803f-e9e9565c3fbf.png
[byte_slice]:  https://user-images.githubusercontent.com/59321248/221392230-eba905b9-d617-475b-be41-868e0c26aca6.png
[line_slice]: https://user-images.githubusercontent.com/59321248/221392233-a00f1684-1b20-4f91-a860-a9deca4def84.png
[rope_from_slice]: https://user-images.githubusercontent.com/59321248/221392238-f7a132c9-53e7-4124-9b9f-3f4001a1ecd9.png
