# Benchmarks

I've benchmarked crop against [Ropey](https://github.com/cessen/ropey) and
[xi_rope](https://github.com/xi-editor/xi-editor/tree/master/rust/rope)
on 4 different use cases:

- [creating](#creation) a rope from a string or using a builder;
- [slicing](#slices) the rope and converting the slice back to an owned `Rope`;
- [iterating](#iterators) over the rope's chunks, bytes, `char`s, and lines;
- [editing](#edits) the rope by inserting/deleting/replacing some text.

using 4 different input texts to track the change in performance as the size of
the underlying buffer increases:

- [tiny.txt][tiny]: 669 bytes, 9 lines;
- [small.txt][small]: 1.5 KB, 20 lines;
- [medium.txt][medium]: 219 KB, 3086 lines;
- [large.txt][large]: 1.5 MB, 21596 lines.

The code used to run the benchmarks can be found
[here](https://github.com/noib3/rope_benches).

All the benchmarks were run on a 2018 MacBook Pro with a (not so) mighty 2.2
GHz 6-Core Intel Core i7.

## Creation

| `cargo bench from_str` | `cargo bench builder` |
|          :--:          |         :--:          |
| ![from_str][from_str]  | ![builder][builder]   |

## Slices

Unlike crop and Ropey, xi_rope doesn't have a proper `RopeSlice` type and
slicing a `Rope` results in a newly allocated `Rope` so it wasn't included in
the `from_slice` benchmark.

|  `cargo bench byte_slice`  | `cargo bench line_slice`  |
|            :--:            |            :--:           |
| ![byte_slice][byte_slice]  | ![line_slice][line_slice] |

|       `cargo bench from_slice`      |      |
|                 :--:                | :--: |
| ![rope_from_slice][rope_from_slice] | &emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&nbsp; |

## Iterators

xi_rope doesn't provide iterators over the bytes and `char`s of its `Rope` so
it wasn't included in the `iter_bytes` and `iter_chars` benchmarks.

| `cargo bench iter_chunks`   | `cargo bench iter_bytes`  |
|             :--:            |            :--:           |
| ![iter_chunks][iter_chunks] | ![iter_bytes][iter_bytes] |

| `cargo bench iter_chars`  | `cargo bench iter_lines`  |
|            :--:           |            :--:           |
| ![iter_chars][iter_chars] | ![iter_lines][iter_lines] |


## Edits

| `cargo bench insert_char`   |    `cargo bench insert_sentence`    |
|             :--:            |                 :--:                |
| ![insert_char][insert_char] | ![insert_sentence][insert_sentence] |

|  `cargo bench insert_large`   |  `cargo bench delete_char`  |
|              :--:             |             :--:            |
| ![insert_large][insert_large] | ![delete_char][delete_char] |

| `cargo bench delete_sentence`       |  `cargo bench delete_large`   |
|                 :--:                |              :--:             |
| ![delete_sentence][delete_sentence] | ![delete_large][delete_large] |

|  `cargo bench replace_char`   |    `cargo bench replace_sentence`     |
|              :--:             |                  :--:                 |
| ![replace_char][replace_char] | ![replace_sentence][replace_sentence] |

|   `cargo bench replace_large`   |      |
|               :--:              | :--: |
| ![replace_large][replace_large] | &emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&emsp;&nbsp; |

[tiny]: https://github.com/noib3/rope_benches/blob/master/benches/common/tiny.txt
[small]: https://github.com/noib3/rope_benches/blob/master/benches/common/small.txt
[medium]: https://github.com/noib3/rope_benches/blob/master/benches/common/medium.txt
[large]: https://github.com/noib3/rope_benches/blob/master/benches/common/large.txt

[from_str]: https://user-images.githubusercontent.com/59321248/221392148-b93aca81-035e-4d2d-92c0-535e28a5a410.png
[builder]: https://user-images.githubusercontent.com/59321248/221392170-21bea58f-e61e-4361-803f-e9e9565c3fbf.png

[byte_slice]:  https://user-images.githubusercontent.com/59321248/221392230-eba905b9-d617-475b-be41-868e0c26aca6.png
[line_slice]: https://user-images.githubusercontent.com/59321248/221392233-a00f1684-1b20-4f91-a860-a9deca4def84.png
[rope_from_slice]: https://user-images.githubusercontent.com/59321248/221392238-f7a132c9-53e7-4124-9b9f-3f4001a1ecd9.png

[iter_chunks]: https://user-images.githubusercontent.com/59321248/221393378-7a3bd6e8-274a-4fe7-bff7-61095b9dd205.png
[iter_bytes]: https://user-images.githubusercontent.com/59321248/221393386-be9f68e9-b4d7-402c-8483-01ee55129987.png
[iter_chars]: https://user-images.githubusercontent.com/59321248/221393393-d7c83a0c-1426-409f-ad72-8941e5179204.png
[iter_lines]: https://user-images.githubusercontent.com/59321248/221393396-48bab915-1414-43cd-ac50-11e7e07f3390.png

[insert_char]: https://user-images.githubusercontent.com/59321248/221394925-4186e25e-3ffa-4dec-a89a-7d9f9859cd9f.png
[insert_sentence]: https://user-images.githubusercontent.com/59321248/221394929-0a317261-3b42-42fe-9bbb-af22d659dfdc.png
[insert_large]: https://user-images.githubusercontent.com/59321248/221394937-476a0c8b-30e2-4d36-a94e-ad95ea2ff1fc.png
[delete_char]: https://user-images.githubusercontent.com/59321248/221395853-25601664-407c-4153-82c2-0d1f0d6dc451.png
[delete_sentence]: https://user-images.githubusercontent.com/59321248/221395858-832af775-63b5-46ff-8b44-2bded84692f3.png
[delete_large]: https://user-images.githubusercontent.com/59321248/221395862-4e921f4d-f56b-49ee-986b-0cf8fb7a9d39.png
[replace_char]: https://user-images.githubusercontent.com/59321248/221396984-e4ea3674-444d-4e22-966a-a7850f28595a.png
[replace_sentence]: https://user-images.githubusercontent.com/59321248/221396989-c980c5ef-e6c0-4da0-a2d2-fbc623f7ffca.png
[replace_large]: https://user-images.githubusercontent.com/59321248/221396991-589796b9-a93f-49bb-ab83-5e199b5e78d4.png
