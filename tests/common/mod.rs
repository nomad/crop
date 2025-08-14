#![allow(dead_code)]

use std::env;

use rand::SeedableRng;

pub const TINY: &str = include_str!("tiny.txt");
pub const SMALL: &str = include_str!("small.txt");
pub const MEDIUM: &str = include_str!("medium.txt");
pub const LARGE: &str = include_str!("large.txt");

#[track_caller]
pub fn rng() -> impl rand::Rng {
    let seed = seed();
    println!("SEED: {seed:?}");
    rand_chacha::ChaChaRng::seed_from_u64(seed)
}

#[track_caller]
fn seed() -> u64 {
    match env::var("SEED") {
        Ok(seed) => seed.parse().expect("couldn't parse $SEED"),
        Err(env::VarError::NotPresent) => rand::random(),
        Err(env::VarError::NotUnicode(seed)) => {
            panic!("$SEED contained invalid unicode: {seed:?}")
        },
    }
}

/// A cursed version of a lorem ipsum paragraph taken from [this online
/// tool][1] with mixed line breaks (LF and CRLF).
///
/// [1]: https://jeff.cis.cabrillo.edu/tools/homoglyphs
pub const CURSED_LIPSUM: &str = "Ḽơᶉëᶆ ȋṕšᶙṁ\nḍỡḽǭᵳ ʂǐť ӓṁệẗ,\r\n \
                                 ĉṓɲṩḙċťᶒțûɾ \nấɖḯƥĭ\r\nṩčįɳġ ḝłįʈ, șế\r\nᶑ \
                                 ᶁⱺ ẽḭŭŝḿꝋď\n ṫĕᶆᶈṓɍ ỉñḉīḑȋᵭṵńť \nṷŧ ḹẩḇőꝛế \
                                 éȶ đꝍꞎ\r\nôꝛȇ ᵯáꞡ\r\nᶇā ąⱡ\nîɋṹẵ.";

// The following test vectors were taken from Ropey.

/// 127 bytes, 103 chars, 1 line
pub const TEXT: &str = "Hello there!  How're you doing?  It's a fine day, \
                        isn't it?  Aren't you glad we're alive?  \
                        こんにちは、みんなさん！";

/// 124 bytes, 100 chars, 4 lines
pub const TEXT_LINES: &str = "Hello there!  How're you doing?\nIt's a fine \
                              day, isn't it?\nAren't you glad we're \
                              alive?\nこんにちは、みんなさん！";

/// 127 bytes, 107 chars, 111 utf16 code units, 1 line
pub const TEXT_EMOJI: &str = "Hello there!🐸  How're you doing?🐸  It's a \
                              fine day, isn't it?🐸  Aren't you glad we're \
                              alive?🐸  こんにちは、みんなさん！";
