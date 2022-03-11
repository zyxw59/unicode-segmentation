#![no_main]
use libfuzzer_sys::fuzz_target;
use unicode_segmentation::UnicodeSegmentation;

fuzz_target!(|data: &[char]| {
    let _g = data.graphemes(true).collect::<Vec<&[char]>>();
    let _w = data.unicode_words().collect::<Vec<&[char]>>();
    let _ws = data.split_word_bounds().collect::<Vec<&[char]>>();
});
