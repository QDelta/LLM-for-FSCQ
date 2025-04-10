use core::str;
use std::io::{self, BufRead};
use tiktoken_rs::o200k_base;

fn main() {
    let enc = o200k_base().unwrap();
    let mut stdin = io::stdin().lock();
    let mut buf = Vec::new();
    loop {
        let sz = stdin.read_until(0u8, &mut buf).unwrap();
        if sz == 0 {
            break;
        }
        let msg = str::from_utf8(&buf).unwrap();
        let tokens = enc.encode_with_special_tokens(msg);
        println!("{}", tokens.len());
        buf.clear();
    }
}
