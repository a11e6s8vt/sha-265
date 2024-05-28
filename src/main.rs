mod hash;
mod nt;
mod utf8;

use crate::hash::sha256;

fn main() {
    let r1 = sha256("abc");
    println!("SHA-256 hash for {}: {}", "abc", r1);
    let r2 = sha256("abcdefghijklmnopqrstuvwxyz");
    println!("SHA-256 hash for {}: {}", "abcdefghijklmnopqrstuvwxyz", r2);
}
