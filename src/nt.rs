use num::Zero;
use num::{BigInt, BigUint};

// Log Base 10 calculation
// Courtesy: https://www.reddit.com/r/rust/comments/7xr8r3/a_question_regarding_the_num_crate_and_logarithms/
pub fn log_base_10(x: &BigInt) -> Result<f64, String> {
    use std::cmp::Ordering;
    let zero = BigInt::zero();
    let x: BigUint = match x.cmp(&zero) {
        Ordering::Less => (-x).to_biguint().unwrap(),
        Ordering::Greater => x.to_biguint().unwrap(),
        Ordering::Equal => return Err("abs_log(0)".to_string()),
    };
    let x: Vec<u8> = x.to_bytes_le();
    use num::Float;
    const BYTES: usize = 12;
    let start = if x.len() < BYTES { 0 } else { x.len() - BYTES };
    let mut n: f64 = 0.0;
    // n will accumulate the f64 value as we go.
    for i in x.iter().skip(start) {
        n = n / 256.0 + (*i as f64);
    }
    let ln_256: f64 = (256.0).ln();
    Ok(n.ln() + ln_256 * ((x.len() - 1) as f64))
}
