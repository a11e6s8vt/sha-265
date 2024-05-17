use std::str::FromStr;

use anyhow::{Context, Result};
use num::{BigInt, Num};
use num_traits::FromBytes;

// TODO: It's tough to pass around big vectors.
// Updating a mutable array is good
pub fn utf8_to_bytes(s: &str) -> Result<Vec<u8>> {
    let encoded_hex = hex::encode(s);
    let byte_arr = BigInt::from_str_radix(&encoded_hex, 16)
        .with_context(|| format!("Failed to create byte array from input '{}'", s))?;
    Ok(byte_arr.to_bytes_be().1)
}

// TODO: Update a mutable array passed by reference.
pub fn bytes_to_utf8(v: Vec<u8>) -> Result<String> {
    let n: BigInt = FromBytes::from_be_bytes(&v[..]);
    let hex_str = n.to_str_radix(16);
    let decoded_bytes = hex::decode(hex_str)
        .with_context(|| "Failed to decode hexadecimal string!!".to_string())?;
    match String::from_utf8(decoded_bytes) {
        Ok(utf8_string) => Ok(utf8_string),
        Err(e) => Err(anyhow::anyhow!(
            "Failed to convert bytes to UTF-8 string: {}",
            e
        )),
    }
}
