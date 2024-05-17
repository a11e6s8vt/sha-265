use crate::utf8::utf8_to_bytes;

fn vec_to_string(v: &Vec<u8>) -> String {
    let str_bits: Vec<String> = v.iter().map(|n| n.to_string()).collect();

    str_bits.join("")
}

fn bytes_to_binary(b: &[u8]) -> Vec<u8> {
    b.iter()
        .flat_map(|val| {
            [
                (val >> 7) & 1,
                (val >> 6) & 1,
                (val >> 5) & 1,
                (val >> 4) & 1,
                (val >> 3) & 1,
                (val >> 2) & 1,
                (val >> 1) & 1,
                (val >> 0) & 1,
            ]
            .into_iter()
        })
        .collect::<Vec<_>>()
}

fn modulo_add(x: &[u8], y: &[u8]) -> Vec<u8> {
    assert_eq!(x.len(), 32);
    assert_eq!(y.len(), 32);

    let mut x = x.to_vec();
    let mut y = y.to_vec();
    // Using BigInt to avoid integer boundary issues
    let mut op1: u32 = 0;
    for i in 0..=31 {
        op1 += x.pop().unwrap() as u32 * 2u32.pow(i as u32);
    }

    let mut op2: u32 = 0;
    for i in 0..=31 {
        op2 += y.pop().unwrap() as u32 * 2u32.pow(i as u32);
    }

    // in n-bit binary addition, we drop the final carry. This is equivalent to
    // modulus (2.pow(n)). The maximum value we can hold hence is 2u32.pow(32u32) - 1
    // wrapping_add in std::num achieves this
    let sum = op1.wrapping_add(op2);

    let res: Vec<u8> = sum.to_be_bytes().to_vec();
    bytes_to_binary(&res)
}

fn ch(x: u32, y: u32, z: u32) -> u32 {
    let x_and_y: u32 = x & y;
    let not_x_and_z: u32 = !x & z;

    x_and_y ^ not_x_and_z
}

fn maj(x: u32, y: u32, z: u32) -> u32 {
    let x_and_y: u32 = x & y;
    let x_and_z: u32 = x & z;
    let y_and_z: u32 = y & z;

    x_and_y ^ x_and_z ^ y_and_z
}

fn large_sigma_zero(x: u32) -> u32 {
    let rr2 = x.rotate_right(2);
    let rr13 = x.rotate_right(13);
    let rr22 = x.rotate_right(22);

    rr2 ^ rr13 ^ rr22
}

fn large_sigma_one(x: u32) -> u32 {
    let rr6 = x.rotate_right(6);
    let rr11 = x.rotate_right(11);
    let rr25 = x.rotate_right(25);

    rr6 ^ rr11 ^ rr25
}

fn sigma_zero(x: u32) -> u32 {
    let rr7 = x.rotate_right(7);
    let rr18 = x.rotate_right(18);
    let sr3 = x >> 3;

    rr7 ^ rr18 ^ sr3
}

fn sigma_one(x: u32) -> u32 {
    let rr17 = x.rotate_right(17);
    let rr19 = x.rotate_right(19);
    let sr10 = x >> 10;

    rr17 ^ rr19 ^ sr10
}

fn compute_t1(e: u32, f: u32, g: u32, h: u32, k_t: u32, w_t: u32) -> u32 {
    let s1 = large_sigma_one(e);
    (((h.wrapping_add(s1)).wrapping_add(ch(e, f, g))).wrapping_add(k_t)).wrapping_add(w_t)
}

fn compute_t2(a: u32, b: u32, c: u32) -> u32 {
    let s1 = large_sigma_zero(a);
    s1.wrapping_add(maj(a, b, c))
}

fn input_padding(msg: &str) -> Vec<u8> {
    // convert the input string into bytes array
    let b = utf8_to_bytes(msg).unwrap();
    // convert the byte array into binary
    let mut bits = bytes_to_binary(&b[..]);
    // lenth of the input in bits
    let l = bits.len();
    // append '1' to the end of the binary vec
    bits.push(3 & 1);

    // calculate the length of '0' suffix to 'bits'
    let mut k = (448 - (l as i64 + 1)) % 512;
    if k < 0 {
        k = (k + 512) % 512;
    }

    // append 'k' zeroes to bits
    let zero_vec = vec![0; k as usize];
    bits.extend(zero_vec);

    // convert 'l' to binary as a 64 bit block
    let l_bits = bytes_to_binary(&l.to_be_bytes());
    // extend 'bits' vec by length of the message
    bits.extend(l_bits);

    bits
}

fn input_parsing(s: &[u8], msg_blocks: &mut Vec<Vec<u32>>) {
    let mut block_lb = 0;
    let mut block_ub = 512;
    loop {
        let mut words: Vec<u32> = Vec::new();
        let msg_block = &s[block_lb..block_ub];
        let mut word_lb = 0;
        let mut word_ub = 32;

        loop {
            let word = &msg_block[word_lb..word_ub];
            let word = vec_to_string(&word.to_vec());
            let word = u32::from_str_radix(&word, 2).expect("decoding binary to u32 failed");
            words.push(word);
            if word_ub >= msg_block.len() {
                break;
            }

            word_lb = word_ub;
            word_ub += 32;
        }
        msg_blocks.push(words);

        if block_ub >= s.len() {
            break;
        }
        block_lb = block_ub;
        block_ub += 512;
    }
}

fn prepare_massage_schedule(msg_block: Vec<u32>, w_message_schedule: &mut Vec<u32>) {
    let mut t = 0;
    while t <= 15 {
        w_message_schedule.push(msg_block[t]);
        t += 1;
    }

    while (16..=63).contains(&t) {
        // msg = "abc" -> message_schedule[t - 2] is all zeroes
        // Hence no effect on sigma_one
        let s1 = sigma_one(w_message_schedule[t - 2]);
        let s0 = sigma_zero(w_message_schedule[t - 15]);
        let w_t = ((s1.wrapping_add(w_message_schedule[t - 7])).wrapping_add(s0))
            .wrapping_add(w_message_schedule[t - 16]);
        w_message_schedule.push(w_t);
        t += 1;
    }
}

fn compute_intermediate_hashes(
    computed_hashes: &mut Vec<Vec<u32>>,
    initial_hash: &[u32],
    K: &[u32],
    i: usize,
    W: &Vec<u32>,
) {
    /* Eight working variables */
    let mut a: u32;
    let mut b: u32;
    let mut c: u32;
    let mut d: u32;
    let mut e: u32;
    let mut f: u32;
    let mut g: u32;
    let mut h: u32;

    if i > 0 {
        a = computed_hashes[i - 1][0];
        b = computed_hashes[i - 1][1];
        c = computed_hashes[i - 1][2];
        d = computed_hashes[i - 1][3];
        e = computed_hashes[i - 1][4];
        f = computed_hashes[i - 1][5];
        g = computed_hashes[i - 1][6];
        h = computed_hashes[i - 1][7];
    } else {
        a = initial_hash[0];
        b = initial_hash[1];
        c = initial_hash[2];
        d = initial_hash[3];
        e = initial_hash[4];
        f = initial_hash[5];
        g = initial_hash[6];
        h = initial_hash[7];
    }

    for t in 0..=63 {
        let t1 = compute_t1(e, f, g, h, K[t], W[t]);
        let t2 = compute_t2(a, b, c);
        h = g;
        g = f;
        f = e;
        e = d.wrapping_add(t1);
        d = c;
        c = b;
        b = a;
        a = t1.wrapping_add(t2);
    }

    let mut intermediate_hash: Vec<u32> = Vec::new();

    if i > 0 {
        intermediate_hash.push(a.wrapping_add(computed_hashes[i - 1][0]));
        intermediate_hash.push(b.wrapping_add(computed_hashes[i - 1][1]));
        intermediate_hash.push(c.wrapping_add(computed_hashes[i - 1][2]));
        intermediate_hash.push(d.wrapping_add(computed_hashes[i - 1][3]));
        intermediate_hash.push(e.wrapping_add(computed_hashes[i - 1][4]));
        intermediate_hash.push(f.wrapping_add(computed_hashes[i - 1][5]));
        intermediate_hash.push(g.wrapping_add(computed_hashes[i - 1][6]));
        intermediate_hash.push(h.wrapping_add(computed_hashes[i - 1][7]));
    } else {
        intermediate_hash.push(a.wrapping_add(initial_hash[0]));
        intermediate_hash.push(b.wrapping_add(initial_hash[1]));
        intermediate_hash.push(c.wrapping_add(initial_hash[2]));
        intermediate_hash.push(d.wrapping_add(initial_hash[3]));
        intermediate_hash.push(e.wrapping_add(initial_hash[4]));
        intermediate_hash.push(f.wrapping_add(initial_hash[5]));
        intermediate_hash.push(g.wrapping_add(initial_hash[6]));
        intermediate_hash.push(h.wrapping_add(initial_hash[7]));
    }
    computed_hashes.push(intermediate_hash);
}

fn sha256(s: &str) -> String {
    /* SHA-256 Constants */
    const K: &[u32] = &[
        0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4,
        0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe,
        0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f,
        0x4a7484aa, 0x5cb0a9dc, 0x76f988da, 0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
        0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc,
        0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b,
        0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070, 0x19a4c116,
        0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
        0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7,
        0xc67178f2,
    ];
    /* Initial Hash */
    const INITIAL_HASH: &[u32] = &[
        0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
        0x5be0cd19,
    ];
    let mut computed_hashes: Vec<Vec<u32>> = Vec::new();

    /* Padding */
    let padded_msg = input_padding(s);

    /* Parse Input */
    let mut msg_blocks: Vec<Vec<u32>> = Vec::new();
    input_parsing(&padded_msg[..], &mut msg_blocks);

    /* Hash Computation */
    let mut w_message_schedule: Vec<u32> = Vec::new();
    for (i, msg_block) in msg_blocks.iter().enumerate() {
        prepare_massage_schedule(msg_block.to_vec(), &mut w_message_schedule);
        compute_intermediate_hashes(
            &mut computed_hashes,
            INITIAL_HASH,
            K,
            i,
            &w_message_schedule,
        )
    }
    //
    let final_hash = computed_hashes.last().unwrap();
    let final_hash = final_hash
        .iter()
        .map(|n| format!("{:01$x}", n, 8))
        .collect::<Vec<String>>();
    final_hash.join("")
}

#[cfg(test)]
mod tests {
    use super::input_padding;
    use super::sha256;

    #[test]
    fn test_input_padding_case1() {
        let s = "abc";
        let r = input_padding(s);
        let str_bits: Vec<String> = r
            .iter()
            .map(|n| n.to_string()) // map every integer to a string
            .collect(); // collect the strings into the vector

        let str_bits = str_bits.join("");
        assert_eq!(
            str_bits,
            "01100001011000100110001110000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000011000".to_string()
        );
    }

    #[test]
    fn test_input_padding_case2() {
        let s = "abcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyz";
        let r = input_padding(s);
        let str_bits: Vec<String> = r
            .iter()
            .map(|n| n.to_string()) // map every integer to a string
            .collect(); // collect the strings into the vector

        let str_bits = str_bits.join("");
        assert_eq!(
            str_bits,
            "0110000101100010011000110110010001100101011001100110011101101000011010010110101001101011011011000110110101101110011011110111000001110001011100100111001101110100011101010111011001110111011110000111100101111010011000010110001001100011011001000110010101100110011001110110100001101001011010100110101101101100011011010110111001101111011100000111000101110010011100110111010001110101011101100111011101111000011110010111101001100001011000100110001101100100011001010110011001100111011010000110100101101010011010110110110001101101011011100110111101110000011100010111001001110011011101000111010101110110011101110111100001111001011110100110000101100010011000110110010001100101011001100110011101101000011010010110101001101011011011000110110101101110011011110111000001110001011100100111001101110100011101010111011001110111011110000111100101111010100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001101000000".to_string()
        );
    }

    #[test]
    fn test_sha256_case1() {
        let s = "abc";
        let r1 = sha256(s);
        assert_eq!(
            r1,
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad".to_string()
        );
    }

    #[test]
    fn test_sha256_case2() {
        let r2 = sha256("abcd");
        assert_eq!(
            r2,
            "88d4266fd4e6338d13b845fcf289579d209c897823b9217da3e161936f031589".to_string()
        );
    }

    #[test]
    fn test_sha256_case3() {
        let r2 = sha256("abcde");
        assert_eq!(
            r2,
            "36bbe50ed96841d10443bcb670d6554f0a34b761be67ec9c4a8ad2c0c44ca42c".to_string()
        );
    }

    #[test]
    fn test_sha256_case4() {
        let r2 = sha256("abcdefghijklm");
        assert_eq!(
            r2,
            "ff10304f1af23606ede1e2d8abcdc94c229047a61458d809d8bbd53ede1f6598".to_string()
        );
    }

    #[test]
    fn test_sha256_case5() {
        let r2 = sha256("abcdefghijklmnopqrstuvwxyz");
        assert_eq!(
            r2,
            "71c480df93d6ae2f1efad1447c66c9525e316218cf51fc8d9ed832f2daf18b73".to_string()
        );
    }

    #[test]
    fn test_sha256_case6() {
        let r2 = sha256("abcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyz");
        assert_eq!(
            r2,
            "2378d314a98e2394fec97b780aa58704a667b7dba1769473c494f4ab3f67e236".to_string()
        );
    }

    #[test]
    fn test_sha256_case7() {
        let r2 = sha256("1 + 2");
        assert_eq!(
            r2,
            "6212702c7a0d68f00b8b23b5aecfca631a96c20d2cad78cd874611ac87cdbce1".to_string()
        );
    }
}
