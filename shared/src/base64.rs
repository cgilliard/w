//! Base64, with padding: how what is kept in a file or copied as text
//! (a slate, a proof, a record of a name) is written.

const B64: &[u8; 64] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";

/// Base64, with padding.
pub fn encode(bytes: &[u8]) -> String {
    let mut out = String::with_capacity(bytes.len().div_ceil(3) * 4);
    for chunk in bytes.chunks(3) {
        let v = chunk.iter().enumerate().fold(0u32, |v, (i, b)| v | (*b as u32) << (16 - 8 * i));
        for k in 0..4 {
            match k <= chunk.len() {
                true => out.push(B64[(v >> (18 - 6 * k)) as usize & 63] as char),
                false => out.push('='),
            }
        }
    }
    out
}

/// What [`encode`] encoded; `None` for anything else.
pub fn decode(text: &str) -> Option<Vec<u8>> {
    let bytes = text.as_bytes();
    if !bytes.len().is_multiple_of(4) {
        return None;
    }
    let mut out = Vec::with_capacity(bytes.len() / 4 * 3);
    for (at, chunk) in bytes.chunks(4).enumerate() {
        let pad = chunk.iter().rev().take_while(|c| **c == b'=').count();
        if pad > 2 || (pad > 0 && at + 1 != bytes.len() / 4) {
            return None;
        }
        let mut v = 0u32;
        for (k, c) in chunk.iter().enumerate() {
            let six = match k < 4 - pad {
                true => B64.iter().position(|b| b == c)? as u32,
                false => 0,
            };
            v |= six << (18 - 6 * k);
        }
        // (What padding stands for is nothing: bits there are no encoding.)
        if pad > 0 && v & ((1 << (8 * pad)) - 1) != 0 {
            return None;
        }
        out.extend_from_slice(&v.to_be_bytes()[1..4 - pad]);
    }
    Some(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn base64_is_base64() {
        for (bytes, text) in [("", ""), ("f", "Zg=="), ("fo", "Zm8="), ("foo", "Zm9v"), ("foobar", "Zm9vYmFy")] {
            assert_eq!(encode(bytes.as_bytes()), text);
            assert_eq!(decode(text).unwrap(), bytes.as_bytes());
        }
        let all: Vec<u8> = (0..=255).collect();
        assert_eq!(decode(&encode(&all)).unwrap(), all);
        for bad in ["Zg=", "Z===", "Zg==Zm9v", "Zh==", "Zm9!", "=m9v"] {
            assert_eq!(decode(bad), None, "{bad}");
        }
    }
}
