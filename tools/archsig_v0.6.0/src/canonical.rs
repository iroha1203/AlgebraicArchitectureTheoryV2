use serde_json::Value;
use sha2::{Digest, Sha256};

/// Canonical JSON as specified by archsig/0.6.0, including control characters.
pub fn bytes(value: &Value) -> Vec<u8> {
    fn string(s: &str, out: &mut String) {
        out.push('"');
        for c in s.chars() {
            match c {
                '"' => out.push_str("\\\""),
                '\\' => out.push_str("\\\\"),
                '\u{0}'..='\u{1f}' => out.push_str(&format!("\\u{:04x}", c as u32)),
                c => out.push(c),
            }
        }
        out.push('"');
    }
    fn write(v: &Value, out: &mut String) {
        match v {
            Value::String(s) => string(s, out),
            Value::Array(xs) => {
                out.push('[');
                for (i, x) in xs.iter().enumerate() {
                    if i != 0 {
                        out.push(',');
                    }
                    write(x, out);
                }
                out.push(']');
            }
            Value::Object(xs) => {
                out.push('{');
                let mut keys: Vec<_> = xs.keys().collect();
                keys.sort();
                for (i, k) in keys.into_iter().enumerate() {
                    if i != 0 {
                        out.push(',');
                    }
                    string(k, out);
                    out.push(':');
                    write(&xs[k], out);
                }
                out.push('}');
            }
            _ => out.push_str(&v.to_string()),
        }
    }
    let mut out = String::new();
    write(value, &mut out);
    out.into_bytes()
}
pub fn digest(bytes: &[u8]) -> String {
    format!("sha256:{:x}", Sha256::digest(bytes))
}
pub fn model_digest(value: &Value) -> String {
    digest(&bytes(value))
}
