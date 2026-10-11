//! canonical JSON(入力仕様 §4)と SHA-256 digest。

use sha2::{Digest, Sha256};
use std::collections::BTreeMap;

/// 結果と manifest に使う JSON 値。object の key は `BTreeMap` が UTF-8 byte 順に保つ。
/// UTF-8 の byte 順は Unicode scalar 順と一致する。
#[derive(Debug, Eq)]
pub enum Json {
    Bool(bool),
    Nat(u64),
    Str(String),
    Arr(Vec<Json>),
    Obj(BTreeMap<String, Json>),
}

impl Json {
    pub fn str(s: impl Into<String>) -> Json {
        Json::Str(s.into())
    }

    pub fn obj<const N: usize>(entries: [(&str, Json); N]) -> Json {
        Json::Obj(
            entries
                .into_iter()
                .map(|(k, v)| (k.to_owned(), v))
                .collect(),
        )
    }

    /// 空白なし、key は Unicode scalar 順、非 ASCII は UTF-8 のまま出力する。
    pub fn canonical(&self) -> String {
        let mut out = String::new();
        self.write(&mut out);
        out
    }

    fn write(&self, out: &mut String) {
        stacker::maybe_grow(64 * 1024, 1024 * 1024, || match self {
            Json::Bool(b) => out.push_str(if *b { "true" } else { "false" }),
            Json::Nat(n) => out.push_str(&n.to_string()),
            Json::Str(s) => write_string(s, out),
            Json::Arr(items) => {
                out.push('[');
                for (i, item) in items.iter().enumerate() {
                    if i > 0 {
                        out.push(',');
                    }
                    item.write(out);
                }
                out.push(']');
            }
            Json::Obj(entries) => {
                out.push('{');
                for (i, (k, v)) in entries.iter().enumerate() {
                    if i > 0 {
                        out.push(',');
                    }
                    write_string(k, out);
                    out.push(':');
                    v.write(out);
                }
                out.push('}');
            }
        })
    }
}

/// 引用符と backslash を escape し、U+0000..001F を小文字4桁の `\u00xx` にする。
/// その他の文字(`/` を含む)は escape しない。
fn write_string(s: &str, out: &mut String) {
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
}

/// `sha256:` と小文字16進64桁。
pub fn sha256_digest(bytes: &[u8]) -> String {
    let hash = Sha256::digest(bytes);
    let mut out = String::from("sha256:");
    for b in hash {
        out.push_str(&format!("{b:02x}"));
    }
    out
}

/// 深い入れ子の JSON を、呼出し側のスタックの深さによらず解放する。
impl Drop for Json {
    fn drop(&mut self) {
        let mut stack = Vec::new();
        take_children(self, &mut stack);
        while let Some(mut j) = stack.pop() {
            take_children(&mut j, &mut stack);
        }
    }
}

fn take_children(j: &mut Json, stack: &mut Vec<Json>) {
    match j {
        Json::Arr(items) => stack.append(items),
        Json::Obj(entries) => stack.extend(std::mem::take(entries).into_values()),
        _ => {}
    }
}

impl Clone for Json {
    fn clone(&self) -> Json {
        stacker::maybe_grow(64 * 1024, 1024 * 1024, || match self {
            Json::Bool(b) => Json::Bool(*b),
            Json::Nat(n) => Json::Nat(*n),
            Json::Str(s) => Json::Str(s.clone()),
            Json::Arr(items) => Json::Arr(items.clone()),
            Json::Obj(entries) => Json::Obj(entries.clone()),
        })
    }
}

impl PartialEq for Json {
    fn eq(&self, other: &Json) -> bool {
        stacker::maybe_grow(64 * 1024, 1024 * 1024, || match (self, other) {
            (Json::Bool(a), Json::Bool(b)) => a == b,
            (Json::Nat(a), Json::Nat(b)) => a == b,
            (Json::Str(a), Json::Str(b)) => a == b,
            (Json::Arr(a), Json::Arr(b)) => a == b,
            (Json::Obj(a), Json::Obj(b)) => a == b,
            _ => false,
        })
    }
}
