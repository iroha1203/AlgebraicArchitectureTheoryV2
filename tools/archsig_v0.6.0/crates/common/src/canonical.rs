//! canonical JSON(入力仕様 §4)と SHA-256 digest。

use crate::control::{Checkpoint, Control};
use crate::json::InputError;
use sha2::{Digest, Sha256};
mod object;
pub use object::JsonObject;

/// 結果と manifest に使う JSON 値。object の key は `JsonObject` が UTF-8 byte 順に保つ。
/// UTF-8 の byte 順は Unicode scalar 順と一致する。
#[derive(Debug, Eq)]
pub enum Json {
    Bool(bool),
    Nat(u64),
    Str(String),
    Arr(Vec<Json>),
    Obj(JsonObject),
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
        self.canonical_controlled::<Box<crate::issue::Issue>>(
            &Control::unlimited(),
            Checkpoint::Expression,
        )
        .expect("通常の表示は中断しない")
    }

    /// 検査中のcanonical encodingは、子構造と文字列の区切りにも同じ停止制御を渡す。
    pub fn canonical_controlled<E: InputError>(
        &self,
        control: &Control,
        point: Checkpoint,
    ) -> Result<String, E> {
        E::checkpoint(control, point)?;
        let mut out = String::new();
        self.write_controlled(
            &mut |text| {
                out.push_str(text);
                Ok(())
            },
            &mut || E::checkpoint(control, point),
        )?;
        E::checkpoint(control, point)?;
        Ok(out)
    }

    /// 確定済みの表示を全文Stringなしで配送する。計算の停止制御は再導入しない。
    /// flushと公開の確定は呼出し側が担う。
    pub fn write_canonical(&self, out: &mut impl std::io::Write) -> std::io::Result<()> {
        self.write_controlled(&mut |text| out.write_all(text.as_bytes()), &mut || Ok(()))
    }

    fn write_controlled<E>(
        &self,
        emit: &mut impl FnMut(&str) -> Result<(), E>,
        checkpoint: &mut impl FnMut() -> Result<(), E>,
    ) -> Result<(), E> {
        stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
            checkpoint()?;
            match self {
                Json::Bool(b) => emit(if *b { "true" } else { "false" })?,
                Json::Nat(n) => emit(&n.to_string())?,
                Json::Str(s) => emit_string(s, emit, checkpoint)?,
                Json::Arr(items) => {
                    emit("[")?;
                    for (i, item) in items.iter().enumerate() {
                        checkpoint()?;
                        if i > 0 {
                            emit(",")?;
                        }
                        item.write_controlled(emit, checkpoint)?;
                        checkpoint()?;
                    }
                    emit("]")?;
                }
                Json::Obj(entries) => {
                    emit("{")?;
                    for (i, (k, v)) in entries.iter().enumerate() {
                        checkpoint()?;
                        if i > 0 {
                            emit(",")?;
                        }
                        emit_string(k, emit, checkpoint)?;
                        emit(":")?;
                        v.write_controlled(emit, checkpoint)?;
                        checkpoint()?;
                    }
                    emit("}")?;
                }
            }
            checkpoint()?;
            Ok(())
        })
    }
}

/// Canonical escaping keeps the original UTF-8 bytes and checks bounded chunks of scalars.
fn emit_string<E>(
    s: &str,
    emit: &mut impl FnMut(&str) -> Result<(), E>,
    checkpoint: &mut impl FnMut() -> Result<(), E>,
) -> Result<(), E> {
    checkpoint()?;
    emit("\"")?;
    let bytes = s.as_bytes();
    let (mut start, mut offset, mut scalars) = (0, 0, 0usize);
    while offset < bytes.len() {
        let byte = bytes[offset];
        // A str is valid UTF-8: each non-continuation byte starts a scalar.
        // Slice only at these boundaries; escapes are single-byte ASCII.
        if byte & 0xc0 != 0x80 {
            if scalars % 256 == 0 {
                emit(&s[start..offset])?;
                start = offset;
                checkpoint()?;
            }
            scalars += 1;
            if byte == b'"' || byte == b'\\' || byte < 0x20 {
                emit(&s[start..offset])?;
                match byte {
                    b'"' => emit("\\\"")?,
                    b'\\' => emit("\\\\")?,
                    _ => {
                        const HEX: &[u8; 16] = b"0123456789abcdef";
                        let escaped = [
                            b'\\',
                            b'u',
                            b'0',
                            b'0',
                            HEX[(byte >> 4) as usize],
                            HEX[(byte & 15) as usize],
                        ];
                        emit(std::str::from_utf8(&escaped).expect("ASCII escape"))?;
                    }
                }
                start = offset + 1;
            }
        }
        offset += 1;
    }
    emit(&s[start..])?;
    emit("\"")?;
    checkpoint()?;
    Ok(())
}

#[cfg(test)]
fn write_string_controlled<E: InputError>(
    s: &str,
    out: &mut String,
    control: &Control,
    point: Checkpoint,
) -> Result<(), E> {
    emit_string(
        s,
        &mut |text| {
            out.push_str(text);
            Ok(())
        },
        &mut || E::checkpoint(control, point),
    )
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

#[cfg(test)]
mod controlled_tests {
    use super::*;
    use crate::control::CheckFailure;
    use crate::control::Signal;
    use crate::issue::Issue;
    use std::{cell::Cell, rc::Rc};

    type Failure = CheckFailure<Box<Issue>>;

    fn example() -> Json {
        Json::obj([
            ("z", Json::Arr(vec![Json::Bool(false), Json::Nat(7)])),
            ("é", Json::str("\"\\\n/雪")),
            ("a", Json::obj([("empty", Json::Arr(vec![]))])),
        ])
    }

    #[test]
    fn controlled_encoding_keeps_canonical_order_and_exact_escaping() {
        let value = example();
        let expected = r#"{"a":{"empty":[]},"z":[false,7],"é":"\"\\\u000a/雪"}"#;
        let result = value
            .canonical_controlled::<Failure>(&Control::unlimited(), Checkpoint::Expression)
            .unwrap();
        assert_eq!(result, expected);
        assert_eq!(value.canonical(), expected);
    }

    #[test]
    fn string_chunks_preserve_every_control_escape_at_utf8_boundaries() {
        for count in [0, 255, 256, 257] {
            let prefix = "雪".repeat(count);
            for byte in 0u8..0x20 {
                let text = format!("{prefix}{}\"\\終", char::from(byte));
                let expected = format!("\"{prefix}\\u{byte:04x}\\\"\\\\終\"");
                assert_eq!(Json::str(text).canonical(), expected);
            }
        }
    }

    #[test]
    fn long_unicode_string_checks_bounded_chunks_and_preserves_escaping() {
        let text = "雪\n\"\\".repeat(300);
        let calls = Rc::new(Cell::new(0));
        let seen = calls.clone();
        let control = Control::new(move |_| {
            seen.set(seen.get() + 1);
            None
        });
        let mut output = String::new();
        write_string_controlled::<Failure>(&text, &mut output, &control, Checkpoint::Expression)
            .unwrap();
        assert_eq!(output, format!("\"{}\"", "雪\\u000a\\\"\\\\".repeat(300)));
        assert_eq!(calls.get(), 2 + 1200usize.div_ceil(256));
        let mut visits = 0;
        let control = Control::new(move |_| {
            visits += 1;
            (visits == 3).then_some(Signal::Int)
        });
        let mut partial = String::new();
        assert!(matches!(
            write_string_controlled::<Failure>(
                &text,
                &mut partial,
                &control,
                Checkpoint::Expression
            ),
            Err(Failure::Stopped(Signal::Int))
        ));
        assert!(partial.len() < output.len());
    }

    #[test]
    fn nested_json_and_string_chunks_stop_at_every_boundary() {
        let value = example();
        let count = Rc::new(Cell::new(0));
        let seen = count.clone();
        let control = Control::new(move |point| {
            assert_eq!(point, Checkpoint::Expression);
            seen.set(seen.get() + 1);
            None
        });
        value
            .canonical_controlled::<Failure>(&control, Checkpoint::Expression)
            .unwrap();
        let total = count.get();
        assert_eq!(total, 43, "preserve the original encoder checkpoint count");
        for at in 1..=total {
            let mut visits = 0;
            let control = Control::new(move |_| {
                visits += 1;
                (visits == at).then_some(Signal::Term)
            });
            let expected = Signal::Term;
            assert!(
                matches!(value.canonical_controlled::<Failure>(&control, Checkpoint::Expression), Err(Failure::Stopped(reason)) if reason == expected)
            );
            assert_eq!(control.stop_reason(), Some(expected));
        }
    }
}

#[cfg(test)]
mod stream_tests;
