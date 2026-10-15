//! canonical JSON(入力仕様 §4)と SHA-256 digest。

use crate::json::InputError;
use crate::observed::control::{Checkpoint, Control};
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
        self.canonical_controlled::<Box<crate::issue::Issue>>(
            &mut Control::unlimited(),
            Checkpoint::Expression,
        )
        .expect("通常の表示は中断しない")
    }

    /// 検査中のcanonical encodingは、子構造と各文字にも同じ停止制御を渡す。
    pub(crate) fn canonical_controlled<E: InputError>(
        &self,
        control: &mut Control,
        point: Checkpoint,
    ) -> Result<String, E> {
        E::checkpoint(control, point)?;
        let mut out = String::new();
        self.write_controlled::<E>(&mut out, control, point)?;
        E::checkpoint(control, point)?;
        Ok(out)
    }

    fn write_controlled<E: InputError>(
        &self,
        out: &mut String,
        control: &mut Control,
        point: Checkpoint,
    ) -> Result<(), E> {
        stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
            E::checkpoint(control, point)?;
            match self {
                Json::Bool(b) => out.push_str(if *b { "true" } else { "false" }),
                Json::Nat(n) => out.push_str(&n.to_string()),
                Json::Str(s) => write_string_controlled::<E>(s, out, control, point)?,
                Json::Arr(items) => {
                    out.push('[');
                    for (i, item) in items.iter().enumerate() {
                        E::checkpoint(control, point)?;
                        if i > 0 {
                            out.push(',');
                        }
                        item.write_controlled::<E>(out, control, point)?;
                        E::checkpoint(control, point)?;
                    }
                    out.push(']');
                }
                Json::Obj(entries) => {
                    out.push('{');
                    for (i, (k, v)) in entries.iter().enumerate() {
                        E::checkpoint(control, point)?;
                        if i > 0 {
                            out.push(',');
                        }
                        write_string_controlled::<E>(k, out, control, point)?;
                        out.push(':');
                        v.write_controlled::<E>(out, control, point)?;
                        E::checkpoint(control, point)?;
                    }
                    out.push('}');
                }
            }
            E::checkpoint(control, point)?;
            Ok(())
        })
    }
}

/// Canonical escaping keeps the original UTF-8 bytes and checks each scalar.
fn write_string_controlled<E: InputError>(
    s: &str,
    out: &mut String,
    control: &mut Control,
    point: Checkpoint,
) -> Result<(), E> {
    E::checkpoint(control, point)?;
    out.push('"');
    for c in s.chars() {
        E::checkpoint(control, point)?;
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
        E::checkpoint(control, point)?;
    }
    out.push('"');
    E::checkpoint(control, point)?;
    Ok(())
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
    use crate::issue::Issue;
    use crate::observed::control::{CheckFailure, Limits, Resource, StopReason, Usage};
    use crate::result::Signal;
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
            .canonical_controlled::<Failure>(&mut Control::unlimited(), Checkpoint::Expression)
            .unwrap();
        assert_eq!(result, expected);
        assert_eq!(value.canonical(), expected);
    }

    #[test]
    fn nested_json_and_each_string_scalar_stop_at_every_boundary() {
        let value = example();
        let count = Rc::new(Cell::new(0));
        let seen = count.clone();
        let mut control = Control::new(Limits::default(), move |point| {
            assert_eq!(point, Checkpoint::Expression);
            seen.set(seen.get() + 1);
            Usage::default()
        });
        value
            .canonical_controlled::<Failure>(&mut control, Checkpoint::Expression)
            .unwrap();
        let total = count.get();
        assert!(total > 30);
        for at in 1..=total {
            for kind in 0..3 {
                let mut visits = 0;
                let mut control = Control::new(
                    Limits {
                        time_ms: (kind == 1).then_some(1),
                        memory_mib: (kind == 2).then_some(1),
                    },
                    move |_| {
                        visits += 1;
                        let hit = visits == at;
                        Usage {
                            signal: (hit && kind == 0).then_some(Signal::Term),
                            elapsed_ms: u128::from(hit && kind == 1),
                            memory_mib: u128::from(hit && kind == 2),
                        }
                    },
                );
                let expected = match kind {
                    0 => StopReason::Cancelled(Signal::Term),
                    1 => StopReason::BudgetExhausted {
                        resource: Resource::TimeMs,
                        limit: 1,
                        observed: 1,
                    },
                    _ => StopReason::BudgetExhausted {
                        resource: Resource::MemoryMib,
                        limit: 1,
                        observed: 1,
                    },
                };
                assert!(
                    matches!(value.canonical_controlled::<Failure>(&mut control, Checkpoint::Expression), Err(Failure::Stopped(reason)) if reason == expected)
                );
                assert_eq!(control.stop_reason(), Some(expected));
            }
        }
    }
}
