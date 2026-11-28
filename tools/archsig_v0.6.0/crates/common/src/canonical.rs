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
    /// 保存結果の同種 Ref 列。通常の singleton object の列と同じ JSON を表す。
    NodeReferences(Vec<usize>),
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

    /// 圧縮可能なのは生成済みの厳密な singleton Ref だけ。入力を正規化しない。
    pub fn exact_node_reference(&self) -> Option<usize> {
        let Json::Obj(fields) = self else { return None };
        if fields.len() != 1 {
            return None;
        }
        let Json::Str(id) = fields.get("node")? else {
            return None;
        };
        let digits = id.strip_prefix('n')?;
        if digits.is_empty()
            || digits.len() > usize::BITS as usize
            || !digits.bytes().all(|b| b.is_ascii_digit())
            || (digits.len() > 1 && digits.starts_with('0'))
        {
            return None;
        }
        digits.parse().ok()
    }

    /// 空白なし、key は Unicode scalar 順、非 ASCII は UTF-8 のまま出力する。
    pub fn canonical(&self) -> String {
        self.canonical_controlled::<Box<crate::issue::Issue>>(
            &Control::unlimited(),
            Checkpoint::Expression,
        )
        .expect("通常の表示は中断しない")
    }

    pub fn try_canonical_with_max_depth(
        &self,
        max_depth: usize,
    ) -> Result<String, Box<crate::issue::Issue>> {
        self.canonical_controlled_with_max_depth::<Box<crate::issue::Issue>>(
            max_depth,
            &Control::unlimited(),
            Checkpoint::Expression,
        )
    }

    /// 検査中のcanonical encodingは、子構造と文字列の区切りにも同じ停止制御を渡す。
    pub fn canonical_controlled<E: InputError>(
        &self,
        control: &Control,
        point: Checkpoint,
    ) -> Result<String, E> {
        self.canonical_controlled_with_max_depth(
            crate::limits::DEFAULT_MAX_JSON_DEPTH,
            control,
            point,
        )
    }

    pub fn canonical_controlled_with_max_depth<E: InputError>(
        &self,
        max_depth: usize,
        control: &Control,
        point: Checkpoint,
    ) -> Result<String, E> {
        E::checkpoint(control, point)?;
        let mut out = String::new();
        self.write_controlled(
            0,
            max_depth,
            &mut |text| {
                out.push_str(text);
                Ok(())
            },
            &mut || E::checkpoint(control, point),
            &mut |limit| {
                Box::new(crate::issue::Issue {
                    code: crate::issue::Code::Syntax,
                    message: format!("JSON nesting depth exceeds limit ({limit})"),
                    location: crate::issue::Location::ArchMap {
                        pointer: String::new(),
                        span: None,
                    },
                    details: crate::issue::Details::Empty,
                })
                .into()
            },
        )?;
        E::checkpoint(control, point)?;
        Ok(out)
    }

    /// 確定済みの表示を全文Stringなしで配送する。計算の停止制御は再導入しない。
    /// flushと公開の確定は呼出し側が担う。
    pub fn write_canonical(&self, out: &mut impl std::io::Write) -> std::io::Result<()> {
        self.write_canonical_with_max_depth(out, crate::limits::DEFAULT_MAX_JSON_DEPTH)
    }

    pub fn write_canonical_with_max_depth(
        &self,
        out: &mut impl std::io::Write,
        max_depth: usize,
    ) -> std::io::Result<()> {
        self.write_controlled(
            0,
            max_depth,
            &mut |text| out.write_all(text.as_bytes()),
            &mut || Ok(()),
            &mut |limit| {
                std::io::Error::new(
                    std::io::ErrorKind::InvalidData,
                    format!("JSON nesting depth exceeds limit ({limit})"),
                )
            },
        )
    }

    /// 2 スペース字下げの整形済み canonical JSON を生成する。
    pub fn pretty(&self) -> String {
        self.try_pretty_with_max_depth(crate::limits::DEFAULT_MAX_JSON_DEPTH)
            .expect("通常の整形表示は深度上限を超えない")
    }

    pub fn try_pretty_with_max_depth(
        &self,
        max_depth: usize,
    ) -> Result<String, Box<crate::issue::Issue>> {
        let mut out = String::new();
        self.write_pretty_controlled(
            0,
            max_depth,
            &mut |text| {
                out.push_str(text);
                Ok(())
            },
            &mut || Ok(()),
            &mut |limit| {
                Box::new(crate::issue::Issue {
                    code: crate::issue::Code::Syntax,
                    message: format!("JSON nesting depth exceeds limit ({limit})"),
                    location: crate::issue::Location::ArchMap {
                        pointer: String::new(),
                        span: None,
                    },
                    details: crate::issue::Details::Empty,
                })
            },
        )?;
        Ok(out)
    }

    /// 2 スペース字下げの整形済み canonical JSON をストリーム出力する。
    pub fn write_pretty(&self, out: &mut impl std::io::Write) -> std::io::Result<()> {
        self.write_pretty_with_max_depth(out, crate::limits::DEFAULT_MAX_JSON_DEPTH)
    }

    pub fn write_pretty_with_max_depth(
        &self,
        out: &mut impl std::io::Write,
        max_depth: usize,
    ) -> std::io::Result<()> {
        self.write_pretty_controlled(
            0,
            max_depth,
            &mut |text| out.write_all(text.as_bytes()),
            &mut || Ok(()),
            &mut |limit| {
                std::io::Error::new(
                    std::io::ErrorKind::InvalidData,
                    format!("JSON nesting depth exceeds limit ({limit})"),
                )
            },
        )
    }

    fn write_pretty_controlled<E>(
        &self,
        depth: usize,
        max_depth: usize,
        emit: &mut impl FnMut(&str) -> Result<(), E>,
        checkpoint: &mut impl FnMut() -> Result<(), E>,
        on_depth_exceeded: &mut impl FnMut(usize) -> E,
    ) -> Result<(), E> {
        fn emit_indent<E>(
            depth: usize,
            emit: &mut impl FnMut(&str) -> Result<(), E>,
        ) -> Result<(), E> {
            for _ in 0..depth {
                emit("  ")?;
            }
            Ok(())
        }
        stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
            checkpoint()?;
            match self {
                Json::Bool(b) => emit(if *b { "true" } else { "false" })?,
                Json::Nat(n) => emit(&n.to_string())?,
                Json::Str(s) => emit_string(s, emit, checkpoint)?,
                Json::Arr(items) => {
                    if depth >= max_depth {
                        return Err(on_depth_exceeded(max_depth));
                    }
                    if items.is_empty() {
                        emit("[]")?;
                    } else {
                        emit("[\n")?;
                        for (i, item) in items.iter().enumerate() {
                            if i > 0 {
                                emit(",\n")?;
                            }
                            emit_indent(depth + 1, emit)?;
                            item.write_pretty_controlled(
                                depth + 1,
                                max_depth,
                                emit,
                                checkpoint,
                                on_depth_exceeded,
                            )?;
                        }
                        emit("\n")?;
                        emit_indent(depth, emit)?;
                        emit("]")?;
                    }
                }
                Json::NodeReferences(items) => {
                    if depth >= max_depth || (!items.is_empty() && depth + 1 >= max_depth) {
                        return Err(on_depth_exceeded(max_depth));
                    }
                    if items.is_empty() {
                        emit("[]")?;
                    } else {
                        emit("[\n")?;
                        for (i, index) in items.iter().enumerate() {
                            if i > 0 {
                                emit(",\n")?;
                            }
                            emit_indent(depth + 1, emit)?;
                            emit("{\n")?;
                            emit_indent(depth + 2, emit)?;
                            emit_string("node", emit, checkpoint)?;
                            emit(": ")?;
                            emit_string(&format!("n{index}"), emit, checkpoint)?;
                            emit("\n")?;
                            emit_indent(depth + 1, emit)?;
                            emit("}")?;
                        }
                        emit("\n")?;
                        emit_indent(depth, emit)?;
                        emit("]")?;
                    }
                }
                Json::Obj(entries) => {
                    if depth >= max_depth {
                        return Err(on_depth_exceeded(max_depth));
                    }
                    if entries.is_empty() {
                        emit("{}")?;
                    } else {
                        emit("{\n")?;
                        for (i, (k, v)) in entries.iter().enumerate() {
                            if i > 0 {
                                emit(",\n")?;
                            }
                            emit_indent(depth + 1, emit)?;
                            emit_string(k, emit, checkpoint)?;
                            emit(": ")?;
                            v.write_pretty_controlled(
                                depth + 1,
                                max_depth,
                                emit,
                                checkpoint,
                                on_depth_exceeded,
                            )?;
                        }
                        emit("\n")?;
                        emit_indent(depth, emit)?;
                        emit("}")?;
                    }
                }
            }
            checkpoint()?;
            Ok(())
        })
    }

    fn write_controlled<E>(
        &self,
        depth: usize,
        max_depth: usize,
        emit: &mut impl FnMut(&str) -> Result<(), E>,
        checkpoint: &mut impl FnMut() -> Result<(), E>,
        on_depth_exceeded: &mut impl FnMut(usize) -> E,
    ) -> Result<(), E> {
        stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
            checkpoint()?;
            match self {
                Json::Bool(b) => emit(if *b { "true" } else { "false" })?,
                Json::Nat(n) => emit(&n.to_string())?,
                Json::Str(s) => emit_string(s, emit, checkpoint)?,
                Json::Arr(items) => {
                    if depth >= max_depth {
                        return Err(on_depth_exceeded(max_depth));
                    }
                    emit("[")?;
                    for (i, item) in items.iter().enumerate() {
                        checkpoint()?;
                        if i > 0 {
                            emit(",")?;
                        }
                        item.write_controlled(
                            depth + 1,
                            max_depth,
                            emit,
                            checkpoint,
                            on_depth_exceeded,
                        )?;
                        checkpoint()?;
                    }
                    emit("]")?;
                }
                Json::NodeReferences(items) => {
                    if depth >= max_depth || (!items.is_empty() && depth + 1 >= max_depth) {
                        return Err(on_depth_exceeded(max_depth));
                    }
                    emit("[")?;
                    for (i, index) in items.iter().enumerate() {
                        checkpoint()?;
                        if i > 0 {
                            emit(",")?;
                        }
                        emit("{")?;
                        emit_string("node", emit, checkpoint)?;
                        emit(":")?;
                        emit_string(&format!("n{index}"), emit, checkpoint)?;
                        emit("}")?;
                        checkpoint()?;
                    }
                    emit("]")?;
                }
                Json::Obj(entries) => {
                    if depth >= max_depth {
                        return Err(on_depth_exceeded(max_depth));
                    }
                    emit("{")?;
                    for (i, (k, v)) in entries.iter().enumerate() {
                        checkpoint()?;
                        if i > 0 {
                            emit(",")?;
                        }
                        emit_string(k, emit, checkpoint)?;
                        emit(":")?;
                        v.write_controlled(
                            depth + 1,
                            max_depth,
                            emit,
                            checkpoint,
                            on_depth_exceeded,
                        )?;
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
        // Numeric Ref arrays own no recursive Json children; their Vec drops normally.
        Json::NodeReferences(_) => {}
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
            Json::NodeReferences(items) => Json::NodeReferences(items.clone()),
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
            (Json::NodeReferences(a), Json::NodeReferences(b)) => a == b,
            (Json::NodeReferences(refs), Json::Arr(items))
            | (Json::Arr(items), Json::NodeReferences(refs)) => {
                refs.len() == items.len()
                    && refs
                        .iter()
                        .zip(items)
                        .all(|(index, item)| item.exact_node_reference() == Some(*index))
            }
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
        let expected_pretty = "{\n  \"a\": {\n    \"empty\": []\n  },\n  \"z\": [\n    false,\n    7\n  ],\n  \"é\": \"\\\"\\\\\\u000a/雪\"\n}";
        assert_eq!(value.pretty(), expected_pretty);
        let mut buf = Vec::new();
        value.write_pretty(&mut buf).unwrap();
        assert_eq!(String::from_utf8(buf).unwrap(), expected_pretty);
        assert!(example().try_pretty_with_max_depth(2).is_err());
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

#[cfg(test)]
mod reference_array_tests {
    use super::*;
    use crate::{
        control::{CheckFailure, Signal},
        issue::Issue,
    };
    use std::{cell::Cell, rc::Rc};
    type Failure = CheckFailure<Box<Issue>>;
    fn plain(indices: &[usize]) -> Json {
        Json::Arr(
            indices
                .iter()
                .map(|n| Json::obj([("node", Json::str(format!("n{n}")))]))
                .collect(),
        )
    }
    #[test]
    fn compact_reference_array_keeps_bytes_order_duplicates_and_json_layout() {
        for indices in [vec![], vec![0], vec![2, 1, 2, usize::MAX]] {
            let compact = Json::NodeReferences(indices.clone());
            let expanded = plain(&indices);
            assert_eq!(compact, expanded);
            assert_eq!(expanded, compact);
            assert_eq!(compact.clone(), compact);
            assert_eq!(compact.canonical(), expanded.canonical());
        }
        assert_ne!(Json::NodeReferences(vec![1, 2]), plain(&[2, 1]));
        assert_ne!(Json::NodeReferences(vec![1, 1]), plain(&[1]));
        #[cfg(target_pointer_width = "64")]
        assert_eq!(std::mem::size_of::<Json>(), 32);
    }
    #[test]
    fn compact_reference_array_does_not_alias_malformed_or_noncanonical_refs() {
        let compact = Json::NodeReferences(vec![1]);
        for item in [
            Json::obj([("node", Json::str("n01"))]),
            Json::obj([("node", Json::str("n+1"))]),
            Json::obj([("node", Json::str("n-1"))]),
            Json::obj([("node", Json::str(format!("n{}0", usize::MAX)))]),
            Json::obj([("node", Json::Nat(1))]),
            Json::obj([("node", Json::str("n1")), ("extra", Json::Bool(true))]),
            Json::str("n1"),
        ] {
            let expanded = Json::Arr(vec![item]);
            assert_ne!(compact, expanded);
            assert_ne!(expanded, compact);
        }
    }
    #[test]
    fn compact_reference_encoding_stops_inside_the_array() {
        let value = Json::NodeReferences(vec![1, 2, 1]);
        let count = Rc::new(Cell::new(0));
        let seen = count.clone();
        let control = Control::new(move |_| {
            seen.set(seen.get() + 1);
            None
        });
        assert_eq!(
            value
                .canonical_controlled::<Failure>(&control, Checkpoint::Expression)
                .unwrap(),
            plain(&[1, 2, 1]).canonical()
        );
        assert!(count.get() > 3);
        for at in 1..=count.get() {
            let mut visits = 0;
            let control = Control::new(move |_| {
                visits += 1;
                (visits == at).then_some(Signal::Term)
            });
            assert!(matches!(
                value.canonical_controlled::<Failure>(&control, Checkpoint::Expression),
                Err(Failure::Stopped(Signal::Term))
            ));
        }
    }
}
