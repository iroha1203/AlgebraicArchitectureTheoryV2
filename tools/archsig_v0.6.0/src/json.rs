//! JSON 読込み(入力仕様 §1)。UTF-8・BOM・重複 key・unpaired surrogate を検査し、
//! 構文エラーは byte 区間、それ以外は JSON Pointer で位置を返す。

use crate::issue::{Code, Issue, Location};
use crate::observed::control::{CheckFailure, Checkpoint, Control};

impl From<Box<Issue>> for CheckFailure<Box<Issue>> {
    fn from(issue: Box<Issue>) -> Self {
        Self::Input(issue)
    }
}

/// Internal error policy shared by ordinary and interruptible input readers.
#[doc(hidden)]
pub trait InputError: From<Box<Issue>> {
    fn checkpoint(control: &mut Control, point: Checkpoint) -> Result<(), Self>;
    fn map_issue(self, map: impl FnOnce(Box<Issue>) -> Box<Issue>) -> Self;
    fn is_stopped(&self) -> bool {
        false
    }
}
impl InputError for Box<Issue> {
    fn checkpoint(_: &mut Control, _: Checkpoint) -> Result<(), Self> {
        Ok(())
    }
    fn map_issue(self, map: impl FnOnce(Box<Issue>) -> Box<Issue>) -> Self {
        map(self)
    }
}
impl InputError for CheckFailure<Box<Issue>> {
    fn checkpoint(control: &mut Control, point: Checkpoint) -> Result<(), Self> {
        control.checkpoint(point).map_err(CheckFailure::Stopped)
    }
    fn map_issue(self, map: impl FnOnce(Box<Issue>) -> Box<Issue>) -> Self {
        match self {
            Self::Input(issue) => Self::Input(map(issue)),
            Self::Stopped(reason) => Self::Stopped(reason),
        }
    }
    fn is_stopped(&self) -> bool {
        matches!(self, Self::Stopped(_))
    }
}

pub type Span = (usize, usize);

#[derive(Debug, PartialEq, Eq)]
pub enum JValue {
    Null,
    Bool(bool),
    /// 元の綴りの number。
    Num(String),
    Str(String),
    Arr(Vec<JNode>),
    /// key と値。元の順。
    Obj(Vec<(String, JNode)>),
}

#[derive(Debug, PartialEq, Eq)]
pub struct JNode {
    pub value: JValue,
}

impl Drop for JNode {
    fn drop(&mut self) {
        let mut stack = Vec::new();
        take(&mut self.value, &mut stack);
        while let Some(mut n) = stack.pop() {
            take(&mut n.value, &mut stack);
        }
    }
}

fn take(v: &mut JValue, stack: &mut Vec<JNode>) {
    match v {
        JValue::Arr(items) => stack.append(items),
        JValue::Obj(entries) => stack.extend(std::mem::take(entries).into_iter().map(|(_, n)| n)),
        _ => {}
    }
}

/// JSON Pointer の一つの参照段。
pub fn pointer_push(base: &str, token: &str) -> String {
    format!("{base}/{}", token.replace('~', "~0").replace('/', "~1"))
}

fn syntax(span: Span, message: impl Into<String>) -> Box<Issue> {
    Box::new(Issue {
        code: Code::Syntax,
        message: message.into(),
        location: Location::ArchMap {
            pointer: String::new(),
            span: Some(span),
        },
        details: crate::issue::Details::Empty,
    })
}

pub fn parse(bytes: &[u8]) -> Result<JNode, Box<Issue>> {
    parse_inner(
        bytes,
        &mut Control::unlimited(),
        Checkpoint::ArchMapIteration,
    )
}

pub(crate) fn parse_inner<E: InputError>(
    bytes: &[u8],
    control: &mut Control,
    point: Checkpoint,
) -> Result<JNode, E> {
    E::checkpoint(control, point)?;
    if bytes.starts_with(&[0xEF, 0xBB, 0xBF]) {
        return Err((syntax((0, 3), "BOM は使えない")).into());
    }
    let text = std::str::from_utf8(bytes).map_err(|e| {
        let at = e.valid_up_to();
        syntax(
            (at, at + e.error_len().unwrap_or(bytes.len() - at)),
            "不正な UTF-8",
        )
    })?;
    let mut p = P {
        s: text.as_bytes(),
        text,
        i: 0,
        control,
        point,
        error: std::marker::PhantomData::<E>,
    };
    p.ws()?;
    let v = p.value("")?;
    p.ws()?;
    if p.i != p.s.len() {
        return Err((syntax((p.i, p.s.len()), "JSON 値の後に余分な文字がある")).into());
    }
    Ok(v)
}

struct P<'a, 'c, E> {
    s: &'a [u8],
    text: &'a str,
    i: usize,
    control: &'c mut Control,
    point: Checkpoint,
    error: std::marker::PhantomData<E>,
}

impl<E: InputError> P<'_, '_, E> {
    fn checkpoint(&mut self) -> Result<(), E> {
        E::checkpoint(self.control, self.point)
    }
    fn ws(&mut self) -> Result<(), E> {
        while self.i < self.s.len() && matches!(self.s[self.i], b' ' | b'\t' | b'\n' | b'\r') {
            self.checkpoint()?;
            self.i += 1;
        }
        Ok(())
    }

    fn here(&self) -> Span {
        let len = self.text[self.i.min(self.s.len())..]
            .chars()
            .next()
            .map_or(0, char::len_utf8);
        (self.i, self.i + len)
    }

    fn value(&mut self, pointer: &str) -> Result<JNode, E> {
        self.checkpoint()?;
        stacker::maybe_grow(128 * 1024, 4 * 1024 * 1024, || self.value_inner(pointer))
    }

    fn value_inner(&mut self, pointer: &str) -> Result<JNode, E> {
        let Some(&c) = self.s.get(self.i) else {
            return Err((syntax(self.here(), "JSON 値が必要")).into());
        };
        let value = match c {
            b'{' => {
                self.i += 1;
                let mut entries: Vec<(String, JNode)> = Vec::new();
                let mut keys = std::collections::HashSet::new();
                self.ws()?;
                if self.s.get(self.i) == Some(&b'}') {
                    self.i += 1;
                } else {
                    loop {
                        self.ws()?;
                        if self.s.get(self.i) != Some(&b'"') {
                            return Err((syntax(self.here(), "object の key は文字列")).into());
                        }
                        let key = self.string()?;
                        let child = pointer_push(pointer, &key);
                        if !keys.insert(key.clone()) {
                            return Err((Box::new(Issue {
                                code: Code::DuplicateKey,
                                message: format!("key `{key}` が重複している"),
                                location: Location::ArchMap {
                                    pointer: child,
                                    span: None,
                                },
                                details: crate::issue::Details::Empty,
                            }))
                            .into());
                        }
                        self.ws()?;
                        if self.s.get(self.i) != Some(&b':') {
                            return Err((syntax(self.here(), "`:` が必要")).into());
                        }
                        self.i += 1;
                        self.ws()?;
                        let v = self.value(&child)?;
                        entries.push((key, v));
                        self.ws()?;
                        match self.s.get(self.i) {
                            Some(b',') => self.i += 1,
                            Some(b'}') => {
                                self.i += 1;
                                break;
                            }
                            _ => return Err((syntax(self.here(), "`,` か `}` が必要")).into()),
                        }
                    }
                }
                JValue::Obj(entries)
            }
            b'[' => {
                self.i += 1;
                let mut items = Vec::new();
                self.ws()?;
                if self.s.get(self.i) == Some(&b']') {
                    self.i += 1;
                } else {
                    loop {
                        self.ws()?;
                        let child = pointer_push(pointer, &items.len().to_string());
                        items.push(self.value(&child)?);
                        self.ws()?;
                        match self.s.get(self.i) {
                            Some(b',') => self.i += 1,
                            Some(b']') => {
                                self.i += 1;
                                break;
                            }
                            _ => return Err((syntax(self.here(), "`,` か `]` が必要")).into()),
                        }
                    }
                }
                JValue::Arr(items)
            }
            b'"' => JValue::Str(self.string()?),
            b't' if self.s[self.i..].starts_with(b"true") => {
                self.i += 4;
                JValue::Bool(true)
            }
            b'f' if self.s[self.i..].starts_with(b"false") => {
                self.i += 5;
                JValue::Bool(false)
            }
            b'n' if self.s[self.i..].starts_with(b"null") => {
                self.i += 4;
                JValue::Null
            }
            b'-' | b'0'..=b'9' => JValue::Num(self.number()?),
            _ => return Err((syntax(self.here(), "JSON 値が必要")).into()),
        };
        Ok(JNode { value })
    }

    fn number(&mut self) -> Result<String, E> {
        let start = self.i;
        let digits = |p: &mut Self| -> Result<bool, E> {
            let s = p.i;
            while p.i < p.s.len() && p.s[p.i].is_ascii_digit() {
                p.checkpoint()?;
                p.i += 1;
            }
            Ok(p.i > s)
        };
        if self.s[self.i] == b'-' {
            self.i += 1;
        }
        if self.s.get(self.i) == Some(&b'0') {
            self.i += 1;
        } else if !digits(self)? {
            return Err((syntax((start, self.i), "不正な number")).into());
        }
        if self.s.get(self.i) == Some(&b'.') {
            self.i += 1;
            if !digits(self)? {
                return Err((syntax((start, self.i), "不正な number")).into());
            }
        }
        if matches!(self.s.get(self.i), Some(b'e' | b'E')) {
            self.i += 1;
            if matches!(self.s.get(self.i), Some(b'+' | b'-')) {
                self.i += 1;
            }
            if !digits(self)? {
                return Err((syntax((start, self.i), "不正な number")).into());
            }
        }
        let text = self.text[start..self.i].to_owned();
        if !text.parse::<f64>().is_ok_and(f64::is_finite) {
            return Err((syntax((start, self.i), "非有限の number")).into());
        }
        Ok(text)
    }

    fn string(&mut self) -> Result<String, E> {
        let start = self.i;
        self.i += 1;
        let mut out = String::new();
        loop {
            self.checkpoint()?;
            let Some(&c) = self.s.get(self.i) else {
                return Err((syntax((start, self.s.len()), "文字列が閉じていない")).into());
            };
            match c {
                b'"' => {
                    self.i += 1;
                    return Ok(out);
                }
                b'\\' => {
                    let at = self.i;
                    let Some(&e) = self.s.get(self.i + 1) else {
                        return Err((syntax((at, self.s.len()), "文字列が閉じていない")).into());
                    };
                    self.i += 2;
                    match e {
                        b'"' => out.push('"'),
                        b'\\' => out.push('\\'),
                        b'/' => out.push('/'),
                        b'b' => out.push('\u{8}'),
                        b'f' => out.push('\u{c}'),
                        b'n' => out.push('\n'),
                        b'r' => out.push('\r'),
                        b't' => out.push('\t'),
                        b'u' => {
                            let hi = self.hex4().ok_or_else(|| {
                                syntax((at, self.i.min(self.s.len())), "不正な \\u escape")
                            })?;
                            if (0xDC00..0xE000).contains(&hi) {
                                return Err((syntax((at, self.i), "unpaired surrogate")).into());
                            }
                            if (0xD800..0xDC00).contains(&hi) {
                                let lo = (self.s.get(self.i) == Some(&b'\\')
                                    && self.s.get(self.i + 1) == Some(&b'u'))
                                .then(|| {
                                    self.i += 2;
                                    self.hex4()
                                })
                                .flatten()
                                .filter(|lo| (0xDC00..0xE000).contains(lo))
                                .ok_or_else(|| syntax((at, at + 6), "unpaired surrogate"))?;
                                let c = 0x10000 + ((hi - 0xD800) << 10) + (lo - 0xDC00);
                                out.push(
                                    char::from_u32(c).expect("surrogate pair は scalar を作る"),
                                );
                            } else {
                                out.push(char::from_u32(hi).expect("surrogate 以外は scalar"));
                            }
                        }
                        _ => return Err((syntax((at, at + 2), "不正な escape")).into()),
                    }
                }
                c if c < 0x20 => {
                    return Err(
                        (syntax((self.i, self.i + 1), "文字列内の制御文字は escape する")).into(),
                    );
                }
                _ => {
                    let ch = self.text[self.i..].chars().next().expect("UTF-8 確認済み");
                    out.push(ch);
                    self.i += ch.len_utf8();
                }
            }
        }
    }

    fn hex4(&mut self) -> Option<u32> {
        let digits = self.s.get(self.i..self.i + 4)?;
        if !digits.iter().all(u8::is_ascii_hexdigit) {
            return None;
        }
        self.i += 4;
        u32::from_str_radix(std::str::from_utf8(digits).ok()?, 16).ok()
    }
}

/// 同じ JSON 構文検査を、明示した定義入力の識別へ接続する。
pub fn parse_definition(bytes: &[u8], input: &str) -> Result<JNode, Box<Issue>> {
    parse(bytes).map_err(|mut issue| {
        if let Location::ArchMap { pointer, span } = &issue.location {
            issue.location = Location::Definition {
                input: input.to_owned(),
                pointer: pointer.clone(),
                span: *span,
            };
        }
        issue
    })
}

pub(crate) fn parse_definition_inner<E: InputError>(
    bytes: &[u8],
    input: &str,
    control: &mut Control,
) -> Result<JNode, E> {
    parse_inner::<E>(bytes, control, Checkpoint::DefinitionIteration).map_err(|failure| {
        failure.map_issue(|mut issue| {
            if let Location::ArchMap { pointer, span } = &issue.location {
                issue.location = Location::Definition {
                    input: input.into(),
                    pointer: pointer.clone(),
                    span: *span,
                };
            }
            issue
        })
    })
}
