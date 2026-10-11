//! JSON 読込み(入力仕様 §1)。UTF-8・BOM・重複 key・unpaired surrogate を検査し、
//! 構文エラーは byte 区間、それ以外は JSON Pointer で位置を返す。

use crate::issue::{Code, Issue, Location};

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
    if bytes.starts_with(&[0xEF, 0xBB, 0xBF]) {
        return Err(syntax((0, 3), "BOM は使えない"));
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
    };
    p.ws();
    let v = p.value("")?;
    p.ws();
    if p.i != p.s.len() {
        return Err(syntax((p.i, p.s.len()), "JSON 値の後に余分な文字がある"));
    }
    Ok(v)
}

struct P<'a> {
    s: &'a [u8],
    text: &'a str,
    i: usize,
}

impl P<'_> {
    fn ws(&mut self) {
        while self.i < self.s.len() && matches!(self.s[self.i], b' ' | b'\t' | b'\n' | b'\r') {
            self.i += 1;
        }
    }

    fn here(&self) -> Span {
        let len = self.text[self.i.min(self.s.len())..]
            .chars()
            .next()
            .map_or(0, char::len_utf8);
        (self.i, self.i + len)
    }

    fn value(&mut self, pointer: &str) -> Result<JNode, Box<Issue>> {
        stacker::maybe_grow(128 * 1024, 4 * 1024 * 1024, || self.value_inner(pointer))
    }

    fn value_inner(&mut self, pointer: &str) -> Result<JNode, Box<Issue>> {
        let Some(&c) = self.s.get(self.i) else {
            return Err(syntax(self.here(), "JSON 値が必要"));
        };
        let value = match c {
            b'{' => {
                self.i += 1;
                let mut entries: Vec<(String, JNode)> = Vec::new();
                let mut keys = std::collections::HashSet::new();
                self.ws();
                if self.s.get(self.i) == Some(&b'}') {
                    self.i += 1;
                } else {
                    loop {
                        self.ws();
                        if self.s.get(self.i) != Some(&b'"') {
                            return Err(syntax(self.here(), "object の key は文字列"));
                        }
                        let key = self.string()?;
                        let child = pointer_push(pointer, &key);
                        if !keys.insert(key.clone()) {
                            return Err(Box::new(Issue {
                                code: Code::DuplicateKey,
                                message: format!("key `{key}` が重複している"),
                                location: Location::ArchMap {
                                    pointer: child,
                                    span: None,
                                },
                                details: crate::issue::Details::Empty,
                            }));
                        }
                        self.ws();
                        if self.s.get(self.i) != Some(&b':') {
                            return Err(syntax(self.here(), "`:` が必要"));
                        }
                        self.i += 1;
                        self.ws();
                        let v = self.value(&child)?;
                        entries.push((key, v));
                        self.ws();
                        match self.s.get(self.i) {
                            Some(b',') => self.i += 1,
                            Some(b'}') => {
                                self.i += 1;
                                break;
                            }
                            _ => return Err(syntax(self.here(), "`,` か `}` が必要")),
                        }
                    }
                }
                JValue::Obj(entries)
            }
            b'[' => {
                self.i += 1;
                let mut items = Vec::new();
                self.ws();
                if self.s.get(self.i) == Some(&b']') {
                    self.i += 1;
                } else {
                    loop {
                        self.ws();
                        let child = pointer_push(pointer, &items.len().to_string());
                        items.push(self.value(&child)?);
                        self.ws();
                        match self.s.get(self.i) {
                            Some(b',') => self.i += 1,
                            Some(b']') => {
                                self.i += 1;
                                break;
                            }
                            _ => return Err(syntax(self.here(), "`,` か `]` が必要")),
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
            _ => return Err(syntax(self.here(), "JSON 値が必要")),
        };
        Ok(JNode { value })
    }

    fn number(&mut self) -> Result<String, Box<Issue>> {
        let start = self.i;
        let digits = |p: &mut Self| {
            let s = p.i;
            while p.i < p.s.len() && p.s[p.i].is_ascii_digit() {
                p.i += 1;
            }
            p.i > s
        };
        if self.s[self.i] == b'-' {
            self.i += 1;
        }
        if self.s.get(self.i) == Some(&b'0') {
            self.i += 1;
        } else if !digits(self) {
            return Err(syntax((start, self.i), "不正な number"));
        }
        if self.s.get(self.i) == Some(&b'.') {
            self.i += 1;
            if !digits(self) {
                return Err(syntax((start, self.i), "不正な number"));
            }
        }
        if matches!(self.s.get(self.i), Some(b'e' | b'E')) {
            self.i += 1;
            if matches!(self.s.get(self.i), Some(b'+' | b'-')) {
                self.i += 1;
            }
            if !digits(self) {
                return Err(syntax((start, self.i), "不正な number"));
            }
        }
        let text = self.text[start..self.i].to_owned();
        if !text.parse::<f64>().is_ok_and(f64::is_finite) {
            return Err(syntax((start, self.i), "非有限の number"));
        }
        Ok(text)
    }

    fn string(&mut self) -> Result<String, Box<Issue>> {
        let start = self.i;
        self.i += 1;
        let mut out = String::new();
        loop {
            let Some(&c) = self.s.get(self.i) else {
                return Err(syntax((start, self.s.len()), "文字列が閉じていない"));
            };
            match c {
                b'"' => {
                    self.i += 1;
                    return Ok(out);
                }
                b'\\' => {
                    let at = self.i;
                    let Some(&e) = self.s.get(self.i + 1) else {
                        return Err(syntax((at, self.s.len()), "文字列が閉じていない"));
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
                                return Err(syntax((at, self.i), "unpaired surrogate"));
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
                        _ => return Err(syntax((at, at + 2), "不正な escape")),
                    }
                }
                c if c < 0x20 => {
                    return Err(syntax(
                        (self.i, self.i + 1),
                        "文字列内の制御文字は escape する",
                    ));
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
