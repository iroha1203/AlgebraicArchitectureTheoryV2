//! Law の字句(Law 仕様 §1)。空白と `//` コメントを除き、字句列を元の順に保持する。

use crate::issue::{Code, Issue};
use crate::json::InputError;
use crate::observed::control::{Checkpoint, Control};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TokenKind {
    Name,
    Str,
    Int,
    Sym,
}

impl TokenKind {
    pub fn wire(self) -> &'static str {
        match self {
            TokenKind::Name => "name",
            TokenKind::Str => "string",
            TokenKind::Int => "integer",
            TokenKind::Sym => "symbol",
        }
    }
}

/// `text` は name・integer・symbol では元の綴り、string では escape を解いた値。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Token {
    pub kind: TokenKind,
    pub text: String,
    pub span: (usize, usize),
}

const SYMBOLS2: [&str; 5] = ["=>", "->", "!=", "<=", ">="];
const SYMBOLS1: &str = ";{}()[]<>,:.=|+-*_";

/// UTF-8・BOM を確かめてから字句に分ける。
pub fn lex(bytes: &[u8]) -> Result<Vec<Token>, Box<Issue>> {
    lex_up_to(bytes, usize::MAX)
}

/// 先頭から `max` 個までの字句。header の版を、残りの字句より先に読むために使う。
pub fn lex_up_to(bytes: &[u8], max: usize) -> Result<Vec<Token>, Box<Issue>> {
    lex_inner(
        bytes,
        max,
        &mut Control::unlimited(),
        Checkpoint::LawIteration,
    )
}
pub(super) fn lex_inner<E: InputError>(
    bytes: &[u8],
    max: usize,
    control: &mut Control,
    point: Checkpoint,
) -> Result<Vec<Token>, E> {
    E::checkpoint(control, point)?;
    if bytes.starts_with(&[0xEF, 0xBB, 0xBF]) {
        return Err((Box::new(Issue::law(Code::Syntax, (0, 3), "BOM は使えない"))).into());
    }
    let text = std::str::from_utf8(bytes).map_err(|e| {
        let at = e.valid_up_to();
        let end = at + e.error_len().unwrap_or(bytes.len() - at);
        Box::new(Issue::law(Code::Syntax, (at, end), "不正な UTF-8"))
    })?;
    let src = text.as_bytes();
    let mut tokens = Vec::new();
    let mut i = 0;
    while i < src.len() && tokens.len() < max {
        E::checkpoint(control, point)?;
        let c = src[i];
        if matches!(c, b' ' | b'\t' | b'\r' | b'\n') {
            i += 1;
        } else if src[i..].starts_with(b"//") {
            while i < src.len() && src[i] != b'\n' {
                E::checkpoint(control, point)?;
                i += 1;
            }
        } else if c.is_ascii_alphabetic() {
            let start = i;
            while i < src.len() && (src[i].is_ascii_alphanumeric() || src[i] == b'_') {
                E::checkpoint(control, point)?;
                i += 1;
            }
            tokens.push(Token {
                kind: TokenKind::Name,
                text: text[start..i].to_owned(),
                span: (start, i),
            });
        } else if c.is_ascii_digit() {
            let start = i;
            while i < src.len() && src[i].is_ascii_digit() {
                E::checkpoint(control, point)?;
                i += 1;
            }
            if c == b'0' && i - start > 1 {
                return Err((Box::new(Issue::law(
                    Code::Syntax,
                    (start, i),
                    "整数に先頭の0は置けない",
                )))
                .into());
            }
            tokens.push(Token {
                kind: TokenKind::Int,
                text: text[start..i].to_owned(),
                span: (start, i),
            });
        } else if c == b'"' {
            let (value, end) = lex_string::<E>(text, i, control, point)?;
            tokens.push(Token {
                kind: TokenKind::Str,
                text: value,
                span: (i, end),
            });
            i = end;
        } else if let Some(s) = SYMBOLS2.iter().find(|s| src[i..].starts_with(s.as_bytes())) {
            tokens.push(Token {
                kind: TokenKind::Sym,
                text: (*s).to_owned(),
                span: (i, i + 2),
            });
            i += 2;
        } else if c.is_ascii() && SYMBOLS1.as_bytes().contains(&c) {
            tokens.push(Token {
                kind: TokenKind::Sym,
                text: (c as char).to_string(),
                span: (i, i + 1),
            });
            i += 1;
        } else {
            let len = text[i..].chars().next().map_or(1, char::len_utf8);
            return Err((Box::new(Issue::law(
                Code::Syntax,
                (i, i + len),
                "字句として読めない文字",
            )))
            .into());
        }
    }
    Ok(tokens)
}

/// JSON の string 文法。制御文字の生の出現と unpaired surrogate を拒否する。
fn lex_string<E: InputError>(
    text: &str,
    start: usize,
    control: &mut Control,
    point: Checkpoint,
) -> Result<(String, usize), E> {
    let src = text.as_bytes();
    let mut out = String::new();
    let mut i = start + 1;
    loop {
        E::checkpoint(control, point)?;
        let Some(&c) = src.get(i) else {
            return Err((Box::new(Issue::law(
                Code::Syntax,
                (start, src.len()),
                "文字列が閉じていない",
            )))
            .into());
        };
        match c {
            b'"' => return Ok((out, i + 1)),
            b'\\' => {
                let esc = *src.get(i + 1).ok_or_else(|| {
                    Box::new(Issue::law(
                        Code::Syntax,
                        (i, src.len()),
                        "文字列が閉じていない",
                    ))
                })?;
                match esc {
                    b'"' => out.push('"'),
                    b'\\' => out.push('\\'),
                    b'/' => out.push('/'),
                    b'b' => out.push('\u{8}'),
                    b'f' => out.push('\u{c}'),
                    b'n' => out.push('\n'),
                    b'r' => out.push('\r'),
                    b't' => out.push('\t'),
                    b'u' => {
                        let hi = hex4(src, i + 2).ok_or_else(|| {
                            Box::new(Issue::law(
                                Code::Syntax,
                                (i, (i + 6).min(src.len())),
                                "不正な \\u escape",
                            ))
                        })?;
                        if (0xDC00..0xE000).contains(&hi) {
                            return Err((Box::new(Issue::law(
                                Code::Syntax,
                                (i, i + 6),
                                "unpaired surrogate",
                            )))
                            .into());
                        }
                        if (0xD800..0xDC00).contains(&hi) {
                            let lo = (src.get(i + 6) == Some(&b'\\')
                                && src.get(i + 7) == Some(&b'u'))
                            .then(|| hex4(src, i + 8))
                            .flatten()
                            .filter(|lo| (0xDC00..0xE000).contains(lo))
                            .ok_or_else(|| {
                                Box::new(Issue::law(Code::Syntax, (i, i + 6), "unpaired surrogate"))
                            })?;
                            let c = 0x10000 + ((hi - 0xD800) << 10) + (lo - 0xDC00);
                            out.push(char::from_u32(c).expect("surrogate pair は scalar を作る"));
                            i += 12;
                        } else {
                            out.push(char::from_u32(hi).expect("surrogate 以外は scalar"));
                            i += 6;
                        }
                        continue;
                    }
                    _ => {
                        return Err((Box::new(Issue::law(
                            Code::Syntax,
                            (i, i + 2),
                            "不正な escape",
                        )))
                        .into());
                    }
                }
                i += 2;
            }
            c if c < 0x20 => {
                return Err((Box::new(Issue::law(
                    Code::Syntax,
                    (i, i + 1),
                    "文字列内の制御文字は escape する",
                )))
                .into());
            }
            _ => {
                let ch = text[i..].chars().next().expect("UTF-8 確認済み");
                out.push(ch);
                i += ch.len_utf8();
            }
        }
    }
}

fn hex4(src: &[u8], at: usize) -> Option<u32> {
    let digits = src.get(at..at + 4)?;
    let s = std::str::from_utf8(digits).ok()?;
    if !s.bytes().all(|b| b.is_ascii_hexdigit()) {
        return None;
    }
    u32::from_str_radix(s, 16).ok()
}
