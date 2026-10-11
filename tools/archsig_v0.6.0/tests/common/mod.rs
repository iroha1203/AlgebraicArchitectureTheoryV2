#![allow(dead_code)]

use archsig::issue::Issue;
use archsig::law::{CheckedLaw, check_law};

pub const HEADER: &str = "law \"archsig.law/1\" semantics \"archsig/0.6.0\";\n";

pub const RESERVATIONS: &str = include_str!("../fixtures/reservations.law");
pub const ENGINE: &str = include_str!("../fixtures/engine.law");

pub fn ok(src: &str) -> CheckedLaw {
    match check_law(src.as_bytes()) {
        Ok(c) => c,
        Err(e) => panic!("検査が通るはず: {:?}\n{src}", e.issue),
    }
}

pub fn err(src: &str) -> Issue {
    match check_law(src.as_bytes()) {
        Ok(_) => panic!("検査が落ちるはず:\n{src}"),
        Err(e) => e.issue,
    }
}

/// reading を一つ持つ Law。
pub fn reading(body: &str) -> String {
    format!("{HEADER}reading R {{\n{body}\n}}\n")
}

pub fn span_text(src: &str, span: (usize, usize)) -> &str {
    &src[span.0..span.1]
}
