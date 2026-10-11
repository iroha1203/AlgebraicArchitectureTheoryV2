#![allow(dead_code)]

use archsig::archmap::{CheckedArchMap, Field, Slot};
use archsig::issue::Issue;
use archsig::law::{CheckedLaw, check_law};
use archsig::types::Type;

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

pub const RESERVATIONS_MAP: &str = include_str!("../fixtures/reservations.archmap.json");
pub const ENGINE_MAP: &str = include_str!("../fixtures/engine.archmap.json");

pub fn map_ok(law: &str, map: &str) -> archsig::archmap::CheckedArchMap {
    let l = ok(law);
    match archsig::archmap::check_archmap(map.as_bytes(), &l) {
        Ok(c) => c,
        Err(e) => panic!("ArchMap の検査が通るはず: {:?}\n{map}", e.issue),
    }
}

pub fn map_err(law: &str, map: &str) -> Issue {
    let l = ok(law);
    match archsig::archmap::check_archmap(map.as_bytes(), &l) {
        Ok(_) => panic!("ArchMap の検査が落ちるはず:\n{map}"),
        Err(e) => e.issue,
    }
}

pub fn pointer(issue: &Issue) -> &str {
    match &issue.location {
        archsig::issue::Location::ArchMap { pointer, .. } => pointer,
        other => panic!("ArchMap の位置ではない: {other:?}"),
    }
}

/// 欠測 slot の identity `(snapshot, subject, field)` と型。
pub fn missing_slots(c: &CheckedArchMap) -> Vec<(&str, &str, &str, &Type)> {
    let mut out = Vec::new();
    for s in &c.snapshots {
        for sub in &s.subjects {
            for f in &sub.fields {
                if f.slot == Slot::Missing {
                    out.push((s.id.as_str(), sub.id.as_str(), f.name.as_str(), &f.ty));
                }
            }
        }
    }
    out
}

/// subject の field を短名で引く。
pub fn field<'a>(c: &'a CheckedArchMap, snapshot: &str, id: &str, name: &str) -> &'a Field {
    let s = c.snapshots.iter().find(|s| s.id == snapshot).unwrap();
    let sub = s.subjects.iter().find(|s| s.id == id).unwrap();
    sub.fields
        .iter()
        .find(|f| f.name.rsplit('.').next() == Some(name))
        .unwrap()
}
