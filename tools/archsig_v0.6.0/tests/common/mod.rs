#![allow(dead_code)]

pub mod cli;
pub mod completion_stops;
pub mod law_definitions;
pub mod map_scope;

use archsig::archmap::{CheckedArchMap, Field, Slot};
use archsig::issue::Issue;
use archsig::law::{CheckedLaw, check_law};
use archsig::types::Type;

pub const HEADER: &str = "law \"archsig.law/2\" semantics \"archsig/0.6.0\";\n";
pub const RESERVATIONS: &str = include_str!("../fixtures/reservations.law");
pub const ENGINE: &str = include_str!("../fixtures/engine.law");
pub const COUNTER: &str = include_str!("../fixtures/counter.law");
pub const RESERVATIONS_DEFINITION: &str = include_str!("../fixtures/reservations.atoms.json");
pub const ENGINE_DEFINITION: &str = include_str!("../fixtures/engine.atoms.json");
pub const COUNTER_DEFINITION: &str = include_str!("../fixtures/counter.atoms.json");
pub const COUNTER_LIBRARY: &str = include_str!("../fixtures/counter-library.atoms.json");
pub const EMPTY_DEFINITION: &str = r#"{"format":"archsig.atom-definition/1","semantics":"archsig/0.6.0","vocabularies":[{"semantics":"archsig/0.6.0","namespace":"Unused","version":"1","dependencies":[],"declarations":[]}]}"#;

pub fn definitions_ok(inputs: &[&str]) -> archsig::definition::CheckedDefinitions {
    let ids: Vec<_> = (0..inputs.len())
        .map(|i| format!("definition{i}"))
        .collect();
    let files: Vec<_> = inputs
        .iter()
        .zip(&ids)
        .map(|(src, id)| (id.as_str(), src.as_bytes()))
        .collect();
    archsig::definition::check_definitions(&files)
        .unwrap_or_else(|e| panic!("定義の検査: {:?}", e.issue))
}
pub fn ok(definition: &str, src: &str) -> CheckedLaw {
    check_law(src.as_bytes(), &definitions_ok(&[definition]))
        .unwrap_or_else(|e| panic!("検査が通るはず: {:?}\n{src}", e.issue))
}
pub fn err(definition: &str, src: &str) -> Issue {
    check_law(src.as_bytes(), &definitions_ok(&[definition]))
        .expect_err("Law の検査が落ちるはず")
        .issue
}
pub fn reading(body: &str) -> String {
    format!("{HEADER}reading R {{\n{body}\n}}\n")
}
pub fn reading_with(namespace: &str, digest: &str, body: &str) -> String {
    reading(&format!(
        "use vocabulary {namespace} version \"1\" digest \"{digest}\";\n{body}"
    ))
}
fn quoted(text: &str) -> String {
    archsig::canonical::Json::str(text).canonical()
}
pub fn definition_json(vocabularies: &str) -> String {
    format!(
        r#"{{"format":"archsig.atom-definition/1","semantics":"archsig/0.6.0","vocabularies":{vocabularies}}}"#
    )
}
pub fn vocabulary_json(namespace: &str, declarations: &str, dependencies: &str) -> String {
    format!(
        r#"{{"semantics":"archsig/0.6.0","namespace":{},"version":"1","dependencies":{dependencies},"declarations":{declarations}}}"#,
        quoted(namespace)
    )
}
pub fn entity_json(name: &str, parameters: &str, fields: &str) -> String {
    format!(
        r#"{{"kind":"entity","name":{},"meaning":"test entity","parameters":{parameters},"fields":{fields},"alignments":[]}}"#,
        quoted(name)
    )
}
pub fn field_json(name: &str, type_json: &str) -> String {
    format!(
        r#"{{"name":{},"type":{type_json},"meaning":"test field"}}"#,
        quoted(name)
    )
}
pub fn data_json(name: &str, constructors: &str) -> String {
    format!(
        r#"{{"kind":"data","name":{},"meaning":"test data","constructors":{constructors}}}"#,
        quoted(name)
    )
}
pub fn constructor_json(name: &str, args: &str) -> String {
    format!(
        r#"{{"name":{},"arguments":{args},"meaning":"test constructor"}}"#,
        quoted(name)
    )
}

pub fn span_text(src: &str, span: (usize, usize)) -> &str {
    &src[span.0..span.1]
}

pub const RESERVATIONS_MAP: &str = include_str!("../fixtures/reservations.archmap.json");
pub const ENGINE_MAP: &str = include_str!("../fixtures/engine.archmap.json");

pub fn map_ok(definition: &str, map: &str) -> CheckedArchMap {
    archsig::archmap::check_archmap(map.as_bytes(), &definitions_ok(&[definition]))
        .unwrap_or_else(|e| panic!("ArchMap の検査: {:?}\n{map}", e.issue))
}
pub fn map_err(definition: &str, map: &str) -> Issue {
    archsig::archmap::check_archmap(map.as_bytes(), &definitions_ok(&[definition]))
        .expect_err("ArchMap の検査が落ちるはず")
        .issue
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
