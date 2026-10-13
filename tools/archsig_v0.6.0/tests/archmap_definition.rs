//! AC4・6・7: 独立定義の推移的 binding、未使用語彙、観測 Term の namespace scope。

mod common;
use archsig::archmap::{CheckedArchMap, Slot, Value, check_archmap};
use archsig::definition::CheckedDefinitions;
use archsig::issue::{Code, Issue};
use common::*;

fn binding(d: &CheckedDefinitions, ns: &str) -> String {
    let v = &d.vocabularies[ns];
    format!(
        r#"{{"namespace":"{ns}","version":"{}","digest":"{}"}}"#,
        v.version, v.digest
    )
}

fn document(bindings: &str, subjects: &str, atoms: &str) -> String {
    format!(
        r#"{{"format":"archsig.archmap/2","semantics":"archsig/0.6.0","vocabularies":[{bindings}],"sources":[],"origins":[{{"id":"o","mode":"specification","method":"仕様の小さい提示","locations":[],"note":"型と参照を検査する"}}],"snapshots":[{{"id":"s","origin":"o","subjects":[{subjects}],"atoms":[{atoms}]}}]}}"#
    )
}

fn subject(id: &str, ty: &str) -> String {
    format!(r#"{{"id":"{id}","type":"{ty}","origin":"o"}}"#)
}

fn atom(id: &str, sub: &str, field: &str, value: &str) -> String {
    format!(r#"{{"id":"{id}","subject":"{sub}","field":"{field}","value":{value},"origin":"o"}}"#)
}

fn accepted(d: &CheckedDefinitions, map: &str) -> CheckedArchMap {
    check_archmap(map.as_bytes(), d).unwrap_or_else(|e| panic!("{:?}", e.issue))
}

fn rejected(d: &CheckedDefinitions, map: &str) -> Issue {
    check_archmap(map.as_bytes(), d)
        .expect_err("ArchMap を拒否する")
        .issue
}

/// A.Item -> B.Boxed -> C.Leaf の型依存と、未使用 Extras.Note を保持する。
fn library() -> String {
    let c = vocabulary_json(
        "C",
        &format!(
            "[{}]",
            data_json("C.Leaf", &format!("[{}]", constructor_json("Leaf", "[]")))
        ),
        "[]",
    );
    let c_doc = definition_json(&format!("[{c}]"));
    let c_defs = definitions_ok(&[&c_doc]);
    let b = vocabulary_json(
        "B",
        &format!(
            "[{}]",
            data_json(
                "B.Boxed",
                &format!("[{}]", constructor_json("Box", r#"[["Data","C.Leaf"]]"#))
            )
        ),
        &format!("[{}]", binding(&c_defs, "C")),
    );
    let bc_doc = definition_json(&format!("[{b},{c}]"));
    let bc_defs = definitions_ok(&[&bc_doc]);
    let a = vocabulary_json(
        "A",
        &format!(
            "[{},{}]",
            data_json("A.Local", &format!("[{}]", constructor_json("Local", "[]"))),
            entity_json(
                "A.Item",
                "[]",
                &format!(
                    "[{},{},{}]",
                    field_json("boxed", r#"["Data","B.Boxed"]"#),
                    field_json("f", r#"["Term",[],"Z"]"#),
                    field_json("g", r#"["Term",[],["Data","A.Local"]]"#)
                )
            )
        ),
        &format!("[{}]", binding(&bc_defs, "B")),
    );
    let extra = vocabulary_json(
        "Extras",
        &format!(
            "[{}]",
            entity_json(
                "Extras.Note",
                "[]",
                &format!("[{}]", field_json("text", r#""Text""#))
            )
        ),
        "[]",
    );
    definition_json(&format!("[{a},{b},{c},{extra}]"))
}

#[test]
fn bindings_follow_subject_and_field_types_transitively() {
    let lib = library();
    let d = definitions_ok(&[&lib]);
    let abc = ["A", "B", "C"].map(|ns| binding(&d, ns)).join(",");
    let s = subject("i", "A.Item");
    let c = accepted(&d, &document(&abc, &s, ""));
    assert_eq!(c.vocabularies.len(), 3);
    assert_eq!(c.snapshots[0].subjects.len(), 1);
    assert_eq!(missing_slots(&c).len(), 3);
    // field の Atom を省略しても、その型の間接 namespace を binding する。
    for absent in ["A", "B", "C"] {
        let bs: Vec<_> = ["A", "B", "C"]
            .into_iter()
            .filter(|n| *n != absent)
            .map(|n| binding(&d, n))
            .collect();
        let issue = rejected(&d, &document(&bs.join(","), &s, ""));
        assert_eq!(
            (issue.code, pointer(&issue)),
            (Code::VocabularyMismatch, "/vocabularies")
        );
    }
    // subject がないと個体と slot を生成しない。
    let empty = accepted(&d, &document("", "", ""));
    assert!(empty.snapshots[0].subjects.is_empty());
}

#[test]
fn extra_bindings_are_checked_and_unused_observations_are_accepted() {
    let lib = library();
    let d = definitions_ok(&[&lib]);
    // Law は Counter のみ参照する。Extras の観測にも Counter の事実を要求しない。
    let defs = definitions_ok(&[COUNTER_DEFINITION, &lib]);
    archsig::law::check_law(COUNTER.as_bytes(), &defs).unwrap();
    let extra = binding(&d, "Extras");
    let count = binding(&defs, "Counter");
    let note = subject("note", "Extras.Note");
    let map = document(&format!("{extra},{count}"), &note, "");
    let c = accepted(&defs, &map);
    assert_eq!(c.snapshots[0].subjects.len(), 1);
    assert_eq!(missing_slots(&c)[0].2, "Extras.Note.text");
    assert_eq!(field(&c, "s", "note", "text").slot, Slot::Missing);
    for (from, to, code, ptr) in [
        (
            r#""namespace":"Counter""#.to_owned(),
            r#""namespace":"Absent""#.to_owned(),
            Code::Reference,
            "/vocabularies/1/namespace",
        ),
        (
            r#""version":"1""#.to_owned(),
            r#""version":"2""#.to_owned(),
            Code::VocabularyMismatch,
            "/vocabularies/0/version",
        ),
        (
            d.vocabularies["Extras"].digest.clone(),
            format!("sha256:{}", "0".repeat(64)),
            Code::VocabularyMismatch,
            "/vocabularies/0/digest",
        ),
    ] {
        let issue = rejected(&defs, &map.replacen(&from, &to, 1));
        assert_eq!((issue.code, pointer(&issue)), (code, ptr));
    }
    let duplicate = document(&format!("{extra},{extra}"), &note, "");
    let issue = rejected(&defs, &duplicate);
    assert_eq!(
        (issue.code, pointer(&issue)),
        (Code::DuplicateId, "/vocabularies/1/namespace")
    );
}

#[test]
fn observed_terms_use_the_definition_namespace_and_dependency_names() {
    let lib = library();
    let d = definitions_ok(&[&lib]);
    let abc = ["A", "B", "C"].map(|ns| binding(&d, ns)).join(",");
    let s = subject("i", "A.Item");
    let checked = |body: &str| {
        let val = format!(
            r#"{{"params":[],"body":{}}}"#,
            archsig::canonical::Json::str(body).canonical()
        );
        document(&abc, &s, &atom("f", "i", "A.Item.f", &val))
    };
    for body in [
        "match Local.Local { Local => 1; }",
        "match A.Local.Local { Local => 1; }",
        "match B.Boxed.Box(C.Leaf.Leaf) { B.Boxed.Box(x) => 1; }",
        "match C.Leaf.Leaf { C.Leaf.Leaf => 1; }",
    ] {
        let c = accepted(&d, &checked(body));
        assert!(matches!(
            field(&c, "s", "i", "f").slot,
            Slot::Known {
                value: Value::Term(_),
                ..
            }
        ));
    }
    // 戻り型に data があると、その期待型から定義元 constructor の短名を解決する。
    let short = document(
        &abc,
        &s,
        &atom("g", "i", "A.Item.g", r#"{"params":[],"body":"Local"}"#),
    );
    let c = accepted(&d, &short);
    assert!(matches!(
        field(&c, "s", "i", "g").slot,
        Slot::Known {
            value: Value::Term(_),
            ..
        }
    ));
    for body in [
        "match Leaf { Leaf => 1; }",
        "match Box(C.Leaf.Leaf) { Box(x) => 1; }",
        "v()",
        "Alias.v()",
        "Extras.Note",
    ] {
        let issue = rejected(&d, &checked(body));
        assert_eq!(issue.code, Code::Reference, "{body}: {issue:?}");
        assert_eq!(pointer(&issue), "/snapshots/0/atoms/0/value/body");
    }
}

#[test]
fn counter_known_high_count_and_missing_count_pass_the_static_check() {
    let original = include_str!("fixtures/counter.archmap.json");
    let high = original.replace(r#""value": "2""#, r#""value": "12""#);
    assert_ne!(high, original);
    let c = map_ok(COUNTER_DEFINITION, &high);
    assert!(
        matches!(field(&c, "v", "s", "count").slot, Slot::Known { value: Value::Z(ref n), .. } if n == &12.into())
    );
    let d = definitions_ok(&[COUNTER_DEFINITION]);
    let missing = document(&binding(&d, "Counter"), &subject("c", "Counter.State"), "");
    let c = accepted(&d, &missing);
    assert_eq!(missing_slots(&c).len(), 1);
    assert_eq!(field(&c, "s", "c", "count").slot, Slot::Missing);
    assert_eq!(missing_slots(&c)[0].3, &archsig::types::Type::Z);
}
