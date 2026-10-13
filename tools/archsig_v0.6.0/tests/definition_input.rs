use archsig::{
    definition::{self, CheckedDefinitions, PrimitiveSignature},
    issue::{Code, Location},
};
const COUNTER: &str = include_str!("fixtures/counter.atoms.json");
const LIBRARY: &str = include_str!("fixtures/counter-library.atoms.json");
const DIGEST: &str = "sha256:388baddb5f87b80f4448ce9be21a4800c92a11001ab356936b14b6d5fb438a11";
fn check(s: &str) -> CheckedDefinitions {
    definition::check_definitions(&[("definition0", s.as_bytes())]).unwrap()
}
fn fail(s: &str, code: Code, pointer: &str) {
    let failure = definition::check_definitions(&[("definition0", s.as_bytes())]).unwrap_err();
    assert_eq!(failure.issue.code, code, "{}", failure.issue.message);
    assert_eq!(failure.inputs.len(), 1);
    assert_eq!(
        failure.issue.location,
        Location::Definition {
            input: "definition0".into(),
            pointer: pointer.into(),
            span: None
        }
    );
}
fn document(declarations: &str) -> String {
    format!(
        r#"{{"format":"archsig.atom-definition/1","semantics":"archsig/0.6.0","vocabularies":[{{"semantics":"archsig/0.6.0","namespace":"N","version":"1","dependencies":[],"declarations":[{declarations}]}}]}}"#
    )
}
fn entity(name: &str, params: &str, fields: &str) -> String {
    format!(
        r#"{{"kind":"entity","name":"N.{name}","meaning":"meaning","parameters":[{params}],"fields":[{fields}],"alignments":[]}}"#
    )
}
fn field(name: &str, ty: &str) -> String {
    format!(r#"{{"name":"{name}","type":{ty},"meaning":"field meaning"}}"#)
}
#[test]
fn counter_fixed_digest_meaning_and_locations() {
    let d = check(COUNTER);
    assert_eq!(d.vocabularies["Counter"].digest, DIGEST);
    let state = &d.declarations["Counter.State"];
    assert_eq!(state.meaning, "実装中の一つのカウンタ状態。");
    assert_eq!(
        state.signature.field("count").unwrap().meaning,
        "この状態が保持する件数。"
    );
    assert_eq!(
        state.location,
        Location::Definition {
            input: "definition0".into(),
            pointer: "/vocabularies/0/declarations/0".into(),
            span: None
        }
    );
    assert_eq!(
        d.inputs[0].model_digest,
        check(&COUNTER.replace('\n', " ")).inputs[0].model_digest
    );
}
#[test]
fn unused_library_and_dependency_are_retained() {
    let d = check(LIBRARY);
    assert_eq!(d.vocabularies.len(), 2);
    assert_eq!(d.declarations.len(), 2);
    assert_eq!(d.vocabularies["Counter"].digest, DIGEST);
    assert_eq!(
        d.vocabularies["Extras"].dependencies[0].namespace,
        "Counter"
    );
    assert_ne!(
        d.inputs[0].model_digest,
        check(COUNTER).inputs[0].model_digest
    );
}
#[test]
fn unused_binding_still_checks_registration_version_digest() {
    fail(
        &LIBRARY.replace("sha256:388b", "sha256:488b"),
        Code::VocabularyMismatch,
        "/vocabularies/1/dependencies/0",
    );
    fail(
        &LIBRARY.replace(
            r#""namespace": "Counter", "version""#,
            r#""namespace": "Absent", "version""#,
        ),
        Code::Reference,
        "/vocabularies/1/dependencies/0",
    );
    let bad = LIBRARY.replace(
        r#""namespace": "Counter", "version": "1", "digest""#,
        r#""namespace": "Counter", "version": "2", "digest""#,
    );
    fail(
        &bad,
        Code::VocabularyMismatch,
        "/vocabularies/1/dependencies/0",
    );
}
#[test]
fn duplicate_namespace_rejected_across_files() {
    let e = definition::check_definitions(&[
        ("definition0", COUNTER.as_bytes()),
        ("definition1", COUNTER.as_bytes()),
    ])
    .unwrap_err();
    assert_eq!(e.issue.code, Code::DuplicateId);
    assert_eq!(e.inputs.len(), 2);
    assert!(matches!(e.issue.location,Location::Definition{input,..} if input=="definition1"));
}
#[test]
fn cycle_precedes_digest_comparison() {
    let bad = LIBRARY.replace(
        r#""namespace": "Counter", "version": "1", "digest""#,
        r#""namespace": "Extras", "version": "999", "digest""#,
    );
    fail(&bad, Code::Cycle, "/vocabularies/1/dependencies/0");
}
#[test]
fn meaning_version_unknown_fields_and_empty_wrapper_rejected() {
    fail(
        &COUNTER.replace("実装中の一つのカウンタ状態。", ""),
        Code::Syntax,
        "/vocabularies/0/declarations/0/meaning",
    );
    fail(
        &COUNTER.replace(r#""version": "1""#, r#""version": """#),
        Code::Syntax,
        "/vocabularies/0/version",
    );
    fail(
        &COUNTER.replace(
            r#""meaning": "実装中の一つのカウンタ状態。""#,
            r#""meanng": "実装中の一つのカウンタ状態。""#,
        ),
        Code::Syntax,
        "/vocabularies/0/declarations/0/meanng",
    );
    fail(
        r#"{"format":"archsig.atom-definition/1","semantics":"archsig/0.6.0","vocabularies":[]}"#,
        Code::Syntax,
        "/vocabularies",
    );
}
#[test]
fn version_precedes_unknown_schema_fields() {
    fail(
        r#"{"format":"archsig.atom-definition/9","semantics":"archsig/0.6.0","future":true}"#,
        Code::UnsupportedVersion,
        "/format",
    );
}
#[test]
fn json_errors_keep_definition_identity_and_byte_span() {
    for bytes in [
        &b"\xef\xbb\xbf{}"[..],
        &b"{\"format\":\"\xff\"}"[..],
        &br#"{"a":"\uD800"}"#[..],
    ] {
        let e = definition::check_definitions(&[("definition4", bytes)]).unwrap_err();
        assert_eq!(e.issue.code, Code::Syntax);
        assert!(
            matches!(e.issue.location,Location::Definition{input,pointer,span:Some(_)}if input=="definition4"&&pointer.is_empty())
        );
    }
    let e = definition::check_definitions(&[("definition4", br#"{"x":1,"x":2}"#)]).unwrap_err();
    assert_eq!(e.issue.code, Code::DuplicateKey);
    assert_eq!(
        e.issue.location,
        Location::Definition {
            input: "definition4".into(),
            pointer: "/x".into(),
            span: None
        }
    );
}
#[test]
fn builtins_allowed_as_fields_constructors_and_namespace() {
    let s = document(&format!(
        r#"{},{{"kind":"data","name":"N.Value","meaning":"data","constructors":[{{"name":"count","arguments":[],"meaning":"zero"}}]}}"#,
        entity("State", "", &field("count", r#""Z""#))
    ));
    check(&s);
    check(&s.replace("\"N\"", "\"count\"").replace("N.", "count."));
    fail(
        &document(&entity("count", "", "")),
        Code::Syntax,
        "/vocabularies/0/declarations/0/name",
    );
}
#[test]
fn type_and_alignment_references_keep_pointer_and_dependency() {
    let root = entity("Root", "", "");
    let node = entity(
        "State",
        &field("owner", r#"["Ref","N.Root"]"#),
        &field("next", r#"["Owned","N.State","owner"]"#),
    );
    let d = check(&document(&format!("{root},{node}")));
    let s = &d.declarations["N.State"];
    assert_eq!(s.dependencies, vec!["N.Root", "N.State"]);
    assert_eq!(
        s.references[0].0,
        Location::Definition {
            input: "definition0".into(),
            pointer: "/vocabularies/0/declarations/1/fields/0/type/1".into(),
            span: None
        }
    );
    let PrimitiveSignature::Entity { owner, .. } = &s.signature else {
        panic!()
    };
    assert_eq!(owner.as_deref(), Some("N.Root"));
}
#[test]
fn primitive_validation_keeps_original_json_location() {
    let s = document(&entity("State", "", &field("owner", r#""Z""#)));
    fail(
        &s,
        Code::Syntax,
        "/vocabularies/0/declarations/0/fields/0/name",
    );
    let s = document(&entity(
        "State",
        "",
        &field("value", r#"["Ref","N.Absent"]"#),
    ));
    fail(
        &s,
        Code::Reference,
        "/vocabularies/0/declarations/0/fields/0/type/1",
    );
}
#[test]
fn data_self_recursion_ground_values_and_variance() {
    check(&document(
        r#"{"kind":"data","name":"N.Tree","meaning":"tree","constructors":[{"name":"Leaf","arguments":[],"meaning":"leaf"},{"name":"Branch","arguments":[["List",["Data","N.Tree"]]],"meaning":"children"}]}"#,
    ));
    let bad = document(
        r#"{"kind":"data","name":"N.Loop","meaning":"loop","constructors":[{"name":"More","arguments":[["Data","N.Loop"]],"meaning":"next"}]}"#,
    );
    let e = definition::check_definitions(&[("definition0", bad.as_bytes())]).unwrap_err();
    assert_eq!(e.issue.code, Code::Syntax);
    assert!(matches!(e.issue.location, Location::Definition { .. }));
}
#[test]
fn reservations_structure_is_checked() {
    let d = check(include_str!("fixtures/reservations.atoms.json"));
    assert_eq!(
        d.vocabularies["Reservations"].digest,
        "sha256:8427a2712c22d6eed1cdd5f48258bea102904173558a7087bb82c7d95665c9ff"
    );
    let PrimitiveSignature::Correspondence { maps, implicit, .. } =
        &d.declarations["Reservations.Migration"].signature
    else {
        panic!()
    };
    assert_eq!(maps.len(), 2);
    assert!(!implicit.is_empty());
}
#[test]
fn meaning_changes_vocabulary_digest() {
    assert_ne!(
        check(COUNTER).vocabularies["Counter"].digest,
        check(&COUNTER.replace("保持する件数。", "保持する数量。")).vocabularies["Counter"].digest
    );
}

#[test]
fn split_files_preserve_vocabulary_digest_and_original_identity() {
    use archsig::canonical::Json;
    let d = check(LIBRARY);
    let wrap = |name: &str| {
        Json::obj([
            ("format", Json::str(definition::FORMAT)),
            ("semantics", Json::str(definition::SEMANTICS)),
            (
                "vocabularies",
                Json::Arr(vec![d.vocabularies[name].manifest.clone()]),
            ),
        ])
        .canonical()
    };
    let extras = wrap("Extras");
    let counter = wrap("Counter");
    let split = definition::check_definitions(&[
        ("definition0", extras.as_bytes()),
        ("definition1", counter.as_bytes()),
    ])
    .unwrap();
    assert_eq!(split.vocabularies["Counter"].digest, DIGEST);
    assert_eq!(
        split.vocabularies["Extras"].digest,
        d.vocabularies["Extras"].digest
    );
    assert_eq!(
        split.declarations["Counter.State"].location,
        Location::Definition {
            input: "definition1".into(),
            pointer: "/vocabularies/0/declarations/0".into(),
            span: None
        }
    );
}
#[test]
fn ref_data_tag_mismatch_identifies_the_incorrect_occurrence() {
    let root = entity("Root", "", "");
    let state = entity(
        "State",
        "",
        &format!(
            "{},{}",
            field("good", r#"["Ref","N.Root"]"#),
            field("bad", r#"["Data","N.Root"]"#)
        ),
    );
    fail(
        &document(&format!("{root},{state}")),
        Code::Syntax,
        "/vocabularies/0/declarations/1/fields/1/type/1",
    );
}
#[test]
fn missing_explicit_dependency_has_original_type_position() {
    let bad = LIBRARY.replace(r#""type": "Text""#, r#""type": ["Ref","Counter.State"]"#);
    check(&bad);
    let bad = bad.replace(
        &format!(r#"{{"namespace": "Counter", "version": "1", "digest": "{DIGEST}"}}"#),
        "",
    );
    fail(
        &bad,
        Code::Reference,
        "/vocabularies/1/declarations/0/fields/0/type/1",
    );
}
#[test]
fn declaration_set_order_normalizes_and_field_order_is_retained() {
    let a = entity(
        "A",
        "",
        &format!(
            "{},{}",
            field("first", r#""Z""#),
            field("second", r#""Text""#)
        ),
    );
    let b = entity("B", "", "");
    let first = check(&document(&format!("{a},{b}")));
    let second = check(&document(&format!("{b},{a}")));
    assert_eq!(
        first.vocabularies["N"].digest,
        second.vocabularies["N"].digest
    );
    assert_eq!(first.inputs[0].model_digest, second.inputs[0].model_digest);
    let swapped = entity(
        "A",
        "",
        &format!(
            "{},{}",
            field("second", r#""Text""#),
            field("first", r#""Z""#)
        ),
    );
    assert_ne!(
        first.vocabularies["N"].digest,
        check(&document(&format!("{swapped},{b}"))).vocabularies["N"].digest
    );
}
#[test]
fn empty_declaration_vocabulary_is_accepted() {
    let d = check(&document(""));
    assert!(d.declarations.is_empty());
    assert_eq!(d.vocabularies.len(), 1);
}
#[test]
fn two_namespace_cycle_precedes_invalid_digest() {
    let binding = format!(
        r#"[{{"namespace":"Extras","version":"wrong","digest":"{}"}}]"#,
        format!("sha256:{}", "0".repeat(64))
    );
    let bad = LIBRARY.replacen(
        r#""dependencies": []"#,
        &format!(r#""dependencies": {binding}"#),
        1,
    );
    // Counter → Extras → Counter。DFSが戻る Extras 側bindingを指す。
    fail(&bad, Code::Cycle, "/vocabularies/1/dependencies/0");
}
#[test]
fn vocabulary_wrapper_order_normalizes_model_digest() {
    use archsig::canonical::Json;
    let original = check(LIBRARY);
    let reverse = Json::obj([
        ("format", Json::str(definition::FORMAT)),
        ("semantics", Json::str(definition::SEMANTICS)),
        (
            "vocabularies",
            Json::Arr(
                original
                    .vocabularies
                    .values()
                    .rev()
                    .map(|v| v.manifest.clone())
                    .collect(),
            ),
        ),
    ])
    .canonical();
    let reversed = check(&reverse);
    assert_eq!(
        original.inputs[0].model_digest,
        reversed.inputs[0].model_digest
    );
    assert_eq!(
        original.vocabularies["Counter"].digest,
        reversed.vocabularies["Counter"].digest
    );
}

#[test]
fn fully_qualified_definition_name_is_not_shadowed_by_local_constructor() {
    let s = document(&format!(
        r#"{},{{"kind":"data","name":"N.N","meaning":"data","constructors":[{{"name":"A","arguments":[],"meaning":"case"}}]}},{}"#,
        entity("A", "", ""),
        entity("State", "", &field("value", r#"["Ref","N.A"]"#))
    ));
    let d = check(&s);
    assert_eq!(
        d.declarations["N.State"]
            .signature
            .field("value")
            .unwrap()
            .ty,
        archsig::types::Type::Ref("N.A".into())
    );
    fail(
        &s.replace(r#"["Ref","N.A"]"#, r#"["Ref","N.Absent"]"#),
        Code::Reference,
        "/vocabularies/0/declarations/2/fields/0/type/1",
    );
}
fn correspondence_with_target_extra(complete: bool) -> String {
    let owner_a = field("owner", r#"["Ref","N.RA"]"#);
    let owner_b = field("owner", r#"["Ref","N.RB"]"#);
    let a = field("a", r#""Z""#);
    let extra = field("extra", r#""Z""#);
    let source_fields = if complete { format!("{a},{extra}") } else { a };
    let extra_alignment = if complete {
        r#",{"source":"N.E.extra","target":"N.F.extra","meaning":"extra position"}"#
    } else {
        ""
    };
    let map = format!(
        r#"{{"kind":"correspondence","name":"N.M","meaning":"map","parameters":[{},{}],"fields":[{}],"alignments":[{{"source":"N.E.owner","target":"N.F.owner","meaning":"owner"}},{{"source":"N.E.a","target":"N.F.b","meaning":"coordinate"}}{extra_alignment}]}}"#,
        field("from", r#"["Ref","N.RA"]"#),
        field("to", r#"["Ref","N.RB"]"#),
        field(
            "states",
            r#"["Map",["Owned","N.E","from"],["Owned","N.F","to"]]"#
        )
    );
    document(&format!(
        "{},{},{},{},{map}",
        entity("RA", "", ""),
        entity("RB", "", ""),
        entity("E", &owner_a, &source_fields),
        entity(
            "F",
            &owner_b,
            &format!("{},{}", field("b", r#""Z""#), extra)
        )
    ))
}
#[test]
fn correspondence_requires_all_target_field_positions() {
    fail(
        &correspondence_with_target_extra(false),
        Code::Syntax,
        "/vocabularies/0/declarations/4/name",
    );
    let complete = check(&correspondence_with_target_extra(true));
    let PrimitiveSignature::Correspondence { alignments, .. } =
        &complete.declarations["N.M"].signature
    else {
        panic!()
    };
    assert_eq!(alignments.len(), 3);
}
#[test]
fn missing_semantics_with_string_format_is_unsupported() {
    use archsig::issue::Details;
    for format in [definition::FORMAT, "archsig.atom-definition/99"] {
        let s = format!(r#"{{"format":"{format}","future":true}}"#);
        let e = definition::check_definitions(&[("definition0", s.as_bytes())]).unwrap_err();
        assert_eq!(e.issue.code, Code::UnsupportedVersion);
        assert_eq!(
            e.issue.details,
            Details::Version {
                found_format: format.into(),
                found_semantics: None
            }
        );
    }
    fail(r#"{"format":1,"future":true}"#, Code::Syntax, "/format");
    fail(
        r#"{"format":"archsig.atom-definition/1","semantics":"archsig/0.6.0","future":true,"vocabularies":[]}"#,
        Code::Syntax,
        "/future",
    );
}
#[test]
fn root_and_vocabulary_unknown_versions_precede_schema_unknown_fields() {
    use archsig::issue::Details;
    fail(
        r#"{"format":"archsig.atom-definition/1","semantics":"archsig/future","future":true}"#,
        Code::UnsupportedVersion,
        "/semantics",
    );
    let s = r#"{"format":"archsig.atom-definition/1","semantics":"archsig/0.6.0","vocabularies":[{"semantics":"archsig/future","future":true}]}"#;
    let e = definition::check_definitions(&[("definition0", s.as_bytes())]).unwrap_err();
    assert_eq!(e.issue.code, Code::UnsupportedVersion);
    assert_eq!(
        e.issue.details,
        Details::Version {
            found_format: definition::FORMAT.into(),
            found_semantics: Some("archsig/future".into())
        }
    );
    assert_eq!(
        e.issue.location,
        Location::Definition {
            input: "definition0".into(),
            pointer: "/vocabularies/0/semantics".into(),
            span: None
        }
    );
    let supported = LIBRARY.replacen(
        r#""namespace": "Counter""#,
        r#""future": true, "namespace": "Counter""#,
        1,
    );
    fail(&supported, Code::Syntax, "/vocabularies/0/future");
}
