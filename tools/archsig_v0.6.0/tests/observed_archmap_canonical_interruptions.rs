//! ArchMap の検査中正規化・namespace/field/constructor 走査への共有制御。
mod common;

use archsig::{
    canonical::Json,
    observed::{
        control::{Checkpoint, Control, Limits, StopReason, Usage},
        input::{InputSources, InputStatus, check_inputs},
    },
    result::Signal,
};
use std::{cell::Cell, rc::Rc};

fn input(fields: &[(&str, &str)], extra: &str, atoms: &[(&str, &str)]) -> InputSources {
    let fields = fields
        .iter()
        .map(|(name, ty)| common::field_json(name, ty))
        .collect::<Vec<_>>()
        .join(",");
    let entity = common::entity_json("V.State", "[]", &format!("[{fields}]"));
    let declarations = if extra.is_empty() {
        entity
    } else {
        format!("{entity},{extra}")
    };
    let definition = common::definition_json(&format!(
        "[{}]",
        common::vocabulary_json("V", &format!("[{declarations}]"), "[]")
    ));
    let definitions = common::definitions_ok(&[&definition]);
    let digest = &definitions.vocabularies["V"].digest;
    let atoms = atoms.iter().enumerate().map(|(i, (field, value))| format!(r#"{{"id":"a{i}","subject":"root","field":"V.State.{field}","origin":"model","value":{value}}}"#)).collect::<Vec<_>>().join(",");
    let map = format!(
        r#"{{"format":"archsig.archmap/2","semantics":"archsig/0.6.0","vocabularies":[{{"namespace":"V","version":"1","digest":"{digest}"}}],"sources":[],"origins":[{{"id":"model","mode":"specification","method":"test","locations":[],"note":"canonical test"}}],"snapshots":[{{"id":"s","origin":"model","subjects":[{{"id":"root","type":"V.State","origin":"model"}}],"atoms":[{atoms}]}}]}}"#
    );
    InputSources::from_bytes(
        vec![definition.into_bytes()],
        common::reading("view one(): Z = 1;").into_bytes(),
        map.into_bytes(),
    )
}

fn count(sources: InputSources, point: Checkpoint) -> usize {
    let seen = Rc::new(Cell::new(0));
    let counter = seen.clone();
    let mut control = Control::new(Limits::default(), move |current| {
        if current == point {
            counter.set(counter.get() + 1);
        }
        Usage::default()
    });
    let _ = check_inputs(sources, &mut control);
    seen.get()
}

fn stop(point: Checkpoint, at: usize, resource: usize) -> Control {
    let mut seen = 0;
    Control::new(
        Limits {
            time_ms: (resource == 1).then_some(1),
            memory_mib: (resource == 2).then_some(1),
        },
        move |current| {
            if current == point {
                seen += 1;
            }
            let stopping = seen == at;
            Usage {
                signal: (stopping && resource == 0).then_some(Signal::Term),
                elapsed_ms: u128::from(stopping && resource == 1),
                memory_mib: u128::from(stopping && resource == 2),
            }
        },
    )
}

fn interrupted(sources: InputSources, point: Checkpoint, at: usize, resource: usize) {
    let mut control = stop(point, at, resource);
    let failure = check_inputs(sources, &mut control).unwrap_err();
    assert_eq!(failure.status(), InputStatus::Interrupted);
    assert!(!failure.primitives().is_empty());
    assert!(!failure.declarations().is_empty());
    let value = failure.wire();
    let Json::Obj(wire) = &value else {
        panic!("object")
    };
    for key in ["requests", "answers", "nodes"] {
        assert_eq!(wire[key], Json::Arr(vec![]));
    }
    match control.stop_reason().unwrap() {
        StopReason::Cancelled(Signal::Term) => assert_eq!(resource, 0),
        StopReason::BudgetExhausted { .. } => assert_ne!(resource, 0),
        other => panic!("unexpected stop {other:?}"),
    }
}

fn invalid(sources: InputSources, code: &str, pointer: &str) {
    let failure = check_inputs(sources, &mut Control::unlimited()).unwrap_err();
    assert_eq!(failure.status(), InputStatus::Invalid);
    assert_eq!(failure.issues().len(), 1);
    let Json::Obj(issue) = &failure.issues()[0] else {
        panic!("issue")
    };
    assert_eq!(issue["code"], Json::str(code));
    assert_eq!(
        issue["location"],
        Json::obj([
            ("input", Json::str("archmap")),
            ("pointer", Json::str(pointer))
        ])
    );
}

#[test]
fn model_digest_nested_values_and_string_escaping_observe_all_resources() {
    let make = || {
        input(
            &[("value", r#"["List",["Tuple","Text",["Option","Bool"]]]"#)],
            "",
            &[(
                "value",
                r#"[["a\n\"b",{"some":true}],["c\\d",{"none":true}]]"#,
            )],
        )
    };
    check_inputs(make(), &mut Control::unlimited()).unwrap();
    let total = count(make(), Checkpoint::ArchMapCanonical);
    assert!(total > 80);
    for at in [1, total / 2, total] {
        for resource in 0..3 {
            interrupted(make(), Checkpoint::ArchMapCanonical, at, resource);
        }
    }
}

#[test]
fn set_duplicate_comparison_walks_nested_values_before_rejection() {
    let make = || {
        input(
            &[("value", r#"["Set",["List","Bool"]]"#)],
            "",
            &[("value", "[[true,false],[true,false]]")],
        )
    };
    invalid(make(), "syntax", "/snapshots/0/atoms/0/value/1");
    let total = count(make(), Checkpoint::ArchMapCanonical);
    assert!(total > 20);
    for at in [1, total / 2, total] {
        for resource in 0..3 {
            interrupted(make(), Checkpoint::ArchMapCanonical, at, resource);
        }
    }
}

#[test]
fn map_key_duplicate_comparison_is_controlled_inside_the_key() {
    let make = || {
        input(
            &[("value", r#"["Map",["Ref","V.State"],["Ref","V.State"]]"#)],
            "",
            &[(
                "value",
                r#"[[["s","root"],["s","root"]],[["s","root"],["s","root"]]]"#,
            )],
        )
    };
    let single = input(
        &[("value", r#"["Map",["Ref","V.State"],["Ref","V.State"]]"#)],
        "",
        &[("value", r#"[[["s","root"],["s","root"]]]"#)],
    );
    check_inputs(single, &mut Control::unlimited()).unwrap();
    invalid(make(), "duplicate_key", "/snapshots/0/atoms/0/value/1/0");
    let total = count(make(), Checkpoint::ArchMapCanonical);
    assert!(total > 20);
    for at in [1, total / 2, total] {
        interrupted(make(), Checkpoint::ArchMapCanonical, at, 0);
    }
}

#[test]
fn required_namespace_type_recursion_adds_internal_schema_boundaries() {
    let flat = || input(&[("value", "\"Bool\"")], "", &[]);
    let nested = || {
        input(
            &[(
                "value",
                r#"["Tuple","Bool",["Option",["Tuple","Bool","Bool"]]]"#,
            )],
            "",
            &[],
        )
    };
    check_inputs(nested(), &mut Control::unlimited()).unwrap();
    let at = count(flat(), Checkpoint::ArchMapSchema) + 1;
    assert!(count(nested(), Checkpoint::ArchMapSchema) > at + 4);
    interrupted(nested(), Checkpoint::ArchMapSchema, at, 0);
}

#[test]
fn missing_field_slots_and_late_field_lookup_add_per_field_boundaries() {
    let small = || input(&[("a", "\"Bool\"")], "", &[]);
    let wide = || {
        input(
            &[
                ("a", "\"Bool\""),
                ("b", "\"Bool\""),
                ("c", "\"Bool\""),
                ("d", "\"Bool\""),
            ],
            "",
            &[],
        )
    };
    let at = count(small(), Checkpoint::ArchMapSchema) + 1;
    assert!(count(wide(), Checkpoint::ArchMapSchema) > at + 4);
    interrupted(wide(), Checkpoint::ArchMapSchema, at, 0);
    let known = |field| {
        input(
            &[
                ("a", "\"Bool\""),
                ("b", "\"Bool\""),
                ("c", "\"Bool\""),
                ("d", "\"Bool\""),
            ],
            "",
            &[(field, "true")],
        )
    };
    check_inputs(known("d"), &mut Control::unlimited()).unwrap();
    // 同じ定義・slot 数で照合対象だけを替え、候補3個分の前後確認を区別する。
    assert_eq!(
        count(known("d"), Checkpoint::ArchMapSchema),
        count(known("a"), Checkpoint::ArchMapSchema) + 6
    );
    let unknown = || {
        input(
            &[("a", "\"Bool\""), ("b", "\"Bool\"")],
            "",
            &[("missing", "true")],
        )
    };
    invalid(unknown(), "reference", "/snapshots/0/atoms/0/field");
    let last = count(unknown(), Checkpoint::ArchMapSchema);
    for resource in 0..3 {
        interrupted(unknown(), Checkpoint::ArchMapSchema, last, resource);
    }
}

#[test]
fn unknown_constructor_checks_each_candidate_and_post_error_boundary() {
    fn make(constructors: usize, tag: &str) -> InputSources {
        let constructors = (0..constructors)
            .map(|i| common::constructor_json(&format!("Case{i}"), "[]"))
            .collect::<Vec<_>>()
            .join(",");
        let data = common::data_json("V.Choice", &format!("[{constructors}]"));
        input(
            &[("value", r#"["Data","V.Choice"]"#)],
            &data,
            &[("value", &format!(r#"{{"tag":"{tag}","args":[]}}"#))],
        )
    }
    invalid(
        make(4, "Absent"),
        "syntax",
        "/snapshots/0/atoms/0/value/tag",
    );
    check_inputs(make(4, "Case3"), &mut Control::unlimited()).unwrap();
    // 定義は同一。最初/最後の既知 tag の差は constructor 探索3候補分だけ。
    assert_eq!(
        count(make(4, "Case3"), Checkpoint::ArchMapSchema),
        count(make(4, "Case0"), Checkpoint::ArchMapSchema) + 6
    );
    let first = count(make(1, "Absent"), Checkpoint::ArchMapSchema);
    let total = count(make(4, "Absent"), Checkpoint::ArchMapSchema);
    assert!(total >= first + 12);
    for at in [1, total / 2, total] {
        for resource in 0..3 {
            interrupted(make(4, "Absent"), Checkpoint::ArchMapSchema, at, resource);
        }
    }
}
