//! 小さい三入力の補完検査で、内部の停止を入力不整合へ読み替えない。
mod common;

use archsig::{
    canonical::Json,
    observed::{
        control::{Checkpoint, Control, Limits, Usage},
        input::{InputFailure, InputSources, InputStatus, check_inputs},
    },
    result::Signal,
};
use std::{cell::Cell, rc::Rc};

fn source(
    declarations: &[String],
    subjects: &[(&str, &str)],
    atoms: &[(&str, &str, &str)],
) -> InputSources {
    let definition = common::definition_json(&format!(
        "[{}]",
        common::vocabulary_json("V", &format!("[{}]", declarations.join(",")), "[]")
    ));
    let definitions = common::definitions_ok(&[&definition]);
    let digest = &definitions.vocabularies["V"].digest;
    let law = common::reading_with("V", digest, "view marker(): Bool = true;");
    let subjects: Vec<_> = subjects
        .iter()
        .map(|(id, ty)| format!(r#"{{"id":"{id}","type":"V.{ty}","origin":"o"}}"#))
        .collect();
    let atoms: Vec<_> = atoms
        .iter()
        .enumerate()
        .map(|(i, (id, field, value))| {
            format!(r#"{{"id":"a{i}","subject":"{id}","field":"V.{field}","value":{value},"origin":"o"}}"#)
        })
        .collect();
    let map = format!(
        r#"{{"format":"archsig.archmap/2","semantics":"archsig/0.6.0","vocabularies":[{{"namespace":"V","version":"1","digest":"{digest}"}}],"sources":[],"origins":[{{"id":"o","mode":"specification","method":"test","locations":[],"note":"small completion"}}],"snapshots":[{{"id":"s","origin":"o","subjects":[{}],"atoms":[{}]}}]}}"#,
        subjects.join(","),
        atoms.join(",")
    );
    InputSources::from_bytes(
        vec![definition.into_bytes()],
        law.into_bytes(),
        map.into_bytes(),
    )
}

fn entity(name: &str, fields: &str) -> String {
    common::entity_json(name, "[]", fields)
}

fn count_completion(source: &InputSources, valid: bool) -> usize {
    let count = Rc::new(Cell::new(0));
    let seen = count.clone();
    let mut control = Control::new(Limits::default(), move |point| {
        if point == Checkpoint::Completion {
            seen.set(seen.get() + 1);
        }
        Usage::default()
    });
    let result = check_inputs(source.clone(), &mut control);
    if valid {
        result.unwrap();
    } else {
        let failure = result.unwrap_err();
        assert_eq!(failure.status(), InputStatus::Invalid);
        let Json::Obj(issue) = &failure.issues()[0] else {
            panic!("issue")
        };
        assert_eq!(issue["code"], Json::str("inconsistent_observation"));
    }
    assert!(count.get() > 10);
    count.get()
}

fn assert_stopped(failure: InputFailure, code: &str, details: Json) {
    assert_eq!(failure.status(), InputStatus::Interrupted);
    // 定義と Law は検査済み。ArchMap の補完中に中断しても、その表を保つ。
    assert_eq!(failure.declarations().len(), 2); // reading と view
    assert!(!failure.primitives().is_empty());
    assert_eq!(failure.vocabularies().len(), 1);
    let Json::Obj(issue) = &failure.issues()[0] else {
        panic!("issue")
    };
    assert_eq!(issue["code"], Json::str(code));
    assert_eq!(issue["details"], details);
    let Json::Obj(ref wire) = failure.wire() else {
        panic!("result")
    };
    for name in ["requests", "answers", "nodes"] {
        assert_eq!(wire[name], Json::Arr(vec![]));
    }
}

fn cancel_at(source: &InputSources, stop_after: usize) {
    let count = Rc::new(Cell::new(0));
    let seen = count.clone();
    let mut control = Control::new(Limits::default(), move |point| {
        if point == Checkpoint::Completion {
            seen.set(seen.get() + 1);
        }
        Usage {
            signal: (seen.get() == stop_after).then_some(Signal::Term),
            ..Usage::default()
        }
    });
    let failure = check_inputs(source.clone(), &mut control).unwrap_err();
    assert_eq!(count.get(), stop_after);
    assert_stopped(
        failure,
        "cancelled",
        Json::obj([("signal", Json::str("SIGTERM"))]),
    );
}

fn map_without_codomain() -> InputSources {
    source(
        &[
            entity("V.A", "[]"),
            entity("V.B", "[]"),
            entity(
                "V.Holder",
                &format!(
                    "[{}]",
                    common::field_json("value", r#"["Map",["Ref","V.A"],["Ref","V.B"]]"#)
                ),
            ),
        ],
        &[("a", "A"), ("h", "Holder")],
        &[],
    )
}

#[test]
fn single_map_constraint_interrupts_before_early_inconsistent_return() {
    // A は登録済み、B は未登録。唯一の欠測 Map 制約が false を返す経路。
    let input = map_without_codomain();
    let total = count_completion(&input, false);
    // 小さい一制約について全境界を確認し、nonempty の候補と空族の両方を通す。
    for stop_after in 1..=total {
        cancel_at(&input, stop_after);
    }
}

#[test]
fn single_map_budget_keeps_resource_limit_and_observed() {
    let input = map_without_codomain();
    let total = count_completion(&input, false);
    for stop_after in [1, total / 2, total - 4, total] {
        for memory in [false, true] {
            let mut seen = 0;
            let mut control = Control::new(
                if memory {
                    Limits {
                        time_ms: None,
                        memory_mib: Some(3),
                    }
                } else {
                    Limits {
                        time_ms: Some(3),
                        memory_mib: None,
                    }
                },
                move |point| {
                    if point == Checkpoint::Completion {
                        seen += 1;
                    }
                    let usage = if seen >= stop_after { 4 } else { 0 };
                    if memory {
                        Usage {
                            memory_mib: usage,
                            ..Usage::default()
                        }
                    } else {
                        Usage {
                            elapsed_ms: usage,
                            ..Usage::default()
                        }
                    }
                },
            );
            let failure = check_inputs(input.clone(), &mut control).unwrap_err();
            assert_stopped(
                failure,
                "budget_exhausted",
                Json::obj([
                    (
                        "resource",
                        Json::str(if memory { "memory_mib" } else { "time_ms" }),
                    ),
                    ("limit", Json::str("3")),
                    ("observed", Json::str("4")),
                ]),
            );
        }
    }
}

#[test]
fn known_container_collection_and_cover_evaluation_keep_the_stop() {
    // 各値は最大2要素。全境界への注入で collector 内の再帰と Map 行処理も覆う。
    for (ty, value, data) in [
        (
            r#"["Tuple",["Ref","V.A"],["Ref","V.A"]]"#,
            r#"[["s","a"],["s","b"]]"#,
            false,
        ),
        (
            r#"["List",["Ref","V.A"]]"#,
            r#"[["s","a"],["s","b"]]"#,
            false,
        ),
        (
            r#"["Set",["Ref","V.A"]]"#,
            r#"[["s","a"],["s","b"]]"#,
            false,
        ),
        (
            r#"["Option",["Ref","V.A"]]"#,
            r#"{"some":["s","a"]}"#,
            false,
        ),
        (
            r#"["Data","V.D"]"#,
            r#"{"tag":"Wrap","args":[["s","a"],["s","b"]]}"#,
            true,
        ),
        (
            r#"["Map",["Ref","V.A"],["Ref","V.A"]]"#,
            r#"[[["s","a"],["s","b"]],[["s","b"],["s","a"]]]"#,
            false,
        ),
    ] {
        let mut declarations = vec![
            entity("V.A", "[]"),
            entity(
                "V.Holder",
                &format!("[{}]", common::field_json("value", ty)),
            ),
        ];
        if data {
            declarations.push(common::data_json(
                "V.D",
                &format!(
                    "[{}]",
                    common::constructor_json("Wrap", r#"[["Ref","V.A"],["Ref","V.A"]]"#)
                ),
            ));
        }
        let input = source(
            &declarations,
            &[("a", "A"), ("b", "A"), ("h", "Holder")],
            &[("h", "Holder.value", value)],
        );
        let total = count_completion(&input, true);
        for stop_after in 1..=total {
            cancel_at(&input, stop_after);
        }
    }
}

#[test]
fn unknown_owners_map_and_tuple_constraints_interrupt_inside_candidate_search() {
    let owner = r#"[{"name":"owner","type":["Ref","V.Root"],"meaning":"owner"}]"#;
    let input = source(
        &[
            entity("V.Root", "[]"),
            common::entity_json("V.Item", owner, "[]"),
            common::entity_json(
                "V.Holder",
                owner,
                &format!(
                    "[{},{}]",
                    common::field_json(
                        "value",
                        r#"["Map",["Owned","V.Item","owner"],["Ref","V.Root"]]"#
                    ),
                    common::field_json(
                        "missing",
                        r#"["Tuple",["Owned","V.Item","owner"],["Map",["Owned","V.Item","owner"],["Owned","V.Item","owner"]]]"#
                    ),
                ),
            ),
        ],
        &[
            ("r1", "Root"),
            ("r2", "Root"),
            ("i1", "Item"),
            ("i2", "Item"),
            ("h", "Holder"),
        ],
        &[
            ("h", "Holder.owner", r#"["s","r1"]"#),
            ("h", "Holder.value", r#"[[["s","i1"],["s","r1"]]]"#),
        ],
    );
    let total = count_completion(&input, true);
    // 前半の収集、変数依存の結合、探索内部と成功の直前をすべて小さい入力で再現する。
    for stop_after in [1, total / 3, total / 2, 2 * total / 3, total - 20, total] {
        cancel_at(&input, stop_after);
    }
}

#[test]
fn data_inhabitation_constructor_arguments_and_fixed_point_keep_the_stop() {
    let input = source(
        &[
            entity("V.A", "[]"),
            entity("V.B", "[]"),
            common::data_json(
                "V.D",
                &format!(
                    "[{},{}]",
                    common::constructor_json("Absent", r#"[["Ref","V.B"]]"#),
                    common::constructor_json(
                        "Present",
                        r#"[["Tuple",["Map",["Ref","V.A"],["Ref","V.A"]],["Data","V.E"]]]"#
                    ),
                ),
            ),
            common::data_json(
                "V.E",
                &format!("[{}]", common::constructor_json("Done", "[]")),
            ),
            entity(
                "V.Holder",
                &format!("[{}]", common::field_json("value", r#"["Data","V.D"]"#)),
            ),
        ],
        &[("a", "A"), ("h", "Holder")],
        &[],
    );
    let total = count_completion(&input, true);
    for stop_after in 1..=total {
        cancel_at(&input, stop_after);
    }
}
