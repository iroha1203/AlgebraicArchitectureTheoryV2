//! 差分を独立な全量表と照合し、同じCLI評価へ接続する。
use crate::common::cli;
#[allow(dead_code)]
#[path = "common/object_view_compatibility_data.rs"]
mod fixture;
use archsig::{
    archmap::{self, Slot},
    canonical::Json as J,
    definition,
    issue::Code,
};
use cli::*;

fn definitions() -> String {
    fixture::D.replacen(r#"{"name":"quantity","type":"Z","meaning":"数量。"}"#,
        r#"{"name":"quantity","type":"Z","meaning":"数量。"},{"name":"label","type":["Tuple","Text","Text"],"meaning":"文字列対。"},{"name":"related","type":["List",["Ref","Pattern.Root"]],"meaning":"参照の列。"}"#,1)
}
fn subject(id: &str, ty: &str) -> J {
    J::obj([
        ("id", J::str(id)),
        ("type", J::str(ty)),
        ("origin", J::str("model")),
    ])
}
fn atom(id: &str, subject: &str, field: &str, value: J) -> J {
    J::obj([
        ("id", J::str(id)),
        ("subject", J::str(subject)),
        ("field", J::str(field)),
        ("value", value),
        ("origin", J::str("model")),
    ])
}
fn pair(a: &str, b: &str) -> J {
    J::Arr(vec![J::str(a), J::str(b)])
}
fn full(id: &str, quantity: Option<&str>, q: bool) -> J {
    let mut subjects = vec![
        subject("root", "Pattern.Root"),
        subject("p", "Pattern.Part"),
    ];
    let mut atoms = vec![
        atom("op", "p", "Pattern.Part.owner", pair(id, "root")),
        atom("lp", "p", "Pattern.Part.label", pair("v", "root")),
        atom("rp", "p", "Pattern.Part.related", J::Arr(vec![pair(id, "root")])),
    ];
    if let Some(n) = quantity {
        atoms.push(atom("xp", "p", "Pattern.Part.quantity", J::str(n)));
    }
    if q {
        subjects.push(subject("q", "Pattern.Part"));
        atoms.extend([
            atom("oq", "q", "Pattern.Part.owner", pair(id, "root")),
            atom("xq", "q", "Pattern.Part.quantity", J::str("9")),
            atom("lq", "q", "Pattern.Part.label", pair("v", "root")),
        ]);
    }
    J::obj([
        ("id", J::str(id)),
        ("origin", J::str("model")),
        ("subjects", J::Arr(subjects)),
        ("atoms", J::Arr(atoms)),
    ])
}
fn delta(id: &str, base: &str, subjects: J, atoms: J) -> J {
    J::obj([
        ("id", J::str(id)),
        ("origin", J::str("model")),
        ("base", J::str(base)),
        ("subjects", subjects),
        ("atoms", atoms),
    ])
}
fn empty() -> J {
    J::obj([] as [(&str, J); 0])
}
fn chain() -> Vec<J> {
    vec![
        full("v", Some("2"), false),
        delta(
            "w",
            "v",
            J::obj([("put", J::Arr(vec![subject("q", "Pattern.Part")]))]),
            J::obj([(
                "put",
                J::Arr(vec![
                    atom("xp", "p", "Pattern.Part.quantity", J::str("7")),
                    atom("oq", "q", "Pattern.Part.owner", pair("w", "root")),
                    atom("xq", "q", "Pattern.Part.quantity", J::str("9")),
                    atom("lq", "q", "Pattern.Part.label", pair("v", "root")),
                ]),
            )]),
        ),
        delta(
            "x",
            "w",
            J::obj([("remove", J::Arr(vec![J::str("q")]))]),
            J::obj([("remove", J::Arr(vec![J::str("xp")]))]),
        ),
    ]
}
fn document(snapshots: Vec<J>) -> String {
    let d = definitions();
    let defs = definition::check_definitions(&[("d", d.as_bytes())]).unwrap();
    J::obj([
        ("format", J::str("archsig.archmap/2")),
        ("semantics", J::str("archsig/0.6.0")),
        (
            "vocabularies",
            J::Arr(vec![J::obj([
                ("namespace", J::str("Pattern")),
                ("version", J::str("1")),
                ("digest", J::str(&defs.vocabularies()["Pattern"].digest)),
            ])]),
        ),
        ("sources", J::Arr(vec![])),
        (
            "origins",
            J::Arr(vec![J::obj([
                ("id", J::str("model")),
                ("mode", J::str("specification")),
                ("method", J::str("差分の独立試験")),
                ("locations", J::Arr(vec![])),
                ("note", J::str("完全表との比較")),
            ])]),
        ),
        ("snapshots", J::Arr(snapshots)),
    ])
    .canonical()
}
fn check(map: &str) -> Result<archmap::CheckedArchMap, archmap::ArchMapFailure> {
    let d = definitions();
    let defs = definition::check_definitions(&[("d", d.as_bytes())]).unwrap();
    archmap::check_archmap(map.as_bytes(), &defs)
}
#[test]
fn full_and_delta_have_the_same_model_and_distinct_original_bytes() {
    let expanded = check(&document(vec![
        full("v", Some("2"), false),
        full("w", Some("7"), true),
        full("x", None, false),
    ]))
    .unwrap();
    let delta = check(&document(chain())).unwrap();
    assert_eq!(delta.model_digest(), expanded.model_digest());
    assert_ne!(delta.bytes_digest(), expanded.bytes_digest());
    assert_eq!(archmap::model_json(&delta), archmap::model_json(&expanded));
    let x = &delta.snapshots()[2];
    assert_eq!(x.subjects.len(), 2);
    let p = x.subjects.iter().find(|s| s.id == "p").unwrap();
    assert!(matches!(
        p.fields
            .iter()
            .find(|f| f.name == "Pattern.Part.quantity")
            .unwrap()
            .slot,
        Slot::Missing
    ));
    let Slot::Known { value, .. } = &p
        .fields
        .iter()
        .find(|f| f.name == "Pattern.Part.owner")
        .unwrap()
        .slot
    else {
        panic!()
    };
    assert!(
        matches!(value,archmap::Value::Ref{snapshot,subject} if snapshot=="x" && subject=="root")
    );
    let mut reordered = chain();
    reordered.reverse();
    assert_eq!(
        check(&document(reordered)).unwrap().model_digest(),
        expanded.model_digest()
    );
}
#[test]
fn unknown_bases_cycles_and_invalid_patch_ids_are_rejected() {
    let put = atom("xp", "p", "Pattern.Part.quantity", J::str("7"));
    for (patch, code) in [
        (delta("w", "absent", empty(), empty()), Code::Reference),
        (delta("w", "w", empty(), empty()), Code::Reference),
        (
            delta(
                "w",
                "v",
                empty(),
                J::obj([("remove", J::Arr(vec![J::str("absent")]))]),
            ),
            Code::Reference,
        ),
        (
            delta(
                "w",
                "v",
                empty(),
                J::obj([("put", J::Arr(vec![put.clone(), put.clone()]))]),
            ),
            Code::DuplicateId,
        ),
        (
            delta(
                "w",
                "v",
                empty(),
                J::obj([
                    ("put", J::Arr(vec![put])),
                    ("remove", J::Arr(vec![J::str("xp")])),
                ]),
            ),
            Code::DuplicateId,
        ),
        (
            delta(
                "w",
                "v",
                J::obj([("remove", J::Arr(vec![J::str("root")]))]),
                empty(),
            ),
            Code::Reference,
        ),
        (
            delta(
                "w",
                "v",
                empty(),
                J::obj([(
                    "put",
                    J::Arr(vec![atom(
                        "xp",
                        "p",
                        "Pattern.Part.quantity",
                        J::Bool(false),
                    )]),
                )]),
            ),
            Code::Syntax,
        ),
    ] {
        assert_eq!(
            check(&document(vec![full("v", Some("2"), false), patch]))
                .unwrap_err()
                .issue
                .code,
            code
        );
    }
    assert_eq!(
        check(&document(vec![
            delta("a", "b", empty(), empty()),
            delta("b", "a", empty(), empty())
        ]))
        .unwrap_err()
        .issue
        .code,
        Code::Reference
    );
}
#[test]
fn explicit_new_atom_references_are_not_rebased() {
    let map = check(&document(vec![
        full("v", Some("2"), false),
        delta(
            "w",
            "v",
            empty(),
            J::obj([(
                "put",
                J::Arr(vec![atom(
                    "op",
                    "p",
                    "Pattern.Part.owner",
                    pair("v", "root"),
                )]),
            )]),
        ),
    ]))
    .unwrap();
    let w = map.snapshots().iter().find(|s| s.id == "w").unwrap();
    let p = w.subjects.iter().find(|s| s.id == "p").unwrap();
    let Slot::Known { value, .. } = &p
        .fields
        .iter()
        .find(|f| f.name == "Pattern.Part.owner")
        .unwrap()
        .slot
    else {
        panic!()
    };
    assert!(matches!(value,archmap::Value::Ref{snapshot,..} if snapshot=="v"));
}
#[test]
fn cli_accepts_delta_and_returns_the_same_values_and_missing_as_full_input() {
    let d = definitions();
    let defs = definition::check_definitions(&[("d", d.as_bytes())]).unwrap();
    let law = format!(
        "law \"archsig.law/2\" semantics \"archsig/0.6.0\";reading Selected{{use vocabulary Pattern version \"1\" digest \"{}\";view quantity(c:Part):Z=c.quantity;law required positive(c:Part):c.quantity>=0;}}",
        defs.vocabularies()["Pattern"].digest
    );
    for (tag, map) in [
        ("delta", document(chain())),
        (
            "full",
            document(vec![
                full("v", Some("2"), false),
                full("w", Some("7"), true),
                full("x", None, false),
            ]),
        ),
    ] {
        let dir = workdir(&format!("delta-{tag}"));
        for (name, data) in [
            ("d.json", d.as_str()),
            ("a.json", map.as_str()),
            ("l.law", law.as_str()),
        ] {
            std::fs::write(dir.join(name), data).unwrap();
        }
        let checked = run(
            &dir,
            &[
                "check",
                "--atom-definition",
                "d.json",
                "--archmap",
                "a.json",
                "--law",
                "l.law",
                "--out",
                "checked",
            ],
        );
        assert_eq!(checked.code, 0, "{}", checked.stdout);
        let result = run(
            &dir,
            &[
                "run",
                "--atom-definition",
                "d.json",
                "--archmap",
                "a.json",
                "--law",
                "l.law",
                "--out",
                "evaluated",
                "--ask",
                "e=evaluate(Selected.quantity,c=@w/p)",
                "--ask",
                "c=check(Selected.positive,c=@w/q)",
                "--ask",
                "m=evaluate(Selected.quantity,c=@x/p)",
            ],
        );
        assert_eq!(result.code, 2, "{}", result.stdout);
        let result = result_json(&dir, &result);
        let answers = arr(get(&result, "answers"));
        assert_eq!(s(get(&answers[0], "status")), "established");
        assert_eq!(s(get(&answers[1], "status")), "established");
        assert_eq!(s(get(&answers[2], "status")), "undetermined");
        let value = get(get(&answers[0], "outputs"), "value");
        let node = arr(get(&result, "nodes"))
            .iter()
            .find(|n| s(get(n, "id")) == s(get(value, "node")))
            .unwrap();
        assert_eq!(s(get(node, "value")), "7");
        assert!(
            arr(get(&answers[2], "reasons"))
                .iter()
                .any(|r| s(get(r, "code")) == "missing_observation")
        );
    }
}
