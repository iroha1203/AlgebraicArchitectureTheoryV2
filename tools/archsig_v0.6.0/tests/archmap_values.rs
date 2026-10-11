//! AC4: 原始値と整合性。欠測と既知値の区別、各型の encoding、参照、由来、補完の存在。

mod common;
use archsig::archmap::{Slot, Value};
use archsig::issue::Code;
use common::*;

const LAW: &str = r#"law "archsig.law/1" semantics "archsig/0.6.0";
reading V {
  entity Sys;
  data Tree = Leaf | Node(Tree, Tree, Z);
  entity Item(owner: Sys) {
    n: Z; q: Q; r: Fp(7); t: Text; b: Bool; u: Unit;
    l: List<Z>; s: Set<Z>; o: Option<Z>; pair: (Z, Text);
    tree: Tree; f: Term<(Z) -> Z>; peer: Item[owner]; mate: Item[owner]; any: Item; m: Z;
  }
  view v(i: Item): Z = i.n;
}
"#;

fn digest() -> String {
    ok(LAW).vocabularies[0].digest.clone()
}

/// subject `(id, 型の短名)` と Atom `(subject, field の短名, 値の JSON)` から ArchMap を作る。
fn doc(subjects: &[(&str, &str)], atoms: &[(&str, &str, &str)]) -> String {
    let subjects: Vec<String> = subjects
        .iter()
        .map(|(id, ty)| format!(r#"{{"id":"{id}","type":"V.{ty}","origin":"o"}}"#))
        .collect();
    let atoms: Vec<String> = atoms
        .iter()
        .enumerate()
        .map(|(i, (s, f, v))| {
            let ty = if *f == "owner" || subjects_type(s) == "Item" {
                "Item"
            } else {
                "Sys"
            };
            format!(
                r#"{{"id":"a{i}","subject":"{s}","field":"V.{ty}.{f}","value":{v},"origin":"o"}}"#
            )
        })
        .collect();
    format!(
        r#"{{"format":"archsig.archmap/1","semantics":"archsig/0.6.0",
"vocabularies":[{{"reading":"V","digest":"{}"}}],"sources":[],
"origins":[{{"id":"o","mode":"specification","method":"手で書いた例","locations":[],"note":"検査の例"}}],
"snapshots":[{{"id":"v","origin":"o","subjects":[{}],"atoms":[{}]}}]}}"#,
        digest(),
        subjects.join(","),
        atoms.join(",")
    )
}

fn subjects_type(s: &str) -> &'static str {
    if s.starts_with(|c: char| c.is_ascii_lowercase()) {
        "Item"
    } else {
        "Sys"
    }
}

const BASE: [(&str, &str); 3] = [("S", "Sys"), ("i", "Item"), ("j", "Item")];

fn item(field: &str, value: &str) -> String {
    doc(
        &BASE,
        &[
            ("i", "owner", r#"["v","S"]"#),
            ("j", "owner", r#"["v","S"]"#),
            ("i", field, value),
        ],
    )
}

fn accepts(field: &str, value: &str) -> Value {
    let c = map_ok(LAW, &item(field, value));
    let i = c.subject("v", "i").unwrap();
    match &i.field(field).unwrap().slot {
        Slot::Known { value, .. } => clone_value(value),
        Slot::Missing => panic!("{field} は既知"),
    }
}

fn clone_value(v: &Value) -> Value {
    match v {
        Value::Z(n) => Value::Z(n.clone()),
        Value::Option(None) => Value::Option(None),
        Value::List(xs) if xs.is_empty() => Value::List(vec![]),
        Value::Set(xs) if xs.is_empty() => Value::Set(vec![]),
        other => panic!("比べない値 {other:?}"),
    }
}

fn rejects(field: &str, value: &str, code: Code) -> String {
    let issue = map_err(LAW, &item(field, value));
    assert_eq!(issue.code, code, "{field}={value} => {issue:?}");
    pointer(&issue).to_owned()
}

#[test]
fn missing_zero_empty_and_none_are_kept_apart() {
    assert_eq!(accepts("n", r#""0""#), Value::Z(0.into()));
    assert_eq!(accepts("o", r#"{"none":true}"#), Value::Option(None));
    assert_eq!(accepts("l", "[]"), Value::List(vec![]));
    assert_eq!(accepts("s", "[]"), Value::Set(vec![]));
    let c = map_ok(LAW, &item("n", r#""0""#));
    let missing: Vec<_> = c
        .missing_slots()
        .into_iter()
        .filter(|m| m.1 == "i")
        .map(|m| m.2.to_owned())
        .collect();
    assert!(missing.contains(&"V.Item.m".to_owned()));
    assert!(missing.contains(&"V.Item.o".to_owned()));
    assert!(!missing.contains(&"V.Item.n".to_owned()));
    let (_, _, _, ty) = c
        .missing_slots()
        .into_iter()
        .find(|m| m.1 == "i" && m.2 == "V.Item.m")
        .unwrap();
    assert_eq!(*ty, archsig::types::Type::Z);
}

#[test]
fn numbers_are_exact_and_canonical() {
    let big = "123456789012345678901234567890123456789";
    assert_eq!(
        accepts("n", &format!("\"-{big}\"")),
        Value::Z(format!("-{big}").parse::<num_bigint::BigInt>().unwrap())
    );
    for bad in [r#""-0""#, r#""01""#, r#""+1""#, r#""1.0""#, "1", r#"" 1""#] {
        rejects("n", bad, Code::Syntax);
    }
    map_ok(LAW, &item("q", r#"["-2","3"]"#));
    map_ok(LAW, &item("q", r#"["0","1"]"#));
    for bad in [
        r#"["2","4"]"#,
        r#"["1","-2"]"#,
        r#"["0","2"]"#,
        r#"["1","0"]"#,
        r#""1""#,
    ] {
        rejects("q", bad, Code::Syntax);
    }
    map_ok(LAW, &item("r", r#""6""#));
    for bad in [r#""7""#, r#""-1""#, r#""08""#] {
        rejects("r", bad, Code::Syntax);
    }
}

#[test]
fn containers_trees_and_terms_follow_their_types() {
    map_ok(LAW, &item("pair", r#"["1","é\u0001"]"#));
    rejects("pair", r#"["1"]"#, Code::Syntax);
    map_ok(LAW, &item("l", r#"["1","1","2"]"#));
    assert_eq!(
        rejects("s", r#"["1","2","1"]"#, Code::Syntax),
        "/snapshots/0/atoms/2/value/2"
    );
    rejects("o", r#"{"some":"1","none":true}"#, Code::Syntax);
    rejects("u", r#"["x"]"#, Code::Syntax);
    rejects("b", r#""true""#, Code::Syntax);
    let tree = r#"{"tag":"Node","args":[{"tag":"Leaf","args":[]},{"tag":"Node","args":[{"tag":"Leaf","args":[]},{"tag":"Leaf","args":[]},"2"]},"1"]}"#;
    map_ok(LAW, &item("tree", tree));
    rejects("tree", r#"{"tag":"Twig","args":[]}"#, Code::Syntax);
    rejects("tree", r#"{"tag":"Node","args":[]}"#, Code::Syntax);
    rejects("tree", r#"{"tag":"V.Tree.Leaf","args":[]}"#, Code::Syntax);
    map_ok(LAW, &item("f", r#"{"params":["x"],"body":"x * x + 1"}"#));
    map_ok(
        LAW,
        &item(
            "f",
            r#"{"params":["x"],"body":"match Tree.Node(Leaf, Leaf, x) { Leaf => 0; Node(a, b, k) => k; }"}"#,
        ),
    );
    rejects("f", r#"{"params":["x","y"],"body":"x"}"#, Code::Syntax);
    rejects("f", r#"{"params":["x"],"body":"x = 1"}"#, Code::Type);
    rejects("f", r#"{"params":["x"],"body":"y + 1"}"#, Code::Reference);
    rejects("f", r#"{"params":["x"],"body":"v(x)"}"#, Code::Reference);
    rejects("f", r#"{"params":["x"],"body":"x +"}"#, Code::Syntax);
    rejects("f", r#"{"params":["in"],"body":"1"}"#, Code::Syntax);
}

#[test]
fn references_carry_their_snapshot_and_declared_type() {
    map_ok(LAW, &item("any", r#"["v","j"]"#));
    rejects("any", r#"["w","j"]"#, Code::Reference);
    rejects("any", r#"["v","k"]"#, Code::Reference);
    rejects("any", r#"["v","S"]"#, Code::Type);
    rejects("any", r#""j""#, Code::Syntax);
    map_ok(LAW, &item("peer", r#"["v","j"]"#));
    // 依存参照は所属先が一致する subject だけを指す。
    let other_owner = doc(
        &[("S", "Sys"), ("T", "Sys"), ("i", "Item"), ("j", "Item")],
        &[
            ("i", "owner", r#"["v","S"]"#),
            ("j", "owner", r#"["v","T"]"#),
            ("i", "peer", r#"["v","j"]"#),
        ],
    );
    let issue = map_err(LAW, &other_owner);
    assert_eq!(
        (issue.code, pointer(&issue)),
        (Code::Reference, "/snapshots/0/atoms/2/value")
    );
}

#[test]
fn completions_exist_for_unknown_owners_and_references() {
    // j の owner が未知でも、S を補えば i.peer の所属条件を満たせる。
    map_ok(
        LAW,
        &doc(
            &BASE,
            &[
                ("i", "owner", r#"["v","S"]"#),
                ("i", "peer", r#"["v","j"]"#),
            ],
        ),
    );
    // i.peer が未知でも、所属の合う Item がある。
    map_ok(
        LAW,
        &doc(
            &BASE,
            &[
                ("i", "owner", r#"["v","S"]"#),
                ("j", "owner", r#"["v","S"]"#),
            ],
        ),
    );
    // i の owner が未知で、peer と mate の所属先が二つの Sys に分かれると補完できない。
    let split = doc(
        &[
            ("S", "Sys"),
            ("T", "Sys"),
            ("i", "Item"),
            ("j", "Item"),
            ("k", "Item"),
        ],
        &[
            ("j", "owner", r#"["v","S"]"#),
            ("k", "owner", r#"["v","T"]"#),
            ("i", "peer", r#"["v","j"]"#),
            ("i", "mate", r#"["v","k"]"#),
        ],
    );
    let issue = map_err(LAW, &split);
    assert_eq!(issue.code, Code::InconsistentObservation, "{issue:?}");
}

#[test]
fn duplicate_facts_are_rejected_even_with_equal_values() {
    let twice = doc(
        &BASE,
        &[
            ("i", "owner", r#"["v","S"]"#),
            ("i", "n", r#""1""#),
            ("i", "n", r#""1""#),
        ],
    );
    let issue = map_err(LAW, &twice);
    assert_eq!(
        (issue.code, pointer(&issue)),
        (Code::DuplicateFact, "/snapshots/0/atoms/2")
    );
}

#[test]
fn origins_and_locations_are_checked() {
    let base = item("n", r#""1""#);
    let variants = [
        (
            r#""locations":[],"note":"検査の例""#,
            r#""locations":[]"#,
            Code::Syntax,
        ),
        (
            r#""mode":"specification""#,
            r#""mode":"observed""#,
            Code::Syntax,
        ),
        (r#""method":"手で書いた例""#, r#""method":"""#, Code::Syntax),
        (
            r#""mode":"specification""#,
            r#""mode":"guessed""#,
            Code::Syntax,
        ),
        (
            r#""snapshots":[{"id":"v","origin":"o""#,
            r#""snapshots":[{"id":"v","origin":"x""#,
            Code::Reference,
        ),
    ];
    for (from, to, code) in variants {
        assert!(base.contains(from), "{from}");
        let issue = map_err(LAW, &base.replacen(from, to, 1));
        assert_eq!(issue.code, code, "{to} => {issue:?}");
    }
    // observed の由来は実在する source の位置を一つ以上持つ。
    let observed = base
        .replace(r#""sources":[]"#, &format!(r#""sources":[{{"id":"src","uri":"file:///repo","revision":"r1","digest":"sha256:{}"}}]"#, "a".repeat(64)))
        .replace(r#""mode":"specification","method":"手で書いた例","locations":[],"note":"検査の例""#, r#""mode":"observed","method":"読んだ","locations":[{"source":"src","path":"src/a.rs","span":[3,9]}]"#);
    map_ok(LAW, &observed);
    for (from, to, code) in [
        (r#""path":"src/a.rs""#, r#""path":"../a.rs""#, Code::Syntax),
        (r#""path":"src/a.rs""#, r#""path":"/a.rs""#, Code::Syntax),
        (r#""path":"src/a.rs""#, r#""path":"""#, Code::Syntax),
        (r#""span":[3,9]"#, r#""span":[9,3]"#, Code::Syntax),
        (
            r#""span":[3,9]"#,
            r#""span":[3,9007199254740992]"#,
            Code::Syntax,
        ),
        (
            r#""source":"src","path""#,
            r#""source":"nope","path""#,
            Code::Reference,
        ),
    ] {
        let issue = map_err(LAW, &observed.replacen(from, to, 1));
        assert_eq!(issue.code, code, "{to} => {issue:?}");
    }
    // snapshot と subject の由来の mode は一致する。
    let mixed = base
        .replace(r#""origins":["#, r#""origins":[{"id":"p","mode":"proposed","method":"案","locations":[],"note":"候補"},"#)
        .replacen(r#"{"id":"i","type":"V.Item","origin":"o"}"#, r#"{"id":"i","type":"V.Item","origin":"p"}"#, 1);
    assert_eq!(map_err(LAW, &mixed).code, Code::Reference);
}
