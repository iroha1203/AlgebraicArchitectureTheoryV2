//! 名前の解決(設計 §3.3)。`unread` の読む所は、読めば答えが決まるか、別の読む所に進む。

use archsig::atom::{Atom, parse_jsonl};
use archsig::structure::{Answer, Reason, Resolved, Structure};

fn atoms(jsonl: &str) -> Vec<Atom> {
    parse_jsonl(jsonl, "test").unwrap()
}

/// 答えの読む所。`unread` でなければ None。
fn read_place(r: &Resolved) -> Option<(Option<String>, Option<String>)> {
    match r {
        Err(u) if u.silence.reason == Reason::Unread => Some((u.silence.read.clone(), u.silence.element.clone())),
        _ => None,
    }
}

/// 読む所を読んだ Atom。ソースならその構造を読み、要素ならその定義を `x.py` で読む。
/// `found` は、読んだときにそこで見つかる Atom(ソースの構造、要素の定義)。
fn read(before: &[Atom], found: &str) -> Structure {
    let mut all = before.to_vec();
    all.extend(atoms(found));
    Structure::new(all)
}

/// `name` の答えが `unread` で、`expected` を読む所として返し、`found` を読み足すと、答えが決まるか読む所が変わる。
fn advances(before: &str, name: &str, expected: (Option<&str>, Option<&str>), found: &str) -> Resolved {
    let before = atoms(before);
    let first = Structure::new(before.clone()).element(name);
    let place = read_place(&first).unwrap_or_else(|| panic!("{name} は unread のはず: {first:?}"));
    assert_eq!((place.0.as_deref(), place.1.as_deref()), expected, "{name}: {first:?}");
    let next = read(&before, found).element(name);
    assert_ne!(read_place(&next), Some(place), "{name} は読んだ後も同じ読む所に戻る: {next:?}");
    next
}

#[test]
fn a_source_that_resolves_points_at_is_read_and_the_answer_is_decided() {
    let next = advances(
        r#"{"kind": "resolves", "subject": "m.g", "object": "g.py", "at": "m.py:1"}"#,
        "m.g",
        (Some("g.py"), None),
        r#"{"kind": "observed", "subject": "g.py", "scope": "structure", "at": "g.py"}
{"kind": "defines", "subject": "m.g", "value": "operation", "params": {}, "at": "g.py:1"}"#,
    );
    assert!(matches!(next, Ok(Answer::Element(e)) if e.kind == "operation"));
    // 読んだソースに定義がなければ、定義がないと決まる(`unresolved`)。
    let next = advances(
        r#"{"kind": "resolves", "subject": "m.g", "object": "g.py", "at": "m.py:1"}"#,
        "m.g",
        (Some("g.py"), None),
        r#"{"kind": "observed", "subject": "g.py", "scope": "structure", "at": "g.py"}"#,
    );
    assert_eq!(next.unwrap_err().silence.reason, Reason::Unresolved);
}

#[test]
fn a_head_named_as_a_type_is_read_before_the_name_below_it() {
    // m.C は引数の型として名指されているが、定義を読んでいない。m.C.x の読む所は、頭 m.C の読む所である。
    let before = r#"{"kind": "defines", "subject": "m.f", "value": "operation", "params": {"c": "m.C"}, "at": "m.py:1"}
{"kind": "resolves", "subject": "m.C", "object": "c.py", "at": "m.py:1"}"#;
    let next = advances(
        before,
        "m.C.x",
        (Some("c.py"), None),
        r#"{"kind": "observed", "subject": "c.py", "scope": "structure", "at": "c.py"}
{"kind": "defines", "subject": "m.C", "value": "type", "at": "c.py:1"}
{"kind": "defines", "subject": "m.C.x", "value": "field", "type": "int", "at": "c.py:2"}"#,
    );
    assert!(matches!(next, Ok(Answer::Element(e)) if e.kind == "field"));
    // 頭の resolves がなければ、頭の名前を読む。頭を読むと、読む所は m.C.x に進む。
    let before = r#"{"kind": "defines", "subject": "m.f", "value": "operation", "params": {"c": "m.C"}, "at": "m.py:1"}"#;
    let next = advances(
        before,
        "m.C.x",
        (None, Some("m.C")),
        r#"{"kind": "observed", "subject": "c.py", "scope": "structure", "at": "c.py"}
{"kind": "defines", "subject": "m.C", "value": "type", "at": "c.py:1"}"#,
    );
    assert_eq!(read_place(&next), Some((None, Some("m.C.x".to_string()))));
}

#[test]
fn a_name_below_a_type_that_does_not_define_it_is_read_by_that_name() {
    // 型 m.C を読んだが、m.C.x の定義がない。m.C.x を読めば決まる。
    let next = advances(
        r#"{"kind": "defines", "subject": "m.C", "value": "type", "at": "m.py:1"}"#,
        "m.C.x",
        (None, Some("m.C.x")),
        r#"{"kind": "defines", "subject": "m.C.x", "value": "field", "type": "int", "at": "x.py:1"}"#,
    );
    assert!(matches!(next, Ok(Answer::Element(e)) if e.kind == "field"));
}

#[test]
fn a_name_named_as_a_type_without_a_head_is_read_by_its_own_name() {
    // m.T は引数の型として名指されるだけで、定義も resolves も頭もない(規則 8)。m.T を読めば決まる。
    let next = advances(
        r#"{"kind": "defines", "subject": "m.f", "value": "operation", "params": {"t": "m.T"}, "at": "m.py:1"}"#,
        "m.T",
        (None, Some("m.T")),
        r#"{"kind": "defines", "subject": "m.T", "value": "type", "at": "t.py:1"}"#,
    );
    assert!(matches!(next, Ok(Answer::Element(e)) if e.kind == "type"));
}

#[test]
fn a_name_whose_head_is_unknown_is_read_by_its_own_name() {
    // 頭 m.mod の resolves が読んでいないソースを指す。m.mod は型として名指されていないので、m.mod.var を読む。
    // 読む所の名前を解析器が解決すれば(`resolves`)、その解決で決まるか、読むソースに進む。
    let before = r#"{"kind": "resolves", "subject": "m.mod", "object": "mod.py", "at": "m.py:1"}"#;
    let next = advances(before, "m.mod.var", (None, Some("m.mod.var")), r#"{"kind": "resolves", "subject": "m.mod.var", "object": "external:lib", "at": "m.py:2"}"#);
    assert!(matches!(next, Ok(Answer::External(_))));
    let next = advances(before, "m.mod.var", (None, Some("m.mod.var")), r#"{"kind": "resolves", "subject": "m.mod.var", "object": "mod.py", "at": "m.py:2"}"#);
    assert_eq!(read_place(&next), Some((Some("mod.py".to_string()), None)));
}

#[test]
fn a_deeply_nested_type_is_resolved_once_per_step() {
    // 入れ子の型 m.T0.T1…T40 の各段が型である。頭は一度だけ解くので、段の数に比例して答えが出る。
    let mut jsonl = String::new();
    let mut name = "m.T0".to_string();
    jsonl.push_str(&format!("{{\"kind\": \"defines\", \"subject\": \"{name}\", \"value\": \"type\", \"at\": \"m.py:1\"}}\n"));
    for d in 1..=40 {
        name = format!("{name}.T{d}");
        jsonl.push_str(&format!("{{\"kind\": \"defines\", \"subject\": \"{name}\", \"value\": \"type\", \"at\": \"m.py:{}\"}}\n", d + 1));
    }
    let s = Structure::new(atoms(&jsonl));
    let start = std::time::Instant::now();
    assert!(matches!(s.element(&format!("{name}.x")), Err(u) if u.silence.element == Some(format!("{name}.x"))));
    assert!(start.elapsed() < std::time::Duration::from_secs(5), "{:?}", start.elapsed());
}

#[test]
fn the_same_name_has_the_same_answer_on_every_path() {
    // 式の道、書き込みの場所、要素(名前)の問い合わせが、同じフィールドを同じ要素に解く。
    let s = Structure::new(atoms(
        r#"{"kind": "defines", "subject": "m.O", "value": "type", "at": "m.py:1"}
{"kind": "defines", "subject": "m.O.a", "value": "field", "type": "m.A", "at": "m.py:2"}
{"kind": "defines", "subject": "m.A", "value": "type", "at": "m.py:3"}
{"kind": "defines", "subject": "m.A.x", "value": "field", "type": "int", "at": "m.py:4"}
{"kind": "defines", "subject": "m.f", "value": "operation", "params": {"o": "m.O"}, "at": "m.py:5"}"#,
    ));
    let path = s.walk(archsig::structure::Start::Param("m.f.$o"), &["a".to_string(), "x".to_string()]);
    let column = s.column(&["m.O.a".to_string(), "m.A.x".to_string()]);
    assert!(path.stop.is_none() && column.walk.stop.is_none());
    assert_eq!(path.place, column.walk.place);
    assert!(matches!(s.element("m.A.x"), Ok(Answer::Element(e)) if e.name == path.place[1]));
}
