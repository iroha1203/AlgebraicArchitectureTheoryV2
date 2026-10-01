//! 操作の実行のエンジン(設計 §5.4)。

use archsig::atom::parse_jsonl;
use archsig::engine::execute;
use archsig::structure::Structure;

#[test]
fn fresh_calls_are_distinct_terms_at_each_call_site() {
    let s = Structure::new(
        parse_jsonl(
            r#"{"kind": "defines", "subject": "m.T.a", "value": "field", "type": "str", "at": "m.py:1"}
{"kind": "defines", "subject": "m.T.b", "value": "field", "type": "str", "at": "m.py:2"}
{"kind": "defines", "subject": "m.f", "value": "operation", "params": {}, "at": "m.py:4"}
{"kind": "writes", "subject": "m.f", "object": "m.T.a", "value": "ids.new()", "at": "m.py:5"}
{"kind": "writes", "subject": "m.f", "object": "m.T.b", "value": "ids.new()", "at": "m.py:6"}
"#,
            "test",
        )
        .unwrap(),
    );
    let values = |fresh: &dyn Fn(&str) -> bool| {
        let (branches, _) = execute(&s, "m.f", fresh).unwrap();
        let st = &branches[0].state;
        (st.read(&["m.T.a".to_string()]).unwrap(), st.read(&["m.T.b".to_string()]).unwrap())
    };
    let (a, b) = values(&|n| n == "ids.new");
    assert_ne!(a, b, "fresh の操作の呼び出しは、呼び出しの場所ごとに別の項");
    let (a, b) = values(&|_| false);
    assert_eq!(a, b, "同じ呼び出し先に同じ項を渡せば同じ項");
}

#[test]
fn a_fresh_value_copied_to_another_field_stays_the_same_term() {
    let s = Structure::new(
        parse_jsonl(
            r#"{"kind": "defines", "subject": "m.T", "value": "type", "at": "m.py:1"}
{"kind": "defines", "subject": "m.T.a", "value": "field", "type": "str", "at": "m.py:1"}
{"kind": "defines", "subject": "m.T.b", "value": "field", "type": "str", "at": "m.py:2"}
{"kind": "defines", "subject": "m.f", "value": "operation", "params": {"t": "m.T"}, "at": "m.py:4"}
{"kind": "writes", "subject": "m.f", "object": "m.T.a", "value": "ids.new()", "at": "m.py:5"}
{"kind": "writes", "subject": "m.f", "object": "m.T.b", "value": "$t.a", "at": "m.py:6"}
"#,
            "test",
        )
        .unwrap(),
    );
    let (branches, _) = execute(&s, "m.f", &|n| n == "ids.new").unwrap();
    let st = &branches[0].state;
    assert_eq!(st.read(&["m.T.a".to_string()]).unwrap(), st.read(&["m.T.b".to_string()]).unwrap());
}
