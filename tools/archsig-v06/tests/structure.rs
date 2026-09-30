//! AC3: 構造(設計 §3.2〜3.5)の回帰例。

use std::collections::BTreeMap;

use archsig::atom::parse_jsonl;
use archsig::expr::parse;
use archsig::structure::{Reason, State, StepKind, Structure, Value};

fn structure(jsonl: &str) -> Structure {
    Structure::new(parse_jsonl(jsonl, "test").unwrap())
}

/// 条件のない手順を順に実行した状態と、書き込みの記録。
fn run(s: &Structure, op: &str) -> (State, Vec<(Vec<String>, Value)>) {
    let (mut branches, _) = archsig::engine::execute(s, op, &|_| false).unwrap();
    assert_eq!(branches.len(), 1, "条件のない操作");
    let b = branches.remove(0);
    (b.state, b.writes.into_iter().map(|w| (w.place, w.value)).collect())
}

fn place(names: &[&str]) -> Vec<String> {
    names.iter().map(|n| n.to_string()).collect()
}

fn c(v: &str) -> Value {
    Value::Const(v.to_string())
}

#[test]
fn two_calls_to_the_same_operation_are_distinct() {
    let s = structure(
        r#"{"kind": "defines", "subject": "m.T", "value": "type", "at": "m.py:1"}
{"kind": "defines", "subject": "m.T.v", "value": "field", "type": "int", "at": "m.py:2"}
{"kind": "defines", "subject": "m.f", "value": "operation", "params": {}, "at": "m.py:4"}
{"kind": "calls", "subject": "m.f", "object": "m.g", "at": "m.py:5"}
{"kind": "passes", "subject": "m.f->m.g", "object": "m.g.$x", "value": "0", "at": "m.py:5"}
{"kind": "calls", "subject": "m.f", "object": "m.g", "at": "m.py:6"}
{"kind": "passes", "subject": "m.f->m.g#2", "object": "m.g.$x", "value": "1", "at": "m.py:6"}
{"kind": "defines", "subject": "m.g", "value": "operation", "params": {"x": "int"}, "at": "m.py:8"}
{"kind": "writes", "subject": "m.g", "object": "m.T.v", "value": "$x", "at": "m.py:9"}
"#,
    );
    let calls: Vec<String> = s
        .unfold("m.f")
        .unwrap()
        .into_iter()
        .filter_map(|st| match st.kind {
            StepKind::Call { call, .. } => Some(call),
            _ => None,
        })
        .collect();
    assert_eq!(calls, vec!["m.f->m.g", "m.f->m.g#2"]);
    let (state, writes) = run(&s, "m.f");
    assert_eq!(writes, vec![(place(&["m.T.v"]), c("0")), (place(&["m.T.v"]), c("1"))], "passes は呼び出しごとに分かれる");
    assert_eq!(state.read(&place(&["m.T.v"])).unwrap(), c("1"), "最後の値は g(1) のもの");
}

#[test]
fn repeated_writes_are_all_kept() {
    // 同じ Atom が三つのうち二つある。同一性で潰さない。
    let s = structure(
        r#"{"kind": "defines", "subject": "m.T.x", "value": "field", "type": "int", "at": "m.py:1"}
{"kind": "defines", "subject": "m.f", "value": "operation", "params": {}, "at": "m.py:3"}
{"kind": "writes", "subject": "m.f", "object": "m.T.x", "value": "0", "at": "m.py:4"}
{"kind": "writes", "subject": "m.f", "object": "m.T.x", "value": "1", "at": "m.py:5"}
{"kind": "writes", "subject": "m.f", "object": "m.T.x", "value": "0", "at": "m.py:6"}
"#,
    );
    let (state, writes) = run(&s, "m.f");
    assert_eq!(writes.iter().map(|(_, v)| v.clone()).collect::<Vec<_>>(), vec![c("0"), c("1"), c("0")]);
    assert_eq!(state.read(&place(&["m.T.x"])).unwrap(), c("0"));
}

#[test]
fn an_element_with_two_kinds_of_defines_is_unresolved() {
    let s = structure(
        r#"{"kind": "defines", "subject": "m.h", "value": "operation", "params": {}, "at": "m.py:1"}
{"kind": "defines", "subject": "m.h", "value": "field", "type": "int", "at": "n.py:1"}
{"kind": "defines", "subject": "m.f", "value": "operation", "params": {}, "at": "m.py:3"}
{"kind": "calls", "subject": "m.f", "object": "m.h", "at": "m.py:4"}
{"kind": "defines", "subject": "m.k", "value": "operation", "params": {}, "at": "m.py:6"}
{"kind": "writes", "subject": "m.k", "object": "m.h", "value": "0", "at": "m.py:7"}
"#,
    );
    assert_eq!(s.kind("m.h").unwrap_err().reason, Reason::Unresolved);
    assert_eq!(s.unfold("m.f").unwrap_err().reason, Reason::Unresolved, "呼び出し先が曖昧");
    assert_eq!(s.unfold("m.k").unwrap_err().reason, Reason::Unresolved, "書き込む先が曖昧");
    assert_eq!(s.unfold("m.h").unwrap_err().reason, Reason::Unresolved, "曖昧な操作そのもの");

    // 式の中の呼び出し先と、引数の型が曖昧なときも沈黙する。
    let s = structure(
        r#"{"kind": "defines", "subject": "m.h", "value": "operation", "params": {}, "at": "m.py:1"}
{"kind": "defines", "subject": "m.h", "value": "field", "type": "int", "at": "n.py:1"}
{"kind": "defines", "subject": "m.T", "value": "type", "at": "m.py:2"}
{"kind": "defines", "subject": "m.T", "value": "operation", "params": {}, "at": "n.py:2"}
{"kind": "defines", "subject": "m.T.v", "value": "field", "type": "int", "at": "m.py:3"}
{"kind": "defines", "subject": "m.U.v", "value": "field", "type": "int", "at": "m.py:4"}
{"kind": "defines", "subject": "m.f", "value": "operation", "params": {}, "at": "m.py:6"}
{"kind": "writes", "subject": "m.f", "object": "m.U.v", "value": "m.h(0)", "at": "m.py:7"}
{"kind": "defines", "subject": "m.k", "value": "operation", "params": {"t": "m.T"}, "at": "m.py:9"}
{"kind": "writes", "subject": "m.k", "object": "m.U.v", "value": "$t.v", "at": "m.py:10"}
"#,
    );
    assert_eq!(s.unfold("m.f").unwrap_err().reason, Reason::Unresolved, "値の中の呼び出し先が曖昧");
    assert_eq!(s.unfold("m.k").unwrap_err().reason, Reason::Unresolved, "引数の型が曖昧");

    // 曖昧な呼び出し先と `?` の呼び出し先は、外部の resolves があっても外部として扱わない。
    let s = structure(
        r#"{"kind": "defines", "subject": "m.h", "value": "operation", "params": {}, "at": "m.py:1"}
{"kind": "defines", "subject": "m.h", "value": "field", "type": "int", "at": "n.py:1"}
{"kind": "resolves", "subject": "m.h", "object": "external:pkg", "at": "m.py:1"}
{"kind": "resolves", "subject": "?mail.send", "object": "external:mail", "at": "m.py:1"}
{"kind": "defines", "subject": "m.f", "value": "operation", "params": {}, "at": "m.py:3"}
{"kind": "calls", "subject": "m.f", "object": "m.h", "at": "m.py:4"}
{"kind": "defines", "subject": "m.g", "value": "operation", "params": {}, "at": "m.py:6"}
{"kind": "calls", "subject": "m.g", "object": "?mail.send", "at": "m.py:7"}
"#,
    );
    assert_eq!(s.unfold("m.f").unwrap_err().reason, Reason::Unresolved);
    assert_eq!(s.unfold("m.g").unwrap_err().reason, Reason::Unresolved);
}

#[test]
fn params_calls_and_channels_are_elements() {
    let s = structure(
        r#"{"kind": "defines", "subject": "m.f", "value": "operation", "params": {"o": "m.T"}, "at": "m.py:1"}
{"kind": "calls", "subject": "m.f", "object": "m.g", "at": "m.py:2"}
{"kind": "sends", "subject": "m.f", "object": "channel:queue:placed:amount", "value": "1", "at": "m.py:3"}
{"kind": "observed", "subject": "m.py", "scope": "structure", "at": "m.py"}
"#,
    );
    assert_eq!(s.kind("m.f.$o").unwrap(), "param");
    assert_eq!(s.kind("m.f->m.g").unwrap(), "call");
    assert_eq!(s.kind("channel:queue:placed:amount").unwrap(), "channel");
    assert_eq!(s.kind("channel:queue:placed").unwrap(), "channel");
}

#[test]
fn unfolding_has_a_limit_on_its_size() {
    // 各段が次の段を二度呼ぶ。再帰はないが、展開すると 2^20 の手順になる。
    let mut jsonl = String::from("{\"kind\": \"defines\", \"subject\": \"m.T.v\", \"value\": \"field\", \"type\": \"int\", \"at\": \"m.py:1\"}\n");
    for d in 0..20 {
        jsonl.push_str(&format!("{{\"kind\": \"defines\", \"subject\": \"m.f{d}\", \"value\": \"operation\", \"params\": {{}}, \"at\": \"m.py:{}\"}}\n", 10 + d * 3));
        for k in 1..=2 {
            jsonl.push_str(&format!("{{\"kind\": \"calls\", \"subject\": \"m.f{d}\", \"object\": \"m.f{}\", \"at\": \"m.py:{}\"}}\n", d + 1, 10 + d * 3 + k));
        }
    }
    jsonl.push_str("{\"kind\": \"defines\", \"subject\": \"m.f20\", \"value\": \"operation\", \"params\": {}, \"at\": \"m.py:100\"}\n");
    jsonl.push_str("{\"kind\": \"writes\", \"subject\": \"m.f20\", \"object\": \"m.T.v\", \"value\": \"1\", \"at\": \"m.py:101\"}\n");
    assert_eq!(structure(&jsonl).unfold("m.f0").unwrap_err().reason, Reason::Limit);
}

#[test]
fn reading_a_place_with_a_later_write_below_it_is_unchecked() {
    let mut state = State::default();
    state.write(place(&["A"]), c("1"));
    state.write(place(&["A", "B"]), c("2"));
    assert_eq!(state.read(&place(&["A", "B"])).unwrap(), c("2"));
    assert_eq!(state.read(&place(&["A"])).unwrap_err().reason, Reason::Unchecked);
}

const SHOP: &str = r#"{"kind": "defines", "subject": "shop.order.model.Order", "value": "type", "at": "shop/order/model.py:7"}
{"kind": "defines", "subject": "shop.order.model.Order.shipping_address", "value": "field", "type": "shop.shipping.address.Address", "at": "shop/order/model.py:9"}
{"kind": "defines", "subject": "shop.order.model.Order.payment_ref", "value": "field", "type": "str", "at": "shop/order/model.py:10"}
{"kind": "defines", "subject": "shop.shipping.address.Address", "value": "type", "at": "shop/shipping/address.py:3"}
{"kind": "defines", "subject": "shop.shipping.address.Address.country", "value": "field", "type": "str", "at": "shop/shipping/address.py:4"}
{"kind": "defines", "subject": "shop.shipping.service.update_shipping", "value": "operation", "params": {"order": "shop.order.model.Order", "new": "shop.shipping.address.Address"}, "at": "shop/shipping/service.py:5"}
"#;

#[test]
fn paths_are_read_as_places() {
    let s = structure(SHOP);
    let op = "shop.shipping.service.update_shipping";
    let env = BTreeMap::new();
    let read = |text: &str| s.resolve(op, &env, &parse(text).unwrap()).unwrap();
    assert_eq!(
        read("$order.shipping_address.country"),
        Value::Read(place(&["shop.order.model.Order.shipping_address", "shop.shipping.address.Address.country"]))
    );
    assert_eq!(read("$new.country"), Value::Read(place(&["shop.shipping.address.Address.country"])));
    assert_eq!(read("$new"), Value::Arg(format!("{op}.$new")));

    // 頭の部分に書き込みがあれば、書き込んだ値からの残りの射影を読む。
    let mut state = State::default();
    let written = Value::Call("shop.shipping.address.normalize_address".to_string(), vec![Value::Arg(format!("{op}.$new"))]);
    state.write(place(&["shop.order.model.Order.shipping_address"]), written.clone());
    assert_eq!(
        state.eval(&read("$order.shipping_address.country")).unwrap(),
        Value::Proj(Box::new(written), place(&["shop.shipping.address.Address.country"]))
    );
    assert_eq!(state.eval(&read("$new.country")).unwrap(), Value::Input(place(&["shop.shipping.address.Address.country"])));
}

#[test]
fn a_passed_path_is_read_through_the_callee() {
    let s = structure(&format!(
        "{SHOP}{}",
        r#"{"kind": "calls", "subject": "shop.shipping.service.update_shipping", "object": "shop.shipping.address.check", "at": "shop/shipping/service.py:6"}
{"kind": "passes", "subject": "shop.shipping.service.update_shipping->shop.shipping.address.check", "object": "shop.shipping.address.check.$addr", "value": "$order.shipping_address", "at": "shop/shipping/service.py:6"}
{"kind": "defines", "subject": "shop.shipping.address.check", "value": "operation", "params": {"addr": "shop.shipping.address.Address"}, "at": "shop/shipping/address.py:8"}
{"kind": "writes", "subject": "shop.shipping.address.check", "object": "shop.order.model.Order.payment_ref", "value": "None", "when": "$addr.country != \"JP\"", "at": "shop/shipping/address.py:9"}
"#
    ));
    let steps = s.unfold("shop.shipping.service.update_shipping").unwrap();
    let write = steps.iter().find(|st| matches!(st.kind, StepKind::Write { .. })).unwrap();
    assert_eq!(
        write.when.iter().map(|c| c.value.clone()).collect::<Vec<_>>(),
        vec![Value::Bin(
            archsig::expr::BinOp::Ne,
            Box::new(Value::Read(place(&["shop.shipping.address.Address.country"]))),
            Box::new(c("\"JP\""))
        )],
        "呼び出し先の `$addr.country` は、引数の型のフィールドの場所 [Address.country] を読む"
    );
}

#[test]
fn an_unread_callee_returns_what_to_read() {
    let s = structure(&format!(
        "{SHOP}{}",
        r#"{"kind": "calls", "subject": "shop.shipping.service.update_shipping", "object": "shop.shipping.address.normalize_address", "at": "shop/shipping/service.py:8"}
{"kind": "resolves", "subject": "shop.shipping.address.normalize_address", "object": "shop/shipping/address.py", "at": "shop/shipping/service.py:2"}
{"kind": "calls", "subject": "shop.shipping.service.notify", "object": "mail.send", "at": "shop/shipping/service.py:12"}
{"kind": "calls", "subject": "shop.shipping.service.notify", "object": "shop.mail.format", "at": "shop/shipping/service.py:13"}
{"kind": "defines", "subject": "shop.shipping.service.notify", "value": "operation", "params": {}, "at": "shop/shipping/service.py:11"}
{"kind": "resolves", "subject": "mail.send", "object": "external:mail", "at": "shop/shipping/service.py:3"}
"#
    ));
    let e = s.unfold("shop.shipping.service.update_shipping").unwrap_err();
    assert_eq!((e.reason, e.read.as_deref()), (Reason::Unread, Some("shop/shipping/address.py")));
    let e = s.unfold("shop.shipping.service.notify").unwrap_err();
    assert_eq!((e.reason, e.element.as_deref()), (Reason::Unread, Some("shop.mail.format")), "resolves がなければ要素の名前");

    // 名前の前の部分の resolves は使わない。
    let s = structure(r#"{"kind": "resolves", "subject": "shop.mail", "object": "shop/mail.py", "at": "shop/a.py:1"}"#);
    let e = s.kind("shop.mail.format").unwrap_err();
    assert_eq!((e.reason, e.read, e.element.as_deref()), (Reason::Unread, None, Some("shop.mail.format")));
}
