//! AC4: 候補を重ねる(設計 §3.6)の回帰例。

use archsig::atom::{Atom, parse_jsonl};
use archsig::structure::{Structure, overlay};

fn atoms(jsonl: &str) -> Vec<Atom> {
    parse_jsonl(jsonl, "test").unwrap()
}

fn pair(a: &str, b: &str) -> (String, String) {
    (a.to_string(), b.to_string())
}

#[test]
fn resolves_in_a_plan_keeps_the_unchanged_definition() {
    let before = atoms(
        r#"{"kind": "defines", "subject": "m.T.v", "value": "field", "type": "int", "at": "m.py:1"}
{"kind": "defines", "subject": "m.g", "value": "operation", "params": {}, "at": "m.py:3"}
{"kind": "writes", "subject": "m.g", "object": "m.T.v", "value": "1", "at": "m.py:4"}
"#,
    );
    let plan = atoms(
        r#"{"kind": "plan", "subject": "add-h", "base": "a1b2c3d"}
{"kind": "defines", "subject": "n.h", "value": "operation", "params": {}, "file": "n.py", "at": "plan:add-h"}
{"kind": "calls", "subject": "n.h", "object": "m.g", "at": "plan:add-h"}
{"kind": "resolves", "subject": "m.g", "object": "m.py", "at": "plan:add-h"}
"#,
    );
    let o = overlay(&before, &plan);
    let s = Structure::new(o.after);
    assert_eq!(s.kind("m.g").unwrap(), "operation", "g の定義が残る");
    assert_eq!(s.unfold("n.h").unwrap().len(), 2, "h から g を呼び、g の書き込みが残る");
    assert!(s.resolves.contains_key("m.g"), "resolves は名前の解決として加わる");
}

const ORDER: &str = r#"{"kind": "defines", "subject": "shop.order.model.Order", "value": "type", "at": "shop/order/model.py:7"}
{"kind": "defines", "subject": "shop.order.model.Order.payment_ref", "value": "field", "type": "str", "at": "shop/order/model.py:10"}
{"kind": "meaning", "subject": "shop.order.model.Order.payment_ref", "meaning": "payment-info", "uses": ["shop/payment/charge.py:6"], "at": "shop/order/model.py:10"}
{"kind": "defines", "subject": "shop.shipping.service.update_shipping", "value": "operation", "params": {"order": "shop.order.model.Order", "new": "str"}, "at": "shop/shipping/service.py:5"}
{"kind": "writes", "subject": "shop.shipping.service.update_shipping", "object": "shop.order.model.Order.payment_ref", "value": "None", "at": "shop/shipping/service.py:7"}
{"kind": "defines", "subject": "shop.payment.charge.charge", "value": "operation", "params": {"order_id": "str"}, "at": "shop/payment/charge.py:4"}
{"kind": "reads", "subject": "shop.payment.charge.charge", "object": "shop.order.model.Order.payment_ref", "at": "shop/payment/charge.py:6"}
"#;

const SPLIT: &str = r#"{"kind": "plan", "subject": "split-order", "base": "a1b2c3d"}
{"kind": "defines", "subject": "shop.payment.model.OrderPayment", "value": "type", "file": "shop/payment/model.py", "at": "plan:split-order"}
{"kind": "defines", "subject": "shop.payment.model.OrderPayment.ref", "value": "field", "type": "str", "file": "shop/payment/model.py", "at": "plan:split-order"}
{"kind": "corresponds", "subject": "shop.order.model.Order.payment_ref", "object": "shop.payment.model.OrderPayment.ref", "at": "plan:split-order"}
{"kind": "corresponds", "subject": "shop.shipping.service.update_shipping.$order", "object": "shop.shipping.service.update_shipping.$payment", "at": "plan:split-order"}
{"kind": "removes", "subject": "shop.order.model.Order", "at": "plan:split-order"}
{"kind": "defines", "subject": "shop.shipping.service.update_shipping", "value": "operation", "params": {"payment": "shop.payment.model.OrderPayment", "new": "str"}, "file": "shop/shipping/service.py", "at": "plan:split-order"}
{"kind": "writes", "subject": "shop.shipping.service.update_shipping", "object": "shop.payment.model.OrderPayment.ref", "value": "None", "at": "plan:split-order"}
"#;

#[test]
fn fields_of_a_removed_type_are_gone() {
    let o = overlay(&atoms(ORDER), &atoms(SPLIT));
    let s = Structure::new(o.after.clone());
    assert!(!s.elements.contains_key("shop.order.model.Order"));
    assert!(!s.elements.contains_key("shop.order.model.Order.payment_ref"), "消えた型のフィールドも消える");
    assert_eq!(s.kind("shop.payment.model.OrderPayment.ref").unwrap(), "field");
    // 意味は対応の行き先へ移る。
    assert_eq!(s.meanings["shop.payment.model.OrderPayment.ref"][0].meaning.as_deref(), Some("payment-info"));
    assert!(!s.meanings.contains_key("shop.order.model.Order.payment_ref"));
}

#[test]
fn an_operation_not_rewritten_that_uses_a_removed_element_is_missing() {
    let o = overlay(&atoms(ORDER), &atoms(SPLIT));
    assert_eq!(o.missing.keys().collect::<Vec<_>>(), vec!["shop.payment.charge.charge"], "書き直した update_shipping は挙がらない");
    assert_eq!(o.missing["shop.payment.charge.charge"].iter().collect::<Vec<_>>(), vec!["shop.order.model.Order.payment_ref"]);
}

#[test]
fn renamed_params_correspond_and_same_names_correspond_to_themselves() {
    let o = overlay(&atoms(ORDER), &atoms(SPLIT));
    let op = "shop.shipping.service.update_shipping";
    assert!(o.corresponds.contains(&pair(&format!("{op}.$order"), &format!("{op}.$payment"))), "名前の変わる引数は corresponds で");
    assert!(o.corresponds.contains(&pair(&format!("{op}.$new"), &format!("{op}.$new"))), "同じ名前の引数は自分自身に");
    assert!(o.corresponds.contains(&pair(op, op)), "同じ名前の要素は自分自身に");
    assert!(o.corresponds.contains(&pair("shop.order.model.Order.payment_ref", "shop.payment.model.OrderPayment.ref")));
    assert!(!o.corresponds.iter().any(|(a, _)| a == "shop.order.model.Order"), "removes した要素は自分自身に対応しない");
}

#[test]
fn params_of_linked_operations_correspond_by_name() {
    let before = atoms(r#"{"kind": "defines", "subject": "m.f", "value": "operation", "params": {"x": "int", "y": "int"}, "at": "m.py:1"}"#);
    let plan = atoms(
        r#"{"kind": "defines", "subject": "n.f2", "value": "operation", "params": {"x": "int"}, "file": "n.py", "at": "plan:p"}
{"kind": "corresponds", "subject": "m.f", "object": "n.f2", "at": "plan:p"}
{"kind": "corresponds", "subject": "m.f.$y", "object": "n.f2.$x | n.f2.$z", "at": "plan:p"}
"#,
    );
    let o = overlay(&before, &plan);
    assert!(o.corresponds.contains(&pair("m.f.$x", "n.f2.$x")), "書いた対応で結んだ操作の、同じ名前の引数");
    assert_eq!(o.undecided, vec![("m.f.$y".to_string(), vec!["n.f2.$x".to_string(), "n.f2.$z".to_string()])], "| の対応は決めていない対応として別に持つ");
}

#[test]
fn two_undecided_correspondences_of_one_element_are_both_kept() {
    let before = atoms(r#"{"kind": "defines", "subject": "m.T.x", "value": "field", "type": "int", "at": "m.py:1"}"#);
    let plan = atoms(
        r#"{"kind": "removes", "subject": "m.T.x", "at": "plan:p"}
{"kind": "corresponds", "subject": "m.T.x", "object": "a.A.x | b.B.x", "at": "plan:p"}
{"kind": "corresponds", "subject": "m.T.x", "object": "c.C.x | d.D.x", "at": "plan:p"}
"#,
    );
    assert_eq!(overlay(&before, &plan).undecided.len(), 2, "一つの要素を二つに分けるなら、対応を二つ書く");
}

#[test]
fn meanings_of_untouched_elements_stay() {
    // 構造をまだ読んでいない要素の意味 Atom も、候補が触れなければ残る。
    let before = atoms(
        r#"{"kind": "meaning", "subject": "z.Z.f", "meaning": "unit", "value": "minor", "uses": ["z.py:3"], "at": "z.py:3"}
{"kind": "defines", "subject": "m.T.v", "value": "field", "type": "int", "at": "m.py:1"}
{"kind": "meaning", "subject": "m.T.v", "meaning": "unit", "value": "yen", "uses": ["m.py:5"], "at": "m.py:1"}
"#,
    );
    let plan = atoms(r#"{"kind": "defines", "subject": "n.h", "value": "operation", "params": {}, "file": "n.py", "at": "plan:p"}"#);
    let s = Structure::new(overlay(&before, &plan).after);
    assert_eq!(s.meanings["z.Z.f"].len(), 1);
    assert_eq!(s.meanings["m.T.v"].len(), 1, "触れていない要素の意味は重ならない");
}

#[test]
fn a_removed_element_defined_again_does_not_correspond_to_itself() {
    let before = atoms(r#"{"kind": "defines", "subject": "m.T.x", "value": "field", "type": "int", "at": "m.py:1"}"#);
    let plan = atoms(
        r#"{"kind": "removes", "subject": "m.T.x", "at": "plan:p"}
{"kind": "defines", "subject": "m.T.x", "value": "field", "type": "str", "file": "m.py", "at": "plan:p"}
"#,
    );
    assert!(overlay(&before, &plan).corresponds.is_empty());
}
