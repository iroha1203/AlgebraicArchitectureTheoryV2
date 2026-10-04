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
    assert!(s.atoms.iter().any(|a| a.kind == "resolves" && a.subject == "m.g"), "resolves は名前の解決として加わる");
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
    assert!(!s.element_names().any(|n| n == "shop.order.model.Order"));
    assert!(!s.element_names().any(|n| n == "shop.order.model.Order.payment_ref"), "消えた型のフィールドも消える");
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

// 以下は、設計 §3.6 とマニュアル第3章「変更の候補」の文ごとの確認。

#[test]
fn rewriting_an_element_drops_its_calls_and_removing_drops_names_below_it() {
    let before = atoms(
        r#"{"kind": "defines", "subject": "m.T.v", "value": "field", "type": "int", "at": "m.py:1"}
{"kind": "defines", "subject": "m.f", "value": "operation", "params": {"p": "int"}, "at": "m.py:3"}
{"kind": "calls", "subject": "m.f", "object": "m.g", "at": "m.py:4"}
{"kind": "passes", "subject": "m.f->m.g", "object": "m.g.$x", "value": "1", "at": "m.py:4"}
{"kind": "meaning", "subject": "m.f.$p", "meaning": "unit", "uses": ["m.py:3"], "at": "m.py:3"}
{"kind": "defines", "subject": "m.g", "value": "operation", "params": {"x": "int"}, "at": "m.py:6"}
{"kind": "calls", "subject": "m.g", "object": "m.k", "at": "m.py:7"}
{"kind": "passes", "subject": "m.g->m.k", "object": "m.k.$y", "value": "2", "at": "m.py:7"}
{"kind": "meaning", "subject": "m.g.$x", "meaning": "unit", "uses": ["m.py:6"], "at": "m.py:6"}
{"kind": "observed", "subject": "m.py", "scope": "structure", "at": "m.py"}
"#,
    );
    let plan = atoms(
        r#"{"kind": "defines", "subject": "m.f", "value": "operation", "params": {"p": "int"}, "file": "m.py", "at": "plan:p"}
{"kind": "writes", "subject": "m.f", "object": "m.T.v", "value": "$p", "at": "plan:p"}
{"kind": "removes", "subject": "m.g", "at": "plan:p"}
"#,
    );
    let after = overlay(&before, &plan).after;
    assert!(!after.iter().any(|a| a.subject == "m.f->m.g"), "書き直した要素から出る呼び出しの Atom も外す");
    assert!(!after.iter().any(|a| a.subject == "m.g->m.k"), "removes した X の X->… を外す");
    assert!(!after.iter().any(|a| a.subject == "m.g.$x"), "removes した X の X.$… を外す");
    assert_eq!(after.iter().filter(|a| a.subject == "m.f.$p").count(), 1, "書き直した操作の同じ名前の引数の意味は、自分自身に移る");
}

#[test]
fn removing_an_element_does_not_drop_a_source_with_a_similar_path() {
    // 要素 `setup` とソース `setup.c` は別の名前の空間にある。
    let before = atoms(
        r#"{"kind": "defines", "subject": "setup", "value": "operation", "params": {}, "at": "setup.c:1"}
{"kind": "observed", "subject": "setup.c", "scope": "structure", "at": "setup.c"}
"#,
    );
    let plan = atoms(r#"{"kind": "removes", "subject": "setup", "at": "plan:p"}"#);
    let s = Structure::new(overlay(&before, &plan).after);
    assert!(s.observed("setup.c", "structure"));
}

#[test]
fn a_rewritten_operation_follows_the_order_of_the_plan() {
    // 候補の中の Atom は行を持たないので、手順と #2 はファイルに書いた Atom の順。
    let before = atoms(
        r#"{"kind": "defines", "subject": "m.T.v", "value": "field", "type": "int", "at": "m.py:1"}
{"kind": "defines", "subject": "m.g", "value": "operation", "params": {"x": "int"}, "at": "m.py:3"}
{"kind": "writes", "subject": "m.g", "object": "m.T.v", "value": "$x", "at": "m.py:4"}
"#,
    );
    let plan = atoms(
        r#"{"kind": "defines", "subject": "m.f", "value": "operation", "params": {}, "file": "m.py", "at": "plan:p"}
{"kind": "calls", "subject": "m.f", "object": "m.g", "at": "plan:p"}
{"kind": "passes", "subject": "m.f->m.g", "object": "m.g.$x", "value": "1", "at": "plan:p"}
{"kind": "writes", "subject": "m.f", "object": "m.T.v", "value": "5", "at": "plan:p"}
{"kind": "calls", "subject": "m.f", "object": "m.g", "at": "plan:p"}
{"kind": "passes", "subject": "m.f->m.g#2", "object": "m.g.$x", "value": "2", "at": "plan:p"}
"#,
    );
    let s = Structure::new(overlay(&before, &plan).after);
    let steps: Vec<String> = s.unfold("m.f").unwrap().into_iter().map(|st| format!("{:?}", st.kind)).collect();
    assert_eq!(steps.len(), 5);
    assert!(steps[0].contains("m.f->m.g\""), "{steps:?}");
    assert!(steps[3].contains("m.f->m.g#2"), "{steps:?}");
    // 書き込みの値は、呼び出しで渡した値で決まる。
    let (branches, _) = archsig::engine::execute(&s, "m.f", &|_| false).unwrap();
    let values: Vec<String> = branches[0].writes.iter().map(|w| archsig::engine::show(&w.value)).collect();
    assert_eq!(values, vec!["1", "5", "2"]);
}

#[test]
fn missing_counts_every_way_an_operation_uses_a_removed_element() {
    let before = atoms(
        r#"{"kind": "defines", "subject": "m.A", "value": "type", "at": "m.py:1"}
{"kind": "defines", "subject": "m.A.flag", "value": "field", "type": "bool", "at": "m.py:2"}
{"kind": "defines", "subject": "m.O", "value": "type", "at": "m.py:3"}
{"kind": "defines", "subject": "m.O.a", "value": "field", "type": "m.A", "at": "m.py:4"}
{"kind": "defines", "subject": "m.O.n", "value": "field", "type": "int", "at": "m.py:5"}
{"kind": "defines", "subject": "m.old", "value": "operation", "params": {}, "at": "m.py:6"}
{"kind": "defines", "subject": "m.by_type", "value": "operation", "params": {"a": "m.A"}, "at": "m.py:10"}
{"kind": "defines", "subject": "m.by_when", "value": "operation", "params": {"o": "m.O"}, "at": "m.py:12"}
{"kind": "writes", "subject": "m.by_when", "object": "m.O.n", "value": "1", "when": "$o.a.flag", "at": "m.py:13"}
{"kind": "defines", "subject": "m.by_value", "value": "operation", "params": {}, "at": "m.py:15"}
{"kind": "writes", "subject": "m.by_value", "object": "m.O.n", "value": "m.old()", "at": "m.py:16"}
{"kind": "defines", "subject": "m.by_passes", "value": "operation", "params": {"o": "m.O"}, "at": "m.py:18"}
{"kind": "calls", "subject": "m.by_passes", "object": "m.k", "at": "m.py:19"}
{"kind": "passes", "subject": "m.by_passes->m.k", "object": "m.k.$x", "value": "$o.a.flag", "at": "m.py:19"}
{"kind": "reads", "subject": "m.undefined", "object": "m.A.flag", "at": "x.py:3"}
{"kind": "defines", "subject": "m.amb", "value": "operation", "params": {}, "at": "m.py:21"}
{"kind": "defines", "subject": "m.amb", "value": "field", "type": "int", "at": "n.py:1"}
{"kind": "reads", "subject": "m.amb", "object": "m.A.flag", "at": "m.py:22"}
{"kind": "defines", "subject": "m.unrelated", "value": "operation", "params": {}, "at": "m.py:24"}
{"kind": "resolves", "subject": "m.unrelated", "object": "m.A.py", "at": "m.py:24"}
"#,
    );
    let plan = atoms(
        r#"{"kind": "removes", "subject": "m.A", "at": "plan:p"}
{"kind": "removes", "subject": "m.old", "at": "plan:p"}
"#,
    );
    let missing = overlay(&before, &plan).missing;
    assert_eq!(missing["m.by_type"].iter().collect::<Vec<_>>(), vec!["m.A"], "引数の型");
    assert_eq!(missing["m.by_when"].iter().collect::<Vec<_>>(), vec!["m.A.flag"], "when の中の $o.a.flag");
    assert_eq!(missing["m.by_value"].iter().collect::<Vec<_>>(), vec!["m.old"], "value の中の呼び出し");
    assert_eq!(missing["m.by_passes"].iter().collect::<Vec<_>>(), vec!["m.A.flag"], "呼び出しの passes の式");
    assert_eq!(missing["m.undefined"].iter().collect::<Vec<_>>(), vec!["m.A.flag"], "定義を読んでいない操作も、書き直していなければ挙がる");
    assert!(missing.contains_key("m.amb"), "曖昧な要素でも、名指す事実は返す。結論はエンジンが決める");
    assert!(!missing.contains_key("m.unrelated"), "resolves の object はソースのパスで、要素の名前ではない");
}

#[test]
fn the_meaning_of_a_renamed_param_moves_away_from_the_old_name() {
    let before = atoms(
        r#"{"kind": "defines", "subject": "s.f", "value": "operation", "params": {"order": "s.O"}, "at": "s.py:1"}
{"kind": "meaning", "subject": "s.f.$order", "meaning": "payment-info", "uses": ["s.py:2"], "at": "s.py:1"}
"#,
    );
    let plan = atoms(
        r#"{"kind": "defines", "subject": "s.f", "value": "operation", "params": {"payment": "s.P"}, "file": "s.py", "at": "plan:p"}
{"kind": "corresponds", "subject": "s.f.$order", "object": "s.f.$payment", "at": "plan:p"}
{"kind": "corresponds", "subject": "s.f.$gone", "at": "plan:p"}
"#,
    );
    let o = overlay(&before, &plan);
    let s = Structure::new(o.after);
    assert!(s.meanings.contains_key("s.f.$payment"));
    assert!(!s.meanings.contains_key("s.f.$order"), "移した意味は、なくなった元の要素に残らない");
    assert!(!o.corresponds.iter().any(|(a, _)| a == "s.f.$gone"), "行き先のない corresponds は対応を作らない");
}

#[test]
fn the_meaning_of_an_untouched_channel_item_stays() {
    // 書き直した操作だけが送っていた項目は要素でなくなるが、候補はその項目に触れていない。
    let before = atoms(
        r#"{"kind": "defines", "subject": "m.f", "value": "operation", "params": {}, "at": "m.py:1"}
{"kind": "sends", "subject": "m.f", "object": "channel:queue:orders:id", "value": "1", "at": "m.py:2"}
{"kind": "meaning", "subject": "channel:queue:orders:id", "meaning": "id", "uses": ["m.py:2"], "at": "m.py:2"}
"#,
    );
    let plan = atoms(r#"{"kind": "defines", "subject": "m.f", "value": "operation", "params": {}, "file": "m.py", "at": "plan:p"}"#);
    let s = Structure::new(overlay(&before, &plan).after);
    assert!(s.meanings.contains_key("channel:queue:orders:id"));
}

#[test]
fn a_bar_makes_an_undecided_correspondence_even_with_one_target() {
    let before = atoms(r#"{"kind": "defines", "subject": "m.T.x", "value": "field", "type": "int", "at": "m.py:1"}"#);
    let plan = atoms(r#"{"kind": "corresponds", "subject": "m.T.x", "object": "a.A.x |", "at": "plan:p"}"#);
    let o = overlay(&before, &plan);
    assert_eq!(o.undecided, vec![("m.T.x".to_string(), vec!["a.A.x".to_string()])], "行き先に | があれば、決めていない対応");
    assert!(!o.corresponds.contains(&pair("m.T.x", "a.A.x")));
}

#[test]
fn missing_does_not_count_atoms_the_plan_replaced() {
    // 候補が呼び出しの passes だけを書き直した。置き換わった古い passes は、もう消える要素を使わない。
    let before = atoms(
        r#"{"kind": "defines", "subject": "m.A.f", "value": "field", "type": "int", "at": "m.py:1"}
{"kind": "defines", "subject": "m.f", "value": "operation", "params": {"a": "m.B"}, "at": "m.py:3"}
{"kind": "defines", "subject": "m.B.a", "value": "field", "type": "m.A", "at": "m.py:2"}
{"kind": "calls", "subject": "m.f", "object": "m.g", "at": "m.py:4"}
{"kind": "passes", "subject": "m.f->m.g", "object": "m.g.$x", "value": "$a.a.f", "at": "m.py:4"}
"#,
    );
    let plan = atoms(
        r#"{"kind": "removes", "subject": "m.A", "at": "plan:p"}
{"kind": "passes", "subject": "m.f->m.g", "object": "m.g.$x", "value": "1", "at": "plan:p"}
"#,
    );
    assert!(!overlay(&before, &plan).missing.contains_key("m.f"));
}

#[test]
fn a_rewritten_operation_whose_definition_was_not_read_keeps_its_meaning() {
    let before = atoms(
        r#"{"kind": "defines", "subject": "m.T.v", "value": "field", "type": "int", "at": "m.py:1"}
{"kind": "writes", "subject": "m.f", "object": "m.T.v", "value": "1", "at": "f.py:2"}
{"kind": "meaning", "subject": "m.f", "meaning": "role", "value": "writer", "uses": ["f.py:2"], "at": "f.py:1"}
"#,
    );
    let plan = atoms(r#"{"kind": "defines", "subject": "m.f", "value": "operation", "params": {}, "file": "f.py", "at": "plan:p"}"#);
    let o = overlay(&before, &plan);
    assert!(o.corresponds.contains(&pair("m.f", "m.f")), "Atom のある名前は変更前にある要素");
    assert_eq!(Structure::new(o.after).meanings["m.f"].len(), 1);
}

#[test]
fn a_bar_without_targets_makes_no_correspondence() {
    let before = atoms(r#"{"kind": "defines", "subject": "m.e", "value": "operation", "params": {"x": "int"}, "at": "m.py:6"}"#);
    let plan = atoms(r#"{"kind": "corresponds", "subject": "m.e.$x", "object": "|", "at": "plan:p"}"#);
    let o = overlay(&before, &plan);
    assert!(o.undecided.is_empty(), "行き先のない | は、決めていない対応を作らない");
    assert!(o.corresponds.iter().all(|(_, t)| !t.is_empty()), "行き先が空の対応も作らない");
}
