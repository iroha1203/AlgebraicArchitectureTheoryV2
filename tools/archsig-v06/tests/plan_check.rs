//! AC5・AC8: `archsig plan check` と `archsig show`(マニュアル第2章の題材、第5章 問い3、第6章)。

use archsig::structure::STEP_LIMIT;
use serde_json::Value;

mod common;

use common::*;

const UPDATE: &str = "shop.shipping.service.update_shipping";

#[test]
fn an_unread_callee_is_silent_and_returns_the_source_to_read() {
    let repo = shop("unread");
    // 候補の update_shipping は、元が読まれていない normalize_address を呼ぶ(第2章 4.)。
    // reset_authorization の行は、呼び出しより前に置いて、呼び出しの順を候補の順にそろえる。
    repo.write(".archsig/plans/split-order/plan.jsonl", SPLIT);
    let s = repo.run(&["plan", "check", "split-order"]);
    let r = result(&s, UPDATE);
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unread")), "{s}");
    let next = s["next"].as_array().unwrap();
    let address = next.iter().find(|n| n["read"] == "shop/shipping/address.py").unwrap_or_else(|| panic!("{s}"));
    assert_eq!(address["scope"], "structure");
    // 読む所ごとにまとめる(AC8)。候補が Order を消すので、normalize_address が消える要素を使うかも、同じソースで決まる。
    // 変更の前後にある normalize_address は自分自身に対応し、その組も同じソースで決まる。
    let removes = result(&s, "removes")["id"].clone();
    let normalize = result(&s, "shop.shipping.address.normalize_address");
    assert_eq!((normalize["outcome"].as_str(), normalize["reason"].as_str()), (Some("silent"), Some("unread")), "{s}");
    let mut decides: Vec<&str> = address["decides"].as_array().unwrap().iter().map(|d| d.as_str().unwrap()).collect();
    decides.sort();
    let mut expected = vec![r["id"].as_str().unwrap(), removes.as_str().unwrap(), normalize["id"].as_str().unwrap()];
    expected.sort();
    assert_eq!(decides, expected);
    // fix_address は引数の型に消える Order を使うので、比べる組ではなく missing として挙がる。
    let fix = result(&s, "shop.shipping.service.fix_address");
    assert_eq!((fix["outcome"].as_str(), fix["kind"].as_str()), (Some("fails"), Some("missing")), "{s}");
}

#[test]
fn a_callee_without_resolves_returns_the_element_to_read() {
    let repo = shop("element");
    repo.map("shop/shipping/service.py", &SERVICE.replace(
        r#"{"kind": "resolves", "subject": "shop.shipping.address.normalize_address", "object": "shop/shipping/address.py", "at": "shop/shipping/service.py:1@blob:3f2a9c1"}
"#,
        "",
    ));
    repo.write(".archsig/plans/split-order/plan.jsonl", SPLIT);
    let s = repo.run(&["plan", "check", "split-order"]);
    let next = s["next"].as_array().unwrap();
    assert!(next.iter().any(|n| n["element"] == "shop.shipping.address.normalize_address" && n.get("read").is_none()), "{s}");
}

#[test]
fn a_counterexample_has_the_check_data_of_chapter_2() {
    let repo = shop("counter");
    repo.map("shop/shipping/address.py", ADDRESS);
    repo.write(".archsig/plans/split-order/plan.jsonl", SPLIT);
    let s = repo.run(&["plan", "check", "split-order"]);
    let r = result(&s, UPDATE);
    assert_eq!((r["outcome"].as_str(), r["kind"].as_str()), (Some("fails"), Some("counterexample")), "{s}");
    let d = repo.run(&["show", r["id"].as_str().unwrap()]);
    let check = &d["check"];
    // 入力が満たす条件。when の字句と場所も付ける。
    let branch = check["branch"].as_array().unwrap();
    assert!(
        branch.iter().any(|c| c["when"] == "$new.country != $order.shipping_address.country" && c["at"] == "shop/shipping/service.py:4@blob:3f2a9c1"),
        "{check}"
    );
    // 二つの順番でたどった書き込みの列
    let before: Vec<&str> = check["before_then_move"]["writes"].as_array().unwrap().iter().map(|w| w["object"].as_str().unwrap()).collect();
    assert_eq!(before, vec!["shop.order.model.Order.payment_ref", "shop.order.model.Order.shipping_address"]);
    let after: Vec<&str> = check["move_then_after"]["writes"].as_array().unwrap().iter().map(|w| w["object"].as_str().unwrap()).collect();
    assert_eq!(after, vec!["shop.shipping.model.OrderShipping.address"]);
    // それぞれの最後の値と、食い違いの元の書き込み
    let div = &check["diverging"][0];
    assert_eq!(div["place"], serde_json::json!(["shop.payment.model.OrderPayment.ref"]));
    assert_eq!(div["before_then_move"], "None");
    assert_eq!(div["move_then_after"], "in(shop.payment.model.OrderPayment.ref)");
    assert_eq!(div["writes"]["before"]["at"], "shop/shipping/service.py:4@blob:3f2a9c1");
    assert!(div["writes"]["after"].is_null(), "候補に、これに対応する書き込みがない");
    assert!(d["conditions"].as_array().unwrap().iter().any(|c| c.as_str().unwrap().contains("同じ型の別々の実体")));
}

#[test]
fn the_fixed_plan_holds_on_both_branches() {
    let repo = shop("holds");
    repo.map("shop/shipping/address.py", ADDRESS);
    // reset_authorization の呼び出しを、配送先の書き込みより前に置く。
    let fixed = SPLIT.replace(
        r#"{"kind": "calls", "subject": "shop.shipping.service.update_shipping", "object": "shop.shipping.address.normalize_address", "at": "plan:split-order"}"#,
        &format!(
            "{}\n{}",
            RESET.trim_end(),
            r#"{"kind": "calls", "subject": "shop.shipping.service.update_shipping", "object": "shop.shipping.address.normalize_address", "at": "plan:split-order"}"#
        ),
    );
    repo.write(".archsig/plans/split-order/plan.jsonl", &fixed);
    let s = repo.run(&["plan", "check", "split-order"]);
    let r = result(&s, UPDATE);
    assert_eq!(r["outcome"], "holds", "{s}");
    let d = repo.run(&["show", r["id"].as_str().unwrap()]);
    // 比べた分岐と、分岐ごとの値(国が変わる / 変わらない)
    let branches = d["check"]["branches"].as_array().unwrap();
    assert_eq!(branches.len(), 2, "{d}");
    let values: Vec<(&str, &str)> = branches
        .iter()
        .map(|b| {
            let v = &b["values"][0];
            (v["before_then_move"].as_str().unwrap(), v["move_then_after"].as_str().unwrap())
        })
        .collect();
    assert!(values.contains(&("None", "None")), "{values:?}");
    assert!(values.contains(&("in(shop.payment.model.OrderPayment.ref)", "in(shop.payment.model.OrderPayment.ref)")), "{values:?}");
}

#[test]
fn an_external_call_is_a_condition() {
    let repo = shop("external");
    repo.map("shop/shipping/address.py", &format!(
        "{ADDRESS}{}",
        r#"{"kind": "calls", "subject": "shop.shipping.address.normalize_address", "object": "requests.post", "at": "shop/shipping/address.py:7@blob:9f2c4e7"}
{"kind": "resolves", "subject": "requests.post", "object": "external:requests", "at": "shop/shipping/address.py:1@blob:9f2c4e7"}
"#
    ));
    repo.write(".archsig/plans/split-order/plan.jsonl", SPLIT);
    let s = repo.run(&["plan", "check", "split-order"]);
    let r = result(&s, UPDATE);
    assert_eq!(r["kind"], "counterexample", "外部の呼び出しがあっても計算する: {s}");
    let d = repo.run(&["show", r["id"].as_str().unwrap()]);
    assert!(d["conditions"].as_array().unwrap().iter().any(|c| c.as_str().unwrap().contains("外部の要素 requests.post")), "{d}");
    let writes = d["check"]["before_then_move"]["writes"].as_array().unwrap();
    assert!(writes.iter().all(|w| !w["object"].as_str().unwrap().starts_with("requests")), "外部の呼び出しは書き込みなし: {d}");
    // 外部の要素そのものは、比べる組にならない。
    assert!(s["results"].as_array().unwrap().iter().all(|r| r["subject"] != "requests.post"), "{s}");
}

#[test]
fn too_many_branches_are_silent_with_limit() {
    let repo = shop("limit");
    repo.map("shop/shipping/address.py", ADDRESS);
    // 条件の違う書き込みを 9 つ並べると、分岐は 2^9 = 512 で上限 256 を超える。
    let mut many = String::new();
    for i in 0..9 {
        many.push_str(&format!(
            r#"{{"kind": "writes", "subject": "{UPDATE}", "object": "shop.order.model.Order.order_id", "value": "{i}", "when": "$new.country == \"c{i}\"", "at": "shop/shipping/service.py:{}@blob:3f2a9c1"}}
"#,
            20 + i
        ));
    }
    repo.map("shop/shipping/service.py", &format!("{SERVICE}{many}"));
    repo.write(".archsig/plans/split-order/plan.jsonl", SPLIT);
    let s = repo.run(&["plan", "check", "split-order"]);
    assert_eq!(result(&s, UPDATE)["reason"], "limit", "{s}");
}

#[test]
fn a_run_is_kept_and_other_rules_are_not_computed() {
    let repo = shop("run");
    repo.write(
        ".archsig/law/shop.law",
        &format!("{LAW}\nlaw no-mail\n  \"メールは送らない\"\n  no call to \"mail.send\"\n"),
    );
    repo.map("shop/shipping/address.py", ADDRESS);
    repo.write(".archsig/plans/split-order/plan.jsonl", SPLIT);
    let s = repo.run(&["plan", "check", "split-order"]);
    assert_eq!(s["not_computed"], serde_json::json!(["no-mail"]), "changes 以外の規則の Law は not_computed に並ぶ");
    let run = s["run"].as_str().unwrap();
    assert_eq!(run, "r-0001");
    let dir = repo.dir.join(".archsig/runs").join(run);
    assert!(dir.join("summary.json").is_file());
    let n = s["results"].as_array().unwrap().len();
    for i in 1..=n {
        assert!(dir.join(format!("{i}.json")).is_file());
    }
    let d = repo.run(&["show", &format!("{run}/1")]);
    assert!(d.get("check").is_some() && d.get("basis").is_some() && d.get("theory").is_some(), "{d}");
    // 二回目の実行は次の番号になる。
    assert_eq!(repo.run(&["plan", "check", "split-order"])["run"], "r-0002");
}

#[test]
fn a_question_mark_says_what_to_read() {
    let repo = shop("question");
    repo.map("shop/shipping/address.py", ADDRESS);
    // 解析器が名前を解決できなかった呼び出しと、形に直せなかった値。
    repo.map("shop/shipping/service.py", &SERVICE.replace(
        r#""value": "shop.shipping.address.normalize_address($new)""#,
        r#""value": "?norm($new)""#,
    ));
    repo.write(".archsig/plans/split-order/plan.jsonl", SPLIT);
    let s = repo.run(&["plan", "check", "split-order"]);
    let r = result(&s, UPDATE);
    assert_eq!(r["reason"], "unresolved", "{s}");
    // `?` の名前や値のせいで沈黙した結論には、その Atom の場所を返す(マニュアル第5章 問い8)。
    assert!(
        s["next"].as_array().unwrap().iter().any(|n| n["read"] == "shop/shipping/service.py" && n["decides"].as_array().unwrap().contains(&r["id"])),
        "? による unresolved には、何を読めば決まるかが付く: {s}"
    );

    repo.map("shop/shipping/service.py", &SERVICE.replace(r#""value": "None", "when""#, r#""value": "?", "when""#));
    let s = repo.run(&["plan", "check", "split-order"]);
    let r = result(&s, UPDATE);
    assert_eq!(r["reason"], "unresolved", "{s}");
    assert!(s["next"].as_array().unwrap().iter().any(|n| n["read"] == "shop/shipping/service.py" && n["decides"].as_array().unwrap().contains(&r["id"])), "{s}");
}

#[test]
fn a_question_mark_in_a_plan_returns_the_element() {
    let repo = shop("question-plan");
    repo.map("shop/shipping/address.py", ADDRESS);
    // 候補の中の Atom の場所はソースではないので、その要素の名前を返す。
    repo.write(".archsig/plans/split-order/plan.jsonl", &SPLIT.replace(
        r#""value": "shop.shipping.address.normalize_address($new)", "at": "plan:split-order""#,
        r#""value": "?", "at": "plan:split-order""#,
    ));
    let s = repo.run(&["plan", "check", "split-order"]);
    let r = result(&s, UPDATE);
    assert_eq!(r["reason"], "unresolved", "{s}");
    assert!(s["next"].as_array().unwrap().iter().any(|n| n["element"] == UPDATE && n.get("read").is_none()), "{s}");
}

#[test]
fn an_undecided_correspondence_makes_the_law_silent() {
    let repo = shop("undecided");
    repo.map("shop/shipping/address.py", ADDRESS);
    repo.write(".archsig/plans/split-order/plan.jsonl", &SPLIT.replace(
        r#""object": "shop.payment.model.OrderPayment.ref""#,
        r#""object": "shop.payment.model.OrderPayment.ref | shop.shipping.model.OrderShipping.order_id""#,
    ));
    let s = repo.run(&["plan", "check", "split-order"]);
    let r = result(&s, "payment-info");
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unresolved")), "{s}");
}

#[test]
fn a_law_without_operation_pairs_holds() {
    let repo = Repo::new("nopairs");
    repo.write(".archsig/law/shop.law", LAW);
    // 操作のない ArchMap に型だけを足す候補。対応する操作の組がないので、比べるものがない。
    repo.map("shop/order/model.py", ORDER);
    repo.write(
        ".archsig/plans/add-type/plan.jsonl",
        r#"{"kind": "defines", "subject": "shop.gift.model.Gift", "value": "type", "file": "shop/gift/model.py", "at": "plan:add-type"}
"#,
    );
    let s = repo.run(&["plan", "check", "add-type"]);
    let r = result(&s, "payment-info");
    assert_eq!(r["outcome"], "holds", "{s}");
    assert_eq!(repo.run(&["show", r["id"].as_str().unwrap()])["check"]["pairs"], serde_json::json!([]));
}

#[test]
fn a_written_field_whose_meaning_was_not_read_is_silent() {
    // Order.payment_ref のソースで、payment-info の意味を読んでいない。
    let run = |name: &str, meaning_atom: bool| {
        let repo = shop(name);
        repo.map("shop/shipping/address.py", ADDRESS);
        let mut order = ORDER.replace(
            r#"{"kind": "observed", "subject": "shop/order/model.py", "scope": "meaning:payment-info", "at": "shop/order/model.py@blob:1d9e3b4"}
"#,
            "",
        );
        if !meaning_atom {
            order = order.lines().filter(|l| !(l.contains(r#""kind": "meaning""#) && l.contains("Order.payment_ref"))).map(|l| format!("{l}\n")).collect();
        }
        repo.map("shop/order/model.py", &order);
        repo.write(".archsig/plans/split-order/plan.jsonl", SPLIT);
        repo.run(&["plan", "check", "split-order"])
    };
    // 意味 Atom があってもなくても、書いたフィールドが意味を持つかは、そのソースの意味を読めば決まる。
    // 意味 Atom があるとき、移した先の OrderPayment.ref で二つの順番の値が食い違うが、その場所の意味が決まらないので反例にしない。
    for (name, meaning_atom) in [("meaning", false), ("meaning-atom", true)] {
        let s = run(name, meaning_atom);
        let r = result(&s, UPDATE);
        assert_eq!(r["reason"], "unread", "{name}: {s}");
        assert!(
            s["next"].as_array().unwrap().iter().any(|n| n["read"] == "shop/order/model.py" && n["scope"] == "meaning:payment-info"),
            "書いたフィールドが意味を持つかは、そのソースの意味を読めば決まる: {name}: {s}"
        );
    }
}

#[test]
fn conditions_of_the_same_shape_have_the_same_truth() {
    let repo = shop("shape");
    repo.map("shop/shipping/address.py", ADDRESS);
    // 候補は、同じ条件を `not (a == b)` の形で書く。`a != b` と同じ原子になる。
    let fixed = SPLIT.replace(
        r#"{"kind": "calls", "subject": "shop.shipping.service.update_shipping", "object": "shop.shipping.address.normalize_address", "at": "plan:split-order"}"#,
        &format!(
            "{}\n{}",
            RESET.trim_end().replace("$new.country != $shipping.address.country", "not ($shipping.address.country == $new.country)"),
            r#"{"kind": "calls", "subject": "shop.shipping.service.update_shipping", "object": "shop.shipping.address.normalize_address", "at": "plan:split-order"}"#
        ),
    );
    repo.write(".archsig/plans/split-order/plan.jsonl", &fixed);
    let s = repo.run(&["plan", "check", "split-order"]);
    assert_eq!(result(&s, UPDATE)["outcome"], "holds", "{s}");
}

#[test]
fn local_meaning_atoms_are_unchecked() {
    let repo = shop("local");
    repo.map("shop/shipping/address.py", ADDRESS);
    repo.write(
        ".archsig/local/module/shop/payment.jsonl",
        r#"{"kind": "meaning", "subject": "local:module:shop/payment", "meaning": "payment-info", "uses": ["shop/payment/charge.py:22@blob:8b41d07"], "at": "shop/payment", "by": "model"}
"#,
    );
    repo.write(".archsig/plans/split-order/plan.jsonl", SPLIT);
    let s = repo.run(&["plan", "check", "split-order"]);
    let r = result(&s, "payment-info");
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unchecked")), "局所ごとの意味 Atom を配る幾何はまだない: {s}");
}

const KEEP: &str = r#"sources "shop/**"

reading module = dir(depth: 2)

meaning payment-info on field
  "注文の支払いを特定する値。"

law payment-info-kept
  "決済情報は変更の後も残る。"
  about payment-info
  changes keep
"#;

fn keep_repo(name: &str) -> Repo {
    let repo = shop(name);
    repo.write(".archsig/law/shop.law", KEEP);
    repo.write("shop/order/model.py", "class Order: ...\n");
    repo
}

#[test]
fn changes_keep_holds_when_the_meaning_has_a_correspondence() {
    let repo = keep_repo("keep-holds");
    repo.write(".archsig/plans/split-order/plan.jsonl", SPLIT);
    let s = repo.run(&["plan", "check", "split-order"]);
    let r = result(&s, "payment-info");
    assert_eq!(r["outcome"], "holds", "{s}");
    let d = repo.run(&["show", r["id"].as_str().unwrap()]);
    assert_eq!(d["check"]["kept"][0]["targets"], serde_json::json!(["shop.payment.model.OrderPayment.ref"]));
}

#[test]
fn changes_keep_reports_an_element_without_a_correspondence_as_missing() {
    let repo = keep_repo("keep-missing");
    repo.write(".archsig/plans/split-order/plan.jsonl", &SPLIT.replace(
        r#"{"kind": "corresponds", "subject": "shop.order.model.Order.payment_ref", "object": "shop.payment.model.OrderPayment.ref", "at": "plan:split-order"}
"#,
        "",
    ));
    let s = repo.run(&["plan", "check", "split-order"]);
    let r = result(&s, "shop.order.model.Order.payment_ref");
    assert_eq!((r["outcome"].as_str(), r["kind"].as_str()), (Some("fails"), Some("missing")), "{s}");
}

#[test]
fn changes_keep_is_silent_where_the_meaning_or_the_definition_was_not_read() {
    let repo = keep_repo("keep-unread");
    // 意味を読んでいないソースがある。
    repo.write("shop/payment/charge.py", "def charge(): ...\n");
    repo.write(".archsig/plans/split-order/plan.jsonl", SPLIT);
    let s = repo.run(&["plan", "check", "split-order"]);
    let r = result(&s, "payment-info");
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unread")), "{s}");
    assert!(s["next"].as_array().unwrap().iter().any(|n| n["read"] == "shop/payment/charge.py" && n["scope"] == "meaning:payment-info"), "{s}");

    // 意味 Atom はあるが、その要素の定義を読んでいない。何も変えない候補でも missing とは言えない。
    let repo = keep_repo("keep-undefined");
    repo.map("shop/order/model.py", r#"{"kind": "observed", "subject": "shop/order/model.py", "scope": "meaning:payment-info", "at": "shop/order/model.py@blob:1d9e3b4"}
{"kind": "meaning", "subject": "shop.order.model.Order.payment_ref", "meaning": "payment-info", "uses": ["shop/payment/charge.py:22@blob:8b41d07"], "at": "shop/order/model.py:10@blob:1d9e3b4"}
"#);
    repo.write(".archsig/plans/nothing/plan.jsonl", r#"{"kind": "plan", "subject": "nothing", "base": "a1b2c3d"}
"#);
    let s = repo.run(&["plan", "check", "nothing"]);
    let r = result(&s, "shop.order.model.Order.payment_ref");
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unread")), "{s}");
    assert!(repo.run(&["show", r["id"].as_str().unwrap()])["theory"].is_string(), "詳細は Rising Sea の節を持つ");
}

#[test]
fn a_law_without_pairs_is_silent_where_the_structure_was_not_read() {
    let repo = Repo::new("nopairs-unread");
    repo.write(".archsig/law/shop.law", LAW);
    repo.map("shop/order/model.py", ORDER);
    repo.write("shop/order/model.py", "class Order: ...\n");
    repo.write("shop/order/confirm.py", "def confirm(): ...\n");
    repo.write(".archsig/plans/add-type/plan.jsonl", r#"{"kind": "defines", "subject": "shop.gift.model.Gift", "value": "type", "file": "shop/gift/model.py", "at": "plan:add-type"}
"#);
    let s = repo.run(&["plan", "check", "add-type"]);
    let r = result(&s, "payment-info");
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unread")), "操作がないとは言えない: {s}");
    assert!(s["next"].as_array().unwrap().iter().any(|n| n["read"] == "shop/order/confirm.py" && n["scope"] == "structure"), "{s}");
}

/// 変更前: f(o) は g(x=$o.a) を呼び、g は T.a = 1 のあとで T.p = $x を書く。p は呼び出しの時点の a。
const CALL_TIME: &str = r#"{"kind": "observed", "subject": "m.py", "scope": "structure", "at": "m.py@blob:aaaaaaa"}
{"kind": "resolves", "subject": "int", "object": "external:builtins", "at": "m.py:1@blob:aaaaaaa"}
{"kind": "observed", "subject": "m.py", "scope": "meaning:payment-info", "at": "m.py@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.T", "value": "type", "at": "m.py:1@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.T.a", "value": "field", "type": "int", "at": "m.py:2@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.T.p", "value": "field", "type": "int", "at": "m.py:3@blob:aaaaaaa"}
{"kind": "meaning", "subject": "m.T.p", "meaning": "payment-info", "uses": ["m.py:9@blob:aaaaaaa"], "at": "m.py:3@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.f", "value": "operation", "params": {"o": "m.T"}, "at": "m.py:5@blob:aaaaaaa"}
{"kind": "calls", "subject": "m.f", "object": "m.g", "at": "m.py:6@blob:aaaaaaa"}
{"kind": "passes", "subject": "m.f->m.g", "object": "m.g.$x", "value": "$o.a", "at": "m.py:6@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.g", "value": "operation", "params": {"x": "int"}, "at": "m.py:8@blob:aaaaaaa"}
{"kind": "writes", "subject": "m.g", "object": "m.T.a", "value": "1", "at": "m.py:9@blob:aaaaaaa"}
{"kind": "writes", "subject": "m.g", "object": "m.T.p", "value": "$x", "at": "m.py:10@blob:aaaaaaa"}
"#;

fn call_time(name: &str, plan: &str) -> Value {
    let repo = Repo::new(name);
    repo.write(".archsig/law/m.law", &LAW.replace("\"shop/**\"", "\"m.py\""));
    repo.map("m.py", CALL_TIME);
    repo.write(".archsig/plans/p/plan.jsonl", plan);
    let s = repo.run(&["plan", "check", "p"]);
    result(&s, "m.f").clone()
}

#[test]
fn a_passed_value_is_read_when_the_call_is_made() {
    // 候補は、同じ振る舞いを展開して書く(p = a を先に、a = 1 を後に)。
    let same = r#"{"kind": "defines", "subject": "m.f", "value": "operation", "params": {"o": "m.T"}, "file": "m.py", "at": "plan:p"}
{"kind": "writes", "subject": "m.f", "object": "m.T.p", "value": "$o.a", "at": "plan:p"}
{"kind": "writes", "subject": "m.f", "object": "m.T.a", "value": "1", "at": "plan:p"}
"#;
    assert_eq!(call_time("call-same", same)["outcome"], "holds");
    // a = 1 を先に書いてから p = a とすると、p は 1 になり、振る舞いが変わる。
    let changed = r#"{"kind": "defines", "subject": "m.f", "value": "operation", "params": {"o": "m.T"}, "file": "m.py", "at": "plan:p"}
{"kind": "writes", "subject": "m.f", "object": "m.T.a", "value": "1", "at": "plan:p"}
{"kind": "writes", "subject": "m.f", "object": "m.T.p", "value": "$o.a", "at": "plan:p"}
"#;
    assert_eq!(call_time("call-changed", changed)["kind"], "counterexample");
}

#[test]
fn a_call_condition_is_read_when_the_call_is_made() {
    // 変更前: f は a == 0 のときだけ g を呼ぶ。g は a = 5 のあとで p = None を書く。
    let before = CALL_TIME
        .replace(r#""object": "m.g", "at": "m.py:6@blob:aaaaaaa"}"#, r#""object": "m.g", "when": "$o.a == 0", "at": "m.py:6@blob:aaaaaaa"}"#)
        .replace(r#""object": "m.T.a", "value": "1""#, r#""object": "m.T.a", "value": "5""#)
        .replace(r#""object": "m.T.p", "value": "$x""#, r#""object": "m.T.p", "value": "None""#);
    let repo = Repo::new("call-when");
    repo.write(".archsig/law/m.law", &LAW.replace("\"shop/**\"", "\"m.py\""));
    repo.map("m.py", &before);
    repo.write(
        ".archsig/plans/p/plan.jsonl",
        r#"{"kind": "defines", "subject": "m.f", "value": "operation", "params": {"o": "m.T"}, "file": "m.py", "at": "plan:p"}
{"kind": "writes", "subject": "m.f", "object": "m.T.p", "value": "None", "when": "$o.a == 0", "at": "plan:p"}
{"kind": "writes", "subject": "m.f", "object": "m.T.a", "value": "5", "when": "$o.a == 0", "at": "plan:p"}
"#,
    );
    let s = repo.run(&["plan", "check", "p"]);
    assert_eq!(result(&s, "m.f")["outcome"], "holds", "{s}");
}

#[test]
fn a_fresh_value_in_an_untouched_operation_is_the_same_before_and_after() {
    let repo = Repo::new("fresh");
    repo.write(".archsig/law/m.law", &format!("{}\nfresh \"ids.new*\"\n", LAW.replace("\"shop/**\"", "\"m.py\"")));
    // 候補が消す要素の Atom が先に読まれ、Atom の並びがずれる形にする。
    repo.map("a.py", r#"{"kind": "observed", "subject": "a.py", "scope": "structure", "at": "a.py@blob:bbbbbbb"}
{"kind": "defines", "subject": "a.Old", "value": "type", "at": "a.py:1@blob:bbbbbbb"}
{"kind": "defines", "subject": "a.Old.x", "value": "field", "type": "int", "at": "a.py:2@blob:bbbbbbb"}
"#);
    repo.map("m.py", &format!("{CALL_TIME}{}", r#"{"kind": "writes", "subject": "m.f", "object": "m.T.p", "value": "ids.new_token()", "at": "m.py:7@blob:aaaaaaa"}
"#));
    repo.write(".archsig/plans/p/plan.jsonl", r#"{"kind": "removes", "subject": "a.Old", "at": "plan:p"}
"#);
    let s = repo.run(&["plan", "check", "p"]);
    assert_eq!(result(&s, "m.f")["outcome"], "holds", "{s}");
}

#[test]
fn recursion_is_silent_with_limit() {
    let repo = Repo::new("recursion");
    repo.write(".archsig/law/m.law", &LAW.replace("\"shop/**\"", "\"m.py\""));
    repo.map("m.py", &format!("{CALL_TIME}{}", r#"{"kind": "calls", "subject": "m.g", "object": "m.g", "at": "m.py:11@blob:aaaaaaa"}
"#));
    repo.write(".archsig/plans/p/plan.jsonl", r#"{"kind": "plan", "subject": "p", "base": "a1b2c3d"}
"#);
    let s = repo.run(&["plan", "check", "p"]);
    assert_eq!(result(&s, "m.f")["reason"], "limit", "{s}");
}

#[test]
fn a_plan_on_a_plan_is_checked_against_the_base_plan() {
    let repo = shop("base");
    repo.map("shop/shipping/address.py", ADDRESS);
    repo.write(".archsig/plans/split-order/plan.jsonl", SPLIT);
    // 元の候補の上で、国が変わるとき決済情報を消す。元の候補の update_shipping は消さないので、振る舞いが変わる。
    repo.write(
        ".archsig/plans/fix/plan.jsonl",
        &format!(
            "{}\n{}{}",
            r#"{"kind": "plan", "subject": "fix", "base": "plan:split-order"}"#,
            RESET.replace("plan:split-order", "plan:fix"),
            SPLIT.lines().filter(|l| l.contains(r#""subject": "shop.shipping.service.update_shipping""#) || l.contains("update_shipping->")).map(|l| format!("{}\n", l.replace("plan:split-order", "plan:fix"))).collect::<String>()
        ),
    );
    let s = repo.run(&["plan", "check", "fix"]);
    assert_eq!(result(&s, UPDATE)["kind"], "counterexample", "元の候補を先に重ねて比べる: {s}");

    repo.write(".archsig/plans/a/plan.jsonl", r#"{"kind": "plan", "subject": "a", "base": "plan:b"}
"#);
    repo.write(".archsig/plans/b/plan.jsonl", r#"{"kind": "plan", "subject": "b", "base": "plan:a"}
"#);
    assert!(repo.fail(&["plan", "check", "a"]).contains("めぐっている"));
}

#[test]
fn each_result_is_listed_once_for_a_place_to_read() {
    let repo = shop("dedupe");
    // 同じソースの、読んでいない呼び出し先が二つある。
    repo.map("shop/shipping/service.py", &format!("{SERVICE}{}", r#"{"kind": "calls", "subject": "shop.shipping.service.fix_address", "object": "shop.shipping.address.validate", "at": "shop/shipping/service.py:10@blob:3f2a9c1"}
{"kind": "resolves", "subject": "shop.shipping.address.validate", "object": "shop/shipping/address.py", "at": "shop/shipping/service.py:1@blob:3f2a9c1"}
"#));
    repo.write(".archsig/plans/split-order/plan.jsonl", SPLIT);
    let s = repo.run(&["plan", "check", "split-order"]);
    for n in s["next"].as_array().unwrap() {
        let ids: Vec<&str> = n["decides"].as_array().unwrap().iter().map(|d| d.as_str().unwrap()).collect();
        let mut unique = ids.clone();
        unique.dedup();
        assert_eq!(ids, unique, "{s}");
    }
    let removes = result(&s, "removes");
    let d = repo.run(&["show", removes["id"].as_str().unwrap()]);
    assert_eq!(d["next"].as_array().unwrap().len(), 1, "同じ読む所は一度だけ: {d}");
}

#[test]
fn changes_keep_is_silent_when_the_target_was_not_read() {
    let repo = keep_repo("keep-target");
    // 行き先 shop.billing.model.Bill.ref は、候補にも ArchMap にも定義がない。
    repo.write(".archsig/plans/split-order/plan.jsonl", &SPLIT.replace(
        r#""object": "shop.payment.model.OrderPayment.ref""#,
        r#""object": "shop.billing.model.Bill.ref""#,
    ));
    let s = repo.run(&["plan", "check", "split-order"]);
    let r = result(&s, "shop.order.model.Order.payment_ref");
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unread")), "{s}");
    assert!(s["next"].as_array().unwrap().iter().any(|n| n["element"] == "shop.billing.model.Bill.ref"), "{s}");
}

/// 変更前: f(o: T) が T.p = $o.a を書く。T.p が payment-info。
const SPLITTING: &str = r#"{"kind": "observed", "subject": "m.py", "scope": "structure", "at": "m.py@blob:ccccccc"}
{"kind": "resolves", "subject": "int", "object": "external:builtins", "at": "m.py:1@blob:ccccccc"}
{"kind": "observed", "subject": "m.py", "scope": "meaning:payment-info", "at": "m.py@blob:ccccccc"}
{"kind": "defines", "subject": "m.T", "value": "type", "at": "m.py:1@blob:ccccccc"}
{"kind": "defines", "subject": "m.T.a", "value": "field", "type": "int", "at": "m.py:2@blob:ccccccc"}
{"kind": "defines", "subject": "m.T.b", "value": "field", "type": "int", "at": "m.py:3@blob:ccccccc"}
{"kind": "defines", "subject": "m.T.p", "value": "field", "type": "int", "at": "m.py:4@blob:ccccccc"}
{"kind": "meaning", "subject": "m.T.p", "meaning": "payment-info", "uses": ["m.py:7@blob:ccccccc"], "at": "m.py:4@blob:ccccccc"}
{"kind": "defines", "subject": "m.f", "value": "operation", "params": {"o": "m.T"}, "at": "m.py:6@blob:ccccccc"}
{"kind": "writes", "subject": "m.f", "object": "m.T.p", "value": "$o.a", "at": "m.py:7@blob:ccccccc"}
"#;

fn splitting(name: &str, plan: &str) -> Value {
    let repo = Repo::new(name);
    repo.write(".archsig/law/m.law", &LAW.replace("\"shop/**\"", "\"m.py\""));
    repo.map("m.py", SPLITTING);
    repo.write(".archsig/plans/p/plan.jsonl", plan);
    let s = repo.run(&["plan", "check", "p"]);
    result(&s, "m.f").clone()
}

const NEW_TYPES: &str = r#"{"kind": "defines", "subject": "m.S", "value": "type", "file": "m.py", "at": "plan:p"}
{"kind": "defines", "subject": "m.S.a", "value": "field", "type": "int", "file": "m.py", "at": "plan:p"}
{"kind": "defines", "subject": "m.P", "value": "type", "file": "m.py", "at": "plan:p"}
{"kind": "defines", "subject": "m.P.a", "value": "field", "type": "int", "file": "m.py", "at": "plan:p"}
{"kind": "defines", "subject": "m.P.p", "value": "field", "type": "int", "file": "m.py", "at": "plan:p"}
{"kind": "corresponds", "subject": "m.T.p", "object": "m.P.p", "at": "plan:p"}
{"kind": "corresponds", "subject": "m.f.$o", "object": "m.f.$q", "at": "plan:p"}
{"kind": "removes", "subject": "m.T", "at": "plan:p"}
{"kind": "defines", "subject": "m.f", "value": "operation", "params": {"q": "m.P"}, "file": "m.py", "at": "plan:p"}
{"kind": "writes", "subject": "m.f", "object": "m.P.p", "value": "$q.a", "at": "plan:p"}
"#;

#[test]
fn a_field_split_into_two_is_compared_under_the_before_name() {
    // T.a を S.a と P.a の二つへ分ける(一対多)。P.a の値は T.a の値なので、成り立つ。
    let plan = format!(
        "{NEW_TYPES}{}",
        r#"{"kind": "corresponds", "subject": "m.T.a", "object": "m.S.a", "at": "plan:p"}
{"kind": "corresponds", "subject": "m.T.a", "object": "m.P.a", "at": "plan:p"}
"#
    );
    assert_eq!(splitting("split", &plan)["outcome"], "holds");
}

#[test]
fn two_fields_merged_into_one_are_silent() {
    // T.a と T.b を P.a へ(多対一)。変更前の名前で置けないので、決まらない。
    let plan = format!(
        "{NEW_TYPES}{}",
        r#"{"kind": "corresponds", "subject": "m.T.a", "object": "m.P.a", "at": "plan:p"}
{"kind": "corresponds", "subject": "m.T.b", "object": "m.P.a", "at": "plan:p"}
"#
    );
    let r = splitting("merge", &plan);
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unresolved")), "{r}");
}

#[test]
fn a_target_field_whose_meaning_was_not_read_is_silent() {
    let repo = Repo::new("target-meaning");
    repo.write(".archsig/law/m.law", &LAW.replace("\"shop/**\"", "\"*.py\""));
    repo.map("m.py", &SPLITTING.replace(r#"{"kind": "meaning", "subject": "m.T.p""#, r#"{"kind": "meaning", "subject": "m.T.zz""#));
    // 行き先 u.U.b は既存のフィールドで、u.py の意味の範囲を読んでいない。
    repo.map("u.py", r#"{"kind": "observed", "subject": "u.py", "scope": "structure", "at": "u.py@blob:ddddddd"}
{"kind": "defines", "subject": "u.U.b", "value": "field", "type": "int", "at": "u.py:2@blob:ddddddd"}
"#);
    repo.write(
        ".archsig/plans/p/plan.jsonl",
        r#"{"kind": "corresponds", "subject": "m.T.p", "object": "u.U.b", "at": "plan:p"}
{"kind": "defines", "subject": "m.f", "value": "operation", "params": {"o": "m.T"}, "file": "m.py", "at": "plan:p"}
"#,
    );
    let s = repo.run(&["plan", "check", "p"]);
    let r = result(&s, "m.f");
    assert_eq!(r["reason"], "unread", "{s}");
    assert!(s["next"].as_array().unwrap().iter().any(|n| n["read"] == "u.py" && n["scope"] == "meaning:payment-info"), "{s}");
}

#[test]
fn a_pair_whose_operation_uses_a_removed_element_is_missing_under_the_law() {
    let repo = shop("pair-missing");
    repo.map("shop/shipping/address.py", ADDRESS);
    // 書き直していない clear は、消える Order.payment_ref を書く。
    repo.map("shop/order/model.py", &format!("{ORDER}{}", r#"{"kind": "defines", "subject": "shop.order.model.clear", "value": "operation", "params": {}, "at": "shop/order/model.py:12@blob:1d9e3b4"}
{"kind": "writes", "subject": "shop.order.model.clear", "object": "shop.order.model.Order.payment_ref", "value": "None", "at": "shop/order/model.py:13@blob:1d9e3b4"}
"#));
    repo.write(".archsig/plans/split-order/plan.jsonl", SPLIT);
    let s = repo.run(&["plan", "check", "split-order"]);
    let under_law = s["results"].as_array().unwrap().iter().any(|r| {
        r["subject"] == "shop.order.model.clear" && r["law"] == "payment-follows-order" && r["kind"] == "missing"
    });
    assert!(under_law, "比べられない組は、その Law の missing として挙げる: {s}");
    assert!(!s["results"].as_array().unwrap().iter().any(|r| r["subject"] == "payment-info" && r["outcome"] == "holds"), "{s}");
}

#[test]
fn an_unread_source_is_listed_even_when_pairs_exist() {
    let repo = shop("unread-with-pairs");
    repo.map("shop/shipping/address.py", ADDRESS);
    repo.write("shop/order/confirm.py", "def confirm(order): order.payment_ref = None\n");
    repo.write(".archsig/plans/split-order/plan.jsonl", SPLIT);
    let s = repo.run(&["plan", "check", "split-order"]);
    let r = result(&s, "payment-info");
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unread")), "{s}");
    let confirm = s["next"].as_array().unwrap().iter().find(|n| n["read"] == "shop/order/confirm.py").unwrap_or_else(|| panic!("{s}"));
    // 消える要素を使うかも、同じソースで決まる。
    let removes = result(&s, "removes")["id"].clone();
    assert!(confirm["decides"].as_array().unwrap().contains(&removes), "{s}");
}

#[test]
fn a_condition_between_constants_branches() {
    // 変更前の f は a = 1 を書いた後、a == 0 のときだけ p = None を書く。書いた後の条件 1 == 0 も、
    // 未割り当ての原子として二つに分ける(設計 §5.4)。定数の字句から真偽を決めない。
    let before = SPLITTING
        .replace(r#""object": "m.T.p", "value": "$o.a", "at": "m.py:7@blob:ccccccc"}"#, r#""object": "m.T.a", "value": "1", "at": "m.py:7@blob:ccccccc"}
{"kind": "writes", "subject": "m.f", "object": "m.T.p", "value": "None", "when": "$o.a == 0", "at": "m.py:8@blob:ccccccc"}"#);
    let repo = Repo::new("const");
    repo.write(".archsig/law/m.law", &LAW.replace("\"shop/**\"", "\"m.py\""));
    repo.map("m.py", &before);
    repo.write(
        ".archsig/plans/p/plan.jsonl",
        r#"{"kind": "defines", "subject": "m.f", "value": "operation", "params": {"o": "m.T"}, "file": "m.py", "at": "plan:p"}
{"kind": "writes", "subject": "m.f", "object": "m.T.a", "value": "1", "at": "plan:p"}
"#,
    );
    let s = repo.run(&["plan", "check", "p"]);
    assert_eq!(result(&s, "m.f")["kind"], "counterexample", "{s}");
}

#[test]
fn an_ambiguous_operation_that_uses_a_removed_element_is_silent_under_the_law() {
    // m.f は操作とフィールドの二つに定義され、曖昧である。候補は m.f が書く m.T.p を消す。
    let before = format!("{SPLITTING}{}", r#"{"kind": "defines", "subject": "m.f", "value": "field", "type": "int", "at": "m.py:9@blob:ccccccc"}
"#);
    let repo = Repo::new("ambiguous-missing");
    repo.write(".archsig/law/m.law", &LAW.replace("\"shop/**\"", "\"m.py\""));
    repo.map("m.py", &before);
    repo.write(".archsig/plans/p/plan.jsonl", r#"{"kind": "removes", "subject": "m.T.p", "at": "plan:p"}
"#);
    let s = repo.run(&["plan", "check", "p"]);
    let rows: Vec<&Value> = s["results"].as_array().unwrap().iter().filter(|r| r["subject"] == "m.f").collect();
    assert!(!rows.is_empty(), "{s}");
    for r in rows {
        assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unresolved")), "{s}");
    }
}

#[test]
fn a_call_in_a_condition_puts_the_same_call_condition() {
    let when = r#""object": "m.T.p", "value": "None", "when": "m.check($o.a) == 1""#;
    let before = SPLITTING.replace(r#""object": "m.T.p", "value": "$o.a""#, when);
    let repo = Repo::new("call-in-condition");
    repo.write(".archsig/law/m.law", &LAW.replace("\"shop/**\"", "\"m.py\""));
    repo.map("m.py", &before);
    repo.write(
        ".archsig/plans/p/plan.jsonl",
        &format!(
            "{}\n{{\"kind\": \"writes\", \"subject\": \"m.f\", {when}, \"at\": \"plan:p\"}}\n",
            r#"{"kind": "defines", "subject": "m.f", "value": "operation", "params": {"o": "m.T"}, "file": "m.py", "at": "plan:p"}"#,
        ),
    );
    let s = repo.run(&["plan", "check", "p"]);
    let r = result(&s, "m.f");
    assert_eq!(r["outcome"], "holds", "{s}");
    let detail = repo.run(&["show", r["id"].as_str().unwrap()]);
    let same_call = detail["conditions"].as_array().unwrap().iter().any(|c| c.as_str().unwrap().starts_with("操作の呼び出しの結果は"));
    assert!(same_call, "分岐の組は条件の中の呼び出しを同じ項とみなして作る: {detail}");
}

#[test]
fn an_operation_rewritten_without_its_definition_is_not_passed_over() {
    // 候補は m.f の本体だけを書き直し、定義を書かない。m.f は変更前にも変更後にもある名前なので、自分自身に対応する。
    let s = splitting_summary(
        "rewritten-without-defines",
        r#"{"kind": "writes", "subject": "m.f", "object": "m.T.p", "value": "2", "at": "plan:p"}
"#,
    );
    let r = result(&s, "m.f");
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unread")), "{s}");
    assert!(s["next"].as_array().unwrap().iter().any(|n| n["element"] == "m.f"), "{s}");
}

fn splitting_summary(name: &str, plan: &str) -> Value {
    let repo = Repo::new(name);
    repo.write(".archsig/law/m.law", &LAW.replace("\"shop/**\"", "\"m.py\""));
    repo.map("m.py", SPLITTING);
    repo.write(".archsig/plans/p/plan.jsonl", plan);
    repo.run(&["plan", "check", "p"])
}

/// 変更前: m.h は読んでいない型 lib.O の引数からたどる。m.k は `?` の呼び出しを、m.j は読めない式を書く。
const UNTRACED: &str = r#"{"kind": "defines", "subject": "m.U", "value": "type", "at": "m.py:10@blob:ccccccc"}
{"kind": "defines", "subject": "m.U.a", "value": "field", "type": "int", "at": "m.py:11@blob:ccccccc"}
{"kind": "resolves", "subject": "lib.O", "object": "lib.py", "at": "m.py:12@blob:ccccccc"}
{"kind": "defines", "subject": "m.h", "value": "operation", "params": {"o": "lib.O"}, "at": "m.py:13@blob:ccccccc"}
{"kind": "writes", "subject": "m.h", "object": "m.T.b", "value": "$o.q.a", "at": "m.py:14@blob:ccccccc"}
{"kind": "defines", "subject": "m.k", "value": "operation", "params": {"o": "m.T"}, "at": "m.py:15@blob:ccccccc"}
{"kind": "writes", "subject": "m.k", "object": "m.T.b", "value": "?u($o)", "at": "m.py:16@blob:ccccccc"}
{"kind": "defines", "subject": "m.j", "value": "operation", "params": {"o": "m.T"}, "at": "m.py:17@blob:ccccccc"}
{"kind": "writes", "subject": "m.j", "object": "m.T.b", "value": "m.u($o", "at": "m.py:18@blob:ccccccc"}
"#;

#[test]
fn an_operation_whose_names_cannot_be_traced_is_silent_on_removes() {
    let repo = Repo::new("untraced");
    repo.write(".archsig/law/m.law", &LAW.replace("\"shop/**\"", "\"m.py\""));
    repo.map("m.py", &format!("{SPLITTING}{UNTRACED}"));
    repo.write(".archsig/plans/p/plan.jsonl", r#"{"kind": "removes", "subject": "m.U.a", "at": "plan:p"}
"#);
    let s = repo.run(&["plan", "check", "p"]);
    let unlawed = |subject: &str| -> &Value {
        s["results"].as_array().unwrap().iter().find(|r| r["subject"] == subject && r["law"].is_null()).unwrap_or_else(|| panic!("{subject}: {s}"))
    };
    // 読んでいない型を通る道は、その型を定義するソースを返す。
    let h = unlawed("m.h");
    assert_eq!((h["outcome"].as_str(), h["reason"].as_str()), (Some("silent"), Some("unread")), "{s}");
    let detail = repo.run(&["show", h["id"].as_str().unwrap()]);
    assert!(detail["next"].as_array().unwrap().iter().any(|n| n["read"] == "lib.py"), "{detail}");
    // `?` の呼び出しと読めない式は、その Atom の場所を返す(マニュアル第5章 問い8)。
    for op in ["m.k", "m.j"] {
        let r = unlawed(op);
        assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unresolved")), "{s}");
        let detail = repo.run(&["show", r["id"].as_str().unwrap()]);
        assert!(detail["next"].as_array().unwrap().iter().any(|n| n["read"] == "m.py"), "{detail}");
    }
}

#[test]
fn a_question_mark_in_a_correspondence_returns_the_element() {
    let s = splitting_summary(
        "question-correspondence",
        r#"{"kind": "corresponds", "subject": "m.f", "object": "?m.g", "at": "plan:p"}
"#,
    );
    let r = result(&s, "?m.g");
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unresolved")), "{s}");
    assert!(s["next"].as_array().unwrap().iter().any(|n| n["element"] == "m.f" && n["decides"].as_array().unwrap().contains(&r["id"])), "{s}");
}

#[test]
fn a_question_mark_on_the_source_side_of_a_correspondence_returns_the_element() {
    let s = splitting_summary(
        "question-source",
        r#"{"kind": "corresponds", "subject": "?m.old", "object": "m.f", "at": "plan:p"}
"#,
    );
    let silent = s["results"].as_array().unwrap().iter().find(|r| r["subject"] == "m.f" && r["outcome"] == "silent").unwrap_or_else(|| panic!("{s}"));
    assert_eq!(silent["reason"], "unresolved", "{s}");
    assert!(s["next"].as_array().unwrap().iter().any(|n| n["element"] == "?m.old" && n["decides"].as_array().unwrap().contains(&silent["id"])), "{s}");
}

#[test]
fn too_many_pairs_of_branches_are_silent_with_limit() {
    // 変更前と変更後が、互いに関係のない条件で 2^8 通りずつに分かれる。矛盾しない組は 2^16 通りある。
    // 書くのは意味のない m.T.b なので、どの組でも食い違わない。
    let writes = |field: &str, at: &str| -> String {
        (0..8)
            .map(|i| format!(r#"{{"kind": "writes", "subject": "m.f", "object": "m.T.b", "value": "{i}", "when": "$o.{field} == {i}", "at": "{at}"}}"#) + "\n")
            .collect()
    };
    let repo = Repo::new("pair-limit");
    repo.write(".archsig/law/m.law", &LAW.replace("\"shop/**\"", "\"m.py\""));
    repo.map("m.py", &format!("{SPLITTING}{}", writes("a", "m.py:8@blob:ccccccc")));
    repo.write(
        ".archsig/plans/p/plan.jsonl",
        &format!(
            "{}\n{}\n{}",
            r#"{"kind": "defines", "subject": "m.f", "value": "operation", "params": {"o": "m.T"}, "file": "m.py", "at": "plan:p"}"#,
            r#"{"kind": "writes", "subject": "m.f", "object": "m.T.p", "value": "$o.a", "at": "plan:p"}"#,
            writes("b", "plan:p")
        ),
    );
    let s = repo.run(&["plan", "check", "p"]);
    assert_eq!(result(&s, "m.f")["reason"], "limit", "{s}");
}

/// 変更前: f(o) は、o.s.p(注文の中の S の p)に 1 を書く。p は payment-info を持つ。
const NESTED: &str = r#"{"kind": "observed", "subject": "m.py", "scope": "structure", "at": "m.py@blob:aaaaaaa"}
{"kind": "resolves", "subject": "int", "object": "external:builtins", "at": "m.py:1@blob:aaaaaaa"}
{"kind": "observed", "subject": "m.py", "scope": "meaning:payment-info", "at": "m.py@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.O", "value": "type", "at": "m.py:1@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.O.s", "value": "field", "type": "m.S", "at": "m.py:2@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.S", "value": "type", "at": "m.py:3@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.S.p", "value": "field", "type": "int", "at": "m.py:4@blob:aaaaaaa"}
{"kind": "meaning", "subject": "m.S.p", "meaning": "payment-info", "uses": ["m.py:7@blob:aaaaaaa"], "at": "m.py:4@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.f", "value": "operation", "params": {"o": "m.O", "t": "m.S"}, "at": "m.py:6@blob:aaaaaaa"}
{"kind": "writes", "subject": "m.f", "via": ["m.O.s"], "object": "m.S.p", "value": "1", "at": "m.py:7@blob:aaaaaaa"}
"#;

fn nested(name: &str, write: &str) -> Value {
    let repo = Repo::new(name);
    repo.write(".archsig/law/m.law", &LAW.replace("\"shop/**\"", "\"m.py\""));
    repo.map("m.py", NESTED);
    repo.write(
        ".archsig/plans/p/plan.jsonl",
        &format!(
            "{}\n{write}\n",
            r#"{"kind": "defines", "subject": "m.f", "value": "operation", "params": {"o": "m.O", "t": "m.S"}, "file": "m.py", "at": "plan:p"}"#
        ),
    );
    let s = repo.run(&["plan", "check", "p"]);
    result(&s, "m.f").clone()
}

#[test]
fn a_nested_write_is_compared_at_the_place_of_the_field_chain() {
    let same = nested("nested-same", r#"{"kind": "writes", "subject": "m.f", "via": ["m.O.s"], "object": "m.S.p", "value": "1", "at": "plan:p"}"#);
    assert_eq!(same["outcome"], "holds", "{same}");
    // 候補は、注文の中の S ではなく、引数 t の S に書く。注文の中の p は 1 にならない。
    let moved = nested("nested-moved", r#"{"kind": "writes", "subject": "m.f", "object": "m.S.p", "value": "1", "at": "plan:p"}"#);
    assert_eq!(moved["kind"], "counterexample", "{moved}");
}

#[test]
fn a_write_through_a_removed_field_is_missing() {
    let repo = Repo::new("nested-removes");
    repo.write(".archsig/law/m.law", &LAW.replace("\"shop/**\"", "\"m.py\""));
    repo.map("m.py", NESTED);
    repo.write(".archsig/plans/p/plan.jsonl", "{\"kind\": \"removes\", \"subject\": \"m.O.s\", \"at\": \"plan:p\"}\n");
    let s = repo.run(&["plan", "check", "p"]);
    let missing: Vec<&Value> = s["results"].as_array().unwrap().iter().filter(|r| r["subject"] == "m.f" && r["kind"] == "missing").collect();
    assert!(!missing.is_empty(), "via に消えるフィールドを持つ書き込みは、その操作を missing に挙げる: {s}");
}

#[test]
fn a_via_field_whose_meaning_was_not_read_is_silent() {
    // 書き込みは via のフィールドの場所 [m.O.s] の値も変える。m.O.s を定義した a.py の payment-info を読んでいなければ、決まらない。
    let run = |name: &str, value: &str| {
        let repo = Repo::new(name);
        repo.write(".archsig/law/m.law", &LAW.replace("\"shop/**\"", "\"*.py\""));
        repo.map("a.py", r#"{"kind": "observed", "subject": "a.py", "scope": "structure", "at": "a.py@blob:bbbbbbb"}
{"kind": "defines", "subject": "m.O", "value": "type", "at": "a.py:1@blob:bbbbbbb"}
{"kind": "defines", "subject": "m.O.s", "value": "field", "type": "m.S", "at": "a.py:2@blob:bbbbbbb"}
"#);
        repo.map("m.py", &NESTED.lines().filter(|l| !l.contains("\"subject\": \"m.O")).map(|l| format!("{l}\n")).collect::<String>());
        repo.write(
            ".archsig/plans/p/plan.jsonl",
            &format!(
                "{}\n{{\"kind\": \"writes\", \"subject\": \"m.f\", \"via\": [\"m.O.s\"], \"object\": \"m.S.p\", \"value\": \"{value}\", \"at\": \"plan:p\"}}\n",
                r#"{"kind": "defines", "subject": "m.f", "value": "operation", "params": {"o": "m.O", "t": "m.S"}, "file": "m.py", "at": "plan:p"}"#
            ),
        );
        repo.run(&["plan", "check", "p"])
    };
    // 書き込む値が同じなら、ほかの場所で食い違わないので、[m.O.s] の沈黙が結論に関わる。
    let s = run("nested-via-meaning", "1");
    let r = result(&s, "m.f");
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unread")), "{s}");
    assert!(s["next"].as_array().unwrap().iter().any(|n| n["read"] == "a.py" && n["scope"] == "meaning:payment-info"), "{s}");
    // 値が違えば、意味を持つ場所 [m.O.s, m.S.p] で食い違うので、頭の部分の場所の沈黙は結論に関わらず、反例を返す(設計 §5.4)。
    let s = run("nested-via-meaning-diverging", "2");
    assert_eq!(result(&s, "m.f")["kind"], "counterexample", "{s}");
}

#[test]
fn a_question_mark_in_via_returns_the_atom() {
    let repo = Repo::new("nested-via-question");
    repo.write(".archsig/law/m.law", &LAW.replace("\"shop/**\"", "\"m.py\""));
    repo.map("m.py", &NESTED.replace(r#""via": ["m.O.s"]"#, r#""via": ["?o.s"]"#));
    // 候補は m.f を書き直す。変更前の m.f を実行する所で、via の ? の名前に出会う。
    repo.write(
        ".archsig/plans/p/plan.jsonl",
        r#"{"kind": "defines", "subject": "m.f", "value": "operation", "params": {"o": "m.O", "t": "m.S"}, "file": "m.py", "at": "plan:p"}
{"kind": "writes", "subject": "m.f", "object": "m.S.p", "value": "1", "at": "plan:p"}
"#,
    );
    let s = repo.run(&["plan", "check", "p"]);
    let r = result(&s, "m.f");
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unresolved")), "{s}");
    assert!(s["next"].as_array().unwrap().iter().any(|n| n["read"] == "m.py"), "via の ? の名前の沈黙は、その Atom の場所を返す: {s}");
}

#[test]
fn a_nested_write_under_a_field_with_the_meaning_is_unchecked() {
    // 意味は via のフィールド m.O.s(S の値)にある。その中の p に書くと、[m.O.s] の値が変わる。
    // 先に書き込みのある場所の値は決めていないので、unchecked で沈黙する(設計 §3.5)。
    let with_meaning = |name: &str, write: &str| {
        let repo = Repo::new(name);
        repo.write(".archsig/law/m.law", &LAW.replace("\"shop/**\"", "\"m.py\""));
        repo.map("m.py", &NESTED.replace(r#""subject": "m.S.p", "meaning""#, r#""subject": "m.O.s", "meaning""#));
        repo.write(
            ".archsig/plans/p/plan.jsonl",
            &format!("{}\n{write}\n", r#"{"kind": "defines", "subject": "m.f", "value": "operation", "params": {"o": "m.O", "t": "m.S"}, "file": "m.py", "at": "plan:p"}"#),
        );
        let s = repo.run(&["plan", "check", "p"]);
        result(&s, "m.f").clone()
    };
    let same = with_meaning("nested-head-same", r#"{"kind": "writes", "subject": "m.f", "via": ["m.O.s"], "object": "m.S.p", "value": "1", "at": "plan:p"}"#);
    assert_eq!((same["outcome"].as_str(), same["reason"].as_str()), (Some("silent"), Some("unchecked")), "{same}");
}

#[test]
fn the_write_at_the_head_of_a_compared_place_is_the_origin_of_the_divergence() {
    // 変更前は [m.O.s, m.S.p] に 1 を書く。候補は [m.O.s] に $t を丸ごと書く。比べる場所 [m.O.s, m.S.p] の値は、候補の頭の書き込みで決まる。
    let repo = Repo::new("nested-origin");
    repo.write(".archsig/law/m.law", &LAW.replace("\"shop/**\"", "\"m.py\""));
    repo.map("m.py", NESTED);
    repo.write(
        ".archsig/plans/p/plan.jsonl",
        r#"{"kind": "defines", "subject": "m.f", "value": "operation", "params": {"o": "m.O", "t": "m.S"}, "file": "m.py", "at": "plan:p"}
{"kind": "writes", "subject": "m.f", "object": "m.O.s", "value": "$t", "at": "plan:p"}
"#,
    );
    let s = repo.run(&["plan", "check", "p"]);
    let r = result(&s, "m.f");
    assert_eq!(r["kind"], "counterexample", "{s}");
    let d = repo.run(&["show", r["id"].as_str().unwrap()]);
    let diverging = d["check"]["diverging"].as_array().unwrap();
    assert!(diverging.iter().any(|x| x["writes"]["after"]["object"] == "m.O.s" && x["writes"]["after"]["at"] == "plan:p"), "{d}");
}

#[test]
fn the_heads_of_a_long_via_are_compared() {
    // via は [m.A.o, m.O.s]。意味は途中のフィールド m.O.s にある。[m.O.s] だけの場所は書かれないので、
    // 頭の部分の場所 [m.A.o, m.O.s] を比べる場所に入れなければ、意味を持つ値の変化を見落とす。
    // その場所の先に書き込みがあるので、値は決めていない(unchecked)。
    // 別の意味を持つフィールド m.A.k で二つの順番が食い違えば、その沈黙は結論に関わらず、反例を返す(設計 §5.4)。
    let run = |name: &str, k: &str| {
        let repo = Repo::new(name);
        repo.write(".archsig/law/m.law", &LAW.replace("\"shop/**\"", "\"m.py\""));
        repo.map(
            "m.py",
            r#"{"kind": "observed", "subject": "m.py", "scope": "structure", "at": "m.py@blob:aaaaaaa"}
{"kind": "resolves", "subject": "int", "object": "external:builtins", "at": "m.py:1@blob:aaaaaaa"}
{"kind": "observed", "subject": "m.py", "scope": "meaning:payment-info", "at": "m.py@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.A", "value": "type", "at": "m.py:1@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.A.o", "value": "field", "type": "m.O", "at": "m.py:2@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.A.k", "value": "field", "type": "int", "at": "m.py:2@blob:aaaaaaa"}
{"kind": "meaning", "subject": "m.A.k", "meaning": "payment-info", "uses": ["m.py:10@blob:aaaaaaa"], "at": "m.py:2@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.O", "value": "type", "at": "m.py:3@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.O.s", "value": "field", "type": "m.S", "at": "m.py:4@blob:aaaaaaa"}
{"kind": "meaning", "subject": "m.O.s", "meaning": "payment-info", "uses": ["m.py:9@blob:aaaaaaa"], "at": "m.py:4@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.S", "value": "type", "at": "m.py:5@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.S.p", "value": "field", "type": "int", "at": "m.py:6@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.f", "value": "operation", "params": {"a": "m.A"}, "at": "m.py:8@blob:aaaaaaa"}
{"kind": "writes", "subject": "m.f", "via": ["m.A.o", "m.O.s"], "object": "m.S.p", "value": "1", "at": "m.py:9@blob:aaaaaaa"}
{"kind": "writes", "subject": "m.f", "object": "m.A.k", "value": "1", "at": "m.py:10@blob:aaaaaaa"}
"#,
        );
        repo.write(
            ".archsig/plans/p/plan.jsonl",
            &format!(
                "{}\n{{\"kind\": \"writes\", \"subject\": \"m.f\", \"object\": \"m.A.k\", \"value\": \"{k}\", \"at\": \"plan:p\"}}\n",
                r#"{"kind": "defines", "subject": "m.f", "value": "operation", "params": {"a": "m.A"}, "file": "m.py", "at": "plan:p"}
{"kind": "writes", "subject": "m.f", "via": ["m.A.o", "m.O.s"], "object": "m.S.p", "value": "2", "at": "plan:p"}"#
            ),
        );
        repo.run(&["plan", "check", "p"])
    };
    let s = run("nested-long-via", "1");
    let r = result(&s, "m.f");
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unchecked")), "{s}");
    let s = run("nested-long-via-diverging", "2");
    let r = result(&s, "m.f");
    assert_eq!(r["kind"], "counterexample", "{s}");
}

#[test]
fn reading_a_head_place_after_a_nested_write_is_unchecked() {
    // 意味は m.S.p だけにある。入れ子に書いた後の手順が、途中の場所 [m.O.s] を丸ごと読む(when)。その値は決めていない。
    let repo = Repo::new("nested-head-read");
    repo.write(".archsig/law/m.law", &LAW.replace("\"shop/**\"", "\"m.py\""));
    repo.map(
        "m.py",
        &format!("{NESTED}{}", r#"{"kind": "writes", "subject": "m.f", "object": "m.S.p", "value": "3", "when": "$o.s == None", "at": "m.py:8@blob:aaaaaaa"}
"#),
    );
    repo.write(
        ".archsig/plans/p/plan.jsonl",
        r#"{"kind": "defines", "subject": "m.f", "value": "operation", "params": {"o": "m.O", "t": "m.S"}, "file": "m.py", "at": "plan:p"}
{"kind": "writes", "subject": "m.f", "via": ["m.O.s"], "object": "m.S.p", "value": "1", "at": "plan:p"}
{"kind": "writes", "subject": "m.f", "object": "m.S.p", "value": "3", "when": "$o.s == None", "at": "plan:p"}
"#,
    );
    let s = repo.run(&["plan", "check", "p"]);
    let r = result(&s, "m.f");
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unchecked")), "{s}");
}

/// 変更前: f(o) は o.s(S の値)を丸ごと書く。payment-info は S.p にある。a.py は O、m.py は S と f を定義する。
fn whole(name: &str, plan_value: &str, read_meaning_of_s: bool) -> Value {
    let repo = Repo::new(name);
    repo.write(".archsig/law/m.law", &LAW.replace("\"shop/**\"", "\"*.py\""));
    repo.map("a.py", r#"{"kind": "observed", "subject": "a.py", "scope": "structure", "at": "a.py@blob:bbbbbbb"}
{"kind": "observed", "subject": "a.py", "scope": "meaning:payment-info", "at": "a.py@blob:bbbbbbb"}
{"kind": "defines", "subject": "m.O", "value": "type", "at": "a.py:1@blob:bbbbbbb"}
{"kind": "defines", "subject": "m.O.s", "value": "field", "type": "m.S", "at": "a.py:2@blob:bbbbbbb"}
"#);
    let meaning_range = if read_meaning_of_s { "{\"kind\": \"observed\", \"subject\": \"m.py\", \"scope\": \"meaning:payment-info\", \"at\": \"m.py@blob:aaaaaaa\"}\n" } else { "" };
    repo.map("m.py", &format!("{}{meaning_range}{}", r#"{"kind": "observed", "subject": "m.py", "scope": "structure", "at": "m.py@blob:aaaaaaa"}
{"kind": "resolves", "subject": "int", "object": "external:builtins", "at": "m.py:1@blob:aaaaaaa"}
"#, r#"{"kind": "defines", "subject": "m.S", "value": "type", "at": "m.py:3@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.S.p", "value": "field", "type": "int", "at": "m.py:4@blob:aaaaaaa"}
{"kind": "meaning", "subject": "m.S.p", "meaning": "payment-info", "uses": ["m.py:7@blob:aaaaaaa"], "at": "m.py:4@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.f", "value": "operation", "params": {"o": "m.O"}, "at": "m.py:6@blob:aaaaaaa"}
{"kind": "writes", "subject": "m.f", "object": "m.O.s", "value": "m.a()", "at": "m.py:7@blob:aaaaaaa"}
"#));
    repo.write(
        ".archsig/plans/p/plan.jsonl",
        &format!(
            "{}\n{{\"kind\": \"writes\", \"subject\": \"m.f\", \"object\": \"m.O.s\", \"value\": \"{plan_value}\", \"at\": \"plan:p\"}}\n",
            r#"{"kind": "defines", "subject": "m.f", "value": "operation", "params": {"o": "m.O"}, "file": "m.py", "at": "plan:p"}"#
        ),
    );
    let s = repo.run(&["plan", "check", "p"]);
    let r = result(&s, "m.f").clone();
    if r["outcome"] == "fails" {
        return repo.run(&["show", r["id"].as_str().unwrap()]);
    }
    serde_json::json!({"summary": s, "result": r})
}

#[test]
fn a_place_below_a_written_field_with_the_meaning_is_compared() {
    // o.s を丸ごと書くと、場所 [m.O.s, m.S.p] の値も変わる。m.S.p は payment-info を持つ。
    let same = whole("below-same", "m.a()", true);
    assert_eq!(same["result"]["outcome"], "holds", "{same}");
    let changed = whole("below-changed", "m.b()", true);
    assert_eq!(changed["kind"], "counterexample", "{changed}");
    let places: Vec<&Value> = changed["check"]["diverging"].as_array().unwrap().iter().map(|d| &d["place"]).collect();
    assert!(places.contains(&&serde_json::json!(["m.O.s", "m.S.p"])), "{changed}");
}

#[test]
fn a_place_below_whose_meaning_was_not_read_is_silent() {
    let r = whole("below-unread", "m.b()", false);
    assert_eq!((r["result"]["outcome"].as_str(), r["result"]["reason"].as_str()), (Some("silent"), Some("unread")), "{r}");
    assert!(r["summary"]["next"].as_array().unwrap().iter().any(|n| n["read"] == "m.py" && n["scope"] == "meaning:payment-info"), "{r}");
}

#[test]
fn places_below_a_recursive_type_with_the_meaning_are_limit() {
    // N.next の型は N。payment-info は N.v にある。[m.O.n] を書くと、[m.O.n, m.N.next, …, m.N.v] が限りなく変わる。
    let repo = Repo::new("below-recursive");
    repo.write(".archsig/law/m.law", &LAW.replace("\"shop/**\"", "\"m.py\""));
    repo.map("m.py", r#"{"kind": "observed", "subject": "m.py", "scope": "structure", "at": "m.py@blob:aaaaaaa"}
{"kind": "resolves", "subject": "int", "object": "external:builtins", "at": "m.py:1@blob:aaaaaaa"}
{"kind": "observed", "subject": "m.py", "scope": "meaning:payment-info", "at": "m.py@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.O", "value": "type", "at": "m.py:1@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.O.n", "value": "field", "type": "m.N", "at": "m.py:2@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.N", "value": "type", "at": "m.py:3@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.N.next", "value": "field", "type": "m.N", "at": "m.py:4@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.N.v", "value": "field", "type": "int", "at": "m.py:5@blob:aaaaaaa"}
{"kind": "meaning", "subject": "m.N.v", "meaning": "payment-info", "uses": ["m.py:8@blob:aaaaaaa"], "at": "m.py:5@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.f", "value": "operation", "params": {"o": "m.O"}, "at": "m.py:7@blob:aaaaaaa"}
{"kind": "writes", "subject": "m.f", "object": "m.O.n", "value": "m.a()", "at": "m.py:8@blob:aaaaaaa"}
"#);
    repo.write(
        ".archsig/plans/p/plan.jsonl",
        r#"{"kind": "defines", "subject": "m.f", "value": "operation", "params": {"o": "m.O"}, "file": "m.py", "at": "plan:p"}
{"kind": "writes", "subject": "m.f", "object": "m.O.n", "value": "m.a()", "at": "plan:p"}
"#,
    );
    let s = repo.run(&["plan", "check", "p"]);
    let r = result(&s, "m.f");
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("limit")), "{s}");
}

#[test]
fn a_place_below_a_via_write_with_the_meaning_is_compared() {
    // via: [m.A.o]、object: m.O.s に書く。payment-info は m.O.s の型 m.S のフィールド m.S.p にある。
    let run = |name: &str, value: &str| {
        let repo = Repo::new(name);
        repo.write(".archsig/law/m.law", &LAW.replace("\"shop/**\"", "\"m.py\""));
        repo.map("m.py", MAP);
        repo.write(
            ".archsig/plans/p/plan.jsonl",
            &format!(
                "{}\n{{\"kind\": \"writes\", \"subject\": \"m.f\", \"via\": [\"m.A.o\"], \"object\": \"m.O.s\", \"value\": \"{value}\", \"at\": \"plan:p\"}}\n",
                r#"{"kind": "defines", "subject": "m.f", "value": "operation", "params": {"a": "m.A"}, "file": "m.py", "at": "plan:p"}"#
            ),
        );
        let s = repo.run(&["plan", "check", "p"]);
        let r = result(&s, "m.f").clone();
        if r["outcome"] == "fails" { repo.run(&["show", r["id"].as_str().unwrap()]) } else { r }
    };
    const MAP: &str = r#"{"kind": "observed", "subject": "m.py", "scope": "structure", "at": "m.py@blob:aaaaaaa"}
{"kind": "resolves", "subject": "int", "object": "external:builtins", "at": "m.py:1@blob:aaaaaaa"}
{"kind": "observed", "subject": "m.py", "scope": "meaning:payment-info", "at": "m.py@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.A", "value": "type", "at": "m.py:1@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.A.o", "value": "field", "type": "m.O", "at": "m.py:2@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.O", "value": "type", "at": "m.py:3@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.O.s", "value": "field", "type": "m.S", "at": "m.py:4@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.S", "value": "type", "at": "m.py:5@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.S.p", "value": "field", "type": "int", "at": "m.py:6@blob:aaaaaaa"}
{"kind": "meaning", "subject": "m.S.p", "meaning": "payment-info", "uses": ["m.py:9@blob:aaaaaaa"], "at": "m.py:6@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.f", "value": "operation", "params": {"a": "m.A"}, "at": "m.py:8@blob:aaaaaaa"}
{"kind": "writes", "subject": "m.f", "via": ["m.A.o"], "object": "m.O.s", "value": "m.a()", "at": "m.py:9@blob:aaaaaaa"}
"#;
    assert_eq!(run("below-via-same", "m.a()")["outcome"], "holds");
    let d = run("below-via-changed", "m.b()");
    let places: Vec<&Value> = d["check"]["diverging"].as_array().unwrap().iter().map(|x| &x["place"]).collect();
    assert_eq!(places, vec![&serde_json::json!(["m.A.o", "m.O.s", "m.S.p"])], "{d}");
}

/// m.py の観測(構造と payment-info を読んだ)と候補で `plan check` し、サマリと m.f の結果(反例なら詳細)を返す。
fn below_case(name: &str, atoms: &str, plan: &str) -> (Value, Value) {
    let repo = Repo::new(name);
    repo.write(".archsig/law/m.law", &LAW.replace("\"shop/**\"", "\"m.py\""));
    repo.map(
        "m.py",
        &format!(
            "{}{atoms}",
            r#"{"kind": "observed", "subject": "m.py", "scope": "structure", "at": "m.py@blob:aaaaaaa"}
{"kind": "resolves", "subject": "int", "object": "external:builtins", "at": "m.py:1@blob:aaaaaaa"}
{"kind": "observed", "subject": "m.py", "scope": "meaning:payment-info", "at": "m.py@blob:aaaaaaa"}
"#
        ),
    );
    repo.write(".archsig/plans/p/plan.jsonl", plan);
    let s = repo.run(&["plan", "check", "p"]);
    let r = result(&s, "m.f").clone();
    let r = if r["outcome"] == "fails" { repo.run(&["show", r["id"].as_str().unwrap()]) } else { r };
    (s, r)
}

const F_WRITES_A: &str = r#"{"kind": "defines", "subject": "m.f", "value": "operation", "params": {"o": "m.O"}, "at": "m.py:9@blob:aaaaaaa"}
{"kind": "writes", "subject": "m.f", "object": "m.O.s", "value": "m.a()", "at": "m.py:10@blob:aaaaaaa"}
"#;

const PLAN_WRITES_B: &str = r#"{"kind": "defines", "subject": "m.f", "value": "operation", "params": {"o": "m.O"}, "file": "m.py", "at": "plan:p"}
{"kind": "writes", "subject": "m.f", "object": "m.O.s", "value": "m.b()", "at": "plan:p"}
"#;

const O_S: &str = r#"{"kind": "defines", "subject": "m.O", "value": "type", "at": "m.py:1@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.O.s", "value": "field", "type": "m.S", "at": "m.py:2@blob:aaaaaaa"}
"#;

#[test]
fn a_type_whose_definition_was_not_read_is_silent_below() {
    // m.S の resolves は s.py を指すが、s.py を読んでいない(設計 §3.3)。
    let (s, r) = below_case(
        "below-unread-type",
        &format!("{O_S}{{\"kind\": \"resolves\", \"subject\": \"m.S\", \"object\": \"s.py\", \"at\": \"m.py:1@blob:aaaaaaa\"}}\n{F_WRITES_A}"),
        PLAN_WRITES_B,
    );
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unread")), "{s}");
    assert!(s["next"].as_array().unwrap().iter().any(|n| n["read"] == "s.py" && n["decides"].as_array().unwrap().contains(&r["id"])), "{s}");
}

#[test]
fn a_question_mark_type_is_silent_below() {
    let (s, r) = below_case("below-question-type", &format!("{}{F_WRITES_A}", O_S.replace("\"type\": \"m.S\"", "\"type\": \"?m.S\"")), PLAN_WRITES_B);
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unresolved")), "{s}");
    assert!(s["next"].as_array().unwrap().iter().any(|n| n["read"] == "m.py"), "その型を書いたフィールドの定義の場所を返す: {s}");
}

#[test]
fn an_ambiguous_type_is_unresolved_below() {
    let atoms = format!(
        "{O_S}{}{F_WRITES_A}",
        r#"{"kind": "defines", "subject": "m.S", "value": "type", "at": "m.py:3@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.S", "value": "operation", "params": {}, "at": "m.py:4@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.S.p", "value": "field", "type": "int", "at": "m.py:5@blob:aaaaaaa"}
{"kind": "meaning", "subject": "m.S.p", "meaning": "payment-info", "uses": ["m.py:10@blob:aaaaaaa"], "at": "m.py:5@blob:aaaaaaa"}
"#
    );
    let (s, r) = below_case("below-ambiguous-type", &atoms, PLAN_WRITES_B);
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unresolved")), "{s}");
}

#[test]
fn too_many_places_below_are_limit() {
    // T0..T13 の各型が、次の型のフィールド a と b を持つ。たどるフィールドは上限(STEP_LIMIT)を超える。
    let mut atoms = String::from(
        r#"{"kind": "defines", "subject": "m.O", "value": "type", "at": "m.py:1@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.O.s", "value": "field", "type": "m.T0", "at": "m.py:2@blob:aaaaaaa"}
"#,
    );
    atoms.push_str("{\"kind\": \"defines\", \"subject\": \"m.T14\", \"value\": \"type\", \"at\": \"m.py:3@blob:aaaaaaa\"}\n");
    for i in 0..14 {
        atoms.push_str(&format!("{{\"kind\": \"defines\", \"subject\": \"m.T{i}\", \"value\": \"type\", \"at\": \"m.py:3@blob:aaaaaaa\"}}\n"));
        for f in ["a", "b"] {
            atoms.push_str(&format!("{{\"kind\": \"defines\", \"subject\": \"m.T{i}.{f}\", \"value\": \"field\", \"type\": \"m.T{}\", \"at\": \"m.py:4@blob:aaaaaaa\"}}\n", i + 1));
        }
    }
    let (s, r) = below_case("below-limit", &format!("{atoms}{F_WRITES_A}"), PLAN_WRITES_B);
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("limit")), "{s}");
}

const S_P: &str = r#"{"kind": "defines", "subject": "m.S", "value": "type", "at": "m.py:3@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.S.p", "value": "field", "type": "int", "at": "m.py:4@blob:aaaaaaa"}
{"kind": "meaning", "subject": "m.S.p", "meaning": "payment-info", "uses": ["m.py:10@blob:aaaaaaa"], "at": "m.py:4@blob:aaaaaaa"}
"#;

#[test]
fn an_external_type_is_a_condition() {
    // m.S.p の型 int は、resolves が外部を指す(below_case の観測に入っている)。意味を持つフィールドを持たないとみなし、成り立つ条件に並べる。
    let (s, r) = below_case("below-condition", &format!("{O_S}{S_P}{F_WRITES_A}"), PLAN_WRITES_B);
    assert_eq!(r["kind"], "counterexample", "{s}");
    assert!(r["conditions"].as_array().unwrap().iter().any(|c| c == "外部の型 int は、意味を持つフィールドを持たないとみなす"), "{r}");
}

#[test]
fn a_type_without_resolves_is_unread_below() {
    // m.O.s の型 m.Z は、定義も resolves もない(設計 §3.3)。要素の名前を次に読む所として返す。
    let (s, r) = below_case("below-no-resolves", &format!("{}{F_WRITES_A}", O_S.replace("\"type\": \"m.S\"", "\"type\": \"m.Z\"")), PLAN_WRITES_B);
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unread")), "{s}");
    assert!(s["next"].as_array().unwrap().iter().any(|n| n["element"] == "m.Z"), "{s}");
}

#[test]
fn a_place_below_is_compared_when_only_one_order_writes() {
    let plan_other = r#"{"kind": "defines", "subject": "m.f", "value": "operation", "params": {"o": "m.O"}, "file": "m.py", "at": "plan:p"}
"#;
    // 変更前だけが o.s を書く。
    let (s, r) = below_case("below-before-only", &format!("{O_S}{S_P}{F_WRITES_A}"), plan_other);
    assert_eq!(r["kind"], "counterexample", "{s}");
    // 変更後だけが o.s を書く。
    let (s, r) = below_case("below-after-only", &format!("{O_S}{S_P}{}", r#"{"kind": "defines", "subject": "m.f", "value": "operation", "params": {"o": "m.O"}, "at": "m.py:9@blob:aaaaaaa"}
"#), PLAN_WRITES_B);
    assert_eq!(r["kind"], "counterexample", "{s}");
}

#[test]
fn a_recursive_type_without_the_meaning_below_is_not_limit() {
    // S.back の型は S だが、S から意味を持つフィールドには着かない。
    let atoms = format!(
        "{O_S}{}{F_WRITES_A}",
        r#"{"kind": "defines", "subject": "m.S", "value": "type", "at": "m.py:3@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.S.back", "value": "field", "type": "m.S", "at": "m.py:4@blob:aaaaaaa"}
"#
    );
    let (s, r) = below_case("below-cycle-no-meaning", &atoms, PLAN_WRITES_B);
    assert_ne!(r["reason"], "limit", "{s}");
    assert_eq!(r["outcome"], "holds", "{s}");
}

#[test]
fn a_type_name_that_is_not_a_type_is_unresolved_below() {
    // m.O.s の型 m.S は、操作として定義されている。
    let atoms = format!(
        "{O_S}{}{F_WRITES_A}",
        r#"{"kind": "defines", "subject": "m.S", "value": "operation", "params": {}, "at": "m.py:3@blob:aaaaaaa"}
"#
    );
    let (s, r) = below_case("below-not-a-type", &atoms, PLAN_WRITES_B);
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unresolved")), "{s}");
}

#[test]
fn the_limit_below_counts_one_written_place_not_the_branches() {
    // 型 m.S はフィールドを 3000 個と p を持つ。o.s を、条件の違う二つの分岐で同じ値に書く。たどる場所は分岐によらず同じである。
    // 分岐と書き込みをまたいで数えると上限(STEP_LIMIT)を超えるが、一つの書き込みの場所から数えれば超えない。
    let mut atoms = format!("{O_S}{S_P}");
    for i in 0..3000 {
        atoms.push_str(&format!("{{\"kind\": \"defines\", \"subject\": \"m.S.f{i}\", \"value\": \"field\", \"type\": \"int\", \"at\": \"m.py:5@blob:aaaaaaa\"}}\n"));
    }
    let f = r#"{"kind": "defines", "subject": "m.f", "value": "operation", "params": {"o": "m.O"}, "at": "m.py:9@blob:aaaaaaa"}
{"kind": "writes", "subject": "m.f", "object": "m.O.s", "value": "m.a()", "when": "m.c1()", "at": "m.py:10@blob:aaaaaaa"}
{"kind": "writes", "subject": "m.f", "object": "m.O.s", "value": "m.a()", "when": "m.c2()", "at": "m.py:11@blob:aaaaaaa"}
"#;
    let plan = r#"{"kind": "defines", "subject": "m.f", "value": "operation", "params": {"o": "m.O"}, "file": "m.py", "at": "plan:p"}
{"kind": "writes", "subject": "m.f", "object": "m.O.s", "value": "m.a()", "when": "m.c1()", "at": "plan:p"}
{"kind": "writes", "subject": "m.f", "object": "m.O.s", "value": "m.a()", "when": "m.c2()", "at": "plan:p"}
"#;
    let (s, r) = below_case("below-limit-per-place", &format!("{atoms}{f}"), plan);
    assert_eq!(r["outcome"], "holds", "{s}");
}

#[test]
fn a_type_whose_definition_was_not_read_is_unread_even_if_some_fields_were_read() {
    // 型 m.S の defines も resolves もない。フィールド m.S.p の定義と意味は読んであるが、m.S のほかのフィールドは分からない(設計 §3.3)。
    let atoms = format!(
        "{O_S}{}{F_WRITES_A}",
        r#"{"kind": "defines", "subject": "m.S.p", "value": "field", "type": "int", "at": "m.py:4@blob:aaaaaaa"}
{"kind": "meaning", "subject": "m.S.p", "meaning": "payment-info", "uses": ["m.py:10@blob:aaaaaaa"], "at": "m.py:4@blob:aaaaaaa"}
"#
    );
    let (s, r) = below_case("below-fields-without-type", &atoms, PLAN_WRITES_B);
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unread")), "{s}");
    assert!(s["next"].as_array().unwrap().iter().any(|n| n["element"] == "m.S"), "{s}");
}

#[test]
fn a_plan_that_adds_a_field_to_an_unread_type_is_still_unread() {
    // m.S の resolves は s.py を指し、s.py は読んでいない。候補が m.S にフィールドを足しても、s.py にあるほかのフィールドは分からない。
    let atoms = format!("{O_S}{{\"kind\": \"resolves\", \"subject\": \"m.S\", \"object\": \"s.py\", \"at\": \"m.py:1@blob:aaaaaaa\"}}\n{F_WRITES_A}");
    let plan = format!("{PLAN_WRITES_B}{}", r#"{"kind": "defines", "subject": "m.S.q", "value": "field", "type": "int", "file": "s.py", "at": "plan:p"}
"#);
    let (s, r) = below_case("below-plan-adds-field", &atoms, &plan);
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unread")), "{s}");
    assert!(s["next"].as_array().unwrap().iter().any(|n| n["read"] == "s.py"), "{s}");
}

#[test]
fn a_cycle_without_the_meaning_does_not_count_toward_the_limit() {
    // m.S は int のフィールド 6000 個と、型 m.S のフィールド 3 個を持つ。意味を持つフィールドはない。たどる場所は 6003 個である。
    // めぐりの確かめのたどりも数えると、上限(STEP_LIMIT)を超える。
    let mut atoms = format!("{O_S}{}", r#"{"kind": "defines", "subject": "m.S", "value": "type", "at": "m.py:3@blob:aaaaaaa"}
"#);
    for i in 0..6000 {
        atoms.push_str(&format!("{{\"kind\": \"defines\", \"subject\": \"m.S.f{i}\", \"value\": \"field\", \"type\": \"int\", \"at\": \"m.py:4@blob:aaaaaaa\"}}\n"));
    }
    for i in 0..3 {
        atoms.push_str(&format!("{{\"kind\": \"defines\", \"subject\": \"m.S.back{i}\", \"value\": \"field\", \"type\": \"m.S\", \"at\": \"m.py:5@blob:aaaaaaa\"}}\n"));
    }
    let (s, r) = below_case("below-cycle-count", &format!("{atoms}{F_WRITES_A}"), PLAN_WRITES_B);
    assert_eq!(r["outcome"], "holds", "{s}");
}

#[test]
fn the_limit_below_counts_each_written_place_on_its_own() {
    // o.s と o.t はどちらも型 m.S(フィールド 6000 個と p)。一つの場所からたどるのは 6001 個で、上限(STEP_LIMIT)を超えない。
    let mut atoms = format!("{O_S}{S_P}{}", r#"{"kind": "defines", "subject": "m.O.t", "value": "field", "type": "m.S", "at": "m.py:2@blob:aaaaaaa"}
"#);
    for i in 0..6000 {
        atoms.push_str(&format!("{{\"kind\": \"defines\", \"subject\": \"m.S.f{i}\", \"value\": \"field\", \"type\": \"int\", \"at\": \"m.py:5@blob:aaaaaaa\"}}\n"));
    }
    let f = r#"{"kind": "defines", "subject": "m.f", "value": "operation", "params": {"o": "m.O"}, "at": "m.py:9@blob:aaaaaaa"}
{"kind": "writes", "subject": "m.f", "object": "m.O.s", "value": "m.a()", "at": "m.py:10@blob:aaaaaaa"}
{"kind": "writes", "subject": "m.f", "object": "m.O.t", "value": "m.a()", "at": "m.py:11@blob:aaaaaaa"}
"#;
    let plan = r#"{"kind": "defines", "subject": "m.f", "value": "operation", "params": {"o": "m.O"}, "file": "m.py", "at": "plan:p"}
{"kind": "writes", "subject": "m.f", "object": "m.O.s", "value": "m.a()", "at": "plan:p"}
{"kind": "writes", "subject": "m.f", "object": "m.O.t", "value": "m.a()", "at": "plan:p"}
"#;
    let (s, r) = below_case("below-limit-each-place", &format!("{atoms}{f}"), plan);
    assert_eq!(r["outcome"], "holds", "{s}");
}

#[test]
fn a_write_before_is_followed_through_the_type_before() {
    // 変更前の o.s の型は m.S(m.S.p が payment-info)。候補は o.s の型を m.S2 に書き直し、別の値を書く。
    let atoms = format!("{O_S}{S_P}{F_WRITES_A}");
    let plan = r#"{"kind": "defines", "subject": "m.f", "value": "operation", "params": {"o": "m.O"}, "file": "m.py", "at": "plan:p"}
{"kind": "writes", "subject": "m.f", "object": "m.O.s", "value": "m.b()", "at": "plan:p"}
{"kind": "defines", "subject": "m.O.s", "value": "field", "type": "m.S2", "file": "m.py", "at": "plan:p"}
{"kind": "defines", "subject": "m.S2", "value": "type", "file": "m.py", "at": "plan:p"}
{"kind": "defines", "subject": "m.S2.q", "value": "field", "type": "int", "file": "m.py", "at": "plan:p"}
"#;
    let (s, r) = below_case("below-type-changed", &atoms, plan);
    assert_eq!(r["kind"], "counterexample", "{s}");
    let places: Vec<&Value> = r["check"]["diverging"].as_array().unwrap().iter().map(|d| &d["place"]).collect();
    assert!(places.contains(&&serde_json::json!(["m.O.s", "m.S.p"])), "{r}");
}

#[test]
fn a_place_two_fields_below_is_compared() {
    // o.s: m.S、m.S.t: m.T、m.T.p が payment-info。
    let atoms = format!(
        "{O_S}{}{F_WRITES_A}",
        r#"{"kind": "defines", "subject": "m.S", "value": "type", "at": "m.py:3@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.S.t", "value": "field", "type": "m.T", "at": "m.py:4@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.T", "value": "type", "at": "m.py:5@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.T.p", "value": "field", "type": "int", "at": "m.py:6@blob:aaaaaaa"}
{"kind": "meaning", "subject": "m.T.p", "meaning": "payment-info", "uses": ["m.py:10@blob:aaaaaaa"], "at": "m.py:6@blob:aaaaaaa"}
"#
    );
    let (s, r) = below_case("below-two-fields", &atoms, PLAN_WRITES_B);
    assert_eq!(r["kind"], "counterexample", "{s}");
    let places: Vec<&Value> = r["check"]["diverging"].as_array().unwrap().iter().map(|d| &d["place"]).collect();
    assert_eq!(places, vec![&serde_json::json!(["m.O.s", "m.S.t", "m.T.p"])], "{r}");
}

#[test]
fn a_write_before_is_also_followed_through_the_type_after() {
    // 変更前は o.s(型 m.S、意味を持つフィールドなし)を書く。候補は o.s の型を m.S2 に変え、m.S2.r: m.T を足し、o.s に書かない。
    // m.T.p は payment-info を持つ。変更前に書いた値から、変更後の型でたどる場所 [m.O.s, m.S2.r, m.T.p] の値が変わる。
    let atoms = format!(
        "{O_S}{}{F_WRITES_A}",
        r#"{"kind": "defines", "subject": "m.S", "value": "type", "at": "m.py:3@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.S.q", "value": "field", "type": "int", "at": "m.py:4@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.T", "value": "type", "at": "m.py:5@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.T.p", "value": "field", "type": "int", "at": "m.py:6@blob:aaaaaaa"}
{"kind": "meaning", "subject": "m.T.p", "meaning": "payment-info", "uses": ["m.py:10@blob:aaaaaaa"], "at": "m.py:6@blob:aaaaaaa"}
"#
    );
    let plan = r#"{"kind": "defines", "subject": "m.f", "value": "operation", "params": {"o": "m.O"}, "file": "m.py", "at": "plan:p"}
{"kind": "defines", "subject": "m.O.s", "value": "field", "type": "m.S2", "file": "m.py", "at": "plan:p"}
{"kind": "defines", "subject": "m.S2", "value": "type", "file": "m.py", "at": "plan:p"}
{"kind": "defines", "subject": "m.S2.r", "value": "field", "type": "m.T", "file": "m.py", "at": "plan:p"}
"#;
    let (s, r) = below_case("below-before-after-type", &atoms, plan);
    assert_eq!(r["kind"], "counterexample", "{s}");
    let places: Vec<&Value> = r["check"]["diverging"].as_array().unwrap().iter().map(|d| &d["place"]).collect();
    assert!(places.contains(&&serde_json::json!(["m.O.s", "m.S2.r", "m.T.p"])), "{r}");
}

#[test]
fn a_type_the_plan_redefines_is_still_unread_where_its_source_was_not_read() {
    // m.S の resolves は s.py を指し、s.py は読んでいない。変更前の m.f は o.s に書かない。
    // 候補は m.S の defines を書き直して o.s に書くが、s.py にある元のフィールドは分からない。
    let atoms = format!(
        "{O_S}{{\"kind\": \"resolves\", \"subject\": \"m.S\", \"object\": \"s.py\", \"at\": \"m.py:1@blob:aaaaaaa\"}}\n{}",
        r#"{"kind": "defines", "subject": "m.f", "value": "operation", "params": {"o": "m.O"}, "at": "m.py:9@blob:aaaaaaa"}
"#
    );
    let plan = format!("{PLAN_WRITES_B}{}", r#"{"kind": "defines", "subject": "m.S", "value": "type", "file": "s.py", "at": "plan:p"}
{"kind": "defines", "subject": "m.S.q", "value": "field", "type": "int", "file": "s.py", "at": "plan:p"}
"#);
    let (s, r) = below_case("below-plan-redefines-type", &atoms, &plan);
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unread")), "{s}");
    assert!(s["next"].as_array().unwrap().iter().any(|n| n["read"] == "s.py"), "{s}");
}

#[test]
fn a_field_without_a_type_is_unresolved_below() {
    // 書いたフィールド m.O.s に type がない。その先に意味を持つフィールドがあるかは決まらない。
    let (s, r) = below_case("below-no-type", &format!("{}{F_WRITES_A}", O_S.replace(", \"type\": \"m.S\"", "")), PLAN_WRITES_B);
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unresolved")), "{s}");
    // たどった先のフィールド m.S.t に type がないときも同じ。
    let atoms = format!(
        "{O_S}{}{F_WRITES_A}",
        r#"{"kind": "defines", "subject": "m.S", "value": "type", "at": "m.py:3@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.S.t", "value": "field", "at": "m.py:4@blob:aaaaaaa"}
"#
    );
    let (s, r) = below_case("below-no-type-inside", &atoms, PLAN_WRITES_B);
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unresolved")), "{s}");
}

#[test]
fn a_field_below_whose_meaning_range_was_not_read_is_unread() {
    // m.S は s.py にある。s.py は構造だけを読み、payment-info の範囲は読んでいない(意味 Atom もない)。
    let repo = Repo::new("below-meaning-range");
    repo.write(".archsig/law/m.law", &LAW.replace("\"shop/**\"", "\"*.py\""));
    repo.map("m.py", &format!("{}{O_S}{F_WRITES_A}", r#"{"kind": "observed", "subject": "m.py", "scope": "structure", "at": "m.py@blob:aaaaaaa"}
{"kind": "observed", "subject": "m.py", "scope": "meaning:payment-info", "at": "m.py@blob:aaaaaaa"}
{"kind": "resolves", "subject": "int", "object": "external:builtins", "at": "m.py:1@blob:aaaaaaa"}
"#));
    repo.map("s.py", r#"{"kind": "observed", "subject": "s.py", "scope": "structure", "at": "s.py@blob:bbbbbbb"}
{"kind": "defines", "subject": "m.S", "value": "type", "at": "s.py:1@blob:bbbbbbb"}
{"kind": "defines", "subject": "m.S.p", "value": "field", "type": "int", "at": "s.py:2@blob:bbbbbbb"}
"#);
    repo.write(".archsig/plans/p/plan.jsonl", PLAN_WRITES_B);
    let s = repo.run(&["plan", "check", "p"]);
    let r = result(&s, "m.f");
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unread")), "{s}");
    assert!(s["next"].as_array().unwrap().iter().any(|n| n["read"] == "s.py" && n["scope"] == "meaning:payment-info"), "{s}");
}

#[test]
fn an_existing_type_without_resolves_that_the_plan_redefines_is_still_unread() {
    // 変更前は m.O.s の型として m.S を名指すが、m.S の定義も resolves もない。変更前の m.f は o.s に書かない。
    // 候補は m.S を定義し直して o.s に書く。元の m.S のフィールドは分からない(設計 §3.3)。
    let atoms = format!(
        "{O_S}{}",
        r#"{"kind": "defines", "subject": "m.f", "value": "operation", "params": {"o": "m.O"}, "at": "m.py:9@blob:aaaaaaa"}
"#
    );
    let plan = format!("{PLAN_WRITES_B}{}", r#"{"kind": "defines", "subject": "m.S", "value": "type", "file": "m.py", "at": "plan:p"}
{"kind": "defines", "subject": "m.S.q", "value": "field", "type": "int", "file": "m.py", "at": "plan:p"}
"#);
    let (s, r) = below_case("below-plan-redefines-unresolved-type", &atoms, &plan);
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unread")), "{s}");
    assert!(s["next"].as_array().unwrap().iter().any(|n| n["element"] == "m.S"), "{s}");
}

#[test]
fn a_large_type_without_the_meaning_is_not_limit() {
    // m.S は int のフィールドを 300 個持ち、意味を持つフィールドはない。
    let mut atoms = format!("{O_S}{}", r#"{"kind": "defines", "subject": "m.S", "value": "type", "at": "m.py:3@blob:aaaaaaa"}
"#);
    for i in 0..300 {
        atoms.push_str(&format!("{{\"kind\": \"defines\", \"subject\": \"m.S.f{i}\", \"value\": \"field\", \"type\": \"int\", \"at\": \"m.py:4@blob:aaaaaaa\"}}\n"));
    }
    let (s, r) = below_case("below-large-type", &format!("{atoms}{F_WRITES_A}"), PLAN_WRITES_B);
    assert_eq!(r["outcome"], "holds", "{s}");
}

#[test]
fn a_field_named_but_not_defined_is_unread_below() {
    // m.S の定義と m.S.q は読んである。m.S.p は resolves で b.py を指して名指されているが、定義を読んでいない。
    let atoms = format!(
        "{O_S}{}{F_WRITES_A}",
        r#"{"kind": "defines", "subject": "m.S", "value": "type", "at": "m.py:3@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.S.q", "value": "field", "type": "int", "at": "m.py:4@blob:aaaaaaa"}
{"kind": "resolves", "subject": "m.S.p", "object": "b.py", "at": "m.py:5@blob:aaaaaaa"}
"#
    );
    let (s, r) = below_case("below-named-field", &atoms, PLAN_WRITES_B);
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unread")), "{s}");
    assert!(s["next"].as_array().unwrap().iter().any(|n| n["read"] == "b.py"), "{s}");
}

#[test]
fn a_type_named_by_a_call_that_the_plan_redefines_is_still_unread() {
    // 変更前は、操作 m.g の呼び出しで m.S を名指すだけで、m.S の定義も resolves もない。o.s の型は m.R。
    // 候補は m.S を定義し、o.s の型を m.S に書き直して書く。元の m.S のフィールドは分からない。
    let atoms = format!(
        "{}{}",
        O_S.replace("\"type\": \"m.S\"", "\"type\": \"m.R\""),
        r#"{"kind": "defines", "subject": "m.R", "value": "type", "at": "m.py:3@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.g", "value": "operation", "params": {}, "at": "m.py:7@blob:aaaaaaa"}
{"kind": "calls", "subject": "m.g", "object": "m.S", "at": "m.py:8@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.f", "value": "operation", "params": {"o": "m.O"}, "at": "m.py:9@blob:aaaaaaa"}
"#
    );
    let plan = format!("{PLAN_WRITES_B}{}", r#"{"kind": "defines", "subject": "m.O.s", "value": "field", "type": "m.S", "file": "m.py", "at": "plan:p"}
{"kind": "defines", "subject": "m.S", "value": "type", "file": "m.py", "at": "plan:p"}
{"kind": "defines", "subject": "m.S.q", "value": "field", "type": "int", "file": "m.py", "at": "plan:p"}
"#);
    let (s, r) = below_case("below-call-named-type", &atoms, &plan);
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unread")), "{s}");
    assert!(s["next"].as_array().unwrap().iter().any(|n| n["element"] == "m.S"), "{s}");
}

#[test]
fn an_external_type_the_plan_redefines_is_read_as_the_plan_defines_it() {
    // 変更前の m.S は resolves で外部を指す。候補が m.S を定義し直せば、候補の定義をその型のすべてとしてたどり、m.S.q の型 int に着く。
    // 変更前の構造でたどる書き込みでは m.S は外部の型だが、変更後の構造が候補の定義でたどるので、外部の型 m.S は条件に並べない(設計 §5.4)。
    let repo = Repo::new("below-external-redefined");
    repo.write(".archsig/law/m.law", &LAW.replace("\"shop/**\"", "\"m.py\""));
    repo.map(
        "m.py",
        &format!(
            "{}{O_S}{{\"kind\": \"resolves\", \"subject\": \"m.S\", \"object\": \"external:lib\", \"at\": \"m.py:1@blob:aaaaaaa\"}}\n{F_WRITES_A}",
            r#"{"kind": "observed", "subject": "m.py", "scope": "structure", "at": "m.py@blob:aaaaaaa"}
{"kind": "observed", "subject": "m.py", "scope": "meaning:payment-info", "at": "m.py@blob:aaaaaaa"}
{"kind": "resolves", "subject": "int", "object": "external:builtins", "at": "m.py:1@blob:aaaaaaa"}
"#
        ),
    );
    repo.write(
        ".archsig/plans/p/plan.jsonl",
        &format!("{PLAN_WRITES_B}{}", r#"{"kind": "defines", "subject": "m.S", "value": "type", "file": "m.py", "at": "plan:p"}
{"kind": "defines", "subject": "m.S.q", "value": "field", "type": "int", "file": "m.py", "at": "plan:p"}
"#),
    );
    let s = repo.run(&["plan", "check", "p"]);
    let r = result(&s, "m.f");
    assert_eq!(r["outcome"], "holds", "{s}");
    let d = repo.run(&["show", r["id"].as_str().unwrap()]);
    assert!(d["conditions"].as_array().unwrap().iter().any(|c| c == "外部の型 int は、意味を持つフィールドを持たないとみなす"), "{d}");
    assert!(!d["conditions"].as_array().unwrap().iter().any(|c| c == "外部の型 m.S は、意味を持つフィールドを持たないとみなす"), "{d}");
}

#[test]
fn a_field_named_only_in_an_expression_is_unread_below() {
    // m.S の定義と m.S.p は読んである。別の操作 m.g の条件が $o.s.q で m.S.q を名指すが、m.S.q の定義を読んでいない。
    let atoms = format!(
        "{O_S}{}{F_WRITES_A}",
        r#"{"kind": "defines", "subject": "m.S", "value": "type", "at": "m.py:3@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.S.p", "value": "field", "type": "int", "at": "m.py:4@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.g", "value": "operation", "params": {"o": "m.O"}, "at": "m.py:6@blob:aaaaaaa"}
{"kind": "writes", "subject": "m.g", "object": "m.S.p", "value": "1", "when": "$o.s.q == 1", "at": "m.py:7@blob:aaaaaaa"}
"#
    );
    let (s, r) = below_case("below-expression-named", &atoms, PLAN_WRITES_B);
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unread")), "{s}");
    assert!(s["next"].as_array().unwrap().iter().any(|n| n["element"] == "m.S.q"), "{s}");
}

#[test]
fn a_counterexample_is_not_hidden_by_a_type_not_read_below() {
    // o.p(payment-info)と o.s(型 m.Z、定義も resolves もない)を書く。o.p の値が違えば、m.Z の先が分からなくても反例は決まる。
    let atoms = |p: &str| {
        format!(
            "{}{}\n{p}\n",
            O_S.replace("\"type\": \"m.S\"", "\"type\": \"m.Z\""),
            r#"{"kind": "defines", "subject": "m.O.p", "value": "field", "type": "int", "at": "m.py:3@blob:aaaaaaa"}
{"kind": "meaning", "subject": "m.O.p", "meaning": "payment-info", "uses": ["m.py:10@blob:aaaaaaa"], "at": "m.py:3@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.f", "value": "operation", "params": {"o": "m.O"}, "at": "m.py:9@blob:aaaaaaa"}
{"kind": "writes", "subject": "m.f", "object": "m.O.s", "value": "m.a()", "at": "m.py:10@blob:aaaaaaa"}"#
        )
    };
    let plan = |p: &str| {
        format!(
            "{}{p}\n",
            r#"{"kind": "defines", "subject": "m.f", "value": "operation", "params": {"o": "m.O"}, "file": "m.py", "at": "plan:p"}
{"kind": "writes", "subject": "m.f", "object": "m.O.s", "value": "m.a()", "at": "plan:p"}
"#
        )
    };
    let before_p = r#"{"kind": "writes", "subject": "m.f", "object": "m.O.p", "value": "1", "at": "m.py:11@blob:aaaaaaa"}"#;
    let (s, r) = below_case("below-hidden-differs", &atoms(before_p), &plan(r#"{"kind": "writes", "subject": "m.f", "object": "m.O.p", "value": "2", "at": "plan:p"}"#));
    assert_eq!(r["kind"], "counterexample", "{s}");
    let (s, r) = below_case("below-hidden-same", &atoms(before_p), &plan(r#"{"kind": "writes", "subject": "m.f", "object": "m.O.p", "value": "1", "at": "plan:p"}"#));
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unread")), "{s}");
}

#[test]
fn a_removed_field_still_named_elsewhere_is_not_unread_below() {
    // 候補は m.S.p を消して m.S.p2 に移す。書き直していない m.h は m.S.p を読んだまま(missing)。
    let atoms = format!(
        "{O_S}{S_P}{}{F_WRITES_A}",
        r#"{"kind": "defines", "subject": "m.h", "value": "operation", "params": {}, "at": "m.py:7@blob:aaaaaaa"}
{"kind": "reads", "subject": "m.h", "object": "m.S.p", "at": "m.py:8@blob:aaaaaaa"}
"#
    );
    let plan = format!("{PLAN_WRITES_B}{}", r#"{"kind": "removes", "subject": "m.S.p", "at": "plan:p"}
{"kind": "defines", "subject": "m.S.p2", "value": "field", "type": "int", "file": "m.py", "at": "plan:p"}
{"kind": "corresponds", "subject": "m.S.p", "object": "m.S.p2", "at": "plan:p"}
"#);
    let (s, r) = below_case("below-removed-named", &atoms, &plan);
    assert_eq!(r["kind"], "counterexample", "{s}");
    let places: Vec<&Value> = r["check"]["diverging"].as_array().unwrap().iter().map(|d| &d["place"]).collect();
    assert!(places.contains(&&serde_json::json!(["m.O.s", "m.S.p2"])), "{r}");
    // 同じ値を書けば成り立つ。消した m.S.p を、読んでいない名前として沈黙しない。
    let (s, r) = below_case("below-removed-named-same", &atoms, &plan.replace("m.b()", "m.a()"));
    assert_eq!(r["outcome"], "holds", "{s}");
}

#[test]
fn an_external_name_under_a_type_is_not_a_field_below() {
    // m.S を読んであり、m.S.p が payment-info。別の操作が m.S.save(resolves が外部を指す)を呼ぶ。
    let atoms = format!(
        "{O_S}{S_P}{}{F_WRITES_A}",
        r#"{"kind": "defines", "subject": "m.g", "value": "operation", "params": {}, "at": "m.py:7@blob:aaaaaaa"}
{"kind": "calls", "subject": "m.g", "object": "m.S.save", "at": "m.py:8@blob:aaaaaaa"}
{"kind": "resolves", "subject": "m.S.save", "object": "external:django", "at": "m.py:1@blob:aaaaaaa"}
"#
    );
    let (s, r) = below_case("below-external-member", &atoms, PLAN_WRITES_B);
    assert_eq!(r["kind"], "counterexample", "{s}");
}

#[test]
fn a_counterexample_below_is_not_hidden_by_a_sibling_field_not_read() {
    // m.S は a(型 m.Z、定義も resolves もない)と p(payment-info)を持つ。o.s の値が違えば、[o.s, S.p] で反例は決まる。
    let atoms = format!(
        "{O_S}{S_P}{}{F_WRITES_A}",
        r#"{"kind": "defines", "subject": "m.S.a", "value": "field", "type": "m.Z", "at": "m.py:5@blob:aaaaaaa"}
"#
    );
    let (s, r) = below_case("below-sibling-differs", &atoms, PLAN_WRITES_B);
    let places: Vec<Value> = r["check"]["diverging"].as_array().into_iter().flatten().map(|x| x["place"].clone()).collect();
    assert_eq!(places, vec![serde_json::json!(["m.O.s", "m.S.p"])], "{s}\n{r}");
    let (s, r) = below_case("below-sibling-same", &atoms, &PLAN_WRITES_B.replace("m.b()", "m.a()"));
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unread")), "{s}");
    assert!(s["next"].as_array().unwrap().iter().any(|n| n["element"] == "m.Z"), "{s}");
}

#[test]
fn a_counterexample_below_is_not_hidden_by_a_recursive_type() {
    // N.next の型は N。N.v は payment-info を持つ。o.n の値が違えば、[o.n, N.v] で反例は決まる。
    let atoms = r#"{"kind": "defines", "subject": "m.O", "value": "type", "at": "m.py:1@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.O.n", "value": "field", "type": "m.N", "at": "m.py:2@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.N", "value": "type", "at": "m.py:3@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.N.next", "value": "field", "type": "m.N", "at": "m.py:4@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.N.v", "value": "field", "type": "int", "at": "m.py:5@blob:aaaaaaa"}
{"kind": "meaning", "subject": "m.N.v", "meaning": "payment-info", "uses": ["m.py:10@blob:aaaaaaa"], "at": "m.py:5@blob:aaaaaaa"}
"#;
    let f = F_WRITES_A.replace("m.O.s", "m.O.n");
    let (s, r) = below_case("below-recursive-differs", &format!("{atoms}{f}"), &PLAN_WRITES_B.replace("m.O.s", "m.O.n"));
    let places: Vec<Value> = r["check"]["diverging"].as_array().into_iter().flatten().map(|x| x["place"].clone()).collect();
    assert!(places.contains(&serde_json::json!(["m.O.n", "m.N.v"])), "{s}\n{r}");
}

/// m.py(構造と payment-info を読んだ)と s.py(構造だけを読んだ)の観測と候補で `plan check` し、サマリと m.f の結果(反例なら詳細)を返す。
fn two_sources_case(name: &str, m: &str, s_py: &str, plan: &str) -> (Value, Value) {
    let repo = Repo::new(name);
    repo.write(".archsig/law/m.law", &LAW.replace("\"shop/**\"", "\"*.py\""));
    repo.map(
        "m.py",
        &format!(
            "{}{m}",
            r#"{"kind": "observed", "subject": "m.py", "scope": "structure", "at": "m.py@blob:aaaaaaa"}
{"kind": "resolves", "subject": "int", "object": "external:builtins", "at": "m.py:1@blob:aaaaaaa"}
{"kind": "observed", "subject": "m.py", "scope": "meaning:payment-info", "at": "m.py@blob:aaaaaaa"}
"#
        ),
    );
    repo.map(
        "s.py",
        &format!(
            "{}{s_py}",
            r#"{"kind": "observed", "subject": "s.py", "scope": "structure", "at": "s.py@blob:bbbbbbb"}
{"kind": "resolves", "subject": "int", "object": "external:builtins", "at": "s.py:1@blob:bbbbbbb"}
"#
        ),
    );
    repo.write(".archsig/plans/p/plan.jsonl", plan);
    let s = repo.run(&["plan", "check", "p"]);
    let r = result(&s, "m.f").clone();
    let r = if r["outcome"] == "fails" { repo.run(&["show", r["id"].as_str().unwrap()]) } else { r };
    (s, r)
}

/// m.py の観測。m.O.s の型 s.S は s.py にある。
const REDEFINE_M: &str = r#"{"kind": "defines", "subject": "m.O", "value": "type", "at": "m.py:1@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.O.s", "value": "field", "type": "s.S", "at": "m.py:2@blob:aaaaaaa"}
{"kind": "resolves", "subject": "s.S", "object": "s.py", "at": "m.py:1@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.f", "value": "operation", "params": {"o": "m.O"}, "at": "m.py:9@blob:aaaaaaa"}
"#;

/// s.py の観測(構造だけ)。
const REDEFINE_S: &str = r#"{"kind": "defines", "subject": "s.S", "value": "type", "at": "s.py:2@blob:bbbbbbb"}
{"kind": "defines", "subject": "s.S.p", "value": "field", "type": "int", "at": "s.py:3@blob:bbbbbbb"}
"#;

#[test]
fn a_field_the_plan_defines_again_is_unread_when_its_meaning_before_was_not_read() {
    // m.S.p は s.py にあり、s.py の payment-info は読んでいない。候補は m.S.p を同じ形で定義し直し、o.s に書く。
    // 候補のフィールドの意味は、元の m.S.p の意味を移したものなので決まらない(設計 §3.6 の4、§5.1)。
    let (m, s_py) = (REDEFINE_M, REDEFINE_S);
    let plan = |redefine: &str| {
        format!(
            "{}{redefine}",
            r#"{"kind": "defines", "subject": "m.f", "value": "operation", "params": {"o": "m.O"}, "file": "m.py", "at": "plan:p"}
{"kind": "writes", "subject": "m.f", "object": "m.O.s", "value": "m.b()", "at": "plan:p"}
"#
        )
    };
    let redefine = r#"{"kind": "defines", "subject": "s.S.p", "value": "field", "type": "int", "file": "s.py", "at": "plan:p"}
"#;
    let (s, r) = two_sources_case("below-redefined-field", m, s_py, &plan(redefine));
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unread")), "{s}");
    assert!(s["next"].as_array().unwrap().iter().any(|n| n["read"] == "s.py" && n["scope"] == "meaning:payment-info"), "{s}");
    // 定義し直さなくても同じく決まらない。
    let (s, r) = two_sources_case("below-plain-field", m, s_py, &plan(""));
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unread")), "{s}");
}

#[test]
fn a_field_the_plan_splits_into_a_new_type_is_unread_when_its_meaning_before_was_not_read() {
    let (m, s_py) = (REDEFINE_M, REDEFINE_S);
    // 新しい型 m.N に分けて、m.N.p を s.S.p の対応の行き先にしても、m.N.p の意味は決まらない。
    let split = r#"{"kind": "defines", "subject": "m.f", "value": "operation", "params": {"o": "m.O"}, "file": "m.py", "at": "plan:p"}
{"kind": "defines", "subject": "m.N", "value": "type", "file": "m.py", "at": "plan:p"}
{"kind": "defines", "subject": "m.N.p", "value": "field", "type": "int", "file": "m.py", "at": "plan:p"}
{"kind": "defines", "subject": "m.O.n", "value": "field", "type": "m.N", "file": "m.py", "at": "plan:p"}
{"kind": "corresponds", "subject": "s.S.p", "object": "m.N.p", "at": "plan:p"}
{"kind": "removes", "subject": "s.S.p", "at": "plan:p"}
{"kind": "writes", "subject": "m.f", "object": "m.O.n", "value": "m.b()", "at": "plan:p"}
"#;
    let (s, r) = two_sources_case("below-split-field", m, s_py, split);
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unread")), "{s}");
    assert!(s["next"].as_array().unwrap().iter().any(|n| n["read"] == "s.py" && n["scope"] == "meaning:payment-info"), "{s}");
}

#[test]
fn a_counterexample_below_is_not_hidden_by_a_field_named_but_not_read() {
    // m.S.p は payment-info を持つ。m.S.q は resolves で b.py を指して名指されているが、定義を読んでいない。
    // 沈黙は m.S.q の場所だけのもので、o.s の値が違えば [o.s, S.p] で反例は決まる。
    let atoms = format!(
        "{O_S}{S_P}{}{F_WRITES_A}",
        r#"{"kind": "resolves", "subject": "m.S.q", "object": "b.py", "at": "m.py:5@blob:aaaaaaa"}
"#
    );
    let (s, r) = below_case("below-named-differs", &atoms, PLAN_WRITES_B);
    let places: Vec<Value> = r["check"]["diverging"].as_array().into_iter().flatten().map(|x| x["place"].clone()).collect();
    assert_eq!(places, vec![serde_json::json!(["m.O.s", "m.S.p"])], "{s}\n{r}");
    let (s, r) = below_case("below-named-same", &atoms, &PLAN_WRITES_B.replace("m.b()", "m.a()"));
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unread")), "{s}");
    assert!(s["next"].as_array().unwrap().iter().any(|n| n["read"] == "b.py"), "{s}");
}

#[test]
fn a_counterexample_below_is_not_hidden_by_an_ambiguous_field() {
    // m.S.a は field と operation の二つの defines を持つ(曖昧)。m.S.p は payment-info を持つ。
    let atoms = format!(
        "{O_S}{S_P}{}{F_WRITES_A}",
        r#"{"kind": "defines", "subject": "m.S.a", "value": "field", "type": "int", "at": "m.py:5@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.S.a", "value": "operation", "params": {}, "at": "m.py:6@blob:aaaaaaa"}
"#
    );
    let (s, r) = below_case("below-ambiguous-differs", &atoms, PLAN_WRITES_B);
    let places: Vec<Value> = r["check"]["diverging"].as_array().into_iter().flatten().map(|x| x["place"].clone()).collect();
    assert_eq!(places, vec![serde_json::json!(["m.O.s", "m.S.p"])], "{s}\n{r}");
    let (s, r) = below_case("below-ambiguous-same", &atoms, &PLAN_WRITES_B.replace("m.b()", "m.a()"));
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unresolved")), "{s}");
}

#[test]
fn a_source_path_is_not_a_field_below() {
    // ソース m.S.py の観測の subject は、型 m.S のフィールドの名前ではない。
    let atoms = format!(
        "{}{O_S}{S_P}{F_WRITES_A}",
        r#"{"kind": "observed", "subject": "m.S.py", "scope": "structure", "at": "m.S.py@blob:ccccccc"}
"#
    );
    let (s, r) = below_case("below-source-path", &atoms, &PLAN_WRITES_B.replace("m.b()", "m.a()"));
    assert_eq!(r["outcome"], "holds", "{s}");
}

#[test]
fn a_field_the_plan_defines_again_and_writes_directly_is_unread() {
    // 候補は s.S.p を定義し直し、via [m.O.s] で s.S.p に直接書く。s.py の payment-info は読んでいない。
    // 書き込みの場所の最後のフィールドの意味は、元の s.S.p の意味を移したものなので決まらない。
    let plan = r#"{"kind": "defines", "subject": "m.f", "value": "operation", "params": {"o": "m.O"}, "file": "m.py", "at": "plan:p"}
{"kind": "defines", "subject": "s.S.p", "value": "field", "type": "int", "file": "s.py", "at": "plan:p"}
{"kind": "writes", "subject": "m.f", "via": ["m.O.s"], "object": "s.S.p", "value": "m.b()", "at": "plan:p"}
"#;
    let (s, r) = two_sources_case("direct-redefined-field", REDEFINE_M, REDEFINE_S, plan);
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unread")), "{s}");
    assert!(s["next"].as_array().unwrap().iter().any(|n| n["read"] == "s.py" && n["scope"] == "meaning:payment-info"), "{s}");
}

/// 構造の書き戻し(#5174)の入力。m.O.t は payment-info を持つ。m.O.n は意味を持たない。
const T_ATOMS: &str = r#"{"kind": "defines", "subject": "m.O", "value": "type", "at": "m.py:1@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.O.t", "value": "field", "type": "int", "at": "m.py:2@blob:aaaaaaa"}
{"kind": "meaning", "subject": "m.O.t", "meaning": "payment-info", "uses": ["m.py:10@blob:aaaaaaa"], "at": "m.py:2@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.O.n", "value": "field", "type": "int", "at": "m.py:3@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.f", "value": "operation", "params": {"o": "m.O"}, "at": "m.py:9@blob:aaaaaaa"}
"#;

/// 変更前の m.f の手順(行 10 から)と、候補の m.f の手順で `plan check` する。手順は (種類, object, value, when) の列。
fn t_case(name: &str, before: &[(&str, &str, &str, &str)], plan: &[(&str, &str, &str, &str)], extra: &str) -> (Value, Value) {
    let atom = |k: &str, o: &str, v: &str, w: &str, at: &str| {
        let mut a = serde_json::json!({"kind": k, "subject": "m.f", "object": o, "at": at});
        if !v.is_empty() {
            a["value"] = Value::String(v.to_string());
        }
        if k == "returns" {
            a.as_object_mut().unwrap().remove("object");
        }
        if !w.is_empty() {
            a["when"] = Value::String(w.to_string());
        }
        a.to_string() + "\n"
    };
    let mut m = format!("{T_ATOMS}{extra}");
    for (i, (k, o, v, w)) in before.iter().enumerate() {
        m.push_str(&atom(k, o, v, w, &format!("m.py:{}@blob:aaaaaaa", 10 + i)));
    }
    let mut p = String::from(r#"{"kind": "defines", "subject": "m.f", "value": "operation", "params": {"o": "m.O"}, "file": "m.py", "at": "plan:p"}
"#);
    for (k, o, v, w) in plan {
        p.push_str(&atom(k, o, v, w, "plan:p"));
    }
    below_case(name, &m, &p)
}

#[test]
fn a_name_without_dollar_is_read_as_a_constant() {
    let w = |v| [("writes", "m.O.t", v, "")];
    let (s, r) = t_case("const-same", &w("JP_CODE"), &w("JP_CODE"), "");
    assert_eq!(r["outcome"], "holds", "{s}");
    let (s, r) = t_case("const-dotted", &w("cfg.RATE"), &w("cfg.RATE"), "");
    assert_eq!(r["outcome"], "holds", "{s}");
    let (s, r) = t_case("const-string", &w("\"JP\""), &w("\"JP\""), "");
    assert_eq!(r["outcome"], "holds", "{s}");
    let (s, r) = t_case("const-negative", &w("-$o.n"), &w("-$o.n"), "");
    assert_eq!(r["outcome"], "holds", "{s}");
    let (s, r) = t_case("const-negative-differs", &w("-$o.n"), &w("$o.n"), "");
    assert_eq!(r["kind"], "counterexample", "{s}");
    // 定数は字句で比べる。名前の定数の値も、数の書き方の違いも知らないので、字句が違えば違う値である(第3章)。
    for (name, a, b) in [("const-name-and-value", "JP_CODE", "\"JP\""), ("const-number-forms", "1", "1.0")] {
        let (s, r) = t_case(name, &w(a), &w(b), "");
        assert_eq!(r["kind"], "counterexample", "{name}: {s}");
    }
}

#[test]
fn a_callee_resolved_to_a_read_source_without_its_definition_is_unresolved() {
    let extra = r#"{"kind": "resolves", "subject": "m.g", "object": "m.py", "at": "m.py:1@blob:aaaaaaa"}
"#;
    let steps = [("calls", "m.g", "", ""), ("writes", "m.O.t", "1", "")];
    let (s, r) = t_case("resolved-undefined", &steps, &steps, extra);
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unresolved")), "{s}");
    assert!(!s["next"].as_array().unwrap().iter().any(|n| n["decides"].as_array().unwrap().contains(&r["id"])), "次に読む所は付かない: {s}");
}

#[test]
fn an_unreadable_value_is_like_a_question_mark() {
    let (s, r) = t_case("unreadable-value", &[("writes", "m.O.t", "a ?? b", "")], &[("writes", "m.O.t", "1", "")], "");
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unresolved")), "{s}");
    assert!(s["next"].as_array().unwrap().iter().any(|n| n["read"] == "m.py" && n["scope"] == "structure"), "{s}");
}

#[test]
fn the_steps_after_a_return_are_done_only_where_it_did_not_return() {
    // 条件のない戻り値の後の書き込みは、どの分岐でも行わない。食い違う書き込みでも成り立つ。
    let (s, r) = t_case(
        "return-unconditional",
        &[("returns", "", "1", ""), ("writes", "m.O.t", "1", "")],
        &[("returns", "", "1", ""), ("writes", "m.O.t", "2", "")],
        "",
    );
    assert_eq!(r["outcome"], "holds", "{s}");
    // 条件付きの戻り値の後の書き込みは、戻らなかった分岐で行う。その分岐で食い違う。
    let (s, r) = t_case(
        "return-conditional",
        &[("returns", "", "1", "$o.n == 1"), ("writes", "m.O.t", "1", "")],
        &[("returns", "", "1", "$o.n == 1"), ("writes", "m.O.t", "2", "")],
        "",
    );
    assert_eq!(r["kind"], "counterexample", "{s}");
    // 戻り値の条件は、戻り値の時点の状態で読む。後で m.O.n を 1 に書いても、n が 1 でなかった分岐では戻らない。
    let (s, r) = t_case(
        "return-condition-at-return",
        &[("returns", "", "1", "$o.n == 1"), ("writes", "m.O.n", "1", ""), ("writes", "m.O.t", "5", "")],
        &[("returns", "", "1", "$o.n == 1"), ("writes", "m.O.n", "1", ""), ("writes", "m.O.t", "6", "")],
        "",
    );
    assert_eq!(r["kind"], "counterexample", "{s}");
    // 戻り値の条件を後の手順の時点で読み直すと、m.O.n を書き換えた後では答えが変わる。戻り値の時点で一度だけ読むので、
    // 戻らなかった分岐でだけ書く候補と同じになる。
    let (s, r) = t_case(
        "return-condition-read-once",
        &[("returns", "", "1", "$o.n == 1"), ("writes", "m.O.n", "$o.t", ""), ("writes", "m.O.t", "5", "")],
        &[("writes", "m.O.t", "5", "$o.n != 1"), ("writes", "m.O.n", "$o.t", "$o.n != 1")],
        "",
    );
    assert_eq!(r["outcome"], "holds", "{s}");
    // 戻った分岐では、後の書き込みを行わない。戻らなかった分岐でだけ書く候補と同じになる。
    let (s, r) = t_case(
        "return-conditional-same",
        &[("returns", "", "1", "$o.n == 1"), ("writes", "m.O.t", "1", "")],
        &[("writes", "m.O.t", "1", "$o.n != 1")],
        "",
    );
    assert_eq!(r["outcome"], "holds", "{s}");
    // 無条件に書く候補とは、戻った分岐(n が 1)で食い違う。
    let (s, r) = t_case(
        "return-conditional-returned-branch",
        &[("returns", "", "1", "$o.n == 1"), ("writes", "m.O.t", "1", "")],
        &[("writes", "m.O.t", "1", "")],
        "",
    );
    assert_eq!(r["kind"], "counterexample", "{s}");
    // 呼び出し先の戻り値は、呼び出し先の本体だけを終える。呼び出し元の後の書き込みは行う。
    let callee = r#"{"kind": "defines", "subject": "m.g", "value": "operation", "params": {}, "at": "m.py:20@blob:aaaaaaa"}
{"kind": "returns", "subject": "m.g", "value": "1", "at": "m.py:21@blob:aaaaaaa"}
"#;
    let (s, r) = t_case(
        "return-in-callee",
        &[("calls", "m.g", "", ""), ("writes", "m.O.t", "1", "")],
        &[("calls", "m.g", "", ""), ("writes", "m.O.t", "2", "")],
        callee,
    );
    assert_eq!(r["kind"], "counterexample", "{s}");
}

#[test]
fn a_question_mark_anywhere_in_the_operation_is_silent() {
    // 意味を持たない m.O.n に ? を書く。m.O.t は 1 と 2 で食い違うが、操作の列を作らずに沈黙する。
    let (s, r) = t_case(
        "question-anywhere",
        &[("writes", "m.O.n", "?", ""), ("writes", "m.O.t", "1", "")],
        &[("writes", "m.O.n", "?", ""), ("writes", "m.O.t", "2", "")],
        "",
    );
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unresolved")), "{s}");
}

#[test]
fn the_step_limit_is_counted_before_a_call_is_unfolded() {
    // 手順の数は、呼び出しを展開する前に、それまでに並べた手順(呼び出しの手順を含む)で数える。
    let callee = r#"{"kind": "defines", "subject": "m.g", "value": "operation", "params": {}, "at": "m.py:5@blob:aaaaaaa"}
{"kind": "writes", "subject": "m.g", "object": "m.O.n", "value": "1", "at": "m.py:6@blob:aaaaaaa"}
{"kind": "writes", "subject": "m.g", "object": "m.O.n", "value": "2", "at": "m.py:7@blob:aaaaaaa"}
"#;
    let run = |name: &str, n: usize, call: bool| {
        let mut steps: Vec<(&str, &str, &str, &str)> = vec![("writes", "m.O.n", "1", ""); n];
        if call {
            steps.push(("calls", "m.g", "", ""));
        }
        steps.push(("writes", "m.O.t", "1", ""));
        let (s, r) = t_case(name, &steps, &steps, callee);
        (r["outcome"].as_str().map(str::to_string), r["reason"].as_str().map(str::to_string), s)
    };
    // 呼び出しのない本体は、手順の数にかかわらず上限にかからない。
    let (o, _, s) = run("steps-flat", STEP_LIMIT + 1, false);
    assert_eq!(o.as_deref(), Some("holds"), "{s}");
    // 上限より一つ少ない手順と呼び出しで、ちょうど上限。呼び出し先の 2 手順は、展開した後には数えない。
    let (o, _, s) = run("steps-call-at-limit", STEP_LIMIT - 1, true);
    assert_eq!(o.as_deref(), Some("holds"), "{s}");
    let (o, reason, s) = run("steps-call-over", STEP_LIMIT, true);
    assert_eq!((o.as_deref(), reason.as_deref()), (Some("silent"), Some("limit")), "{s}");
}

#[test]
fn and_splits_a_condition_and_or_and_not_and_do_not() {
    // 反例の分岐が持つ条件の数で確かめる。`and` は二つに分け、`or` と `not` の中の `and` は一つの条件にする。
    let branch = |name: &str, when: &'static str| {
        let w = |v| [("writes", "m.O.t", v, when)];
        let (s, r) = t_case(name, &w("1"), &w("2"), "");
        assert_eq!(r["kind"], "counterexample", "{s}");
        r["check"]["branch"].as_array().unwrap().len()
    };
    assert_eq!(branch("cond-and", "$o.n == 1 and $o.t == 2"), 2);
    assert_eq!(branch("cond-or", "$o.n == 1 or $o.n == 2"), 1);
    assert_eq!(branch("cond-not-and", "not ($o.n == 1 and $o.t == 2)"), 1);
    // 二重の `not` は外してから分ける。
    assert_eq!(branch("cond-not-not-and", "not not ($o.n == 1 and $o.t == 2)"), 2);
}

#[test]
fn a_return_value_is_not_compared() {
    let (s, r) = t_case(
        "return-not-compared",
        &[("returns", "", "1", ""), ("writes", "m.O.t", "1", "")],
        &[("returns", "", "2", ""), ("writes", "m.O.t", "1", "")],
        "",
    );
    assert_eq!(r["outcome"], "holds", "{s}");
}

#[test]
fn a_return_in_the_callee_does_not_end_the_callers_steps() {
    let callee = r#"{"kind": "defines", "subject": "m.g", "value": "operation", "params": {}, "at": "m.py:5@blob:aaaaaaa"}
{"kind": "returns", "subject": "m.g", "value": "1", "at": "m.py:6@blob:aaaaaaa"}
"#;
    let (s, r) = t_case(
        "callee-return",
        &[("calls", "m.g", "", ""), ("writes", "m.O.t", "1", "")],
        &[("calls", "m.g", "", ""), ("writes", "m.O.t", "2", "")],
        callee,
    );
    assert_eq!(r["kind"], "counterexample", "{s}");
}

#[test]
fn a_question_mark_or_an_unreadable_expression_anywhere_in_the_steps_is_silent() {
    let silent = |name: &str, steps: &[(&str, &str, &str, &str)], extra: &str| {
        let mut before = steps.to_vec();
        before.push(("writes", "m.O.t", "1", ""));
        let mut plan = steps.to_vec();
        plan.push(("writes", "m.O.t", "2", ""));
        let (s, r) = t_case(name, &before, &plan, extra);
        assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unresolved")), "{name}: {s}");
        s
    };
    silent("q-when", &[("writes", "m.O.n", "1", "?")], "");
    silent("q-sends-when", &[("sends", "channel:queue:q:item", "1", "?")], "");
    silent("q-returns-when", &[("returns", "", "1", "?")], "");
    let s = silent("unreadable-when", &[("writes", "m.O.n", "1", "$o.n ~ 1")], "");
    assert!(s["next"].as_array().unwrap().iter().any(|n| n["read"] == "m.py" && n["scope"] == "structure"), "{s}");
    silent("q-sends", &[("sends", "channel:queue:q:item", "?", "")], "");
    silent("q-returns", &[("returns", "", "?", "")], "");
    let callee = r#"{"kind": "defines", "subject": "m.g", "value": "operation", "params": {}, "at": "m.py:5@blob:aaaaaaa"}
{"kind": "writes", "subject": "m.g", "object": "m.O.n", "value": "?", "at": "m.py:6@blob:aaaaaaa"}
"#;
    silent("q-callee", &[("calls", "m.g", "", "")], callee);
    silent("q-call-when", &[("calls", "m.g", "", "?")], &callee.replace("\"?\"", "\"1\""));
}

#[test]
fn a_pass_to_an_argument_the_callee_does_not_have_is_unresolved() {
    let callee = r#"{"kind": "defines", "subject": "m.g", "value": "operation", "params": {"x": "int"}, "at": "m.py:5@blob:aaaaaaa"}
{"kind": "writes", "subject": "m.g", "object": "m.O.t", "value": "$x", "at": "m.py:6@blob:aaaaaaa"}
"#;
    let run = |name: &str, to: &str, before: &str, after: &str| {
        let atoms = format!(
            "{T_ATOMS}{callee}{{\"kind\": \"calls\", \"subject\": \"m.f\", \"object\": \"m.g\", \"at\": \"m.py:10@blob:aaaaaaa\"}}\n{{\"kind\": \"passes\", \"subject\": \"m.f->m.g\", \"object\": \"{to}\", \"value\": \"{before}\", \"at\": \"m.py:10@blob:aaaaaaa\"}}\n"
        );
        let plan = format!(
            "{}{{\"kind\": \"passes\", \"subject\": \"m.f->m.g\", \"object\": \"m.g.$x\", \"value\": \"{after}\", \"at\": \"plan:p\"}}\n",
            r#"{"kind": "defines", "subject": "m.f", "value": "operation", "params": {"o": "m.O"}, "file": "m.py", "at": "plan:p"}
{"kind": "calls", "subject": "m.f", "object": "m.g", "at": "plan:p"}
"#
        );
        below_case(name, &atoms, &plan)
    };
    // 呼び出し先の引数に渡せば束なる。渡す値が違えば反例。
    let (s, r) = run("pass-right", "m.g.$x", "1", "2");
    assert_eq!(r["kind"], "counterexample", "{s}");
    // 呼び出し先の引数にない受け取り先(m.g.$y、名前だけの x)は、渡す値の行き先が決まらない。
    for to in ["m.g.$y", "x"] {
        let (s, r) = run(&format!("pass-wrong-{}", to.len()), to, "2", "2");
        assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unresolved")), "{to}: {s}");
        assert!(s["next"].as_array().unwrap().iter().any(|n| n["read"] == "m.py" && n["scope"] == "structure"), "{to}: {s}");
    }
}

#[test]
fn an_element_defined_without_a_kind_is_unresolved() {
    // 変更前の m.f の defines に value がない。書き込みは 1 から 2 に変わる。
    let atoms = r#"{"kind": "defines", "subject": "m.O", "value": "type", "at": "m.py:1@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.O.t", "value": "field", "type": "int", "at": "m.py:2@blob:aaaaaaa"}
{"kind": "meaning", "subject": "m.O.t", "meaning": "payment-info", "uses": ["m.py:10@blob:aaaaaaa"], "at": "m.py:2@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.f", "params": {"o": "m.O"}, "at": "m.py:9@blob:aaaaaaa"}
{"kind": "writes", "subject": "m.f", "object": "m.O.t", "value": "1", "at": "m.py:10@blob:aaaaaaa"}
"#;
    let plan = r#"{"kind": "defines", "subject": "m.f", "value": "operation", "params": {"o": "m.O"}, "file": "m.py", "at": "plan:p"}
{"kind": "writes", "subject": "m.f", "object": "m.O.t", "value": "2", "at": "plan:p"}
"#;
    let (s, r) = below_case("defines-without-value", atoms, plan);
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unresolved")), "{s}");
    // 引数の型 m.O の defines に value がなければ、$o.n の場所は決まらない。
    let (s, r) = t_case(
        "type-without-value",
        &[("writes", "m.O.t", "$o.n", "")],
        &[("writes", "m.O.t", "$o.n", "")],
        "",
    );
    assert_eq!(r["outcome"], "holds", "対照: {s}");
    let typeless = T_ATOMS.replace(r#"{"kind": "defines", "subject": "m.O", "value": "type","#, r#"{"kind": "defines", "subject": "m.O","#);
    let (s, r) = below_case(
        "type-without-value-q",
        &format!("{typeless}{}", r#"{"kind": "writes", "subject": "m.f", "object": "m.O.t", "value": "$o.n", "at": "m.py:10@blob:aaaaaaa"}
"#),
        r#"{"kind": "defines", "subject": "m.f", "value": "operation", "params": {"o": "m.O"}, "file": "m.py", "at": "plan:p"}
{"kind": "writes", "subject": "m.f", "object": "m.O.t", "value": "$o.n", "at": "plan:p"}
"#,
    );
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unresolved")), "{s}");
    // 書いたフィールドの型 m.S の、value のないフィールド m.S.p(payment-info)は、型をたどるときも決まらない。
    let fieldless = format!("{O_S}{}{F_WRITES_A}", S_P.replace(r#""subject": "m.S.p", "value": "field","#, r#""subject": "m.S.p","#));
    let (s, r) = below_case("field-without-value-below", &fieldless, PLAN_WRITES_B);
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unresolved")), "{s}");
}

#[test]
fn a_resolves_recorded_with_dot_slash_is_read_once_its_source_is_read() {
    // record が resolves の object を m/b.py にそろえるので、m/b.py を読めば呼び出し先の定義が読める。
    let repo = Repo::new("resolves-path");
    repo.write(".archsig/law/m.law", &LAW.replace("\"shop/**\"", "\"m/*.py\""));
    repo.write("m/a.py", "# a\n");
    repo.write("m/b.py", "# b\n");
    repo.write(
        "in.jsonl",
        r#"{"kind": "observed", "subject": "m/a.py", "scope": "structure", "at": "m/a.py"}
{"kind": "observed", "subject": "m/a.py", "scope": "meaning:payment-info", "at": "m/a.py"}
{"kind": "resolves", "subject": "int", "object": "external:builtins", "at": "m/a.py:1"}
{"kind": "resolves", "subject": "m.g", "object": "./m/b.py", "at": "m/a.py:1"}
{"kind": "defines", "subject": "m.O", "value": "type", "at": "m/a.py:2"}
{"kind": "defines", "subject": "m.O.t", "value": "field", "type": "int", "at": "m/a.py:3"}
{"kind": "meaning", "subject": "m.O.t", "meaning": "payment-info", "uses": ["m/a.py:10"], "at": "m/a.py:3"}
{"kind": "defines", "subject": "m.f", "value": "operation", "params": {"o": "m.O"}, "at": "m/a.py:9"}
{"kind": "calls", "subject": "m.f", "object": "m.g", "at": "m/a.py:10"}
{"kind": "writes", "subject": "m.f", "object": "m.O.t", "value": "1", "at": "m/a.py:11"}
{"kind": "observed", "subject": "m/b.py", "scope": "structure", "at": "m/b.py"}
{"kind": "defines", "subject": "m.g", "value": "operation", "params": {}, "at": "m/b.py:1"}
"#,
    );
    let observed_b = r#"{"kind": "observed", "subject": "m/b.py", "scope": "structure", "at": "m/b.py"}
{"kind": "defines", "subject": "m.g", "value": "operation", "params": {}, "at": "m/b.py:1"}
"#;
    // m/b.py を読む前は、次に読む所はそろえたパスの m/b.py である。
    repo.write("in.jsonl", &std::fs::read_to_string(repo.dir.join("in.jsonl")).unwrap().replace(observed_b, ""));
    repo.run(&["record", "in.jsonl"]);
    repo.write(
        ".archsig/plans/p/plan.jsonl",
        r#"{"kind": "defines", "subject": "m.f", "value": "operation", "params": {"o": "m.O"}, "file": "m/a.py", "at": "plan:p"}
{"kind": "calls", "subject": "m.f", "object": "m.g", "at": "plan:p"}
{"kind": "writes", "subject": "m.f", "object": "m.O.t", "value": "2", "at": "plan:p"}
"#,
    );
    let s = repo.run(&["plan", "check", "p"]);
    let r = result(&s, "m.f");
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unread")), "{s}");
    assert!(s["next"].as_array().unwrap().iter().any(|n| n["read"] == "m/b.py"), "{s}");
    assert!(!s["next"].as_array().unwrap().iter().any(|n| n["read"] == "./m/b.py"), "{s}");
    // m/b.py を読めば、呼び出し先の定義が読め、反例が決まる。
    repo.write("in.jsonl", observed_b);
    repo.run(&["record", "in.jsonl"]);
    let s = repo.run(&["plan", "check", "p"]);
    let r = result(&s, "m.f");
    assert_eq!((r["outcome"].as_str(), r["kind"].as_str()), (Some("fails"), Some("counterexample")), "{s}");
}

#[test]
fn an_operation_defined_without_a_kind_that_names_a_removed_type_is_unresolved() {
    // m.x は引数の型に m.T を持つ。候補が m.T を消す。changes keep の Law では、対応の組を比べないので、
    // 消える要素を名指す操作の結論だけが出る。value のない m.x は、種類の違う defines を持つ要素と同じく沈黙する。
    let run = |name: &str, defines: &str| {
        let repo = Repo::new(name);
        repo.write(".archsig/law/m.law", &KEEP.replace("\"shop/**\"", "\"m.py\""));
        repo.map(
            "m.py",
            &format!(
                "{}{defines}\n",
                r#"{"kind": "observed", "subject": "m.py", "scope": "structure", "at": "m.py@blob:aaaaaaa"}
{"kind": "observed", "subject": "m.py", "scope": "meaning:payment-info", "at": "m.py@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.T", "value": "type", "at": "m.py:1@blob:aaaaaaa"}
"#
            ),
        );
        repo.write(".archsig/plans/p/plan.jsonl", r#"{"kind": "removes", "subject": "m.T", "at": "plan:p"}
"#);
        repo.run(&["plan", "check", "p"])
    };
    let s = run("removed-param-op", r#"{"kind": "defines", "subject": "m.x", "value": "operation", "params": {"q": "m.T"}, "at": "m.py:2@blob:aaaaaaa"}"#);
    assert_eq!((result(&s, "m.x")["outcome"].as_str(), result(&s, "m.x")["kind"].as_str()), (Some("fails"), Some("missing")), "対照: {s}");
    let s = run("removed-param-valueless", r#"{"kind": "defines", "subject": "m.x", "params": {"q": "m.T"}, "at": "m.py:2@blob:aaaaaaa"}"#);
    assert_eq!((result(&s, "m.x")["outcome"].as_str(), result(&s, "m.x")["reason"].as_str()), (Some("silent"), Some("unresolved")), "{s}");
}

#[test]
fn an_argument_kept_through_an_operation_without_a_kind_is_unresolved() {
    // m.f の引数 x は payment-info を持つ。候補は m.f を消して m.g に対応させる。引数の対応は、操作どうしの対応から作る。
    // m.g が操作なら x の対応ができて holds。種類が決まらなければ(value がない)、対応があるかも決まらない。型なら missing。
    let law = r#"sources "m.py"

reading module = dir(depth: 2)

meaning payment-info on param
  "注文の支払いを特定する値。"

law payment-info-kept
  "決済情報は変更の後も残る。"
  about payment-info
  changes keep
"#;
    let run_with = |name: &str, f_value: &str, g_value: &str| {
        let repo = Repo::new(name);
        repo.write(".archsig/law/m.law", law);
        let map = r#"{"kind": "observed", "subject": "m.py", "scope": "structure", "at": "m.py@blob:aaaaaaa"}
{"kind": "observed", "subject": "m.py", "scope": "meaning:payment-info", "at": "m.py@blob:aaaaaaa"}
{"kind": "resolves", "subject": "int", "object": "external:builtins", "at": "m.py:1@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.f", "#
            .to_string()
            + f_value
            + r#""params": {"x": "int"}, "at": "m.py:2@blob:aaaaaaa"}
{"kind": "meaning", "subject": "m.f.$x", "meaning": "payment-info", "uses": ["m.py:3@blob:aaaaaaa"], "at": "m.py:2@blob:aaaaaaa"}
"#;
        repo.map("m.py", &map);
        repo.write(
            ".archsig/plans/p/plan.jsonl",
            &format!(
                "{{\"kind\": \"removes\", \"subject\": \"m.f\", \"at\": \"plan:p\"}}\n{{\"kind\": \"defines\", \"subject\": \"m.g\", {g_value}\"params\": {{\"x\": \"int\"}}, \"file\": \"m.py\", \"at\": \"plan:p\"}}\n{{\"kind\": \"corresponds\", \"subject\": \"m.f\", \"object\": \"m.g\", \"at\": \"plan:p\"}}\n"
            ),
        );
        repo.run(&["plan", "check", "p"])
    };
    let run = |name: &str, g_value: &str| run_with(name, r#""value": "operation", "#, g_value);
    let s = run("keep-op", r#""value": "operation", "#);
    assert_eq!(result(&s, "payment-info")["outcome"], "holds", "{s}");
    let s = run("keep-type", r#""value": "type", "#);
    assert_eq!((result(&s, "m.f.$x")["outcome"].as_str(), result(&s, "m.f.$x")["kind"].as_str()), (Some("fails"), Some("missing")), "{s}");
    let s = run("keep-valueless", "");
    assert_eq!((result(&s, "m.f.$x")["outcome"].as_str(), result(&s, "m.f.$x")["reason"].as_str()), (Some("silent"), Some("unresolved")), "{s}");
    // 変更前の持ち主 m.f の種類が決まらなくても、引数の対応があるかは決まらない。
    let s = run_with("keep-owner-valueless", "", r#""value": "operation", "#);
    assert_eq!((result(&s, "m.f.$x")["outcome"].as_str(), result(&s, "m.f.$x")["reason"].as_str()), (Some("silent"), Some("unresolved")), "{s}");
}

#[test]
fn a_long_expression_is_limit() {
    // 字句の数が上限を超える式は値を求めず、limit で沈黙する。深い入れ子でもプロセスは落ちない。
    // 上限は ArchSig の側の限界なので、ソースを読み直す所は返さない。
    let nested = format!("{}1{}", "(".repeat(10_000), ")".repeat(10_000));
    let negated = format!("{}1", "-".repeat(10_000));
    let long_sum = vec!["1"; 10_000].join(" + ");
    for (name, v) in [("long-nested", nested.as_str()), ("long-negated", negated.as_str()), ("long-sum", long_sum.as_str())] {
        // value に書いても、when に書いても同じ。
        for (at, steps) in [("value", [("writes", "m.O.t", v, "")]), ("when", [("writes", "m.O.t", "1", v)])] {
            let (s, r) = t_case(&format!("{name}-{at}"), &steps, &[("writes", "m.O.t", "1", "")], "");
            assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("limit")), "{name} {at}: {s}");
            assert!(!s["next"].as_array().unwrap().iter().any(|n| n["decides"].as_array().unwrap().contains(&r["id"])), "{name} {at}: {s}");
        }
    }
    // 上限より短い式は読む。上限の近くまで入れ子にしても落ちない。
    let deep = format!("{}1{}", "(".repeat(499), ")".repeat(499));
    let (s, r) = t_case("deep-within", &[("writes", "m.O.t", deep.as_str(), "")], &[("writes", "m.O.t", "1", "")], "");
    assert_eq!(r["outcome"], "holds", "{s}");
    let short_sum = vec!["1"; 400].join(" + ");
    let (s, r) = t_case("short-sum", &[("writes", "m.O.t", short_sum.as_str(), "")], &[("writes", "m.O.t", short_sum.as_str(), "")], "");
    assert_eq!(r["outcome"], "holds", "{s}");
}

#[test]
fn a_value_that_grows_beyond_the_term_limit_is_limit() {
    // $o.t + 1 を重ねて書くと、値の項が書き込みのたびに大きくなる。上限を超えれば limit。
    let run = |name: &str, n: usize| {
        let steps: Vec<(&str, &str, &str, &str)> = vec![("writes", "m.O.t", "$o.t + 1", ""); n];
        let (s, r) = t_case(name, &steps, &steps, "");
        (r["outcome"].as_str().map(str::to_string), r["reason"].as_str().map(str::to_string), s)
    };
    let (o, _, s) = run("grow-small", 100);
    assert_eq!(o.as_deref(), Some("holds"), "{s}");
    let (o, reason, s) = run("grow-large", 5_000);
    assert_eq!((o.as_deref(), reason.as_deref()), (Some("silent"), Some("limit")), "{s}");
    // 形をそろえると節が増える。1 != 1 を and で 250 個つなぐと、そろえる前は 999 節、そろえた後は 1,249 節。
    let ne = vec!["1 != 1"; 250].join(" and ");
    let (s, r) = t_case("grow-normalized", &[("writes", "m.O.t", ne.as_str(), "")], &[("writes", "m.O.t", ne.as_str(), "")], "");
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("limit")), "{s}");
    // 形をそろえる前にも数える。not を 996 個重ねた値は、そろえる前は 1,005 節で上限を超え、そろえると 9 節に縮む。
    let nots = format!("{}$o.t", "not ".repeat(996));
    let steps = [("writes", "m.O.t", "1 + 1 + 1 + 1 + 1", ""), ("writes", "m.O.t", nots.as_str(), "")];
    let (s, r) = t_case("shrink-normalized", &steps, &steps, "");
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("limit")), "{s}");
}

#[test]
fn a_long_expression_still_names_what_it_mentions() {
    // 別の操作 m.h の長い式が、定義を読んでいない m.S.zz を名指す。名指しは字句から拾うので、
    // 型 m.S をたどる所は m.S.zz が分からないとして沈黙する(短い式と同じ)。
    let mention = |v: &str| {
        format!(
            "{O_S}{S_P}{}{{\"kind\": \"writes\", \"subject\": \"m.h\", \"object\": \"m.O.t\", \"value\": \"{v}\", \"at\": \"m.py:8@blob:aaaaaaa\"}}\n{F_WRITES_A}",
            r#"{"kind": "defines", "subject": "m.O.t", "value": "field", "type": "int", "at": "m.py:5@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.h", "value": "operation", "params": {"o": "m.O"}, "at": "m.py:7@blob:aaaaaaa"}
"#
        )
    };
    let long = format!("$o.s.zz{}", " + 1".repeat(600));
    for (name, v) in [("mention-short", "$o.s.zz + 1".to_string()), ("mention-long", long)] {
        let (s, r) = below_case(name, &mention(&v), &PLAN_WRITES_B.replace("m.b()", "m.a()"));
        assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unread")), "{name}: {s}");
        assert!(s["next"].as_array().unwrap().iter().any(|n| n["element"] == "m.S.zz"), "{name}: {s}");
    }
}

#[test]
fn a_condition_or_a_passed_value_that_grows_beyond_the_term_limit_is_limit() {
    // 書き込みは小さいまま、条件と渡す値の項だけが上限を超える。
    // $x + $x を渡し続けると、渡す値の項は呼び出しの段ごとに倍になる。
    let mut extra = String::new();
    for i in 1..=12 {
        extra.push_str(&format!(
            "{{\"kind\": \"defines\", \"subject\": \"m.g{i}\", \"value\": \"operation\", \"params\": {{\"x\": \"int\"}}, \"at\": \"m.py:{}@blob:aaaaaaa\"}}\n",
            100 + i
        ));
        if i < 12 {
            extra.push_str(&format!(
                "{{\"kind\": \"calls\", \"subject\": \"m.g{i}\", \"object\": \"m.g{}\", \"at\": \"m.py:{}@blob:aaaaaaa\"}}\n{{\"kind\": \"passes\", \"subject\": \"m.g{i}->m.g{}\", \"object\": \"m.g{}.$x\", \"value\": \"$x + $x\", \"at\": \"m.py:{}@blob:aaaaaaa\"}}\n",
                i + 1, 200 + i, i + 1, i + 1, 200 + i
            ));
        }
    }
    extra.push_str("{\"kind\": \"passes\", \"subject\": \"m.f->m.g1\", \"object\": \"m.g1.$x\", \"value\": \"$o.n\", \"at\": \"m.py:10@blob:aaaaaaa\"}\n");
    let steps = [("calls", "m.g1", "", ""), ("writes", "m.O.t", "1", "")];
    let (s, r) = t_case("passes-grow", &steps, &steps, &extra);
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("limit")), "{s}");
    // 条件: $o.n を $o.n + $o.n で 8 回重ねると、値の項は 511 節で上限の内側。
    // 条件 $o.n == $o.n で二つ並べると 1,023 節になり、条件で初めて上限を超える。
    let mut steps: Vec<(&str, &str, &str, &str)> = vec![("writes", "m.O.n", "$o.n + $o.n", ""); 8];
    steps.push(("writes", "m.O.t", "1", ""));
    let (s, r) = t_case("when-within", &steps, &steps, "");
    assert_eq!(r["outcome"], "holds", "書き込みは上限の内側: {s}");
    steps.pop();
    steps.push(("writes", "m.O.t", "1", "$o.n == $o.n"));
    let (s, r) = t_case("when-grow", &steps, &steps, "");
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("limit")), "{s}");
    // 条件と渡す値も、形をそろえた後に数える。1 != 1 を and で 250 個つなぐと、そろえた後に 1,249 節になる。
    let ne = vec!["1 != 1"; 250].join(" and ");
    let steps = [("writes", "m.O.t", "1", ne.as_str())];
    let (s, r) = t_case("when-grow-normalized", &steps, &steps, "");
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("limit")), "{s}");
    let extra = format!(
        "{{\"kind\": \"defines\", \"subject\": \"m.g1\", \"value\": \"operation\", \"params\": {{\"x\": \"int\"}}, \"at\": \"m.py:101@blob:aaaaaaa\"}}\n{{\"kind\": \"passes\", \"subject\": \"m.f->m.g1\", \"object\": \"m.g1.$x\", \"value\": \"{ne}\", \"at\": \"m.py:10@blob:aaaaaaa\"}}\n"
    );
    let steps = [("calls", "m.g1", "", ""), ("writes", "m.O.t", "1", "")];
    let (s, r) = t_case("passes-grow-normalized", &steps, &steps, &extra);
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("limit")), "{s}");
}

#[test]
fn a_long_expression_does_not_decide_whether_a_removed_element_is_used() {
    // m.j の式が長いと、構文として読めるかを確かめていないので、消える m.U.a を使うかは決まらない。
    // 字句から拾う名前が m.U.a に届いても届かなくても、結論を落とさず limit で沈黙する。
    let atoms = r#"{"kind": "defines", "subject": "m.T", "value": "type", "at": "m.py:1@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.T.q", "value": "field", "type": "m.U", "at": "m.py:2@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.T.b", "value": "field", "type": "int", "at": "m.py:3@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.U", "value": "type", "at": "m.py:4@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.U.a", "value": "field", "type": "int", "at": "m.py:5@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.j", "value": "operation", "params": {"o": "m.T"}, "at": "m.py:6@blob:aaaaaaa"}
"#;
    let run = |name: &str, v: &str| {
        let m = format!("{atoms}{{\"kind\": \"writes\", \"subject\": \"m.j\", \"object\": \"m.T.b\", \"value\": \"{v}\", \"at\": \"m.py:7@blob:aaaaaaa\"}}\n");
        let repo = Repo::new(name);
        repo.write(".archsig/law/m.law", &LAW.replace("\"shop/**\"", "\"m.py\""));
        repo.map(
            "m.py",
            &format!(
                "{}{m}",
                r#"{"kind": "observed", "subject": "m.py", "scope": "structure", "at": "m.py@blob:aaaaaaa"}
{"kind": "resolves", "subject": "int", "object": "external:builtins", "at": "m.py:1@blob:aaaaaaa"}
{"kind": "observed", "subject": "m.py", "scope": "meaning:payment-info", "at": "m.py@blob:aaaaaaa"}
"#
            ),
        );
        repo.write(".archsig/plans/p/plan.jsonl", "{\"kind\": \"removes\", \"subject\": \"m.U.a\", \"at\": \"plan:p\"}\n");
        repo.run(&["plan", "check", "p"])
    };
    // 消える要素を使うかの結論は、Law なしの行に出る(changes commute の行とは別)。その行の理由と、それを決める次に読む所を返す。
    let removes_row = |s: &Value| {
        let r = s["results"].as_array().unwrap().iter().find(|r| r["subject"] == "m.j" && r["law"].is_null()).cloned().unwrap_or(Value::Null);
        let read = s["next"].as_array().unwrap().iter().any(|n| n["decides"].as_array().unwrap().contains(&r["id"]));
        (r["outcome"].as_str().map(str::to_string), r["reason"].as_str().map(str::to_string), read)
    };
    // 短い読めない式は ? と同じに沈黙し、ソースを読む所として返す(対照)。
    let s = run("removes-short-unreadable", "$o.q(1).a + 1");
    assert_eq!(removes_row(&s), (Some("silent".into()), Some("unresolved".into()), true), "{s}");
    let s = run("removes-short-names-unreadable", "$o.q.a ?? 1");
    assert_eq!(removes_row(&s), (Some("silent".into()), Some("unresolved".into()), true), "{s}");
    // 短い読める式が m.U.a を名指せば missing(対照)。
    let s = run("removes-short-names", "$o.q.a + 1");
    let r = s["results"].as_array().unwrap().iter().find(|r| r["subject"] == "m.j" && r["law"].is_null()).cloned().unwrap();
    assert_eq!((r["outcome"].as_str(), r["kind"].as_str()), (Some("fails"), Some("missing")), "{s}");
    // 字句の数が上限を超える式は、構文として読めても読めなくても、limit で沈黙し、読む所は付けない。
    // 上限を超えた式の中の ? や引数にない道も、読み直しても決まらないので limit にそろえる。
    // m.U.a を名指す長い式も、読めない(??)と短い式では沈黙するので、拾った名前で missing と決めない。
    let tail = " + 1".repeat(600);
    for (name, v) in [
        ("removes-long-unreadable", format!("$o.q(1).a{tail}")),
        ("removes-long-readable", format!("$o.b{tail}")),
        ("removes-long-question", format!("$o.b + ?{tail}")),
        ("removes-long-question-name", format!("$o.b + ?m.g(1){tail}")),
        ("removes-long-unknown-arg", format!("$zz.b{tail}")),
        ("removes-long-unknown-field", format!("$o.q.zz.w{tail}")),
        ("removes-long-names-readable", format!("$o.q.a{tail}")),
        ("removes-long-names-unreadable", format!("$o.q.a ?? 1{tail}")),
        ("removes-deep-question", format!("{}?{}", "(".repeat(600), ")".repeat(600))),
    ] {
        let s = run(name, &v);
        assert_eq!(removes_row(&s), (Some("silent".into()), Some("limit".into()), false), "{name}: {s}");
    }
}

#[test]
fn a_value_that_grows_through_calls_or_negation_is_limit() {
    // 値の項は、呼び出しや否定を重ねても大きくなる。上限を超えれば limit。
    let extra = r#"{"kind": "resolves", "subject": "m.g", "object": "external:lib", "at": "m.py:1@blob:aaaaaaa"}
"#;
    for (name, v) in [("grow-call", "m.g($o.t)"), ("grow-neg", "-$o.t")] {
        let steps: Vec<(&str, &str, &str, &str)> = vec![("writes", "m.O.t", v, ""); 3_000];
        let (s, r) = t_case(name, &steps, &steps, extra);
        assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("limit")), "{name}: {s}");
    }
}

#[test]
fn a_moved_write_place_whose_kind_is_not_known_does_not_hide_a_counterexample() {
    // 候補は書き込みの場所 m.T.a を、定義のない m.Z.a へ移す。移した場所が意味を持つかは決まらない(m.Z.a を読めば決まる)。
    // 意味を持つ m.T.k で二つの順番が食い違えば、その沈黙は結論に関わらず、反例を返す(設計 §5.4)。
    let run = |name: &str, k: &str| {
        let repo = Repo::new(name);
        repo.write(".archsig/law/m.law", &LAW.replace("\"shop/**\"", "\"m.py\""));
        repo.map("m.py", r#"{"kind": "observed", "subject": "m.py", "scope": "structure", "at": "m.py@blob:aaaaaaa"}
{"kind": "resolves", "subject": "int", "object": "external:builtins", "at": "m.py:1@blob:aaaaaaa"}
{"kind": "observed", "subject": "m.py", "scope": "meaning:payment-info", "at": "m.py@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.T", "value": "type", "at": "m.py:1@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.T.a", "value": "field", "type": "int", "at": "m.py:2@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.T.k", "value": "field", "type": "int", "at": "m.py:3@blob:aaaaaaa"}
{"kind": "meaning", "subject": "m.T.k", "meaning": "payment-info", "uses": ["m.py:7@blob:aaaaaaa"], "at": "m.py:3@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.f", "value": "operation", "params": {"o": "m.T"}, "at": "m.py:5@blob:aaaaaaa"}
{"kind": "writes", "subject": "m.f", "object": "m.T.a", "value": "1", "at": "m.py:6@blob:aaaaaaa"}
{"kind": "writes", "subject": "m.f", "object": "m.T.k", "value": "1", "at": "m.py:7@blob:aaaaaaa"}
"#);
        repo.write(".archsig/plans/p/plan.jsonl", &format!("{}\n{{\"kind\": \"writes\", \"subject\": \"m.f\", \"object\": \"m.T.k\", \"value\": \"{k}\", \"at\": \"plan:p\"}}\n", r#"{"kind": "corresponds", "subject": "m.T.a", "object": "m.Z.a", "at": "plan:p"}
{"kind": "defines", "subject": "m.f", "value": "operation", "params": {"o": "m.T"}, "file": "m.py", "at": "plan:p"}"#));
        repo.run(&["plan", "check", "p"])
    };
    let s = run("moved-place-same", "1");
    let r = result(&s, "m.f");
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unread")), "{s}");
    assert!(s["next"].as_array().unwrap().iter().any(|n| n["element"] == "m.Z.a"), "{s}");
    let s = run("moved-place-diverging", "2");
    assert_eq!(result(&s, "m.f")["kind"], "counterexample", "{s}");
}

#[test]
fn a_field_whose_meaning_was_not_read_and_is_not_written_does_not_silence() {
    // a.py の m.O.z は意味 Atom を持つが、a.py の payment-info は読んでいない。どちらの順番も m.O.z に書かないので、
    // 二つの順番の値は食い違わない。意味が決まらなくても結論に関わらないので、成り立つ。
    let repo = Repo::new("unsure-unwritten");
    repo.write(".archsig/law/m.law", &LAW.replace("\"shop/**\"", "\"*.py\""));
    repo.map("a.py", r#"{"kind": "observed", "subject": "a.py", "scope": "structure", "at": "a.py@blob:bbbbbbb"}
{"kind": "defines", "subject": "m.O", "value": "type", "at": "a.py:1@blob:bbbbbbb"}
{"kind": "defines", "subject": "m.O.z", "value": "field", "type": "int", "at": "a.py:2@blob:bbbbbbb"}
{"kind": "meaning", "subject": "m.O.z", "meaning": "payment-info", "uses": ["a.py:2@blob:bbbbbbb"], "at": "a.py:2@blob:bbbbbbb"}
"#);
    repo.map("m.py", SPLITTING);
    repo.write(
        ".archsig/plans/p/plan.jsonl",
        r#"{"kind": "defines", "subject": "m.f", "value": "operation", "params": {"o": "m.T"}, "file": "m.py", "at": "plan:p"}
{"kind": "writes", "subject": "m.f", "object": "m.T.p", "value": "$o.a", "at": "plan:p"}
"#,
    );
    let s = repo.run(&["plan", "check", "p"]);
    assert_eq!(result(&s, "m.f")["outcome"], "holds", "{s}");
}

#[test]
fn a_write_place_only_before_whose_meaning_was_not_read_is_silent() {
    // 変更前の m.f は m.O.x と m.O.k に書く。m.O.x を定義した a.py の payment-info は読んでいない。
    // 候補は m.O.x を m.O.y へ移し、m.f は m.O.k にだけ書く。変更前の書き込みの場所 m.O.x の意味が決まらない。
    let run = |name: &str, k: &str| {
        let repo = Repo::new(name);
        repo.write(".archsig/law/m.law", &LAW.replace("\"shop/**\"", "\"*.py\""));
        repo.map("a.py", r#"{"kind": "observed", "subject": "a.py", "scope": "structure", "at": "a.py@blob:bbbbbbb"}
{"kind": "defines", "subject": "m.O", "value": "type", "at": "a.py:1@blob:bbbbbbb"}
{"kind": "defines", "subject": "m.O.x", "value": "field", "type": "int", "at": "a.py:2@blob:bbbbbbb"}
"#);
        repo.map("m.py", r#"{"kind": "observed", "subject": "m.py", "scope": "structure", "at": "m.py@blob:aaaaaaa"}
{"kind": "resolves", "subject": "int", "object": "external:builtins", "at": "m.py:1@blob:aaaaaaa"}
{"kind": "observed", "subject": "m.py", "scope": "meaning:payment-info", "at": "m.py@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.O.k", "value": "field", "type": "int", "at": "m.py:2@blob:aaaaaaa"}
{"kind": "meaning", "subject": "m.O.k", "meaning": "payment-info", "uses": ["m.py:6@blob:aaaaaaa"], "at": "m.py:2@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.f", "value": "operation", "params": {"o": "m.O"}, "at": "m.py:4@blob:aaaaaaa"}
{"kind": "writes", "subject": "m.f", "object": "m.O.x", "value": "1", "at": "m.py:5@blob:aaaaaaa"}
{"kind": "writes", "subject": "m.f", "object": "m.O.k", "value": "1", "at": "m.py:6@blob:aaaaaaa"}
"#);
        repo.write(
            ".archsig/plans/p/plan.jsonl",
            &format!(
                "{}\n{{\"kind\": \"writes\", \"subject\": \"m.f\", \"object\": \"m.O.k\", \"value\": \"{k}\", \"at\": \"plan:p\"}}\n",
                r#"{"kind": "defines", "subject": "m.O.y", "value": "field", "type": "int", "file": "a.py", "at": "plan:p"}
{"kind": "corresponds", "subject": "m.O.x", "object": "m.O.y", "at": "plan:p"}
{"kind": "defines", "subject": "m.f", "value": "operation", "params": {"o": "m.O"}, "file": "m.py", "at": "plan:p"}"#
            ),
        );
        repo.run(&["plan", "check", "p"])
    };
    let s = run("before-place-same", "1");
    let r = result(&s, "m.f");
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unread")), "{s}");
    assert!(s["next"].as_array().unwrap().iter().any(|n| n["read"] == "a.py" && n["scope"] == "meaning:payment-info"), "{s}");
    let s = run("before-place-diverging", "2");
    assert_eq!(result(&s, "m.f")["kind"], "counterexample", "{s}");
}

/// SPLITTING に `extra` の Atom を足し、候補 `plan` で plan check した m.f の結果と出力。
fn splitting_with(name: &str, extra: &str, plan: &str) -> (Value, Value) {
    let repo = Repo::new(name);
    repo.write(".archsig/law/m.law", &LAW.replace("\"shop/**\"", "\"m.py\""));
    repo.map("m.py", &format!("{SPLITTING}{extra}"));
    repo.write(".archsig/plans/p/plan.jsonl", plan);
    let s = repo.run(&["plan", "check", "p"]);
    (result(&s, "m.f").clone(), s)
}

const REWRITE_F: &str = r#"{"kind": "defines", "subject": "m.f", "value": "operation", "params": {"o": "m.T"}, "file": "m.py", "at": "plan:p"}
{"kind": "writes", "subject": "m.f", "object": "m.T.p", "value": "$o.a", "at": "plan:p"}
"#;

#[test]
fn resolves_that_point_to_different_places_are_unresolved() {
    // m.f は外部の m.g を呼ぶ。m.g の resolves が二つあり、指す先が違えば、外部かどうかも決まらない。
    let call = r#"{"kind": "calls", "subject": "m.f", "object": "m.g", "at": "m.py:8@blob:ccccccc"}
{"kind": "resolves", "subject": "m.g", "object": "external:a", "at": "m.py:1@blob:ccccccc"}
"#;
    let plan = format!("{REWRITE_F}{}", r#"{"kind": "calls", "subject": "m.f", "object": "m.g", "at": "plan:p"}
"#);
    let second = |object: &str| format!("{call}{{\"kind\": \"resolves\", \"subject\": \"m.g\", \"object\": \"{object}\", \"at\": \"m.py:2@blob:ccccccc\"}}\n");
    let (r, s) = splitting_with("resolves-different", &second("external:b"), &plan);
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unresolved")), "{s}");
    // 指す先が同じ resolves が重なるのは、一つと同じ。
    let (r, s) = splitting_with("resolves-same", &second("external:a"), &plan);
    assert_eq!(r["outcome"], "holds", "{s}");
}

#[test]
fn an_element_defined_in_two_places_is_unresolved() {
    // m.T.p の defines が二か所にあると、どちらの定義か(型)が決まらない。
    let (r, s) = splitting_with(
        "defines-twice",
        r#"{"kind": "defines", "subject": "m.T.p", "value": "field", "type": "int", "at": "m.py:9@blob:ccccccc"}
"#,
        REWRITE_F,
    );
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unresolved")), "{s}");
    // 一か所なら計算する(対照)。
    let (r, s) = splitting_with("defines-once", "", REWRITE_F);
    assert_eq!(r["outcome"], "holds", "{s}");
}

#[test]
fn a_field_of_an_external_type_is_unresolved_without_a_place_to_read() {
    // m.T.q の型 x.Resp は外部の型。そのフィールド x.Resp.code に書くか、$o.q.code で読むと、フィールドが分からない。
    // 外部には読むソースがないので、読む所は返さない。x.Resp の解決が決まらないとき(resolves が二つ)も同じ。
    let resolves = |object: &str, line: u32| {
        format!("{{\"kind\": \"resolves\", \"subject\": \"x.Resp\", \"object\": \"{object}\", \"at\": \"m.py:{line}@blob:ccccccc\"}}\n")
    };
    let field = r#"{"kind": "defines", "subject": "m.T.q", "value": "field", "type": "x.Resp", "at": "m.py:9@blob:ccccccc"}
"#;
    for (types, extra) in [
        ("external", format!("{field}{}", resolves("external:x", 9))),
        ("two-externals", format!("{field}{}{}", resolves("external:x", 9), resolves("external:y", 10))),
        ("external-and-source", format!("{field}{}{}", resolves("external:x", 9), resolves("x/resp.py", 10))),
    ] {
        for (name, step) in [
            ("write", r#"{"kind": "writes", "subject": "m.f", "via": ["m.T.q"], "object": "x.Resp.code", "value": "1", "at": "plan:p"}"#),
            ("read", r#"{"kind": "writes", "subject": "m.f", "object": "m.T.b", "value": "$o.q.code", "at": "plan:p"}"#),
        ] {
            let name = format!("{types}-field-{name}");
            let (r, s) = splitting_with(&name, &extra, &format!("{REWRITE_F}{step}\n"));
            assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unresolved")), "{name}: {s}");
            assert!(!s["next"].as_array().unwrap().iter().any(|n| n["decides"].as_array().unwrap().contains(&r["id"])), "{name}: {s}");
        }
    }
}

#[test]
fn a_path_through_a_field_defined_in_two_places_does_not_decide_whether_a_removed_element_is_used() {
    // m.T.q の defines が二か所にあり、型が m.U1 と m.U2 で違う。m.j の $o.q.g が m.U2.g を使うかは決まらない。
    // 候補が m.U2.g を removes しても、m.j を missing と決めない。
    let repo = Repo::new("removes-through-twice-defined");
    repo.write(".archsig/law/m.law", &LAW.replace("\"shop/**\"", "\"m.py\""));
    repo.map(
        "m.py",
        r#"{"kind": "observed", "subject": "m.py", "scope": "structure", "at": "m.py@blob:aaaaaaa"}
{"kind": "resolves", "subject": "int", "object": "external:builtins", "at": "m.py:1@blob:aaaaaaa"}
{"kind": "observed", "subject": "m.py", "scope": "meaning:payment-info", "at": "m.py@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.T", "value": "type", "at": "m.py:1@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.T.q", "value": "field", "type": "m.U1", "at": "m.py:2@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.T.q", "value": "field", "type": "m.U2", "at": "m.py:3@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.T.b", "value": "field", "type": "int", "at": "m.py:4@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.U1", "value": "type", "at": "m.py:5@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.U1.g", "value": "field", "type": "int", "at": "m.py:6@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.U2", "value": "type", "at": "m.py:7@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.U2.g", "value": "field", "type": "int", "at": "m.py:8@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.j", "value": "operation", "params": {"o": "m.T"}, "at": "m.py:9@blob:aaaaaaa"}
{"kind": "writes", "subject": "m.j", "object": "m.T.b", "value": "$o.q.g", "at": "m.py:10@blob:aaaaaaa"}
"#,
    );
    repo.write(".archsig/plans/p/plan.jsonl", "{\"kind\": \"removes\", \"subject\": \"m.U2.g\", \"at\": \"plan:p\"}\n");
    let s = repo.run(&["plan", "check", "p"]);
    let rows: Vec<&Value> = s["results"].as_array().unwrap().iter().filter(|r| r["subject"] == "m.j").collect();
    assert!(!rows.is_empty(), "{s}");
    assert!(rows.iter().all(|r| r["outcome"] == "silent"), "{s}");
}

#[test]
fn a_callee_whose_resolution_is_undecided_does_not_decide_whether_a_removed_element_is_used() {
    // m.h は定義のない m.g を呼ぶ。m.g の resolves が二つあり指す先が違うと、m.g が外部か(消える要素を使わないか)は決まらない。
    let run = |name: &str, second: &str| {
        let repo = Repo::new(name);
        repo.write(".archsig/law/m.law", &LAW.replace("\"shop/**\"", "\"m.py\""));
        repo.map(
            "m.py",
            &format!(
                "{SPLITTING}{}{{\"kind\": \"resolves\", \"subject\": \"m.g\", \"object\": \"{second}\", \"at\": \"m.py:11@blob:ccccccc\"}}\n",
                r#"{"kind": "defines", "subject": "m.h", "value": "operation", "params": {"o": "m.T"}, "at": "m.py:9@blob:ccccccc"}
{"kind": "calls", "subject": "m.h", "object": "m.g", "at": "m.py:10@blob:ccccccc"}
{"kind": "resolves", "subject": "m.g", "object": "external:a", "at": "m.py:10@blob:ccccccc"}
"#
            ),
        );
        repo.write(".archsig/plans/p/plan.jsonl", "{\"kind\": \"removes\", \"subject\": \"m.T.b\", \"at\": \"plan:p\"}\n");
        repo.run(&["plan", "check", "p"])
    };
    let row = |s: &Value| s["results"].as_array().unwrap().iter().find(|r| r["subject"] == "removes").cloned();
    // 外部を指す resolves だけなら、外部の呼び出しとして扱う(対照)。
    let s = run("callee-external", "external:a");
    assert_eq!(row(&s), None, "{s}");
    for (name, second) in [("callee-two-externals", "external:b"), ("callee-external-and-source", "m2.py")] {
        let s = run(name, second);
        let r = row(&s).unwrap_or_else(|| panic!("{name}: {s}"));
        assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unresolved")), "{name}: {s}");
        // 解決が決まらない呼び出し先には読む所がないので、読む所のない項目を next に出さない。
        assert!(s["next"].as_array().unwrap().iter().all(|n| n.get("read").is_some() || n.get("element").is_some()), "{name}: {s}");
    }
}

#[test]
fn an_operation_defined_in_two_places_does_not_decide_whether_a_removed_element_is_used() {
    // m.j の defines が二か所にあり、引数 o の型が m.U1 と m.U2 で違う。m.j が m.U1 を使うかは決まらない。
    let run = |name: &str, body: &str| {
        let repo = Repo::new(name);
        repo.write(".archsig/law/m.law", &LAW.replace("\"shop/**\"", "\"m.py\""));
        repo.map(
            "m.py",
            &format!(
                "{}{body}",
                r#"{"kind": "observed", "subject": "m.py", "scope": "structure", "at": "m.py@blob:aaaaaaa"}
{"kind": "resolves", "subject": "int", "object": "external:builtins", "at": "m.py:1@blob:aaaaaaa"}
{"kind": "observed", "subject": "m.py", "scope": "meaning:payment-info", "at": "m.py@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.U1", "value": "type", "at": "m.py:1@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.U1.g", "value": "field", "type": "int", "at": "m.py:2@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.U2", "value": "type", "at": "m.py:3@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.U2.g", "value": "field", "type": "int", "at": "m.py:4@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.j", "value": "operation", "params": {"o": "m.U1"}, "at": "m.py:5@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.j", "value": "operation", "params": {"o": "m.U2"}, "at": "m.py:7@blob:aaaaaaa"}
"#
            ),
        );
        repo.write(".archsig/plans/p/plan.jsonl", "{\"kind\": \"removes\", \"subject\": \"m.U1\", \"at\": \"plan:p\"}\n");
        repo.run(&["plan", "check", "p"])
    };
    for (name, body) in [
        ("twice-defined-op-body", r#"{"kind": "writes", "subject": "m.j", "object": "m.U2.g", "value": "$o.g", "at": "m.py:8@blob:aaaaaaa"}
"#),
        ("twice-defined-op-no-body", ""),
    ] {
        let s = run(name, body);
        let r = s["results"].as_array().unwrap().iter().find(|r| r["subject"] == "m.j" && r["law"].is_null()).cloned();
        let r = r.unwrap_or_else(|| panic!("{name}: {s}"));
        assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unresolved")), "{name}: {s}");
    }
}

#[test]
fn an_operation_with_one_valueless_defines_still_decides_what_it_names() {
    // m.k の defines は一つで value がない。種類は決まらないが、引数の型は決まっているので、名指す要素も決まる。
    // m.k は消える m.T.b を名指さないので、消える要素を使うかの行は出さない。
    let (_, s) = splitting_with(
        "valueless-op-names",
        r#"{"kind": "defines", "subject": "m.k", "params": {"o": "m.T"}, "at": "m.py:9@blob:ccccccc"}
"#,
        "{\"kind\": \"removes\", \"subject\": \"m.T.b\", \"at\": \"plan:p\"}\n",
    );
    assert!(!s["results"].as_array().unwrap().iter().any(|r| r["subject"] == "m.k" && r["law"].is_null()), "{s}");
}

#[test]
fn a_type_whose_resolution_is_undecided_is_unresolved_when_traced() {
    // m.T.q の型 x.Resp の resolves が二つあり、指す先が違う。m.T.q に書くと、その型のフィールドをたどる所で、
    // 外部の型(意味を持つフィールドを持たない)とみなせないので、unresolved で沈黙する。
    let extra = r#"{"kind": "defines", "subject": "m.T.q", "value": "field", "type": "x.Resp", "at": "m.py:9@blob:ccccccc"}
{"kind": "resolves", "subject": "x.Resp", "object": "external:x", "at": "m.py:9@blob:ccccccc"}
{"kind": "resolves", "subject": "x.Resp", "object": "external:y", "at": "m.py:10@blob:ccccccc"}
"#;
    // 書くのは候補だけ。変更前の操作は m.T.q に書かないので、型をたどるのは変更後の側だけである。
    let write = r#"{"kind": "writes", "subject": "m.f", "object": "m.T.q", "value": "1", "at": "plan:p"}
"#;
    // 候補が x.Resp を定義し直しても、変更前の解決が決まらないので、元のフィールドは分からない。
    let redefine = r#"{"kind": "defines", "subject": "x.Resp", "value": "type", "file": "m.py", "at": "plan:p"}
"#;
    for (name, plan) in [("undecided-type-traced", format!("{REWRITE_F}{write}")), ("undecided-type-redefined", format!("{REWRITE_F}{write}{redefine}"))] {
        let (r, s) = splitting_with(name, extra, &plan);
        assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unresolved")), "{name}: {s}");
    }
}

#[test]
fn a_passed_value_that_depends_on_a_condition_other_than_the_call_is_unresolved() {
    // m.f は m.g を呼び、m.g は渡された x を意味を持つ m.O.t に書く。候補は m.f を同じ形で書き直す。
    // passes が呼び出しと違う when を持つか、一つの引数に値の違う passes が二つあれば、渡す値が一つに決まらない。
    let callee = r#"{"kind": "defines", "subject": "m.g", "value": "operation", "params": {"x": "int"}, "at": "m.py:20@blob:aaaaaaa"}
{"kind": "writes", "subject": "m.g", "object": "m.O.t", "value": "$x", "at": "m.py:21@blob:aaaaaaa"}
"#;
    let run = |name: &str, call_when: &str, passes: &[(&str, &str)], plan_passes: &[(&str, &str)]| {
        let atoms = |at: &str, passes: &[(&str, &str)]| {
            let mut out = String::new();
            let when = if call_when.is_empty() { String::new() } else { format!(", \"when\": \"{call_when}\"") };
            out.push_str(&format!("{{\"kind\": \"calls\", \"subject\": \"m.f\", \"object\": \"m.g\"{when}, \"at\": \"{at}\"}}\n"));
            for (value, w) in passes {
                let w = if w.is_empty() { String::new() } else { format!(", \"when\": \"{w}\"") };
                out.push_str(&format!("{{\"kind\": \"passes\", \"subject\": \"m.f->m.g\", \"object\": \"m.g.$x\", \"value\": \"{value}\"{w}, \"at\": \"{at}\"}}\n"));
            }
            out
        };
        let repo = Repo::new(name);
        repo.write(".archsig/law/m.law", &LAW.replace("\"shop/**\"", "\"m.py\""));
        repo.map(
            "m.py",
            &format!(
                "{}{T_ATOMS}{callee}{}",
                r#"{"kind": "observed", "subject": "m.py", "scope": "structure", "at": "m.py@blob:aaaaaaa"}
{"kind": "observed", "subject": "m.py", "scope": "meaning:payment-info", "at": "m.py@blob:aaaaaaa"}
{"kind": "resolves", "subject": "int", "object": "external:builtins", "at": "m.py:1@blob:aaaaaaa"}
"#,
                atoms("m.py:10@blob:aaaaaaa", passes)
            ),
        );
        repo.write(
            ".archsig/plans/p/plan.jsonl",
            &format!(
                "{}{}",
                r#"{"kind": "defines", "subject": "m.f", "value": "operation", "params": {"o": "m.O"}, "file": "m.py", "at": "plan:p"}
"#,
                atoms("plan:p", plan_passes)
            ),
        );
        let s = repo.run(&["plan", "check", "p"]);
        (result(&s, "m.f").clone(), s)
    };
    // 呼び出しと違う when、一つの引数に値の違う二つの passes は、渡す値が決まらない。
    for (name, call_when, passes) in [
        ("passes-other-when", "", vec![("1", "$o.n == 1")]),
        ("passes-two-values", "", vec![("1", ""), ("2", "")]),
        ("passes-two-conditions", "", vec![("1", "$o.n == 1"), ("2", "$o.n != 1")]),
    ] {
        let (r, s) = run(name, call_when, &passes, &passes);
        assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unresolved")), "{name}: {s}");
    }
    // 呼び出しと同じ when の passes と、when のない passes(条件付きの呼び出しを含む)は、計算する(対照)。
    for (name, call_when, passes) in [
        ("passes-plain", "", vec![("1", "")]),
        ("passes-same-when", "$o.n == 1", vec![("1", "$o.n == 1")]),
        ("passes-conditional-call", "$o.n == 1", vec![("1", "")]),
        ("passes-same-twice", "", vec![("1", ""), ("1", "")]),
    ] {
        let (r, s) = run(name, call_when, &passes, &passes);
        assert_eq!(r["outcome"], "holds", "{name}: {s}");
    }
    // 渡す値は計算に使う。候補が渡す値を変えれば、反例になる(対照)。
    for (name, call_when, before, plan) in [
        ("passes-plain-changed", "", vec![("1", "")], vec![("2", "")]),
        ("passes-same-when-changed", "$o.n == 1", vec![("1", "$o.n == 1")], vec![("2", "$o.n == 1")]),
        ("passes-conditional-call-changed", "$o.n == 1", vec![("1", "")], vec![("2", "")]),
    ] {
        let (r, s) = run(name, call_when, &before, &plan);
        assert_eq!(r["kind"], "counterexample", "{name}: {s}");
    }
}

#[test]
fn a_write_after_a_return_on_the_same_line_is_not_done() {
    // `if o.n == 1: return 1; o.t = 1` を、同じ行の returns と writes として観測する。戻り値の後に並ぶ書き込みは、戻った分岐では行わない。
    let body = r#"{"kind": "returns", "subject": "m.f", "value": "1", "when": "$o.n == 1", "at": "m.py:10@blob:aaaaaaa"}
{"kind": "writes", "subject": "m.f", "object": "m.O.t", "value": "1", "when": "$o.n == 1", "at": "m.py:10@blob:aaaaaaa"}
"#;
    let repo = Repo::new("return-write-same-line");
    repo.write(".archsig/law/m.law", &LAW.replace("\"shop/**\"", "\"m.py\""));
    repo.map(
        "m.py",
        &format!(
            "{}{T_ATOMS}{body}",
            r#"{"kind": "observed", "subject": "m.py", "scope": "structure", "at": "m.py@blob:aaaaaaa"}
{"kind": "observed", "subject": "m.py", "scope": "meaning:payment-info", "at": "m.py@blob:aaaaaaa"}
{"kind": "resolves", "subject": "int", "object": "external:builtins", "at": "m.py:1@blob:aaaaaaa"}
"#
        ),
    );
    repo.write(
        ".archsig/plans/p/plan.jsonl",
        r#"{"kind": "defines", "subject": "m.f", "value": "operation", "params": {"o": "m.O"}, "file": "m.py", "at": "plan:p"}
{"kind": "returns", "subject": "m.f", "value": "1", "when": "$o.n == 1", "at": "plan:p"}
"#,
    );
    let s = repo.run(&["plan", "check", "p"]);
    assert_eq!(result(&s, "m.f")["outcome"], "holds", "{s}");
}

#[test]
fn a_call_to_a_callee_whose_body_changed_is_unchecked() {
    // m.f は m.g() の戻り値を意味を持つ m.O.t に書く。候補は m.g の戻り値を書き直し、m.f は書き直さない。
    // 呼び出しの値を同じ項とみなす前提が、入力の上で確かめられない。
    let run = |name: &str, f_body: &str, g_plan: &str, plan_f: &str| {
        let repo = Repo::new(name);
        repo.write(".archsig/law/m.law", &LAW.replace("\"shop/**\"", "\"m.py\""));
        repo.map(
            "m.py",
            &format!(
                "{}{T_ATOMS}{f_body}{}",
                r#"{"kind": "observed", "subject": "m.py", "scope": "structure", "at": "m.py@blob:aaaaaaa"}
{"kind": "observed", "subject": "m.py", "scope": "meaning:payment-info", "at": "m.py@blob:aaaaaaa"}
{"kind": "resolves", "subject": "int", "object": "external:builtins", "at": "m.py:1@blob:aaaaaaa"}
"#,
                r#"{"kind": "defines", "subject": "m.g", "value": "operation", "params": {}, "at": "m.py:20@blob:aaaaaaa"}
{"kind": "returns", "subject": "m.g", "value": "1", "at": "m.py:21@blob:aaaaaaa"}
{"kind": "meaning", "subject": "m.O.n", "meaning": "payment-info", "uses": ["m.py:11@blob:aaaaaaa"], "at": "m.py:3@blob:aaaaaaa"}
"#
            ),
        );
        repo.write(
            ".archsig/plans/p/plan.jsonl",
            &format!(
                "{}{{\"kind\": \"returns\", \"subject\": \"m.g\", \"value\": \"{g_plan}\", \"at\": \"plan:p\"}}\n{plan_f}",
                r#"{"kind": "defines", "subject": "m.g", "value": "operation", "params": {}, "file": "m.py", "at": "plan:p"}
"#
            ),
        );
        let s = repo.run(&["plan", "check", "p"]);
        (result(&s, "m.f").clone(), s)
    };
    let writes_g = r#"{"kind": "writes", "subject": "m.f", "object": "m.O.t", "value": "m.g()", "at": "m.py:10@blob:aaaaaaa"}
"#;
    // 戻り値を書き直すと、値に m.g() を含む場所は比べられない。
    let (r, s) = run("changed-callee-value", writes_g, "2", "");
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unchecked")), "{s}");
    // 条件に m.g() を含むと、分岐の組み方が決まらない。
    let when_g = r#"{"kind": "writes", "subject": "m.f", "object": "m.O.t", "value": "1", "when": "m.g() == 1", "at": "m.py:10@blob:aaaaaaa"}
"#;
    let (r, s) = run("changed-callee-condition", when_g, "2", "");
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unchecked")), "{s}");
    // 本体が同じなら、これまでどおり同じ項として計算する(対照)。
    let (r, s) = run("same-callee-value", writes_g, "1", "");
    assert_eq!(r["outcome"], "holds", "{s}");
    // m.g() を含む場所は比べないが、意味を持つ m.O.n で食い違えば反例になる。
    let f_two = format!("{writes_g}{}", r#"{"kind": "writes", "subject": "m.f", "object": "m.O.n", "value": "1", "at": "m.py:11@blob:aaaaaaa"}
"#);
    let plan_f = r#"{"kind": "defines", "subject": "m.f", "value": "operation", "params": {"o": "m.O"}, "file": "m.py", "at": "plan:p"}
{"kind": "writes", "subject": "m.f", "object": "m.O.t", "value": "m.g()", "at": "plan:p"}
{"kind": "writes", "subject": "m.f", "object": "m.O.n", "value": "2", "at": "plan:p"}
"#;
    let (r, s) = run("changed-callee-other-place", &f_two, "2", plan_f);
    assert_eq!(r["kind"], "counterexample", "{s}");
}

#[test]
fn a_call_to_a_callee_that_calls_a_changed_body_is_unchecked() {
    // m.f は m.g() を m.O.t に書き、m.g は m.h を呼んで返す。候補は m.h だけを書き直す。m.g の結果も変わりうる。
    let repo = Repo::new("changed-callee-nested");
    repo.write(".archsig/law/m.law", &LAW.replace("\"shop/**\"", "\"m.py\""));
    repo.map(
        "m.py",
        &format!(
            "{}{T_ATOMS}{}",
            r#"{"kind": "observed", "subject": "m.py", "scope": "structure", "at": "m.py@blob:aaaaaaa"}
{"kind": "observed", "subject": "m.py", "scope": "meaning:payment-info", "at": "m.py@blob:aaaaaaa"}
{"kind": "resolves", "subject": "int", "object": "external:builtins", "at": "m.py:1@blob:aaaaaaa"}
"#,
            r#"{"kind": "writes", "subject": "m.f", "object": "m.O.t", "value": "m.g()", "at": "m.py:10@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.g", "value": "operation", "params": {}, "at": "m.py:20@blob:aaaaaaa"}
{"kind": "calls", "subject": "m.g", "object": "m.h", "at": "m.py:21@blob:aaaaaaa"}
{"kind": "returns", "subject": "m.g", "value": "m.h()", "at": "m.py:22@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.h", "value": "operation", "params": {}, "at": "m.py:30@blob:aaaaaaa"}
{"kind": "returns", "subject": "m.h", "value": "1", "at": "m.py:31@blob:aaaaaaa"}
"#
        ),
    );
    repo.write(
        ".archsig/plans/p/plan.jsonl",
        r#"{"kind": "defines", "subject": "m.h", "value": "operation", "params": {}, "file": "m.py", "at": "plan:p"}
{"kind": "returns", "subject": "m.h", "value": "2", "at": "plan:p"}
"#,
    );
    let s = repo.run(&["plan", "check", "p"]);
    let r = result(&s, "m.f");
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unchecked")), "{s}");
}

#[test]
fn a_call_to_an_external_callee_whose_resolution_changed_is_unchecked() {
    // m.f は外部の m.g() の戻り値を m.O.t に書く。候補は m.g の解決を別の外部へ書き換える。呼び出し先の本体(解決)が変わる。
    let run = |name: &str, plan: &str| {
        let repo = Repo::new(name);
        repo.write(".archsig/law/m.law", &LAW.replace("\"shop/**\"", "\"m.py\""));
        repo.map(
            "m.py",
            &format!(
                "{}{T_ATOMS}{}",
                r#"{"kind": "observed", "subject": "m.py", "scope": "structure", "at": "m.py@blob:aaaaaaa"}
{"kind": "observed", "subject": "m.py", "scope": "meaning:payment-info", "at": "m.py@blob:aaaaaaa"}
{"kind": "resolves", "subject": "int", "object": "external:builtins", "at": "m.py:1@blob:aaaaaaa"}
"#,
                r#"{"kind": "writes", "subject": "m.f", "object": "m.O.t", "value": "m.g()", "at": "m.py:10@blob:aaaaaaa"}
{"kind": "resolves", "subject": "m.g", "object": "external:lib", "at": "m.py:10@blob:aaaaaaa"}
"#
            ),
        );
        repo.write(".archsig/plans/p/plan.jsonl", plan);
        let s = repo.run(&["plan", "check", "p"]);
        (result(&s, "m.f").clone(), s)
    };
    let (r, s) = run("changed-external-callee", "{\"kind\": \"resolves\", \"subject\": \"m.g\", \"object\": \"external:lib2\", \"at\": \"plan:p\"}\n");
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unchecked")), "{s}");
    // 解決を書き換えない候補では、これまでどおり同じ項として計算する(対照)。
    let (r, s) = run("same-external-callee", "{\"kind\": \"removes\", \"subject\": \"m.O.n\", \"at\": \"plan:p\"}\n");
    assert_eq!(r["outcome"], "holds", "{s}");
}

#[test]
fn reordering_or_splitting_a_callee_is_a_changed_body() {
    // m.f は m.g() を m.O.t に書く。m.g は条件付きの戻り値を二つ持つ。
    let base = r#"{"kind": "observed", "subject": "m.py", "scope": "structure", "at": "m.py@blob:aaaaaaa"}
{"kind": "observed", "subject": "m.py", "scope": "meaning:payment-info", "at": "m.py@blob:aaaaaaa"}
{"kind": "resolves", "subject": "int", "object": "external:builtins", "at": "m.py:1@blob:aaaaaaa"}
"#;
    let run = |name: &str, map: &str, plan: &str| {
        let repo = Repo::new(name);
        repo.write(".archsig/law/m.law", &LAW.replace("\"shop/**\"", "\"m.py\""));
        repo.map("m.py", &format!("{base}{T_ATOMS}{map}"));
        repo.write(".archsig/plans/p/plan.jsonl", plan);
        let s = repo.run(&["plan", "check", "p"]);
        (result(&s, "m.f").clone(), s)
    };
    let g = r#"{"kind": "writes", "subject": "m.f", "object": "m.O.t", "value": "m.g()", "at": "m.py:10@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.g", "value": "operation", "params": {}, "at": "m.py:20@blob:aaaaaaa"}
{"kind": "returns", "subject": "m.g", "value": "1", "when": "X == 2", "at": "m.py:21@blob:aaaaaaa"}
{"kind": "returns", "subject": "m.g", "value": "2", "at": "m.py:22@blob:aaaaaaa"}
"#;
    // 戻り値の順を入れ替えると、戻り値が変わる。Atom の集まりは同じでも、本体が違う。
    let reordered = r#"{"kind": "defines", "subject": "m.g", "value": "operation", "params": {}, "file": "m.py", "at": "plan:p"}
{"kind": "returns", "subject": "m.g", "value": "2", "at": "plan:p"}
{"kind": "returns", "subject": "m.g", "value": "1", "when": "X == 2", "at": "plan:p"}
"#;
    let (r, s) = run("reordered-callee", g, reordered);
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unchecked")), "{s}");
    // 同じ順で書き直すなら、本体は同じ(対照)。
    let same = r#"{"kind": "defines", "subject": "m.g", "value": "operation", "params": {}, "file": "m.py", "at": "plan:p"}
{"kind": "returns", "subject": "m.g", "value": "1", "when": "X == 2", "at": "plan:p"}
{"kind": "returns", "subject": "m.g", "value": "2", "at": "plan:p"}
"#;
    let (r, s) = run("same-order-callee", g, same);
    assert_eq!(r["outcome"], "holds", "{s}");
    // m.g を m.g と m.g2 に分け、m.g2 の戻り値を変える。行き先のどれかの本体が違えば、本体が違う。
    let split = r#"{"kind": "corresponds", "subject": "m.g", "object": "m.g2", "at": "plan:p"}
{"kind": "defines", "subject": "m.g2", "value": "operation", "params": {}, "file": "m.py", "at": "plan:p"}
{"kind": "returns", "subject": "m.g2", "value": "3", "at": "plan:p"}
{"kind": "defines", "subject": "m.f", "value": "operation", "params": {"o": "m.O"}, "file": "m.py", "at": "plan:p"}
{"kind": "writes", "subject": "m.f", "object": "m.O.t", "value": "m.g2()", "at": "plan:p"}
"#;
    let (r, s) = run("split-callee", g, split);
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unchecked")), "{s}");
    // m.g が calls の Atom なしに式の中で m.h を呼ぶ。候補が m.h を書き直せば、m.g の本体も違う。
    let nested = r#"{"kind": "writes", "subject": "m.f", "object": "m.O.t", "value": "m.g()", "at": "m.py:10@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.g", "value": "operation", "params": {}, "at": "m.py:20@blob:aaaaaaa"}
{"kind": "returns", "subject": "m.g", "value": "m.h()", "at": "m.py:21@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.h", "value": "operation", "params": {}, "at": "m.py:30@blob:aaaaaaa"}
{"kind": "returns", "subject": "m.h", "value": "1", "at": "m.py:31@blob:aaaaaaa"}
"#;
    let h2 = r#"{"kind": "defines", "subject": "m.h", "value": "operation", "params": {}, "file": "m.py", "at": "plan:p"}
{"kind": "returns", "subject": "m.h", "value": "2", "at": "plan:p"}
"#;
    let (r, s) = run("value-call-callee", nested, h2);
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unchecked")), "{s}");
    // m.g が m.h を、m.h が m.k を呼ぶ。候補が二段先の m.k を書き直しても、m.g の本体は違う。
    let two_levels = r#"{"kind": "writes", "subject": "m.f", "object": "m.O.t", "value": "m.g()", "at": "m.py:10@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.g", "value": "operation", "params": {}, "at": "m.py:20@blob:aaaaaaa"}
{"kind": "returns", "subject": "m.g", "value": "m.h()", "at": "m.py:21@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.h", "value": "operation", "params": {}, "at": "m.py:30@blob:aaaaaaa"}
{"kind": "returns", "subject": "m.h", "value": "m.k()", "at": "m.py:31@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.k", "value": "operation", "params": {}, "at": "m.py:40@blob:aaaaaaa"}
{"kind": "returns", "subject": "m.k", "value": "1", "at": "m.py:41@blob:aaaaaaa"}
"#;
    let k2 = r#"{"kind": "defines", "subject": "m.k", "value": "operation", "params": {}, "file": "m.py", "at": "plan:p"}
{"kind": "returns", "subject": "m.k", "value": "2", "at": "plan:p"}
"#;
    let (r, s) = run("two-level-callee", two_levels, k2);
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unchecked")), "{s}");
}

#[test]
fn the_body_of_a_callee_is_compared_in_every_part() {
    let base = r#"{"kind": "observed", "subject": "m.py", "scope": "structure", "at": "m.py@blob:aaaaaaa"}
{"kind": "observed", "subject": "m.py", "scope": "meaning:payment-info", "at": "m.py@blob:aaaaaaa"}
{"kind": "resolves", "subject": "int", "object": "external:builtins", "at": "m.py:1@blob:aaaaaaa"}
"#;
    let run = |name: &str, map: &str, plan: &str| {
        let repo = Repo::new(name);
        repo.write(".archsig/law/m.law", &LAW.replace("\"shop/**\"", "\"m.py\""));
        repo.map("m.py", &format!("{base}{T_ATOMS}{map}"));
        repo.write(".archsig/plans/p/plan.jsonl", plan);
        let s = repo.run(&["plan", "check", "p"]);
        (result(&s, "m.f").clone(), s)
    };
    let unchecked = |name: &str, map: &str, plan: &str| {
        let (r, s) = run(name, map, plan);
        assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unchecked")), "{name}: {s}");
    };
    let f_g = r#"{"kind": "writes", "subject": "m.f", "object": "m.O.t", "value": "m.g()", "at": "m.py:10@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.g", "value": "operation", "params": {}, "at": "m.py:20@blob:aaaaaaa"}
"#;
    let g_def = r#"{"kind": "defines", "subject": "m.g", "value": "operation", "params": {}, "file": "m.py", "at": "plan:p"}
"#;
    // 本体の手順の when だけを変える。
    unchecked(
        "callee-when",
        &format!("{f_g}{}", r#"{"kind": "returns", "subject": "m.g", "value": "1", "when": "X == 2", "at": "m.py:21@blob:aaaaaaa"}
"#),
        &format!("{g_def}{}", r#"{"kind": "returns", "subject": "m.g", "value": "1", "when": "X == 3", "at": "plan:p"}
"#),
    );
    // 呼び出し先の中の呼び出しに渡す値(passes)だけを変える。
    let h = r#"{"kind": "defines", "subject": "m.h", "value": "operation", "params": {"x": "int"}, "at": "m.py:30@blob:aaaaaaa"}
{"kind": "returns", "subject": "m.h", "value": "$x", "at": "m.py:31@blob:aaaaaaa"}
"#;
    unchecked(
        "callee-passes",
        &format!("{f_g}{h}{}", r#"{"kind": "calls", "subject": "m.g", "object": "m.h", "at": "m.py:21@blob:aaaaaaa"}
{"kind": "passes", "subject": "m.g->m.h", "object": "m.h.$x", "value": "1", "at": "m.py:21@blob:aaaaaaa"}
"#),
        &format!("{g_def}{}", r#"{"kind": "calls", "subject": "m.g", "object": "m.h", "at": "plan:p"}
{"kind": "passes", "subject": "m.g->m.h", "object": "m.h.$x", "value": "2", "at": "plan:p"}
"#),
    );
    // 変更後の値にだけ、新しい操作の呼び出しが現れる。
    let f_plain = r#"{"kind": "writes", "subject": "m.f", "object": "m.O.t", "value": "1", "at": "m.py:10@blob:aaaaaaa"}
"#;
    let k = r#"{"kind": "defines", "subject": "m.k", "value": "operation", "params": {}, "file": "m.py", "at": "plan:p"}
{"kind": "returns", "subject": "m.k", "value": "1", "at": "plan:p"}
{"kind": "defines", "subject": "m.f", "value": "operation", "params": {"o": "m.O"}, "file": "m.py", "at": "plan:p"}
"#;
    unchecked(
        "new-callee-value",
        f_plain,
        &format!("{k}{}", r#"{"kind": "writes", "subject": "m.f", "object": "m.O.t", "value": "m.k()", "at": "plan:p"}
"#),
    );
    // 変更後の条件にだけ、新しい操作の呼び出しが現れる。
    unchecked(
        "new-callee-condition",
        f_plain,
        &format!("{k}{}", r#"{"kind": "writes", "subject": "m.f", "object": "m.O.t", "value": "1", "when": "m.k() == 1", "at": "plan:p"}
"#),
    );
    // 呼び出し先の名前を変え(行き先は一つ)、本体は同じ。行き先の本体と比べるので、同じ項である。
    let renamed = r#"{"kind": "corresponds", "subject": "m.g", "object": "m.g2", "at": "plan:p"}
{"kind": "removes", "subject": "m.g", "at": "plan:p"}
{"kind": "defines", "subject": "m.g2", "value": "operation", "params": {}, "file": "m.py", "at": "plan:p"}
{"kind": "returns", "subject": "m.g2", "value": "1", "at": "plan:p"}
{"kind": "defines", "subject": "m.f", "value": "operation", "params": {"o": "m.O"}, "file": "m.py", "at": "plan:p"}
{"kind": "writes", "subject": "m.f", "object": "m.O.t", "value": "m.g2()", "at": "plan:p"}
"#;
    let (r, s) = run(
        "renamed-callee",
        &format!("{f_g}{}", r#"{"kind": "returns", "subject": "m.g", "value": "1", "at": "m.py:21@blob:aaaaaaa"}
"#),
        renamed,
    );
    assert_eq!(r["outcome"], "holds", "{s}");
}

#[test]
fn the_body_of_a_callee_is_compared_without_noise_and_with_care() {
    let base = r#"{"kind": "observed", "subject": "m.py", "scope": "structure", "at": "m.py@blob:aaaaaaa"}
{"kind": "observed", "subject": "m.py", "scope": "meaning:payment-info", "at": "m.py@blob:aaaaaaa"}
{"kind": "resolves", "subject": "int", "object": "external:builtins", "at": "m.py:1@blob:aaaaaaa"}
"#;
    let run = |name: &str, map: &str, plan: &str| {
        let repo = Repo::new(name);
        repo.write(".archsig/law/m.law", &LAW.replace("\"shop/**\"", "\"m.py\""));
        repo.map("m.py", &format!("{base}{T_ATOMS}{map}"));
        repo.write(".archsig/plans/p/plan.jsonl", plan);
        let s = repo.run(&["plan", "check", "p"]);
        (result(&s, "m.f").clone(), s)
    };
    let outcome = |name: &str, map: &str, plan: &str| {
        let (r, s) = run(name, map, plan);
        (r["outcome"].as_str().map(str::to_string), r["reason"].as_str().map(str::to_string), s)
    };
    let f_g = r#"{"kind": "writes", "subject": "m.f", "object": "m.O.t", "value": "m.g()", "at": "m.py:10@blob:aaaaaaa"}
{"kind": "resolves", "subject": "m.g", "object": "m.py", "at": "m.py:10@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.g", "value": "operation", "params": {}, "at": "m.py:20@blob:aaaaaaa"}
{"kind": "returns", "subject": "m.g", "value": "1", "at": "m.py:21@blob:aaaaaaa"}
"#;
    let z = r#"{"kind": "defines", "subject": "m.z", "value": "operation", "params": {}, "file": "m.py", "at": "plan:p"}
"#;
    // 同じ指す先の resolves が一つ増えるだけなら、本体は同じ(重なりは一つと同じ)。
    let (o, _, s) = outcome("same-resolves-again", f_g, &format!("{z}{}", r#"{"kind": "resolves", "subject": "m.g", "object": "m.py", "at": "plan:p"}
"#));
    assert_eq!(o.as_deref(), Some("holds"), "{s}");
    // 解決を持つ呼び出し先を、同じ内容で書き直す。定義のある操作の本体に解決は入らない。
    let (o, _, s) = outcome("same-rewrite-with-resolves", f_g, r#"{"kind": "defines", "subject": "m.g", "value": "operation", "params": {}, "file": "m.py", "at": "plan:p"}
{"kind": "returns", "subject": "m.g", "value": "1", "at": "plan:p"}
"#);
    assert_eq!(o.as_deref(), Some("holds"), "{s}");
    let g_def = r#"{"kind": "writes", "subject": "m.f", "object": "m.O.t", "value": "m.g()", "at": "m.py:10@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.g", "value": "operation", "params": {}, "at": "m.py:20@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.h", "value": "operation", "params": {}, "at": "m.py:30@blob:aaaaaaa"}
{"kind": "returns", "subject": "m.h", "value": "1", "at": "m.py:31@blob:aaaaaaa"}
"#;
    let h2 = r#"{"kind": "defines", "subject": "m.h", "value": "operation", "params": {}, "file": "m.py", "at": "plan:p"}
{"kind": "returns", "subject": "m.h", "value": "2", "at": "plan:p"}
"#;
    // 読めない式の中の呼び出しはたどれないので、本体を比べられない。違うとして沈黙する。
    let (o, r, s) = outcome("unreadable-callee", &format!("{g_def}{}", r#"{"kind": "returns", "subject": "m.g", "value": "m.h() +", "at": "m.py:21@blob:aaaaaaa"}
"#), h2);
    assert_eq!((o.as_deref(), r.as_deref()), (Some("silent"), Some("unchecked")), "{s}");
    // 式に現れず calls の Atom だけで呼ぶ操作もたどる。
    let (o, r, s) = outcome("calls-only-callee", &format!("{g_def}{}", r#"{"kind": "calls", "subject": "m.g", "object": "m.h", "at": "m.py:21@blob:aaaaaaa"}
{"kind": "returns", "subject": "m.g", "value": "1", "at": "m.py:22@blob:aaaaaaa"}
"#), h2);
    assert_eq!((o.as_deref(), r.as_deref()), (Some("silent"), Some("unchecked")), "{s}");
    // 手順の via だけを変える。本体は、`via` と `object` の列を道で解いた場所で比べる。
    // m.O.s の定義を読んでいなければ、変更前の道が決まらないので、その道の沈黙(m.O.s を読む)で沈黙する。
    let (o, r, s) = outcome(
        "callee-via",
        &format!("{g_def}{}", r#"{"kind": "writes", "subject": "m.g", "via": ["m.O.s"], "object": "m.S.p", "value": "1", "at": "m.py:21@blob:aaaaaaa"}
"#),
        r#"{"kind": "defines", "subject": "m.g", "value": "operation", "params": {}, "file": "m.py", "at": "plan:p"}
{"kind": "writes", "subject": "m.g", "object": "m.S.p", "value": "1", "at": "plan:p"}
"#,
    );
    assert_eq!((o.as_deref(), r.as_deref()), (Some("silent"), Some("unread")), "{s}");
    assert!(s["next"].as_array().unwrap().iter().any(|n| n["element"] == "m.O.s"), "{s}");
    // 道が決まれば、via を通る場所 [m.O.s, m.S.p] と via のない場所 [m.S.p] は違うので、本体が違う。
    let (o, r, s) = outcome(
        "callee-via-read",
        &format!("{g_def}{}", r#"{"kind": "defines", "subject": "m.O.s", "value": "field", "type": "m.S", "at": "m.py:4@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.S", "value": "type", "at": "m.py:5@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.S.p", "value": "field", "type": "int", "at": "m.py:6@blob:aaaaaaa"}
{"kind": "writes", "subject": "m.g", "via": ["m.O.s"], "object": "m.S.p", "value": "1", "at": "m.py:21@blob:aaaaaaa"}
"#),
        r#"{"kind": "defines", "subject": "m.g", "value": "operation", "params": {}, "file": "m.py", "at": "plan:p"}
{"kind": "writes", "subject": "m.g", "object": "m.S.p", "value": "1", "at": "plan:p"}
"#,
    );
    assert_eq!((o.as_deref(), r.as_deref()), (Some("silent"), Some("unchecked")), "{s}");
    // 変更前の値にだけ、本体の変わった呼び出しが現れる。
    let (o, r, s) = outcome(
        "changed-callee-before-only",
        &format!("{g_def}{}", r#"{"kind": "returns", "subject": "m.g", "value": "1", "at": "m.py:21@blob:aaaaaaa"}
"#),
        r#"{"kind": "defines", "subject": "m.g", "value": "operation", "params": {}, "file": "m.py", "at": "plan:p"}
{"kind": "returns", "subject": "m.g", "value": "2", "at": "plan:p"}
{"kind": "defines", "subject": "m.f", "value": "operation", "params": {"o": "m.O"}, "file": "m.py", "at": "plan:p"}
{"kind": "writes", "subject": "m.f", "object": "m.O.t", "value": "1", "at": "plan:p"}
"#,
    );
    assert_eq!((o.as_deref(), r.as_deref()), (Some("silent"), Some("unchecked")), "{s}");
}

#[test]
fn a_callee_with_a_too_long_expression_is_a_changed_body() {
    // m.g の戻り値の式が字句の上限を超える。構文として読めるかを確かめていないので、その先をたどれず、本体を比べられない。
    let long = format!("m.h(){}", " + 1".repeat(600));
    let repo = Repo::new("too-long-callee");
    repo.write(".archsig/law/m.law", &LAW.replace("\"shop/**\"", "\"m.py\""));
    repo.map(
        "m.py",
        &format!(
            "{}{T_ATOMS}{}{{\"kind\": \"returns\", \"subject\": \"m.g\", \"value\": \"{long}\", \"at\": \"m.py:21@blob:aaaaaaa\"}}\n",
            r#"{"kind": "observed", "subject": "m.py", "scope": "structure", "at": "m.py@blob:aaaaaaa"}
{"kind": "observed", "subject": "m.py", "scope": "meaning:payment-info", "at": "m.py@blob:aaaaaaa"}
{"kind": "resolves", "subject": "int", "object": "external:builtins", "at": "m.py:1@blob:aaaaaaa"}
"#,
            r#"{"kind": "writes", "subject": "m.f", "object": "m.O.t", "value": "m.g()", "at": "m.py:10@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.g", "value": "operation", "params": {}, "at": "m.py:20@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.h", "value": "operation", "params": {}, "at": "m.py:30@blob:aaaaaaa"}
{"kind": "returns", "subject": "m.h", "value": "1", "at": "m.py:31@blob:aaaaaaa"}
"#
        ),
    );
    repo.write(
        ".archsig/plans/p/plan.jsonl",
        r#"{"kind": "defines", "subject": "m.h", "value": "operation", "params": {}, "file": "m.py", "at": "plan:p"}
{"kind": "returns", "subject": "m.h", "value": "2", "at": "plan:p"}
"#,
    );
    let s = repo.run(&["plan", "check", "p"]);
    let r = result(&s, "m.f");
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unchecked")), "{s}");
}

/// 呼び出し先 m.g の戻り値を `value` とし、候補が m.g を同じ戻り値で書き直したときの、呼び出し元 m.f の結果。
fn rewritten_callee(name: &str, value: &str) -> (Option<String>, Option<String>) {
    let repo = Repo::new(name);
    repo.write(".archsig/law/m.law", &LAW.replace("\"shop/**\"", "\"m.py\""));
    repo.map(
        "m.py",
        &format!(
            "{}{T_ATOMS}{}{{\"kind\": \"returns\", \"subject\": \"m.g\", \"value\": \"{value}\", \"at\": \"m.py:21@blob:aaaaaaa\"}}\n",
            r#"{"kind": "observed", "subject": "m.py", "scope": "structure", "at": "m.py@blob:aaaaaaa"}
{"kind": "observed", "subject": "m.py", "scope": "meaning:payment-info", "at": "m.py@blob:aaaaaaa"}
{"kind": "resolves", "subject": "int", "object": "external:builtins", "at": "m.py:1@blob:aaaaaaa"}
"#,
            r#"{"kind": "writes", "subject": "m.f", "object": "m.O.t", "value": "m.g()", "at": "m.py:10@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.g", "value": "operation", "params": {}, "at": "m.py:20@blob:aaaaaaa"}
"#
        ),
    );
    repo.write(
        ".archsig/plans/p/plan.jsonl",
        &format!(
            "{{\"kind\": \"defines\", \"subject\": \"m.g\", \"value\": \"operation\", \"params\": {{}}, \"file\": \"m.py\", \"at\": \"plan:p\"}}\n{{\"kind\": \"returns\", \"subject\": \"m.g\", \"value\": \"{value}\", \"at\": \"plan:p\"}}\n"
        ),
    );
    let s = repo.run(&["plan", "check", "p"]);
    let r = result(&s, "m.f");
    (r["outcome"].as_str().map(String::from), r["reason"].as_str().map(String::from))
}

#[test]
fn a_callee_body_with_a_question_mark_is_a_changed_body() {
    // `?` は入力から決まらない値なので、前後で同じ字句でも、本体が同じとはみなさない。
    for (name, value) in [("q-value", "?"), ("q-name", "?m.h()"), ("q-inner", "1 + ?x")] {
        assert_eq!(rewritten_callee(name, value), (Some("silent".into()), Some("unchecked".into())), "{value}");
    }
    // 同じ形で `?` がなければ、本体は同じである。
    assert_eq!(rewritten_callee("q-none", "1").0.as_deref(), Some("holds"));
}

#[test]
fn a_callee_body_with_an_undecided_resolution_is_a_changed_body() {
    // m.g は外部の m.h() を返す。m.h の解決は指す先が二つあり、決まらない。前後で同じでも、本体が同じとはみなさない。
    let repo = Repo::new("undecided-callee");
    repo.write(".archsig/law/m.law", &LAW.replace("\"shop/**\"", "\"m.py\""));
    repo.map(
        "m.py",
        &format!(
            "{}{T_ATOMS}{}",
            r#"{"kind": "observed", "subject": "m.py", "scope": "structure", "at": "m.py@blob:aaaaaaa"}
{"kind": "observed", "subject": "m.py", "scope": "meaning:payment-info", "at": "m.py@blob:aaaaaaa"}
{"kind": "resolves", "subject": "int", "object": "external:builtins", "at": "m.py:1@blob:aaaaaaa"}
"#,
            r#"{"kind": "writes", "subject": "m.f", "object": "m.O.t", "value": "m.g()", "at": "m.py:10@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.g", "value": "operation", "params": {}, "at": "m.py:20@blob:aaaaaaa"}
{"kind": "returns", "subject": "m.g", "value": "m.h()", "at": "m.py:21@blob:aaaaaaa"}
{"kind": "resolves", "subject": "m.h", "object": "external:lib", "at": "m.py:2@blob:aaaaaaa"}
{"kind": "resolves", "subject": "m.h", "object": "external:lib2", "at": "m.py:3@blob:aaaaaaa"}
"#
        ),
    );
    repo.write(
        ".archsig/plans/p/plan.jsonl",
        r#"{"kind": "defines", "subject": "m.g", "value": "operation", "params": {}, "file": "m.py", "at": "plan:p"}
{"kind": "returns", "subject": "m.g", "value": "m.h()", "at": "plan:p"}
"#,
    );
    let s = repo.run(&["plan", "check", "p"]);
    let r = result(&s, "m.f");
    assert_ne!(r["outcome"], "holds", "{s}");
}

#[test]
fn a_callee_body_with_a_question_mark_target_is_a_changed_body() {
    // m.g は形に直せなかった先 `?m.h` を呼ぶ。候補は m.g を同じ形で書き直す。`?` は入力から決まらないので、本体が同じとはみなさない。
    let repo = Repo::new("q-target-callee");
    repo.write(".archsig/law/m.law", &LAW.replace("\"shop/**\"", "\"m.py\""));
    repo.map(
        "m.py",
        &format!(
            "{}{T_ATOMS}{}",
            r#"{"kind": "observed", "subject": "m.py", "scope": "structure", "at": "m.py@blob:aaaaaaa"}
{"kind": "observed", "subject": "m.py", "scope": "meaning:payment-info", "at": "m.py@blob:aaaaaaa"}
{"kind": "resolves", "subject": "int", "object": "external:builtins", "at": "m.py:1@blob:aaaaaaa"}
"#,
            r#"{"kind": "writes", "subject": "m.f", "object": "m.O.t", "value": "m.g()", "at": "m.py:10@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.g", "value": "operation", "params": {}, "at": "m.py:20@blob:aaaaaaa"}
{"kind": "calls", "subject": "m.g", "object": "?m.h", "at": "m.py:21@blob:aaaaaaa"}
{"kind": "returns", "subject": "m.g", "value": "1", "at": "m.py:22@blob:aaaaaaa"}
"#
        ),
    );
    repo.write(
        ".archsig/plans/p/plan.jsonl",
        r#"{"kind": "defines", "subject": "m.g", "value": "operation", "params": {}, "file": "m.py", "at": "plan:p"}
{"kind": "calls", "subject": "m.g", "object": "?m.h", "at": "plan:p"}
{"kind": "returns", "subject": "m.g", "value": "1", "at": "plan:p"}
"#,
    );
    let s = repo.run(&["plan", "check", "p"]);
    let r = result(&s, "m.f");
    assert_ne!(r["outcome"], "holds", "{s}");
}

#[test]
fn swapping_the_arguments_of_two_calls_in_a_callee_is_a_changed_body() {
    // m.g は m.h を二度呼び、一度目に 1、二度目に 2 を渡す。m.h は $o.n に $x を書き、m.g は $o.n を返す。
    // 候補は二つの呼び出しに渡す値を入れ替える。m.g の戻り値は 2 から 1 に変わるので、本体が同じとはみなさない。
    let run = |name: &str, first: &str, second: &str| {
        let repo = Repo::new(name);
        repo.write(".archsig/law/m.law", &LAW.replace("\"shop/**\"", "\"m.py\""));
        repo.map(
            "m.py",
            &format!(
                "{}{T_ATOMS}{}",
                r#"{"kind": "observed", "subject": "m.py", "scope": "structure", "at": "m.py@blob:aaaaaaa"}
{"kind": "observed", "subject": "m.py", "scope": "meaning:payment-info", "at": "m.py@blob:aaaaaaa"}
{"kind": "resolves", "subject": "int", "object": "external:builtins", "at": "m.py:1@blob:aaaaaaa"}
"#,
                r#"{"kind": "writes", "subject": "m.f", "object": "m.O.t", "value": "m.g($o)", "at": "m.py:10@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.g", "value": "operation", "params": {"o": "m.O"}, "at": "m.py:20@blob:aaaaaaa"}
{"kind": "calls", "subject": "m.g", "object": "m.h", "at": "m.py:21@blob:aaaaaaa"}
{"kind": "passes", "subject": "m.g->m.h", "object": "m.h.$o", "value": "$o", "at": "m.py:21@blob:aaaaaaa"}
{"kind": "passes", "subject": "m.g->m.h", "object": "m.h.$x", "value": "1", "at": "m.py:21@blob:aaaaaaa"}
{"kind": "calls", "subject": "m.g", "object": "m.h", "at": "m.py:22@blob:aaaaaaa"}
{"kind": "passes", "subject": "m.g->m.h#2", "object": "m.h.$o", "value": "$o", "at": "m.py:22@blob:aaaaaaa"}
{"kind": "passes", "subject": "m.g->m.h#2", "object": "m.h.$x", "value": "2", "at": "m.py:22@blob:aaaaaaa"}
{"kind": "returns", "subject": "m.g", "value": "$o.n", "at": "m.py:23@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.h", "value": "operation", "params": {"o": "m.O", "x": "int"}, "at": "m.py:30@blob:aaaaaaa"}
{"kind": "writes", "subject": "m.h", "object": "$o.n", "value": "$x", "at": "m.py:31@blob:aaaaaaa"}
"#
            ),
        );
        repo.write(
            ".archsig/plans/p/plan.jsonl",
            &format!(
                r#"{{"kind": "defines", "subject": "m.g", "value": "operation", "params": {{"o": "m.O"}}, "file": "m.py", "at": "plan:p"}}
{{"kind": "calls", "subject": "m.g", "object": "m.h", "at": "plan:p"}}
{{"kind": "passes", "subject": "m.g->m.h", "object": "m.h.$o", "value": "$o", "at": "plan:p"}}
{{"kind": "passes", "subject": "m.g->m.h", "object": "m.h.$x", "value": "{first}", "at": "plan:p"}}
{{"kind": "calls", "subject": "m.g", "object": "m.h", "at": "plan:p"}}
{{"kind": "passes", "subject": "m.g->m.h#2", "object": "m.h.$o", "value": "$o", "at": "plan:p"}}
{{"kind": "passes", "subject": "m.g->m.h#2", "object": "m.h.$x", "value": "{second}", "at": "plan:p"}}
{{"kind": "returns", "subject": "m.g", "value": "$o.n", "at": "plan:p"}}
"#
            ),
        );
        let s = repo.run(&["plan", "check", "p"]);
        (result(&s, "m.f")["outcome"].as_str().map(String::from), s)
    };
    let run_reordered = |name: &str| {
        let (first, second) = ("1", "2");
        let repo = Repo::new(name);
        repo.write(".archsig/law/m.law", &LAW.replace("\"shop/**\"", "\"m.py\""));
        repo.map(
            "m.py",
            &format!(
                "{}{T_ATOMS}{}",
                r#"{"kind": "observed", "subject": "m.py", "scope": "structure", "at": "m.py@blob:aaaaaaa"}
{"kind": "observed", "subject": "m.py", "scope": "meaning:payment-info", "at": "m.py@blob:aaaaaaa"}
{"kind": "resolves", "subject": "int", "object": "external:builtins", "at": "m.py:1@blob:aaaaaaa"}
"#,
                r#"{"kind": "writes", "subject": "m.f", "object": "m.O.t", "value": "m.g($o)", "at": "m.py:10@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.g", "value": "operation", "params": {"o": "m.O"}, "at": "m.py:20@blob:aaaaaaa"}
{"kind": "calls", "subject": "m.g", "object": "m.h", "at": "m.py:21@blob:aaaaaaa"}
{"kind": "passes", "subject": "m.g->m.h", "object": "m.h.$o", "value": "$o", "at": "m.py:21@blob:aaaaaaa"}
{"kind": "passes", "subject": "m.g->m.h", "object": "m.h.$x", "value": "1", "at": "m.py:21@blob:aaaaaaa"}
{"kind": "calls", "subject": "m.g", "object": "m.h", "at": "m.py:22@blob:aaaaaaa"}
{"kind": "passes", "subject": "m.g->m.h#2", "object": "m.h.$o", "value": "$o", "at": "m.py:22@blob:aaaaaaa"}
{"kind": "passes", "subject": "m.g->m.h#2", "object": "m.h.$x", "value": "2", "at": "m.py:22@blob:aaaaaaa"}
{"kind": "returns", "subject": "m.g", "value": "$o.n", "at": "m.py:23@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.h", "value": "operation", "params": {"o": "m.O", "x": "int"}, "at": "m.py:30@blob:aaaaaaa"}
{"kind": "writes", "subject": "m.h", "object": "$o.n", "value": "$x", "at": "m.py:31@blob:aaaaaaa"}
"#
            ),
        );
        repo.write(
            ".archsig/plans/p/plan.jsonl",
            &format!(
                r#"{{"kind": "defines", "subject": "m.g", "value": "operation", "params": {{"o": "m.O"}}, "file": "m.py", "at": "plan:p"}}
{{"kind": "calls", "subject": "m.g", "object": "m.h", "at": "plan:p"}}
{{"kind": "passes", "subject": "m.g->m.h", "object": "m.h.$x", "value": "{first}", "at": "plan:p"}}
{{"kind": "passes", "subject": "m.g->m.h", "object": "m.h.$o", "value": "$o", "at": "plan:p"}}
{{"kind": "calls", "subject": "m.g", "object": "m.h", "at": "plan:p"}}
{{"kind": "passes", "subject": "m.g->m.h#2", "object": "m.h.$o", "value": "$o", "at": "plan:p"}}
{{"kind": "passes", "subject": "m.g->m.h#2", "object": "m.h.$x", "value": "{second}", "at": "plan:p"}}
{{"kind": "returns", "subject": "m.g", "value": "$o.n", "at": "plan:p"}}
"#
            ),
        );
        let s = repo.run(&["plan", "check", "p"]);
        (result(&s, "m.f")["outcome"].as_str().map(String::from), s)
    };
    let (o, s) = run("swapped-calls", "2", "1");
    assert_ne!(o.as_deref(), Some("holds"), "{s}");
    // 同じ値で書き直せば、本体は同じである(対照)。
    let (o, s) = run("same-calls", "1", "2");
    assert_eq!(o.as_deref(), Some("holds"), "{s}");
    // 手順でない Atom(`passes`)の並びだけが違っても、本体は同じである。
    let (o, s) = run_reordered("reordered-passes");
    assert_eq!(o.as_deref(), Some("holds"), "{s}");
}

#[test]
fn changing_the_parameter_types_of_a_callee_is_a_changed_body() {
    // m.g は引数 o の $o.n を返す。候補は m.g を同じ戻り値で書き直し、o の型だけを変える。読むフィールドが変わるので、本体が同じとはみなさない。
    let run = |name: &str, ty: &str| {
        let repo = Repo::new(name);
        repo.write(".archsig/law/m.law", &LAW.replace("\"shop/**\"", "\"m.py\""));
        repo.map(
            "m.py",
            &format!(
                "{}{T_ATOMS}{}",
                r#"{"kind": "observed", "subject": "m.py", "scope": "structure", "at": "m.py@blob:aaaaaaa"}
{"kind": "observed", "subject": "m.py", "scope": "meaning:payment-info", "at": "m.py@blob:aaaaaaa"}
{"kind": "resolves", "subject": "int", "object": "external:builtins", "at": "m.py:1@blob:aaaaaaa"}
"#,
                r#"{"kind": "writes", "subject": "m.f", "object": "m.O.t", "value": "m.g($o)", "at": "m.py:10@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.g", "value": "operation", "params": {"o": "m.O"}, "at": "m.py:20@blob:aaaaaaa"}
{"kind": "returns", "subject": "m.g", "value": "$o.n", "at": "m.py:21@blob:aaaaaaa"}
"#
            ),
        );
        repo.write(
            ".archsig/plans/p/plan.jsonl",
            &format!(
                "{{\"kind\": \"defines\", \"subject\": \"m.g\", \"value\": \"operation\", \"params\": {{\"o\": \"{ty}\"}}, \"file\": \"m.py\", \"at\": \"plan:p\"}}\n{{\"kind\": \"returns\", \"subject\": \"m.g\", \"value\": \"$o.n\", \"at\": \"plan:p\"}}\n"
            ),
        );
        let s = repo.run(&["plan", "check", "p"]);
        (result(&s, "m.f")["outcome"].as_str().map(String::from), s)
    };
    let run2 = |name: &str, ty: &str| {
        let repo = Repo::new(name);
        repo.write(".archsig/law/m.law", &LAW.replace("\"shop/**\"", "\"m.py\""));
        repo.map(
            "m.py",
            &format!(
                "{}{T_ATOMS}{}",
                r#"{"kind": "observed", "subject": "m.py", "scope": "structure", "at": "m.py@blob:aaaaaaa"}
{"kind": "observed", "subject": "m.py", "scope": "meaning:payment-info", "at": "m.py@blob:aaaaaaa"}
{"kind": "resolves", "subject": "int", "object": "external:builtins", "at": "m.py:1@blob:aaaaaaa"}
"#,
                r#"{"kind": "writes", "subject": "m.f", "object": "m.O.t", "value": "m.g($o)", "at": "m.py:10@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.g", "value": "operation", "params": {"o": "?m.O"}, "at": "m.py:20@blob:aaaaaaa"}
{"kind": "returns", "subject": "m.g", "value": "$o.n", "at": "m.py:21@blob:aaaaaaa"}
"#
            ),
        );
        repo.write(
            ".archsig/plans/p/plan.jsonl",
            &format!(
                "{{\"kind\": \"defines\", \"subject\": \"m.g\", \"value\": \"operation\", \"params\": {{\"o\": \"{ty}\"}}, \"file\": \"m.py\", \"at\": \"plan:p\"}}\n{{\"kind\": \"returns\", \"subject\": \"m.g\", \"value\": \"$o.n\", \"at\": \"plan:p\"}}\n"
            ),
        );
        let s = repo.run(&["plan", "check", "p"]);
        (result(&s, "m.f")["outcome"].as_str().map(String::from), s)
    };
    let (o, s) = run("param-type-changed", "m.P");
    assert_ne!(o.as_deref(), Some("holds"), "{s}");
    let (o, s) = run("param-type-question", "?m.O");
    assert_ne!(o.as_deref(), Some("holds"), "{s}");
    let (o, s) = run2("param-type-both-question", "?m.O");
    assert_ne!(o.as_deref(), Some("holds"), "{s}");
    // 同じ型で書き直せば、本体は同じである(対照)。
    let (o, s) = run("param-type-same", "m.O");
    assert_eq!(o.as_deref(), Some("holds"), "{s}");
}

#[test]
fn the_resolution_of_a_callee_without_a_definition_is_part_of_its_body() {
    // m.f は定義のない m.g() の戻り値を m.O.t に書く。m.g の解決が本体である。
    let run = |name: &str, resolves: &str, plan: &str| {
        let repo = Repo::new(name);
        repo.write(".archsig/law/m.law", &LAW.replace("\"shop/**\"", "\"m.py\""));
        repo.map(
            "m.py",
            &format!(
                "{}{T_ATOMS}{}{resolves}",
                r#"{"kind": "observed", "subject": "m.py", "scope": "structure", "at": "m.py@blob:aaaaaaa"}
{"kind": "observed", "subject": "m.py", "scope": "meaning:payment-info", "at": "m.py@blob:aaaaaaa"}
{"kind": "resolves", "subject": "int", "object": "external:builtins", "at": "m.py:1@blob:aaaaaaa"}
"#,
                r#"{"kind": "writes", "subject": "m.f", "object": "m.O.t", "value": "m.g()", "at": "m.py:10@blob:aaaaaaa"}
"#
            ),
        );
        repo.write(".archsig/plans/p/plan.jsonl", plan);
        let s = repo.run(&["plan", "check", "p"]);
        (result(&s, "m.f")["outcome"].as_str().map(String::from), s)
    };
    let unrelated = "{\"kind\": \"removes\", \"subject\": \"m.O.n\", \"at\": \"plan:p\"}\n";
    // 解決の指す先が `?` なら、入力から本体が決まらない。
    let (o, s) = run("q-resolution", "{\"kind\": \"resolves\", \"subject\": \"m.g\", \"object\": \"?lib\", \"at\": \"m.py:2@blob:aaaaaaa\"}\n", unrelated);
    assert_ne!(o.as_deref(), Some("holds"), "{s}");
    // 変更前に解決がなく、候補が解決を足せば、本体が違う。
    let (o, s) = run("added-resolution", "", "{\"kind\": \"resolves\", \"subject\": \"m.g\", \"object\": \"external:lib2\", \"at\": \"plan:p\"}\n");
    assert_ne!(o.as_deref(), Some("holds"), "{s}");
}

#[test]
fn a_callee_body_with_a_question_mark_field_or_parameter_name_is_a_changed_body() {
    // 道のフィールドが `?` で始まる式は、前後で同じ字句でも、入力から決まらない。
    assert_eq!(rewritten_callee("q-field", "$o.?x"), (Some("silent".into()), Some("unchecked".into())));
    // `?` で始まる引数の名前も、入力から決まらない。
    let repo = Repo::new("q-param-name");
    repo.write(".archsig/law/m.law", &LAW.replace("\"shop/**\"", "\"m.py\""));
    repo.map(
        "m.py",
        &format!(
            "{}{T_ATOMS}{}",
            r#"{"kind": "observed", "subject": "m.py", "scope": "structure", "at": "m.py@blob:aaaaaaa"}
{"kind": "observed", "subject": "m.py", "scope": "meaning:payment-info", "at": "m.py@blob:aaaaaaa"}
{"kind": "resolves", "subject": "int", "object": "external:builtins", "at": "m.py:1@blob:aaaaaaa"}
"#,
            r#"{"kind": "writes", "subject": "m.f", "object": "m.O.t", "value": "m.g()", "at": "m.py:10@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.g", "value": "operation", "params": {"?p": "int"}, "at": "m.py:20@blob:aaaaaaa"}
{"kind": "returns", "subject": "m.g", "value": "1", "at": "m.py:21@blob:aaaaaaa"}
"#
        ),
    );
    repo.write(
        ".archsig/plans/p/plan.jsonl",
        r#"{"kind": "defines", "subject": "m.g", "value": "operation", "params": {"?p": "int"}, "file": "m.py", "at": "plan:p"}
{"kind": "returns", "subject": "m.g", "value": "1", "at": "plan:p"}
"#,
    );
    let s = repo.run(&["plan", "check", "p"]);
    assert_ne!(result(&s, "m.f")["outcome"], "holds", "{s}");
}

/// m.f は m.g() を m.O.t に書く。変更前の m.g の Atom を `before`、候補が書き直した m.g の Atom を `after` としたときの、m.f の結果。
fn callee_rewritten_as(name: &str, before: &str, after: &str) -> String {
    let repo = Repo::new(name);
    repo.write(".archsig/law/m.law", &LAW.replace("\"shop/**\"", "\"m.py\""));
    repo.map(
        "m.py",
        &format!(
            "{}{T_ATOMS}{}{before}",
            r#"{"kind": "observed", "subject": "m.py", "scope": "structure", "at": "m.py@blob:aaaaaaa"}
{"kind": "observed", "subject": "m.py", "scope": "meaning:payment-info", "at": "m.py@blob:aaaaaaa"}
{"kind": "resolves", "subject": "int", "object": "external:builtins", "at": "m.py:1@blob:aaaaaaa"}
"#,
            r#"{"kind": "writes", "subject": "m.f", "object": "m.O.t", "value": "m.g()", "at": "m.py:10@blob:aaaaaaa"}
"#
        ),
    );
    repo.write(".archsig/plans/p/plan.jsonl", after);
    let s = repo.run(&["plan", "check", "p"]);
    result(&s, "m.f")["outcome"].as_str().unwrap_or_default().to_string()
}

#[test]
fn the_body_of_a_callee_compares_kinds_and_parameter_names() {
    // Atom の種類だけが違う。
    let before = r#"{"kind": "defines", "subject": "m.g", "value": "operation", "params": {}, "at": "m.py:20@blob:aaaaaaa"}
{"kind": "reads", "subject": "m.g", "object": "m.O.n", "at": "m.py:21@blob:aaaaaaa"}
{"kind": "returns", "subject": "m.g", "value": "1", "at": "m.py:22@blob:aaaaaaa"}
"#;
    let after = |kind: &str| {
        format!(
            "{{\"kind\": \"defines\", \"subject\": \"m.g\", \"value\": \"operation\", \"params\": {{}}, \"file\": \"m.py\", \"at\": \"plan:p\"}}\n{{\"kind\": \"{kind}\", \"subject\": \"m.g\", \"object\": \"m.O.n\", \"at\": \"plan:p\"}}\n{{\"kind\": \"returns\", \"subject\": \"m.g\", \"value\": \"1\", \"at\": \"plan:p\"}}\n"
        )
    };
    assert_ne!(callee_rewritten_as("kind-changed", before, &after("receives")), "holds");
    assert_eq!(callee_rewritten_as("kind-same", before, &after("reads")), "holds");
    // 引数の名前だけが違う。
    let before = r#"{"kind": "defines", "subject": "m.g", "value": "operation", "params": {"x": "int"}, "at": "m.py:20@blob:aaaaaaa"}
{"kind": "returns", "subject": "m.g", "value": "1", "at": "m.py:21@blob:aaaaaaa"}
"#;
    let after = |p: &str| {
        format!(
            "{{\"kind\": \"defines\", \"subject\": \"m.g\", \"value\": \"operation\", \"params\": {{\"{p}\": \"int\"}}, \"file\": \"m.py\", \"at\": \"plan:p\"}}\n{{\"kind\": \"returns\", \"subject\": \"m.g\", \"value\": \"1\", \"at\": \"plan:p\"}}\n"
        )
    };
    assert_ne!(callee_rewritten_as("param-renamed", before, &after("y")), "holds");
    assert_eq!(callee_rewritten_as("param-same", before, &after("x")), "holds");
}

#[test]
fn the_path_to_a_removed_element_is_traced_in_the_structure_after_the_change() {
    // m.g は書き直さず、$o.a.x を返す。候補は m.O.a の型を m.A から m.B に書き換え、一つのフィールドを消す。
    // 変更後、m.g の $o.a.x は m.B.x を名指す。消える要素を使うかは、変更後の構造でたどって決める。
    let run = |name: &str, removes: &str| {
        let repo = Repo::new(name);
        repo.write(".archsig/law/m.law", &LAW.replace("\"shop/**\"", "\"m.py\""));
        repo.map(
            "m.py",
            r#"{"kind": "observed", "subject": "m.py", "scope": "structure", "at": "m.py@blob:aaaaaaa"}
{"kind": "observed", "subject": "m.py", "scope": "meaning:payment-info", "at": "m.py@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.O", "value": "type", "at": "m.py:1@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.O.a", "value": "field", "type": "m.A", "at": "m.py:2@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.A", "value": "type", "at": "m.py:3@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.A.x", "value": "field", "type": "int", "at": "m.py:4@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.B", "value": "type", "at": "m.py:5@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.B.x", "value": "field", "type": "int", "at": "m.py:6@blob:aaaaaaa"}
{"kind": "resolves", "subject": "int", "object": "external:builtins", "at": "m.py:1@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.g", "value": "operation", "params": {"o": "m.O"}, "at": "m.py:10@blob:aaaaaaa"}
{"kind": "returns", "subject": "m.g", "value": "$o.a.x", "at": "m.py:11@blob:aaaaaaa"}
"#,
        );
        repo.write(
            ".archsig/plans/p/plan.jsonl",
            &format!(
                "{{\"kind\": \"defines\", \"subject\": \"m.O.a\", \"value\": \"field\", \"type\": \"m.B\", \"file\": \"m.py\", \"at\": \"plan:p\"}}\n{{\"kind\": \"removes\", \"subject\": \"{removes}\", \"at\": \"plan:p\"}}\n"
            ),
        );
        let s = repo.run(&["plan", "check", "p"]);
        let missing = s["results"].as_array().unwrap().iter().any(|r| r["subject"] == "m.g" && r["kind"] == "missing");
        (missing, s)
    };
    // 変更前の型のフィールドを消しても、変更後の m.g はもう名指さない。
    let (missing, s) = run("old-type-field-removed", "m.A.x");
    assert!(!missing, "{s}");
    // 変更後の型のフィールドを消せば、m.g はそれを使う。
    let (missing, s) = run("new-type-field-removed", "m.B.x");
    assert!(missing, "{s}");
    // 変更後の型そのものを消しても、m.g はそのフィールドを使う。
    let (missing, s) = run("new-type-removed", "m.B");
    assert!(missing, "{s}");
}

#[test]
fn a_path_through_a_rewritten_type_that_was_not_read_returns_the_source_to_read() {
    // 候補は m.O.a の型を、定義を読んでいない c.py の m.C に書き換え、m.A.x を消す。
    // m.g の $o.a.x.y は、変更後の構造では m.C の先がたどれないので、消える要素を使うかが決まらない。読む所は c.py である。
    let repo = Repo::new("rewritten-type-unread");
    repo.write(".archsig/law/m.law", &LAW.replace("\"shop/**\"", "\"m.py\""));
    repo.map(
        "m.py",
        r#"{"kind": "observed", "subject": "m.py", "scope": "structure", "at": "m.py@blob:aaaaaaa"}
{"kind": "observed", "subject": "m.py", "scope": "meaning:payment-info", "at": "m.py@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.O", "value": "type", "at": "m.py:1@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.O.a", "value": "field", "type": "m.A", "at": "m.py:2@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.A", "value": "type", "at": "m.py:3@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.A.x", "value": "field", "type": "m.A", "at": "m.py:4@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.g", "value": "operation", "params": {"o": "m.O"}, "at": "m.py:10@blob:aaaaaaa"}
{"kind": "returns", "subject": "m.g", "value": "$o.a.x.y", "at": "m.py:11@blob:aaaaaaa"}
"#,
    );
    repo.write(
        ".archsig/plans/p/plan.jsonl",
        r#"{"kind": "defines", "subject": "m.O.a", "value": "field", "type": "m.C", "file": "m.py", "at": "plan:p"}
{"kind": "resolves", "subject": "m.C", "object": "c.py", "at": "plan:p"}
{"kind": "removes", "subject": "m.A.x", "at": "plan:p"}
"#,
    );
    let s = repo.run(&["plan", "check", "p"]);
    // 消える要素を使うかの沈黙(Law に依らない m.g の結果)が、c.py を読む所に持つ。
    let r = s["results"].as_array().unwrap().iter().find(|r| r["subject"] == "m.g" && r["law"].is_null()).cloned().unwrap_or_default();
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unread")), "{s}");
    assert!(s["next"].as_array().unwrap().iter().any(|n| n["read"] == "c.py" && n["decides"].as_array().unwrap().contains(&r["id"])), "{s}");
}

#[test]
fn a_path_through_a_question_mark_type_is_silent_on_removes() {
    // 候補は m.O.a の型を `?m.B` に書き換え、m.B.x を消す。m.g の $o.a.x が何を名指すかは決まらないので、消える要素を使うかで沈黙する。
    let repo = Repo::new("q-type-removes");
    repo.write(".archsig/law/m.law", &LAW.replace("\"shop/**\"", "\"m.py\""));
    repo.map(
        "m.py",
        r#"{"kind": "observed", "subject": "m.py", "scope": "structure", "at": "m.py@blob:aaaaaaa"}
{"kind": "observed", "subject": "m.py", "scope": "meaning:payment-info", "at": "m.py@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.P", "value": "type", "at": "m.py:7@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.P.b", "value": "field", "type": "?m.B", "at": "m.py:8@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.O", "value": "type", "at": "m.py:1@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.O.a", "value": "field", "type": "m.A", "at": "m.py:2@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.A", "value": "type", "at": "m.py:3@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.A.x", "value": "field", "type": "int", "at": "m.py:4@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.B", "value": "type", "at": "m.py:5@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.B.x", "value": "field", "type": "int", "at": "m.py:6@blob:aaaaaaa"}
{"kind": "resolves", "subject": "int", "object": "external:builtins", "at": "m.py:1@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.g", "value": "operation", "params": {"o": "m.O"}, "at": "m.py:10@blob:aaaaaaa"}
{"kind": "returns", "subject": "m.g", "value": "$o.a.x", "at": "m.py:11@blob:aaaaaaa"}
"#,
    );
    repo.write(
        ".archsig/plans/p/plan.jsonl",
        r#"{"kind": "defines", "subject": "m.O.a", "value": "field", "type": "?m.B", "file": "m.py", "at": "plan:p"}
{"kind": "removes", "subject": "m.B.x", "at": "plan:p"}
"#,
    );
    let s = repo.run(&["plan", "check", "p"]);
    let r = s["results"].as_array().unwrap().iter().find(|r| r["subject"] == "m.g" && r["law"].is_null()).cloned().unwrap_or_default();
    assert_eq!(r["outcome"], "silent", "{s}");
    // 読む所は、道の上で `?m.B` を書いた候補の定義(要素 m.O.a)である。同じ型を書いた道の外の m.P.b ではない。
    assert!(s["next"].as_array().unwrap().iter().any(|n| n["element"] == "m.O.a" && n["decides"].as_array().unwrap().contains(&r["id"])), "{s}");
}

#[test]
fn a_type_the_plan_redefines_that_was_not_read_before_is_unread_on_removes() {
    // m.g の $o.c.x は、変更前は定義を読んでいない c.py の m.C を通る。候補は m.C を定義し直し、ほかの要素を消す。
    // 元の m.C のフィールドは分からないので、消える要素を使うかは、変更前の構造で、c.py を読む所に持って沈黙する(マニュアル第5章 問い3)。
    let repo = Repo::new("redefined-unread-type");
    repo.write(".archsig/law/m.law", &LAW.replace("\"shop/**\"", "\"m.py\""));
    repo.map(
        "m.py",
        r#"{"kind": "observed", "subject": "m.py", "scope": "structure", "at": "m.py@blob:aaaaaaa"}
{"kind": "observed", "subject": "m.py", "scope": "meaning:payment-info", "at": "m.py@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.O", "value": "type", "at": "m.py:1@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.O.c", "value": "field", "type": "m.C", "at": "m.py:2@blob:aaaaaaa"}
{"kind": "resolves", "subject": "m.C", "object": "c.py", "at": "m.py:3@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.D", "value": "type", "at": "m.py:4@blob:aaaaaaa"}
{"kind": "resolves", "subject": "int", "object": "external:builtins", "at": "m.py:1@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.g", "value": "operation", "params": {"o": "m.O"}, "at": "m.py:10@blob:aaaaaaa"}
{"kind": "returns", "subject": "m.g", "value": "$o.c.x", "at": "m.py:11@blob:aaaaaaa"}
"#,
    );
    repo.write(
        ".archsig/plans/p/plan.jsonl",
        r#"{"kind": "defines", "subject": "m.C", "value": "type", "file": "c.py", "at": "plan:p"}
{"kind": "defines", "subject": "m.C.x", "value": "field", "type": "int", "file": "c.py", "at": "plan:p"}
{"kind": "removes", "subject": "m.D", "at": "plan:p"}
"#,
    );
    let s = repo.run(&["plan", "check", "p"]);
    let r = s["results"].as_array().unwrap().iter().find(|r| r["subject"] == "m.g" && r["law"].is_null()).cloned().unwrap_or_default();
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unread")), "{s}");
    assert!(s["next"].as_array().unwrap().iter().any(|n| n["read"] == "c.py" && n["decides"].as_array().unwrap().contains(&r["id"])), "{s}");
}

#[test]
fn a_type_that_pointed_to_an_external_before_is_not_silent_when_the_plan_redefines_it() {
    // 変更前の m.C は外部を指す。候補が m.C を定義し直しても、外部の型として扱うので(マニュアル第5章 問い3)、消える要素を使うかで沈黙しない。
    let repo = Repo::new("redefined-external-type");
    repo.write(".archsig/law/m.law", &LAW.replace("\"shop/**\"", "\"m.py\""));
    repo.map(
        "m.py",
        r#"{"kind": "observed", "subject": "m.py", "scope": "structure", "at": "m.py@blob:aaaaaaa"}
{"kind": "observed", "subject": "m.py", "scope": "meaning:payment-info", "at": "m.py@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.O", "value": "type", "at": "m.py:1@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.O.c", "value": "field", "type": "m.C", "at": "m.py:2@blob:aaaaaaa"}
{"kind": "resolves", "subject": "m.C", "object": "external:lib", "at": "m.py:3@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.D", "value": "type", "at": "m.py:4@blob:aaaaaaa"}
{"kind": "resolves", "subject": "int", "object": "external:builtins", "at": "m.py:1@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.g", "value": "operation", "params": {"o": "m.O"}, "at": "m.py:10@blob:aaaaaaa"}
{"kind": "returns", "subject": "m.g", "value": "$o.c.x", "at": "m.py:11@blob:aaaaaaa"}
"#,
    );
    repo.write(
        ".archsig/plans/p/plan.jsonl",
        r#"{"kind": "defines", "subject": "m.C", "value": "type", "file": "m.py", "at": "plan:p"}
{"kind": "defines", "subject": "m.C.x", "value": "field", "type": "int", "file": "m.py", "at": "plan:p"}
{"kind": "removes", "subject": "m.D", "at": "plan:p"}
"#,
    );
    let s = repo.run(&["plan", "check", "p"]);
    assert!(!s["results"].as_array().unwrap().iter().any(|r| r["subject"] == "m.g" && r["law"].is_null()), "{s}");
}

#[test]
fn the_field_right_under_a_redefined_unread_type_is_silent() {
    // 定義し直した未読の型 m.C は、受け継ぎが分からないので、直下のフィールド m.C.x も段で決まらない(設計 §3.3、§3.6)。
    // 候補が m.C.x を消しても、m.g が m.C.x を使うかは決まらず、変更前の m.C の読む所(c.py)で沈黙する。
    let repo = Repo::new("redefined-unread-type-field");
    repo.write(".archsig/law/m.law", &LAW.replace("\"shop/**\"", "\"m.py\""));
    repo.map(
        "m.py",
        r#"{"kind": "observed", "subject": "m.py", "scope": "structure", "at": "m.py@blob:aaaaaaa"}
{"kind": "observed", "subject": "m.py", "scope": "meaning:payment-info", "at": "m.py@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.O", "value": "type", "at": "m.py:1@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.O.c", "value": "field", "type": "m.C", "at": "m.py:2@blob:aaaaaaa"}
{"kind": "resolves", "subject": "m.C", "object": "c.py", "at": "m.py:3@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.D", "value": "type", "at": "m.py:4@blob:aaaaaaa"}
{"kind": "resolves", "subject": "int", "object": "external:builtins", "at": "m.py:1@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.g", "value": "operation", "params": {"o": "m.O"}, "at": "m.py:10@blob:aaaaaaa"}
{"kind": "returns", "subject": "m.g", "value": "$o.c.x", "at": "m.py:11@blob:aaaaaaa"}
"#,
    );
    repo.write(
        ".archsig/plans/p/plan.jsonl",
        r#"{"kind": "defines", "subject": "m.C", "value": "type", "file": "c.py", "at": "plan:p"}
{"kind": "defines", "subject": "m.C.y", "value": "field", "type": "int", "file": "c.py", "at": "plan:p"}
{"kind": "removes", "subject": "m.C.x", "at": "plan:p"}
"#,
    );
    let s = repo.run(&["plan", "check", "p"]);
    assert!(!s["results"].as_array().unwrap().iter().any(|r| r["subject"] == "m.g" && r["kind"] == "missing"), "{s}");
    let r = s["results"].as_array().unwrap().iter().find(|r| r["subject"] == "m.g" && r["law"].is_null()).unwrap();
    assert_eq!(r["outcome"], "silent", "{s}");
    assert!(s["next"].as_array().unwrap().iter().any(|n| n["read"] == "c.py" && n["decides"].as_array().unwrap().contains(&r["id"])), "{s}");
}

#[test]
fn a_question_mark_value_on_removes_returns_the_atom_that_has_it() {
    // m.g は `?m.B` の値を返す。n.py に `?m.B` を型に書いたフィールドと、`?m.B` を呼ぶ Atom があっても、読む所はその値を持つ Atom の場所 m.py である(マニュアル第5章 問い8)。
    let repo = Repo::new("q-value-removes");
    repo.write(".archsig/law/m.law", &LAW.replace("\"shop/**\"", "\"*.py\""));
    repo.map(
        "n.py",
        r#"{"kind": "observed", "subject": "n.py", "scope": "structure", "at": "n.py@blob:bbbbbbb"}
{"kind": "defines", "subject": "n.P", "value": "type", "at": "n.py:1@blob:bbbbbbb"}
{"kind": "defines", "subject": "n.P.z", "value": "field", "type": "?m.B", "at": "n.py:2@blob:bbbbbbb"}
{"kind": "defines", "subject": "n.k", "value": "operation", "params": {}, "at": "n.py:3@blob:bbbbbbb"}
{"kind": "calls", "subject": "n.k", "object": "?m.B", "at": "n.py:4@blob:bbbbbbb"}
"#,
    );
    repo.map(
        "m.py",
        r#"{"kind": "observed", "subject": "m.py", "scope": "structure", "at": "m.py@blob:aaaaaaa"}
{"kind": "observed", "subject": "m.py", "scope": "meaning:payment-info", "at": "m.py@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.D", "value": "type", "at": "m.py:4@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.g", "value": "operation", "params": {}, "at": "m.py:10@blob:aaaaaaa"}
{"kind": "returns", "subject": "m.g", "value": "?m.B", "at": "m.py:11@blob:aaaaaaa"}
"#,
    );
    repo.write(".archsig/plans/p/plan.jsonl", "{\"kind\": \"removes\", \"subject\": \"m.D\", \"at\": \"plan:p\"}\n");
    let s = repo.run(&["plan", "check", "p"]);
    let r = s["results"].as_array().unwrap().iter().find(|r| r["subject"] == "m.g" && r["law"].is_null()).cloned().unwrap_or_default();
    assert_eq!(r["outcome"], "silent", "{s}");
    let next: Vec<&Value> = s["next"].as_array().unwrap().iter().filter(|n| n["decides"].as_array().unwrap().contains(&r["id"])).collect();
    assert!(!next.is_empty() && next.iter().all(|n| n["read"] == "m.py"), "{s}");
}

#[test]
fn a_field_the_plan_defines_without_a_type_is_unresolved_on_removes() {
    // 変更前は m.C を定義し、m.C.x は名指すだけで定義を読んでいない。候補は m.C.x を型なしで定義する。
    // 候補が定義したフィールドの型は変更後の構造で決まらないので、`unresolved` で沈黙する(定義し直した型の例外は型だけに効く)。
    let repo = Repo::new("plan-untyped-field");
    repo.write(".archsig/law/m.law", &LAW.replace("\"shop/**\"", "\"m.py\""));
    repo.map(
        "m.py",
        r#"{"kind": "observed", "subject": "m.py", "scope": "structure", "at": "m.py@blob:aaaaaaa"}
{"kind": "observed", "subject": "m.py", "scope": "meaning:payment-info", "at": "m.py@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.O", "value": "type", "at": "m.py:1@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.O.c", "value": "field", "type": "m.C", "at": "m.py:2@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.C", "value": "type", "at": "m.py:3@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.D", "value": "type", "at": "m.py:4@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.g", "value": "operation", "params": {"o": "m.O"}, "at": "m.py:10@blob:aaaaaaa"}
{"kind": "returns", "subject": "m.g", "value": "$o.c.x.y", "at": "m.py:11@blob:aaaaaaa"}
"#,
    );
    repo.write(
        ".archsig/plans/p/plan.jsonl",
        r#"{"kind": "defines", "subject": "m.C.x", "value": "field", "file": "m.py", "at": "plan:p"}
{"kind": "removes", "subject": "m.D", "at": "plan:p"}
"#,
    );
    let s = repo.run(&["plan", "check", "p"]);
    let r = s["results"].as_array().unwrap().iter().find(|r| r["subject"] == "m.g" && r["law"].is_null()).cloned().unwrap_or_default();
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unresolved")), "{s}");
}

#[test]
fn a_question_mark_name_on_removes_returns_the_atom_that_has_it_even_if_the_plan_names_it() {
    // m.g は `?m.B` を返す。候補も、定義し直した m.h の呼び出し先に同じ `?m.B` を書く。
    // m.g の消える要素を使うかの沈黙は、`?m.B` を持つ m.g の Atom の場所 m.py を返す(マニュアル第5章 問い8)。候補の要素 m.h ではない。
    let repo = Repo::new("q-name-plan-removes");
    repo.write(".archsig/law/m.law", &LAW.replace("\"shop/**\"", "\"m.py\""));
    repo.map(
        "m.py",
        r#"{"kind": "observed", "subject": "m.py", "scope": "structure", "at": "m.py@blob:aaaaaaa"}
{"kind": "observed", "subject": "m.py", "scope": "meaning:payment-info", "at": "m.py@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.D", "value": "type", "at": "m.py:4@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.h", "value": "operation", "params": {}, "at": "m.py:5@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.g", "value": "operation", "params": {}, "at": "m.py:10@blob:aaaaaaa"}
{"kind": "returns", "subject": "m.g", "value": "?m.B", "at": "m.py:11@blob:aaaaaaa"}
"#,
    );
    repo.write(
        ".archsig/plans/p/plan.jsonl",
        r#"{"kind": "defines", "subject": "m.h", "value": "operation", "params": {}, "file": "m.py", "at": "plan:p"}
{"kind": "calls", "subject": "m.h", "object": "?m.B", "at": "plan:p"}
{"kind": "removes", "subject": "m.D", "at": "plan:p"}
"#,
    );
    let s = repo.run(&["plan", "check", "p"]);
    let r = s["results"].as_array().unwrap().iter().find(|r| r["subject"] == "m.g" && r["law"].is_null()).cloned().unwrap_or_default();
    assert_eq!(r["outcome"], "silent", "{s}");
    let next: Vec<&Value> = s["next"].as_array().unwrap().iter().filter(|n| n["decides"].as_array().unwrap().contains(&r["id"])).collect();
    assert!(!next.is_empty() && next.iter().all(|n| n["read"] == "m.py"), "{s}");
}

#[test]
fn a_path_through_a_question_mark_parameter_type_returns_the_operation_definition() {
    // m.g の引数 o の型が `?m.O` なので、$o.a が何を名指すかは決まらない。読む所は、その型を書いた m.g の定義のソース g.py である。
    let repo = Repo::new("q-param-type-removes");
    repo.write(".archsig/law/m.law", &LAW.replace("\"shop/**\"", "\"*.py\""));
    repo.map(
        "m.py",
        r#"{"kind": "observed", "subject": "m.py", "scope": "structure", "at": "m.py@blob:aaaaaaa"}
{"kind": "observed", "subject": "m.py", "scope": "meaning:payment-info", "at": "m.py@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.D", "value": "type", "at": "m.py:4@blob:aaaaaaa"}
"#,
    );
    repo.map(
        "g.py",
        r#"{"kind": "observed", "subject": "g.py", "scope": "structure", "at": "g.py@blob:ccccccc"}
{"kind": "defines", "subject": "m.g", "value": "operation", "params": {"o": "?m.O"}, "at": "g.py:10@blob:ccccccc"}
"#,
    );
    repo.map(
        "h.py",
        r#"{"kind": "observed", "subject": "h.py", "scope": "structure", "at": "h.py@blob:ddddddd"}
{"kind": "returns", "subject": "m.g", "value": "$o.a", "at": "h.py:11@blob:ddddddd"}
"#,
    );
    repo.write(".archsig/plans/p/plan.jsonl", "{\"kind\": \"removes\", \"subject\": \"m.D\", \"at\": \"plan:p\"}\n");
    let s = repo.run(&["plan", "check", "p"]);
    let r = s["results"].as_array().unwrap().iter().find(|r| r["subject"] == "m.g" && r["law"].is_null()).cloned().unwrap_or_default();
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unresolved")), "{s}");
    let next: Vec<&Value> = s["next"].as_array().unwrap().iter().filter(|n| n["decides"].as_array().unwrap().contains(&r["id"])).collect();
    assert!(!next.is_empty() && next.iter().all(|n| n["read"] == "g.py"), "{s}");
}

#[test]
fn changes_keep_of_an_argument_whose_owner_maps_to_an_unread_operation_is_unread() {
    // 意味を持つ引数 m.f.$x。候補は m.f を消し、定義を読んでいない g.py の m.g へ対応させる。
    // m.g に同じ名前の引数があるかは決まらないので、引数の対応があるかも決まらない。`unread` で沈黙し、g.py を返す(設計 §5.1)。
    let law = r#"sources "*.py"

reading module = dir(depth: 1)

meaning payment-info on field
  "注文の支払いを特定する値。"

law payment-info-kept
  "決済情報は変更の後も残る。"
  about payment-info
  changes keep
"#;
    let repo = Repo::new("keep-unread-owner");
    repo.write(".archsig/law/m.law", law);
    repo.map(
        "m.py",
        r#"{"kind": "observed", "subject": "m.py", "scope": "structure", "at": "m.py@blob:aaaaaaa"}
{"kind": "observed", "subject": "m.py", "scope": "meaning:payment-info", "at": "m.py@blob:aaaaaaa"}
{"kind": "resolves", "subject": "int", "object": "external:builtins", "at": "m.py:1@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.f", "value": "operation", "params": {"x": "int"}, "at": "m.py:2@blob:aaaaaaa"}
{"kind": "meaning", "subject": "m.f.$x", "meaning": "payment-info", "uses": ["m.py:3@blob:aaaaaaa"], "at": "m.py:2@blob:aaaaaaa"}
{"kind": "resolves", "subject": "m.g", "object": "g.py", "at": "m.py:4@blob:aaaaaaa"}
"#,
    );
    repo.write(
        ".archsig/plans/p/plan.jsonl",
        "{\"kind\": \"removes\", \"subject\": \"m.f\", \"at\": \"plan:p\"}\n{\"kind\": \"corresponds\", \"subject\": \"m.f\", \"object\": \"m.g\", \"at\": \"plan:p\"}\n",
    );
    let s = repo.run(&["plan", "check", "p"]);
    let r = result(&s, "m.f.$x");
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unread")), "{s}");
    assert!(s["next"].as_array().unwrap().iter().any(|n| n["read"] == "g.py" && n["decides"].as_array().unwrap().contains(&r["id"])), "{s}");
}

/// f(o) は `return m.g()` で、g は o.u(payment-info)に書く。`calls` を `returns` より前に書き、`returns` の `at` は return 文の
/// 最後の行にする(第3章の `returns`)。`calls_at` と `returns_at` は観測した行。候補は g の書く値を変える。
fn return_call(name: &str, calls_at: &str, returns_at: &str) -> Value {
    let repo = Repo::new(name);
    repo.write(".archsig/law/m.law", &LAW.replace("\"shop/**\"", "\"m.py\""));
    repo.map(
        "m.py",
        &r#"{"kind": "observed", "subject": "m.py", "scope": "structure", "at": "m.py@blob:aaaaaaa"}
{"kind": "observed", "subject": "m.py", "scope": "meaning:payment-info", "at": "m.py@blob:aaaaaaa"}
{"kind": "resolves", "subject": "int", "object": "external:builtins", "at": "m.py:1@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.O", "value": "type", "at": "m.py:1@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.O.u", "value": "field", "type": "int", "at": "m.py:2@blob:aaaaaaa"}
{"kind": "meaning", "subject": "m.O.u", "meaning": "payment-info", "uses": ["m.py:5@blob:aaaaaaa"], "at": "m.py:2@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.g", "value": "operation", "params": {"o": "m.O"}, "at": "m.py:4@blob:aaaaaaa"}
{"kind": "writes", "subject": "m.g", "object": "m.O.u", "value": "1", "at": "m.py:5@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.f", "value": "operation", "params": {"o": "m.O"}, "at": "m.py:9@blob:aaaaaaa"}
{"kind": "calls", "subject": "m.f", "object": "m.g", "at": "m.py:CALLS@blob:aaaaaaa"}
{"kind": "passes", "subject": "m.f->m.g", "object": "m.g.$o", "value": "$o", "at": "m.py:CALLS@blob:aaaaaaa"}
{"kind": "returns", "subject": "m.f", "value": "m.g($o)", "at": "m.py:RETURNS@blob:aaaaaaa"}
"#
        .replace("CALLS", calls_at)
        .replace("RETURNS", returns_at),
    );
    repo.write(
        ".archsig/plans/p/plan.jsonl",
        r#"{"kind": "defines", "subject": "m.g", "value": "operation", "params": {"o": "m.O"}, "file": "m.py", "at": "plan:p"}
{"kind": "writes", "subject": "m.g", "object": "m.O.u", "value": "2", "at": "plan:p"}
"#,
    );
    let s = repo.run(&["plan", "check", "p"]);
    result(&s, "m.f").clone()
}

#[test]
fn a_call_in_a_returned_expression_is_made_when_observed_before_the_return() {
    // 一行の `return m.g(o)`: 同じ行で `calls` を `returns` より前に書けば、f は g を呼び、o.u に書く値が変わる。
    let r = return_call("return-call-one-line", "10", "10");
    assert_eq!((r["outcome"].as_str(), r["kind"].as_str()), (Some("fails"), Some("counterexample")), "{r}");
    // 複数の行にわたる return 文: `returns` の `at` を最後の行にすれば、前の行の呼び出しが先に並ぶ。
    let r = return_call("return-call-lines", "10", "12");
    assert_eq!((r["outcome"].as_str(), r["kind"].as_str()), (Some("fails"), Some("counterexample")), "{r}");
}

#[test]
fn a_module_that_imports_is_not_an_element_to_correspond() {
    // `imports` の `subject` はモジュールで、要素ではない(第3章)。自分自身への対応に入れず、操作の組にもならない。
    let repo = Repo::new("imports-module");
    repo.write(".archsig/law/m.law", &LAW.replace("\"shop/**\"", "\"m.py\""));
    repo.map("m.py", r#"{"kind": "observed", "subject": "m.py", "scope": "structure", "at": "m.py@blob:aaaaaaa"}
{"kind": "observed", "subject": "m.py", "scope": "meaning:payment-info", "at": "m.py@blob:aaaaaaa"}
{"kind": "imports", "subject": "m", "object": "n", "at": "m.py:1@blob:aaaaaaa"}
{"kind": "resolves", "subject": "int", "object": "external:builtins", "at": "m.py:1@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.O", "value": "type", "at": "m.py:2@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.O.u", "value": "field", "type": "int", "at": "m.py:3@blob:aaaaaaa"}
{"kind": "meaning", "subject": "m.O.u", "meaning": "payment-info", "uses": ["m.py:6@blob:aaaaaaa"], "at": "m.py:3@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.f", "value": "operation", "params": {"o": "m.O"}, "at": "m.py:5@blob:aaaaaaa"}
{"kind": "writes", "subject": "m.f", "object": "m.O.u", "value": "1", "at": "m.py:6@blob:aaaaaaa"}
"#);
    repo.write(
        ".archsig/plans/p/plan.jsonl",
        r#"{"kind": "defines", "subject": "m.f", "value": "operation", "params": {"o": "m.O"}, "file": "m.py", "at": "plan:p"}
{"kind": "writes", "subject": "m.f", "object": "m.O.u", "value": "1", "at": "plan:p"}
"#,
    );
    let s = repo.run(&["plan", "check", "p"]);
    assert_eq!(result(&s, "m.f")["outcome"], "holds", "{s}");
    assert!(s["results"].as_array().unwrap().iter().all(|r| r["outcome"] == "holds"), "{s}");
    assert_eq!(s["next"], serde_json::json!([]), "{s}");
}

/// 変更前: m.O.a の型は m.A。f(o) は o.a.x に 1 を書く(`via [m.O.a]`、`object m.A.x`)。
/// 候補は m.O.a の型を m.B に書き換え、f は書き直さない。`plan` は候補に足す Atom。
fn retyped_via(name: &str, plan: &str) -> Value {
    result(&retyped_via_all(name, plan), "m.f").clone()
}

/// `retyped_via` の実行の結果の全体。
fn retyped_via_all(name: &str, plan: &str) -> Value {
    let repo = Repo::new(name);
    repo.write(".archsig/law/m.law", &LAW.replace("\"shop/**\"", "\"m.py\""));
    repo.map("m.py", r#"{"kind": "observed", "subject": "m.py", "scope": "structure", "at": "m.py@blob:aaaaaaa"}
{"kind": "observed", "subject": "m.py", "scope": "meaning:payment-info", "at": "m.py@blob:aaaaaaa"}
{"kind": "resolves", "subject": "int", "object": "external:builtins", "at": "m.py:1@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.A", "value": "type", "at": "m.py:1@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.A.x", "value": "field", "type": "int", "at": "m.py:2@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.B", "value": "type", "at": "m.py:3@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.B.x", "value": "field", "type": "int", "at": "m.py:4@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.O", "value": "type", "at": "m.py:5@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.O.a", "value": "field", "type": "m.A", "at": "m.py:6@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.O.u", "value": "field", "type": "int", "at": "m.py:7@blob:aaaaaaa"}
{"kind": "meaning", "subject": "m.O.u", "meaning": "payment-info", "uses": ["m.py:11@blob:aaaaaaa"], "at": "m.py:7@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.f", "value": "operation", "params": {"o": "m.O"}, "at": "m.py:9@blob:aaaaaaa"}
{"kind": "writes", "subject": "m.f", "via": ["m.O.a"], "object": "m.A.x", "value": "1", "at": "m.py:10@blob:aaaaaaa"}
"#);
    repo.write(
        ".archsig/plans/p/plan.jsonl",
        &format!("{}{plan}", r#"{"kind": "defines", "subject": "m.O.a", "value": "field", "type": "m.B", "file": "m.py", "at": "plan:p"}
"#),
    );
    repo.run(&["plan", "check", "p"])
}


#[test]
fn removing_the_field_of_the_old_type_is_not_missing_and_the_new_one_is() {
    // 書き換えた後の f の書き込みは m.B.x を名指し、m.A.x はもう名指さない(f は書き込みだけを持つ)。
    let s = retyped_via_all("retyped-via-remove-old", "{\"kind\": \"removes\", \"subject\": \"m.A.x\", \"at\": \"plan:p\"}\n");
    assert!(s["results"].as_array().unwrap().iter().all(|r| r["subject"] != "m.f" || r["kind"] != "missing"), "{s}");
    let r = retyped_via("retyped-via-remove-new", "{\"kind\": \"removes\", \"subject\": \"m.B.x\", \"at\": \"plan:p\"}\n");
    assert_eq!((r["outcome"].as_str(), r["kind"].as_str()), (Some("fails"), Some("missing")), "{r}");
}

#[test]
fn a_write_path_names_the_fields_before_a_question_mark() {
    // 書き込みの道の後ろに `?` の名前があっても、その前のフィールド m.O.a は名指す。候補が m.O.a を消すと missing。
    let repo = Repo::new("write-path-question");
    repo.write(".archsig/law/m.law", &LAW.replace("\"shop/**\"", "\"m.py\""));
    repo.map("m.py", r#"{"kind": "observed", "subject": "m.py", "scope": "structure", "at": "m.py@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.A", "value": "type", "at": "m.py:1@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.O", "value": "type", "at": "m.py:2@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.O.a", "value": "field", "type": "m.A", "at": "m.py:3@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.f", "value": "operation", "params": {"o": "m.O"}, "at": "m.py:5@blob:aaaaaaa"}
{"kind": "writes", "subject": "m.f", "via": ["m.O.a"], "object": "?x", "value": "1", "at": "m.py:6@blob:aaaaaaa"}
"#);
    repo.write(".archsig/plans/p/plan.jsonl", "{\"kind\": \"removes\", \"subject\": \"m.O.a\", \"at\": \"plan:p\"}\n");
    let s = repo.run(&["plan", "check", "p"]);
    let r = result(&s, "m.f");
    assert_eq!((r["outcome"].as_str(), r["kind"].as_str()), (Some("fails"), Some("missing")), "{s}");
}


#[test]
fn a_write_path_that_begins_with_a_question_mark_names_nothing_after_it() {
    // 書き込みの道の最初が `?` の名前なら、その先は名指す要素が決まらない。後ろの m.A.x を字句で名指さない。
    let repo = Repo::new("write-path-leading-question");
    repo.write(".archsig/law/m.law", &LAW.replace("\"shop/**\"", "\"m.py\""));
    repo.map("m.py", r#"{"kind": "observed", "subject": "m.py", "scope": "structure", "at": "m.py@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.A", "value": "type", "at": "m.py:1@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.A.x", "value": "field", "type": "int", "at": "m.py:2@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.f", "value": "operation", "params": {}, "at": "m.py:5@blob:aaaaaaa"}
{"kind": "writes", "subject": "m.f", "via": ["?m.O.a"], "object": "m.A.x", "value": "1", "at": "m.py:6@blob:aaaaaaa"}
"#);
    repo.write(".archsig/plans/p/plan.jsonl", "{\"kind\": \"removes\", \"subject\": \"m.A.x\", \"at\": \"plan:p\"}\n");
    let s = repo.run(&["plan", "check", "p"]);
    assert!(s["results"].as_array().unwrap().iter().all(|r| r["kind"] != "missing"), "{s}");
    assert!(s["results"].as_array().unwrap().iter().any(|r| r["outcome"] == "silent"), "{s}");
}

#[test]
fn a_correspondence_with_one_external_end_is_silent() {
    // m.clear は m.O.pay(payment-info)に 0 を書く。候補は m.clear を外部の lib.clear に対応させて消す。
    // 片方だけが外部の組は、外部の端の種類が決まらないので沈黙する。両端が外部なら組にしない。
    let run = |name: &str, from_external: bool, extra: &str| {
        let repo = Repo::new(name);
        repo.write(".archsig/law/m.law", &LAW.replace("\"shop/**\"", "\"m.py\""));
        let ext = if from_external { "{\"kind\": \"resolves\", \"subject\": \"lib.old\", \"object\": \"external:lib\", \"at\": \"m.py:1@blob:aaaaaaa\"}\n" } else { "" };
        repo.map("m.py", &format!("{}{ext}{extra}", r#"{"kind": "observed", "subject": "m.py", "scope": "structure", "at": "m.py@blob:aaaaaaa"}
{"kind": "observed", "subject": "m.py", "scope": "meaning:payment-info", "at": "m.py@blob:aaaaaaa"}
{"kind": "resolves", "subject": "int", "object": "external:builtins", "at": "m.py:1@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.O", "value": "type", "at": "m.py:2@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.O.pay", "value": "field", "type": "int", "at": "m.py:3@blob:aaaaaaa"}
{"kind": "meaning", "subject": "m.O.pay", "meaning": "payment-info", "uses": ["m.py:6@blob:aaaaaaa"], "at": "m.py:3@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.clear", "value": "operation", "params": {"o": "m.O"}, "at": "m.py:5@blob:aaaaaaa"}
{"kind": "writes", "subject": "m.clear", "object": "m.O.pay", "value": "0", "at": "m.py:6@blob:aaaaaaa"}
"#));
        let from = if from_external { "lib.old" } else { "m.clear" };
        repo.write(".archsig/plans/p/plan.jsonl", &format!("{{\"kind\": \"resolves\", \"subject\": \"lib.clear\", \"object\": \"external:lib\", \"at\": \"plan:p\"}}\n{{\"kind\": \"corresponds\", \"subject\": \"{from}\", \"object\": \"lib.clear\", \"at\": \"plan:p\"}}\n{}", if from_external { "" } else { "{\"kind\": \"removes\", \"subject\": \"m.clear\", \"at\": \"plan:p\"}\n" }));
        repo.run(&["plan", "check", "p"])
    };
    // 定義のある m.clear に外部を指す `resolves` があっても、m.clear は外部の要素ではない(設計 §3.3)。
    for (name, extra) in [("one-external-end", ""), ("defined-with-external-resolves", "{\"kind\": \"resolves\", \"subject\": \"m.clear\", \"object\": \"external:lib\", \"at\": \"m.py:1@blob:aaaaaaa\"}\n")] {
        let s = run(name, false, extra);
        let law = s["results"].as_array().unwrap().iter().filter(|r| r["law"] == "payment-follows-order").collect::<Vec<_>>();
        assert!(law.iter().any(|r| r["outcome"] == "silent" && r["reason"] == "unresolved") && !law.iter().any(|r| r["outcome"] == "holds"), "{name}: {s}");
    }
    let s = run("two-external-ends", true, "");
    assert!(!s["results"].as_array().unwrap().iter().any(|r| r["outcome"] == "silent" || r["subject"] == "lib.old" || r["subject"] == "lib.clear"), "{s}");
}

#[test]
fn a_correspondence_from_an_external_end_returns_what_the_other_end_needs() {
    // 変更前の lib.old は外部。候補は lib.old を、読んでいない n.py に解決する m.new に対応させる。
    // 外部でない端 m.new の種類は n.py を読めば決まるので、n.py を読む所として返す。
    let repo = Repo::new("external-from-end");
    repo.write(".archsig/law/m.law", &LAW.replace("\"shop/**\"", "\"m.py\""));
    repo.map("m.py", r#"{"kind": "observed", "subject": "m.py", "scope": "structure", "at": "m.py@blob:aaaaaaa"}
{"kind": "observed", "subject": "m.py", "scope": "meaning:payment-info", "at": "m.py@blob:aaaaaaa"}
{"kind": "resolves", "subject": "lib.old", "object": "external:lib", "at": "m.py:1@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.O", "value": "type", "at": "m.py:2@blob:aaaaaaa"}
"#);
    repo.write(".archsig/plans/p/plan.jsonl", r#"{"kind": "resolves", "subject": "m.new", "object": "n.py", "at": "plan:p"}
{"kind": "corresponds", "subject": "lib.old", "object": "m.new", "at": "plan:p"}
"#);
    let s = repo.run(&["plan", "check", "p"]);
    let r = result(&s, "m.new");
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unread")), "{s}");
    assert!(s["next"].as_array().unwrap().iter().any(|n| n["read"] == "n.py" && n["decides"].as_array().unwrap().contains(&r["id"])), "{s}");
}

#[test]
fn a_name_not_settled_by_its_head_is_not_passed_over_for_removes() {
    // m.o は書き直さず、値 m.C.f.g() で呼ぶ。m.C.f.g の頭 m.C.f はフィールドで型ではないので、名前は決まらない(設計 §3.3 規則 8)。
    // 型を読んでいない頭 m.T の下の m.T.g() も、受け継ぎが分からないので名指す要素が決まらない。
    // どちらも、候補が m.U.g を消すとき、消える要素を使わないとは言えないので沈黙する(設計 §3.6)。
    for (name, value) in [("head-is-a-field", "m.C.f.g()"), ("head-type-unread", "m.T.g()")] {
        let repo = Repo::new(name);
        repo.write(".archsig/law/m.law", &LAW.replace("\"shop/**\"", "\"m.py\""));
        repo.map("m.py", &format!(
            "{}{{\"kind\": \"writes\", \"subject\": \"m.o\", \"object\": \"m.C.p\", \"value\": \"{value}\", \"at\": \"m.py:21@blob:aaaaaaa\"}}\n",
            r#"{"kind": "observed", "subject": "m.py", "scope": "structure", "at": "m.py@blob:aaaaaaa"}
{"kind": "observed", "subject": "m.py", "scope": "meaning:payment-info", "at": "m.py@blob:aaaaaaa"}
{"kind": "resolves", "subject": "int", "object": "external:builtins", "at": "m.py:1@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.C", "value": "type", "at": "m.py:2@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.C.f", "value": "field", "type": "m.U", "at": "m.py:3@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.C.p", "value": "field", "type": "int", "at": "m.py:4@blob:aaaaaaa"}
{"kind": "meaning", "subject": "m.C.p", "meaning": "payment-info", "uses": ["m.py:21@blob:aaaaaaa"], "at": "m.py:4@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.U", "value": "type", "at": "m.py:5@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.U.g", "value": "operation", "params": {}, "at": "m.py:6@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.k", "value": "operation", "params": {"t": "m.T"}, "at": "m.py:10@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.o", "value": "operation", "params": {}, "at": "m.py:20@blob:aaaaaaa"}
"#
        ));
        repo.write(".archsig/plans/p/plan.jsonl", "{\"kind\": \"removes\", \"subject\": \"m.U.g\", \"at\": \"plan:p\"}\n");
        let s = repo.run(&["plan", "check", "p"]);
        let silent = s["results"].as_array().unwrap().iter().any(|r| r["subject"] == "m.o" && r["law"].is_null() && r["outcome"] == "silent");
        assert!(silent, "{name}: {s}");
    }
}

#[test]
fn a_removed_name_the_old_structure_only_names_is_not_unread_below() {
    // 変更前は m.S.p を resolves で名指すだけで、定義を読んでいない。候補が m.S.p を消す。
    // 変更前の構造で書いた場所より先をたどるときも、removes した要素は沈黙の対象にしない(設計 §5.4)。
    let atoms = format!("{O_S}{}{F_WRITES_A}", r#"{"kind": "defines", "subject": "m.S", "value": "type", "at": "m.py:3@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.S.q", "value": "field", "type": "int", "at": "m.py:4@blob:aaaaaaa"}
{"kind": "resolves", "subject": "m.S.p", "object": "b.py", "at": "m.py:1@blob:aaaaaaa"}
"#);
    let plan = format!("{PLAN_WRITES_B}{}", "{\"kind\": \"removes\", \"subject\": \"m.S.p\", \"at\": \"plan:p\"}\n");
    let (s, r) = below_case("below-removed-only-named", &atoms, &plan);
    assert_eq!(r["outcome"], "holds", "{s}");
}

#[test]
fn a_name_under_an_unsettled_type_is_silent_on_every_path_for_removes() {
    // m.C は定義し直した読んでいない型、m.Svc は読んでいない型(引数の型として名指されるだけ)。候補はその直下の名前を消す。
    // 直下の名前が何を指すかは型の受け継ぎで決まるので、道、列、呼び出し、式の中の呼び出しのどれで名指しても、`missing` にせず沈黙する(設計 §3.3、§3.6)。
    let atoms = |h: &str| {
        format!(
            "{}{h}\n",
            r#"{"kind": "observed", "subject": "m.py", "scope": "structure", "at": "m.py@blob:aaaaaaa"}
{"kind": "observed", "subject": "m.py", "scope": "meaning:payment-info", "at": "m.py@blob:aaaaaaa"}
{"kind": "resolves", "subject": "int", "object": "external:builtins", "at": "m.py:1@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.O", "value": "type", "at": "m.py:1@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.O.c", "value": "field", "type": "m.C", "at": "m.py:2@blob:aaaaaaa"}
{"kind": "resolves", "subject": "m.C", "object": "c.py", "at": "m.py:3@blob:aaaaaaa"}
{"kind": "resolves", "subject": "m.Svc", "object": "svc.py", "at": "m.py:3@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.g", "value": "operation", "params": {"o": "m.O", "s": "m.Svc"}, "at": "m.py:10@blob:aaaaaaa"}
"#
        )
    };
    let plan = r#"{"kind": "defines", "subject": "m.C", "value": "type", "file": "c.py", "at": "plan:p"}
{"kind": "removes", "subject": "m.C.x", "at": "plan:p"}
{"kind": "removes", "subject": "m.Svc.run", "at": "plan:p"}
"#;
    for (name, h) in [
        ("unsettled-path", r#"{"kind": "returns", "subject": "m.g", "value": "$o.c.x", "at": "m.py:11@blob:aaaaaaa"}"#),
        ("unsettled-calls", r#"{"kind": "calls", "subject": "m.g", "object": "m.C.x", "at": "m.py:11@blob:aaaaaaa"}"#),
        ("unsettled-expression-call", r#"{"kind": "returns", "subject": "m.g", "value": "m.C.x()", "at": "m.py:11@blob:aaaaaaa"}"#),
        ("unsettled-unread-calls", r#"{"kind": "calls", "subject": "m.g", "object": "m.Svc.run", "at": "m.py:11@blob:aaaaaaa"}"#),
        ("unsettled-unread-write", r#"{"kind": "writes", "subject": "m.g", "object": "m.Svc.run", "value": "1", "at": "m.py:11@blob:aaaaaaa"}"#),
        ("unsettled-unread-path", r#"{"kind": "returns", "subject": "m.g", "value": "$s.run", "at": "m.py:11@blob:aaaaaaa"}"#),
    ] {
        let repo = Repo::new(name);
        repo.write(".archsig/law/m.law", &LAW.replace("\"shop/**\"", "\"m.py\""));
        repo.map("m.py", &atoms(h));
        repo.write(".archsig/plans/p/plan.jsonl", plan);
        let s = repo.run(&["plan", "check", "p"]);
        assert!(!s["results"].as_array().unwrap().iter().any(|r| r["kind"] == "missing"), "{name}: {s}");
        assert!(s["results"].as_array().unwrap().iter().any(|r| r["subject"] == "m.g" && r["outcome"] == "silent"), "{name}: {s}");
    }
}
