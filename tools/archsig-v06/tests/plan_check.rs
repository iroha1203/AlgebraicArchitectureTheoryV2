//! AC5・AC8: `archsig plan check` と `archsig show`(マニュアル第2章の題材、第5章 問い3、第6章)。

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
    let repo = shop("meaning");
    repo.map("shop/shipping/address.py", ADDRESS);
    // Order.payment_ref のソースで、payment-info の意味を読んでいない。
    repo.map("shop/order/model.py", &ORDER.replace(
        r#"{"kind": "observed", "subject": "shop/order/model.py", "scope": "meaning:payment-info", "at": "shop/order/model.py@blob:1d9e3b4"}
"#,
        "",
    ));
    repo.write(".archsig/plans/split-order/plan.jsonl", SPLIT);
    let s = repo.run(&["plan", "check", "split-order"]);
    let r = result(&s, UPDATE);
    assert_eq!(r["reason"], "unread", "{s}");
    assert!(
        s["next"].as_array().unwrap().iter().any(|n| n["read"] == "shop/order/model.py" && n["scope"] == "meaning:payment-info"),
        "書いたフィールドが意味を持つかは、そのソースの意味を読めば決まる: {s}"
    );
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
    let repo = Repo::new("nested-via-meaning");
    repo.write(".archsig/law/m.law", &LAW.replace("\"shop/**\"", "\"*.py\""));
    repo.map("a.py", r#"{"kind": "observed", "subject": "a.py", "scope": "structure", "at": "a.py@blob:bbbbbbb"}
{"kind": "defines", "subject": "m.O", "value": "type", "at": "a.py:1@blob:bbbbbbb"}
{"kind": "defines", "subject": "m.O.s", "value": "field", "type": "m.S", "at": "a.py:2@blob:bbbbbbb"}
"#);
    repo.map("m.py", &NESTED.lines().filter(|l| !l.contains("\"subject\": \"m.O")).map(|l| format!("{l}\n")).collect::<String>());
    repo.write(
        ".archsig/plans/p/plan.jsonl",
        r#"{"kind": "defines", "subject": "m.f", "value": "operation", "params": {"o": "m.O", "t": "m.S"}, "file": "m.py", "at": "plan:p"}
{"kind": "writes", "subject": "m.f", "via": ["m.O.s"], "object": "m.S.p", "value": "2", "at": "plan:p"}
"#,
    );
    let s = repo.run(&["plan", "check", "p"]);
    let r = result(&s, "m.f");
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unread")), "{s}");
    assert!(s["next"].as_array().unwrap().iter().any(|n| n["read"] == "a.py" && n["scope"] == "meaning:payment-info"), "{s}");
}

#[test]
fn a_question_mark_in_via_returns_the_atom() {
    let repo = Repo::new("nested-via-question");
    repo.write(".archsig/law/m.law", &LAW.replace("\"shop/**\"", "\"m.py\""));
    repo.map("m.py", &NESTED.replace(r#""via": ["m.O.s"]"#, r#""via": ["?o.s"]"#));
    repo.write(".archsig/plans/p/plan.jsonl", "{\"kind\": \"removes\", \"subject\": \"m.X\", \"at\": \"plan:p\"}\n");
    let s = repo.run(&["plan", "check", "p"]);
    let r = result(&s, "m.f");
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unresolved")), "{s}");
    assert!(s["next"].as_array().unwrap().iter().any(|n| n["read"] == "m.py"), "via の ? の名前の沈黙は、その Atom の場所を返す: {s}");
}

#[test]
fn a_nested_write_under_a_field_with_the_meaning_compares_the_updated_value() {
    // 意味は via のフィールド m.O.s(S の値)にある。その中の p に書くと、[m.O.s] の値は書き換えた値になる。
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
    assert_eq!(same["outcome"], "holds", "{same}");
    let changed = with_meaning("nested-head-changed", r#"{"kind": "writes", "subject": "m.f", "via": ["m.O.s"], "object": "m.S.p", "value": "2", "at": "plan:p"}"#);
    assert_eq!(changed["kind"], "counterexample", "{changed}");
}
