//! AC5・AC8: `archsig plan check` と `archsig show`(マニュアル第2章の題材、第5章 問い3、第6章)。

use std::path::PathBuf;
use std::process::Command;

use serde_json::Value;

struct Repo {
    dir: PathBuf,
}

impl Repo {
    fn new(name: &str) -> Repo {
        let dir = std::env::temp_dir().join(format!("archsig-plan-{name}-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(dir.join(".archsig/law")).unwrap();
        Repo { dir }
    }

    fn write(&self, path: &str, text: &str) {
        let p = self.dir.join(path);
        std::fs::create_dir_all(p.parent().unwrap()).unwrap();
        std::fs::write(p, text).unwrap();
    }

    fn map(&self, source: &str, text: &str) {
        self.write(&format!(".archsig/map/{source}.jsonl"), text);
    }

    fn run(&self, args: &[&str]) -> Value {
        let out = Command::new(env!("CARGO_BIN_EXE_archsig")).current_dir(&self.dir).args(args).output().unwrap();
        assert!(out.status.success(), "archsig {args:?}: {}", String::from_utf8_lossy(&out.stderr));
        serde_json::from_slice(&out.stdout).unwrap()
    }
}

impl Drop for Repo {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.dir);
    }
}

const LAW: &str = r#"sources "shop/**"
  except "**/tests/**"

reading module = dir(depth: 2)

meaning payment-info on field
  "注文の支払いを特定する値。決済サービスの呼び出しに渡る値として使われているもの。"

law payment-follows-order
  "注文の型を変えても、決済情報は今の操作と同じように扱われる。"
  about payment-info
  changes commute with operations
"#;

const SERVICE: &str = r#"{"kind": "observed", "subject": "shop/shipping/service.py", "scope": "structure", "at": "shop/shipping/service.py@blob:3f2a9c1"}
{"kind": "observed", "subject": "shop/shipping/service.py", "scope": "meaning:payment-info", "at": "shop/shipping/service.py@blob:3f2a9c1"}
{"kind": "defines", "subject": "shop.shipping.service.update_shipping", "value": "operation", "params": {"order": "shop.order.model.Order", "new": "shop.shipping.model.Address"}, "at": "shop/shipping/service.py:2@blob:3f2a9c1"}
{"kind": "writes", "subject": "shop.shipping.service.update_shipping", "object": "shop.order.model.Order.payment_ref", "value": "None", "when": "$new.country != $order.shipping_address.country", "at": "shop/shipping/service.py:4@blob:3f2a9c1"}
{"kind": "calls", "subject": "shop.shipping.service.update_shipping", "object": "shop.shipping.address.normalize_address", "at": "shop/shipping/service.py:5@blob:3f2a9c1"}
{"kind": "passes", "subject": "shop.shipping.service.update_shipping->shop.shipping.address.normalize_address", "object": "shop.shipping.address.normalize_address.$addr", "value": "$new", "at": "shop/shipping/service.py:5@blob:3f2a9c1"}
{"kind": "writes", "subject": "shop.shipping.service.update_shipping", "object": "shop.order.model.Order.shipping_address", "value": "shop.shipping.address.normalize_address($new)", "at": "shop/shipping/service.py:5@blob:3f2a9c1"}
{"kind": "resolves", "subject": "shop.shipping.address.normalize_address", "object": "shop/shipping/address.py", "at": "shop/shipping/service.py:1@blob:3f2a9c1"}
{"kind": "defines", "subject": "shop.shipping.service.fix_address", "value": "operation", "params": {"order": "shop.order.model.Order"}, "at": "shop/shipping/service.py:8@blob:3f2a9c1"}
{"kind": "calls", "subject": "shop.shipping.service.fix_address", "object": "shop.shipping.address.normalize_address", "at": "shop/shipping/service.py:9@blob:3f2a9c1"}
"#;

const ORDER: &str = r#"{"kind": "observed", "subject": "shop/order/model.py", "scope": "structure", "at": "shop/order/model.py@blob:1d9e3b4"}
{"kind": "observed", "subject": "shop/order/model.py", "scope": "meaning:payment-info", "at": "shop/order/model.py@blob:1d9e3b4"}
{"kind": "defines", "subject": "shop.order.model.Order", "value": "type", "at": "shop/order/model.py:7@blob:1d9e3b4"}
{"kind": "defines", "subject": "shop.order.model.Order.order_id", "value": "field", "type": "str", "at": "shop/order/model.py:8@blob:1d9e3b4"}
{"kind": "defines", "subject": "shop.order.model.Order.shipping_address", "value": "field", "type": "shop.shipping.model.Address", "at": "shop/order/model.py:9@blob:1d9e3b4"}
{"kind": "defines", "subject": "shop.order.model.Order.payment_ref", "value": "field", "type": "str", "at": "shop/order/model.py:10@blob:1d9e3b4"}
{"kind": "meaning", "subject": "shop.order.model.Order.payment_ref", "meaning": "payment-info", "uses": ["shop/payment/charge.py:22@blob:8b41d07"], "at": "shop/order/model.py:10@blob:1d9e3b4"}
"#;

const ADDRESS_MODEL: &str = r#"{"kind": "observed", "subject": "shop/shipping/model.py", "scope": "structure", "at": "shop/shipping/model.py@blob:6a1b2c3"}
{"kind": "observed", "subject": "shop/shipping/model.py", "scope": "meaning:payment-info", "at": "shop/shipping/model.py@blob:6a1b2c3"}
{"kind": "defines", "subject": "shop.shipping.model.Address", "value": "type", "at": "shop/shipping/model.py:3@blob:6a1b2c3"}
{"kind": "defines", "subject": "shop.shipping.model.Address.country", "value": "field", "type": "str", "at": "shop/shipping/model.py:4@blob:6a1b2c3"}
"#;

const ADDRESS: &str = r#"{"kind": "observed", "subject": "shop/shipping/address.py", "scope": "structure", "at": "shop/shipping/address.py@blob:9f2c4e7"}
{"kind": "observed", "subject": "shop/shipping/address.py", "scope": "meaning:payment-info", "at": "shop/shipping/address.py@blob:9f2c4e7"}
{"kind": "defines", "subject": "shop.shipping.address.normalize_address", "value": "operation", "params": {"addr": "shop.shipping.model.Address"}, "at": "shop/shipping/address.py:5@blob:9f2c4e7"}
{"kind": "returns", "subject": "shop.shipping.address.normalize_address", "value": "$addr", "at": "shop/shipping/address.py:6@blob:9f2c4e7"}
"#;

/// マニュアル第2章の候補(一つ目)。
const SPLIT: &str = r#"{"kind": "plan", "subject": "split-order", "base": "a1b2c3d"}
{"kind": "defines", "subject": "shop.shipping.model.OrderShipping", "value": "type", "file": "shop/shipping/model.py", "at": "plan:split-order"}
{"kind": "defines", "subject": "shop.payment.model.OrderPayment", "value": "type", "file": "shop/payment/model.py", "at": "plan:split-order"}
{"kind": "defines", "subject": "shop.shipping.model.OrderShipping.address", "value": "field", "type": "shop.shipping.model.Address", "file": "shop/shipping/model.py", "at": "plan:split-order"}
{"kind": "defines", "subject": "shop.shipping.model.OrderShipping.order_id", "value": "field", "type": "str", "file": "shop/shipping/model.py", "at": "plan:split-order"}
{"kind": "defines", "subject": "shop.payment.model.OrderPayment.ref", "value": "field", "type": "str", "file": "shop/payment/model.py", "at": "plan:split-order"}
{"kind": "corresponds", "subject": "shop.order.model.Order.shipping_address", "object": "shop.shipping.model.OrderShipping.address", "at": "plan:split-order"}
{"kind": "corresponds", "subject": "shop.order.model.Order.payment_ref", "object": "shop.payment.model.OrderPayment.ref", "at": "plan:split-order"}
{"kind": "corresponds", "subject": "shop.shipping.service.update_shipping.$order", "object": "shop.shipping.service.update_shipping.$shipping", "at": "plan:split-order"}
{"kind": "removes", "subject": "shop.order.model.Order", "at": "plan:split-order"}
{"kind": "defines", "subject": "shop.shipping.service.update_shipping", "value": "operation", "params": {"shipping": "shop.shipping.model.OrderShipping", "new": "shop.shipping.model.Address"}, "file": "shop/shipping/service.py", "at": "plan:split-order"}
{"kind": "calls", "subject": "shop.shipping.service.update_shipping", "object": "shop.shipping.address.normalize_address", "at": "plan:split-order"}
{"kind": "passes", "subject": "shop.shipping.service.update_shipping->shop.shipping.address.normalize_address", "object": "shop.shipping.address.normalize_address.$addr", "value": "$new", "at": "plan:split-order"}
{"kind": "writes", "subject": "shop.shipping.service.update_shipping", "object": "shop.shipping.model.OrderShipping.address", "value": "shop.shipping.address.normalize_address($new)", "at": "plan:split-order"}
"#;

/// 第2章 5. の直した候補。国が変わるとき決済側の reset_authorization を呼ぶ。
const RESET: &str = r#"{"kind": "defines", "subject": "shop.payment.service.reset_authorization", "value": "operation", "params": {"order_id": "str"}, "file": "shop/payment/service.py", "at": "plan:split-order"}
{"kind": "writes", "subject": "shop.payment.service.reset_authorization", "object": "shop.payment.model.OrderPayment.ref", "value": "None", "at": "plan:split-order"}
{"kind": "calls", "subject": "shop.shipping.service.update_shipping", "object": "shop.payment.service.reset_authorization", "when": "$new.country != $shipping.address.country", "at": "plan:split-order"}
{"kind": "passes", "subject": "shop.shipping.service.update_shipping->shop.payment.service.reset_authorization", "object": "shop.payment.service.reset_authorization.$order_id", "value": "$shipping.order_id", "at": "plan:split-order"}
"#;

fn shop(name: &str) -> Repo {
    let repo = Repo::new(name);
    repo.write(".archsig/law/shop.law", LAW);
    repo.map("shop/shipping/service.py", SERVICE);
    repo.map("shop/order/model.py", ORDER);
    repo.map("shop/shipping/model.py", ADDRESS_MODEL);
    repo
}

fn result<'a>(summary: &'a Value, subject: &str) -> &'a Value {
    summary["results"].as_array().unwrap().iter().find(|r| r["subject"] == subject).unwrap_or_else(|| panic!("{subject} がない: {summary}"))
}

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
    // 読む所ごとにまとめる。fix_address も同じソースで決まる(AC8)。
    let fix = result(&s, "shop.shipping.service.fix_address")["id"].clone();
    // 候補が Order を消すので、normalize_address が消える要素を使うかも、同じソースで決まる。
    let removes = result(&s, "removes")["id"].clone();
    let mut decides: Vec<&str> = address["decides"].as_array().unwrap().iter().map(|d| d.as_str().unwrap()).collect();
    decides.sort();
    let mut expected = vec![r["id"].as_str().unwrap(), fix.as_str().unwrap(), removes.as_str().unwrap()];
    expected.sort();
    assert_eq!(decides, expected);
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
    let d = repo.run(&["show", result(&s, UPDATE)["id"].as_str().unwrap()]);
    assert!(d["conditions"].as_array().unwrap().iter().any(|c| c.as_str().unwrap().contains("外部の要素 requests.post")), "{d}");
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
    assert!(s["next"].as_array().unwrap().iter().any(|n| n["element"] == "norm" && n["decides"].as_array().unwrap().contains(&r["id"])), "? による unresolved には、何を読めば決まるかが付く: {s}");

    repo.map("shop/shipping/service.py", &SERVICE.replace(r#""value": "None", "when""#, r#""value": "?", "when""#));
    let s = repo.run(&["plan", "check", "split-order"]);
    let r = result(&s, UPDATE);
    assert_eq!(r["reason"], "unresolved", "{s}");
    assert!(s["next"].as_array().unwrap().iter().any(|n| n["read"] == "shop/shipping/service.py" && n["decides"].as_array().unwrap().contains(&r["id"])), "{s}");
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
