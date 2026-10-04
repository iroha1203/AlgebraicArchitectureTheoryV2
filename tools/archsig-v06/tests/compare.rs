//! AC7: `archsig compare`(マニュアル第2章 7.、第5章 問い3の「実装後に比べる」)。

use std::collections::BTreeMap;
use std::path::Path;

use serde_json::Value;

mod common;

use common::*;

/// 第2章の変更前のリポジトリと、それを写した変更後のリポジトリ。変更後のほうで実装する。
/// Law の `sources` に当たるソースのファイルも置く。読んだ範囲は、これと突き合わせる。
fn prepared(name: &str) -> (Repo, Repo) {
    let before = shop(&format!("{name}-before"));
    before.map("shop/shipping/address.py", ADDRESS);
    for f in ["shop/shipping/service.py", "shop/shipping/address.py", "shop/shipping/model.py", "shop/order/model.py"] {
        before.write(f, "# source\n");
    }
    let after = Repo::new(name);
    copy(&before.dir, &after.dir);
    (before, after)
}

fn copy(from: &Path, to: &Path) {
    for e in std::fs::read_dir(from).unwrap().map(|e| e.unwrap().path()) {
        let target = to.join(e.file_name().unwrap());
        if e.is_dir() {
            std::fs::create_dir_all(&target).unwrap();
            copy(&e, &target);
        } else {
            std::fs::copy(&e, &target).unwrap();
        }
    }
}

fn compare(repo: &Repo, before: &Repo, plan: Option<&str>) -> Value {
    let before = before.dir.to_string_lossy().to_string();
    let mut args = vec!["compare", "--before", before.as_str()];
    if let Some(p) = plan {
        args.extend(["--plan", p]);
    }
    repo.run(&args)
}

/// 候補の構造 Atom を実装したときの観測。候補の Atom に、ソースの場所を付ける。
/// `defines` は `file` のソースに、それ以外は `subject` の操作を定義したソースに置く。
fn implemented(plan: &str, edit: impl Fn(&str) -> String) -> BTreeMap<String, String> {
    let atoms: Vec<Value> = plan.lines().map(|l| serde_json::from_str(l).unwrap()).collect();
    let mut file_of: BTreeMap<String, String> = BTreeMap::new();
    for a in atoms.iter().filter(|a| a["kind"] == "defines") {
        file_of.insert(a["subject"].as_str().unwrap().to_string(), a["file"].as_str().unwrap().to_string());
    }
    let mut out: BTreeMap<String, String> = BTreeMap::new();
    for (i, a) in atoms.iter().enumerate().filter(|(_, a)| !matches!(a["kind"].as_str(), Some("plan" | "corresponds" | "removes"))) {
        let owner = a["subject"].as_str().unwrap().split("->").next().unwrap();
        let file = a["file"].as_str().map(str::to_string).unwrap_or_else(|| file_of[owner].clone());
        let mut a = a.clone();
        a.as_object_mut().unwrap().remove("file");
        a["at"] = Value::String(format!("{file}:{}@blob:5e5e5e5", i + 1));
        out.entry(file).or_default().push_str(&edit(&(a.to_string() + "\n")));
    }
    for (file, text) in out.iter_mut() {
        *text = format!(
            "{{\"kind\": \"observed\", \"subject\": \"{file}\", \"scope\": \"structure\", \"at\": \"{file}@blob:5e5e5e5\"}}\n{{\"kind\": \"observed\", \"subject\": \"{file}\", \"scope\": \"meaning:payment-info\", \"at\": \"{file}@blob:5e5e5e5\"}}\n{text}"
        );
    }
    // 実装したソースを観測する解析器は、そこで使う組み込みの型 str の解決も書く(第3章)。
    for (file, text) in out.iter_mut().filter(|(_, t)| t.contains("\"str\"")) {
        text.push_str(&format!("{{\"kind\": \"resolves\", \"subject\": \"str\", \"object\": \"external:builtins\", \"at\": \"{file}:1@blob:5e5e5e5\"}}\n"));
    }
    out
}

const RESOLVES: &str = r#"{"kind": "resolves", "subject": "shop.shipping.address.normalize_address", "object": "shop/shipping/address.py", "at": "shop/shipping/service.py:1@blob:5e5e5e5"}
"#;
const PAYMENT_MEANING: &str = r#"{"kind": "meaning", "subject": "shop.payment.model.OrderPayment.ref", "meaning": "payment-info", "uses": ["shop/payment/charge.py:22@blob:8b41d07"], "at": "shop/payment/model.py:5@blob:5e5e5e5"}
"#;

/// 実装した後の ArchMap に置き換える。注文の型を消し、配送と決済の新しい型と操作を観測し直した。
fn implement(repo: &Repo, plan: &str, edit: impl Fn(&str) -> String) {
    std::fs::remove_file(repo.dir.join(".archsig/map/shop/order/model.py.jsonl")).unwrap();
    std::fs::remove_file(repo.dir.join("shop/order/model.py")).unwrap();
    for (file, mut text) in implemented(plan, edit) {
        repo.write(&file, "# source\n");
        if file == "shop/shipping/model.py" {
            // Address の型は変わらない。
            text.push_str(ADDRESS_MODEL.lines().filter(|l| l.contains("\"defines\"")).collect::<Vec<_>>().join("\n").as_str());
            text.push('\n');
        }
        if file == "shop/shipping/service.py" {
            text.push_str(RESOLVES);
        }
        if file == "shop/payment/model.py" {
            text.push_str(PAYMENT_MEANING);
        }
        repo.map(&file, &text);
    }
}

fn planned(repo: &Repo, plan: &str) {
    repo.write(".archsig/plans/split-order/plan.jsonl", plan);
}

#[test]
fn the_implementation_of_chapter_2_holds_and_matches_the_plan() {
    let (before, repo) = prepared("ch2");
    let plan = fixed_plan();
    planned(&repo, &plan);
    implement(&repo, &plan, |l| l.to_string());
    let s = compare(&repo, &before, Some("split-order"));
    assert_eq!(s["command"], "compare");
    let results = s["results"].as_array().unwrap();
    assert!(results.iter().any(|r| r["subject"] == "shop.shipping.service.update_shipping"), "{s}");
    assert!(results.iter().all(|r| r["outcome"] == "holds"), "すべて成り立つ: {s}");
    // 候補の構造 Atom 13 件すべてに、対応する観測がある(第2章 7.)。
    let matched = repo.run(&["show", result(&s, "split-order")["id"].as_str().unwrap()]);
    assert_eq!((matched["check"]["planned"].as_u64(), matched["check"]["observed"].as_u64()), (Some(13), Some(13)), "{matched}");
    // 国が変わる / 変わらないの2分岐で、二つの順番の決済情報の値を比べている。
    let d = repo.run(&["show", result(&s, "shop.shipping.service.update_shipping")["id"].as_str().unwrap()]);
    let branches = d["check"]["branches"].as_array().unwrap();
    assert_eq!(branches.len(), 2, "{d}");
    assert!(branches.iter().all(|b| b["values"].as_array().unwrap().iter().any(|v| v["place"][0] == "shop.payment.model.OrderPayment.ref")), "{d}");
}

#[test]
fn an_empty_string_in_place_of_none_is_a_counterexample_and_a_mismatch() {
    let (before, repo) = prepared("empty-string");
    let plan = fixed_plan();
    planned(&repo, &plan);
    // 決済側が OrderPayment.ref を None ではなく空文字にした。
    implement(&repo, &plan, |l| {
        if l.contains("\"kind\":\"writes\"") && l.contains("\"subject\":\"shop.payment.service.reset_authorization\"") {
            l.replace("\"value\":\"None\"", "\"value\":\"\\\"\\\"\"")
        } else {
            l.to_string()
        }
    });
    let s = compare(&repo, &before, Some("split-order"));
    let results = s["results"].as_array().unwrap();
    let update = result(&s, "shop.shipping.service.update_shipping");
    assert_eq!(update["kind"], "counterexample", "{s}");
    let mismatches: Vec<&Value> = results.iter().filter(|r| r["kind"] == "mismatch").collect();
    // 候補の書き込み(None)が観測されず、候補にない書き込み(空文字)が観測された。
    assert_eq!(mismatches.len(), 2, "{s}");
    let details: Vec<Value> = mismatches.iter().map(|r| repo.run(&["show", r["id"].as_str().unwrap()])).collect();
    assert!(details.iter().any(|d| d["check"]["planned"]["value"] == "None" && d["check"]["observed"].is_null()), "{details:?}");
    assert!(details.iter().any(|d| d["check"]["observed"]["value"] == "\"\"" && d["check"]["observed"]["at"].as_str().unwrap().starts_with("shop/payment/service.py")), "{details:?}");
}

#[test]
fn an_atom_planned_twice_must_be_observed_twice() {
    let (before, repo) = prepared("twice");
    let plan = fixed_plan();
    let reset_write = plan.lines().find(|l| l.contains("\"writes\"") && l.contains("reset_authorization")).unwrap().to_string();
    planned(&repo, &format!("{plan}{reset_write}\n"));
    implement(&repo, &plan, |l| l.to_string());
    let s = compare(&repo, &before, Some("split-order"));
    let mismatches: Vec<&Value> = s["results"].as_array().unwrap().iter().filter(|r| r["kind"] == "mismatch").collect();
    assert_eq!(mismatches.len(), 1, "{s}");
    assert_eq!(mismatches[0]["subject"], "shop.payment.service.reset_authorization");
}

#[test]
fn compare_without_a_plan_computes_the_laws() {
    let (before, repo) = prepared("base");
    // 名前を変えない変更:fix_address が決済情報を空文字にするようになった。
    repo.map(
        "shop/shipping/service.py",
        &format!(
            "{SERVICE}{}",
            r#"{"kind": "writes", "subject": "shop.shipping.service.fix_address", "object": "shop.order.model.Order.payment_ref", "value": "\"\"", "at": "shop/shipping/service.py:10@blob:3f2a9c1"}
"#
        ),
    );
    let s = compare(&repo, &before, None);
    assert_eq!(s["command"], "compare");
    assert_eq!(result(&s, "shop.shipping.service.fix_address")["kind"], "counterexample", "{s}");
    assert_eq!(result(&s, "shop.shipping.service.update_shipping")["outcome"], "holds", "{s}");
}

#[test]
fn a_target_without_the_meaning_after_reobservation_is_missing() {
    let (before, repo) = prepared("meaning");
    let plan = fixed_plan();
    planned(&repo, &plan);
    implement(&repo, &plan, |l| l.to_string());
    // 観測し直すと、OrderPayment.ref は決済情報として使われていなかった。
    let payment = std::fs::read_to_string(repo.dir.join(".archsig/map/shop/payment/model.py.jsonl")).unwrap();
    repo.map("shop/payment/model.py", &payment.replace(PAYMENT_MEANING, ""));
    let s = compare(&repo, &before, Some("split-order"));
    let r = s["results"].as_array().unwrap().iter().find(|r| r["subject"] == "shop.payment.model.OrderPayment.ref").unwrap_or_else(|| panic!("{s}"));
    assert_eq!((r["kind"].as_str(), r["law"].as_str()), (Some("missing"), Some("payment-follows-order")), "{s}");
}


#[test]
fn atoms_are_compared_by_the_identity_of_chapter_3() {
    // 同一性は kind、subject、object、value、when、meaning、scope で決まる。型の表記の違いは食い違いではない。
    let (before, repo) = prepared("identity");
    let plan = fixed_plan();
    planned(&repo, &plan);
    implement(&repo, &plan, |l| l.replace("\"type\":\"str\"", "\"type\":\"builtins.str\"").replace("\"order_id\":\"str\"", "\"order_id\":\"builtins.str\""));
    let s = compare(&repo, &before, Some("split-order"));
    assert!(s["results"].as_array().unwrap().iter().all(|r| r["kind"] != "mismatch"), "{s}");
}

#[test]
fn a_write_with_another_via_is_another_atom() {
    // 書き込み先の列(`via`)は同一性に入る。候補と違う列を通った書き込みは、候補の書き込みに当たらない。
    let (before, repo) = prepared("via");
    let plan = fixed_plan();
    planned(&repo, &plan);
    implement(&repo, &plan, |l| if l.contains("\"kind\":\"writes\"") { l.replacen('{', "{\"via\":[\"shop.order.model.Order.shipping_address\"],", 1) } else { l.to_string() });
    let s = compare(&repo, &before, Some("split-order"));
    assert!(s["results"].as_array().unwrap().iter().any(|r| r["kind"] == "mismatch"), "{s}");
}

#[test]
fn a_planned_atom_in_a_source_not_read_again_is_silent() {
    let (before, repo) = prepared("not-read-again");
    let plan = fixed_plan();
    planned(&repo, &plan);
    implement(&repo, &plan, |l| l.to_string());
    // 決済のサービスを観測し直していない。
    std::fs::remove_file(repo.dir.join(".archsig/map/shop/payment/service.py.jsonl")).unwrap();
    let s = compare(&repo, &before, Some("split-order"));
    let reset: Vec<&Value> = s["results"].as_array().unwrap().iter().filter(|r| r["subject"] == "shop.payment.service.reset_authorization").collect();
    assert!(!reset.is_empty() && reset.iter().all(|r| r["outcome"] == "silent" && r["reason"] == "unread"), "{s}");
    assert!(s["next"].as_array().unwrap().iter().any(|n| n["read"] == "shop/payment/service.py" && n["scope"] == "structure"), "{s}");
}

#[test]
fn a_source_not_read_after_the_change_is_silent() {
    let (before, repo) = prepared("not-read-after");
    let plan = fixed_plan();
    planned(&repo, &plan);
    implement(&repo, &plan, |l| l.to_string());
    // 実装で足したソースを、観測していない。
    repo.write("shop/shipping/legacy.py", "# source\n");
    let s = compare(&repo, &before, Some("split-order"));
    let r = s["results"].as_array().unwrap().iter().find(|r| r["subject"] == "payment-info" && r["outcome"] == "silent").unwrap_or_else(|| panic!("{s}"));
    assert_eq!(r["reason"], "unread", "{s}");
    assert!(s["next"].as_array().unwrap().iter().any(|n| n["read"] == "shop/shipping/legacy.py"), "{s}");
}


#[test]
fn a_planned_resolves_not_observed_is_silent() {
    // `resolves` の `subject` は参照先の名前で、参照したソースは Atom から決まらない。
    let (before, repo) = prepared("resolves");
    let resolves = r#"{"kind": "resolves", "subject": "shop.payment.service.reset_authorization", "object": "shop/payment/service.py", "at": "plan:split-order"}"#;
    let plan = format!("{}{resolves}\n", fixed_plan());
    planned(&repo, &plan);
    implement(&repo, &plan, |l| if l.contains("\"kind\":\"resolves\"") { String::new() } else { l.to_string() });
    let s = compare(&repo, &before, Some("split-order"));
    let rows: Vec<&Value> = s["results"].as_array().unwrap().iter().filter(|r| r["subject"] == "shop.payment.service.reset_authorization").collect();
    assert!(!rows.is_empty() && rows.iter().all(|r| r["outcome"] == "silent"), "{s}");
}

#[test]
fn a_counterexample_is_not_hidden_by_a_mapped_place_whose_meaning_was_not_read() {
    // 変更前は m.S が m.py にある。実装した後は m.S を s.py に移し、s.py は構造だけを読み直した(payment-info は読んでいない)。
    // 変更前の型でたどった [o.s, S.p] を写した場所は決まらないが、o.t の値が違えば反例は決まる(設計 §5.4)。
    let law = LAW.replace("\"shop/**\"", "\"*.py\"");
    let m = |t: &str, with_s: bool| {
        let s = if with_s {
            r#"{"kind": "defines", "subject": "m.S", "value": "type", "at": "m.py:3@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.S.p", "value": "field", "type": "int", "at": "m.py:4@blob:aaaaaaa"}
{"kind": "meaning", "subject": "m.S.p", "meaning": "payment-info", "uses": ["m.py:10@blob:aaaaaaa"], "at": "m.py:4@blob:aaaaaaa"}
"#
        } else {
            r#"{"kind": "resolves", "subject": "m.S", "object": "s.py", "at": "m.py:1@blob:aaaaaaa"}
"#
        };
        format!(
            r#"{{"kind": "observed", "subject": "m.py", "scope": "structure", "at": "m.py@blob:aaaaaaa"}}
{{"kind": "observed", "subject": "m.py", "scope": "meaning:payment-info", "at": "m.py@blob:aaaaaaa"}}
{{"kind": "resolves", "subject": "int", "object": "external:builtins", "at": "m.py:1@blob:aaaaaaa"}}
{{"kind": "defines", "subject": "m.O", "value": "type", "at": "m.py:1@blob:aaaaaaa"}}
{{"kind": "defines", "subject": "m.O.s", "value": "field", "type": "m.S", "at": "m.py:2@blob:aaaaaaa"}}
{{"kind": "defines", "subject": "m.O.t", "value": "field", "type": "int", "at": "m.py:5@blob:aaaaaaa"}}
{{"kind": "meaning", "subject": "m.O.t", "meaning": "payment-info", "uses": ["m.py:11@blob:aaaaaaa"], "at": "m.py:5@blob:aaaaaaa"}}
{s}{{"kind": "defines", "subject": "m.f", "value": "operation", "params": {{"o": "m.O"}}, "at": "m.py:9@blob:aaaaaaa"}}
{{"kind": "writes", "subject": "m.f", "object": "m.O.s", "value": "m.a()", "at": "m.py:10@blob:aaaaaaa"}}
{{"kind": "writes", "subject": "m.f", "object": "m.O.t", "value": "{t}", "at": "m.py:11@blob:aaaaaaa"}}
"#
        )
    };
    let run = |name: &str, t: &str| {
        let before = Repo::new(&format!("{name}-before"));
        before.write(".archsig/law/m.law", &law);
        before.write("m.py", "# source\n");
        before.map("m.py", &m("1", true));
        let after = Repo::new(name);
        after.write(".archsig/law/m.law", &law);
        after.write("m.py", "# source\n");
        after.write("s.py", "# source\n");
        after.map("m.py", &m(t, false));
        after.map(
            "s.py",
            r#"{"kind": "observed", "subject": "s.py", "scope": "structure", "at": "s.py@blob:bbbbbbb"}
{"kind": "resolves", "subject": "int", "object": "external:builtins", "at": "s.py:1@blob:bbbbbbb"}
{"kind": "defines", "subject": "m.S", "value": "type", "at": "s.py:2@blob:bbbbbbb"}
{"kind": "defines", "subject": "m.S.p", "value": "field", "type": "int", "at": "s.py:3@blob:bbbbbbb"}
"#,
        );
        compare(&after, &before, None)
    };
    let s = run("mapped-unread-differs", "2");
    let r = result(&s, "m.f");
    assert_eq!((r["outcome"].as_str(), r["kind"].as_str()), (Some("fails"), Some("counterexample")), "{s}");
    let s = run("mapped-unread-same", "1");
    let r = result(&s, "m.f");
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unread")), "{s}");
    assert!(s["next"].as_array().unwrap().iter().any(|n| n["read"] == "s.py" && n["scope"] == "meaning:payment-info"), "{s}");
}

#[test]
fn a_target_whose_kind_is_not_decided_after_reobservation_is_unresolved() {
    // 変更前は m.O.t が payment-info を持つ。観測し直した m.O.t の defines に value がなければ、種類が決まらず、
    // 意味を持つかも決まらない(設計 §3.2)。value が field なら、意味を持たないので missing。
    let law = LAW.replace("\"shop/**\"", "\"*.py\"");
    let m = |t_defines: &str, meaning: bool| {
        format!(
            r#"{{"kind": "observed", "subject": "m.py", "scope": "structure", "at": "m.py@blob:aaaaaaa"}}
{{"kind": "observed", "subject": "m.py", "scope": "meaning:payment-info", "at": "m.py@blob:aaaaaaa"}}
{{"kind": "resolves", "subject": "int", "object": "external:builtins", "at": "m.py:1@blob:aaaaaaa"}}
{{"kind": "defines", "subject": "m.O", "value": "type", "at": "m.py:1@blob:aaaaaaa"}}
{t_defines}
{}{{"kind": "defines", "subject": "m.f", "value": "operation", "params": {{"o": "m.O"}}, "at": "m.py:9@blob:aaaaaaa"}}
{{"kind": "writes", "subject": "m.f", "object": "m.O.t", "value": "1", "at": "m.py:10@blob:aaaaaaa"}}
"#,
            if meaning { "{\"kind\": \"meaning\", \"subject\": \"m.O.t\", \"meaning\": \"payment-info\", \"uses\": [\"m.py:10@blob:aaaaaaa\"], \"at\": \"m.py:2@blob:aaaaaaa\"}\n" } else { "" }
        )
    };
    let run = |name: &str, after_t: &str| {
        let before = Repo::new(&format!("{name}-before"));
        before.write(".archsig/law/m.law", &law);
        before.write("m.py", "# source\n");
        before.map("m.py", &m(r#"{"kind": "defines", "subject": "m.O.t", "value": "field", "type": "int", "at": "m.py:2@blob:aaaaaaa"}"#, true));
        let after = Repo::new(name);
        after.write(".archsig/law/m.law", &law);
        after.write("m.py", "# source\n");
        after.map("m.py", &m(after_t, false));
        compare(&after, &before, None)
    };
    let s = run("target-field", r#"{"kind": "defines", "subject": "m.O.t", "value": "field", "type": "int", "at": "m.py:2@blob:aaaaaaa"}"#);
    let r = result(&s, "m.O.t");
    assert_eq!((r["outcome"].as_str(), r["kind"].as_str()), (Some("fails"), Some("missing")), "対照: {s}");
    let s = run("target-valueless", r#"{"kind": "defines", "subject": "m.O.t", "type": "int", "at": "m.py:2@blob:aaaaaaa"}"#);
    let r = result(&s, "m.O.t");
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unresolved")), "{s}");
}

#[test]
fn an_operation_without_a_kind_only_after_the_change_that_names_a_removed_type_is_unresolved() {
    // 変更前は型 m.T だけ。観測し直した変更後に、m.T を引数の型に持つ m.x がある。候補は m.T を消す。
    // m.x の種類は変更後の構造で問い合わせる。value がなければ種類が決まらないので沈黙する。
    let law = LAW.replace("\"shop/**\"", "\"*.py\"");
    let base = r#"{"kind": "observed", "subject": "m.py", "scope": "structure", "at": "m.py@blob:aaaaaaa"}
{"kind": "observed", "subject": "m.py", "scope": "meaning:payment-info", "at": "m.py@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.T", "value": "type", "at": "m.py:1@blob:aaaaaaa"}
"#;
    let run = |name: &str, x: &str| {
        let before = Repo::new(&format!("{name}-before"));
        before.write(".archsig/law/m.law", &law);
        before.write("m.py", "# source\n");
        before.map("m.py", base);
        let after = Repo::new(name);
        after.write(".archsig/law/m.law", &law);
        after.write("m.py", "# source\n");
        after.map("m.py", &format!("{base}{x}\n"));
        after.write(".archsig/plans/p/plan.jsonl", "{\"kind\": \"removes\", \"subject\": \"m.T\", \"at\": \"plan:p\"}\n");
        compare(&after, &before, Some("p"))
    };
    let s = run("after-only-op", r#"{"kind": "defines", "subject": "m.x", "value": "operation", "params": {"q": "m.T"}, "at": "m.py:2@blob:aaaaaaa"}"#);
    let r = result(&s, "m.x");
    assert_eq!((r["outcome"].as_str(), r["kind"].as_str()), (Some("fails"), Some("missing")), "対照: {s}");
    let s = run("after-only-valueless", r#"{"kind": "defines", "subject": "m.x", "params": {"q": "m.T"}, "at": "m.py:2@blob:aaaaaaa"}"#);
    let r = result(&s, "m.x");
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unresolved")), "{s}");
}

#[test]
fn an_operation_that_loses_its_kind_after_the_change_and_names_a_removed_type_is_unresolved() {
    // 変更前の m.x は操作。観測し直した変更後の m.x には value がない。種類は変更後の構造で問い合わせる。
    let law = LAW.replace("\"shop/**\"", "\"*.py\"");
    let base = r#"{"kind": "observed", "subject": "m.py", "scope": "structure", "at": "m.py@blob:aaaaaaa"}
{"kind": "observed", "subject": "m.py", "scope": "meaning:payment-info", "at": "m.py@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.T", "value": "type", "at": "m.py:1@blob:aaaaaaa"}
"#;
    let before = Repo::new("loses-kind-before");
    before.write(".archsig/law/m.law", &law);
    before.write("m.py", "# source\n");
    before.map("m.py", &format!("{base}{}\n", r#"{"kind": "defines", "subject": "m.x", "value": "operation", "params": {"q": "m.T"}, "at": "m.py:2@blob:aaaaaaa"}"#));
    let after = Repo::new("loses-kind");
    after.write(".archsig/law/m.law", &law);
    after.write("m.py", "# source\n");
    after.map("m.py", &format!("{base}{}\n", r#"{"kind": "defines", "subject": "m.x", "params": {"q": "m.T"}, "at": "m.py:2@blob:aaaaaaa"}"#));
    after.write(".archsig/plans/p/plan.jsonl", "{\"kind\": \"removes\", \"subject\": \"m.T\", \"at\": \"plan:p\"}\n");
    let s = compare(&after, &before, Some("p"));
    assert!(!s["results"].as_array().unwrap().iter().any(|r| r["subject"] == "m.x" && r["outcome"] == "fails"), "{s}");
    let r = result(&s, "m.x");
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unresolved")), "{s}");
    // 変更後で種類が決まっていれば(型)、種類は変更前で問い合わせる。変更前は操作なので missing。
    // 名指しは、消える型 m.T のフィールドへの書き込みで作る(引数の型の名指しは、操作と種類の決まらない要素だけが持つ)。
    let writes = r#"{"kind": "defines", "subject": "m.T.f", "value": "field", "type": "m.T", "at": "m.py:1@blob:aaaaaaa"}
{"kind": "writes", "subject": "m.x", "object": "m.T.f", "value": "1", "at": "m.py:3@blob:aaaaaaa"}
"#;
    before.map("m.py", &format!("{base}{writes}{}\n", r#"{"kind": "defines", "subject": "m.x", "value": "operation", "params": {}, "at": "m.py:2@blob:aaaaaaa"}"#));
    after.map("m.py", &format!("{base}{writes}{}\n", r#"{"kind": "defines", "subject": "m.x", "value": "type", "at": "m.py:2@blob:aaaaaaa"}"#));
    let s = compare(&after, &before, Some("p"));
    let r = result(&s, "m.x");
    assert_eq!((r["outcome"].as_str(), r["kind"].as_str()), (Some("fails"), Some("missing")), "{s}");
}

#[test]
fn a_question_mark_target_after_reobservation_says_what_to_read() {
    // 候補の対応の行き先が ? の名前なら、意味を持つかは決まらない。候補の Atom の場所を次に読む所として返す。
    let law = LAW.replace("\"shop/**\"", "\"*.py\"");
    let m = r#"{"kind": "observed", "subject": "m.py", "scope": "structure", "at": "m.py@blob:aaaaaaa"}
{"kind": "observed", "subject": "m.py", "scope": "meaning:payment-info", "at": "m.py@blob:aaaaaaa"}
{"kind": "resolves", "subject": "int", "object": "external:builtins", "at": "m.py:1@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.O", "value": "type", "at": "m.py:1@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.O.t", "value": "field", "type": "int", "at": "m.py:2@blob:aaaaaaa"}
{"kind": "meaning", "subject": "m.O.t", "meaning": "payment-info", "uses": ["m.py:2@blob:aaaaaaa"], "at": "m.py:2@blob:aaaaaaa"}
"#;
    let before = Repo::new("q-target-before");
    before.write(".archsig/law/m.law", &law);
    before.write("m.py", "# source\n");
    before.map("m.py", m);
    let after = Repo::new("q-target");
    after.write(".archsig/law/m.law", &law);
    after.write("m.py", "# source\n");
    after.map("m.py", m);
    after.write(".archsig/plans/p/plan.jsonl", "{\"kind\": \"corresponds\", \"subject\": \"m.O.t\", \"object\": \"?x\", \"at\": \"plan:p\"}\n");
    let s = compare(&after, &before, Some("p"));
    let r = result(&s, "?x");
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unresolved")), "{s}");
    assert!(s["next"].as_array().unwrap().iter().any(|n| n["decides"].as_array().unwrap().contains(&r["id"])), "{s}");
}

#[test]
fn a_moved_field_defined_in_two_places_after_reobservation_is_unresolved() {
    // 候補は m.T.s を m.T.r へ移す。観測し直した m.T.r の defines が二か所にあり、型が m.U1 と m.U2 で違う。
    // m.U2.g だけが payment-info を持つ。m.T.r の型が決まらないので、その先の場所も決まらない(並びによらない)。
    let law = LAW.replace("\"shop/**\"", "\"*.py\"");
    let common = r#"{"kind": "observed", "subject": "m.py", "scope": "structure", "at": "m.py@blob:aaaaaaa"}
{"kind": "observed", "subject": "m.py", "scope": "meaning:payment-info", "at": "m.py@blob:aaaaaaa"}
{"kind": "resolves", "subject": "int", "object": "external:builtins", "at": "m.py:1@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.T", "value": "type", "at": "m.py:1@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.T.k", "value": "field", "type": "int", "at": "m.py:3@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.U1", "value": "type", "at": "m.py:4@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.U1.g", "value": "field", "type": "int", "at": "m.py:5@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.U2", "value": "type", "at": "m.py:6@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.U2.g", "value": "field", "type": "int", "at": "m.py:7@blob:aaaaaaa"}
{"kind": "meaning", "subject": "m.U2.g", "meaning": "payment-info", "uses": ["m.py:7@blob:aaaaaaa"], "at": "m.py:7@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.f", "value": "operation", "params": {"o": "m.T"}, "at": "m.py:9@blob:aaaaaaa"}
"#;
    let run = |name: &str, types: [&str; 2], meaning_on_r: bool| {
        let before = Repo::new(&format!("{name}-before"));
        before.write(".archsig/law/m.law", &law);
        before.write("m.py", "# source\n");
        before.map(
            "m.py",
            &format!(
                "{common}{}",
                r#"{"kind": "defines", "subject": "m.T.s", "value": "field", "type": "m.U1", "at": "m.py:2@blob:aaaaaaa"}
{"kind": "writes", "subject": "m.f", "object": "m.T.s", "value": "1", "at": "m.py:10@blob:aaaaaaa"}
"#
            ),
        );
        let after = Repo::new(name);
        after.write(".archsig/law/m.law", &law);
        after.write("m.py", "# source\n");
        after.map(
            "m.py",
            &format!(
                "{common}{{\"kind\": \"defines\", \"subject\": \"m.T.r\", \"value\": \"field\", \"type\": \"{}\", \"at\": \"m.py:2@blob:aaaaaaa\"}}\n{{\"kind\": \"defines\", \"subject\": \"m.T.r\", \"value\": \"field\", \"type\": \"{}\", \"at\": \"m.py:8@blob:aaaaaaa\"}}\n{}{}",
                types[0],
                types[1],
                if meaning_on_r { "{\"kind\": \"meaning\", \"subject\": \"m.T.r\", \"meaning\": \"payment-info\", \"uses\": [\"m.py:2@blob:aaaaaaa\"], \"at\": \"m.py:2@blob:aaaaaaa\"}\n" } else { "" },
                r#"{"kind": "writes", "subject": "m.f", "object": "m.T.k", "value": "1", "at": "m.py:10@blob:aaaaaaa"}
"#
            ),
        );
        after.write(
            ".archsig/plans/p/plan.jsonl",
            r#"{"kind": "corresponds", "subject": "m.T.s", "object": "m.T.r", "at": "plan:p"}
{"kind": "removes", "subject": "m.T.s", "at": "plan:p"}
"#,
        );
        compare(&after, &before, Some("p"))
    };
    // 型が同じでも、m.T.r そのものが意味を持つかは、どちらの定義のソースで読むかが決まらない。
    for (name, types, meaning_on_r) in [
        ("twice-defined-target-u1-u2", ["m.U1", "m.U2"], false),
        ("twice-defined-target-u2-u1", ["m.U2", "m.U1"], false),
        ("twice-defined-target-with-meaning", ["int", "int"], true),
    ] {
        let s = run(name, types, meaning_on_r);
        let r = result(&s, "m.f");
        assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unresolved")), "{name}: {s}");
    }
}

#[test]
fn removes_after_reobservation_traces_paths_in_the_structure_after_the_change() {
    // 実装後に観測し直した構造で、m.O.a の型が `?m.B` なら、m.g の $o.a.x が何を名指すかは決まらない。読んでいない c.py の m.C なら、読む所は c.py。
    let law = LAW.replace("\"shop/**\"", "\"*.py\"");
    let base = r#"{"kind": "observed", "subject": "m.py", "scope": "structure", "at": "m.py@blob:aaaaaaa"}
{"kind": "observed", "subject": "m.py", "scope": "meaning:payment-info", "at": "m.py@blob:aaaaaaa"}
{"kind": "resolves", "subject": "int", "object": "external:builtins", "at": "m.py:1@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.O", "value": "type", "at": "m.py:1@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.A", "value": "type", "at": "m.py:3@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.A.x", "value": "field", "type": "m.A", "at": "m.py:4@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.B", "value": "type", "at": "m.py:5@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.B.x", "value": "field", "type": "int", "at": "m.py:6@blob:aaaaaaa"}
"#;
    // 使う側の m.g は別のソース g.py に置く。読む所が、使う側でなく型を書いた定義のソースであることを区別する。
    let g = r#"{"kind": "observed", "subject": "g.py", "scope": "structure", "at": "g.py@blob:ccccccc"}
{"kind": "defines", "subject": "m.g", "value": "operation", "params": {"o": "m.O"}, "at": "g.py:10@blob:ccccccc"}
{"kind": "returns", "subject": "m.g", "value": "$o.a.x.y", "at": "g.py:11@blob:ccccccc"}
"#;
    let run = |name: &str, field: &str, removes: &str| {
        let before = Repo::new(&format!("{name}-before"));
        before.write(".archsig/law/m.law", &law);
        before.write("m.py", "# source\n");
        before.write("g.py", "# source\n");
        before.map("g.py", g);
        before.map("m.py", &format!("{base}{{\"kind\": \"defines\", \"subject\": \"m.O.a\", \"value\": \"field\", \"type\": \"m.A\", \"at\": \"m.py:2@blob:aaaaaaa\"}}\n"));
        let after = Repo::new(name);
        after.write(".archsig/law/m.law", &law);
        after.write("m.py", "# source\n");
        after.write("g.py", "# source\n");
        after.map("g.py", g);
        after.map("m.py", &format!("{base}{field}"));
        after.write(".archsig/plans/p/plan.jsonl", &format!("{{\"kind\": \"removes\", \"subject\": \"{removes}\", \"at\": \"plan:p\"}}\n"));
        let s = compare(&after, &before, Some("p"));
        let r = s["results"].as_array().unwrap().iter().find(|r| r["subject"] == "m.g" && r["law"].is_null()).cloned().unwrap_or_default();
        (r, s)
    };
    let (r, s) = run("reobserved-q-type", "{\"kind\": \"defines\", \"subject\": \"m.O.a\", \"value\": \"field\", \"type\": \"?m.B\", \"at\": \"m.py:2@blob:aaaaaaa\"}\n", "m.B.x");
    assert_eq!(r["outcome"], "silent", "{s}");
    // 読む所は、`?m.B` を書いたフィールドの定義のソース m.py である。使う側の g.py ではない。
    let next: Vec<&Value> = s["next"].as_array().unwrap().iter().filter(|n| n["decides"].as_array().unwrap().contains(&r["id"])).collect();
    assert!(!next.is_empty() && next.iter().all(|n| n["read"] == "m.py"), "{s}");
    let (r, s) = run(
        "reobserved-unread-type",
        "{\"kind\": \"defines\", \"subject\": \"m.O.a\", \"value\": \"field\", \"type\": \"m.C\", \"at\": \"m.py:2@blob:aaaaaaa\"}\n{\"kind\": \"resolves\", \"subject\": \"m.C\", \"object\": \"c.py\", \"at\": \"m.py:7@blob:aaaaaaa\"}\n",
        "m.A.x",
    );
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unread")), "{s}");
    assert!(s["next"].as_array().unwrap().iter().any(|n| n["read"] == "c.py" && n["decides"].as_array().unwrap().contains(&r["id"])), "{s}");
}

#[test]
fn a_target_not_read_after_reobservation_is_unread_on_the_meaning_check() {
    // 候補は m.O.t を m.O.t と m.P.u の二つへ分ける。観測し直した変更後で、m.P.u は定義を読んでいない p.py の型 m.P のフィールドである。
    // m.P.u が意味を持つかは決まらないので、黙って外さず、`unread` で沈黙し、読む所を返す(設計 §5.1)。
    let law = r#"sources "*.py"

reading module = dir(depth: 1)

meaning payment-info on field
  "注文の支払いを特定する値。"

law payment-info-kept
  "決済情報は変更の後も残る。"
  about payment-info
  changes keep
"#;
    let m = r#"{"kind": "observed", "subject": "m.py", "scope": "structure", "at": "m.py@blob:aaaaaaa"}
{"kind": "observed", "subject": "m.py", "scope": "meaning:payment-info", "at": "m.py@blob:aaaaaaa"}
{"kind": "resolves", "subject": "int", "object": "external:builtins", "at": "m.py:1@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.O", "value": "type", "at": "m.py:1@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.O.t", "value": "field", "type": "int", "at": "m.py:2@blob:aaaaaaa"}
{"kind": "meaning", "subject": "m.O.t", "meaning": "payment-info", "uses": ["m.py:2@blob:aaaaaaa"], "at": "m.py:2@blob:aaaaaaa"}
"#;
    let before = Repo::new("split-unread-before");
    before.write(".archsig/law/m.law", law);
    before.write("m.py", "# source\n");
    before.map("m.py", m);
    let after = Repo::new("split-unread");
    after.write(".archsig/law/m.law", law);
    after.write("m.py", "# source\n");
    after.map("m.py", &format!("{m}{{\"kind\": \"resolves\", \"subject\": \"m.P\", \"object\": \"p.py\", \"at\": \"m.py:3@blob:aaaaaaa\"}}\n"));
    after.write(
        ".archsig/plans/p/plan.jsonl",
        "{\"kind\": \"corresponds\", \"subject\": \"m.O.t\", \"object\": \"m.O.t\", \"at\": \"plan:p\"}\n{\"kind\": \"corresponds\", \"subject\": \"m.O.t\", \"object\": \"m.P.u\", \"at\": \"plan:p\"}\n",
    );
    let s = compare(&after, &before, Some("p"));
    let r = result(&s, "m.P.u");
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unread")), "{s}");
    assert!(s["next"].as_array().unwrap().iter().any(|n| n["decides"].as_array().unwrap().contains(&r["id"])), "{s}");
}

#[test]
fn changes_keep_after_reobservation_is_unread_where_the_structure_was_not_read_again() {
    // 変更後の ArchMap は m.py の構造を読んでいない(意味の範囲だけ読んだ)。m.O.t が変更後にもあるかは決まらないので、
    // `missing` にせず、`unread` で沈黙し、m.py の構造を返す(設計 §5.1)。
    let law = r#"sources "*.py"

reading module = dir(depth: 1)

meaning payment-info on field
  "注文の支払いを特定する値。"

law payment-info-kept
  "決済情報は変更の後も残る。"
  about payment-info
  changes keep
"#;
    let m = r#"{"kind": "observed", "subject": "m.py", "scope": "structure", "at": "m.py@blob:aaaaaaa"}
{"kind": "observed", "subject": "m.py", "scope": "meaning:payment-info", "at": "m.py@blob:aaaaaaa"}
{"kind": "resolves", "subject": "int", "object": "external:builtins", "at": "m.py:1@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.O", "value": "type", "at": "m.py:1@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.O.t", "value": "field", "type": "int", "at": "m.py:2@blob:aaaaaaa"}
{"kind": "meaning", "subject": "m.O.t", "meaning": "payment-info", "uses": ["m.py:2@blob:aaaaaaa"], "at": "m.py:2@blob:aaaaaaa"}
"#;
    let before = Repo::new("keep-unobserved-before");
    before.write(".archsig/law/m.law", law);
    before.write("m.py", "# source\n");
    before.map("m.py", m);
    let after = Repo::new("keep-unobserved");
    after.write(".archsig/law/m.law", law);
    after.write("m.py", "# source\n");
    after.map("m.py", r#"{"kind": "observed", "subject": "m.py", "scope": "meaning:payment-info", "at": "m.py@blob:bbbbbbb"}
"#);
    // 候補が m.O.t を消すなら、消えることは候補で決まっているので `missing` である。
    after.write(".archsig/plans/p/plan.jsonl", "{\"kind\": \"removes\", \"subject\": \"m.O.t\", \"at\": \"plan:p\"}\n");
    let s = compare(&after, &before, Some("p"));
    assert_eq!((result(&s, "m.O.t")["outcome"].as_str(), result(&s, "m.O.t")["kind"].as_str()), (Some("fails"), Some("missing")), "{s}");
    let s = compare(&after, &before, None);
    assert!(!s["results"].as_array().unwrap().iter().any(|r| r["kind"] == "missing"), "{s}");
    let r = result(&s, "m.O.t");
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unread")), "{s}");
    assert!(s["next"].as_array().unwrap().iter().any(|n| n["read"] == "m.py" && n["scope"] == "structure" && n["decides"].as_array().unwrap().contains(&r["id"])), "{s}");
}

#[test]
fn changes_keep_of_an_argument_after_reobservation_is_unread_where_the_structure_was_not_read_again() {
    // 意味を持つ引数 m.f.$x。変更後は m.py の構造を読んでいないので、m.f とその引数が変更後にもあるかは決まらない。
    // 引数は持ち主の操作 m.f の定義のソースで見て、`unread` で沈黙し、m.py の構造を返す。
    let law = r#"sources "*.py"

reading module = dir(depth: 1)

meaning payment-info on param
  "注文の支払いを特定する値。"

law payment-info-kept
  "決済情報は変更の後も残る。"
  about payment-info
  changes keep
"#;
    let m = r#"{"kind": "observed", "subject": "m.py", "scope": "structure", "at": "m.py@blob:aaaaaaa"}
{"kind": "observed", "subject": "m.py", "scope": "meaning:payment-info", "at": "m.py@blob:aaaaaaa"}
{"kind": "resolves", "subject": "int", "object": "external:builtins", "at": "m.py:1@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.f", "value": "operation", "params": {"x": "int"}, "at": "m.py:2@blob:aaaaaaa"}
{"kind": "meaning", "subject": "m.f.$x", "meaning": "payment-info", "uses": ["m.py:3@blob:aaaaaaa"], "at": "m.py:2@blob:aaaaaaa"}
"#;
    let before = Repo::new("keep-arg-unobserved-before");
    before.write(".archsig/law/m.law", law);
    before.write("m.py", "# source\n");
    before.map("m.py", m);
    let after = Repo::new("keep-arg-unobserved");
    after.write(".archsig/law/m.law", law);
    after.write("m.py", "# source\n");
    after.map("m.py", r#"{"kind": "observed", "subject": "m.py", "scope": "meaning:payment-info", "at": "m.py@blob:bbbbbbb"}
"#);
    let s = compare(&after, &before, None);
    let r = result(&s, "m.f.$x");
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unread")), "{s}");
    assert!(s["next"].as_array().unwrap().iter().any(|n| n["read"] == "m.py" && n["scope"] == "structure" && n["decides"].as_array().unwrap().contains(&r["id"])), "{s}");
}

/// 変更前の m.py の ArchMap(`meaning` の付いた要素を `extra` で足す)と、`law` の `changes keep` で、変更後を `after_map` にしたときの compare。
fn keep_after(name: &str, law: &str, extra: &str, after_files: &[(&str, &str)], plan: Option<&str>) -> Value {
    let m = format!(
        "{}{extra}",
        r#"{"kind": "observed", "subject": "m.py", "scope": "structure", "at": "m.py@blob:aaaaaaa"}
{"kind": "observed", "subject": "m.py", "scope": "meaning:payment-info", "at": "m.py@blob:aaaaaaa"}
{"kind": "resolves", "subject": "int", "object": "external:builtins", "at": "m.py:1@blob:aaaaaaa"}
"#
    );
    let before = Repo::new(&format!("{name}-before"));
    before.write(".archsig/law/m.law", law);
    before.write("m.py", "# source\n");
    before.map("m.py", &m);
    let after = Repo::new(name);
    after.write(".archsig/law/m.law", law);
    for (file, map) in after_files {
        after.write(file, "# source\n");
        after.map(file, map);
    }
    if let Some(p) = plan {
        after.write(".archsig/plans/p/plan.jsonl", p);
    }
    compare(&after, &before, plan.map(|_| "p"))
}

#[test]
fn changes_keep_after_reobservation_of_a_deleted_source_call_or_removed_owner() {
    let keep_law = |on: &str| {
        format!(
            "sources \"*.py\"\n\nreading module = dir(depth: 1)\n\nmeaning payment-info on {on}\n  \"注文の支払いを特定する値。\"\n\nlaw payment-info-kept\n  \"決済情報は変更の後も残る。\"\n  about payment-info\n  changes keep\n"
        )
    };
    let field = r#"{"kind": "defines", "subject": "m.O", "value": "type", "at": "m.py:1@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.O.t", "value": "field", "type": "int", "at": "m.py:2@blob:aaaaaaa"}
{"kind": "meaning", "subject": "m.O.t", "meaning": "payment-info", "uses": ["m.py:2@blob:aaaaaaa"], "at": "m.py:2@blob:aaaaaaa"}
"#;
    let n = r#"{"kind": "observed", "subject": "n.py", "scope": "structure", "at": "n.py@blob:ccccccc"}
{"kind": "observed", "subject": "n.py", "scope": "meaning:payment-info", "at": "n.py@blob:ccccccc"}
"#;
    // m.py を観測し直し、m.O.t の定義がなくなった。読んだ範囲に m.O.t がないので `missing` である(対照)。
    let reread = r#"{"kind": "observed", "subject": "m.py", "scope": "structure", "at": "m.py@blob:bbbbbbb"}
{"kind": "observed", "subject": "m.py", "scope": "meaning:payment-info", "at": "m.py@blob:bbbbbbb"}
"#;
    let s = keep_after("keep-reread-gone", &keep_law("field"), field, &[("m.py", reread)], None);
    assert_eq!((result(&s, "m.O.t")["outcome"].as_str(), result(&s, "m.O.t")["kind"].as_str()), (Some("fails"), Some("missing")), "{s}");
    // 実装で m.py を消した。m.py は変更後の `sources` にないので、読む所にならず `missing` である。
    let s = keep_after("keep-deleted-source", &keep_law("field"), field, &[("n.py", n)], None);
    assert_eq!((result(&s, "m.O.t")["outcome"].as_str(), result(&s, "m.O.t")["kind"].as_str()), (Some("fails"), Some("missing")), "{s}");
    // 候補が持ち主の型 m.O を消すなら、m.O.t が消えることも候補で決まっている。
    let meaning_only = r#"{"kind": "observed", "subject": "m.py", "scope": "meaning:payment-info", "at": "m.py@blob:bbbbbbb"}
"#;
    let s = keep_after(
        "keep-removed-owner",
        &keep_law("field"),
        field,
        &[("m.py", meaning_only)],
        Some("{\"kind\": \"removes\", \"subject\": \"m.O\", \"at\": \"plan:p\"}\n"),
    );
    assert_eq!((result(&s, "m.O.t")["outcome"].as_str(), result(&s, "m.O.t")["kind"].as_str()), (Some("fails"), Some("missing")), "{s}");
    // 意味を持つ呼び出し m.f->m.g は、持ち主の操作 m.f の定義のソースで見る。m.py の構造を読み直していなければ決まらない。
    let call = r#"{"kind": "defines", "subject": "m.f", "value": "operation", "params": {}, "at": "m.py:2@blob:aaaaaaa"}
{"kind": "calls", "subject": "m.f", "object": "m.g", "at": "m.py:3@blob:aaaaaaa"}
{"kind": "meaning", "subject": "m.f->m.g", "meaning": "payment-info", "uses": ["m.py:3@blob:aaaaaaa"], "at": "m.py:3@blob:aaaaaaa"}
"#;
    let s = keep_after("keep-call-unobserved", &keep_law("call"), call, &[("m.py", meaning_only)], None);
    let r = result(&s, "m.f->m.g");
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unread")), "{s}");
    assert!(s["next"].as_array().unwrap().iter().any(|n| n["read"] == "m.py" && n["scope"] == "structure" && n["decides"].as_array().unwrap().contains(&r["id"])), "{s}");
    // 候補が持ち主の操作 m.f を消すなら、呼び出しが消えることも候補で決まっている。
    let s = keep_after(
        "keep-call-removed-owner",
        &keep_law("call"),
        call,
        &[("m.py", meaning_only)],
        Some("{\"kind\": \"removes\", \"subject\": \"m.f\", \"at\": \"plan:p\"}\n"),
    );
    assert_eq!((result(&s, "m.f->m.g")["outcome"].as_str(), result(&s, "m.f->m.g")["kind"].as_str()), (Some("fails"), Some("missing")), "{s}");
}

#[test]
fn an_operation_added_by_the_implementation_with_a_question_mark_is_silent() {
    // 変更前に m.g はない。実装で足した m.g は ? の値を書く。候補は m.A.x を消す。
    // m.g が消える要素を使うかは決まらないので、m.g は沈黙する。
    let law = LAW.replace("\"shop/**\"", "\"*.py\"");
    let base = r#"{"kind": "observed", "subject": "m.py", "scope": "structure", "at": "m.py@blob:aaaaaaa"}
{"kind": "observed", "subject": "m.py", "scope": "meaning:payment-info", "at": "m.py@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.A", "value": "type", "at": "m.py:1@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.O", "value": "type", "at": "m.py:2@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.O.u", "value": "field", "type": "m.O", "at": "m.py:3@blob:aaaaaaa"}
"#;
    // 実装で二か所に定義した(種類が決まらない)m.g と、変更前は型だった m.g も同じ。
    let g = r#"{"kind": "defines", "subject": "m.g", "value": "operation", "params": {"o": "m.O"}, "at": "m.py:6@blob:aaaaaaa"}
{"kind": "writes", "subject": "m.g", "object": "m.O.u", "value": "?", "at": "m.py:7@blob:aaaaaaa"}
"#;
    let twice = format!("{g}{}\n", r#"{"kind": "defines", "subject": "m.g", "value": "operation", "params": {"o": "m.O"}, "at": "m.py:8@blob:aaaaaaa"}"#);
    let was_type = r#"{"kind": "defines", "subject": "m.g", "value": "type", "at": "m.py:6@blob:aaaaaaa"}
"#;
    // 消える要素を名指す書き込みも持つと、`missing` は変更前の種類(型)で決まらないので、たどれなかった所で沈黙する。
    let names_removed = format!("{g}{}\n", r#"{"kind": "writes", "subject": "m.g", "object": "m.A.x", "value": "?", "at": "m.py:8@blob:aaaaaaa"}"#);
    for (name, old, new) in [
        ("added-question", "", g.to_string()),
        ("added-twice", "", twice),
        ("type-to-operation", was_type, g.to_string()),
        ("type-to-operation-naming-removed", was_type, names_removed),
    ] {
        let before = Repo::new(&format!("{name}-before"));
        before.write(".archsig/law/m.law", &law);
        before.write("m.py", "# source\n");
        before.map("m.py", &format!("{base}{old}{}\n", r#"{"kind": "defines", "subject": "m.A.x", "value": "field", "type": "m.O", "at": "m.py:4@blob:aaaaaaa"}"#));
        let after = Repo::new(name);
        after.write(".archsig/law/m.law", &law);
        after.write("m.py", "# source\n");
        after.map("m.py", &format!("{base}{new}"));
        after.write(".archsig/plans/p/plan.jsonl", "{\"kind\": \"removes\", \"subject\": \"m.A.x\", \"at\": \"plan:p\"}\n");
        let s = compare(&after, &before, Some("p"));
        assert!(s["results"].as_array().unwrap().iter().any(|r| r["subject"] == "m.g" && r["outcome"] == "silent"), "{name}: {s}");
    }
    // 変更前は型で、変更後に m.g の定義を読んでいなければ、消える要素を名指していても `missing` は決まらないので、`removes` の沈黙に入る。
    let unread_after = r#"{"kind": "writes", "subject": "m.g", "object": "m.O.u", "value": "?", "at": "m.py:7@blob:aaaaaaa"}
{"kind": "writes", "subject": "m.g", "object": "m.A.x", "value": "1", "at": "m.py:8@blob:aaaaaaa"}
"#;
    let before = Repo::new("type-to-unread-before");
    before.write(".archsig/law/m.law", &law);
    before.write("m.py", "# source\n");
    before.map("m.py", &format!("{base}{was_type}{}\n", r#"{"kind": "defines", "subject": "m.A.x", "value": "field", "type": "m.O", "at": "m.py:4@blob:aaaaaaa"}"#));
    let after = Repo::new("type-to-unread");
    after.write(".archsig/law/m.law", &law);
    after.write("m.py", "# source\n");
    after.map("m.py", &format!("{base}{unread_after}"));
    after.write(".archsig/plans/p/plan.jsonl", "{\"kind\": \"removes\", \"subject\": \"m.A.x\", \"at\": \"plan:p\"}\n");
    let s = compare(&after, &before, Some("p"));
    assert!(s["results"].as_array().unwrap().iter().any(|r| r["subject"] == "removes" && r["outcome"] == "silent"), "{s}");
}
