//! AC7: `archsig compare`(マニュアル第2章 7.、第5章 問い3の「実装後に比べる」)。

use std::collections::BTreeMap;
use std::process::Command;

use serde_json::Value;

mod common;

use common::*;

fn git(repo: &Repo, args: &[&str]) -> String {
    let out = Command::new("git").current_dir(&repo.dir).args(args).output().unwrap();
    assert!(out.status.success(), "git {args:?}: {}", String::from_utf8_lossy(&out.stderr));
    String::from_utf8_lossy(&out.stdout).trim().to_string()
}

/// 第2章の変更前の ArchMap をコミットし、そのコミットを返す。
fn committed(name: &str) -> (Repo, String) {
    let repo = shop(name);
    repo.map("shop/shipping/address.py", ADDRESS);
    git(&repo, &["init", "-q"]);
    git(&repo, &["-c", "user.name=t", "-c", "user.email=t@example.com", "add", "-A"]);
    git(&repo, &["-c", "user.name=t", "-c", "user.email=t@example.com", "commit", "-q", "-m", "base"]);
    let sha = git(&repo, &["rev-parse", "HEAD"]);
    (repo, sha)
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
    out
}

const RESOLVES: &str = r#"{"kind": "resolves", "subject": "shop.shipping.address.normalize_address", "object": "shop/shipping/address.py", "at": "shop/shipping/service.py:1@blob:5e5e5e5"}
"#;
const PAYMENT_MEANING: &str = r#"{"kind": "meaning", "subject": "shop.payment.model.OrderPayment.ref", "meaning": "payment-info", "uses": ["shop/payment/charge.py:22@blob:8b41d07"], "at": "shop/payment/model.py:5@blob:5e5e5e5"}
"#;

/// 実装した後の ArchMap に置き換える。注文の型を消し、配送と決済の新しい型と操作を観測し直した。
fn implement(repo: &Repo, plan: &str, edit: impl Fn(&str) -> String) {
    std::fs::remove_file(repo.dir.join(".archsig/map/shop/order/model.py.jsonl")).unwrap();
    for (file, mut text) in implemented(plan, edit) {
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

fn planned(repo: &Repo, sha: &str, plan: &str) {
    repo.write(".archsig/plans/split-order/plan.jsonl", &plan.replace("\"base\": \"a1b2c3d\"", &format!("\"base\": \"{sha}\"")));
}

#[test]
fn the_implementation_of_chapter_2_holds_and_matches_the_plan() {
    let (repo, sha) = committed("ch2");
    let plan = fixed_plan();
    planned(&repo, &sha, &plan);
    implement(&repo, &plan, |l| l.to_string());
    let s = repo.run(&["compare", "--plan", "split-order"]);
    assert_eq!(s["command"], "compare");
    let results = s["results"].as_array().unwrap();
    assert!(results.iter().any(|r| r["subject"] == "shop.shipping.service.update_shipping"), "{s}");
    assert!(results.iter().all(|r| r["outcome"] == "holds"), "すべて成り立つ: {s}");
    // 国が変わる / 変わらないの2分岐で、二つの順番の決済情報の値を比べている。
    let d = repo.run(&["show", result(&s, "shop.shipping.service.update_shipping")["id"].as_str().unwrap()]);
    let branches = d["check"]["branches"].as_array().unwrap();
    assert_eq!(branches.len(), 2, "{d}");
    assert!(branches.iter().all(|b| b["values"].as_array().unwrap().iter().any(|v| v["place"][0] == "shop.payment.model.OrderPayment.ref")), "{d}");
}

#[test]
fn an_empty_string_in_place_of_none_is_a_counterexample_and_a_mismatch() {
    let (repo, sha) = committed("empty-string");
    let plan = fixed_plan();
    planned(&repo, &sha, &plan);
    // 決済側が OrderPayment.ref を None ではなく空文字にした。
    implement(&repo, &plan, |l| {
        if l.contains("\"kind\":\"writes\"") && l.contains("\"subject\":\"shop.payment.service.reset_authorization\"") {
            l.replace("\"value\":\"None\"", "\"value\":\"\\\"\\\"\"")
        } else {
            l.to_string()
        }
    });
    let s = repo.run(&["compare", "--plan", "split-order"]);
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
    let (repo, sha) = committed("twice");
    let plan = fixed_plan();
    let reset_write = plan.lines().find(|l| l.contains("\"writes\"") && l.contains("reset_authorization")).unwrap().to_string();
    planned(&repo, &sha, &format!("{plan}{reset_write}\n"));
    implement(&repo, &plan, |l| l.to_string());
    let s = repo.run(&["compare", "--plan", "split-order"]);
    let mismatches: Vec<&Value> = s["results"].as_array().unwrap().iter().filter(|r| r["kind"] == "mismatch").collect();
    assert_eq!(mismatches.len(), 1, "{s}");
    assert_eq!(mismatches[0]["subject"], "shop.payment.service.reset_authorization");
}

#[test]
fn compare_with_a_base_computes_without_a_plan() {
    let (repo, sha) = committed("base");
    // 名前を変えない変更:fix_address が決済情報を空文字にするようになった。
    repo.map(
        "shop/shipping/service.py",
        &format!(
            "{SERVICE}{}",
            r#"{"kind": "writes", "subject": "shop.shipping.service.fix_address", "object": "shop.order.model.Order.payment_ref", "value": "\"\"", "at": "shop/shipping/service.py:10@blob:3f2a9c1"}
"#
        ),
    );
    let s = repo.run(&["compare", "--base", &sha]);
    assert_eq!(s["command"], "compare");
    assert_eq!(result(&s, "shop.shipping.service.fix_address")["kind"], "counterexample", "{s}");
    assert_eq!(result(&s, "shop.shipping.service.update_shipping")["outcome"], "holds", "{s}");
}

#[test]
fn a_target_without_the_meaning_after_reobservation_is_missing() {
    let (repo, sha) = committed("meaning");
    let plan = fixed_plan();
    planned(&repo, &sha, &plan);
    implement(&repo, &plan, |l| l.to_string());
    // 観測し直すと、OrderPayment.ref は決済情報として使われていなかった。
    let payment = std::fs::read_to_string(repo.dir.join(".archsig/map/shop/payment/model.py.jsonl")).unwrap();
    repo.map("shop/payment/model.py", &payment.replace(PAYMENT_MEANING, ""));
    let s = repo.run(&["compare", "--plan", "split-order"]);
    let r = s["results"].as_array().unwrap().iter().find(|r| r["subject"] == "shop.payment.model.OrderPayment.ref").unwrap_or_else(|| panic!("{s}"));
    assert_eq!((r["kind"].as_str(), r["law"].as_str()), (Some("missing"), Some("payment-follows-order")), "{s}");
}

