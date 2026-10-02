//! AC9: マニュアル第2章の一周を、一つのリポジトリの上で順に通す。
//! 観測は `archsig record` で記録し、版はツールに補わせる。

use std::collections::BTreeMap;
use std::path::Path;

use serde_json::Value;

mod common;

use common::*;

const UPDATE: &str = "shop.shipping.service.update_shipping";
const RESET_OP: &str = "shop.payment.service.reset_authorization";

/// 題材の観測から、ソースの版を外す。`record` が今のソースの版を補う。
fn unversioned(atoms: &str) -> String {
    ["@blob:3f2a9c1", "@blob:1d9e3b4", "@blob:6a1b2c3", "@blob:9f2c4e7"].iter().fold(atoms.to_string(), |s, v| s.replace(v, ""))
}

fn record(repo: &Repo, atoms: &str) {
    let f = repo.dir.join("observed.jsonl");
    std::fs::write(&f, atoms).unwrap();
    repo.run(&["record", f.to_str().unwrap()]);
    std::fs::remove_file(f).unwrap();
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

fn lines(repo: &Repo, path: &str) -> Vec<Value> {
    std::fs::read_to_string(repo.dir.join(path)).unwrap().lines().map(|l| serde_json::from_str(l).unwrap()).collect()
}

/// 候補の構造 Atom を実装したコードの観測。`defines` は `file` のソースに、それ以外は `subject` の操作を定義したソースに置く。
fn implementation(plan: &str, edit: impl Fn(&str) -> String) -> BTreeMap<String, String> {
    let atoms: Vec<Value> = plan.lines().map(|l| serde_json::from_str(l).unwrap()).collect();
    let file_of: BTreeMap<String, String> = atoms
        .iter()
        .filter(|a| a["kind"] == "defines")
        .map(|a| (a["subject"].as_str().unwrap().to_string(), a["file"].as_str().unwrap().to_string()))
        .collect();
    let mut out: BTreeMap<String, String> = BTreeMap::new();
    for (i, a) in atoms.iter().enumerate().filter(|(_, a)| !matches!(a["kind"].as_str(), Some("plan" | "corresponds" | "removes"))) {
        let owner = a["subject"].as_str().unwrap().split("->").next().unwrap();
        let file = a["file"].as_str().map(str::to_string).unwrap_or_else(|| file_of[owner].clone());
        let mut a = a.clone();
        a.as_object_mut().unwrap().remove("file");
        a["at"] = Value::String(format!("{file}:{}", i + 1));
        out.entry(file).or_default().push_str(&edit(&(a.to_string() + "\n")));
    }
    out
}

/// 第2章の一周を 4. まで進め、変更前を用意し、実装して `compare --plan` を返す。
/// 実装は、候補の構造 Atom を `edit` で書き換えたものになる。
fn walk(name: &str, edit: impl Fn(&str) -> String) -> (Vec<Value>, Value) {
    let repo = Repo::new(name);
    repo.write(".archsig/law/shop.law", LAW);
    for f in ["shop/shipping/service.py", "shop/order/model.py", "shop/shipping/model.py", "shop/shipping/address.py"] {
        repo.write(f, "# before\n");
    }
    let mut steps = Vec::new();

    // 4. 候補を書いて検査する。ArchMap には、まだ address.py の構造がない。
    record(&repo, &unversioned(&format!("{SERVICE}{ORDER}{ADDRESS_MODEL}")));
    repo.write(".archsig/plans/split-order/plan.jsonl", SPLIT);
    steps.push(repo.run(&["plan", "check", "split-order"]));

    // 沈黙の next のとおり address.py を読み足して、もう一度検査する。
    record(&repo, &unversioned(ADDRESS));
    steps.push(repo.run(&["plan", "check", "split-order"]));

    // 5. 人が判断し、候補を直す。
    let plan = fixed_plan();
    repo.write(".archsig/plans/split-order/plan.jsonl", &plan);
    steps.push(repo.run(&["plan", "check", "split-order"]));

    // 6. 仕事を分ける。
    steps.push(repo.run(&["plan", "split", "split-order"]));
    steps.push(Value::Array(
        ["shop/order", "shop/payment", "shop/shipping"]
            .iter()
            .map(|l| Value::Array(lines(&repo, &format!(".archsig/plans/split-order/{l}/plan.jsonl"))))
            .chain([Value::Array(lines(&repo, ".archsig/plans/split-order/shop/payment/shared.jsonl"))])
            .collect(),
    ));

    // 7. 実装する前の ArchMap とソースを、変更前として取っておく(使う側の仕事)。
    let before = Repo::new(&format!("{name}-before"));
    copy(&repo.dir, &before.dir);

    // 実装して、変わったソースを観測し直す。注文のモデルは消えた。
    std::fs::remove_file(repo.dir.join("shop/order/model.py")).unwrap();
    repo.run(&["record", "--drop", "shop/order/model.py"]);
    let mut observed = String::new();
    for (file, mut text) in implementation(&plan, edit) {
        repo.write(&file, "# after\n");
        if file == "shop/shipping/model.py" {
            // Address の型は変わらない。
            text.push_str(&unversioned(&ADDRESS_MODEL.lines().filter(|l| l.contains("\"defines\"")).map(|l| format!("{l}\n")).collect::<String>()));
        }
        if file == "shop/shipping/service.py" {
            text.push_str(r#"{"kind": "resolves", "subject": "shop.shipping.address.normalize_address", "object": "shop/shipping/address.py", "at": "shop/shipping/service.py:1"}
"#);
        }
        if file == "shop/payment/model.py" {
            text.push_str(r#"{"kind": "meaning", "subject": "shop.payment.model.OrderPayment.ref", "meaning": "payment-info", "uses": ["shop/payment/charge.py:22@blob:8b41d07"], "at": "shop/payment/model.py:5"}
"#);
        }
        observed.push_str(&format!(
            "{{\"kind\": \"observed\", \"subject\": \"{file}\", \"scope\": \"structure\"}}\n{{\"kind\": \"observed\", \"subject\": \"{file}\", \"scope\": \"meaning:payment-info\"}}\n{text}"
        ));
    }
    record(&repo, &observed);
    let compared = repo.run(&["compare", "--before", before.dir.to_str().unwrap(), "--plan", "split-order"]);
    // 結果の詳細も一緒に返す。
    let details: Vec<Value> = compared["results"].as_array().unwrap().iter().map(|r| repo.run(&["show", r["id"].as_str().unwrap()])).collect();
    steps.push(compared);
    (steps, Value::Array(details))
}

#[test]
fn the_change_of_chapter_2_goes_around() {
    let (steps, details) = walk("ch2", |l| l.to_string());

    // 1. 最初の plan check は unread で沈黙し、address.py を返す。
    let first = &steps[0];
    let r = result(first, UPDATE);
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unread")), "{first}");
    assert!(first["next"].as_array().unwrap().iter().any(|n| n["read"] == "shop/shipping/address.py" && n["scope"] == "structure"), "{first}");

    // 2. 読み足すと、国をまたぐ分岐で反例が出る。
    let second = &steps[1];
    assert_eq!(result(second, UPDATE)["kind"], "counterexample", "{second}");

    // 3. reset_authorization を呼ぶ候補では、2分岐とも成り立つ。
    let third = &steps[2];
    assert_eq!(result(third, UPDATE)["outcome"], "holds", "{third}");

    // 4. plan split が三つの局所に分け、呼び出しと引数渡しが共有に入る。
    let split = &steps[3];
    assert_eq!(result(split, "split-order")["outcome"], "holds", "{split}");
    let shared = steps[4].as_array().unwrap()[3].as_array().unwrap().clone();
    assert!(shared.iter().any(|a| a["kind"] == "calls" && a["subject"] == UPDATE && a["object"] == RESET_OP), "{shared:?}");
    assert!(shared.iter().any(|a| a["kind"] == "passes" && a["subject"] == format!("{UPDATE}->{RESET_OP}")), "{shared:?}");

    // 5. 実装後の compare --plan がすべて成り立つ。
    let compared = &steps[5];
    let results = compared["results"].as_array().unwrap();
    assert!(!results.is_empty() && results.iter().all(|r| r["outcome"] == "holds"), "{compared}");
    let matched = details.as_array().unwrap().iter().find(|d| d["subject"] == "split-order").unwrap_or_else(|| panic!("{compared}"));
    assert_eq!((matched["check"]["planned"].as_u64(), matched["check"]["observed"].as_u64()), (Some(13), Some(13)));
    let update = details.as_array().unwrap().iter().find(|d| d["subject"] == UPDATE).unwrap();
    assert_eq!(update["check"]["branches"].as_array().unwrap().len(), 2, "{update}");
}

#[test]
fn an_empty_string_in_the_payment_implementation_is_caught() {
    // 6. 決済側が OrderPayment.ref を None ではなく空文字にした。
    let (steps, details) = walk("ch2-empty", |l| {
        if l.contains("\"kind\":\"writes\"") && l.contains(&format!("\"subject\":\"{RESET_OP}\"")) {
            l.replace("\"value\":\"None\"", "\"value\":\"\\\"\\\"\"")
        } else {
            l.to_string()
        }
    });
    let compared = &steps[5];
    assert_eq!(result(compared, UPDATE)["kind"], "counterexample", "{compared}");
    let mismatches: Vec<&Value> = details.as_array().unwrap().iter().filter(|d| d["kind"] == "mismatch").collect();
    assert_eq!(mismatches.len(), 2, "{compared}");
    // 食い違いの場所は、決済のサービスの書き込みである。
    assert!(mismatches.iter().any(|d| d["check"]["observed"]["at"].as_str().is_some_and(|a| a.starts_with("shop/payment/service.py"))), "{mismatches:?}");
}
