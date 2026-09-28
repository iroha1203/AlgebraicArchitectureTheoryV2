//! マニュアル第2章「一つの変更を最初から最後まで」の一周。

use std::path::{Path, PathBuf};
use std::process::Command;

use serde_json::Value;

fn fixture() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/shop")
}

struct Repo {
    dir: PathBuf,
}

impl Repo {
    fn new(name: &str) -> Repo {
        let dir = std::env::temp_dir().join(format!("archsig-ch2-{name}-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        copy(&fixture().join("repo"), &dir);
        let repo = Repo { dir };
        repo.git(&["init", "-q"]);
        repo.git(&["-c", "user.name=t", "-c", "user.email=t@example.com", "commit", "-q", "--allow-empty", "-m", "init"]);
        repo.commit("sources");
        repo
    }

    fn git(&self, args: &[&str]) -> String {
        let out = Command::new("git").arg("-C").arg(&self.dir).args(args).output().unwrap();
        assert!(out.status.success(), "git {args:?}: {}", String::from_utf8_lossy(&out.stderr));
        String::from_utf8_lossy(&out.stdout).trim().to_string()
    }

    fn commit(&self, msg: &str) -> String {
        self.git(&["add", "-A"]);
        self.git(&["-c", "user.name=t", "-c", "user.email=t@example.com", "commit", "-q", "--allow-empty", "-m", msg]);
        self.git(&["rev-parse", "HEAD"])
    }

    fn archsig(&self, args: &[&str]) -> Value {
        let out = Command::new(env!("CARGO_BIN_EXE_archsig")).current_dir(&self.dir).args(args).output().unwrap();
        assert!(out.status.success(), "archsig {args:?}: {}", String::from_utf8_lossy(&out.stderr));
        serde_json::from_slice(&out.stdout).unwrap()
    }

    fn record(&self, files: &[&str]) {
        let mut args = vec!["record".to_string()];
        args.extend(files.iter().map(|f| fixture().join("atoms").join(f).display().to_string()));
        let args: Vec<&str> = args.iter().map(String::as_str).collect();
        self.archsig(&args);
    }

    fn plan(&self, file: &str, base: &str) {
        let text = std::fs::read_to_string(fixture().join("plans").join(file)).unwrap().replace("BASE", base);
        let dir = self.dir.join(".archsig/plans/split-order");
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(dir.join("plan.jsonl"), text).unwrap();
    }

    fn show(&self, id: &str) -> Value {
        self.archsig(&["show", id])
    }
}

impl Drop for Repo {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.dir);
    }
}

fn copy(from: &Path, to: &Path) {
    std::fs::create_dir_all(to).unwrap();
    for e in std::fs::read_dir(from).unwrap() {
        let e = e.unwrap();
        let target = to.join(e.file_name());
        if e.file_type().unwrap().is_dir() {
            copy(&e.path(), &target);
        } else {
            std::fs::copy(e.path(), target).unwrap();
        }
    }
}

fn results(v: &Value) -> &Vec<Value> {
    v["results"].as_array().unwrap()
}

const BEFORE: &[&str] = &["before/order_model.jsonl", "before/shipping_service.jsonl"];
const AFTER: &[&str] = &[
    "after/order_model.jsonl",
    "after/shipping_model.jsonl",
    "after/payment_model.jsonl",
    "after/payment_service.jsonl",
    "after/shipping_service.jsonl",
];

/// 候補を検査し、直し、分け、実装して比べるところまで。
fn prepared(name: &str) -> (Repo, String) {
    let repo = Repo::new(name);
    repo.record(BEFORE);
    repo.record(&["address.jsonl"]);
    let base = repo.commit("archmap");
    repo.plan("split-order-fixed.jsonl", &base);
    (repo, base)
}

#[test]
fn law_check_reads_the_chapter_2_law() {
    let repo = Repo::new("law");
    let v = repo.archsig(&["law", "check"]);
    assert_eq!(v["laws"][0]["name"], "payment-follows-order");
    assert_eq!(v["laws"][0]["rule"], "changes commute");
}

#[test]
fn status_separates_unread_from_stale() {
    let repo = Repo::new("status");
    repo.record(BEFORE);
    let v = repo.archsig(&["status"]);
    assert_eq!(v["stale"].as_array().unwrap().len(), 0);
    let unread: Vec<&str> = v["unread"].as_array().unwrap().iter().map(|u| u["source"].as_str().unwrap()).collect();
    assert_eq!(unread, vec!["shop/payment/charge.py", "shop/shipping/address.py"]);

    std::fs::write(repo.dir.join("shop/shipping/service.py"), "# changed\n").unwrap();
    let v = repo.archsig(&["status"]);
    let stale: Vec<&str> = v["stale"].as_array().unwrap().iter().map(|s| s["scope"].as_str().unwrap()).collect();
    assert_eq!(stale, vec!["meaning:payment-info", "structure"]);
}

#[test]
fn plan_check_is_silent_until_the_callee_is_read() {
    let repo = Repo::new("silent");
    repo.record(BEFORE);
    repo.plan("split-order.jsonl", "HEAD");
    let v = repo.archsig(&["plan", "check", "split-order"]);
    let r = &results(&v)[0];
    assert_eq!(r["outcome"], "silent");
    assert_eq!(r["reason"], "unread");
    assert_eq!(v["next"][0]["read"], "shop/shipping/address.py");
    assert_eq!(v["next"][0]["scope"], "structure");
}

#[test]
fn plan_check_finds_the_cross_country_counterexample() {
    let repo = Repo::new("counter");
    repo.record(BEFORE);
    repo.record(&["address.jsonl"]);
    repo.plan("split-order.jsonl", "HEAD");
    let v = repo.archsig(&["plan", "check", "split-order"]);
    assert_eq!(results(&v).len(), 1);
    let r = &results(&v)[0];
    assert_eq!(r["outcome"], "fails");
    assert_eq!(r["kind"], "counterexample");
    assert_eq!(r["subject"], "shop.shipping.service.update_shipping");

    let d = repo.show(r["id"].as_str().unwrap());
    let c = &d["check"];
    assert_eq!(c["field"], "shop.payment.model.OrderPayment.ref");
    assert_eq!(c["input"][0]["when"], "$new.country != $order.shipping_address.country");
    assert_eq!(c["input"][0]["holds"], true);
    assert_eq!(c["operate_then_migrate"]["value"], "None");
    assert_eq!(c["migrate_then_operate"]["value"], "入力(shop.order.model.Order.payment_ref)");
    assert!(c["operate_then_migrate"]["last_write"].as_str().unwrap().starts_with("shop/shipping/service.py:7@blob:"));
    assert!(c["migrate_then_operate"]["last_write"].is_null());
    assert_eq!(c["failing_branches"], 1);
    assert_eq!(c["branches"], 2);
    assert_eq!(d["conditions"].as_array().unwrap().len(), 3);
}

#[test]
fn fixed_plan_holds_on_both_branches() {
    let (repo, _) = prepared("holds");
    let v = repo.archsig(&["plan", "check", "split-order"]);
    assert_eq!(results(&v).len(), 1);
    let r = &results(&v)[0];
    assert_eq!(r["outcome"], "holds");
    let d = repo.show(r["id"].as_str().unwrap());
    let branches = d["check"]["branches"].as_array().unwrap();
    assert_eq!(branches.len(), 2);
    for b in branches {
        let vals = &b["values"]["shop.payment.model.OrderPayment.ref"];
        assert_eq!(vals["operate_then_migrate"], vals["migrate_then_operate"]);
    }
}

#[test]
fn split_puts_the_cross_local_call_in_shared() {
    let (repo, _) = prepared("split");
    let v = repo.archsig(&["plan", "split", "split-order"]);
    let written: Vec<&str> = v["written"].as_array().unwrap().iter().map(|w| w.as_str().unwrap()).collect();
    assert_eq!(written, vec!["split-order/shop/order", "split-order/shop/payment", "split-order/shop/shipping"]);
    let shared = results(&v).iter().find(|r| r["subject"] == "shared").unwrap();
    let d = repo.show(shared["id"].as_str().unwrap());
    let kinds: Vec<(String, String)> = d["check"]["atoms"]
        .as_array()
        .unwrap()
        .iter()
        .map(|a| (a["atom"]["kind"].as_str().unwrap().to_string(), a["atom"]["subject"].as_str().unwrap().to_string()))
        .collect();
    assert!(kinds.contains(&("calls".to_string(), "shop.shipping.service.update_shipping".to_string())));
    assert!(kinds.contains(&(
        "passes".to_string(),
        "shop.shipping.service.update_shipping->shop.payment.service.reset_authorization".to_string()
    )));
    assert!(kinds.contains(&("corresponds".to_string(), "shop.order.model.Order.payment_ref".to_string())));
    assert!(repo.dir.join(".archsig/plans/split-order/shop/payment/plan.jsonl").exists());
}

fn implement(repo: &Repo) {
    copy(&fixture().join("after"), &repo.dir);
    repo.record(AFTER);
}

#[test]
fn compare_after_implementation_matches_the_plan() {
    let (repo, base) = prepared("compare");
    implement(&repo);
    let v = repo.archsig(&["compare", "--plan", "split-order"]);
    assert_eq!(v["base"], base);
    for r in results(&v) {
        assert_eq!(r["outcome"], "holds", "{r}");
    }
    let plan = results(&v).iter().find(|r| r["subject"] == "plan").unwrap();
    let d = repo.show(plan["id"].as_str().unwrap());
    assert_eq!(d["check"]["planned_structure_atoms"], d["check"]["observed"]);
}

#[test]
fn compare_reports_an_empty_string_instead_of_none() {
    let (repo, _) = prepared("mismatch");
    implement(&repo);
    let service = repo.dir.join("shop/payment/service.py");
    let text = std::fs::read_to_string(&service).unwrap().replace("payment.ref = None", "payment.ref = \"\"");
    std::fs::write(&service, text).unwrap();
    let atoms = std::fs::read_to_string(fixture().join("atoms/after/payment_service.jsonl"))
        .unwrap()
        .replace("\"value\": \"None\"", "\"value\": \"\\\"\\\"\"");
    let tmp = repo.dir.join("payment_service.jsonl");
    std::fs::write(&tmp, atoms).unwrap();
    repo.archsig(&["record", tmp.to_str().unwrap()]);

    let v = repo.archsig(&["compare", "--plan", "split-order"]);
    let kinds: Vec<(&str, &str)> = results(&v)
        .iter()
        .map(|r| (r["kind"].as_str().unwrap_or("-"), r["subject"].as_str().unwrap()))
        .collect();
    assert!(kinds.contains(&("counterexample", "shop.shipping.service.update_shipping")), "{kinds:?}");
    assert!(kinds.contains(&("mismatch", "shop.payment.service.reset_authorization")), "{kinds:?}");
    let extra = results(&v)
        .iter()
        .filter(|r| r["kind"] == "mismatch")
        .map(|r| repo.show(r["id"].as_str().unwrap()))
        .find(|d| d["check"]["detail"] == "候補にない書き込み")
        .expect("候補にない書き込みが挙がる");
    assert_eq!(extra["check"]["observed"]["value"], "\"\"");
}
