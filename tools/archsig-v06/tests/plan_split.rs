//! AC6: `archsig plan split`(マニュアル第2章 6.、第5章 問い7の「分ける」)。

use serde_json::Value;

mod common;

use common::*;

/// 第2章 5. の直した候補(`reset_authorization` を呼ぶ)を、読んだ ArchMap の上に置く。
fn fixed(name: &str) -> Repo {
    let repo = shop(name);
    repo.map("shop/shipping/address.py", ADDRESS);
    repo.write(".archsig/plans/split-order/plan.jsonl", &fixed_plan());
    repo
}

fn lines(repo: &Repo, path: &str) -> Vec<Value> {
    let text = std::fs::read_to_string(repo.dir.join(path)).unwrap_or_else(|e| panic!("{path}: {e}"));
    text.lines().map(|l| serde_json::from_str(l).unwrap()).collect()
}

fn has(atoms: &[Value], kind: &str, subject: &str, object: Option<&str>) -> bool {
    atoms.iter().any(|a| a["kind"] == kind && a["subject"] == subject && object.is_none_or(|o| a["object"] == o))
}

const UPDATE: &str = "shop.shipping.service.update_shipping";
const RESET_OP: &str = "shop.payment.service.reset_authorization";

#[test]
fn the_plan_of_chapter_2_is_split_into_three_locals() {
    let repo = fixed("ch2");
    let s = repo.run(&["plan", "split", "split-order"]);
    let r = result(&s, "split-order");
    assert_eq!((r["question"].as_str(), r["outcome"].as_str()), (Some("split"), Some("holds")), "{s}");

    // 書き出した局所の候補は、ちょうどこの三つ。
    let dir = repo.dir.join(".archsig/plans/split-order");
    let mut locals: Vec<String> = Vec::new();
    let mut stack = vec![dir.clone()];
    while let Some(d) = stack.pop() {
        for e in std::fs::read_dir(&d).unwrap().map(|e| e.unwrap().path()) {
            if e.is_dir() {
                stack.push(e);
            } else if e.file_name().unwrap() == "plan.jsonl" && d != dir {
                locals.push(d.strip_prefix(&dir).unwrap().to_string_lossy().to_string());
            }
        }
    }
    locals.sort();
    assert_eq!(locals, ["shop/order", "shop/payment", "shop/shipping"]);

    // 局所をまたぐ呼び出しと引数渡し、局所をまたぐ corresponds が共有に入る。
    let shared = lines(&repo, ".archsig/plans/split-order/shop/payment/shared.jsonl");
    assert!(has(&shared, "calls", UPDATE, Some(RESET_OP)), "{shared:?}");
    assert!(has(&shared, "passes", &format!("{UPDATE}->{RESET_OP}"), None), "{shared:?}");
    assert!(has(&shared, "corresponds", "shop.order.model.Order.shipping_address", Some("shop.shipping.model.OrderShipping.address")));
    assert!(has(&shared, "corresponds", "shop.order.model.Order.payment_ref", Some("shop.payment.model.OrderPayment.ref")));
    // 引数の対応は配送の局所に閉じるので、共有に入らない。
    assert!(!has(&shared, "corresponds", &format!("{UPDATE}.$order"), None), "{shared:?}");
    assert_eq!(shared, lines(&repo, ".archsig/plans/split-order/shop/shipping/shared.jsonl"));

    // 局所の候補は、見出しとその局所の Atom を持つ。元は候補全体と同じ。
    let payment = lines(&repo, ".archsig/plans/split-order/shop/payment/plan.jsonl");
    assert_eq!((payment[0]["kind"].as_str(), payment[0]["subject"].as_str(), payment[0]["base"].as_str()), (Some("plan"), Some("split-order/shop/payment"), Some("a1b2c3d")));
    assert!(has(&payment, "writes", RESET_OP, Some("shop.payment.model.OrderPayment.ref")), "{payment:?}");
    let shipping = lines(&repo, ".archsig/plans/split-order/shop/shipping/plan.jsonl");
    assert!(has(&shipping, "writes", UPDATE, Some("shop.shipping.model.OrderShipping.address")), "{shipping:?}");
    assert!(has(&shipping, "corresponds", &format!("{UPDATE}.$order"), None), "{shipping:?}");
    let order = lines(&repo, ".archsig/plans/split-order/shop/order/plan.jsonl");
    assert!(has(&order, "removes", "shop.order.model.Order", None), "{order:?}");

    // 合わせると候補全体になる(第6章の検算データ)。
    let detail = repo.run(&["show", r["id"].as_str().unwrap()]);
    let mut parts: Vec<Value> = detail["check"]["shared"].as_array().unwrap().clone();
    for l in detail["check"]["locals"].as_array().unwrap() {
        parts.extend(l["atoms"].as_array().unwrap().iter().cloned());
    }
    let plan = lines(&repo, ".archsig/plans/split-order/plan.jsonl");
    let mut whole: Vec<String> = plan.iter().filter(|a| a["kind"] != "plan").map(|a| a.to_string()).collect();
    let mut parts: Vec<String> = parts.iter().map(|a| a.to_string()).collect();
    whole.sort();
    parts.sort();
    assert_eq!(parts, whole);
}

#[test]
fn a_local_plan_can_be_checked() {
    let repo = fixed("local-check");
    repo.run(&["plan", "split", "split-order"]);
    let s = repo.run(&["plan", "check", "split-order/shop/payment"]);
    assert_eq!(s["command"], "plan check", "{s}");
}

#[test]
fn a_correspondence_without_one_target_is_a_conflict_and_nothing_is_written() {
    for (name, extra) in [
        (
            "conflict-undecided",
            r#"{"kind": "corresponds", "subject": "shop.order.model.Order.order_id", "object": "shop.shipping.model.OrderShipping.order_id | shop.payment.model.OrderPayment.order_id", "at": "plan:split-order"}
"#,
        ),
        (
            "conflict-trailing-bar",
            r#"{"kind": "corresponds", "subject": "shop.order.model.Order.order_id", "object": "shop.shipping.model.OrderShipping.order_id |", "at": "plan:split-order"}
"#,
        ),
        (
            // 残る Address.country は自分自身にも対応するので、行き先が二つになる(設計 §3.6)。
            "conflict-with-itself",
            r#"{"kind": "corresponds", "subject": "shop.shipping.model.Address.country", "object": "shop.shipping.model.OrderShipping.order_id", "at": "plan:split-order"}
"#,
        ),
        (
            "conflict-two",
            r#"{"kind": "corresponds", "subject": "shop.order.model.Order.payment_ref", "object": "shop.shipping.model.OrderShipping.order_id", "at": "plan:split-order"}
"#,
        ),
    ] {
        let repo = shop(name);
        repo.map("shop/shipping/address.py", ADDRESS);
        repo.write(".archsig/plans/split-order/plan.jsonl", &format!("{}{extra}", fixed_plan()));
        let s = repo.run(&["plan", "split", "split-order"]);
        let results = s["results"].as_array().unwrap();
        assert!(!results.is_empty() && results.iter().all(|r| r["outcome"] == "fails" && r["kind"] == "conflict"), "{s}");
        assert!(!repo.dir.join(".archsig/plans/split-order/shop").exists(), "{name}: 書き出さない");
    }
}

#[test]
fn a_question_mark_name_is_silent_and_nothing_is_written() {
    let repo = shop("question");
    repo.map("shop/shipping/address.py", ADDRESS);
    let extra = r#"{"kind": "calls", "subject": "shop.shipping.service.update_shipping", "object": "?notify", "at": "plan:split-order"}
"#;
    repo.write(".archsig/plans/split-order/plan.jsonl", &format!("{}{extra}", fixed_plan()));
    let s = repo.run(&["plan", "split", "split-order"]);
    let r = result(&s, "?notify");
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unresolved")), "{s}");
    assert!(s["next"].as_array().unwrap().iter().any(|n| n["element"] == UPDATE), "{s}");
    assert!(!repo.dir.join(".archsig/plans/split-order/shop").exists());
}

#[test]
fn another_reading_can_be_chosen() {
    let repo = fixed("reading");
    repo.write(".archsig/law/shop.law", &format!("{LAW}\nreading files = file\n"));
    let s = repo.run(&["plan", "split", "split-order", "--reading", "files"]);
    assert_eq!(result(&s, "split-order")["outcome"], "holds", "{s}");
    assert!(repo.dir.join(".archsig/plans/split-order/shop/payment/service.py/plan.jsonl").is_file());
    assert!(!repo.dir.join(".archsig/plans/split-order/shop/payment/plan.jsonl").exists());
}

#[test]
fn a_local_that_cannot_be_a_directory_writes_nothing() {
    // 局所 `zz/..` は、候補のディレクトリの外に重なる。名前の順で後ろに来ても、前の局所を書き出さない。
    let repo = fixed("bad-local");
    let extra = r#"{"kind": "defines", "subject": "app.main", "value": "operation", "file": "zz/../app.py", "at": "plan:split-order"}
"#;
    repo.write(".archsig/plans/split-order/plan.jsonl", &format!("{}{extra}", fixed_plan()));
    let err = repo.fail(&["plan", "split", "split-order"]);
    assert!(err.contains("局所 zz/.."), "{err}");
    assert!(!repo.dir.join(".archsig/plans/split-order/shop").exists());
}


#[test]
fn a_write_through_a_field_of_another_local_is_shared() {
    // via のフィールドも、その Atom が名指す要素である(設計 §6)。Order.shipping_address は shop/order の局所にある。
    let repo = shop("via");
    repo.write(
        ".archsig/plans/p/plan.jsonl",
        &format!(
            "{}\n{}\n",
            r#"{"kind": "defines", "subject": "shop.shipping.service.update_shipping", "value": "operation", "params": {"order": "shop.order.model.Order", "new": "shop.shipping.model.Address"}, "file": "shop/shipping/service.py", "at": "plan:p"}"#,
            r#"{"kind": "writes", "subject": "shop.shipping.service.update_shipping", "via": ["shop.order.model.Order.shipping_address"], "object": "shop.shipping.model.Address.country", "value": "\"JP\"", "at": "plan:p"}"#
        ),
    );
    let s = repo.run(&["plan", "split", "p"]);
    assert_eq!(result(&s, "p")["outcome"], "holds", "{s}");
    let shared = lines(&repo, ".archsig/plans/p/shop/shipping/shared.jsonl");
    assert!(has(&shared, "writes", UPDATE, Some("shop.shipping.model.Address.country")), "{shared:?}");
    let local = lines(&repo, ".archsig/plans/p/shop/shipping/plan.jsonl");
    assert!(!has(&local, "writes", UPDATE, None), "via が別の局所を名指す書き込みは、局所の候補に入らない: {local:?}");
}

#[test]
fn a_call_to_an_element_resolved_to_an_unread_source_has_no_decided_local() {
    // a.f は b.g を呼ぶ候補を書く。b.g の定義はなく、`resolves` が b/g.py を指す。
    // b.g の局所は b/g.py を読むまで決まらないので、局所をまたぐかが決まらない。`unread` で沈黙し、b/g.py を返す(設計 §3.3)。
    let law = r#"sources "**/*.py"

reading module = dir(depth: 1)
"#;
    let run = |name: &str, resolves: &str, observed_b: bool| {
        let repo = Repo::new(name);
        repo.write(".archsig/law/m.law", law);
        repo.write("a/f.py", "# source\n");
        repo.write("b/g.py", "# source\n");
        repo.map(
            "a/f.py",
            &format!(
                "{{\"kind\": \"observed\", \"subject\": \"a/f.py\", \"scope\": \"structure\", \"at\": \"a/f.py@blob:aaaaaaa\"}}\n{{\"kind\": \"defines\", \"subject\": \"a.f\", \"value\": \"operation\", \"params\": {{}}, \"at\": \"a/f.py:1@blob:aaaaaaa\"}}\n{{\"kind\": \"resolves\", \"subject\": \"b.g\", \"object\": \"{resolves}\", \"at\": \"a/f.py:2@blob:aaaaaaa\"}}\n"
            ),
        );
        if observed_b {
            repo.map("b/g.py", "{\"kind\": \"observed\", \"subject\": \"b/g.py\", \"scope\": \"structure\", \"at\": \"b/g.py@blob:bbbbbbb\"}\n");
        }
        repo.write(".archsig/plans/p/plan.jsonl", "{\"kind\": \"calls\", \"subject\": \"a.f\", \"object\": \"b.g\", \"at\": \"plan:p\"}\n");
        repo.run(&["plan", "split", "p"])
    };
    let s = run("split-unread-resolves", "b/g.py", false);
    let r = result(&s, "b.g");
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unread")), "{s}");
    assert!(s["next"].as_array().unwrap().iter().any(|n| n["read"] == "b/g.py" && n["scope"] == "structure" && n["decides"].as_array().unwrap().contains(&r["id"])), "{s}");
    // b/g.py の構造を読んだのに b.g の定義がなければ、`unresolved` で沈黙する。
    let s = run("split-read-resolves", "b/g.py", true);
    let r = result(&s, "b.g");
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unresolved")), "{s}");
    // 外部を指す要素は、これまでどおりどの局所にも属さず、呼び出しは a の局所に入る。
    let s = run("split-external-resolves", "external:lib", false);
    assert_eq!(result(&s, "p")["outcome"], "holds", "{s}");
}
