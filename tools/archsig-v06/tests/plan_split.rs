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

    // 局所をまたぐ呼び出しと引数渡し、局所をまたぐ corresponds が共有に入る。共有の条件は、結果の詳細に並ぶ。
    let shared: Vec<Value> = repo.run(&["show", r["id"].as_str().unwrap()])["check"]["shared"].as_array().unwrap().clone();
    assert!(has(&shared, "calls", UPDATE, Some(RESET_OP)), "{shared:?}");
    assert!(has(&shared, "passes", &format!("{UPDATE}->{RESET_OP}"), None), "{shared:?}");
    assert!(has(&shared, "corresponds", "shop.order.model.Order.shipping_address", Some("shop.shipping.model.OrderShipping.address")));
    assert!(has(&shared, "corresponds", "shop.order.model.Order.payment_ref", Some("shop.payment.model.OrderPayment.ref")));
    // 引数の対応は配送の局所に閉じるので、共有に入らない。
    assert!(!has(&shared, "corresponds", &format!("{UPDATE}.$order"), None), "{shared:?}");
    // 局所の候補は、その局所の Atom と共有の条件を、元の候補に書いた順のまま持つ(手順の順は Atom の順。マニュアル第3章)。
    // 配送の局所では、共有の reset_authorization の呼び出しが、局所の書き込みより前に並ぶ。
    let original: Vec<Value> = fixed_plan().lines().map(|l| serde_json::from_str(l).unwrap()).collect();
    for local in ["shop/payment", "shop/shipping", "shop/order"] {
        let atoms = lines(&repo, &format!(".archsig/plans/split-order/{local}/plan.jsonl"));
        for a in &shared {
            assert!(atoms.contains(a), "{local}: {a}");
        }
        let positions: Vec<usize> = atoms[1..].iter().map(|a| original.iter().position(|o| o == a).unwrap()).collect();
        assert!(positions.windows(2).all(|w| w[0] < w[1]), "{local}: {positions:?}");
    }

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
    let detail = repo.run(&["show", result(&s, "p")["id"].as_str().unwrap()]);
    let shared: Vec<Value> = detail["check"]["shared"].as_array().unwrap().clone();
    assert!(has(&shared, "writes", UPDATE, Some("shop.shipping.model.Address.country")), "{shared:?}");
    let locals = detail["check"]["locals"].as_array().unwrap();
    assert!(
        locals.iter().all(|l| !has(l["atoms"].as_array().unwrap(), "writes", UPDATE, None)),
        "via が別の局所を名指す書き込みは、局所の Atom に入らない: {detail}"
    );
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
    // 引数の要素 b.g.$x は、持ち主の操作 b.g で見る。
    let repo = Repo::new("split-unread-argument");
    repo.write(".archsig/law/m.law", law);
    repo.write("a/f.py", "# source\n");
    repo.write("b/g.py", "# source\n");
    repo.map(
        "a/f.py",
        "{\"kind\": \"observed\", \"subject\": \"a/f.py\", \"scope\": \"structure\", \"at\": \"a/f.py@blob:aaaaaaa\"}\n{\"kind\": \"defines\", \"subject\": \"a.f\", \"value\": \"operation\", \"params\": {}, \"at\": \"a/f.py:1@blob:aaaaaaa\"}\n{\"kind\": \"resolves\", \"subject\": \"b.g\", \"object\": \"b/g.py\", \"at\": \"a/f.py:2@blob:aaaaaaa\"}\n",
    );
    repo.write(".archsig/plans/p/plan.jsonl", "{\"kind\": \"passes\", \"subject\": \"a.f->a.f\", \"object\": \"b.g.$x\", \"value\": \"1\", \"at\": \"plan:p\"}\n");
    let t = repo.run(&["plan", "split", "p"]);
    assert_eq!((result(&t, "b.g.$x")["outcome"].as_str(), result(&t, "b.g.$x")["reason"].as_str()), (Some("silent"), Some("unread")), "{t}");
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
    // 指す先の違う `resolves` が二つ以上あれば、解決が決まらないので `unresolved` で沈黙する(外部を含んでも)。
    for (name, second) in [("split-two-resolves", "c/h.py"), ("split-external-and-source", "external:lib"), ("split-two-externals", "external:other")] {
        let first = if second == "external:other" { "external:lib" } else { "b/g.py" };
        let repo = Repo::new(name);
        repo.write(".archsig/law/m.law", law);
        repo.write("a/f.py", "# source\n");
        repo.write("b/g.py", "# source\n");
        repo.map(
            "a/f.py",
            &format!(
                "{{\"kind\": \"observed\", \"subject\": \"a/f.py\", \"scope\": \"structure\", \"at\": \"a/f.py@blob:aaaaaaa\"}}\n{{\"kind\": \"defines\", \"subject\": \"a.f\", \"value\": \"operation\", \"params\": {{}}, \"at\": \"a/f.py:1@blob:aaaaaaa\"}}\n{{\"kind\": \"resolves\", \"subject\": \"b.g\", \"object\": \"{first}\", \"at\": \"a/f.py:2@blob:aaaaaaa\"}}\n{{\"kind\": \"resolves\", \"subject\": \"b.g\", \"object\": \"{second}\", \"at\": \"a/f.py:3@blob:aaaaaaa\"}}\n"
            ),
        );
        repo.write(".archsig/plans/p/plan.jsonl", "{\"kind\": \"calls\", \"subject\": \"a.f\", \"object\": \"b.g\", \"at\": \"plan:p\"}\n");
        let s = repo.run(&["plan", "split", "p"]);
        let r = result(&s, "b.g");
        assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unresolved")), "{name}: {s}");
    }
}

#[test]
fn a_field_without_a_definition_belongs_to_the_local_of_its_type() {
    // a.f は b の型 b.M のフィールド b.M.x に書く。b.M.x の定義は観測していない。フィールドは型(`<型>.<名前>`)で見る。
    let law = r#"sources "**/*.py"

reading module = dir(depth: 1)
"#;
    let run = |name: &str, b_map: Option<&str>, write: &str| {
        let repo = Repo::new(name);
        repo.write(".archsig/law/m.law", law);
        repo.write("a/f.py", "# source\n");
        repo.write("b/m.py", "# source\n");
        repo.map(
            "a/f.py",
            "{\"kind\": \"observed\", \"subject\": \"a/f.py\", \"scope\": \"structure\", \"at\": \"a/f.py@blob:aaaaaaa\"}\n{\"kind\": \"defines\", \"subject\": \"a.f\", \"value\": \"operation\", \"params\": {}, \"at\": \"a/f.py:1@blob:aaaaaaa\"}\n{\"kind\": \"defines\", \"subject\": \"a.O\", \"value\": \"type\", \"at\": \"a/f.py:2@blob:aaaaaaa\"}\n{\"kind\": \"defines\", \"subject\": \"a.O.t\", \"value\": \"field\", \"type\": \"b.M\", \"at\": \"a/f.py:3@blob:aaaaaaa\"}\n{\"kind\": \"resolves\", \"subject\": \"b.M\", \"object\": \"b/m.py\", \"at\": \"a/f.py:4@blob:aaaaaaa\"}\n",
        );
        if let Some(m) = b_map {
            repo.map("b/m.py", m);
        }
        repo.write(".archsig/plans/p/plan.jsonl", write);
        let s = repo.run(&["plan", "split", "p"]);
        (repo, s)
    };
    let object = "{\"kind\": \"writes\", \"subject\": \"a.f\", \"object\": \"b.M.x\", \"value\": \"1\", \"at\": \"plan:p\"}\n";
    let via = "{\"kind\": \"writes\", \"subject\": \"a.f\", \"via\": [\"a.O.t\", \"b.M.x\"], \"object\": \"b.N.y\", \"value\": \"1\", \"at\": \"plan:p\"}\n";
    // 型 b.M の定義を読んでいなければ、b.M.x の局所は b/m.py を読むまで決まらない(`via` に書いても同じ)。
    for (name, write) in [("field-unread-type", object), ("field-unread-type-via", via)] {
        let (_, s) = run(name, None, write);
        let r = result(&s, "b.M.x");
        assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unread")), "{name}: {s}");
        assert!(s["next"].as_array().unwrap().iter().any(|n| n["read"] == "b/m.py" && n["decides"].as_array().unwrap().contains(&r["id"])), "{name}: {s}");
    }
    // 型 b.M を b/m.py で読んでいれば、b.M.x は b の局所に属し、a.f の書き込みは局所をまたぐので共有に入る。
    let b = "{\"kind\": \"observed\", \"subject\": \"b/m.py\", \"scope\": \"structure\", \"at\": \"b/m.py@blob:bbbbbbb\"}\n{\"kind\": \"defines\", \"subject\": \"b.M\", \"value\": \"type\", \"at\": \"b/m.py:1@blob:bbbbbbb\"}\n";
    // 型の種類が決まらない(`value` のない `defines`)ときも、頭の定義を観測していれば頭の局所で見る。
    // 型のメソッドの呼び出し(定義のない b.M.run)も同じ。
    let b_valueless = b.replace(", \"value\": \"type\"", "");
    let call = "{\"kind\": \"calls\", \"subject\": \"a.f\", \"object\": \"b.M.run\", \"at\": \"plan:p\"}\n";
    for (name, m, write, kind, object) in [
        ("field-read-type", b.to_string(), object, "writes", "b.M.x"),
        ("field-read-valueless-type", b_valueless, object, "writes", "b.M.x"),
        ("method-read-type", b.to_string(), call, "calls", "b.M.run"),
    ] {
        let (repo, s) = run(name, Some(&m), write);
        let r = result(&s, "p");
        assert_eq!(r["outcome"], "holds", "{name}: {s}");
        let detail = repo.run(&["show", r["id"].as_str().unwrap()]);
        let shared: Vec<Value> = detail["check"]["shared"].as_array().unwrap().clone();
        assert!(has(&shared, kind, "a.f", Some(object)), "{name}: {detail}");
    }
    // 要素自身の定義を観測していれば、頭と別のソースでも、定義したソースの局所に属する。ここでは b.M.x を a/f.py で定義したので、書き込みは a の局所に入る。
    let (repo, s) = run("field-defined-in-a", Some(b), "{\"kind\": \"defines\", \"subject\": \"b.M.x\", \"value\": \"field\", \"file\": \"a/f.py\", \"at\": \"plan:p\"}\n{\"kind\": \"writes\", \"subject\": \"a.f\", \"object\": \"b.M.x\", \"value\": \"1\", \"at\": \"plan:p\"}\n");
    assert_eq!(result(&s, "p")["outcome"], "holds", "{s}");
    let local = lines(&repo, ".archsig/plans/p/a/plan.jsonl");
    assert!(has(&local, "writes", "a.f", Some("b.M.x")), "{local:?}");
    // 要素自身の `resolves` が外部を指せば、外部の要素として、頭を読んでいてもいなくても、どの局所にも属さない(書き込みは a の局所)。
    let ext = "{\"kind\": \"resolves\", \"subject\": \"b.M.run\", \"object\": \"external:lib\", \"at\": \"plan:p\"}\n{\"kind\": \"calls\", \"subject\": \"a.f\", \"object\": \"b.M.run\", \"at\": \"plan:p\"}\n";
    for (name, m) in [("method-external-read-type", Some(b)), ("method-external-unread-type", None)] {
        let (repo, s) = run(name, m, ext);
        assert_eq!(result(&s, "p")["outcome"], "holds", "{name}: {s}");
        let local = lines(&repo, ".archsig/plans/p/a/plan.jsonl");
        assert!(has(&local, "calls", "a.f", Some("b.M.run")), "{name}: {local:?}");
    }
    // 要素自身に局所の決まらない解決があれば、それを先に見る(頭を読んでいても沈黙する)。
    let (_, s) = run("field-own-resolves", Some(b), "{\"kind\": \"resolves\", \"subject\": \"b.M.x\", \"object\": \"c/x.py\", \"at\": \"plan:p\"}\n{\"kind\": \"writes\", \"subject\": \"a.f\", \"object\": \"b.M.x\", \"value\": \"1\", \"at\": \"plan:p\"}\n");
    let r = result(&s, "b.M.x");
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unread")), "{s}");
    assert!(s["next"].as_array().unwrap().iter().any(|n| n["read"] == "c/x.py"), "{s}");
}

#[test]
fn channels_that_send_to_each_other_do_not_loop() {
    // 送る Atom の subject にチャネルを書いた(第3章の形に反する)候補でも、局所を求めるたどりはめぐらずに終わる。
    let repo = Repo::new("split-channel-loop");
    repo.write(".archsig/law/m.law", "sources \"**/*.py\"\n\nreading module = dir(depth: 1)\n");
    repo.write("a/f.py", "# source\n");
    repo.map("a/f.py", "{\"kind\": \"observed\", \"subject\": \"a/f.py\", \"scope\": \"structure\", \"at\": \"a/f.py@blob:aaaaaaa\"}\n");
    repo.write(
        ".archsig/plans/p/plan.jsonl",
        r#"{"kind": "sends", "subject": "channel:queue:a:b", "object": "channel:queue:c:d", "value": "1", "at": "plan:p"}
{"kind": "sends", "subject": "channel:queue:c:d", "object": "channel:queue:a:b", "value": "1", "at": "plan:p"}
"#,
    );
    let s = repo.run(&["plan", "split", "p"]);
    assert!(s["results"].as_array().is_some(), "{s}");
}

#[test]
fn an_element_whose_place_is_unknown_before_the_change_is_silent() {
    // 変更後で決まらない要素は、変更前の構造で解いた定義した所の局所に属する。変更前でも分からなければ、局所は決まらない(設計 §6)。
    let run = |name: &str, map: &str, plan: &str| {
        let repo = Repo::new(name);
        repo.write(".archsig/law/m.law", "sources \"**/*.py\"\n\nreading module = dir(depth: 1)\n");
        repo.write("a/x.py", "# source\n");
        repo.map("a/x.py", map);
        repo.write(".archsig/plans/p/plan.jsonl", plan);
        repo.run(&["plan", "split", "p"])
    };
    let observed = "{\"kind\": \"observed\", \"subject\": \"a/x.py\", \"scope\": \"structure\", \"at\": \"a/x.py@blob:aaaaaaa\"}\n";
    // 消した要素 m.g の定義は、読んでいない c/y.py にある。
    let s = run(
        "split-removed-unread",
        &format!("{observed}{}", r#"{"kind": "defines", "subject": "m.f", "value": "operation", "params": {}, "at": "a/x.py:1@blob:aaaaaaa"}
{"kind": "calls", "subject": "m.f", "object": "m.g", "at": "a/x.py:2@blob:aaaaaaa"}
{"kind": "resolves", "subject": "m.g", "object": "c/y.py", "at": "a/x.py:1@blob:aaaaaaa"}
"#),
        "{\"kind\": \"removes\", \"subject\": \"m.g\", \"at\": \"plan:p\"}\n",
    );
    let r = result(&s, "m.g");
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unread")), "{s}");
    assert!(s["next"].as_array().unwrap().iter().any(|n| n["read"] == "c/y.py"), "{s}");
    // `file` なしに定義し直した m.T の元の定義は、読んでいない c/t.py にある。
    let s = run(
        "split-redefined-unread",
        &format!("{observed}{}", r#"{"kind": "defines", "subject": "m.f", "value": "operation", "params": {"t": "m.T"}, "at": "a/x.py:1@blob:aaaaaaa"}
{"kind": "resolves", "subject": "m.T", "object": "c/t.py", "at": "a/x.py:1@blob:aaaaaaa"}
"#),
        "{\"kind\": \"defines\", \"subject\": \"m.T\", \"value\": \"type\", \"at\": \"plan:p\"}\n",
    );
    let r = result(&s, "m.T");
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unread")), "{s}");
}

#[test]
fn a_channel_belongs_to_the_locals_of_the_operations_after_the_change() {
    // 項目を送る m.op1 を消す。変更後の列にその項目の送り受けがないので、項目はどの局所にも属さない。
    let repo = Repo::new("split-channel-after");
    repo.write(".archsig/law/m.law", "sources \"**/*.py\"\n\nreading module = dir(depth: 1)\n");
    repo.write("a/x.py", "# source\n");
    repo.map("a/x.py", r#"{"kind": "observed", "subject": "a/x.py", "scope": "structure", "at": "a/x.py@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.op1", "value": "operation", "params": {}, "at": "a/x.py:1@blob:aaaaaaa"}
{"kind": "sends", "subject": "m.op1", "object": "channel:queue:svc:item", "value": "1", "at": "a/x.py:2@blob:aaaaaaa"}
"#);
    repo.write(".archsig/plans/p/plan.jsonl", r#"{"kind": "removes", "subject": "m.op1", "at": "plan:p"}
{"kind": "corresponds", "subject": "channel:queue:svc:item", "object": "channel:queue:svc:item2", "at": "plan:p"}
"#);
    let s = repo.run(&["plan", "split", "p"]);
    let r = result(&s, "p");
    assert_eq!(r["outcome"], "holds", "{s}");
    let detail = repo.run(&["show", r["id"].as_str().unwrap()]);
    let shared: Vec<Value> = detail["check"]["shared"].as_array().unwrap().clone();
    assert!(has(&shared, "corresponds", "channel:queue:svc:item", None), "{detail}");
}

#[test]
fn an_element_whose_place_is_unknown_in_either_structure_is_silent() {
    let run = |name: &str, map: &str, plan: &str| {
        let repo = Repo::new(name);
        repo.write(".archsig/law/m.law", "sources \"**/*.py\"\n\nreading module = dir(depth: 1)\n");
        repo.write("a/x.py", "# source\n");
        repo.map("a/x.py", &format!("{{\"kind\": \"observed\", \"subject\": \"a/x.py\", \"scope\": \"structure\", \"at\": \"a/x.py@blob:aaaaaaa\"}}\n{map}"));
        repo.write(".archsig/plans/p/plan.jsonl", plan);
        repo.run(&["plan", "split", "p"])
    };
    let silent = |s: &Value, subject: &str, read: &str| {
        let r = result(s, subject);
        assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unread")), "{s}");
        assert!(s["next"].as_array().unwrap().iter().any(|n| n["read"] == read), "{s}");
    };
    // 消した b.S は、別のフィールドの型として名指されたまま。変更前の定義は読んでいない c/z.py にある。
    let s = run(
        "split-removed-still-typed",
        r#"{"kind": "defines", "subject": "a.f", "value": "operation", "params": {}, "at": "a/x.py:1@blob:aaaaaaa"}
{"kind": "calls", "subject": "a.f", "object": "b.S", "at": "a/x.py:2@blob:aaaaaaa"}
{"kind": "resolves", "subject": "b.S", "object": "c/z.py", "at": "a/x.py:1@blob:aaaaaaa"}
{"kind": "defines", "subject": "a.O", "value": "type", "at": "a/x.py:3@blob:aaaaaaa"}
{"kind": "defines", "subject": "a.O.s", "value": "field", "type": "b.S", "at": "a/x.py:4@blob:aaaaaaa"}
"#,
        "{\"kind\": \"removes\", \"subject\": \"b.S\", \"at\": \"plan:p\"}\n",
    );
    silent(&s, "b.S", "c/z.py");
    // 頭 b.M(型として名指されていない)の定義を読んでいない。`<頭>.<名前>` は頭で見る(マニュアル第4章、第5章 問い7)。
    let head = r#"{"kind": "defines", "subject": "a.f", "value": "operation", "params": {}, "at": "a/x.py:1@blob:aaaaaaa"}
{"kind": "resolves", "subject": "b.M", "object": "b/m.py", "at": "a/x.py:1@blob:aaaaaaa"}
"#;
    let s = run("split-head-unread-write", head, "{\"kind\": \"writes\", \"subject\": \"a.f\", \"object\": \"b.M.x\", \"value\": \"1\", \"at\": \"plan:p\"}\n");
    silent(&s, "b.M.x", "b/m.py");
    let s = run("split-head-unread-calls", head, "{\"kind\": \"calls\", \"subject\": \"a.f\", \"object\": \"b.M.run\", \"at\": \"plan:p\"}\n");
    silent(&s, "b.M.run", "b/m.py");
}

#[test]
fn an_element_the_plan_defines_ambiguously_is_placed_by_the_plan() {
    // 候補を重ねた列で曖昧な m.T は、候補の定義した所で見る。定義した所が一つの局所なら、その局所。分かれれば決まらない(設計 §6)。
    let run = |name: &str, plan: &str| {
        let repo = Repo::new(name);
        repo.write(".archsig/law/m.law", "sources \"**/*.py\"\n\nreading module = dir(depth: 1)\n");
        repo.write("b/t.py", "# source\n");
        repo.map("b/t.py", r#"{"kind": "observed", "subject": "b/t.py", "scope": "structure", "at": "b/t.py@blob:aaaaaaa"}
{"kind": "defines", "subject": "m.T", "value": "type", "at": "b/t.py:1@blob:aaaaaaa"}
"#);
        repo.write(".archsig/plans/p/plan.jsonl", plan);
        (repo.run(&["plan", "split", "p"]), repo)
    };
    let (s, repo) = run("split-plan-valueless", "{\"kind\": \"defines\", \"subject\": \"m.T\", \"file\": \"c/z.py\", \"at\": \"plan:p\"}\n");
    assert_eq!(result(&s, "p")["outcome"], "holds", "{s}");
    assert!(has(&lines(&repo, ".archsig/plans/p/c/plan.jsonl"), "defines", "m.T", None), "{s}");
    let (s, _) = run(
        "split-plan-two-kinds",
        "{\"kind\": \"defines\", \"subject\": \"m.T\", \"value\": \"type\", \"file\": \"a/z.py\", \"at\": \"plan:p\"}\n{\"kind\": \"defines\", \"subject\": \"m.T\", \"value\": \"operation\", \"file\": \"c/z.py\", \"at\": \"plan:p\"}\n",
    );
    assert_eq!((result(&s, "m.T")["outcome"].as_str(), result(&s, "m.T")["reason"].as_str()), (Some("silent"), Some("unresolved")), "{s}");
}

#[test]
fn an_element_the_plan_defines_twice_in_two_files_is_silent() {
    // 候補が同じ種類の `defines` を二つの `file` に書けば、同じ種類の `defines` を二か所に持つ要素である(マニュアル第3章、設計 §3.2)。
    // 定義した所が二つの局所に分かれるので、局所が決まらない(設計 §6)。
    let repo = Repo::new("split-plan-two-files");
    repo.write(".archsig/law/m.law", "sources \"**/*.py\"\n\nreading module = dir(depth: 1)\n");
    repo.write("b/t.py", "# source\n");
    repo.map("b/t.py", "{\"kind\": \"observed\", \"subject\": \"b/t.py\", \"scope\": \"structure\", \"at\": \"b/t.py@blob:aaaaaaa\"}\n");
    repo.write(
        ".archsig/plans/p/plan.jsonl",
        "{\"kind\": \"defines\", \"subject\": \"m.T\", \"value\": \"type\", \"file\": \"a/z.py\", \"at\": \"plan:p\"}\n{\"kind\": \"defines\", \"subject\": \"m.T\", \"value\": \"type\", \"file\": \"c/y.py\", \"at\": \"plan:p\"}\n",
    );
    let s = repo.run(&["plan", "split", "p"]);
    let r = result(&s, "m.T");
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unresolved")), "{s}");
}

#[test]
fn a_column_is_placed_only_where_its_names_are_decided() {
    let run = |name: &str, maps: &[(&str, &str)], plan: &str| {
        let repo = Repo::new(name);
        repo.write(".archsig/law/m.law", "sources \"**/*.py\"\n\nreading module = dir(depth: 1)\n");
        for (src, map) in maps {
            repo.write(src, "# source\n");
            repo.map(src, &format!("{{\"kind\": \"observed\", \"subject\": \"{src}\", \"scope\": \"structure\", \"at\": \"{src}@blob:aaaaaaa\"}}\n{map}"));
        }
        repo.write(".archsig/plans/p/plan.jsonl", plan);
        (repo.run(&["plan", "split", "p"]), repo)
    };
    // 列 [a.O.s, b.S.p] は a.O.s の段で止まる(定義を読んでいない)。後ろの b.S.p は型が決まらないので、書き込みの局所は決まらない。
    let (s, _) = run(
        "split-column-stopped-early",
        &[
            ("a/f.py", r#"{"kind": "defines", "subject": "a.f", "value": "operation", "params": {}, "at": "a/f.py:1@blob:aaaaaaa"}
{"kind": "defines", "subject": "a.O", "value": "type", "at": "a/f.py:2@blob:aaaaaaa"}
"#),
            ("b/s.py", r#"{"kind": "defines", "subject": "b.S", "value": "type", "at": "b/s.py:1@blob:aaaaaaa"}
{"kind": "defines", "subject": "b.S.p", "value": "field", "type": "int", "at": "b/s.py:2@blob:aaaaaaa"}
"#),
        ],
        "{\"kind\": \"writes\", \"subject\": \"a.f\", \"via\": [\"a.O.s\"], \"object\": \"b.S.p\", \"value\": \"1\", \"at\": \"plan:p\"}\n",
    );
    let r = result(&s, "a.O.s");
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unread")), "{s}");
    // 列の最初の名前 o.O.s で止まれば(頭 o.O の定義を読んでおらず、候補が o.O.s を消す)、その名前を変更前の構造で解いた定義した所で見る。
    let (s, repo) = run(
        "split-column-removed-first",
        &[
            ("o/model.py", r#"{"kind": "defines", "subject": "o.O.s", "value": "field", "type": "int", "at": "o/model.py:1@blob:aaaaaaa"}
{"kind": "defines", "subject": "o.f", "value": "operation", "params": {"x": "o.O"}, "at": "o/model.py:2@blob:aaaaaaa"}
"#),
            ("p/svc.py", r#"{"kind": "defines", "subject": "p.g", "value": "operation", "params": {}, "at": "p/svc.py:1@blob:aaaaaaa"}
"#),
        ],
        "{\"kind\": \"removes\", \"subject\": \"o.O.s\", \"at\": \"plan:p\"}\n{\"kind\": \"writes\", \"subject\": \"p.g\", \"object\": \"o.O.s\", \"value\": \"1\", \"at\": \"plan:p\"}\n",
    );
    let r = result(&s, "p");
    assert_eq!(r["outcome"], "holds", "{s}");
    let detail = repo.run(&["show", r["id"].as_str().unwrap()]);
    assert!(has(detail["check"]["shared"].as_array().unwrap(), "writes", "p.g", Some("o.O.s")), "{detail}");
    // フィールドでない要素(操作 o.T.m)を書く列は決まらない。頭の局所に倒さない。
    let (s, _) = run(
        "split-column-not-a-field",
        &[
            ("o/model.py", "{\"kind\": \"defines\", \"subject\": \"o.T\", \"value\": \"type\", \"at\": \"o/model.py:1@blob:aaaaaaa\"}\n"),
            ("p/ext.py", "{\"kind\": \"defines\", \"subject\": \"o.T.m\", \"value\": \"operation\", \"params\": {}, \"at\": \"p/ext.py:1@blob:aaaaaaa\"}\n"),
            ("q/svc.py", "{\"kind\": \"defines\", \"subject\": \"q.g\", \"value\": \"operation\", \"params\": {}, \"at\": \"q/svc.py:1@blob:aaaaaaa\"}\n"),
        ],
        "{\"kind\": \"writes\", \"subject\": \"q.g\", \"object\": \"o.T.m\", \"value\": \"1\", \"at\": \"plan:p\"}\n",
    );
    let r = result(&s, "o.T.m");
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unresolved")), "{s}");
}

#[test]
fn an_element_the_plan_defines_under_a_redefined_unread_type_is_in_the_local_of_its_file() {
    // 変更前の o.S は引数の型として名指されるだけで、定義を読んでいない。候補が o.S を定義し直し、o.S.y を p/svc.py に定義する。
    // 候補の中で定義した要素は、その `file` の局所に属する(設計 §6)。
    let repo = Repo::new("split-planned-under-redefined");
    repo.write(".archsig/law/m.law", "sources \"**/*.py\"\n\nreading module = dir(depth: 1)\n");
    repo.write("o/model.py", "# source\n");
    repo.map("o/model.py", r#"{"kind": "observed", "subject": "o/model.py", "scope": "structure", "at": "o/model.py@blob:aaaaaaa"}
{"kind": "defines", "subject": "o.f", "value": "operation", "params": {"x": "o.S"}, "at": "o/model.py:1@blob:aaaaaaa"}
"#);
    repo.write(
        ".archsig/plans/p/plan.jsonl",
        "{\"kind\": \"defines\", \"subject\": \"o.S\", \"value\": \"type\", \"file\": \"o/model.py\", \"at\": \"plan:p\"}\n{\"kind\": \"defines\", \"subject\": \"o.S.y\", \"value\": \"field\", \"type\": \"int\", \"file\": \"p/svc.py\", \"at\": \"plan:p\"}\n",
    );
    let s = repo.run(&["plan", "split", "p"]);
    assert_eq!(result(&s, "p")["outcome"], "holds", "{s}");
    assert!(has(&lines(&repo, ".archsig/plans/p/p/plan.jsonl"), "defines", "o.S.y", None), "{s}");
}

/// 読み `dir(depth: 1)` で、ソースごとの構造の Atom(`observed` は足す)と候補を置き、`plan split` を実行する。
fn split_repo(name: &str, maps: &[(&str, &str)], plan: &str) -> (Value, Repo) {
    let repo = Repo::new(name);
    repo.write(".archsig/law/m.law", "sources \"**/*.py\"\n\nreading module = dir(depth: 1)\n");
    for (src, map) in maps {
        repo.write(src, "# source\n");
        repo.map(src, &format!("{{\"kind\": \"observed\", \"subject\": \"{src}\", \"scope\": \"structure\", \"at\": \"{src}@blob:aaaaaaa\"}}\n{map}"));
    }
    repo.write(".archsig/plans/p/plan.jsonl", plan);
    (repo.run(&["plan", "split", "p"]), repo)
}

/// 局所 `local` の候補が、`kind`・`subject` の Atom を持つ。
fn in_local(repo: &Repo, local: &str, kind: &str, subject: &str) -> bool {
    has(&lines(repo, &format!(".archsig/plans/p/{local}/plan.jsonl")), kind, subject, None)
}

#[test]
fn a_name_whose_own_resolves_points_to_a_question_mark_is_not_put_in_the_local_of_its_type() {
    // a.T.x の定義はなく、その `resolves` は解析器が解決できなかった行き先(`?`)を指す。局所は T で決めず、`?` の答えで決まらない(設計 §6)。
    let (s, _) = split_repo(
        "split-stage-question",
        &[
            ("a/m.py", "{\"kind\": \"defines\", \"subject\": \"a.T\", \"value\": \"type\", \"at\": \"a/m.py:1@blob:aaaaaaa\"}\n{\"kind\": \"resolves\", \"subject\": \"a.T.x\", \"object\": \"?a\", \"at\": \"a/m.py:2@blob:aaaaaaa\"}\n"),
            ("b/m.py", "{\"kind\": \"defines\", \"subject\": \"b.g\", \"value\": \"operation\", \"params\": {}, \"at\": \"b/m.py:1@blob:aaaaaaa\"}\n"),
        ],
        "{\"kind\": \"calls\", \"subject\": \"b.g\", \"object\": \"a.T.x\", \"at\": \"plan:p\"}\n",
    );
    let r = result(&s, "a.T.x");
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unresolved")), "{s}");
    // 読む所は、その `resolves` を書いた所。
    assert!(s["next"].as_array().unwrap().iter().any(|n| n["read"] == "a/m.py"), "{s}");
}

#[test]
fn an_undecided_name_after_the_plan_is_undecided_even_if_it_was_external_before() {
    // 変更前の m.X は外部の要素で、候補は別の `resolves` を足す。変更後は指す先の違う `resolves` で決まらないので、局所も決まらない(設計 §6)。
    let (s, _) = split_repo(
        "split-external-before",
        &[("b/m.py", "{\"kind\": \"defines\", \"subject\": \"b.g\", \"value\": \"operation\", \"params\": {}, \"at\": \"b/m.py:1@blob:aaaaaaa\"}\n{\"kind\": \"resolves\", \"subject\": \"m.X\", \"object\": \"external:lib\", \"at\": \"b/m.py:2@blob:aaaaaaa\"}\n")],
        "{\"kind\": \"resolves\", \"subject\": \"m.X\", \"object\": \"c/x.py\", \"at\": \"plan:p\"}\n{\"kind\": \"calls\", \"subject\": \"b.g\", \"object\": \"m.X\", \"at\": \"plan:p\"}\n",
    );
    let r = result(&s, "m.X");
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unresolved")), "{s}");
}

#[test]
fn a_new_member_the_plan_defines_without_a_file_is_in_the_local_of_its_type() {
    // 候補は b.N を a/m.py に、そのフィールド b.N.p を `file` なしに定義する。b.N.p に元の定義はないので、それを定義した型 b.N の局所に属する(設計 §6)。
    // b.N を二か所に定義しても(曖昧)、定義した所が一つの局所にあれば、その局所である。
    for (name, types) in [
        ("split-new-member", "{\"kind\": \"defines\", \"subject\": \"b.N\", \"value\": \"type\", \"file\": \"a/m.py\", \"at\": \"plan:p\"}\n"),
        (
            "split-new-member-ambiguous-type",
            "{\"kind\": \"defines\", \"subject\": \"b.N\", \"value\": \"type\", \"file\": \"a/m.py\", \"at\": \"plan:p\"}\n{\"kind\": \"defines\", \"subject\": \"b.N\", \"value\": \"type\", \"at\": \"plan:p\"}\n",
        ),
    ] {
        let (s, repo) = split_repo(
            name,
            &[
                ("a/m.py", "{\"kind\": \"defines\", \"subject\": \"a.f\", \"value\": \"operation\", \"params\": {}, \"at\": \"a/m.py:1@blob:aaaaaaa\"}\n"),
                ("c/m.py", "{\"kind\": \"defines\", \"subject\": \"c.k\", \"value\": \"operation\", \"params\": {}, \"at\": \"c/m.py:1@blob:aaaaaaa\"}\n"),
            ],
            &format!("{types}{{\"kind\": \"defines\", \"subject\": \"b.N.p\", \"value\": \"field\", \"type\": \"int\", \"at\": \"plan:p\"}}\n"),
        );
        let r = result(&s, "p");
        assert_eq!(r["outcome"], "holds", "{name}: {s}");
        let detail = repo.run(&["show", r["id"].as_str().unwrap()]);
        assert!(!has(detail["check"]["shared"].as_array().unwrap(), "defines", "b.N.p", None), "{name}: {detail}");
        assert!(in_local(&repo, "a", "defines", "b.N.p"), "{name}: {s}");
    }
}

#[test]
fn a_name_that_stops_in_the_middle_of_its_stages_has_no_local() {
    // a.T.x.p の途中の段 a.T.x の定義を読んでいない。その先の型が決まらないので、a.T.x.p の局所も決まらない(a.T の局所にしない)。
    let (s, _) = split_repo(
        "split-middle-stage",
        &[
            ("a/m.py", "{\"kind\": \"defines\", \"subject\": \"a.T\", \"value\": \"type\", \"at\": \"a/m.py:1@blob:aaaaaaa\"}\n"),
            ("b/m.py", "{\"kind\": \"defines\", \"subject\": \"b.g\", \"value\": \"operation\", \"params\": {}, \"at\": \"b/m.py:1@blob:aaaaaaa\"}\n"),
        ],
        "{\"kind\": \"calls\", \"subject\": \"b.g\", \"object\": \"a.T.x.p\", \"at\": \"plan:p\"}\n",
    );
    let r = result(&s, "a.T.x.p");
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unread")), "{s}");
    assert!(s["next"].as_array().unwrap().iter().any(|n| n["element"] == "a.T.x"), "{s}");
}

#[test]
fn a_removed_element_is_found_in_the_structure_before_the_plan() {
    // 候補が b.S.y を消すと、変更後の b.S.y は頭 b.S(外部)から外部の要素に解ける。消える要素は変更前の構造で見つけるので、
    // 変更前の b.S.y の `resolves` が指す読んでいない b/m.py で沈黙する(設計 §6)。
    let (s, _) = split_repo(
        "split-removed-external-head",
        &[("a/m.py", "{\"kind\": \"resolves\", \"subject\": \"b.S\", \"object\": \"external:lib\", \"at\": \"a/m.py:1@blob:aaaaaaa\"}\n{\"kind\": \"resolves\", \"subject\": \"b.S.y\", \"object\": \"b/m.py\", \"at\": \"a/m.py:2@blob:aaaaaaa\"}\n")],
        "{\"kind\": \"removes\", \"subject\": \"b.S.y\", \"at\": \"plan:p\"}\n",
    );
    let r = result(&s, "b.S.y");
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unread")), "{s}");
    assert!(s["next"].as_array().unwrap().iter().any(|n| n["read"] == "b/m.py"), "{s}");
}

#[test]
fn a_column_that_stops_at_an_unread_type_has_no_local() {
    // 列 [c.U.x, b.N.x] は、c.U.x の型 b.N の定義を読んでいないので二段目で止まる。b.N.x の局所は決まらない(どの局所にも属さないとしない)。
    let (s, _) = split_repo(
        "split-column-unread-type",
        &[
            ("c/m.py", "{\"kind\": \"defines\", \"subject\": \"c.U\", \"value\": \"type\", \"at\": \"c/m.py:1@blob:aaaaaaa\"}\n{\"kind\": \"defines\", \"subject\": \"c.U.x\", \"value\": \"field\", \"type\": \"b.N\", \"at\": \"c/m.py:2@blob:aaaaaaa\"}\n"),
            ("b/m.py", "{\"kind\": \"defines\", \"subject\": \"b.h\", \"value\": \"operation\", \"params\": {}, \"at\": \"b/m.py:1@blob:aaaaaaa\"}\n"),
        ],
        "{\"kind\": \"reads\", \"subject\": \"b.h\", \"via\": [\"c.U.x\"], \"object\": \"b.N.x\", \"at\": \"plan:p\"}\n",
    );
    let r = result(&s, "b.N.x");
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unread")), "{s}");
    assert!(s["next"].as_array().unwrap().iter().any(|n| n["element"] == "b.N"), "{s}");
}

#[test]
fn a_name_under_a_redefined_unread_type_with_its_own_resolves_is_placed_by_the_resolves() {
    // 変更前の c.U は引数の型として名指されるだけで、候補が a/m.py に定義し直す。c.U.z そのものの `resolves` は読んでいない c/m.py を指す。
    // 段は c.U の定義し直しで決まらないが、局所は c.U.z の `resolves` の答えで決める(設計 §6)。
    let (s, _) = split_repo(
        "split-redefined-own-resolves",
        &[("b/m.py", "{\"kind\": \"defines\", \"subject\": \"b.h\", \"value\": \"operation\", \"params\": {\"o\": \"c.U\"}, \"at\": \"b/m.py:1@blob:aaaaaaa\"}\n")],
        "{\"kind\": \"defines\", \"subject\": \"c.U\", \"value\": \"type\", \"file\": \"a/m.py\", \"at\": \"plan:p\"}\n{\"kind\": \"resolves\", \"subject\": \"c.U.z\", \"object\": \"c/m.py\", \"at\": \"plan:p\"}\n",
    );
    let r = result(&s, "c.U.z");
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unread")), "{s}");
    assert!(s["next"].as_array().unwrap().iter().any(|n| n["read"] == "c/m.py"), "{s}");
}

#[test]
fn an_element_the_plan_defines_without_a_file_is_placed_by_its_own_resolves() {
    // 変更前の b.N は型として名指されるだけ。候補は b.N を `file` なしに定義し、その `resolves` は読んでいない c/m.py を指す。
    // 元の定義した所が決まらないので、名前そのものの `resolves` の答えで決める(設計 §6)。
    let (s, _) = split_repo(
        "split-planned-own-resolves",
        &[("b/m.py", "{\"kind\": \"defines\", \"subject\": \"b.h\", \"value\": \"operation\", \"params\": {\"o\": \"b.N\"}, \"at\": \"b/m.py:1@blob:aaaaaaa\"}\n")],
        "{\"kind\": \"resolves\", \"subject\": \"b.N\", \"object\": \"c/m.py\", \"at\": \"plan:p\"}\n{\"kind\": \"defines\", \"subject\": \"b.N\", \"value\": \"type\", \"at\": \"plan:p\"}\n",
    );
    let r = result(&s, "b.N");
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unread")), "{s}");
    assert!(s["next"].as_array().unwrap().iter().any(|n| n["read"] == "c/m.py"), "{s}");
}

#[test]
fn a_name_has_the_same_place_to_read_wherever_it_is_written_in_a_column() {
    // b.M.s の頭 b.M の `resolves` は読んでいない b/m.py を指す。b.M.s を `object` に書いても、後ろに名前の続く `via` に書いても、
    // 局所は b.M.s の答えから決め、同じ読む所(b/m.py)を返す(設計 §6)。
    let a = "{\"kind\": \"defines\", \"subject\": \"a.f\", \"value\": \"operation\", \"params\": {}, \"at\": \"a/m.py:1@blob:aaaaaaa\"}\n{\"kind\": \"resolves\", \"subject\": \"b.M\", \"object\": \"b/m.py\", \"at\": \"a/m.py:2@blob:aaaaaaa\"}\n";
    for (name, plan) in [
        ("split-same-read-object", "{\"kind\": \"writes\", \"subject\": \"a.f\", \"object\": \"b.M.s\", \"value\": \"1\", \"at\": \"plan:p\"}\n"),
        ("split-same-read-via", "{\"kind\": \"writes\", \"subject\": \"a.f\", \"via\": [\"b.M.s\"], \"object\": \"x.Y.t\", \"value\": \"1\", \"at\": \"plan:p\"}\n"),
    ] {
        let (s, _) = split_repo(name, &[("a/m.py", a)], plan);
        let r = result(&s, "b.M.s");
        assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unread")), "{name}: {s}");
        assert!(s["next"].as_array().unwrap().iter().any(|n| n["read"] == "b/m.py"), "{name}: {s}");
    }
}
