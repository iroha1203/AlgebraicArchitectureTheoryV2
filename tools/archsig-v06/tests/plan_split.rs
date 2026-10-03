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
fn a_write_to_an_inherited_field_belongs_to_the_local_of_the_type_that_defines_it() {
    // a.C は b.P を受け継ぎ、t は b.P が定義する。a.f は a.C の値の t に書く(`object` は値の型の名前 a.C.t)。
    // 書き込みは、受け継ぎで解いた b.P.t も名指すので、a と b の局所をまたぎ、共有に入る。
    let law = r#"sources "**/*.py"

reading module = dir(depth: 1)
"#;
    let run = |name: &str, b_map: Option<&str>| {
        let repo = Repo::new(name);
        repo.write(".archsig/law/m.law", law);
        repo.write("a/f.py", "# source\n");
        repo.write("b/m.py", "# source\n");
        repo.map(
            "a/f.py",
            r#"{"kind": "observed", "subject": "a/f.py", "scope": "structure", "at": "a/f.py@blob:aaaaaaa"}
{"kind": "defines", "subject": "a.f", "value": "operation", "params": {"c": "a.C"}, "at": "a/f.py:1@blob:aaaaaaa"}
{"kind": "defines", "subject": "a.C", "value": "type", "at": "a/f.py:2@blob:aaaaaaa"}
{"kind": "inherits", "subject": "a.C", "object": "b.P", "at": "a/f.py:2@blob:aaaaaaa"}
{"kind": "resolves", "subject": "b.P", "object": "b/m.py", "at": "a/f.py:3@blob:aaaaaaa"}
"#,
        );
        if let Some(m) = b_map {
            repo.map("b/m.py", m);
        }
        repo.write(".archsig/plans/p/plan.jsonl", "{\"kind\": \"writes\", \"subject\": \"a.f\", \"object\": \"a.C.t\", \"value\": \"1\", \"at\": \"plan:p\"}\n");
        let s = repo.run(&["plan", "split", "p"]);
        (repo, s)
    };
    let b = r#"{"kind": "observed", "subject": "b/m.py", "scope": "structure", "at": "b/m.py@blob:bbbbbbb"}
{"kind": "defines", "subject": "b.P", "value": "type", "at": "b/m.py:1@blob:bbbbbbb"}
{"kind": "defines", "subject": "b.P.t", "value": "field", "type": "int", "at": "b/m.py:2@blob:bbbbbbb"}
"#;
    let (repo, s) = run("inherited-field-shared", Some(b));
    let r = result(&s, "p");
    assert_eq!(r["outcome"], "holds", "{s}");
    let detail = repo.run(&["show", r["id"].as_str().unwrap()]);
    let shared: Vec<Value> = detail["check"]["shared"].as_array().unwrap().clone();
    assert!(has(&shared, "writes", "a.f", Some("a.C.t")), "{detail}");
    // b.P の定義を読んでいなければ、a.C.t がどの型のフィールドかが決まらないので、b/m.py を読むまで局所が決まらない。
    let (_, s) = run("inherited-field-unread", None);
    let r = result(&s, "a.C.t");
    assert_eq!((r["outcome"].as_str(), r["reason"].as_str()), (Some("silent"), Some("unread")), "{s}");
    assert!(s["next"].as_array().unwrap().iter().any(|n| n["read"] == "b/m.py"), "{s}");
}
