//! AC1: `archsig record` と `archsig status`(マニュアル第3章、設計 §3.1)。

use std::path::PathBuf;
use std::process::{Command, Output};

use serde_json::Value;

struct Repo {
    dir: PathBuf,
}

impl Repo {
    fn new(name: &str) -> Repo {
        let dir = std::env::temp_dir().join(format!("archsig-archmap-{name}-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        let repo = Repo { dir };
        repo.write(
            ".archsig/law/a.law",
            "sources \"src/**\"\n  except \"**/tests/**\"\n\nreading module = dir(depth: 1)\n\nmeaning m on field\n  \"手がかり\"\n",
        );
        repo.write("src/a.py", "a = 1\n");
        repo.write("src/b.py", "b = 2\n");
        repo.write("src/tests/t.py", "t = 3\n");
        repo
    }

    fn write(&self, path: &str, text: &str) {
        let p = self.dir.join(path);
        std::fs::create_dir_all(p.parent().unwrap()).unwrap();
        std::fs::write(p, text).unwrap();
    }

    fn run(&self, args: &[&str]) -> Output {
        Command::new(env!("CARGO_BIN_EXE_archsig")).current_dir(&self.dir).args(args).output().unwrap()
    }

    fn ok(&self, args: &[&str]) -> Value {
        let out = self.run(args);
        assert!(out.status.success(), "archsig {args:?}: {}", String::from_utf8_lossy(&out.stderr));
        serde_json::from_slice(&out.stdout).unwrap()
    }

    fn record(&self, atoms: &str) -> Value {
        let f = self.dir.join("in.jsonl");
        std::fs::write(&f, atoms).unwrap();
        self.ok(&["record", f.to_str().unwrap()])
    }

    fn map(&self, source: &str) -> Vec<Value> {
        let text = std::fs::read_to_string(self.dir.join(format!(".archsig/map/{source}.jsonl"))).unwrap();
        text.lines().map(|l| serde_json::from_str(l).unwrap()).collect()
    }
}

impl Drop for Repo {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.dir);
    }
}

/// `git hash-object` と同じ値。
fn blob(text: &str) -> String {
    let out = Command::new("git").args(["hash-object", "--stdin"]).stdin(std::process::Stdio::piped()).stdout(std::process::Stdio::piped()).spawn().and_then(|mut c| {
        use std::io::Write;
        c.stdin.take().unwrap().write_all(text.as_bytes())?;
        c.wait_with_output()
    });
    format!("blob:{}", String::from_utf8(out.unwrap().stdout).unwrap().trim())
}

fn kinds_scopes(atoms: &[Value]) -> Vec<(String, String)> {
    atoms
        .iter()
        .map(|a| (a["kind"].as_str().unwrap().to_string(), a["scope"].as_str().unwrap_or("").to_string()))
        .collect()
}

#[test]
fn record_fills_the_version_and_observed() {
    let repo = Repo::new("fill");
    let v = repo.record(r#"{"kind": "defines", "subject": "src.a.A", "value": "type", "at": "src/a.py:1", "by": "tool:t"}"#);
    assert_eq!(v["recorded"][0]["source"], "src/a.py");
    assert_eq!(v["recorded"][0]["scope"], "structure");
    let atoms = repo.map("src/a.py");
    let version = blob("a = 1\n");
    assert_eq!(atoms[0]["kind"], "observed");
    assert_eq!(atoms[0]["scope"], "structure");
    assert_eq!(atoms[0]["at"], format!("src/a.py@{version}"));
    assert_eq!(atoms[1]["at"], format!("src/a.py:1@{version}"));
}

#[test]
fn record_replaces_only_the_same_source_and_scope() {
    let repo = Repo::new("replace");
    repo.record(concat!(
        r#"{"kind": "defines", "subject": "src.a.A", "value": "type", "at": "src/a.py:1"}"#, "\n",
        r#"{"kind": "defines", "subject": "src.a.A.x", "value": "field", "type": "int", "at": "src/a.py:1"}"#, "\n",
        r#"{"kind": "meaning", "subject": "src.a.A.x", "meaning": "m", "uses": ["src/b.py:1"], "at": "src/a.py:1"}"#, "\n",
    ));
    repo.record(r#"{"kind": "defines", "subject": "src.a.B", "value": "type", "at": "src/a.py:1"}"#);
    let atoms = repo.map("src/a.py");
    let subjects: Vec<&str> = atoms.iter().filter(|a| a["kind"] == "defines").map(|a| a["subject"].as_str().unwrap()).collect();
    assert_eq!(subjects, vec!["src.a.B"]);
    let meaning = atoms.iter().find(|a| a["kind"] == "meaning").expect("意味の範囲は残る");
    assert_eq!(meaning["uses"][0], format!("src/b.py:1@{}", blob("b = 2\n")));
}

#[test]
fn observed_alone_records_a_read_scope_without_atoms() {
    let repo = Repo::new("observed");
    repo.record(r#"{"kind": "meaning", "subject": "src.b.x", "meaning": "m", "at": "src/b.py:1"}"#);
    let v = repo.record(r#"{"kind": "observed", "subject": "src/b.py", "scope": "meaning:m", "at": "src/b.py"}"#);
    assert_eq!(v["recorded"][0]["atoms"], 0);
    assert_eq!(kinds_scopes(&repo.map("src/b.py")), vec![("observed".to_string(), "meaning:m".to_string())]);
}

#[test]
fn record_accepts_every_atom_kind_of_chapter_3() {
    let repo = Repo::new("kinds");
    let v = repo.record(concat!(
        r#"{"kind": "defines", "subject": "src.a.f", "value": "operation", "params": {"x": "int"}, "at": "src/a.py:1"}"#, "\n",
        r#"{"kind": "calls", "subject": "src.a.f", "object": "src.b.g", "when": "$x > 0", "at": "src/a.py:1"}"#, "\n",
        r#"{"kind": "reads", "subject": "src.a.f", "object": "src.a.A.x", "at": "src/a.py:1"}"#, "\n",
        r#"{"kind": "writes", "subject": "src.a.f", "object": "src.a.A.x", "value": "$x", "at": "src/a.py:1"}"#, "\n",
        r#"{"kind": "passes", "subject": "src.a.f->src.b.g", "object": "src.b.g.$y", "value": "$x", "at": "src/a.py:1"}"#, "\n",
        r#"{"kind": "sends", "subject": "src.a.f", "object": "channel:queue:q:x", "value": "$x", "at": "src/a.py:1"}"#, "\n",
        r#"{"kind": "receives", "subject": "src.a.f", "object": "channel:queue:r:y", "value": "$msg.y", "at": "src/a.py:1"}"#, "\n",
        r#"{"kind": "returns", "subject": "src.a.f", "value": "$x", "at": "src/a.py:1"}"#, "\n",
        r#"{"kind": "imports", "subject": "src.a", "object": "src.b", "at": "src/a.py:1"}"#, "\n",
        r#"{"kind": "resolves", "subject": "src.b.g", "object": "src/b.py", "at": "src/a.py:1"}"#, "\n",
        r#"{"kind": "resolves", "subject": "requests.post", "object": "external:requests", "at": "src/a.py:1"}"#, "\n",
        r#"{"kind": "meaning", "subject": "src.a.A.x", "meaning": "m", "value": "v", "uses": ["src/a.py:1"], "at": "src/a.py:1"}"#, "\n",
    ));
    let recorded: Vec<(String, u64)> = v["recorded"]
        .as_array()
        .unwrap()
        .iter()
        .map(|r| (r["scope"].as_str().unwrap().to_string(), r["atoms"].as_u64().unwrap()))
        .collect();
    assert_eq!(recorded, vec![("meaning:m".to_string(), 1), ("structure".to_string(), 11)]);
}

#[test]
fn a_path_with_at_sign_is_not_a_version() {
    let repo = Repo::new("atsign");
    repo.write("src/@app/x.ts", "x\n");
    repo.record(r#"{"kind": "defines", "subject": "app.x", "value": "type", "at": "src/@app/x.ts:1"}"#);
    let atoms = repo.map("src/@app/x.ts");
    assert_eq!(atoms[1]["at"], format!("src/@app/x.ts:1@{}", blob("x\n")));
    let v = repo.ok(&["status"]);
    assert!(!v["unread"].as_array().unwrap().iter().any(|u| u["source"] == "src/@app/x.ts" && u["scopes"][0] == "structure"));
}

#[test]
fn record_keeps_paths_inside_the_repository() {
    let repo = Repo::new("paths");
    repo.record(concat!(
        r#"{"kind": "defines", "subject": "src.a.A", "value": "type", "uses": [], "at": "./src//a.py:1"}"#, "\n",
        r#"{"kind": "observed", "subject": "./src/b.py", "scope": "structure", "at": "./src/b.py"}"#, "\n",
        r#"{"kind": "meaning", "subject": "src.a.A.x", "meaning": "m", "uses": ["./src/b.py:1"], "at": "src/a.py:1"}"#, "\n",
    ));
    assert_eq!(repo.map("src/a.py")[1]["at"], format!("src/a.py:1@{}", blob("a = 1\n")));
    assert_eq!(repo.map("src/b.py")[0]["subject"], "src/b.py");
    let meaning = repo.map("src/a.py").into_iter().find(|a| a["kind"] == "meaning").unwrap();
    assert_eq!(meaning["uses"][0], format!("src/b.py:1@{}", blob("b = 2\n")));
    let v = repo.ok(&["status"]);
    assert!(!v["unread"].as_array().unwrap().iter().any(|u| u["source"] == "src/b.py" && u["scopes"][0] == "structure"), "{v}");

    repo.record(r#"{"kind": "defines", "subject": "src.b.B", "value": "type", "at": "src/../src/b.py:1"}"#);
    assert_eq!(repo.map("src/b.py").iter().filter(|a| a["kind"] == "defines").count(), 1, "根の中を指す .. はたどる");
    assert!(repo.dir.join(".archsig/map/src/a.py.jsonl").exists(), "別のソースの Atom は残る");
    for subject in ["local:x:../../../escaped", "local:x", "local:..:src/a.py"] {
        let f = repo.dir.join("in.jsonl");
        std::fs::write(&f, format!(r#"{{"kind": "meaning", "subject": "{subject}", "meaning": "m", "at": "src"}}"#)).unwrap();
        assert!(!repo.run(&["record", f.to_str().unwrap()]).status.success(), "{subject}");
    }

    let outside = repo.dir.parent().unwrap().join(format!("archsig-outside-{}.py", std::process::id()));
    std::fs::write(&outside, "x\n").unwrap();
    for at in [outside.display().to_string(), format!("../{}", outside.file_name().unwrap().to_string_lossy())] {
        let f = repo.dir.join("in.jsonl");
        std::fs::write(&f, format!(r#"{{"kind": "defines", "subject": "x", "value": "type", "at": "{at}:1"}}"#)).unwrap();
        assert!(!repo.run(&["record", f.to_str().unwrap()]).status.success(), "{at}");
        std::fs::write(&f, format!(r#"{{"kind": "meaning", "subject": "x", "meaning": "m", "uses": ["{at}:1"], "at": "src/a.py:1"}}"#)).unwrap();
        assert!(!repo.run(&["record", f.to_str().unwrap()]).status.success(), "uses {at}");
    }
    assert!(!repo.run(&["record", "--drop", "../victim"]).status.success());
    let v = repo.ok(&["record", "--drop", "local:..:map/src/a.py"]);
    assert_eq!(v["dropped"].as_array().unwrap().len(), 0);
    assert!(repo.dir.join(".archsig/map/src/a.py.jsonl").exists(), "--drop の引数はソースのパスとして読む");
    std::fs::remove_file(outside).unwrap();
}

#[test]
fn except_applies_only_to_its_own_sources() {
    let repo = Repo::new("except");
    repo.write(".archsig/law/a.law", "sources \"src/**\"\n  except \"**/tests/**\"\n\nsources \"tools/tests/**\"\n");
    repo.write("tools/tests/check.py", "c = 1\n");
    let v = repo.ok(&["status"]);
    let unread: Vec<&str> = v["unread"].as_array().unwrap().iter().map(|u| u["source"].as_str().unwrap()).collect();
    assert_eq!(unread, vec!["src/a.py", "src/b.py", "tools/tests/check.py"]);
}

#[test]
fn path_patterns_do_not_cross_directories_with_one_star() {
    let repo = Repo::new("glob");
    repo.write(".archsig/law/a.law", "sources \"src/*.py\"\n");
    repo.write("src/sub/c.py", "c = 1\n");
    let v = repo.ok(&["status"]);
    let unread: Vec<&str> = v["unread"].as_array().unwrap().iter().map(|u| u["source"].as_str().unwrap()).collect();
    assert_eq!(unread, vec!["src/a.py", "src/b.py"]);
}

/// マニュアル第3章の局所ごとの意味 Atom と、読んだ範囲の例。
#[test]
fn manual_chapter_3_local_meaning_and_observed() {
    let repo = Repo::new("local");
    repo.write(
        ".archsig/law/a.law",
        "sources \"shop/**\"\n\nreading module = dir(depth: 2)\nreading service = groups\n  money: \"shop/payment/**\"\n  rest: \"**\"\n\nmeaning unit on field\n  values minor | major\n  \"金額の単位\"\n",
    );
    repo.write("shop/payment/charge.py", "def charge(): pass\n");
    repo.write("shop/shipping/address.py", "def normalize_address(a): return a\n");
    repo.record(concat!(
        r#"{"kind": "meaning", "subject": "local:service:money", "meaning": "unit", "value": "minor", "uses": ["shop/payment/charge.py:1"], "at": "shop/payment", "by": "model:claude-sonnet-5"}"#, "\n",
        r#"{"kind": "observed", "subject": "shop/shipping/address.py", "scope": "structure", "at": "shop/shipping/address.py", "by": "tool:tree-sitter-python@0.23"}"#, "\n",
    ));
    repo.record(r#"{"kind": "meaning", "subject": "local:module:shop/payment", "meaning": "unit", "value": "minor", "uses": ["shop/payment/charge.py:1"], "by": "model:claude-sonnet-5"}"#);
    let local = |p: &str| -> Vec<serde_json::Value> {
        let text = std::fs::read_to_string(repo.dir.join(format!(".archsig/local/{p}.jsonl"))).unwrap();
        text.lines().map(|l| serde_json::from_str(l).unwrap()).collect()
    };
    let money = local("service/money");
    assert_eq!(money.len(), 1, "局所ごとの意味 Atom は局所の名前で置き、observed を補わない");
    assert_eq!(money[0]["at"], "shop/payment", "at に版を補わない");
    assert_eq!(local("module/shop/payment")[0]["subject"], "local:module:shop/payment", "読みの違う局所は置き換え合わない");
    repo.write("local/service/money", "x\n");
    repo.record(r#"{"kind": "observed", "subject": "local/service/money", "scope": "meaning:unit", "at": "local/service/money"}"#);
    assert_eq!(local("service/money")[0]["subject"], "local:service:money", "同じ名前のソースを記録しても、局所の Atom は消えない");
    repo.write("local:service:money", "y\n");
    repo.record(r#"{"kind": "observed", "subject": "local:service:money", "scope": "meaning:unit", "at": "local:service:money"}"#);
    assert_eq!(local("service/money")[0]["subject"], "local:service:money", "local: で始まる名前のソースも、局所とぶつからない");
    assert_eq!(repo.map("local:service:money")[0]["kind"], "observed");
    let v = repo.ok(&["record", "--drop", "local:service:money"]);
    assert_eq!(v["dropped"][0], "local:service:money");
    assert_eq!(local("service/money").len(), 1, "--drop はソースだけを外す");
    let v = repo.ok(&["status"]);
    assert_eq!(v["stale"].as_array().unwrap().len(), 0, "{v}");
    let charge = v["unread"].as_array().unwrap().iter().find(|u| u["source"] == "shop/payment/charge.py").unwrap();
    assert!(charge["scopes"].as_array().unwrap().contains(&serde_json::json!("meaning:unit")), "局所ごとの意味 Atom は、ソースごとの読んだ範囲に数えない");

    repo.write("shop/payment/charge.py", "def charge(): return 1\n");
    let v = repo.ok(&["status"]);
    let stale = v["stale"].as_array().unwrap();
    assert_eq!(stale.len(), 2, "{v}");
    assert_eq!(stale[0]["source"], "local:module:shop/payment");
    assert_eq!(stale[1]["source"], "local:service:money");
    assert_eq!(stale[1]["element"], "local:service:money");
}

#[test]
fn record_rejects_an_unknown_kind() {
    let repo = Repo::new("unknown");
    let f = repo.dir.join("in.jsonl");
    std::fs::write(&f, r#"{"kind": "verdict", "subject": "src.a", "at": "src/a.py:1"}"#).unwrap();
    let out = repo.run(&["record", f.to_str().unwrap()]);
    assert!(!out.status.success());
}

#[test]
fn drop_removes_a_deleted_source() {
    let repo = Repo::new("drop");
    repo.record(r#"{"kind": "defines", "subject": "src.b.B", "value": "type", "at": "src/b.py:1"}"#);
    std::fs::remove_file(repo.dir.join("src/b.py")).unwrap();
    let v = repo.ok(&["status"]);
    assert_eq!(v["stale"][0]["source"], "src/b.py");
    assert!(v["stale"][0]["current"].is_null());
    let v = repo.ok(&["record", "--drop", "./src//b.py"]);
    assert_eq!(v["dropped"][0], "src/b.py", "外したソースは、そろえたパスで返す");
    assert!(!repo.dir.join(".archsig/map/src/b.py.jsonl").exists());
    assert_eq!(repo.ok(&["status"])["stale"].as_array().unwrap().len(), 0);
}

#[test]
fn status_reports_unread_and_stale_scopes() {
    let repo = Repo::new("status");
    let v = repo.ok(&["status"]);
    let unread: Vec<(&str, Vec<&str>)> = v["unread"]
        .as_array()
        .unwrap()
        .iter()
        .map(|u| (u["source"].as_str().unwrap(), u["scopes"].as_array().unwrap().iter().map(|s| s.as_str().unwrap()).collect()))
        .collect();
    assert_eq!(
        unread,
        vec![("src/a.py", vec!["structure", "meaning:m"]), ("src/b.py", vec!["structure", "meaning:m"])],
        "テストコードは sources の except で外れる"
    );

    repo.record(concat!(
        r#"{"kind": "defines", "subject": "src.a.A.x", "value": "field", "type": "int", "at": "src/a.py:1"}"#, "\n",
        r#"{"kind": "meaning", "subject": "src.a.A.x", "meaning": "m", "uses": ["src/b.py:1"], "at": "src/a.py:1"}"#, "\n",
    ));
    let v = repo.ok(&["status"]);
    assert_eq!(v["stale"].as_array().unwrap().len(), 0);
    assert_eq!(v["unread"][0]["source"], "src/b.py");

    repo.write("src/b.py", "b = 3\n");
    let v = repo.ok(&["status"]);
    let stale = v["stale"].as_array().unwrap();
    assert_eq!(stale.len(), 1, "a.py は変わっていないが、uses の b.py が変わった");
    assert_eq!(stale[0]["source"], "src/a.py", "観測し直すのは、意味 Atom の範囲");
    assert_eq!(stale[0]["scope"], "meaning:m");
    assert_eq!(stale[0]["observed"], blob("b = 2\n"));
    assert_eq!(stale[0]["current"], blob("b = 3\n"));
    assert_eq!(stale[0]["element"], "src.a.A.x");
    assert_eq!(stale[0]["use"], format!("src/b.py:1@{}", blob("b = 2\n")));

    std::fs::remove_file(repo.dir.join("src/b.py")).unwrap();
    let v = repo.ok(&["status"]);
    assert!(v["stale"][0]["current"].is_null(), "使用箇所のソースが消えれば、今の版は null");
    repo.write("src/b.py", "b = 3\n");

    repo.write("src/a.py", "a = 2\n");
    let v = repo.ok(&["status"]);
    let scopes: Vec<&str> = v["stale"].as_array().unwrap().iter().map(|s| s["scope"].as_str().unwrap()).collect();
    assert_eq!(scopes, vec!["meaning:m", "meaning:m", "structure"], "ソース、範囲、要素の順に並ぶ");
}
