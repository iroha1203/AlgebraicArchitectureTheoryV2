//! AC2: `archsig law check`(マニュアル第4章、設計 §4)。

use std::path::{Path, PathBuf};
use std::process::Command;

use serde_json::Value;

struct Repo {
    dir: PathBuf,
}

impl Repo {
    fn new(name: &str) -> Repo {
        let dir = std::env::temp_dir().join(format!("archsig-law-{name}-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(dir.join(".archsig/law")).unwrap();
        Repo { dir }
    }

    fn law(&self, name: &str, text: &str) {
        std::fs::write(self.dir.join(".archsig/law").join(name), text).unwrap();
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

fn errors(v: &Value) -> Vec<(String, String)> {
    v["errors"]
        .as_array()
        .unwrap()
        .iter()
        .map(|e| (e["at"].as_str().unwrap().to_string(), e["message"].as_str().unwrap().to_string()))
        .collect()
}

#[test]
fn law_check_reads_the_manual_chapter_4_example() {
    let repo = Repo::new("manual");
    let text = std::fs::read_to_string(Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/law/shop.law")).unwrap();
    repo.law("shop.law", &text);
    let v = repo.run(&["law", "check"]);
    assert!(errors(&v).is_empty(), "{:?}", errors(&v));
    let forms: Vec<(&str, &str)> = v["laws"]
        .as_array()
        .unwrap()
        .iter()
        .map(|l| (l["name"].as_str().unwrap(), l["rule"]["form"].as_str().unwrap()))
        .collect();
    assert_eq!(
        forms,
        vec![
            ("payment-follows-order", "changes commute"),
            ("identity-mail-from-auth", "no"),
            ("payment-writes-are-audited", "each"),
            ("amount-units-agree", "agrees along"),
            ("transaction-id-kept", "agrees along"),
            ("payment-info-kept", "changes keep"),
            ("order-view-sync", "roundtrips"),
        ]
    );
    assert_eq!(v["laws"][0]["on"], "module", "on を省くと最初の読み");
    assert_eq!(v["laws"][5]["on"], "service");
    let each = &v["laws"][2]["rule"];
    assert_eq!(each["select"]["kind"], "operation", "def は展開される");
    assert_eq!(each["select"]["that"][0]["rel"], "writes");
    assert_eq!(each["require"][0]["rel"], "calls");
    let no = &v["laws"][1]["rule"]["select"];
    assert_eq!(no["to"], "mail.send");
    assert_eq!(no["that"][0]["cond"], "has");
    assert_eq!(no["that"][1]["cond"], "outside");
    assert_eq!(v["laws"][3]["rule"]["convert"][0]["factor"], "100");
    let readings: Vec<&str> = v["readings"].as_array().unwrap().iter().map(|r| r["name"].as_str().unwrap()).collect();
    assert_eq!(readings, vec!["module", "service", "files"]);
    assert_eq!(v["meanings"][3]["on"], serde_json::json!(["field", "param"]));
}

#[test]
fn resolution_errors_come_with_file_and_line() {
    let repo = Repo::new("errors");
    repo.law(
        "a.law",
        r#"sources "shop/**"

meaning role on call
  values a | b
  "役割"

meaning unit on field
  values minor | major
  "単位"

law l1
  "宣言されていない意味"
  about payment-info
  changes keep

law l2
  "宣言されていない読み"
  on nowhere
  no call that has role a

law l3
  "about のない規則"
  changes commute with operations

law l4
  "values にない値"
  no call that has role c

law l5
  "宣言されていない意味を has に書く"
  no call that has color red

law l6
  "convert の値"
  about unit
  agrees along flows
  convert yen -> minor by * 100

reading r = file
"#,
    );
    let v = repo.run(&["law", "check"]);
    let e = errors(&v);
    let at = |line: usize| format!(".archsig/law/a.law:{line}");
    assert!(e.contains(&(at(11), "意味 `payment-info` が宣言されていない".to_string())), "{e:?}");
    assert!(e.contains(&(at(16), "読み `nowhere` が宣言されていない".to_string())), "{e:?}");
    assert!(e.contains(&(at(21), "changes commute の規則には about が要る".to_string())), "{e:?}");
    assert!(e.contains(&(at(25), "値 `c` は意味 `role` の values にない".to_string())), "{e:?}");
    assert!(e.contains(&(at(29), "意味 `color` が宣言されていない".to_string())), "{e:?}");
    assert!(e.contains(&(at(33), "convert の `yen` は意味 `unit` の values にない".to_string())), "{e:?}");
    assert_eq!(e.len(), 6, "{e:?}");
    let names: Vec<&str> = v["laws"].as_array().unwrap().iter().map(|l| l["name"].as_str().unwrap()).collect();
    assert!(names.is_empty(), "誤りのある law は外す: {names:?}");
}

#[test]
fn duplicates_broken_defs_and_syntax_rules() {
    let repo = Repo::new("dup");
    repo.law(
        "a.law",
        r#"reading r = file

meaning unit on field
  values minor | major
  "単位"

meaning unit on field
  values x
  "二度目"

def w = operation that writes unit
def bad = operation that writes nope
def nested = operation that calls w

law uses-bad
  "誤りのある def"
  each bad
    calls "audit.record"

law ok
  "正しい law"
  about unit
  agrees along flows
  convert major -> minor by * 100

law ok
  "二度目"
  about unit
  changes keep

law factor
  "倍率"
  about unit
  agrees along flows
  convert major -> minor by * 7

law twice
  "on を二度"
  on r
  on r
  changes keep

law multi
  "no を二行"
  no call
    that has unit minor
"#,
    );
    let v = repo.run(&["law", "check"]);
    let e = errors(&v);
    let has = |line: usize, msg: &str| e.contains(&(format!(".archsig/law/a.law:{line}"), msg.to_string()));
    assert!(has(7, "意味 `unit` が二度宣言されている"), "{e:?}");
    assert!(has(12, "`nope` は意味の語彙にも def にもない"), "{e:?}");
    assert!(has(13, "def の中で def `w` は使えない"), "{e:?}");
    assert!(has(15, "def `bad` は誤りがあるので使えない"), "{e:?}");
    assert!(has(26, "law `ok` が二度宣言されている"), "{e:?}");
    assert!(has(31, "convert の倍率は 10 の冪(10、100、1000 …)で書く"), "{e:?}");
    assert!(has(37, "on は一度だけ書く"), "{e:?}");
    assert!(has(43, "no の規則は一行で書く"), "{e:?}");
    assert_eq!(e.len(), 8, "{e:?}");
    let names: Vec<&str> = v["laws"].as_array().unwrap().iter().map(|l| l["name"].as_str().unwrap()).collect();
    assert_eq!(names, vec!["ok"], "誤りのある宣言は外し、二度目は最初を残す");
    let defs: Vec<&str> = v["defs"].as_array().unwrap().iter().map(|d| d["name"].as_str().unwrap()).collect();
    assert_eq!(defs, vec!["w"]);
}

#[test]
fn readings_patterns_and_grammar_are_checked() {
    let repo = Repo::new("grammar");
    repo.law(
        "a.law",
        r#"sources "shop/**", "shop/[x"

reading first = dir(depth: two)
reading second = file

meaning m on field
  values a |
  "m"

meaning n on field
  "n"
  "二つ目の手がかり"

meaning d on field
  "d"

def d = operation

fresh "x.*"
  "y.*"

law implicit
  "on を省く"
  about d
  changes keep

law quoted
  "on に文字列"
  on "second"
  about d
  changes keep

law explicit
  "誤りのある読みを明示する"
  on first
  about d
  changes keep
"#,
    );
    let v = repo.run(&["law", "check"]);
    let e = errors(&v);
    let has = |line: usize, msg: &str| e.iter().any(|(at, m)| at == &format!(".archsig/law/a.law:{line}") && m.starts_with(msg));
    assert!(has(1, "パターン `shop/[x` が読めない"), "{e:?}");
    assert!(has(3, "depth は整数で書く"), "{e:?}");
    assert!(has(6, "values は `a | b` と書く"), "{e:?}");
    assert!(has(10, "観測の手がかりは一つだけ書く"), "{e:?}");
    assert!(has(17, "`d` は意味の語彙にもある"), "{e:?}");
    assert!(has(19, "fresh の下には何も書かない"), "{e:?}");
    assert!(has(22, "on を省いた Law が使う最初の読み `first` に誤りがある"), "{e:?}");
    assert!(has(27, "on の後には名前を一つ書く"), "{e:?}");
    assert!(has(33, "読み `first` に誤りがある"), "{e:?}");
    assert_eq!(e.len(), 9, "{e:?}");
    assert_eq!(v["laws"].as_array().unwrap().len(), 0);

    repo.law("a.law", "sources \"shop/**\"\n\nmeaning m on field\n  \"m\"\n\nlaw l\n  \"読みがない\"\n  about m\n  changes keep\n");
    let v = repo.run(&["law", "check"]);
    assert_eq!(errors(&v), vec![(".archsig/law/a.law:6".to_string(), "on を省いた Law が使う読みが、一つも宣言されていない".to_string())]);
}

#[test]
fn a_broken_declaration_is_reported_and_the_rest_is_read() {
    let repo = Repo::new("broken");
    repo.law(
        "a.law",
        "sources \"shop/**\"\n\nreading r = dir\n\ndef d = operation that writes m\ndef e = d\n\nmeaning m on field\n  \"m\"\n",
    );
    std::fs::create_dir_all(repo.dir.join("shop")).unwrap();
    std::fs::write(repo.dir.join("shop/a.py"), "a = 1\n").unwrap();
    let v = repo.run(&["law", "check"]);
    let e = errors(&v);
    assert!(e.contains(&(".archsig/law/a.law:3".to_string(), "dir は dir(depth: n) と書く".to_string())), "{e:?}");
    assert!(e.contains(&(".archsig/law/a.law:6".to_string(), "def の中で def `d` は使えない".to_string())), "{e:?}");
    assert_eq!(v["meanings"][0]["name"], "m", "誤りのある宣言のほかは読む");
    let s = repo.run(&["status"]);
    assert_eq!(s["unread"][0]["scopes"], serde_json::json!(["structure", "meaning:m"]), "status は Law の誤りがあっても動く");
    assert_eq!(s["law_errors"].as_array().unwrap().len(), 2, "status は Law の誤りを理由として返す");

    repo.law("a.law", "sources \"shop/**\" \"x/**\"\n\nsources \"shop/[x\"\n");
    let s = repo.run(&["status"]);
    assert_eq!(s["unread"].as_array().unwrap().len(), 0, "読めないパターンの宣言は外れ、status は止まらない");
    assert_eq!(s["law_errors"].as_array().unwrap().len(), 2);
    assert_eq!(s["law_errors"][0]["at"], ".archsig/law/a.law:1", "sources が外れて空になるときも、理由が付く");
}
