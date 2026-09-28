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
            ("payment-follows-order", "changes_commute"),
            ("identity-mail-from-auth", "no"),
            ("payment-writes-are-audited", "each"),
            ("amount-units-agree", "agrees"),
            ("transaction-id-kept", "agrees"),
            ("payment-info-kept", "changes_keep"),
            ("order-view-sync", "roundtrips"),
        ]
    );
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
}
