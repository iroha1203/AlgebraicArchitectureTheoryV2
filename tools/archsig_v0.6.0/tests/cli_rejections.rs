//! AC6: 拒否の code・位置・終了コードと、Law と ArchMap の失敗での表の保持。

mod common;
use common::cli::*;
use std::path::Path;

const LAW: &str = include_str!("fixtures/reservations.law");
const MAP: &str = include_str!("fixtures/reservations.archmap.json");

fn write(dir: &Path, name: &str, bytes: &[u8]) -> String {
    std::fs::write(dir.join(name), bytes).unwrap();
    name.to_owned()
}

/// 一つの issue の code、input、pointer または span 開始。
fn only_issue(res: &archsig::json::JNode) -> (String, String, String) {
    let issues = arr(get(res, "issues"));
    assert_eq!(issues.len(), 1);
    let i = &issues[0];
    let code = s(get(i, "code")).to_owned();
    if !has(i, "location") {
        return (code, String::new(), String::new());
    }
    let loc = get(i, "location");
    let input = s(get(loc, "input")).to_owned();
    // pointer が決まらない構文エラーは、span の開始を位置とする。
    let at = match has(loc, "pointer").then(|| s(get(loc, "pointer"))) {
        Some(p) if !p.is_empty() => p.to_owned(),
        _ => num(&arr(get(loc, "span"))[0]).to_string(),
    };
    (code, input, at)
}

fn check_map(name: &str, map: &[u8]) -> (archsig::json::JNode, Run) {
    let dir = workdir(name);
    write(&dir, "l.law", LAW.as_bytes());
    write(&dir, "a.json", map);
    let r = run(
        &dir,
        &[
            "check",
            "--law",
            "l.law",
            "--archmap",
            "a.json",
            "--out",
            "o",
        ],
    );
    let res = result_json(&dir, &r);
    (res, r)
}

#[test]
fn archmap_rejections_keep_the_law_tables() {
    let cases: Vec<(&str, Vec<u8>, &str, &str, i32)> = vec![
        (
            "dupkey",
            MAP.replacen("\"sources\": [],", "\"sources\": [], \"sources\": [],", 1)
                .into_bytes(),
            "duplicate_key",
            "/sources",
            65,
        ),
        (
            "unknown",
            MAP.replacen("\"sources\": [],", "\"sources\": [], \"extra\": true,", 1)
                .into_bytes(),
            "syntax",
            "/extra",
            65,
        ),
        (
            "null",
            MAP.replacen("\"locations\": [],", "\"locations\": null,", 1)
                .into_bytes(),
            "syntax",
            "/origins/0/locations",
            65,
        ),
        (
            "surrogate",
            MAP.replacen("二つのシステム", "\\udc00", 1).into_bytes(),
            "syntax",
            "",
            65,
        ),
        (
            "version",
            MAP.replacen("archsig.archmap/1", "archsig.archmap/2", 1)
                .into_bytes(),
            "unsupported_version",
            "/format",
            69,
        ),
        (
            "binding",
            MAP.replacen(
                "ede3c701fddea98a6ebf3d31406a0d684dc01256e3ee14a0fb151250b5f05ea1",
                &"0".repeat(64),
                1,
            )
            .into_bytes(),
            "vocabulary_mismatch",
            "/vocabularies/0/digest",
            65,
        ),
    ];
    for (name, map, code, pointer, exit) in cases {
        let (res, r) = check_map(name, &map);
        let status = if exit == 69 { "unsupported" } else { "invalid" };
        let dir = std::env::temp_dir().join(format!("archsig-cli-{}-{name}", std::process::id()));
        consistent(&dir, &r, status, exit);
        let (c, input, at) = only_issue(&res);
        assert_eq!((c.as_str(), input.as_str()), (code, "archmap"), "{name}");
        if !pointer.is_empty() {
            assert_eq!(at, pointer, "{name}");
        }
        // Law の検査は完了しているので、宣言と語彙の表を保持する。
        assert!(!arr(get(&res, "declarations")).is_empty(), "{name}");
        assert_eq!(arr(get(&res, "vocabularies")).len(), 1, "{name}");
    }
    // 構文エラーの位置は byte 区間の開始。
    let surrogate = MAP.replacen("二つのシステム", "\\udc00", 1);
    let (res, _) = check_map("surrogate-at", surrogate.as_bytes());
    let at = surrogate.find("\\udc00").unwrap().to_string();
    assert_eq!(
        only_issue(&res),
        ("syntax".to_owned(), "archmap".to_owned(), at)
    );
    let mut bom = vec![0xEF, 0xBB, 0xBF];
    bom.extend_from_slice(MAP.as_bytes());
    let (res, r) = check_map("bom", &bom);
    assert_eq!(r.code, 65);
    assert_eq!(
        only_issue(&res),
        ("syntax".to_owned(), "archmap".to_owned(), "0".to_owned())
    );
    let mut bad = MAP.as_bytes().to_vec();
    let at = MAP.find("二つ").unwrap();
    bad[at] = 0xFF;
    let (res, r) = check_map("utf8", &bad);
    assert_eq!(r.code, 65);
    assert_eq!(
        only_issue(&res),
        ("syntax".to_owned(), "archmap".to_owned(), at.to_string())
    );
    assert!(!arr(get(&res, "declarations")).is_empty());
}

#[test]
fn law_rejections_empty_the_tables() {
    let cases: Vec<(&str, Vec<u8>, &str, &str, i32)> = vec![
        (
            "law-type",
            LAW.replacen("(s.free, s.held)", "(s.free, true)", 1)
                .into_bytes(),
            "type",
            "law",
            65,
        ),
        (
            "law-version",
            LAW.replacen("archsig.law/1", "archsig.law/9", 1)
                .into_bytes(),
            "unsupported_version",
            "law",
            69,
        ),
        (
            "law-surrogate",
            LAW.replacen(
                "reading Reservations {",
                "reading Reservations { view t(): Text = \"\\ud800\";",
                1,
            )
            .into_bytes(),
            "syntax",
            "law",
            65,
        ),
    ];
    let mut cases = cases;
    let mut bom = vec![0xEF, 0xBB, 0xBF];
    bom.extend_from_slice(LAW.as_bytes());
    cases.push(("law-bom", bom, "syntax", "law", 65));
    let mut bad = LAW.as_bytes().to_vec();
    bad[LAW.find("Reservations").unwrap()] = 0xFF;
    cases.push(("law-utf8", bad, "syntax", "law", 65));
    for (name, law, code, input, exit) in cases {
        let dir = workdir(name);
        write(&dir, "l.law", &law);
        write(&dir, "a.json", MAP.as_bytes());
        let r = run(
            &dir,
            &[
                "check",
                "--law",
                "l.law",
                "--archmap",
                "a.json",
                "--out",
                "o",
            ],
        );
        let status = if exit == 69 { "unsupported" } else { "invalid" };
        let res = consistent(&dir, &r, status, exit);
        let (c, i, at) = only_issue(&res);
        assert_eq!((c.as_str(), i.as_str()), (code, input), "{name}");
        assert!(at.parse::<usize>().is_ok(), "Law の位置は span");
        if name == "law-surrogate" {
            let text = String::from_utf8(law.clone()).unwrap();
            assert_eq!(at, text.find("\\ud800").unwrap().to_string());
        }
        assert!(arr(get(&res, "declarations")).is_empty(), "{name}");
        assert!(arr(get(&res, "vocabularies")).is_empty(), "{name}");
        // 読めた入力は同梱する。
        assert_eq!(std::fs::read(dir.join("o/inputs/law.law")).unwrap(), law);
        assert!(dir.join("o/inputs/archmap.json").exists());
    }
}

#[test]
fn cli_misuse_is_usage() {
    let dir = workdir("usage");
    write(&dir, "l.law", LAW.as_bytes());
    for args in [
        vec!["check", "--law", "l.law"],
        vec!["check", "--law", "l.law", "--law", "l.law", "--out", "o1"],
        vec!["check", "--law", "l.law", "--out", "o2", "--time-ms", "5"],
        vec!["check", "--law", "l.law", "--out", "o3", "extra"],
        vec!["check", "--out", "o4"],
        vec!["frobnicate"],
        vec![
            "run",
            "--law",
            "l.law",
            "--archmap",
            "a.json",
            "--ask",
            "x=check(R.l)",
            "--out",
            "o5",
        ],
        vec!["version", "--law"],
    ] {
        let r = run(&dir, &args);
        assert_eq!(r.code, 64, "{args:?}");
        assert_eq!(s(get(&r.receipt, "status")), "invalid");
        if has(&r.receipt, "result") {
            let res = consistent(&dir, &r, "invalid", 64);
            assert_eq!(only_issue(&res).0, "usage");
            assert!(arr(get(&res, "inputs")).is_empty());
        }
    }
    // 提供しない run は、出力を作らない usage とする。
    let r = run(
        &dir,
        &[
            "run",
            "--law",
            "l.law",
            "--ask",
            "x=check(R.l)",
            "--out",
            "o7",
        ],
    );
    assert_eq!(r.code, 64);
    assert!(!has(&r.receipt, "result"));
    assert!(!dir.join("o7").exists());
    // 未知の flag の後の --out も出力先として読む。
    let r = run(
        &dir,
        &["check", "--law", "l.law", "--bogus", "--out", "o10"],
    );
    consistent(&dir, &r, "invalid", 64);
    // --out が二つあれば出力先を決めず、出力を作らない。
    let r = run(
        &dir,
        &["check", "--law", "l.law", "--out", "o8", "--out", "o9"],
    );
    assert_eq!(r.code, 64);
    assert!(!has(&r.receipt, "result"));
    assert!(!dir.join("o8").exists() && !dir.join("o9").exists());
    // 出力先を読めた CLI の不正は、usage の issue を result.json に残す。
    let r = run(
        &dir,
        &["check", "--law", "l.law", "--out", "o6", "--unknown", "x"],
    );
    let res = consistent(&dir, &r, "invalid", 64);
    let issue = &arr(get(&res, "issues"))[0];
    assert_eq!(s(get(get(issue, "details"), "argument")), "--unknown");
}
