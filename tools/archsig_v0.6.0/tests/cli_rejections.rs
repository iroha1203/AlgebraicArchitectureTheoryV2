//! AC6: 拒否の code・位置・終了コードと、Law と ArchMap の失敗での表の保持。

mod common;
use common::cli::*;
use std::path::Path;

const DEFINITION: &str = include_str!("fixtures/reservations.atoms.json");
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
    write(&dir, "d.json", DEFINITION.as_bytes());
    write(&dir, "l.law", LAW.as_bytes());
    write(&dir, "a.json", map);
    let r = run(
        &dir,
        &[
            "check",
            "--atom-definition",
            "d.json",
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
            MAP.replacen("archsig.archmap/2", "archsig.archmap/1", 1)
                .into_bytes(),
            "unsupported_version",
            "/format",
            69,
        ),
        (
            "binding",
            MAP.replacen(
                "8427a2712c22d6eed1cdd5f48258bea102904173558a7087bb82c7d95665c9ff",
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
            LAW.replacen("archsig.law/2", "archsig.law/1", 1)
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
        write(&dir, "d.json", DEFINITION.as_bytes());
        write(&dir, "l.law", &law);
        write(&dir, "a.json", MAP.as_bytes());
        let r = run(
            &dir,
            &[
                "check",
                "--atom-definition",
                "d.json",
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
    write(&dir, "d.json", DEFINITION.as_bytes());
    write(&dir, "l.law", LAW.as_bytes());
    for mut args in [
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
        if args.first() == Some(&"check") {
            args.splice(1..1, ["--atom-definition", "d.json"]);
        }
        let r = run(&dir, &args);
        assert_eq!(r.code, 64, "{args:?}");
        assert_eq!(s(get(&r.receipt, "status")), "invalid");
        if has(&r.receipt, "result") {
            let res = consistent(&dir, &r, "invalid", 64);
            assert_eq!(only_issue(&res).0, "usage");
            assert!(arr(get(&res, "inputs")).is_empty());
        }
    }
    // 定義は一つ以上必須。単数 flag の ArchMap 重複も usage。
    for (out, args) in [
        (
            "no-definition",
            vec!["check", "--law", "l.law", "--out", "no-definition"],
        ),
        (
            "duplicate-map",
            vec![
                "check",
                "--atom-definition",
                "d.json",
                "--law",
                "l.law",
                "--archmap",
                "a.json",
                "--archmap",
                "a.json",
                "--out",
                "duplicate-map",
            ],
        ),
    ] {
        let r = run(&dir, &args);
        let res = consistent(&dir, &r, "invalid", 64);
        assert_eq!(only_issue(&res).0, "usage");
        assert!(arr(get(&res, "inputs")).is_empty());
        assert!(!dir.join(out).join("inputs/law.law").exists());
        assert!(!dir.join(out).join("inputs/definitions/0.json").exists());
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
        &[
            "check",
            "--atom-definition",
            "d.json",
            "--law",
            "l.law",
            "--bogus",
            "--out",
            "o10",
        ],
    );
    consistent(&dir, &r, "invalid", 64);
    // --out が二つあれば出力先を決めず、出力を作らない。
    let r = run(
        &dir,
        &[
            "check",
            "--atom-definition",
            "d.json",
            "--law",
            "l.law",
            "--out",
            "o8",
            "--out",
            "o9",
        ],
    );
    assert_eq!(r.code, 64);
    assert!(!has(&r.receipt, "result"));
    assert!(!dir.join("o8").exists() && !dir.join("o9").exists());
    // 出力先を読めた CLI の不正は、usage の issue を result.json に残す。
    let r = run(
        &dir,
        &[
            "check",
            "--atom-definition",
            "d.json",
            "--law",
            "l.law",
            "--out",
            "o6",
            "--unknown",
            "x",
        ],
    );
    let res = consistent(&dir, &r, "invalid", 64);
    let issue = &arr(get(&res, "issues"))[0];
    assert_eq!(s(get(get(issue, "details"), "argument")), "--unknown");
}

#[test]
fn public_run_with_valid_counter_inputs_and_request_is_usage_without_delivery() {
    use archsig::observed::{control::Control, input::InputSources, prepare_observed};

    let dir = workdir("run-valid-counter-usage");
    write(
        &dir,
        "counter.atoms.json",
        include_bytes!("fixtures/counter.atoms.json"),
    );
    write(&dir, "counter.law", include_bytes!("fixtures/counter.law"));
    write(
        &dir,
        "counter.archmap.json",
        include_bytes!("fixtures/counter.archmap.json"),
    );
    let ask = "a=evaluate(CountCheck.amount,s=@v/s)";
    // 公開 run の拒否を、入力や問いの不正による拒否と区別する。
    let sources = InputSources::from_bytes(
        vec![std::fs::read(dir.join("counter.atoms.json")).unwrap()],
        std::fs::read(dir.join("counter.law")).unwrap(),
        std::fs::read(dir.join("counter.archmap.json")).unwrap(),
    );
    let prepared = prepare_observed(sources, &[ask], &mut Control::unlimited()).unwrap();
    assert_eq!(prepared.requests().requests().len(), 1);
    assert_eq!(
        prepared.requests().requests()[0].declaration(),
        "CountCheck.amount"
    );

    let r = run(
        &dir,
        &[
            "run",
            "--atom-definition",
            "counter.atoms.json",
            "--law",
            "counter.law",
            "--archmap",
            "counter.archmap.json",
            "--ask",
            ask,
            "--out",
            "run-output",
        ],
    );
    assert_eq!(r.code, 64, "{}", r.stderr);
    assert_eq!(s(get(&r.receipt, "format")), "archsig.receipt/1");
    assert_eq!(s(get(&r.receipt, "status")), "invalid");
    assert_eq!(num(get(&r.receipt, "exit_code")), 64);
    // receipt に result がなく、配送先もないため回答や導出は生成されない。
    assert!(!has(&r.receipt, "result"));
    assert!(!dir.join("run-output").exists());
}

#[test]
fn definition_failure_precedes_law_and_archmap_and_empty_tables_keep_copies() {
    let dir = workdir("definition-first");
    let definition = DEFINITION.replacen("\"version\": \"1\"", "\"version\": \"\"", 1);
    write(&dir, "d.json", definition.as_bytes());
    write(&dir, "l.law", b"invalid law");
    write(&dir, "a.json", b"invalid JSON");
    let r = run(
        &dir,
        &[
            "check",
            "--atom-definition",
            "d.json",
            "--law",
            "l.law",
            "--archmap",
            "a.json",
            "--out",
            "o",
        ],
    );
    let res = consistent(&dir, &r, "invalid", 65);
    assert_eq!(
        only_issue(&res),
        (
            "syntax".into(),
            "definition0".into(),
            "/vocabularies/0/version".into()
        )
    );
    assert!(arr(get(&res, "declarations")).is_empty());
    assert!(arr(get(&res, "vocabularies")).is_empty());
    for (path, bytes) in [
        ("inputs/definitions/0.json", definition.as_bytes()),
        ("inputs/law.law", b"invalid law".as_slice()),
        ("inputs/archmap.json", b"invalid JSON".as_slice()),
    ] {
        assert_eq!(std::fs::read(dir.join("o").join(path)).unwrap(), bytes);
    }
}

#[test]
fn unsupported_json_versions_precede_unknown_fields() {
    for (kind, original, format, pointer) in [
        (
            "definition0",
            DEFINITION,
            "archsig.atom-definition/1",
            "/format",
        ),
        ("archmap", MAP, "archsig.archmap/2", "/format"),
    ] {
        for (field, replacement, expected_pointer) in [
            (format, "archsig.future/9", pointer),
            ("archsig/0.6.0", "archsig/9.0.0", "/semantics"),
        ] {
            let dir = workdir(&format!(
                "unknown-{kind}-{}",
                expected_pointer.trim_start_matches('/')
            ));
            let unknown =
                original
                    .replacen(field, replacement, 1)
                    .replacen('{', "{\"future\": true,", 1);
            write(
                &dir,
                "d.json",
                if kind == "definition0" {
                    unknown.as_bytes()
                } else {
                    DEFINITION.as_bytes()
                },
            );
            write(&dir, "l.law", LAW.as_bytes());
            write(
                &dir,
                "a.json",
                if kind == "archmap" {
                    unknown.as_bytes()
                } else {
                    MAP.as_bytes()
                },
            );
            let r = run(
                &dir,
                &[
                    "check",
                    "--atom-definition",
                    "d.json",
                    "--law",
                    "l.law",
                    "--archmap",
                    "a.json",
                    "--out",
                    "o",
                ],
            );
            let res = consistent(&dir, &r, "unsupported", 69);
            assert_eq!(
                only_issue(&res),
                (
                    "unsupported_version".into(),
                    kind.into(),
                    expected_pointer.into()
                )
            );
            assert_eq!(
                arr(get(&res, "declarations")).is_empty(),
                kind == "definition0"
            );
            assert_eq!(
                arr(get(&res, "vocabularies")).is_empty(),
                kind == "definition0"
            );
        }
    }
}

#[test]
fn law_header_version_precedes_lexer_and_primitive_declarations_are_rejected() {
    for (name, law, code, exit) in [
        (
            "unknown-law",
            LAW.replacen("archsig.law/2", "archsig.law/9", 1) + "\n@",
            "unsupported_version",
            69,
        ),
        (
            "primitive-law",
            LAW.replacen(
                "reading Reservations {",
                "reading Reservations { entity Hidden;",
                1,
            ),
            "syntax",
            65,
        ),
    ] {
        let dir = workdir(name);
        write(&dir, "d.json", DEFINITION.as_bytes());
        write(&dir, "l.law", law.as_bytes());
        let r = run(
            &dir,
            &[
                "check",
                "--atom-definition",
                "d.json",
                "--law",
                "l.law",
                "--out",
                "o",
            ],
        );
        let res = consistent(
            &dir,
            &r,
            if exit == 69 { "unsupported" } else { "invalid" },
            exit,
        );
        let issue = only_issue(&res);
        assert_eq!((issue.0.as_str(), issue.1.as_str()), (code, "law"));
        assert!(issue.2.parse::<usize>().is_ok());
        assert!(arr(get(&res, "declarations")).is_empty());
        assert!(arr(get(&res, "vocabularies")).is_empty());
    }
}
