//! Handleが消えた形への案内を実CLIで確かめる。
use crate::common;
use common::cli::*;
use std::path::PathBuf;

fn input(label: &str) -> PathBuf {
    let dir = workdir(label);
    for (name, bytes) in [
        (
            "d.json",
            include_bytes!("fixtures/counter.atoms.json").as_slice(),
        ),
        ("l.law", include_bytes!("fixtures/counter.law").as_slice()),
        (
            "a.json",
            include_bytes!("fixtures/counter.archmap.json").as_slice(),
        ),
    ] {
        std::fs::write(dir.join(name), bytes).unwrap();
    }
    dir
}

#[test]
fn syntax_and_duplicate_keys_or_ids_precede_input_errors() {
    let dir = input("syntax-before-inputs");
    let bad_asks: &[&[&str]] = &[
        &["bad=evaluate(CountCheck.amount,s=@v)"],
        &["bad=needed(.value)"],
        &["bad=evaluate(CountCheck.amount,s=@v/s,s=@v/s)"],
        &["same=needed($other)", "same=needed($other)"],
    ];
    for missing in [true, false] {
        if !missing {
            std::fs::write(dir.join("bad.json"), "{\"format\":false}").unwrap();
        }
        for asks in bad_asks {
            let mut args = vec![
                "run",
                "--atom-definition",
                "bad.json",
                "--law",
                "l.law",
                "--archmap",
                "a.json",
                "--out",
                "out",
            ];
            for ask in *asks {
                args.extend(["--ask", ask]);
            }
            let result = without_file_changes(&dir, || run_binary(&dir, &args));
            assert_eq!(result.code, 64, "{}", result.stderr);
            assert!(result.stdout.is_empty());
            let issue = &arr(get(&result.receipt, "issues"))[0];
            assert_eq!(s(get(issue, "code")), "usage");
            assert!(!has(issue, "location"));
            assert!(!dir.join("out").exists());
        }
        // 宣言名の解決は入力検査後なので、同じ入力の失敗が先に返る。
        let result = run_binary(
            &dir,
            &[
                "run",
                "--atom-definition",
                "bad.json",
                "--law",
                "l.law",
                "--archmap",
                "a.json",
                "--ask",
                "q=check(Unknown.rule,s=@v/s)",
            ],
        );
        assert_eq!(result.code, if missing { 74 } else { 65 });
        assert!(result.stdout.is_empty());
    }
    let result = run_binary(
        &dir,
        &[
            "run",
            "--atom-definition",
            "d.json",
            "--law",
            "l.law",
            "--archmap",
            "a.json",
            "--ask",
            "q=evaluate(CountCheck.amount,s=@v/s)",
        ],
    );
    assert_eq!(result.code, 0);
    assert!(result.stderr.is_empty());
    assert_eq!(
        s(get(
            get(
                get(&arr(get(&result.receipt, "answers"))[0], "outputs"),
                "value"
            ),
            "value"
        )),
        "2"
    );
}

#[test]
fn missing_handle_shapes_suggest_single_quotes_without_changing_the_error() {
    let dir = input("shell-hint-shapes");
    for ask in [
        "bad=needed()",
        "bad=needed( )",
        "bad=evaluate(CountCheck.amount,s=.value)",
        "bad=evaluate(CountCheck.amount,s=[0])",
        "bad=evaluate(CountCheck.amount,s=)",
        "bad=evaluate(CountCheck.amount,s=",
        "bad=compose(.evaluation,then=.evaluation)",
        "bad=compose($ok.evaluation,then=.evaluation)",
        "bad=compose(,then=$ok.evaluation)",
        "bad=compare($ok.value,to=[0],kind=value)",
        "bad=localize(.object)",
        "bad=diagnose(.system)",
        "bad=build(CountCheck,on=)",
        "bad=map(Counter.Unknown,on=.value,reading=CountCheck)",
    ] {
        let r = without_file_changes(&dir, || {
            run(
                &dir,
                &[
                    "run",
                    "--atom-definition",
                    "d.json",
                    "--law",
                    "l.law",
                    "--archmap",
                    "a.json",
                    "--out",
                    "out",
                    "--ask",
                    ask,
                ],
            )
        });
        assert_eq!(r.code, 64, "{ask}: {}", r.stdout);
        assert_eq!(s(get(&r.receipt, "status")), "invalid");
        assert!(!has(&r.receipt, "result"));
        let issues = arr(get(&r.receipt, "issues"));
        assert_eq!(issues.len(), 1);
        let issue = &issues[0];
        assert_eq!(s(get(issue, "code")), "usage");
        assert_eq!(s(get(issue, "request")), "bad");
        assert_eq!(s(get(get(issue, "details"), "argument")), ask);
        let message = s(get(issue, "message"));
        assert!(
            message.contains("may have expanded $id"),
            "{ask}: {message}"
        );
        assert!(
            message.contains("--ask expression in single quotes"),
            "{ask}: {message}"
        );
    }
}

#[test]
fn unrelated_errors_and_declaration_positions_do_not_get_the_shell_hint() {
    let dir = input("shell-hint-negative");
    for ask in [
        "bad=check(CountCheck.nonnegativ,s=@v/s)",
        "bad=needed(Unknown)",
        "bad=evaluate(.amount,s=@v/s)",
        "bad=build(,on=@v/s)",
        "bad=map(Counter.Unknown,on=@v/s,reading=.value)",
        "bad=localize($ok.object,law=)",
        "bad=localize($ok.object,using=.value)",
        "bad=solve(CountCheck.nonnegative,using=)",
        "bad=quotient(CountCheck.amount,law=.value)",
        "bad=compare($ok.value,to=$ok.value,kind=)",
        "bad=compose($ok.evaluation,other=.evaluation)",
        "bad=diagnose($ok.system,degree=)",
        "bad=diagnose($ok.system,side=.semantic)",
        "bad=unknown()",
        "bad=needed($)",
        "bad=needed(@)",
        "bad=needed($ok.)",
        "bad=needed",
    ] {
        let r = without_file_changes(&dir, || {
            run(
                &dir,
                &[
                    "run",
                    "--atom-definition",
                    "d.json",
                    "--law",
                    "l.law",
                    "--archmap",
                    "a.json",
                    "--out",
                    "out",
                    "--ask",
                    ask,
                ],
            )
        });
        assert_eq!(r.code, 64, "{ask}: {}", r.stdout);
        assert!(!has(&r.receipt, "result"));
        for issue in arr(get(&r.receipt, "issues")) {
            assert!(
                !s(get(issue, "message")).contains("single quotes"),
                "{ask}: {}",
                r.stdout
            );
        }
    }
}

#[test]
fn actual_double_quoted_shell_expansion_gets_the_hint() {
    let dir = input("shell-hint-real-shell");
    let output = std::process::Command::new("/bin/sh")
        .current_dir(&dir)
        .env_remove("ok")
        .args(["-c", r#"exec "$1" run --atom-definition d.json --law l.law --archmap a.json --out out --ask "n=needed($ok)""#,
            "archsig-shell-hint", env!("CARGO_BIN_EXE_archsig")])
        .output().unwrap();
    assert_eq!(output.status.code(), Some(64));
    assert!(output.stdout.is_empty());
    let stderr = String::from_utf8(output.stderr).unwrap();
    assert_eq!(stderr.matches('\n').count(), 1);
    let receipt = archsig_common::json::parse(stderr.trim_end().as_bytes()).unwrap();
    let issue = &arr(get(&receipt, "issues"))[0];
    assert_eq!(s(get(issue, "code")), "usage");
    assert_eq!(s(get(get(issue, "details"), "argument")), "n=needed()");
    assert!(s(get(issue, "message")).contains("single quotes"));
    assert!(!has(&receipt, "result"));
    let mut files = std::fs::read_dir(&dir)
        .unwrap()
        .map(|entry| entry.unwrap().file_name())
        .collect::<Vec<_>>();
    files.sort();
    assert_eq!(files, ["a.json", "d.json", "l.law"]);
}
