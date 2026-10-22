#[allow(dead_code)]
#[path = "common/cli.rs"]
mod cli;
#[path = "common/request_acceptance_data.rs"]
mod fixture;
use cli::*;
use std::path::{Path, PathBuf};

fn files(name: &str) -> PathBuf {
    let dir = workdir(name);
    let i = fixture::input();
    std::fs::write(dir.join("d.json"), i.definitions()[0].bytes()).unwrap();
    std::fs::write(dir.join("l.law"), i.law().bytes()).unwrap();
    std::fs::write(dir.join("a.json"), i.archmap().bytes()).unwrap();
    dir
}
fn ask(dir: &Path, asks: &[&str]) -> Run {
    let mut args = vec![
        "run",
        "--atom-definition",
        "d.json",
        "--law",
        "l.law",
        "--archmap",
        "a.json",
        "--out",
        "out",
    ];
    for text in asks {
        args.extend(["--ask", *text]);
    }
    run(dir, &args)
}
fn no_artifacts(dir: &Path) {
    let mut names = std::fs::read_dir(dir)
        .unwrap()
        .map(|entry| entry.unwrap().file_name())
        .collect::<Vec<_>>();
    names.sort();
    assert_eq!(
        names,
        ["a.json", "d.json", "l.law"].map(std::ffi::OsString::from)
    );
}
#[test]
fn malformed_build_reports_concrete_usage_before_execution_support() {
    for (index, asks) in [
        vec!["b=build(R)"],
        vec!["b=build(R,on=@v/A,extra=@v/A)"],
        vec!["b=build(R,on=@v/A,on=@v/B)"],
        vec!["b=build(Unknown,on=@v/A)"],
        vec!["b=build(R,on=@v/i)"],
        vec!["b=build(R,on=$a.object.private)", "a=build(R,on=@v/A)"],
        vec!["b=build(R,on=@v/A)", "later=evaluate(R.unknown)"],
    ]
    .into_iter()
    .enumerate()
    {
        let dir = files(&format!("build-usage-{index}"));
        let run = ask(&dir, &asks);
        notified(&dir, &run, "invalid", 64);
        assert!(!arr(get(&run.receipt, "issues")).is_empty());
        assert!(!run.stdout.contains("未実装"), "{}", run.stdout);
        no_artifacts(&dir);
        std::fs::remove_dir_all(dir).unwrap();
    }
}
#[test]
fn build_cycle_stdout_identifies_requests_and_dependency_edges() {
    let dir = files("build-cycle");
    let run = ask(
        &dir,
        &[
            "a=build(R,on=$b.object.root)",
            "b=build(R,on=$a.algebra.base.subject)",
        ],
    );
    notified(&dir, &run, "invalid", 64);
    let issues = arr(get(&run.receipt, "issues"));
    for id in ["a", "b"] {
        let issue = issues.iter().find(|i| s(get(i, "request")) == id).unwrap();
        assert_eq!(s(get(issue, "code")), "cycle");
        let message = s(get(issue, "message"));
        assert!(message.contains("a, b"), "{message}");
        assert!(
            message.contains(if id == "a" { "a -> b" } else { "b -> a" }),
            "{message}"
        );
    }
    no_artifacts(&dir);
    std::fs::remove_dir_all(dir).unwrap();
}
#[test]
fn valid_build_keeps_explicit_unimplemented_error_and_no_failure_artifacts() {
    let dir = files("build-not-implemented");
    let run = ask(&dir, &["b=build(R,on=@v/A)"]);
    notified(&dir, &run, "error", 70);
    assert!(run.stdout.contains("未実装"));
    assert!(run.stdout.contains("`b`"));
    assert!(run.stdout.contains("`build`"));
    assert!(!run.stdout.contains("unsupported_algorithm"));
    no_artifacts(&dir);
    std::fs::remove_dir_all(dir).unwrap();
}
#[test]
fn invalid_build_preserves_existing_output_contents() {
    let dir = files("build-existing-out");
    std::fs::create_dir(dir.join("out")).unwrap();
    std::fs::write(dir.join("out/kept"), "existing-result").unwrap();
    let run = ask(&dir, &["b=build(R,on=@v/i)"]);
    notified(&dir, &run, "invalid", 64);
    assert_eq!(
        std::fs::read(dir.join("out/kept")).unwrap(),
        b"existing-result"
    );
    assert_eq!(std::fs::read_dir(dir.join("out")).unwrap().count(), 1);
    assert_eq!(std::fs::read_dir(&dir).unwrap().count(), 4);
    std::fs::remove_dir_all(dir).unwrap();
}
