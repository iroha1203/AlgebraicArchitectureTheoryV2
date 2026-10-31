use crate::common::cli;
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
        let run = without_file_changes(&dir, || ask(&dir, &asks));
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
    let run = without_file_changes(&dir, || ask(
        &dir,
        &[
            "a=build(R,on=$b.object.root)",
            "b=build(R,on=$a.algebra.base.subject)",
        ],
    ));
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
fn valid_build_constructs_the_empty_reading_algebra() {
    let dir = files("build-empty-reading");
    let law = std::fs::read_to_string(dir.join("l.law"))
        .unwrap()
        .replace(fixture::BODY, "");
    std::fs::write(dir.join("l.law"), law).unwrap();
    let run = ask(&dir, &["b=build(R,on=@v/A)"]);
    assert_eq!(run.code, 0, "{}", run.stdout);
    let result = result_json(&dir, &run);
    let answer = &arr(get(&result, "answers"))[0];
    assert_eq!(s(get(answer, "status")), "established");
    assert!(has(get(answer, "outputs"), "object"));
    assert!(has(get(answer, "outputs"), "algebra"));
    std::fs::remove_dir_all(dir).unwrap();
}
#[test]
fn invalid_build_preserves_existing_output_contents() {
    let dir = files("build-existing-out");
    std::fs::create_dir(dir.join("out")).unwrap();
    std::fs::write(dir.join("out/kept"), "existing-result").unwrap();
    let run = without_file_changes(&dir, || ask(&dir, &["b=build(R,on=@v/i)"]));
    notified(&dir, &run, "invalid", 64);
    assert_eq!(
        std::fs::read(dir.join("out/kept")).unwrap(),
        b"existing-result"
    );
    assert_eq!(std::fs::read_dir(dir.join("out")).unwrap().count(), 1);
    assert_eq!(std::fs::read_dir(&dir).unwrap().count(), 4);
    std::fs::remove_dir_all(dir).unwrap();
}
