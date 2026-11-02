use crate::common::{cli::*, watchdog};
use archsig_common::{
    canonical::sha256_digest,
    json::{JValue, parse},
};
use std::{path::Path, process::Output};

fn invoke(dir: &Path, args: &[&str]) -> Output {
    let mut command = bin();
    // Neither Python nor any other executable is discoverable via PATH.
    command
        .current_dir(dir)
        .env_clear()
        .env("PATH", dir.join("no-executables"))
        .args(args);
    let captured = watchdog::output(&mut command, CHILD_DEADLINE).unwrap();
    assert!(!captured.timed_out);
    captured.output
}
fn map(digest: &str, span: &str) -> String {
    format!(
        r#"{{"sources":[{{"id":"code","digest":"{digest}","revision":"r1"}}],"origins":[{{"id":"o","locations":[{{"source":"code"{span}}}]}}],"snapshots":[{{"id":"v","atoms":[{{"id":"a","value":[null,-2,1.5,{{"text":"意味"}}],"origin":"o"}},{{"id":"b","value":true,"origin":"o"}}]}}]}}"#
    )
}
fn rejected(output: Output, code: i32, message: &str) {
    assert_eq!(
        output.status.code(),
        Some(code),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(output.stdout.is_empty());
    let error = parse(&output.stderr).unwrap();
    assert_eq!(num(get(&error, "exit_code")), code as u64);
    assert!(String::from_utf8(output.stderr).unwrap().contains(message));
}
const EVIDENCE: &[&str] = &[
    "evidence",
    "--archmap",
    "map.json",
    "--atom",
    "v/a",
    "--atom",
    "v/b",
    "--source",
    "code=source",
];

#[test]
fn evidence_preserves_values_bytes_selection_and_shared_references_without_python() {
    let dir = workdir("observe-evidence");
    let data = "意味\r\nend\n";
    std::fs::write(dir.join("source"), data).unwrap();
    std::fs::write(
        dir.join("map.json"),
        map(&sha256_digest(data.as_bytes()), ""),
    )
    .unwrap();
    let output = invoke(&dir, EVIDENCE);
    assert_eq!(output.status.code(), Some(0));
    assert!(output.stderr.is_empty());
    let result = parse(&output.stdout).unwrap();
    let atoms = arr(get(&result, "atoms"));
    assert_eq!(atoms.len(), 2);
    assert_eq!(s(get(&atoms[0], "id")), "a");
    assert_eq!(s(get(&atoms[1], "id")), "b");
    assert_eq!(s(get(&atoms[0], "snapshot")), "v");
    let values = arr(get(&atoms[0], "value"));
    assert_eq!(values[0].value, JValue::Null);
    assert_eq!(values[1].value, JValue::Num("-2".into()));
    assert_eq!(values[2].value, JValue::Num("1.5".into()));
    assert_eq!(s(get(&values[3], "text")), "意味");
    assert_eq!(arr(get(&result, "sources")).len(), 1);
    let origins = arr(get(&result, "origins"));
    assert_eq!(origins.len(), 1);
    let location = &arr(get(&origins[0], "locations"))[0];
    assert_eq!(s(get(location, "excerpt")), data);
    assert_eq!(
        num(&arr(get(location, "resolved_span"))[1]),
        data.len() as u64
    );
    assert_eq!(
        std::fs::read_dir(&dir).unwrap().count(),
        2,
        "no output files"
    );
}

#[test]
fn evidence_rejects_bad_links_digests_spans_and_duplicates() {
    let dir = workdir("observe-invalid");
    let data = "意味";
    std::fs::write(dir.join("source"), data).unwrap();
    let valid = map(&sha256_digest(data.as_bytes()), "");
    for (text, message) in [
        (
            valid.replace("\"origin\":\"o\"", "\"origin\":\"absent\""),
            "missing reference",
        ),
        (
            valid.replace("\"source\":\"code\"", "\"source\":\"absent\""),
            "missing reference",
        ),
        (
            valid.replace("\"id\":\"b\"", "\"id\":\"a\""),
            "duplicate id",
        ),
        (
            valid.replace("\"value\":true", "\"value\":true,\"value\":false"),
            "duplicate",
        ),
        (valid.replace("sha256:", "sha256:0"), "digest mismatch"),
    ] {
        std::fs::write(dir.join("map.json"), text).unwrap();
        rejected(invoke(&dir, EVIDENCE), 65, message);
    }
    for span in [
        "[1,3]",
        "[0,1]",
        "[3,1]",
        "[-1,3]",
        "[0,7]",
        "[false,3]",
        "[0,1.0]",
        "[0]",
        "null",
    ] {
        std::fs::write(
            dir.join("map.json"),
            map(
                &sha256_digest(data.as_bytes()),
                &format!(",\"span\":{span}"),
            ),
        )
        .unwrap();
        rejected(invoke(&dir, EVIDENCE), 65, "");
    }
    std::fs::write(dir.join("map.json"), &valid).unwrap();
    for selector in ["missing/a", "v/missing"] {
        rejected(
            invoke(
                &dir,
                &[
                    "evidence",
                    "--archmap",
                    "map.json",
                    "--atom",
                    selector,
                    "--source",
                    "code=source",
                ],
            ),
            65,
            "missing reference",
        );
    }
    rejected(
        invoke(
            &dir,
            &["evidence", "--archmap", "map.json", "--atom", "v/a"],
        ),
        65,
        "missing source binding",
    );
    std::fs::write(dir.join("source"), [0xff]).unwrap();
    rejected(invoke(&dir, EVIDENCE), 65, "UTF-8");
    for extra in [
        vec!["--atom", "v/a"],
        vec!["--source", "code=source"],
        vec!["--atom", "bad"],
        vec!["--out", "new"],
    ] {
        let mut args = EVIDENCE.to_vec();
        args.extend(extra);
        rejected(invoke(&dir, &args), 64, "");
    }
    rejected(
        invoke(&dir, &["law-fibers", "--table", "absent"]),
        74,
        "read",
    );
}

#[test]
fn finite_table_cli_refutations_and_help_without_python() {
    let dir = workdir("observe-fibers");
    let table = r#"{"scope":"models","sources":["b","a","c"],"laws":["x"],"q":{"b":"same","a":"same","c":"other"},"v":{"b":{"x":"yes"},"a":{"x":"no"},"c":{"x":"yes"}}}"#;
    for (text, code) in [
        (table.to_owned(), 1),
        (table.replace("\"no\"", "\"yes\""), 0),
    ] {
        std::fs::write(dir.join("table.json"), text).unwrap();
        let output = invoke(&dir, &["law-fibers", "--table", "table.json"]);
        assert_eq!(output.status.code(), Some(code));
        assert!(output.stderr.is_empty());
        let result = parse(&output.stdout).unwrap();
        assert_eq!(has(&result, "descent"), code == 0);
        assert_eq!(
            get(&result, "q_partition"),
            &parse(br#"[["b","a"],["c"]]"#).unwrap()
        );
        if code == 1 {
            let examples = arr(get(&result, "counterexamples"));
            assert_eq!(examples.len(), 1);
            assert_eq!(s(get(&examples[0], "left")), "b");
            assert_eq!(s(get(&examples[0], "right")), "a");
            assert_eq!(get(&examples[0], "laws"), &parse(br#"["x"]"#).unwrap());
        }
    }
    std::fs::write(dir.join("table.json"), r#"{"scope":"x","scope":"y"}"#).unwrap();
    rejected(
        invoke(&dir, &["law-fibers", "--table", "table.json"]),
        65,
        "duplicate",
    );
    for kind in ["evidence", "law-fibers"] {
        for args in [vec![kind, "--help"], vec![kind, "-h"], vec!["help", kind]] {
            let output = invoke(&dir, &args);
            assert!(output.status.success());
            assert!(output.stderr.is_empty());
            assert!(
                String::from_utf8(output.stdout)
                    .unwrap()
                    .contains(&format!("Usage: archsig {kind}"))
            );
        }
    }
}
