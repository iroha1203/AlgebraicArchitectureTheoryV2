//! receiptから得たdigestを入力者が貼り直す経路を確かめる。
use crate::common;
use archsig_common::json::JNode;
use common::cli::*;
use std::path::{Path, PathBuf};

const DEFINITION: &str = include_str!("fixtures/counter.atoms.json");
const LIBRARY: &str = include_str!("fixtures/counter-library.atoms.json");
const LAW: &str = include_str!("fixtures/counter.law");
const MAP: &str = include_str!("fixtures/counter.archmap.json");
const OLD_DIGEST: &str = "sha256:388baddb5f87b80f4448ce9be21a4800c92a11001ab356936b14b6d5fb438a11";

fn input(label: &str, definition: &str, law: &str, map: &str) -> PathBuf {
    let dir = workdir(label);
    for (name, text) in [("d.json", definition), ("l.law", law), ("a.json", map)] {
        std::fs::write(dir.join(name), text).unwrap();
    }
    dir
}
fn check(dir: &Path) -> Run {
    run(
        dir,
        &[
            "check",
            "--atom-definition",
            "d.json",
            "--law",
            "l.law",
            "--archmap",
            "a.json",
            "--out",
            "out",
        ],
    )
}
fn rejection<'a>(r: &'a Run, code: &str, input: &str) -> &'a JNode {
    assert_eq!(r.code, 65, "{}", r.stdout);
    assert_eq!(s(get(&r.receipt, "status")), "invalid");
    assert!(!has(&r.receipt, "result"));
    let issues = arr(get(&r.receipt, "issues"));
    assert_eq!(issues.len(), 1);
    let issue = &issues[0];
    assert_eq!(s(get(issue, "code")), code);
    assert_eq!(s(get(get(issue, "location"), "input")), input);
    assert!(s(get(issue, "message")).is_ascii());
    issue
}

#[test]
fn changed_meaning_is_repaired_from_law_and_archmap_receipts_without_bootstrap() {
    let definition = DEFINITION.replace("この状態が保持する件数。", "The revised counter meaning.");
    assert_ne!(definition, DEFINITION);
    let dir = input("vocabulary-digest-repair", &definition, LAW, MAP);
    let r = without_file_changes(&dir, || check(&dir));
    let law_issue = rejection(&r, "vocabulary_mismatch", "law");
    let details = get(&law_issue, "details");
    assert_eq!(s(get(details, "namespace")), "Counter");
    assert_eq!(s(get(details, "version")), "1");
    assert_eq!(s(get(details, "found_digest")), OLD_DIGEST);
    assert!(!has(details, "available"));
    assert!(r.stdout.len() < 1000);
    let digest = s(get(details, "expected_digest")).to_owned();
    assert_ne!(digest, OLD_DIGEST);
    assert!(digest.starts_with("sha256:"));
    assert_eq!(digest.len(), 71);
    assert!(s(get(&law_issue, "message")).contains(&digest));
    assert!(has(get(&law_issue, "location"), "span"));

    // 入力者がreceiptの値だけを貼る。製品が入力を書き換えないことは各失敗で検査する。
    std::fs::write(dir.join("l.law"), LAW.replace(OLD_DIGEST, &digest)).unwrap();
    let r = without_file_changes(&dir, || check(&dir));
    let map_issue = rejection(&r, "vocabulary_mismatch", "archmap");
    assert_eq!(get(&map_issue, "details").value, details.value);
    assert_eq!(
        get(map_issue, "message").value,
        get(law_issue, "message").value
    );
    assert_eq!(
        s(get(get(&map_issue, "location"), "pointer")),
        "/vocabularies/0/digest"
    );
    assert!(s(get(&map_issue, "message")).contains(&digest));

    std::fs::write(dir.join("a.json"), MAP.replace(OLD_DIGEST, &digest)).unwrap();
    let r = check(&dir);
    assert_eq!(r.code, 0, "{}", r.stdout);
    let result = result_json(&dir, &r);
    let vocabulary = &arr(get(&result, "vocabularies"))[0];
    assert_eq!(s(get(vocabulary, "digest")), digest);
    assert_eq!(
        std::fs::read_to_string(dir.join("d.json")).unwrap(),
        definition
    );
    let mut names = std::fs::read_dir(&dir)
        .unwrap()
        .map(|e| e.unwrap().file_name())
        .collect::<Vec<_>>();
    names.sort();
    assert_eq!(names, ["a.json", "d.json", "l.law", "out"]);
}

#[test]
fn absent_namespace_or_version_lists_the_supplied_vocabularies_in_both_inputs() {
    for (namespace, version, code, field) in [
        ("Missing", "1", "reference", "namespace"),
        ("Counter", "99", "vocabulary_mismatch", "version"),
    ] {
        let bad_law = LAW.replacen(
            "vocabulary Counter version \"1\"",
            &format!("vocabulary {namespace} version \"{version}\""),
            1,
        );
        let bad_map = MAP.replacen(
            "\"namespace\": \"Counter\", \"version\": \"1\"",
            &format!("\"namespace\": \"{namespace}\", \"version\": \"{version}\""),
            1,
        );
        assert_ne!(bad_law, LAW);
        assert_ne!(bad_map, MAP);
        let mut previous: Option<Run> = None;
        for (kind, law, map) in [
            ("law", bad_law.as_str(), MAP),
            ("archmap", LAW, bad_map.as_str()),
        ] {
            let dir = input(
                &format!("vocabulary-absent-{namespace}-{version}-{kind}"),
                LIBRARY,
                law,
                map,
            );
            let r = without_file_changes(&dir, || check(&dir));
            let issue = rejection(&r, code, kind);
            let details = get(&issue, "details");
            assert_eq!(s(get(details, "namespace")), namespace);
            assert_eq!(s(get(details, "version")), version);
            assert!(!has(details, "expected_digest"));
            let available = arr(get(details, "available"));
            assert_eq!(
                available
                    .iter()
                    .map(|v| (s(get(v, "namespace")), s(get(v, "version"))))
                    .collect::<Vec<_>>(),
                [("Counter", "1"), ("Extras", "1")]
            );
            let message = s(get(&issue, "message"));
            assert!(message.contains("is not defined"));
            assert!(message.contains("Counter@1"));
            assert!(message.contains("Extras@1"));
            if kind == "archmap" {
                assert_eq!(
                    s(get(get(&issue, "location"), "pointer")),
                    format!("/vocabularies/0/{field}")
                );
            }
            if let Some(previous) = &previous {
                let previous_issue = &arr(get(&previous.receipt, "issues"))[0];
                assert_eq!(details.value, get(previous_issue, "details").value);
            }
            previous = Some(r);
        }
    }
}

#[test]
fn missing_archmap_binding_returns_the_known_binding_without_a_fabricated_input_digest() {
    let written =
        format!(r#"{{"namespace": "Counter", "version": "1", "digest": "{OLD_DIGEST}"}}"#);
    let map = MAP.replacen(&written, "", 1);
    assert_ne!(map, MAP);
    let dir = input("vocabulary-missing-binding", DEFINITION, LAW, &map);
    let r = without_file_changes(&dir, || check(&dir));
    let issue = rejection(&r, "vocabulary_mismatch", "archmap");
    assert_eq!(s(get(get(&issue, "location"), "pointer")), "/vocabularies");
    let details = get(&issue, "details");
    assert_eq!(s(get(details, "namespace")), "Counter");
    assert_eq!(s(get(details, "version")), "1");
    assert_eq!(s(get(details, "expected_digest")), OLD_DIGEST);
    assert!(!has(details, "found_digest"));
    assert!(s(get(&issue, "message")).contains(OLD_DIGEST));
}
