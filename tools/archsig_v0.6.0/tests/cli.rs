//! AC1・AC6・AC8: `archsig check` と `archsig version` を実行して確かめる。

mod common;
use archsig::json::{JNode, parse};
use common::cli::*;
use std::path::{Path, PathBuf};

fn fixture(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures")
        .join(name)
}

fn input<'a>(res: &'a JNode, kind: &str) -> Option<&'a JNode> {
    arr(get(res, "inputs"))
        .iter()
        .find(|i| s(get(i, "kind")) == kind)
}

#[test]
fn normative_examples_complete_both_checks() {
    for (law, map, reading) in [
        (
            "reservations.law",
            "reservations.archmap.json",
            "Reservations",
        ),
        ("engine.law", "engine.archmap.json", "Engine"),
    ] {
        let dir = workdir(reading);
        let law_path = fixture(law);
        let map_path = fixture(map);
        // Law 単独で語彙を得る。ArchMap の欄は inputs に作らない。
        let r = run(
            &dir,
            &[
                "check",
                "--law",
                law_path.to_str().unwrap(),
                "--out",
                "vocab",
            ],
        );
        let res = consistent(&dir, &r, "complete", 0);
        assert_eq!(arr(get(&res, "inputs")).len(), 1);
        assert!(input(&res, "archmap").is_none());
        assert!(!dir.join("vocab/inputs/archmap.json").exists());
        let vocab = &arr(get(&res, "vocabularies"))[0];
        assert_eq!(s(get(get(vocab, "manifest"), "reading")), reading);
        let digest = s(get(vocab, "digest")).to_owned();
        // 例の ArchMap の binding と一致する。
        let map_doc = parse(&std::fs::read(&map_path).unwrap()).unwrap();
        let binding = &arr(get(&map_doc, "vocabularies"))[0];
        assert_eq!(s(get(binding, "digest")), digest);
        // 対応する ArchMap とともに再検査する。
        let r = run(
            &dir,
            &[
                "check",
                "--law",
                law_path.to_str().unwrap(),
                "--archmap",
                map_path.to_str().unwrap(),
                "--out",
                "both",
            ],
        );
        let res = consistent(&dir, &r, "complete", 0);
        assert_eq!(s(get(&res, "command")), "check");
        assert_eq!(s(get(&r.receipt, "result")), "both/result.json");
        assert_eq!(
            std::fs::read(dir.join("both/inputs/law.law")).unwrap(),
            std::fs::read(&law_path).unwrap()
        );
        assert_eq!(
            std::fs::read(dir.join("both/inputs/archmap.json")).unwrap(),
            std::fs::read(&map_path).unwrap()
        );
        let law_input = input(&res, "law").unwrap();
        assert_eq!(s(get(law_input, "state")), "read");
        assert_eq!(s(get(law_input, "path")), "inputs/law.law");
        let map_input = input(&res, "archmap").unwrap();
        assert_eq!(s(get(map_input, "path")), "inputs/archmap.json");
        assert_eq!(
            s(get(map_input, "bytes_digest")),
            archsig::canonical::sha256_digest(&std::fs::read(&map_path).unwrap())
        );
        assert!(s(get(map_input, "model_digest")).starts_with("sha256:"));
        assert!(!arr(get(&res, "declarations")).is_empty());
        assert!(arr(get(&res, "issues")).is_empty());
        for k in ["elapsed_ms", "peak_bytes"] {
            assert!(
                s(get(get(&res, "usage"), k))
                    .bytes()
                    .all(|b| b.is_ascii_digit())
            );
        }
    }
}

#[test]
fn version_matches_the_execution_spec() {
    let out = bin().arg("version").output().unwrap();
    assert_eq!(out.status.code(), Some(0));
    assert_eq!(
        String::from_utf8(out.stdout).unwrap(),
        "{\"product\":\"archsig\",\"version\":\"0.6.0\",\"semantics\":[\"archsig/0.6.0\"]}\n"
    );
}

/// README の利用手順と同じ二つの check。
#[test]
fn readme_usage_reproduces_the_two_checks() {
    let readme = include_str!("../README.md");
    let dir = workdir("readme");
    let crate_dir = env!("CARGO_MANIFEST_DIR");
    let mut ran = 0;
    for line in readme.lines().filter(|l| l.starts_with("archsig check ")) {
        let args: Vec<String> = line
            .split_whitespace()
            .skip(1)
            .map(|a| a.replace("tools/archsig_v0.6.0", crate_dir))
            .collect();
        let args: Vec<&str> = args.iter().map(String::as_str).collect();
        let r = run(&dir, &args);
        consistent(&dir, &r, "complete", 0);
        ran += 1;
    }
    assert_eq!(ran, 2, "README に二つの check がある");
}
