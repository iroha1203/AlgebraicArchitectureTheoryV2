//! AC1・AC5・AC6・AC7: 独立定義を使う check と version。

mod common;
use archsig::json::{JNode, parse};
use common::cli::*;
use std::path::{Path, PathBuf};

fn fixture(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures")
        .join(name)
}

fn input<'a>(res: &'a JNode, id: &str) -> Option<&'a JNode> {
    arr(get(res, "inputs"))
        .iter()
        .find(|i| s(get(i, "id")) == id)
}

fn declaration<'a>(res: &'a JNode, name: &str) -> &'a JNode {
    arr(get(res, "declarations"))
        .iter()
        .find(|i| s(get(i, "name")) == name)
        .unwrap()
}

#[test]
fn normative_examples_complete_both_checks() {
    for (stem, namespace) in [
        ("counter", "Counter"),
        ("reservations", "Reservations"),
        ("engine", "Engine"),
    ] {
        let dir = workdir(namespace);
        let definition = fixture(&format!("{stem}.atoms.json"));
        let law_path = fixture(&format!("{stem}.law"));
        let map_path = fixture(&format!("{stem}.archmap.json"));
        // 定義と Law で語彙を得る。ArchMap の欄は inputs に作らない。
        let r = run(
            &dir,
            &[
                "check",
                "--atom-definition",
                definition.to_str().unwrap(),
                "--law",
                law_path.to_str().unwrap(),
                "--out",
                "vocab",
            ],
        );
        let res = consistent(&dir, &r, "complete", 0);
        assert_eq!(arr(get(&res, "inputs")).len(), 2);
        assert!(input(&res, "archmap").is_none());
        assert!(!dir.join("vocab/inputs/archmap.json").exists());
        let vocab = &arr(get(&res, "vocabularies"))[0];
        assert_eq!(s(get(get(vocab, "manifest"), "namespace")), namespace);
        assert_eq!(s(get(get(vocab, "location"), "input")), "definition0");
        assert_eq!(s(get(get(vocab, "location"), "pointer")), "/vocabularies/0");
        let digest = s(get(vocab, "digest")).to_owned();
        let map_doc = parse(&std::fs::read(&map_path).unwrap()).unwrap();
        let binding = &arr(get(&map_doc, "vocabularies"))[0];
        assert_eq!(s(get(binding, "digest")), digest);
        let r = run(
            &dir,
            &[
                "check",
                "--atom-definition",
                definition.to_str().unwrap(),
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
        for (id, path, source, kind) in [
            (
                "definition0",
                "inputs/definitions/0.json",
                &definition,
                "atom_definition",
            ),
            ("law", "inputs/law.law", &law_path, "law"),
            ("archmap", "inputs/archmap.json", &map_path, "archmap"),
        ] {
            let bytes = std::fs::read(source).unwrap();
            assert_eq!(std::fs::read(dir.join("both").join(path)).unwrap(), bytes);
            let identity = input(&res, id).unwrap();
            assert_eq!(s(get(identity, "state")), "read");
            assert_eq!(s(get(identity, "kind")), kind);
            assert_eq!(s(get(identity, "path")), path);
            assert_eq!(
                s(get(identity, "bytes_digest")),
                archsig::canonical::sha256_digest(&bytes)
            );
            assert!(s(get(identity, "model_digest")).starts_with("sha256:"));
        }
        assert_eq!(
            arr(get(&res, "inputs"))
                .iter()
                .map(|i| s(get(i, "id")))
                .collect::<Vec<_>>(),
            ["archmap", "definition0", "law"]
        );
        assert!(!arr(get(&res, "declarations")).is_empty());
        assert!(arr(get(&res, "issues")).is_empty());
        for k in ["elapsed_ms", "peak_bytes"] {
            assert!(
                s(get(get(&res, "usage"), k))
                    .bytes()
                    .all(|b| b.is_ascii_digit())
            );
        }
        if stem == "counter" {
            assert_eq!(
                digest,
                "sha256:388baddb5f87b80f4448ce9be21a4800c92a11001ab356936b14b6d5fb438a11"
            );
            assert_eq!(
                arr(get(&res, "declarations"))
                    .iter()
                    .filter(|d| s(get(d, "name")) == "Counter.State")
                    .count(),
                1
            );
            let primitive = declaration(&res, "Counter.State");
            assert_eq!(s(get(get(primitive, "location"), "input")), "definition0");
            assert_eq!(
                s(get(get(primitive, "location"), "pointer")),
                "/vocabularies/0/declarations/0"
            );
            assert!(arr(get(primitive, "vocabularies")).is_empty());
            let law_text = std::fs::read_to_string(&law_path).unwrap();
            for reading in ["CountCheck", "CountAudit"] {
                let info = declaration(&res, reading);
                let imports = arr(get(info, "vocabularies"));
                assert_eq!(imports.len(), 1);
                assert_eq!(s(get(&imports[0], "namespace")), "Counter");
                assert_eq!(s(get(&imports[0], "digest")), digest);
                assert_eq!(s(get(get(info, "location"), "input")), "law");
            }
            for name in [
                "CountCheck.amount",
                "CountCheck.nonnegative",
                "CountAudit.bounded",
            ] {
                let info = declaration(&res, name);
                assert!(arr(get(info, "vocabularies")).is_empty());
                let ty = get(&arr(get(info, "parameters"))[0], "type");
                assert_eq!(s(&arr(ty)[0]), "Ref");
                assert_eq!(s(&arr(ty)[1]), "Counter.State");
                let span = arr(get(get(info, "location"), "span"));
                let text = &law_text[num(&span[0]) as usize..num(&span[1]) as usize];
                assert!(text.contains(name.rsplit('.').next().unwrap()));
                let refs = arr(get(get(info, "resolution"), "references"));
                let state = refs
                    .iter()
                    .find(|r| s(get(r, "name")) == "Counter.State")
                    .unwrap();
                let span = arr(get(get(state, "location"), "span"));
                assert_eq!(
                    &law_text[num(&span[0]) as usize..num(&span[1]) as usize],
                    "State"
                );
            }
        }
    }
}

#[test]
fn unused_library_split_and_definition_order_preserve_identity_and_locations() {
    let dir = workdir("library");
    let law = fixture("counter.law");
    let library = fixture("counter-library.atoms.json");
    let counter = fixture("counter.atoms.json");
    let extras = fixture("extras.atoms.json");
    let r = run(
        &dir,
        &[
            "check",
            "--atom-definition",
            library.to_str().unwrap(),
            "--law",
            law.to_str().unwrap(),
            "--out",
            "library",
        ],
    );
    let one = consistent(&dir, &r, "complete", 0);
    assert!(arr(get(&one, "issues")).is_empty());
    assert_eq!(arr(get(&one, "vocabularies")).len(), 2);
    let extras_decl = declaration(&one, "Extras.Note");
    assert_eq!(
        s(get(get(extras_decl, "location"), "pointer")),
        "/vocabularies/1/declarations/0"
    );
    for (out, first, second, counter_id, extras_id) in [
        ("split", &counter, &extras, "definition0", "definition1"),
        ("reverse", &extras, &counter, "definition1", "definition0"),
    ] {
        let r = run(
            &dir,
            &[
                "check",
                "--atom-definition",
                first.to_str().unwrap(),
                "--atom-definition",
                second.to_str().unwrap(),
                "--law",
                law.to_str().unwrap(),
                "--out",
                out,
            ],
        );
        let split = consistent(&dir, &r, "complete", 0);
        assert_eq!(
            arr(get(&split, "inputs"))
                .iter()
                .map(|i| s(get(i, "id")))
                .collect::<Vec<_>>(),
            ["definition0", "definition1", "law"]
        );
        for (n, source) in [first, second].iter().enumerate() {
            assert_eq!(
                std::fs::read(dir.join(out).join(format!("inputs/definitions/{n}.json"))).unwrap(),
                std::fs::read(source).unwrap()
            );
        }
        for (i, original) in arr(get(&one, "vocabularies")).iter().enumerate() {
            let current = &arr(get(&split, "vocabularies"))[i];
            assert_eq!(s(get(current, "digest")), s(get(original, "digest")));
            let namespace = s(get(get(current, "manifest"), "namespace"));
            let expected = if namespace == "Counter" {
                counter_id
            } else {
                extras_id
            };
            assert_eq!(s(get(get(current, "location"), "input")), expected);
            assert_eq!(
                s(get(get(current, "location"), "pointer")),
                "/vocabularies/0"
            );
        }
        assert_ne!(
            s(get(input(&one, "definition0").unwrap(), "model_digest")),
            s(get(input(&split, counter_id).unwrap(), "model_digest"))
        );
        let extra = declaration(&split, "Extras.Note");
        assert_eq!(s(get(get(extra, "location"), "input")), extras_id);
        assert_eq!(
            s(get(get(extra, "location"), "pointer")),
            "/vocabularies/0/declarations/0"
        );
        assert!(arr(get(&split, "issues")).is_empty());
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

#[test]
fn counter_count_outside_law_and_missing_are_static_successes() {
    let dir = workdir("counter-static");
    let definition = fixture("counter.atoms.json");
    let law = fixture("counter.law");
    let original = include_str!("fixtures/counter.archmap.json");
    let atom = "{\"id\": \"count\", \"subject\": \"s\", \"field\": \"Counter.State.count\", \"value\": \"2\", \"origin\": \"model\"}";
    assert!(original.contains(atom));
    for (name, map) in [
        (
            "count12",
            original.replacen("\"value\": \"2\"", "\"value\": \"12\"", 1),
        ),
        ("missing", original.replacen(atom, "", 1)),
    ] {
        std::fs::write(dir.join(format!("{name}.json")), &map).unwrap();
        let r = run(
            &dir,
            &[
                "check",
                "--atom-definition",
                definition.to_str().unwrap(),
                "--law",
                law.to_str().unwrap(),
                "--archmap",
                &format!("{name}.json"),
                "--out",
                name,
            ],
        );
        let res = consistent(&dir, &r, "complete", 0);
        assert!(arr(get(&res, "issues")).is_empty());
        assert_eq!(
            std::fs::read(dir.join(name).join("inputs/archmap.json")).unwrap(),
            map.as_bytes()
        );
        let map_input = input(&res, "archmap").unwrap();
        assert!(has(map_input, "model_digest"));
        assert_eq!(
            s(get(map_input, "bytes_digest")),
            archsig::canonical::sha256_digest(map.as_bytes())
        );
        assert_eq!(
            arr(get(&res, "declarations"))
                .iter()
                .filter(|d| s(get(d, "name")) == "Counter.State")
                .count(),
            1
        );
    }
}
