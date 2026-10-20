//! 再利用候補を採用しない全再計算と、現在入力への帰属。
mod common;
use archsig::canonical::Json;
use archsig::json::{JNode, JValue};
use common::cli::*;
use std::path::{Path, PathBuf};
const D: &[u8] = include_bytes!("fixtures/counter.atoms.json");
const L: &str = include_str!("fixtures/counter.law");
const A: &str = include_str!("fixtures/counter.archmap.json");
const ASKS: [&str; 3] = [
    "n=evaluate(CountCheck.amount,s=@v/s)",
    "audit=check(CountAudit.bounded,s=@v/s)",
    "u=check(CountAudit.bounded)",
];
fn setup(name: &str) -> PathBuf {
    let dir = workdir(name);
    for (name, bytes) in [
        ("d.json", D),
        ("l.law", L.as_bytes()),
        ("a.json", A.as_bytes()),
    ] {
        std::fs::write(dir.join(name), bytes).unwrap();
    }
    dir
}
fn execute(dir: &Path, out: &str, reuse: Option<&str>, asks: &[&str]) -> Run {
    let mut args = vec![
        "run",
        "--atom-definition",
        "d.json",
        "--law",
        "l.law",
        "--archmap",
        "a.json",
        "--out",
        out,
    ];
    if let Some(path) = reuse {
        args.extend(["--reuse", path]);
    }
    for ask in asks {
        args.extend(["--ask", ask]);
    }
    run(dir, &args)
}
fn checked(dir: &Path, r: &Run, code: i32, reused: bool) -> JNode {
    assert_eq!(r.code, code, "{}", r.stdout);
    let result = result_json(dir, r);
    let reuse = get(&result, "reuse");
    assert_eq!(get(reuse, "requested").value, JValue::Bool(reused));
    assert_eq!(num(get(reuse, "accepted_nodes")), 0);
    assert_eq!(
        num(get(reuse, "recomputed_nodes")),
        arr(get(&result, "nodes")).len() as u64
    );
    assert_eq!(num(get(&result, "exit_code")), code as u64);
    assert!(!has(&r.receipt, "issues"), "候補の拒否は実行失敗にしない");
    result
}
fn value(result: &JNode) -> &str {
    let output = get(get(&arr(get(result, "answers"))[0], "outputs"), "value");
    s(get(
        arr(get(result, "nodes"))
            .iter()
            .find(|n| s(get(n, "id")) == s(get(output, "node")))
            .unwrap(),
        "value",
    ))
}
// 候補の改変だけに用いる。期待値は手計算した2/12とLawの条件で明記する。
fn owned(node: &JNode) -> Json {
    match &node.value {
        JValue::Bool(b) => Json::Bool(*b),
        JValue::Num(n) => Json::Nat(n.parse().unwrap()),
        JValue::Str(s) => Json::str(s),
        JValue::Arr(values) => Json::Arr(values.iter().map(owned).collect()),
        JValue::Obj(fields) => Json::Obj(
            fields
                .iter()
                .map(|(key, value)| (key.clone(), owned(value)))
                .collect(),
        ),
        JValue::Null => panic!("製品結果にnullはない"),
    }
}
fn field_mut<'a>(json: &'a mut Json, name: &str) -> &'a mut Json {
    let Json::Obj(fields) = json else {
        panic!("object")
    };
    fields.get_mut(name).unwrap()
}
fn first_node(json: &mut Json) -> &mut Json {
    let Json::Arr(nodes) = field_mut(json, "nodes") else {
        panic!("nodes")
    };
    &mut nodes[0]
}
fn typed_node<'a>(json: &'a mut Json, ty: &str) -> &'a mut Json {
    let Json::Arr(nodes) = field_mut(json, "nodes") else {
        panic!("nodes")
    };
    nodes
        .iter_mut()
        .find(|node| match node {
            Json::Obj(fields) => matches!(fields.get("type"),Some(Json::Str(name)) if name==ty),
            _ => false,
        })
        .unwrap()
}

#[test]
fn valid_reuse_recomputes_current_values_with_exact_counts() {
    let dir = setup("valid-reuse");
    let previous = execute(&dir, "previous", None, &ASKS);
    let plain = checked(&dir, &previous, 0, false);
    let bytes = std::fs::read(dir.join("previous/result.json")).unwrap();
    let reused = execute(&dir, "out", Some("previous"), &ASKS);
    let result = checked(&dir, &reused, 0, true);
    assert_eq!(value(&result), "2");
    assert!(arr(get(get(&result, "reuse"), "rejected")).is_empty());
    for field in [
        "requests",
        "answers",
        "nodes",
        "inputs",
        "declarations",
        "vocabularies",
    ] {
        assert_eq!(get(&plain, field), get(&result, field), "{field}");
    }
    assert_eq!(
        std::fs::read(dir.join("previous/result.json")).unwrap(),
        bytes
    );
    // Natは綴りでなく値を検査する。整数を表す小数/指数のmetadataも同じ値である。
    let notation = String::from_utf8(bytes)
        .unwrap()
        .replace("\"accepted_nodes\":0", "\"accepted_nodes\":0e0")
        .replace("\"exit_code\":0", "\"exit_code\":0.0");
    std::fs::write(dir.join("previous/result.json"), notation).unwrap();
    let notation_run = execute(&dir, "out-notation", Some("previous"), &ASKS);
    let notation_result = checked(&dir, &notation_run, 0, true);
    assert_eq!(value(&notation_result), "2");
    assert!(arr(get(get(&notation_result, "reuse"), "rejected")).is_empty());
}

#[test]
fn duplicate_verified_derivation_does_not_require_the_same_plan_or_node_count() {
    let dir = setup("reuse-unshared-derivation");
    let previous = execute(&dir, "previous", None, &ASKS);
    let source = result_json(&dir, &previous);
    let mut candidate = owned(&source);
    let Json::Arr(nodes) = field_mut(&mut candidate, "nodes") else {
        panic!("nodes")
    };
    let original_len = nodes.len();
    let mut duplicate = nodes.last().unwrap().clone();
    *field_mut(&mut duplicate, "id") = Json::str(format!("n{original_len}"));
    nodes.push(duplicate);
    *field_mut(field_mut(&mut candidate, "reuse"), "recomputed_nodes") =
        Json::Nat((original_len + 1) as u64);
    std::fs::write(dir.join("previous/result.json"), candidate.canonical()).unwrap();
    let reused = execute(&dir, "out", Some("previous"), &ASKS);
    let result = checked(&dir, &reused, 0, true);
    assert_eq!(value(&result), "2");
    assert!(arr(get(get(&result, "reuse"), "rejected")).is_empty());
    assert_eq!(arr(get(&result, "nodes")).len(), original_len);
}

#[test]
fn missing_observations_remain_partial_with_a_valid_partial_candidate() {
    let dir = setup("reuse-partial");
    let missing = A.replace("{\"id\": \"count\", \"subject\": \"s\", \"field\": \"Counter.State.count\", \"value\": \"2\", \"origin\": \"model\"}", "");
    std::fs::write(dir.join("a.json"), missing).unwrap();
    let previous = execute(&dir, "previous", None, &ASKS);
    let plain = checked(&dir, &previous, 2, false);
    let reused = execute(&dir, "out", Some("previous"), &ASKS);
    let result = checked(&dir, &reused, 2, true);
    assert!(arr(get(get(&result, "reuse"), "rejected")).is_empty());
    for name in ["answers", "nodes", "issues"] {
        assert_eq!(get(&plain, name), get(&result, name));
    }
    assert!(
        arr(get(&result, "answers"))
            .iter()
            .all(|a| s(get(a, "status")) == "undetermined")
    );
}

#[test]
fn invalid_candidate_versions_types_dag_and_json_are_rejected_without_failure() {
    let dir = setup("invalid-reuse");
    let previous = execute(&dir, "previous", None, &ASKS);
    let source = result_json(&dir, &previous);
    for kind in [
        "version",
        "unknown_type",
        "wrong_payload",
        "forward",
        "duplicate_id",
        "unknown_field",
        "null",
        "syntax",
        "duplicate_key",
        "command_check",
        "nat_accepted",
        "nat_recomputed",
        "nat_huge",
        "Evaluation",
        "Evidence",
        "Expression",
        "LawInstance",
        "Proposition",
        "Domain",
        "judgment",
        "rule",
        "scope",
        "support",
        "reasons",
        "rule_extra",
        "inputs",
        "requests",
        "declarations",
        "vocabularies",
        "issues",
        "ref_type",
    ] {
        let mut candidate = owned(&source);
        let bytes = match kind {
            "syntax" => b"{".to_vec(),
            "duplicate_key" => {
                b"{\"format\":\"archsig.result/2\",\"format\":\"archsig.result/2\"}".to_vec()
            }
            "nat_huge" => owned(&source)
                .canonical()
                .replace(
                    "\"accepted_nodes\":0",
                    &format!("\"accepted_nodes\":1{}", "0".repeat(100)),
                )
                .into_bytes(),
            _ => {
                match kind {
                    "command_check" => {
                        *field_mut(&mut candidate, "command") = Json::str("check");
                    }
                    "nat_accepted" | "nat_recomputed" => {
                        let name = if kind == "nat_accepted" {
                            "accepted_nodes"
                        } else {
                            "recomputed_nodes"
                        };
                        *field_mut(field_mut(&mut candidate, "reuse"), name) =
                            Json::Nat(9_007_199_254_740_992);
                    }
                    "version" => {
                        *field_mut(&mut candidate, "format") = Json::str("archsig.result/999")
                    }
                    "unknown_type" => {
                        *field_mut(first_node(&mut candidate), "type") = Json::str("Invented")
                    }
                    "wrong_payload" => {
                        *field_mut(first_node(&mut candidate), "type") = Json::str("Bool")
                    }
                    "forward" => {
                        *field_mut(first_node(&mut candidate), "arguments") =
                            Json::Arr(vec![Json::obj([("node", Json::str("future"))])])
                    }
                    "duplicate_id" => {
                        let Json::Arr(nodes) = field_mut(&mut candidate, "nodes") else {
                            panic!("nodes")
                        };
                        let id = field_mut(&mut nodes[0], "id").clone();
                        *field_mut(&mut nodes[1], "id") = id;
                    }
                    "unknown_field" => {
                        let Json::Obj(fields) = &mut candidate else {
                            panic!("object")
                        };
                        fields.insert("extra".into(), Json::Bool(true));
                    }
                    "Evaluation" | "Evidence" | "Expression" | "LawInstance" | "Proposition"
                    | "Domain" => {
                        *field_mut(typed_node(&mut candidate, kind), "value") = Json::obj([]);
                    }
                    "judgment" => {
                        let Json::Obj(fields) = typed_node(&mut candidate, "Proposition") else {
                            panic!("node")
                        };
                        fields.remove("judgment");
                    }
                    "rule" | "scope" => {
                        *field_mut(first_node(&mut candidate), kind) = Json::obj([])
                    }
                    "support" => {
                        *field_mut(first_node(&mut candidate), kind) =
                            Json::Arr(vec![Json::Bool(true)])
                    }
                    "reasons" => {
                        *field_mut(first_node(&mut candidate), kind) =
                            Json::Arr(vec![Json::obj([("code", Json::str("made_up"))])])
                    }
                    "rule_extra" => {
                        let Json::Obj(fields) = field_mut(first_node(&mut candidate), "rule")
                        else {
                            panic!("rule")
                        };
                        fields.insert("extra".into(), Json::Bool(true));
                    }
                    "inputs" | "requests" | "declarations" | "vocabularies" | "issues" => {
                        *field_mut(&mut candidate, kind) = Json::Arr(vec![Json::Bool(true)])
                    }
                    "ref_type" => {
                        let node = typed_node(&mut candidate, "Z");
                        *field_mut(node, "type") = Json::str("Bool");
                        *field_mut(node, "value") = Json::Bool(true);
                    }
                    "null" => {}
                    _ => unreachable!(),
                }
                let text = candidate.canonical();
                if kind == "null" {
                    text.replacen("\"command\":\"run\"", "\"command\":null", 1)
                        .into_bytes()
                } else {
                    text.into_bytes()
                }
            }
        };
        let name = format!("candidate-{kind}");
        std::fs::create_dir(dir.join(&name)).unwrap();
        std::fs::write(dir.join(&name).join("result.json"), &bytes).unwrap();
        let out = format!("out-{kind}");
        let run = execute(&dir, &out, Some(&name), &ASKS);
        let result = checked(&dir, &run, 0, true);
        assert_eq!(value(&result), "2");
        let rejected = arr(get(get(&result, "reuse"), "rejected"));
        assert!(!rejected.is_empty(), "{kind}");
        assert_eq!(s(get(get(&rejected[0], "details"), "argument")), "--reuse");
        assert!(!s(get(&rejected[0], "message")).is_empty());
        assert_eq!(
            std::fs::read(dir.join(&name).join("result.json")).unwrap(),
            bytes
        );
    }
}

#[test]
fn reuse_never_imports_old_values_bindings_laws_or_provenance() {
    let dir = setup("changed-reuse");
    let previous = execute(&dir, "previous", None, &ASKS);
    checked(&dir, &previous, 0, false);
    std::fs::write(
        dir.join("a.json"),
        A.replace("\"value\": \"2\"", "\"value\": \"12\"")
            .replace("\"model\"", "\"changed-source\""),
    )
    .unwrap();
    let run = execute(&dir, "changed", Some("previous"), &ASKS);
    let result = checked(&dir, &run, 1, true);
    assert_eq!(value(&result), "12");
    let current_bytes = std::fs::read(dir.join("a.json")).unwrap();
    let identity = arr(get(&result, "inputs"))
        .iter()
        .find(|i| s(get(i, "id")) == "archmap")
        .unwrap();
    assert_eq!(
        s(get(identity, "bytes_digest")),
        archsig::canonical::sha256_digest(&current_bytes)
    );
    assert_eq!(
        s(get(&arr(get(&result, "answers"))[1], "status")),
        "refuted"
    );
    assert_eq!(
        std::fs::read(dir.join("changed/inputs/archmap.json")).unwrap(),
        std::fs::read(dir.join("a.json")).unwrap()
    );
    std::fs::write(dir.join("l.law"), L.replace("<= 10", "<= 20")).unwrap();
    let run = execute(&dir, "law-changed", Some("previous"), &ASKS);
    let result = checked(&dir, &run, 0, true);
    assert_eq!(value(&result), "12");
    assert_eq!(
        s(get(&arr(get(&result, "answers"))[1], "status")),
        "established"
    );
    let renamed = A
        .replace("\"id\": \"s\"", "\"id\": \"t\"")
        .replace("\"subject\": \"s\"", "\"subject\": \"t\"");
    std::fs::write(dir.join("a.json"), renamed).unwrap();
    let asks = ["n=evaluate(CountCheck.amount,s=@v/t)"];
    let run = execute(&dir, "binding-changed", Some("previous"), &asks);
    let result = checked(&dir, &run, 0, true);
    assert_eq!(value(&result), "2");
    assert!(
        arr(get(&result, "nodes"))
            .iter()
            .flat_map(|n| arr(get(n, "support")))
            .all(|p| s(get(p, "subject")) == "t")
    );
}

#[test]
fn unavailable_and_linked_candidates_do_not_change_inputs_or_outputs() {
    let dir = setup("unavailable-reuse");
    std::fs::write(dir.join("not-directory"), b"sentinel").unwrap();
    std::fs::create_dir(dir.join("empty")).unwrap();
    for (index, candidate) in ["missing", "not-directory", "empty"].iter().enumerate() {
        let r = execute(&dir, &format!("out-{index}"), Some(candidate), &ASKS);
        let result = checked(&dir, &r, 0, true);
        assert!(!arr(get(get(&result, "reuse"), "rejected")).is_empty());
        assert_eq!(value(&result), "2");
    }
    #[cfg(unix)]
    {
        let prior = execute(&dir, "previous", None, &ASKS);
        checked(&dir, &prior, 0, false);
        std::os::unix::fs::symlink("previous", dir.join("linked-dir")).unwrap();
        std::fs::create_dir(dir.join("linked-file")).unwrap();
        std::os::unix::fs::symlink(
            "../previous/result.json",
            dir.join("linked-file/result.json"),
        )
        .unwrap();
        for (index, candidate) in [
            "linked-dir",
            "linked-dir/",
            "linked-dir/.",
            "linked-dir/./",
            "linked-file",
        ]
        .iter()
        .enumerate()
        {
            let r = execute(&dir, &format!("out-linked-{index}"), Some(candidate), &ASKS);
            let result = checked(&dir, &r, 0, true);
            assert!(!arr(get(get(&result, "reuse"), "rejected")).is_empty());
        }
    }
    assert_eq!(
        std::fs::read(dir.join("not-directory")).unwrap(),
        b"sentinel"
    );
    std::fs::write(dir.join("d.json"), b"{").unwrap();
    let r = execute(&dir, "invalid-input", Some("missing"), &ASKS);
    assert_eq!(r.code, 65);
    assert!(!has(&r.receipt, "result"));
    assert!(!dir.join("invalid-input").exists());
    assert!(
        arr(get(&r.receipt, "issues"))
            .iter()
            .all(|i| s(get(i, "code")) != "usage")
    );
}
