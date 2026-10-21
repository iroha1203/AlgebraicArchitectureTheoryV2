//! 原始候補・総作用・部分結果を実バイナリから検査する独立fixture。
mod common;
use archsig::json::JNode;
use common::cli::*;
use std::path::{Path, PathBuf};
const D: &[u8] = include_bytes!("fixtures/reservations.atoms.json");
const L: &[u8] = include_bytes!("fixtures/reservations.law");
const A: &str = include_str!("fixtures/reservations.archmap.json");
const ASK: &str = "m=map(Reservations.Migration,on=@v/m,reading=Reservations)";
fn inputs(name: &str, map: &str) -> PathBuf {
    let dir = workdir(name);
    for (name, bytes) in [("d.json", D), ("l.law", L), ("a.json", map.as_bytes())] {
        std::fs::write(dir.join(name), bytes).unwrap();
    }
    dir
}
fn asks(dir: &Path, requests: &[&str]) -> Run {
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
    for request in requests {
        args.extend(["--ask", request]);
    }
    run(dir, &args)
}
fn node<'a>(result: &'a JNode, r: &JNode) -> &'a JNode {
    arr(get(result, "nodes"))
        .iter()
        .find(|n| s(get(n, "id")) == s(get(r, "node")))
        .unwrap()
}
fn value<'a>(result: &'a JNode, r: &JNode) -> &'a JNode {
    get(node(result, r), "value")
}
fn answer<'a>(result: &'a JNode, id: &str) -> &'a JNode {
    arr(get(result, "answers"))
        .iter()
        .find(|a| s(get(a, "id")) == id)
        .unwrap()
}
fn saved(dir: &Path, run: &Run, status: &str, code: i32) -> JNode {
    assert_eq!(run.code, code, "{}", run.stdout);
    assert_eq!(s(get(&run.receipt, "status")), status);
    let result = result_json(dir, run);
    assert_eq!(s(get(&result, "status")), status);
    assert_eq!(num(get(&result, "exit_code")), code as u64);
    result
}
#[test]
fn configuration_map_exports_complete_architectures_total_action_and_confirmed_operation() {
    let dir = inputs("map-success", A);
    let run = asks(&dir, &[ASK]);
    let result = saved(&dir, &run, "complete", 0);
    let a = answer(&result, "m");
    assert_eq!(s(get(a, "status")), "established");
    let outputs = get(a, "outputs");
    let candidate = value(&result, get(outputs, "candidate"));
    assert_eq!(s(get(candidate, "declaration")), "Reservations.Migration");
    for (key, root, arrow) in [("source", "A", "e"), ("target", "B", "f")] {
        let architecture = value(&result, get(candidate, key));
        assert_eq!(s(get(architecture, "reading")), "Reservations");
        assert_eq!(s(&arr(value(&result, get(architecture, "root")))[1]), root);
        let laws = arr(get(architecture, "laws"));
        assert_eq!(laws.len(), 1);
        let law = value(&result, &laws[0]);
        assert_eq!(s(get(law, "name")), "Reservations.conserved");
        assert_eq!(s(get(law, "role")), "required");
        assert_eq!(arr(get(law, "bindings")).len(), 1);
        let body = value(&result, get(law, "body"));
        assert_eq!(s(get(body, "kind")), "source");
        assert!(has(body, "location"));
        assert!(has(law, "occurrence"));
        let arrows = arr(get(architecture, "internal_arrows"));
        assert_eq!(arrows.len(), 1);
        assert_eq!(s(&arr(value(&result, &arrows[0]))[1]), arrow);
        assert!(arr(get(architecture, "overrides")).is_empty());
        let config = value(&result, get(architecture, "configuration"));
        assert_eq!(arr(get(config, "family")).len(), 13);
        assert_eq!(arr(get(config, "requirements")).len(), 9);
        assert_eq!(arr(get(config, "relations")).len(), 14);
        assert_eq!(arr(get(config, "identifications")).len(), 13);
    }
    let action = value(&result, get(candidate, "action"));
    let universe = arr(get(value(&result, get(action, "universe")), "atoms"));
    let images = arr(get(action, "images"));
    assert_eq!(universe.len(), 31);
    assert_eq!(images.len(), 31);
    for (atom, image) in universe.iter().zip(images) {
        let source = s(get(atom, "subject"));
        let expected = match source {
            "A" => "B",
            "p" => "r",
            "q" => "s",
            "e" => "f",
            _ => "B",
        };
        assert_eq!(s(get(image, "subject")), expected);
        assert_eq!(s(get(image, "snapshot")), "v");
        if matches!(source, "p" | "q" | "e") && has(atom, "field") {
            assert_eq!(s(get(image, "field")), s(get(atom, "field")));
        } else if !matches!(source, "A" | "p" | "q" | "e") {
            assert!(!has(image, "field"));
        }
    }
    let map = value(&result, get(outputs, "map"));
    assert_eq!(
        s(get(get(map, "candidate"), "node")),
        s(get(get(outputs, "candidate"), "node"))
    );
    let operation = value(&result, get(outputs, "operation"));
    assert_eq!(arr(get(operation, "word")).len(), 1);
    assert_eq!(
        s(&arr(value(&result, &arr(get(operation, "word"))[0]))[1]),
        "m"
    );
    let arguments = arr(get(&arr(get(&result, "requests"))[0], "arguments"));
    for name in ["kind", "to_reading"] {
        let arg = arguments
            .iter()
            .find(|a| s(get(a, "name")) == name)
            .unwrap();
        assert_eq!(s(get(arg, "origin")), "defaulted");
    }
    assert_eq!(
        std::fs::read(dir.join("out/inputs/archmap.json")).unwrap(),
        A.as_bytes()
    );
    std::fs::remove_dir_all(dir).unwrap();
}
fn bad_endpoints() -> String {
    A.lines()
        .map(|line| {
            if line.contains("\"id\": \"m-states\"") {
                line.replace("[\"v\", \"r\"]", "[\"v\", \"temp\"]")
                    .replace("[\"v\", \"s\"]", "[\"v\", \"r\"]")
                    .replace("[\"v\", \"temp\"]", "[\"v\", \"s\"]")
            } else {
                line.into()
            }
        })
        .collect::<Vec<_>>()
        .join("\n")
}
fn remove(map: &str, id: &str) -> String {
    map.lines()
        .filter(|line| !line.contains(&format!("\"id\": \"{id}\"")))
        .collect::<Vec<_>>()
        .join("\n")
        .replace(",\n    ]", "\n    ]")
}
#[test]
fn endpoint_refutation_keeps_candidate_and_concrete_facts_without_map_or_operation() {
    let dir = inputs("map-refutation", &bad_endpoints());
    let run = asks(&dir, &[ASK]);
    let result = saved(&dir, &run, "complete", 1);
    let a = answer(&result, "m");
    assert_eq!(s(get(a, "status")), "refuted");
    let outputs = get(a, "outputs");
    assert!(has(outputs, "candidate"));
    assert!(!has(outputs, "map"));
    assert!(!has(outputs, "operation"));
    let claim = node(&result, get(outputs, "proposition"));
    assert_eq!(s(get(get(claim, "judgment"), "status")), "refuted");
    let evidence = arr(get(a, "evidence"));
    assert!(!evidence.is_empty());
    let mut facts = vec![];
    for e in evidence {
        let e = value(&result, e);
        assert_eq!(s(get(e, "kind")), "counterexample");
        for f in arr(get(get(e, "data"), "facts")) {
            if has(f, "field") {
                facts.push((
                    s(get(f, "subject")).to_string(),
                    s(get(f, "field")).to_string(),
                ));
            }
        }
    }
    assert!(facts.contains(&("e".into(), "Reservations.Reserve.from".into())));
    assert!(facts.contains(&("f".into(), "Reservations.Reserve.from".into())));
    std::fs::remove_dir_all(dir).unwrap();
}
#[test]
fn missing_table_keeps_independent_endpoint_refutation_and_needed_slots() {
    let dir = inputs(
        "map-missing-refutation",
        &remove(&bad_endpoints(), "m-reserves"),
    );
    let run = asks(&dir, &["plan=needed($m)", ASK]);
    let result = saved(&dir, &run, "partial", 2);
    let a = answer(&result, "m");
    assert_eq!(s(get(a, "status")), "undetermined");
    let outputs = get(a, "outputs");
    assert!(!has(outputs, "map"));
    assert!(!has(outputs, "operation"));
    let candidate = node(&result, get(outputs, "candidate"));
    assert_eq!(s(get(candidate, "state")), "blocked");
    assert!(!has(candidate, "value"));
    assert!(has(candidate, "partial"));
    let evidence = arr(get(a, "evidence"));
    assert_eq!(evidence.len(), 1);
    assert_eq!(
        s(get(get(node(&result, &evidence[0]), "scope"), "domain")),
        "all_completions"
    );
    let facts = arr(get(get(value(&result, &evidence[0]), "data"), "facts"));
    assert!(
        facts
            .iter()
            .any(|f| has(f, "field") && s(get(f, "field")) == "Reservations.Reserve.from")
    );
    let reasons = arr(get(a, "reasons"));
    assert!(reasons.iter().any(|r| {
        s(get(r, "code")) == "missing_observation"
            && arr(get(r, "missing"))
                .iter()
                .any(|f| s(get(f, "field")) == "Reservations.Migration.reserves")
    }));
    let plan = value(
        &result,
        get(get(answer(&result, "plan"), "outputs"), "plan"),
    );
    assert!(format!("{plan:?}").contains("Reservations.Migration.reserves"));
    assert_eq!(s(get(&arr(get(&result, "answers"))[0], "id")), "plan");
    std::fs::remove_dir_all(dir).unwrap();
}
#[test]
fn map_projection_binds_the_existing_subject_and_keeps_original_answer_order() {
    let dir = inputs("map-dependency", A);
    let run = asks(
        &dir,
        &[
            "copy=map(Reservations.Migration,on=$m.operation.word[0],reading=Reservations)",
            "audit=check(Reservations.retained,m=$m.candidate.subject)",
            "holdings=evaluate(Reservations.holdings,s=@v/p)",
            ASK,
        ],
    );
    let result = saved(&dir, &run, "complete", 1);
    assert_eq!(s(get(answer(&result, "copy"), "status")), "established");
    assert_eq!(s(get(answer(&result, "audit"), "status")), "refuted");
    let expected = ["copy", "audit", "holdings", "m"];
    assert_eq!(
        arr(get(&result, "answers"))
            .iter()
            .map(|a| s(get(a, "id")))
            .collect::<Vec<_>>(),
        expected
    );
    let universes = arr(get(&result, "nodes"))
        .iter()
        .filter(
            |n| matches!(&get(n,"type").value,archsig::json::JValue::Str(t) if t=="AtomUniverse"),
        )
        .count();
    assert_eq!(universes, 1);
    std::fs::remove_dir_all(dir).unwrap();
}
#[test]
fn unavailable_map_operation_blocks_consumers_and_preserves_producer_reasons() {
    let dir = inputs("map-blocked", &remove(A, "m-states"));
    let run = asks(
        &dir,
        &[
            "copy=map(Reservations.Migration,on=$m.operation.word[0],reading=Reservations)",
            "audit=check(Reservations.retained,m=$m.candidate.subject)",
            ASK,
        ],
    );
    let result = saved(&dir, &run, "partial", 2);
    for id in ["copy", "audit"] {
        let a = answer(&result, id);
        assert_eq!(s(get(a, "status")), "undetermined");
        let reasons = arr(get(a, "reasons"));
        assert!(
            reasons
                .iter()
                .any(|r| s(get(r, "code")) == "dependency_blocked")
        );
        assert!(
            reasons
                .iter()
                .any(|r| s(get(r, "code")) == "missing_observation" && s(get(r, "request")) == "m")
        );
    }
    std::fs::remove_dir_all(dir).unwrap();
}
#[test]
fn map_keeps_distinct_readings_and_unbound_law_parameter_domains() {
    let dir = inputs("map-readings", A);
    std::fs::write(
        dir.join("l.law"),
        include_bytes!("fixtures/public-map-readings.law"),
    )
    .unwrap();
    let run = asks(
        &dir,
        &[
            "m=map(Reservations.Migration,on=@v/m,reading=SourceReading,to_reading=TargetReading,kind=configuration)",
        ],
    );
    let result = saved(&dir, &run, "complete", 0);
    let candidate = value(
        &result,
        get(get(answer(&result, "m"), "outputs"), "candidate"),
    );
    let source = value(&result, get(candidate, "source"));
    let target = value(&result, get(candidate, "target"));
    assert_eq!(s(get(source, "reading")), "SourceReading");
    assert_eq!(s(get(target, "reading")), "TargetReading");
    assert_eq!(arr(get(source, "laws")).len(), 1);
    assert_eq!(arr(get(target, "laws")).len(), 2);
    for law in arr(get(target, "laws")) {
        let law = value(&result, law);
        assert_eq!(s(get(law, "name")), "TargetReading.lower");
        assert_eq!(s(get(law, "role")), "optional");
        let body = value(&result, get(law, "body"));
        let parameters = arr(get(body, "parameters"));
        assert_eq!(parameters.len(), 1);
        assert_eq!(s(get(&parameters[0], "name")), "n");
        assert_eq!(s(get(&parameters[0], "type")), "Z");
    }
    let request = &arr(get(&result, "requests"))[0];
    for name in ["kind", "to_reading"] {
        assert_eq!(
            s(get(
                arr(get(request, "arguments"))
                    .iter()
                    .find(|a| s(get(a, "name")) == name)
                    .unwrap(),
                "origin"
            )),
            "explicit"
        );
    }
    std::fs::remove_dir_all(dir).unwrap();
}
#[test]
fn unknown_owner_retains_conditional_laws_as_blocked_partial_records() {
    let dir = inputs("map-conditional-law", &remove(A, "p-owner"));
    std::fs::write(
        dir.join("l.law"),
        include_bytes!("fixtures/public-map-conditional.law"),
    )
    .unwrap();
    let run = asks(&dir, &[ASK]);
    let result = saved(&dir, &run, "partial", 2);
    let nodes = arr(get(&result, "nodes"));
    let conditional = nodes
        .iter()
        .filter(|n| {
            matches!(&get(n,"type").value,archsig::json::JValue::Str(t) if t=="LawInstance")
                && s(get(n, "state")) == "blocked"
        })
        .collect::<Vec<_>>();
    assert!(!conditional.is_empty());
    for law in conditional {
        assert!(!has(law, "value"));
        assert!(has(law, "partial"));
        assert!(arr(get(law, "reasons")).iter().any(|r| {
            arr(get(r, "missing"))
                .iter()
                .any(|f| s(get(f, "field")) == "Reservations.State.owner")
        }));
    }
    let a = answer(&result, "m");
    assert!(!has(get(a, "outputs"), "operation"));
    assert!(!has(get(a, "outputs"), "map"));
    let candidate = node(&result, get(get(a, "outputs"), "candidate"));
    assert_eq!(s(get(candidate, "state")), "blocked");
    std::fs::remove_dir_all(dir).unwrap();
}
#[test]
fn invalid_map_selectors_and_private_projections_fail_as_concrete_usage_errors() {
    for (i, ask) in [
        "bad=map(Reservations.Migration,on=@v/m)",
        "bad=map(Reservations.Migration,on=@v/m,reading=Unknown)",
        "bad=map(Reservations.Migration,on=@v/m,reading=Reservations,to_reading=Unknown)",
        "bad=map(Reservations.Migration,on=@v/m,reading=Reservations,kind=other)",
        "bad=map(Reservations.Migration,on=@v/p,reading=Reservations)",
        "bad=map(Reservations.Migration,on=Reservations.Migration,reading=Reservations)",
        "bad=map(Reservations.Migration,on=@v/m,reading=Reservations,extra=configuration)",
        "bad=map(Reservations.Migration,on=@v/m,on=@v/m,reading=Reservations)",
        "bad=map(Unknown,on=@v/m,reading=Reservations)",
        "bad=map(Reservations.State,on=@v/p,reading=Reservations)",
        "bad=map(Reservations.Migration,on=$m.candidate.support,reading=Reservations)",
        "bad=map(Reservations.Migration,on=$m.operation.word[1],reading=Reservations)",
        "bad=check(Reservations.retained,m=$m.candidate)",
    ]
    .iter()
    .enumerate()
    {
        let dir = inputs(&format!("map-usage-{i}"), A);
        let r = asks(&dir, &[ask, ASK]);
        let receipt = notified(&dir, &r, "invalid", 64);
        assert!(
            arr(get(&receipt, "issues"))
                .iter()
                .all(|issue| s(get(issue, "code")) == "usage")
        );
        assert!(!dir.join("out").exists());
        std::fs::remove_dir_all(dir).unwrap();
    }
}
#[test]
fn valid_object_algebra_kind_reports_internal_unimplemented_instead_of_math_uncertainty() {
    let dir = inputs("map-unimplemented-kind", A);
    let r = asks(
        &dir,
        &["m=map(Reservations.Migration,on=@v/m,reading=Reservations,kind=object_algebra)"],
    );
    let receipt = notified(&dir, &r, "error", 70);
    assert!(
        arr(get(&receipt, "issues"))
            .iter()
            .all(|i| s(get(i, "code")) == "internal")
    );
    assert!(!dir.join("out").exists());
    std::fs::remove_dir_all(dir).unwrap();
}
#[test]
fn map_reuse_rechecks_the_total_action_and_rejects_a_forged_saved_operation() {
    let dir = inputs("map-reuse", A);
    let first = asks(&dir, &[ASK]);
    let original = saved(&dir, &first, "complete", 0);
    let command = |out: &str| {
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
                out,
                "--reuse",
                "out",
                "--ask",
                ASK,
            ],
        )
    };
    let second = command("second");
    let result = saved(&dir, &second, "complete", 0);
    assert!(arr(get(get(&result, "reuse"), "rejected")).is_empty());
    let output = get(answer(&original, "m"), "outputs");
    let operation_id = s(get(get(output, "operation"), "node"));
    let mut forged = std::fs::read_to_string(dir.join("out/result.json")).unwrap();
    let node_text = archsig::canonical::Json::str(operation_id).canonical();
    let old_word = format!(
        "\"word\":[{{\"node\":{}}}]",
        archsig::canonical::Json::str(s(get(
            &arr(get(value(&original, get(output, "operation")), "word"))[0],
            "node"
        )))
        .canonical()
    );
    assert!(forged.contains(&old_word));
    assert!(forged.contains(&node_text));
    forged = forged.replace(&old_word, "\"word\":[]");
    std::fs::write(dir.join("out/result.json"), forged).unwrap();
    let third = command("third");
    let result = saved(&dir, &third, "complete", 0);
    assert!(!arr(get(get(&result, "reuse"), "rejected")).is_empty());
    let operation = value(
        &result,
        get(get(answer(&result, "m"), "outputs"), "operation"),
    );
    assert_eq!(arr(get(operation, "word")).len(), 1);
    assert_eq!(num(get(get(&result, "reuse"), "accepted_nodes")), 0);
    std::fs::remove_dir_all(dir).unwrap();
}
#[test]
fn refuted_candidate_remains_consumable_while_its_missing_operation_blocks_only_that_dependency() {
    let dir = inputs("map-refuted-dependencies", &bad_endpoints());
    let r = asks(
        &dir,
        &[
            "again=map(Reservations.Migration,on=$m.candidate.subject,reading=Reservations)",
            "blocked=map(Reservations.Migration,on=$m.operation.word[0],reading=Reservations)",
            ASK,
        ],
    );
    let result = saved(&dir, &r, "partial", 2);
    for id in ["m", "again"] {
        let a = answer(&result, id);
        assert_eq!(s(get(a, "status")), "refuted");
        assert!(!arr(get(a, "evidence")).is_empty());
    }
    let blocked = answer(&result, "blocked");
    assert_eq!(s(get(blocked, "status")), "undetermined");
    assert!(!has(get(blocked, "outputs"), "candidate"));
    assert!(
        arr(get(blocked, "reasons"))
            .iter()
            .any(|r| s(get(r, "code")) == "dependency_blocked")
    );
    assert!(
        !arr(get(blocked, "reasons"))
            .iter()
            .any(|r| s(get(r, "code")) == "unsupported_algorithm"
                || s(get(r, "code")) == "missing_observation")
    );
    std::fs::remove_dir_all(dir).unwrap();
}
#[test]
fn map_and_architecture_projections_select_existing_typed_refs_through_nested_records() {
    let dir = inputs("map-nested-projections", A);
    std::fs::write(
        dir.join("l.law"),
        include_bytes!("fixtures/public-map-readings.law"),
    )
    .unwrap();
    let r = asks(
        &dir,
        &[
            "source=evaluate(SourceReading.root_id,a=$m.map.candidate.source.root)",
            "target=evaluate(SourceReading.root_id,a=$m.operation.target.root)",
            "copy=map(Reservations.Migration,on=$m.operation.configuration_map.candidate.subject,reading=SourceReading,to_reading=TargetReading)",
            "m=map(Reservations.Migration,on=@v/m,reading=SourceReading,to_reading=TargetReading)",
        ],
    );
    let result = saved(&dir, &r, "complete", 0);
    for (id, expected) in [("source", "A"), ("target", "B")] {
        let output = get(answer(&result, id), "outputs");
        assert_eq!(s(&arr(value(&result, get(output, "value")))[1]), expected);
        let candidate = value(
            &result,
            get(get(answer(&result, "m"), "outputs"), "candidate"),
        );
        let architecture = value(&result, get(candidate, id));
        assert_eq!(
            s(get(get(output, "value"), "node")),
            s(get(get(architecture, "root"), "node"))
        );
    }
    assert_eq!(s(get(answer(&result, "copy"), "status")), "established");
    std::fs::remove_dir_all(dir).unwrap();
}
#[test]
fn map_dependency_cycles_report_edges_without_calculating_or_writing_results() {
    let dir = inputs("map-cycles", A);
    let r = asks(
        &dir,
        &[
            "a=map(Reservations.Migration,on=$b.candidate.subject,reading=Reservations)",
            "b=map(Reservations.Migration,on=$a.map.candidate.subject,reading=Reservations)",
        ],
    );
    let receipt = notified(&dir, &r, "invalid", 64);
    let issues = arr(get(&receipt, "issues"));
    assert_eq!(issues.len(), 2);
    for issue in issues {
        assert_eq!(s(get(issue, "code")), "cycle");
        let id = s(get(issue, "request"));
        let other = if id == "a" {
            "b"
        } else {
            assert_eq!(id, "b");
            "a"
        };
        let message = s(get(issue, "message"));
        assert!(
            message.contains("a")
                && message.contains("b")
                && message.contains(&format!("{id} -> {other}"))
        );
        assert!(!has(issue, "location"));
        assert!(
            matches!(&get(issue,"details").value,archsig::json::JValue::Obj(fields) if fields.is_empty())
        );
    }
    assert!(!dir.join("out").exists());
    std::fs::remove_dir_all(dir).unwrap();
}
#[test]
fn architecture_scope_retains_the_owner_fact_used_to_exclude_another_roots_subject() {
    let dir = inputs("map-classification-scope", A);
    let r = asks(&dir, &[ASK]);
    let result = saved(&dir, &r, "complete", 0);
    let candidate = value(
        &result,
        get(get(answer(&result, "m"), "outputs"), "candidate"),
    );
    let architecture = node(&result, get(candidate, "source"));
    let modes = arr(get(get(architecture, "scope"), "modes"))
        .iter()
        .map(s)
        .collect::<Vec<_>>();
    assert_eq!(modes, ["specification"]);
    let support = arr(get(architecture, "support"));
    assert!(support.iter().any(|f| has(f, "field")
        && s(get(f, "subject")) == "r"
        && s(get(f, "field")) == "Reservations.State.owner"));
    assert!(!support.iter().any(|f| has(f, "field")
        && s(get(f, "subject")) == "r"
        && s(get(f, "field")) == "Reservations.State.free"));
    std::fs::remove_dir_all(dir).unwrap();
}
