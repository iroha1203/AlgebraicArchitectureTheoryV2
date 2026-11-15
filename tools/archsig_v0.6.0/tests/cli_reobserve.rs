use crate::common::cli::*;
use archsig_common::{control::Control, json::parse};
use archsig_computation::observed::{
    assembly_reobservation::{
        AssemblyCandidateAlignment, MultiAssemblyAlignment, reevaluate_assembly_many,
    },
    evaluate_observed_bytes, prepare_observed,
};
use archsig_input::input::InputSources;
use std::path::Path;

const DEFINITIONS: &[u8] = include_bytes!("fixtures/r2-assembly-reobservation/definitions.json");
const LAW: &[u8] = include_bytes!("fixtures/r2-assembly-reobservation/laws.law");
const BEFORE: &[u8] = include_bytes!("fixtures/r2-assembly-reobservation/before.json");
const AFTER: &[u8] = include_bytes!("fixtures/r2-assembly-reobservation/after.json");
const QUERIES: &str = include_str!("fixtures/r2-assembly-reobservation/queries.txt");
const SUBJECTS: &[(&str, &str)] = &[
    ("A", "A"),
    ("B", "B"),
    ("G", "G"),
    ("a", "a"),
    ("b", "b"),
    ("ma", "ma"),
    ("mb", "mb"),
];

fn source(map: &[u8]) -> InputSources {
    InputSources::from_bytes(vec![DEFINITIONS.to_vec()], LAW.to_vec(), map.to_vec())
}

fn inputs(
    dir: &Path,
    previous: &[u8],
    before_snapshot: &str,
    current: &[u8],
    after_snapshot: &str,
) {
    let alignment = format!(
        r#"{{
        "before_snapshot":"{before_snapshot}","after_snapshot":"{after_snapshot}","reading":"Assembly","assembly":"joined",
        "subjects":[["A","A"],["B","B"],["G","G"],["a","a"],["b","b"],["ma","ma"],["mb","mb"]],
        "candidates":[{{"participant":"a","previous_candidate":"pick","current_solve":"solveIt"}}]
    }}"#
    );
    for (name, bytes) in [
        ("d.json", DEFINITIONS),
        ("l.law", LAW),
        ("before.json", previous),
        ("after.json", current),
        ("alignment.json", alignment.as_bytes()),
    ] {
        std::fs::write(dir.join(name), bytes).unwrap();
    }
}

fn arguments<'a>(previous: &'a str, current: &'a str, out: Option<&'a str>) -> Vec<&'a str> {
    let mut args = vec![
        "reobserve",
        "--before-atom-definition",
        "d.json",
        "--before-law",
        "l.law",
        "--before-archmap",
        "before.json",
        "--atom-definition",
        "d.json",
        "--law",
        "l.law",
        "--archmap",
        "after.json",
        "--alignment",
        "alignment.json",
    ];
    for ask in previous.lines() {
        args.extend(["--before-ask", ask]);
    }
    for ask in current.lines() {
        args.extend(["--ask", ask]);
    }
    if let Some(out) = out {
        args.extend(["--out", out]);
    }
    args
}

#[test]
fn reobserve_saves_current_native_evidence_for_additions_corrections_and_withdrawals() {
    let c = Control::unlimited();
    let corrected = std::str::from_utf8(AFTER).unwrap().replace(
        concat!(
            "\"id\": \"a-quantity\",\n          \"subject\": \"a\",\n",
            "          \"field\": \"Assemble.Part.quantity\",\n          \"value\": \"1\""
        ),
        concat!(
            "\"id\": \"a-quantity\",\n          \"subject\": \"a\",\n",
            "          \"field\": \"Assemble.Part.quantity\",\n          \"value\": \"0\""
        ),
    );
    assert_ne!(corrected.as_bytes(), AFTER);
    for (case, previous_map, before_snapshot, map, snapshot, status) in [
        ("addition", BEFORE, "before", AFTER, "after", "retained"),
        (
            "correction",
            AFTER,
            "after",
            corrected.as_bytes(),
            "after",
            "retained",
        ),
        ("withdrawal", AFTER, "after", BEFORE, "before", "retained"),
    ] {
        let dir = workdir(case);
        inputs(&dir, previous_map, before_snapshot, map, snapshot);
        let previous_queries = QUERIES.replace("SNAP", before_snapshot);
        let previous_asks = previous_queries.lines().collect::<Vec<_>>();
        let old = evaluate_observed_bytes(source(previous_map), &previous_asks, &c).unwrap();
        let current_queries = QUERIES.replace("SNAP", snapshot);
        let candidates = [AssemblyCandidateAlignment {
            participant: "a",
            previous_candidate: "pick",
            current_solve: "solveIt",
        }];
        let alignment = MultiAssemblyAlignment {
            before_snapshot,
            after_snapshot: snapshot,
            reading: "Assembly",
            subjects: SUBJECTS,
            assembly: "joined",
            candidates: &candidates,
        };
        let current_asks = current_queries.lines().collect::<Vec<_>>();
        let native = reevaluate_assembly_many(
            &old,
            prepare_observed(source(map), &current_asks, &c).unwrap(),
            &alignment,
            &c,
        )
        .unwrap();
        let cold = evaluate_observed_bytes(source(map), &current_asks, &c).unwrap();
        let run = run_binary(
            &dir,
            &arguments(&previous_queries, &current_queries, Some("out")),
        );
        assert!(matches!(run.code, 0..=2), "{}{}", run.stdout, run.stderr);
        let saved = result_json(&dir, &run);
        assert_eq!(s(get(&saved, "format")), "archsig.reobservation/1");
        let current = get(&saved, "current");
        for direct in [native.evaluation(), &cold] {
            let direct = parse(direct.result_wire().canonical().as_bytes()).unwrap();
            for key in ["answers", "nodes", "issues"] {
                assert_eq!(
                    get(current, key).value,
                    get(&direct, key).value,
                    "{case}: {key}"
                );
            }
        }
        let assembled = get(&saved, "assembly");
        assert_eq!(
            assembled.value,
            parse(native.continuity_wire().canonical().as_bytes())
                .unwrap()
                .value
        );
        if case == "withdrawal" {
            let joined = |stage: &str| {
                arr(get(get(&saved, stage), "answers"))
                    .iter()
                    .find(|answer| s(get(answer, "id")) == "joined")
                    .unwrap()
            };
            assert_eq!(s(get(joined("previous"), "status")), "established");
            assert_eq!(s(get(joined("current"), "status")), "undetermined");
            assert!(
                arr(get(joined("current"), "reasons"))
                    .iter()
                    .flat_map(|reason| arr(get(reason, "missing")))
                    .any(|fact| s(get(fact, "subject")) == "mb"
                        && s(get(fact, "field")) == "Assemble.Part.quantity")
            );
        }
        let [candidate] = arr(get(assembled, "candidates")) else {
            panic!("one candidate")
        };
        assert_eq!(s(get(candidate, "status")), status);
        let solve = arr(get(current, "answers"))
            .iter()
            .find(|answer| s(get(answer, "id")) == s(get(candidate, "current_solve")))
            .unwrap();
        let reference = get(get(solve, "outputs"), "solutions");
        assert!(arr(get(current, "nodes")).iter().any(|node| {
            s(get(node, "id")) == s(get(reference, "node")) && s(get(node, "type")) == "SolutionSet"
        }));
        assert!(!has(get(candidate, "current_assignment"), "solutions"));
        assert_eq!(has(candidate, "current_assignment"), status == "retained");
        assert_eq!(
            std::fs::read(dir.join("out/inputs/current.archmap.json")).unwrap(),
            map
        );
        let unsaved = run_binary(&dir, &arguments(&previous_queries, &current_queries, None));
        assert_eq!(unsaved.code, run.code);
        assert!(!has(&unsaved.receipt, "result"));
        assert_eq!(get(&unsaved.receipt, "assembly").value, assembled.value);
    }
}

#[test]
fn reobserve_rejects_invalid_alignment_current_input_and_io_failures() {
    let dir = workdir("reobserve-errors");
    inputs(&dir, BEFORE, "before", AFTER, "after");
    let before = QUERIES.replace("SNAP", "before");
    let after = QUERIES.replace("SNAP", "after");
    let args = arguments(&before, &after, Some("out"));
    let path = dir.join("alignment.json");
    let alignment = std::fs::read_to_string(&path).unwrap();
    std::fs::write(&path, alignment.replace("\"solveIt\"", "\"wrong\"")).unwrap();
    let rejected = run_binary(&dir, &args);
    assert_eq!(rejected.code, 64);
    assert!(!dir.join("out").exists());
    std::fs::write(path, alignment).unwrap();
    std::fs::write(dir.join("after.json"), b"invalid JSON").unwrap();
    assert_eq!(run_binary(&dir, &args).code, 65);
    std::fs::remove_file(dir.join("after.json")).unwrap();
    assert_eq!(run_binary(&dir, &args).code, 74);
    assert!(!dir.join("out").exists());
}

#[test]
fn reobserve_integer_rebuilds_current_rows_when_coefficients_change() {
    mod fixture {
        include!("common/integer_reobservation_data.rs");
    }
    let dir = workdir("integer-reobserve");
    let body = "view selected(s:State):Z=s.h;change choose(s:State,p:Z)=s with {h=p};law required valid(s:State):s.a*s.h=s.b;";
    let asks = [
        "r=repair(Pair.valid,using=Pair.choose,on=@v/s,s=@v/s)",
        "h=evaluate(Pair.selected,on=$r.object,s=@v/s)",
    ];
    let queries = asks.join("\n");
    let before = fixture::input(body, "2", "2");
    for (name, bytes) in [
        ("d.json", before.definitions()[0].bytes()),
        ("l.law", before.law().bytes()),
        ("before.json", before.archmap().bytes()),
    ] {
        std::fs::write(dir.join(name), bytes).unwrap();
    }
    for (coefficient, rhs, expected, out) in [
        ("2", "6", "3", "same-matrix"),
        ("5", "10", "2", "different-matrix"),
    ] {
        let current = fixture::input(body, coefficient, rhs);
        std::fs::write(dir.join("after.json"), current.archmap().bytes()).unwrap();
        let mut args = arguments(&queries, &queries, Some(out));
        let align = args.iter().position(|&arg| arg == "--alignment").unwrap();
        args.drain(align..align + 2);
        let actual = run_binary(&dir, &args);
        assert_eq!(actual.code, 0, "{}{}", actual.stdout, actual.stderr);
        let section = get(&actual.receipt, "current");
        assert_eq!(
            s(get(
                get(get(&arr(get(section, "answers"))[1], "outputs"), "value"),
                "value"
            )),
            expected
        );
        let saved = result_json(&dir, &actual);
        let cold = evaluate_observed_bytes(current, &asks, &Control::unlimited()).unwrap();
        let cold = parse(cold.result_wire().canonical().as_bytes()).unwrap();
        let saved = get(&saved, "current");
        for key in ["answers", "nodes", "issues"] {
            assert_eq!(get(saved, key).value, get(&cold, key).value);
        }
    }
}
