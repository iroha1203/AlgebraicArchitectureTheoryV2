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
fn reobserve_retains_a_common_solution_when_concrete_updates_need_observation() {
    let dir = workdir("reobserve-common-solution-variable-update");
    let definitions = std::str::from_utf8(DEFINITIONS).unwrap();
    let with_gate = definitions.replace(
        r#""name": "quantity","#,
        r#""name":"gate","type":"Bool","meaning":"Determines the updated quantity."},
           {"name": "quantity","#,
    );
    let digest = |source: &str| {
        archsig_input::definition::check_definitions(&[("d", source.as_bytes())])
            .unwrap()
            .vocabularies()["Assemble"]
            .digest
            .clone()
    };
    let (old, current) = (digest(definitions), digest(&with_gate));
    let law = std::str::from_utf8(LAW)
        .unwrap()
        .replace(&old, &current)
        .replace(
            "quantity=if q then 1 else 0",
            "quantity=if q then (if p.gate then 1 else 0) else 2",
        )
        .replace(
            "law optional desired(p:Part,b:Part):p.quantity=b.quantity;",
            "view gate(p:Part):Bool=p.gate; law optional desired(p:Part):true;",
        );
    let law = law
        .lines()
        .filter(|line| {
            !["pair(", "boundary(", "boundaryOne("].iter().any(|name| {
                line.trim_start()
                    .strip_prefix("law optional ")
                    .is_some_and(|rest| rest.starts_with(name))
            })
        })
        .collect::<Vec<_>>()
        .join(
            "
",
        );
    let map = |subjects: &[&str]| {
        let atoms = subjects.iter().map(|subject| {
            format!(r#"{{"id":"{subject}-gate","subject":"{subject}","field":"Assemble.Part.gate","value":{},"origin":"model"}}"#, matches!(*subject, "a" | "b"))
        }).collect::<Vec<_>>();
        std::str::from_utf8(AFTER)
            .unwrap()
            .replace(&old, &current)
            .replacen(
                r#""atoms": ["#,
                &format!(r#""atoms": [{},"#, atoms.join(",")),
                1,
            )
    };
    let previous = map(&["a", "b", "ma", "mb"]);
    let current = map(&["b", "ma", "mb"]);
    inputs(
        &dir,
        previous.as_bytes(),
        "after",
        current.as_bytes(),
        "after",
    );
    std::fs::write(dir.join("d.json"), with_gate).unwrap();
    std::fs::write(dir.join("l.law"), law).unwrap();
    let questions = QUERIES.lines().filter(|line| !line.starts_with("global="))
        .map(|line| if line.starts_with("prepareIt=") {
            "prepareIt=prepare(Assembly.desired,using=Assembly.choose,on=@after/A,p=@after/a,inputs=Assembly.gate)".into()
        } else {
            line.replace("SNAP", "after").replace("index=0", "index=1")
        }).collect::<Vec<_>>().join("
");
    let run = run_binary(&dir, &arguments(&questions, &questions, Some("out")));
    assert_eq!(run.code, 2, "{}{}", run.stdout, run.stderr);
    let saved = result_json(&dir, &run);
    let report = get(&saved, "assembly");
    assert_eq!(s(get(report, "assembly_status")), "undetermined");
    assert!(arr(get(report, "layout_missing")).is_empty());
    let [candidate] = arr(get(report, "candidates")) else {
        panic!("one candidate")
    };
    assert_eq!(s(get(candidate, "status")), "retained");
    assert!(has(candidate, "current_assignment"));
    assert!(arr(get(candidate, "missing")).is_empty());
    for phase in ["previous", "current"] {
        let answers = arr(get(get(&saved, phase), "answers"));
        let answer = |name| answers.iter().find(|a| s(get(a, "id")) == name).unwrap();
        assert_eq!(s(get(answer("solveIt"), "status")), "established");
        assert_eq!(s(get(answer("pick"), "status")), "established");
        if phase == "previous" {
            assert_eq!(s(get(answer("joined"), "status")), "established");
        } else {
            let apply = answer("selected");
            assert_eq!(s(get(apply, "status")), "undetermined");
            assert!(arr(get(apply, "reasons")).iter().any(|reason| {
                arr(get(reason, "missing")).iter().any(|fact| {
                    s(get(fact, "subject")) == "a" && s(get(fact, "field")) == "Assemble.Part.gate"
                })
            }));
        }
    }
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
    let issue = &arr(get(&rejected.receipt, "issues"))[0];
    let message = s(get(issue, "message"));
    assert!(message.contains("current_solve") && message.contains("wrong"));
    assert!(message.is_ascii());
    assert!(!dir.join("out").exists());
    std::fs::write(path, alignment).unwrap();
    let current_definition = dir.join("current-definition.json");
    let mut changed_definitions = DEFINITIONS.to_vec();
    changed_definitions.push(b'\n');
    std::fs::write(&current_definition, changed_definitions).unwrap();
    let mut unsupported_args = args.clone();
    let selected = unsupported_args
        .iter()
        .position(|arg| *arg == "--atom-definition")
        .unwrap();
    unsupported_args[selected + 1] = "current-definition.json";
    let unsupported = run_binary(&dir, &unsupported_args);
    assert_eq!(unsupported.code, 69);
    assert_eq!(s(get(&unsupported.receipt, "status")), "unsupported");
    let [issue] = arr(get(&unsupported.receipt, "issues")) else {
        panic!("one unsupported alignment issue");
    };
    assert_eq!(s(get(issue, "code")), "usage");
    assert_eq!(s(get(get(issue, "details"), "argument")), "--alignment");
    assert!(arr(get(issue, "dependencies")).is_empty());
    assert!(arr(get(issue, "missing")).is_empty());
    assert!(s(get(issue, "message")).contains("identical Atom Definition inputs"));
    assert!(!dir.join("out").exists());
    for (stage, name, valid) in [
        ("previous", "before.json", BEFORE),
        ("current", "after.json", AFTER),
    ] {
        std::fs::write(dir.join(name), b"invalid JSON").unwrap();
        let rejected = run_binary(&dir, &args);
        assert_eq!(rejected.code, 65);
        let [issue] = arr(get(&rejected.receipt, "issues")) else {
            panic!("one invalid input issue")
        };
        assert_eq!(s(get(issue, "stage")), stage);
        assert_eq!(s(get(get(issue, "location"), "input")), "archmap");
        std::fs::write(dir.join(name), valid).unwrap();
    }
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
