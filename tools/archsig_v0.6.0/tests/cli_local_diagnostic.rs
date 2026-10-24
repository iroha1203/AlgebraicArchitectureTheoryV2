//! 固定対象の局所化と有限診断。Law成立と貼り合わせを区別する実CLI試験。
#[allow(dead_code)]
#[path = "common/cli.rs"]
mod cli;
use archsig::{definition, json::JNode};
use cli::*;
const D: &str = r#"{"format":"archsig.atom-definition/1","semantics":"archsig/0.6.0","vocabularies":[{"semantics":"archsig/0.6.0","namespace":"Fixed","version":"1","dependencies":[],"declarations":[{"kind":"entity","name":"Fixed.State","meaning":"固定状態。","parameters":[],"fields":[{"name":"flag","type":"Bool","meaning":"観測値。"}],"alignments":[]}]}]}"#;
fn input(name: &str, value: Option<bool>) -> std::path::PathBuf {
    let definitions = definition::check_definitions(&[("d", D.as_bytes())]).unwrap();
    let digest = &definitions.vocabularies["Fixed"].digest;
    let atoms=value.map(|v|format!(r#"{{"id":"f","subject":"s","field":"Fixed.State.flag","value":{v},"origin":"model"}}"#)).unwrap_or_default();
    let map = format!(
        r#"{{"format":"archsig.archmap/2","semantics":"archsig/0.6.0","vocabularies":[{{"namespace":"Fixed","version":"1","digest":"{digest}"}}],"sources":[],"origins":[{{"id":"model","mode":"specification","method":"固定状態の独立試験。","locations":[],"note":"観測有無を分ける試験モデル。"}}],"snapshots":[{{"id":"fixed","origin":"model","subjects":[{{"id":"s","type":"Fixed.State","origin":"model"}}],"atoms":[{atoms}]}}]}}"#
    );
    let law = format!(
        "law \"archsig.law/2\" semantics \"archsig/0.6.0\"; reading Fixed {{ use vocabulary Fixed version \"1\" digest \"{digest}\"; law required valid(s:State):s.flag=true; view current(s:State):Bool=s.flag; }}"
    );
    let dir = workdir(name);
    for (name, value) in [
        ("d.json", D),
        ("a.json", map.as_str()),
        ("l.law", law.as_str()),
    ] {
        std::fs::write(dir.join(name), value).unwrap();
    }
    dir
}
fn execute(dir: &std::path::Path, out: &str, asks: &[&str]) -> Run {
    let mut args = vec![
        "run",
        "--atom-definition",
        "d.json",
        "--archmap",
        "a.json",
        "--law",
        "l.law",
        "--out",
        out,
        "--time-ms",
        "120000",
    ];
    for ask in asks {
        args.extend(["--ask", *ask]);
    }
    run(dir, &args)
}
fn node<'a>(r: &'a JNode, reference: &JNode) -> &'a JNode {
    arr(get(r, "nodes"))
        .iter()
        .find(|n| s(get(n, "id")) == s(get(reference, "node")))
        .unwrap()
}
fn output<'a>(r: &'a JNode, i: usize, name: &str) -> &'a JNode {
    node(r, get(get(&arr(get(r, "answers"))[i], "outputs"), name))
}
#[test]
fn fixed_state_diagnostic_keeps_empty_solutions_separate_from_identity_gluing() {
    for value in [true, false] {
        let dir = input(
            if value { "local-true" } else { "local-false" },
            Some(value),
        );
        let r = execute(
            &dir,
            "out",
            &[
                "a=build(Fixed,on=@fixed/s)",
                "l=localize($a.object,law=Fixed.valid,s=@fixed/s)",
                "e=diagnose($l.system)",
                "s=diagnose($l.system,side=semantic)",
                "z=diagnose($l.system,degree=0)",
                "v=evaluate(Fixed.current,on=$l.system.base,s=@fixed/s)",
            ],
        );
        assert_eq!(
            r.code,
            if value { 0 } else { 1 },
            "{} {}",
            r.stdout,
            r.stderr
        );
        let json = result_json(&dir, &r);
        assert_eq!(
            s(get(&arr(get(&json, "answers"))[1], "status")),
            "established"
        );
        assert_eq!(
            s(get(&arr(get(&json, "answers"))[4], "status")),
            "established"
        );
        let system = get(output(&json, 1, "system"), "value");
        assert_eq!(arr(get(system, "contexts")).len(), 1);
        let context = get(node(&json, &arr(get(system, "contexts"))[0]), "value");
        let carrier = arr(get(context, "carrier"));
        assert_eq!(carrier.len(), 1);
        assert_eq!(s(&arr(get(&carrier[0], "value"))[1]), "s");
        let arrow = get(node(&json, &arr(get(system, "maps"))[0]), "value");
        assert_eq!(arr(get(arrow, "images")).len(), carrier.len());
        assert_eq!(num(&arr(get(arrow, "images"))[0]), 0);
        assert_eq!(arr(get(system, "sheaf_checks")).len(), 4);
        let topology = get(node(&json, get(system, "topology")), "value");
        assert_eq!(arr(get(topology, "covering_sieves")).len(), 1);
        for i in [2, 3] {
            assert_eq!(
                s(get(&arr(get(&json, "answers"))[i], "status")),
                if value { "established" } else { "refuted" }
            );
            let diagnostic = get(output(&json, i, "diagnostic"), "value");
            assert_eq!(s(get(diagnostic, "kind")), "finite_matching");
            let matching = get(node(&json, get(diagnostic, "matching")), "value");
            assert_eq!(arr(get(matching, "elements")).len(), usize::from(value));
            let global = get(node(&json, get(diagnostic, "global")), "value");
            assert_eq!(
                arr(get(get(global, "representation"), "values")).len(),
                usize::from(value)
            );
            let restriction = get(node(&json, get(diagnostic, "restriction")), "value");
            assert_eq!(arr(get(restriction, "pairs")).len(), usize::from(value));
        }
    }
}
#[test]
fn localize_defaults_select_required_law_and_fixed_unit_candidate() {
    let dir = input("local-defaults", Some(true));
    let r = execute(
        &dir,
        "out",
        &[
            "a=build(Fixed,on=@fixed/s)",
            "l=localize($a.object)",
            "d=diagnose($l.system,degree=1,side=equation)",
        ],
    );
    assert_eq!(r.code, 0, "{} {}", r.stdout, r.stderr);
    let json = result_json(&dir, &r);
    let scope = get(output(&json, 1, "system"), "scope");
    assert!(
        arr(get(scope, "quantifiers"))
            .iter()
            .any(|q| s(get(q, "name")) == "s" && has(q, "domain"))
    );
    let system = get(output(&json, 1, "system"), "value");
    let semantic = &arr(get(system, "semantic_states"))[0];
    let solutions = get(node(&json, get(semantic, "parameters")), "value");
    let candidates = get(node(&json, get(solutions, "domain")), "value");
    assert_eq!(s(get(candidates, "kind")), "identity");
    assert!(!has(candidates, "change"));
    let equation = &arr(get(system, "equation_states"))[0];
    let space = get(node(&json, get(equation, "space")), "value");
    assert!(arr(get(space, "variables")).is_empty());
    assert!(!arr(get(space, "fixed")).is_empty());
}
#[test]
fn unknown_fixed_value_is_not_a_free_coordinate_or_empty_solution() {
    let dir = input("local-missing", None);
    let r = execute(
        &dir,
        "out",
        &[
            "a=build(Fixed,on=@fixed/s)",
            "l=localize($a.object,law=Fixed.valid,s=@fixed/s)",
            "d=diagnose($l.system)",
            "n=needed($l)",
        ],
    );
    assert_eq!(r.code, 2, "{} {}", r.stdout, r.stderr);
    let json = result_json(&dir, &r);
    let answers = arr(get(&json, "answers"));
    assert_eq!(s(get(&answers[1], "status")), "undetermined");
    assert!(!has(get(&answers[1], "outputs"), "system"));
    assert!(!has(get(&answers[2], "outputs"), "diagnostic"));
}
#[test]
fn local_system_saved_reuse_and_answer_bindings_keep_the_same_result() {
    let dir = input("local-reuse", Some(true));
    let asks = [
        "a=build(Fixed,on=@fixed/s)",
        "l=localize($a.object,law=Fixed.valid,s=$a.object.root)",
        "d=diagnose($l.system)",
        "again=diagnose($d.diagnostic.system,degree=0)",
    ];
    let result = execute(&dir, "out", &asks);
    assert_eq!(result.code, 0, "{} {}", result.stdout, result.stderr);
    let before = result_json(&dir, &result);
    let mut args = vec![
        "run",
        "--atom-definition",
        "d.json",
        "--archmap",
        "a.json",
        "--law",
        "l.law",
        "--out",
        "again",
        "--reuse",
        "out",
        "--time-ms",
        "120000",
    ];
    for ask in &asks {
        args.extend(["--ask", ask]);
    }
    let result = run(&dir, &args);
    assert_eq!(result.code, 0, "{} {}", result.stdout, result.stderr);
    let after = result_json(&dir, &result);
    for field in ["answers", "nodes"] {
        assert_eq!(get(&before, field).value, get(&after, field).value);
    }
}
#[test]
fn finite_higher_degree_is_unsupported_and_does_not_stop_independent_answers() {
    let dir = input("local-degree", Some(true));
    let r = execute(
        &dir,
        "out",
        &[
            "a=build(Fixed,on=@fixed/s)",
            "l=localize($a.object)",
            "d=diagnose($l.system,degree=2)",
            "v=evaluate(Fixed.current,s=@fixed/s)",
        ],
    );
    assert_eq!(r.code, 2, "{} {}", r.stdout, r.stderr);
    let json = result_json(&dir, &r);
    let answers = arr(get(&json, "answers"));
    assert!(!has(get(&answers[2], "outputs"), "diagnostic"));
    assert!(
        arr(get(&answers[2], "reasons"))
            .iter()
            .any(|r| s(get(r, "code")) == "unsupported_algorithm")
    );
    assert_eq!(s(get(&answers[3], "status")), "established");
}
#[test]
fn localize_budget_and_signal_stop_keep_the_prior_architecture() {
    use archsig::observed::{
        control::{Checkpoint, Control, Limits, Usage},
        evaluate::evaluate_observed_bytes,
        input::InputSources,
    };
    use std::{cell::Cell, rc::Rc};
    let dir = input("local-stop", Some(true));
    for mode in 0..3 {
        let seen = Rc::new(Cell::new(false));
        let active = seen.clone();
        let mut control = Control::new(
            Limits {
                time_ms: Some(1),
                memory_mib: Some(1),
            },
            move |point| {
                if point == Checkpoint::Localize {
                    active.set(true);
                }
                if active.get() {
                    match mode {
                        0 => Usage {
                            elapsed_ms: 2,
                            ..Usage::default()
                        },
                        1 => Usage {
                            memory_mib: 2,
                            ..Usage::default()
                        },
                        _ => Usage {
                            signal: Some(archsig::result::Signal::Term),
                            ..Usage::default()
                        },
                    }
                } else {
                    Usage::default()
                }
            },
        );
        let sources = InputSources::from_bytes(
            vec![std::fs::read(dir.join("d.json")).unwrap()],
            std::fs::read(dir.join("l.law")).unwrap(),
            std::fs::read(dir.join("a.json")).unwrap(),
        );
        let result = evaluate_observed_bytes(
            sources,
            &["a=build(Fixed,on=@fixed/s)", "l=localize($a.object)"],
            &mut control,
        )
        .unwrap();
        assert!(seen.get());
        let json = archsig::json::parse(result.wire().canonical().as_bytes()).unwrap();
        let answers = arr(get(&json, "answers"));
        assert!(has(get(&answers[0], "outputs"), "object"));
        assert!(!has(get(&answers[1], "outputs"), "system"));
        assert_eq!(s(get(&answers[1], "status")), "undetermined");
        assert!(
            arr(get(&answers[1], "reasons"))
                .iter()
                .any(|r| s(get(r, "code"))
                    == if mode == 2 {
                        "cancelled"
                    } else {
                        "budget_exhausted"
                    })
        );
    }
}
#[test]
fn implicit_context_exposes_the_primitive_read_as_well_as_the_equation_value() {
    let dir = input("local-integer-reading", Some(true));
    let original = definition::check_definitions(&[("d", D.as_bytes())]).unwrap();
    let definitions = D.replace("\"Bool\"", "\"Z\"");
    let checked = definition::check_definitions(&[("d", definitions.as_bytes())]).unwrap();
    let old = &original.vocabularies["Fixed"].digest;
    let new = &checked.vocabularies["Fixed"].digest;
    std::fs::write(dir.join("d.json"), definitions).unwrap();
    let map = std::fs::read_to_string(dir.join("a.json"))
        .unwrap()
        .replace(old, new)
        .replace("\"value\":true", "\"value\":\"3\"");
    std::fs::write(dir.join("a.json"), map).unwrap();
    let law = std::fs::read_to_string(dir.join("l.law"))
        .unwrap()
        .replace(old, new)
        .replace("s.flag=true", "s.flag+s.flag=6")
        .replace(":Bool=s.flag", ":Z=s.flag");
    std::fs::write(dir.join("l.law"), law).unwrap();
    let result = execute(
        &dir,
        "out",
        &[
            "a=build(Fixed,on=@fixed/s)",
            "l=localize($a.object)",
            "d=diagnose($l.system)",
        ],
    );
    assert_eq!(result.code, 0, "{} {}", result.stdout, result.stderr);
    let json = result_json(&dir, &result);
    let system = get(output(&json, 1, "system"), "value");
    let context = get(node(&json, &arr(get(system, "contexts"))[0]), "value");
    let mut values = vec![];
    for reading in arr(get(context, "readings")) {
        let domain = get(node(&json, get(reading, "domain")), "value");
        for reference in arr(get(domain, "elements")) {
            values.push(s(get(node(&json, reference), "value")));
        }
    }
    assert!(values.contains(&"3"));
    assert!(values.contains(&"6"));
}
