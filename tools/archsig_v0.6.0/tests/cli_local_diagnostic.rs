//! 固定対象の局所化と有限診断。Law成立と貼り合わせを区別する実CLI試験。
#[allow(dead_code)]
#[path = "common/cli.rs"]
mod cli;
use archsig::{definition, json::JNode};
use cli::*;
#[path = "common/mod.rs"]
mod common;
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
                "equationBase=evaluate(Fixed.current,on=$e.diagnostic.global.domain.base,s=@fixed/s)",
                "semanticBase=evaluate(Fixed.current,on=$s.diagnostic.global.domain.base,s=@fixed/s)",
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
        let zero = &arr(get(&json, "answers"))[4];
        assert!(!has(zero, "claim"));
        assert!(!has(get(zero, "outputs"), "proposition"));
        assert!(has(get(zero, "outputs"), "diagnostic"));
        for index in [5, 6, 7] {
            assert_eq!(
                get(output(&json, index, "value"), "value").value,
                archsig::json::JValue::Bool(value)
            );
        }
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
            if !value {
                let answer = &arr(get(&json, "answers"))[i];
                let claim = node(&json, get(answer, "claim"));
                let evidence = arr(get(get(claim, "judgment"), "evidence"));
                assert_eq!(evidence.len(), 1);
                assert_eq!(
                    get(answer, "evidence").value,
                    get(get(claim, "judgment"), "evidence").value
                );
                let certificate = get(node(&json, &evidence[0]), "value");
                assert_eq!(s(get(certificate, "kind")), "finite_exhaustion");
                let data = get(certificate, "data");
                assert_eq!(num(get(data, "checked")), 1);
                assert_eq!(arr(get(data, "instances")).len(), 1);
                let domain = get(node(&json, get(data, "domain")), "value");
                assert_eq!(arr(get(domain, "elements")).len(), 1);
            }
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
            "explicit=localize($a.object,law=Fixed.valid)",
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
    let context = get(node(&json, &arr(get(system, "contexts"))[0]), "value");
    for slots in [get(space, "fixed"), get(context, "dependencies")] {
        for slot in arr(slots) {
            assert!(!has(slot, "snapshot"));
            assert_eq!(s(get(slot, "field")), "Fixed.State.flag");
            let subject = node(&json, get(slot, "subject"));
            let value = arr(get(subject, "value"));
            assert_eq!(s(&value[0]), "fixed");
            assert_eq!(s(&value[1]), "s");
        }
    }
    let equation_solution = node(&json, get(equation, "solutions"));
    assert_eq!(
        s(get(get(equation_solution, "rule"), "name")),
        "equation_solutions"
    );
    let cover = get(node(&json, get(system, "cover")), "value");
    for overlap in arr(get(cover, "overlaps")) {
        assert_eq!(s(get(get(node(&json, overlap), "rule"), "name")), "context");
    }
    let rejected = execute(
        &dir,
        "private-path",
        &[
            "a=build(Fixed,on=@fixed/s)",
            "l=localize($a.object)",
            "d=diagnose($l.system,side=semantic)",
            "v=evaluate(Fixed.current,on=$d.diagnostic.global.domain.states.base,s=@fixed/s)",
        ],
    );
    assert_eq!(rejected.code, 64, "{} {}", rejected.stdout, rejected.stderr);
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
    assert!(arr(get(&answers[0], "reasons")).iter().all(|r|
        s(get(r, "code")) != "unsupported_algorithm"));
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
#[test]
fn localize_checks_answer_bound_owners_before_using_the_values() {
    let root = common::entity_json("W.Root", "[]", "[]");
    let owner = common::field_json("owner", r#"["Ref","W.Root"]"#);
    let item = common::entity_json("W.Item", &format!("[{owner}]"), "[]");
    let definition = common::definition_json(&format!(
        "[{}]",
        common::vocabulary_json("W", &format!("[{root},{item}]"), "[]")
    ));
    let definitions = common::definitions_ok(&[&definition]);
    let digest = &definitions.vocabularies["W"].digest;
    let law = format!(
        "{}reading R {{use vocabulary W version \"1\" digest \"{digest}\";view echo(a:Root):Root=a;law optional present(a:Root,b:Item[a]):true=true;}}",
        common::HEADER
    );
    let map = format!(
        r#"{{"format":"archsig.archmap/2","semantics":"archsig/0.6.0","vocabularies":[{{"namespace":"W","version":"1","digest":"{digest}"}}],"sources":[],"origins":[{{"id":"o","mode":"specification","method":"所属の独立試験。","locations":[],"note":"固定owner。"}}],"snapshots":[{{"id":"v","origin":"o","subjects":[{{"id":"A","type":"W.Root","origin":"o"}},{{"id":"B","type":"W.Root","origin":"o"}},{{"id":"i","type":"W.Item","origin":"o"}}],"atoms":[{{"id":"owner","subject":"i","field":"W.Item.owner","value":["v","A"],"origin":"o"}}]}}]}}"#
    );
    let dir = workdir("local-owned");
    for (name, value) in [("d.json", definition), ("l.law", law), ("a.json", map)] {
        std::fs::write(dir.join(name), value).unwrap();
    }
    for (name, selection, code) in [
        ("valid", "owner=evaluate(R.echo,a=@v/A)", 1),
        ("invalid", "owner=evaluate(R.echo,a=@v/B)", 2),
    ] {
        let r = execute(
            &dir,
            name,
            &[
                "a=build(R,on=@v/A)",
                selection,
                "l=localize($a.object,law=R.present,a=$owner.value,b=@v/i)",
                "d=diagnose($l.system)",
            ],
        );
        assert_eq!(r.code, code, "{} {}", r.stdout, r.stderr);
        let json = result_json(&dir, &r);
        if name == "valid" {
            assert_eq!(
                s(get(&arr(get(&json, "answers"))[2], "status")),
                "established"
            );
            assert_eq!(
                s(get(&arr(get(&json, "answers"))[3], "status")),
                "established"
            );
            assert!(has(
                get(&arr(get(&json, "answers"))[2], "outputs"),
                "system"
            ));
        } else {
            let answer = &arr(get(&json, "answers"))[2];
            assert!(!has(get(answer, "outputs"), "system"));
            assert!(
                arr(get(answer, "reasons"))
                    .iter()
                    .any(|r| s(get(r, "code")) == "condition_failed")
            );
        }
    }
}

#[test]
fn short_circuit_truth_keeps_missing_local_reads_and_needed_slots() {
    for (index, expression) in ["(s.flag and false)=false", "(s.flag or true)=true"]
        .iter()
        .enumerate()
    {
        for value in [None, Some(false), Some(true)] {
            let dir = input(&format!("local-short-{index}-{value:?}"), value);
            let path = dir.join("l.law");
            let law = std::fs::read_to_string(&path)
                .unwrap()
                .replace("s.flag=true", expression);
            std::fs::write(path, law).unwrap();
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
            assert_eq!(
                r.code,
                if value.is_some() { 0 } else { 2 },
                "{} {}",
                r.stdout,
                r.stderr
            );
            let result = result_json(&dir, &r);
            let answers = arr(get(&result, "answers"));
            if value.is_none() {
                assert!(!has(get(&answers[1], "outputs"), "system"));
                assert!(!has(get(&answers[2], "outputs"), "diagnostic"));
                for answer in &answers[1..3] {
                    assert_eq!(s(get(answer, "status")), "undetermined");
                    assert!(
                        arr(get(answer, "reasons"))
                            .iter()
                            .any(|reason| s(get(reason, "code")) == "missing_observation")
                    );
                }
                assert_eq!(s(get(&answers[3], "status")), "established");
                let plan = get(output(&result, 3, "plan"), "value");
                assert!(arr(get(plan, "requirements")).iter().any(|requirement| {
                    let field = get(requirement, "field");
                    s(get(field, "snapshot")) == "fixed"
                        && s(get(field, "subject")) == "s"
                        && s(get(field, "field")) == "Fixed.State.flag"
                }));
            } else {
                assert_eq!(s(get(&answers[1], "status")), "established");
                assert_eq!(s(get(&answers[2], "status")), "established");
                assert!(has(get(&answers[1], "outputs"), "system"));
            }
        }
    }
}

#[test]
fn missing_parameter_owner_domain_reaches_needed_without_becoming_unimplemented() {
    #[path = "common/architecture_environment.rs"]
    mod fixture;
    let map = fixture::remove_atom("p-owner");
    let input = fixture::input("law optional localValid(s:State):true=true;", Some(&map));
    let dir = workdir("local-owner-domain");
    for (name, bytes) in [
        ("d.json", input.definitions()[0].bytes()),
        ("l.law", input.law().bytes()),
        ("a.json", input.archmap().bytes()),
    ] {
        std::fs::write(dir.join(name), bytes).unwrap();
    }
    let r = execute(
        &dir,
        "out",
        &[
            fixture::MAP,
            "l=localize($m.candidate.source,law=Reservations.localValid)",
            "n=needed($l)",
        ],
    );
    assert_eq!(r.code, 2, "{} {}", r.stdout, r.stderr);
    let result = result_json(&dir, &r);
    let answers = arr(get(&result, "answers"));
    assert!(!has(get(&answers[1], "outputs"), "system"));
    assert_eq!(s(get(&answers[1], "status")), "undetermined");
    assert_eq!(s(get(&answers[2], "status")), "established");
    let plan = get(output(&result, 2, "plan"), "value");
    assert!(arr(get(plan, "requirements")).iter().any(|requirement| {
        let field = get(requirement, "field");
        s(get(field, "subject")) == "p" && s(get(field, "field")) == "Reservations.State.owner"
    }));
}

#[test]
fn boolean_law_forms_localize_with_their_actual_truth_and_missing_reads() {
    for (index, body) in ["s.flag", "not s.flag", "s.flag and true"]
        .iter()
        .enumerate()
    {
        for value in [Some(false), Some(true), None] {
            let dir = input(&format!("local-bool-{index}-{value:?}"), value);
            let path = dir.join("l.law");
            let law = std::fs::read_to_string(&path)
                .unwrap()
                .replace("s.flag=true", body);
            std::fs::write(path, law).unwrap();
            let mut asks = vec![
                "a=build(Fixed,on=@fixed/s)",
                "l=localize($a.object)",
                "e=diagnose($l.system,side=equation)",
                "s=diagnose($l.system,side=semantic)",
            ];
            asks.push("n=needed($l)");
            let r = execute(&dir, "out", &asks);
            let truth = value.map(|v| if index == 1 { !v } else { v });
            assert_eq!(
                r.code,
                match truth {
                    None => 2,
                    Some(false) => 1,
                    Some(true) => 0,
                },
                "{} {}",
                r.stdout,
                r.stderr
            );
            let result = result_json(&dir, &r);
            let answers = arr(get(&result, "answers"));
            assert_eq!(s(get(&answers[4], "status")), "established");
            if let Some(truth) = truth {
                assert_eq!(s(get(&answers[1], "status")), "established");
                for answer in &answers[2..4] {
                    assert_eq!(
                        s(get(answer, "status")),
                        if truth { "established" } else { "refuted" }
                    );
                }
                let system = get(output(&result, 1, "system"), "value");
                let context = get(node(&result, &arr(get(system, "contexts"))[0]), "value");
                assert!(!arr(get(context, "readings")).is_empty());
            } else {
                assert!(!has(get(&answers[1], "outputs"), "system"));
                assert_eq!(s(get(&answers[4], "status")), "established");
                let plan = get(output(&result, 4, "plan"), "value");
                assert!(
                    arr(get(plan, "requirements"))
                        .iter()
                        .any(|r| s(get(get(r, "field"), "field")) == "Fixed.State.flag")
                );
            }
        }
    }
}

#[test]
fn fixed_integer_comparison_is_a_finite_local_condition() {
    #[path = "common/architecture_environment.rs"]
    mod fixture;
    for (index, condition, expected) in [(0, "s.free<3", true), (1, "s.free>3", false)] {
        let input = fixture::input(
            &format!("law optional localCompare(s:State):{condition};"),
            None,
        );
        let dir = workdir(&format!("local-inequality-{index}"));
        for (name, bytes) in [
            ("d.json", input.definitions()[0].bytes()),
            ("l.law", input.law().bytes()),
            ("a.json", input.archmap().bytes()),
        ] {
            std::fs::write(dir.join(name), bytes).unwrap();
        }
        let r = execute(
            &dir,
            "out",
            &[
                fixture::MAP,
                "l=localize($m.candidate.source,law=Reservations.localCompare,s=@v/p)",
                "d=diagnose($l.system)",
            ],
        );
        let result = result_json(&dir, &r);
        let answers = arr(get(&result, "answers"));
        assert_eq!(
            s(get(&answers[1], "status")),
            "established",
            "{} {}",
            r.stdout,
            r.stderr
        );
        assert_eq!(
            s(get(&answers[2], "status")),
            if expected { "established" } else { "refuted" },
            "{} {}",
            r.stdout,
            r.stderr
        );
        assert_eq!(r.code, if expected { 0 } else { 1 });
        let system = get(output(&result, 1, "system"), "value");
        let context = get(node(&result, &arr(get(system, "contexts"))[0]), "value");
        assert!(!arr(get(context, "readings")).is_empty());
    }
}

#[test]
fn conditional_law_localization_preserves_guard_and_nonapplication() {
    for (guard, body, value, expected) in [
        ("true", "s.flag", Some(true), "established"),
        ("true", "s.flag", Some(false), "refuted"),
        ("true", "s.flag", None, "undetermined"),
        ("false", "s.flag", Some(false), "established"),
        ("false", "s.flag", None, "undetermined"),
        ("s.flag", "false", Some(true), "refuted"),
        ("s.flag", "false", Some(false), "established"),
        ("s.flag", "false", None, "undetermined"),
    ] {
        let dir = input("local-conditional", value);
        let law = std::fs::read_to_string(dir.join("l.law")).unwrap();
        std::fs::write(
            dir.join("l.law"),
            law.replace(
                "law required valid(s:State):s.flag=true;",
                &format!("law required valid(s:State) when {guard}:{body};"),
            ),
        )
        .unwrap();
        let r = execute(
            &dir,
            "out",
            &[
                "a=build(Fixed,on=@fixed/s)",
                "l=localize($a.object)",
                "e=diagnose($l.system,side=equation)",
                "s=diagnose($l.system,side=semantic)",
                "n=needed($l)",
            ],
        );
        assert_eq!(
            r.code,
            match expected {
                "established" if value.is_none() => 2, // build の公開 view は欠測のまま。
                "established" => 0,
                "refuted" => 1,
                _ => 2,
            },
            "{guard} / {body} / {value:?}: {} {}",
            r.stdout,
            r.stderr
        );
        let result = result_json(&dir, &r);
        let answers = arr(get(&result, "answers"));
        assert_eq!(
            s(get(&answers[1], "status")),
            if expected == "undetermined" {
                expected
            } else {
                "established"
            }
        );
        assert_eq!(s(get(&answers[4], "status")), "established");
        if expected == "undetermined" {
            assert!(!has(get(&answers[1], "outputs"), "system"));
            let plan = get(output(&result, 4, "plan"), "value");
            assert!(
                arr(get(plan, "requirements"))
                    .iter()
                    .any(|r| s(get(get(r, "field"), "field")) == "Fixed.State.flag")
            );
            continue;
        }
        for index in [2, 3] {
            assert_eq!(s(get(&answers[index], "status")), expected);
            let diagnostic = get(output(&result, index, "diagnostic"), "value");
            let global = get(node(&result, get(diagnostic, "global")), "value");
            assert_eq!(
                arr(get(get(global, "representation"), "values")).len(),
                usize::from(expected == "established")
            );
        }
        let system = get(output(&result, 1, "system"), "value");
        let context = get(node(&result, &arr(get(system, "contexts"))[0]), "value");
        let instance = get(
            node(&result, &arr(get(context, "law_coordinates"))[0]),
            "value",
        );
        assert!(
            arr(get(context, "dependencies"))
                .iter()
                .any(|slot| s(get(slot, "field")) == "Fixed.State.flag")
        );
        let diagnostic = get(output(&result, 2, "diagnostic"), "value");
        let solutions = get(node(&result, get(diagnostic, "global")), "value");
        let equations = get(node(&result, get(solutions, "domain")), "value");
        assert!(
            arr(get(equations, "fixed"))
                .iter()
                .any(|slot| s(get(slot, "field")) == "Fixed.State.flag")
        );
        assert!(has(instance, "guard"));
        assert_eq!(
            s(get(node(&result, get(instance, "guard")), "type")),
            "Expression"
        );
    }
}

#[test]
fn conditional_local_system_saved_reuse_keeps_guarded_instance() {
    let dir = input("local-conditional-reuse", Some(false));
    let law = std::fs::read_to_string(dir.join("l.law")).unwrap();
    std::fs::write(
        dir.join("l.law"),
        law.replace(
            "law required valid(s:State):s.flag=true;",
            "law required valid(s:State) when s.flag:false;",
        ),
    )
    .unwrap();
    let asks = [
        "a=build(Fixed,on=@fixed/s)",
        "l=localize($a.object)",
        "d=diagnose($l.system)",
        "v=evaluate(Fixed.current,on=$d.diagnostic.global.domain.base,s=@fixed/s)",
    ];
    let first = execute(&dir, "out", &asks);
    assert_eq!(first.code, 0, "{} {}", first.stdout, first.stderr);
    let before = result_json(&dir, &first);
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
    for ask in asks {
        args.extend(["--ask", ask]);
    }
    let second = run(&dir, &args);
    assert_eq!(second.code, 0, "{} {}", second.stdout, second.stderr);
    let after = result_json(&dir, &second);
    for field in ["answers", "nodes"] {
        assert_eq!(get(&before, field).value, get(&after, field).value);
    }
    assert_eq!(
        get(output(&after, 3, "value"), "value").value,
        archsig::json::JValue::Bool(false)
    );
}

#[test]
fn required_laws_on_the_same_support_are_all_retained_and_checked() {
    for (second, value, truth) in [
        ("s.flag=s.flag", Some(true), Some(true)),
        ("s.flag=s.flag", Some(false), Some(false)),
        ("not s.flag", Some(true), Some(false)),
        ("s.flag=s.flag", None, None),
    ] {
        let dir = input("local-law-family", value);
        let law = std::fs::read_to_string(dir.join("l.law")).unwrap();
        std::fs::write(
            dir.join("l.law"),
            law.replace(
                "view current",
                &format!(
                    "law required also(t:State):{}; view current",
                    second.replace("s.flag", "t.flag")
                ),
            ),
        )
        .unwrap();
        let r = execute(
            &dir,
            "out",
            &[
                "a=build(Fixed,on=@fixed/s)",
                "l=localize($a.object)",
                "e=diagnose($l.system)",
                "s=diagnose($l.system,side=semantic)",
                "n=needed($l)",
            ],
        );
        assert_eq!(
            r.code,
            match truth {
                Some(true) => 0,
                Some(false) => 1,
                None => 2,
            },
            "{} {}",
            r.stdout,
            r.stderr
        );
        let result = result_json(&dir, &r);
        let answers = arr(get(&result, "answers"));
        if let Some(truth) = truth {
            assert_eq!(s(get(&answers[1], "status")), "established");
            let system = get(output(&result, 1, "system"), "value");
            let laws = arr(get(system, "laws"));
            assert_eq!(laws.len(), 2);
            let names = laws
                .iter()
                .map(|r| s(get(get(node(&result, r), "value"), "name")))
                .collect::<Vec<_>>();
            assert_eq!(names, vec!["Fixed.also", "Fixed.valid"]);
            let context = get(node(&result, &arr(get(system, "contexts"))[0]), "value");
            assert_eq!(arr(get(context, "law_coordinates")).len(), 2);
            assert_eq!(arr(get(context, "dependencies")).len(), 1);
            for index in [2, 3] {
                assert_eq!(
                    s(get(&answers[index], "status")),
                    if truth { "established" } else { "refuted" }
                );
                let diagnostic = get(output(&result, index, "diagnostic"), "value");
                let global = get(node(&result, get(diagnostic, "global")), "value");
                assert_eq!(
                    arr(get(get(global, "representation"), "values")).len(),
                    usize::from(truth)
                );
                if !truth {
                    let claim = node(&result, get(&answers[index], "claim"));
                    let certificate = get(
                        node(&result, &arr(get(get(claim, "judgment"), "evidence"))[0]),
                        "value",
                    );
                    assert_eq!(arr(get(get(certificate, "data"), "instances")).len(), 2);
                }
            }
        } else {
            assert_eq!(s(get(&answers[1], "status")), "undetermined");
            assert!(!has(get(&answers[1], "outputs"), "system"));
            assert_eq!(arr(get(&answers[1], "reasons")).len(), 2);
            assert_eq!(s(get(&answers[4], "status")), "established");
        }
    }
}

#[test]
fn distinct_law_supports_are_not_replaced_by_an_added_full_patch() {
    let dir = input("local-distinct-support", Some(true));
    let law = std::fs::read_to_string(dir.join("l.law")).unwrap();
    std::fs::write(
        dir.join("l.law"),
        law.replace(
            "view current",
            "law required separate(s:State):true; view current",
        ),
    )
    .unwrap();
    let r = execute(
        &dir,
        "out",
        &[
            "a=build(Fixed,on=@fixed/s)",
            "v=evaluate(Fixed.current,s=@fixed/s)",
            "l=localize($a.object)",
        ],
    );
    assert_eq!(r.code, 0, "{} {}", r.stdout, r.stderr);
    let result = result_json(&dir, &r);
    let answers = arr(get(&result, "answers"));
    assert!(has(get(&answers[2], "outputs"), "system"));
    let system = get(output(&result, 2, "system"), "value");
    assert_eq!(arr(get(system,"contexts")).len(),2);
    let cover=get(node(&result,get(system,"cover")),"value");
    assert_eq!(arr(get(cover,"patches")).len(),2);
    assert_eq!(
        get(output(&result, 1, "value"), "value").value,
        archsig::json::JValue::Bool(true)
    );
}

#[test]
fn shared_support_law_family_reuses_each_original_requirement() {
    let dir = input("local-family-reuse", Some(true));
    let law = std::fs::read_to_string(dir.join("l.law")).unwrap();
    std::fs::write(dir.join("l.law"),law.replace("view current","law required other(t:State):t.flag=t.flag; law optional ignored(s:State):not s.flag; view current")).unwrap();
    let asks = [
        "a=build(Fixed,on=@fixed/s)",
        "l=localize($a.object)",
        "d=diagnose($l.system)",
        "v=evaluate(Fixed.current,on=$d.diagnostic.global.domain.base,s=@fixed/s)",
    ];
    let first = execute(&dir, "out", &asks);
    assert_eq!(first.code, 0, "{} {}", first.stdout, first.stderr);
    let before = result_json(&dir, &first);
    assert_eq!(
        arr(get(get(output(&before, 1, "system"), "value"), "laws")).len(),
        2
    );
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
    ];
    for ask in asks {
        args.extend(["--ask", ask]);
    }
    let second = run(&dir, &args);
    assert_eq!(second.code, 0, "{} {}", second.stdout, second.stderr);
    let after = result_json(&dir, &second);
    for field in ["answers", "nodes"] {
        assert_eq!(get(&before, field).value, get(&after, field).value);
    }
    assert_eq!(
        get(output(&after, 3, "value"), "value").value,
        archsig::json::JValue::Bool(true)
    );
}

#[test]
fn finite_law_parameters_are_universal_and_keep_each_binding() {
    for value in [Some(true), Some(false), None] {
        let dir = input("local-finite-instances", value);
        let law = std::fs::read_to_string(dir.join("l.law")).unwrap();
        std::fs::write(
            dir.join("l.law"),
            law.replace(
                "law required valid(s:State):s.flag=true;",
                "law required valid(s:State,p:Bool) when p:s.flag;",
            ),
        )
        .unwrap();
        let r = execute(
            &dir,
            "out",
            &[
                "a=build(Fixed,on=@fixed/s)",
                "l=localize($a.object)",
                "e=diagnose($l.system)",
                "s=diagnose($l.system,side=semantic)",
                "n=needed($l)",
            ],
        );
        assert_eq!(
            r.code,
            match value {
                Some(true) => 0,
                Some(false) => 1,
                None => 2,
            },
            "{} {}",
            r.stdout,
            r.stderr
        );
        let result = result_json(&dir, &r);
        let answers = arr(get(&result, "answers"));
        if let Some(value) = value {
            let system = get(output(&result, 1, "system"), "value");
            let laws = arr(get(system, "laws"));
            assert_eq!(laws.len(), 2);
            let mut seen = vec![];
            for reference in laws {
                let law = get(node(&result, reference), "value");
                assert_eq!(s(get(law, "name")), "Fixed.valid");
                let binding = arr(get(law, "bindings"))
                    .iter()
                    .find(|b| s(get(b, "name")) == "p")
                    .unwrap();
                seen.push(
                    match &get(node(&result, get(binding, "value")), "value").value {
                        archsig::json::JValue::Bool(v) => *v,
                        _ => panic!("Bool binding"),
                    },
                );
            }
            assert!(seen.contains(&false));
            assert!(seen.contains(&true));
            for index in [2, 3] {
                assert_eq!(
                    s(get(&answers[index], "status")),
                    if value { "established" } else { "refuted" }
                );
                let diagnostic = get(output(&result, index, "diagnostic"), "value");
                let global = get(node(&result, get(diagnostic, "global")), "value");
                assert_eq!(
                    arr(get(get(global, "representation"), "values")).len(),
                    usize::from(value)
                );
            }
            let scope = get(&answers[1], "scope");
            let quantifiers = arr(get(scope, "quantifiers"));
            let p = quantifiers
                .iter()
                .find(|q| s(get(q, "name")) == "p")
                .unwrap();
            let domain = get(node(&result, get(p, "domain")), "value");
            assert_eq!(arr(get(domain, "elements")).len(), 2);
        } else {
            assert_eq!(s(get(&answers[1], "status")), "undetermined");
            assert!(!has(get(&answers[1], "outputs"), "system"));
            assert_eq!(arr(get(&answers[1], "reasons")).len(), 2);
            assert_eq!(s(get(&answers[4], "status")), "established");
        }
    }
}

#[test]
fn binding_a_boolean_answer_selects_one_law_instance_without_changing_the_universal_family() {
    let dir = input("local-finite-binding", Some(false));
    let law = std::fs::read_to_string(dir.join("l.law")).unwrap();
    std::fs::write(
        dir.join("l.law"),
        law.replace(
            "law required valid(s:State):s.flag=true;",
            "law required valid(s:State,p:Bool) when p:s.flag;",
        ),
    )
    .unwrap();
    let r = execute(
        &dir,
        "out",
        &[
            "a=build(Fixed,on=@fixed/s)",
            "v=evaluate(Fixed.current,s=@fixed/s)",
            "all=localize($a.object,law=Fixed.valid,s=@fixed/s)",
            "one=localize($a.object,law=Fixed.valid,s=@fixed/s,p=$v.value)",
            "da=diagnose($all.system)",
            "do=diagnose($one.system)",
        ],
    );
    assert_eq!(r.code, 1, "{} {}", r.stdout, r.stderr);
    let result = result_json(&dir, &r);
    let answers = arr(get(&result, "answers"));
    assert_eq!(
        arr(get(get(output(&result, 2, "system"), "value"), "laws")).len(),
        2
    );
    assert_eq!(
        arr(get(get(output(&result, 3, "system"), "value"), "laws")).len(),
        1
    );
    assert_eq!(s(get(&answers[4], "status")), "refuted");
    assert_eq!(s(get(&answers[5], "status")), "established");
}

#[test]
fn finite_parameter_product_and_saved_reuse_keep_all_four_instances() {
    let dir = input("local-finite-product", Some(false));
    let law = std::fs::read_to_string(dir.join("l.law")).unwrap();
    std::fs::write(
        dir.join("l.law"),
        law.replace(
            "law required valid(s:State):s.flag=true;",
            "law required valid(s:State,p:Bool,q:Bool) when p and q:s.flag;",
        ),
    )
    .unwrap();
    let asks = [
        "a=build(Fixed,on=@fixed/s)",
        "l=localize($a.object)",
        "d=diagnose($l.system)",
    ];
    let r = execute(&dir, "out", &asks);
    assert_eq!(r.code, 1, "{} {}", r.stdout, r.stderr);
    let before = result_json(&dir, &r);
    let system = get(output(&before, 1, "system"), "value");
    let laws = arr(get(system, "laws"));
    assert_eq!(laws.len(), 4);
    let pairs = laws
        .iter()
        .map(|r| {
            let instance = get(node(&before, r), "value");
            let value = |name| {
                let b = arr(get(instance, "bindings"))
                    .iter()
                    .find(|b| s(get(b, "name")) == name)
                    .unwrap();
                match get(node(&before, get(b, "value")), "value").value {
                    archsig::json::JValue::Bool(v) => v,
                    _ => panic!("Bool binding"),
                }
            };
            (value("p"), value("q"))
        })
        .collect::<std::collections::BTreeSet<_>>();
    assert_eq!(
        pairs,
        std::collections::BTreeSet::from([
            (false, false),
            (false, true),
            (true, false),
            (true, true)
        ])
    );
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
    ];
    for ask in asks {
        args.extend(["--ask", ask]);
    }
    let r = run(&dir, &args);
    assert_eq!(r.code, 1, "{} {}", r.stdout, r.stderr);
    let after = result_json(&dir, &r);
    for field in ["answers", "nodes"] {
        assert_eq!(get(&before, field).value, get(&after, field).value);
    }
}

fn explicit_local(dir: &std::path::Path, declaration: &str) {
    let path = dir.join("l.law");
    let law = std::fs::read_to_string(&path).unwrap();
    std::fs::write(
        path,
        law.replace("view current", &format!("{declaration} view current")),
    )
    .unwrap();
}
#[test]
fn explicit_direct_read_local_keeps_both_diagnostic_sides_and_base() {
    for value in [true, false] {
        let dir = input(
            if value {
                "explicit-local-true"
            } else {
                "explicit-local-false"
            },
            Some(value),
        );
        explicit_local(&dir, "local here(t:State) reads t.flag;");
        let r = execute(
            &dir,
            "out",
            &[
                "a=build(Fixed,on=@fixed/s)",
                "l=localize($a.object)",
                "e=diagnose($l.system)",
                "s=diagnose($l.system,side=semantic)",
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
        let j = result_json(&dir, &r);
        let answers = arr(get(&j, "answers"));
        for i in [2, 3] {
            assert_eq!(
                s(get(&answers[i], "status")),
                if value { "established" } else { "refuted" }
            );
        }
        assert_eq!(
            get(output(&j, 4, "value"), "value").value,
            archsig::json::JValue::Bool(value)
        );
        let system = get(output(&j, 1, "system"), "value");
        let context = get(node(&j, &arr(get(system, "contexts"))[0]), "value");
        let locals = arr(get(context, "locals"));
        assert_eq!(locals.len(), 1);
        assert_eq!(s(get(&locals[0], "declaration")), "Fixed.here");
        assert_eq!(s(get(&arr(get(&locals[0], "bindings"))[0], "name")), "t");
        assert_eq!(arr(get(context, "readings")).len(), 1);
    }
}
#[test]
fn explicit_reference_read_and_false_guard_report_visibility_not_missing_observations() {
    for (name, declaration) in [
        ("explicit-local-hidden", "local here(t:State) reads t;"),
        (
            "explicit-local-guard-false",
            "local here(t:State) when false reads t.flag;",
        ),
    ] {
        let dir = input(name, Some(true));
        explicit_local(&dir, declaration);
        let r = execute(
            &dir,
            "out",
            &[
                "a=build(Fixed,on=@fixed/s)",
                "l=localize($a.object)",
                "p=needed($l)",
                "v=evaluate(Fixed.current,on=$a.object,s=@fixed/s)",
            ],
        );
        assert_eq!(r.code, 2, "{} {}", r.stdout, r.stderr);
        let j = result_json(&dir, &r);
        let a = &arr(get(&j, "answers"))[1];
        assert_eq!(s(get(a, "status")), "undetermined");
        assert!(!has(get(a, "outputs"), "system"));
        let reasons = arr(get(a, "reasons"));
        assert!(reasons
            .iter()
            .any(|r| s(get(r, "code")) == "visibility_insufficient"));
        assert!(reasons.iter().all(|r| arr(get(r, "missing")).is_empty()));
        let plan = get(output(&j, 2, "plan"), "value");
        assert!(arr(get(plan, "requirements")).is_empty());
        assert!(!arr(get(plan, "blockers")).is_empty());
        assert_eq!(s(get(&arr(get(&j, "answers"))[3], "status")), "established");
    }
}
#[test]
fn explicit_read_missing_observation_remains_needed() {
    let dir = input("explicit-local-missing", None);
    explicit_local(&dir, "local here(t:State) reads t.flag;");
    let r = execute(
        &dir,
        "out",
        &[
            "a=build(Fixed,on=@fixed/s)",
            "l=localize($a.object)",
            "p=needed($l)",
        ],
    );
    assert_eq!(r.code, 2, "{} {}", r.stdout, r.stderr);
    let j = result_json(&dir, &r);
    assert!(!has(get(&arr(get(&j, "answers"))[1], "outputs"), "system"));
    let plan = get(output(&j, 2, "plan"), "value");
    let requirements = arr(get(plan, "requirements"));
    assert_eq!(requirements.len(), 1);
    assert_eq!(
        s(get(get(&requirements[0], "field"), "field")),
        "Fixed.State.flag"
    );
}

#[test]
fn explicit_local_guard_missing_is_an_observation_requirement_and_true_guard_reuses() {
    for flag in [None, Some(true)] {
        let dir = input("explicit-local-guard", flag);
        let law = std::fs::read_to_string(dir.join("l.law")).unwrap();
        std::fs::write(dir.join("l.law"), law.replace("s.flag=true", "true")).unwrap();
        explicit_local(&dir, "local here(t:State) when t.flag reads t.flag;");
        let asks = [
            "a=build(Fixed,on=@fixed/s)",
            "l=localize($a.object)",
            "p=needed($l)",
        ];
        let r = execute(&dir, "out", &asks);
        assert_eq!(
            r.code,
            if flag.is_some() { 0 } else { 2 },
            "{} {}",
            r.stdout,
            r.stderr
        );
        let j = result_json(&dir, &r);
        let plan = get(output(&j, 2, "plan"), "value");
        if flag.is_none() {
            assert_eq!(arr(get(plan, "requirements")).len(), 1);
            assert_eq!(
                s(get(
                    get(&arr(get(plan, "requirements"))[0], "field"),
                    "field"
                )),
                "Fixed.State.flag"
            );
            assert!(!has(get(&arr(get(&j, "answers"))[1], "outputs"), "system"));
        } else {
            assert!(arr(get(plan, "requirements")).is_empty());
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
            ];
            for ask in asks {
                args.extend(["--ask", ask]);
            }
            let reused = run(&dir, &args);
            assert_eq!(reused.code, 0, "{} {}", reused.stdout, reused.stderr);
            let again = result_json(&dir, &reused);
            for field in ["answers", "nodes"] {
                assert_eq!(get(&j, field).value, get(&again, field).value);
            }
        }
    }
}

fn multiple_read_input(
    name: &str,
    left: bool,
    right: Option<bool>,
    reads: &str,
) -> std::path::PathBuf {
    let definition = D.replace(
        r#""meaning":"観測値。"}"#,
        r#""meaning":"観測値。"},{"name":"other","type":"Bool","meaning":"別の観測値。"}"#,
    );
    let definitions = definition::check_definitions(&[("d", definition.as_bytes())]).unwrap();
    let digest = &definitions.vocabularies["Fixed"].digest;
    let dir = input(name, Some(left));
    std::fs::write(dir.join("d.json"), &definition).unwrap();
    let old = definition::check_definitions(&[("d", D.as_bytes())]).unwrap();
    let old_digest = &old.vocabularies["Fixed"].digest;
    let map = std::fs::read_to_string(dir.join("a.json"))
        .unwrap()
        .replace(old_digest, digest);
    let map = if let Some(v) = right {
        map.replace(r#""atoms":["#,&format!(r#""atoms":[{{"id":"other","subject":"s","field":"Fixed.State.other","value":{v},"origin":"model"}},"#))
    } else {
        map
    };
    std::fs::write(dir.join("a.json"), map).unwrap();
    let law = std::fs::read_to_string(dir.join("l.law"))
        .unwrap()
        .replace(old_digest, digest)
        .replace(
            "view current",
            "law required second(s:State):s.other=true; view current",
        );
    std::fs::write(dir.join("l.law"), law).unwrap();
    explicit_local(&dir, &format!("local here(t:State) reads {reads};"));
    dir
}
#[test]
fn explicit_multiple_reads_cover_distinct_law_supports_without_an_extra_patch() {
    for (left, right) in [(true, true), (true, false), (false, true)] {
        let dir = multiple_read_input("local-multiple-reads", left, Some(right), "t.flag,t.other");
        let r = execute(
            &dir,
            "out",
            &[
                "a=build(Fixed,on=@fixed/s)",
                "l=localize($a.object)",
                "e=diagnose($l.system)",
                "s=diagnose($l.system,side=semantic)",
            ],
        );
        assert_eq!(
            r.code,
            if left && right { 0 } else { 1 },
            "{} {}",
            r.stdout,
            r.stderr
        );
        let j = result_json(&dir, &r);
        for i in [2, 3] {
            assert_eq!(
                s(get(&arr(get(&j, "answers"))[i], "status")),
                if left && right {
                    "established"
                } else {
                    "refuted"
                }
            );
        }
        let system = get(output(&j, 1, "system"), "value");
        assert_eq!(arr(get(system, "laws")).len(), 2);
        assert_eq!(arr(get(system, "contexts")).len(), 1);
        let context = get(node(&j, &arr(get(system, "contexts"))[0]), "value");
        assert_eq!(arr(get(context, "locals")).len(), 1);
        assert_eq!(arr(get(context, "readings")).len(), 2);
        assert_eq!(arr(get(context, "dependencies")).len(), 2);
        assert_eq!(arr(get(context, "law_coordinates")).len(), 2);
        let cover = get(node(&j, get(system, "cover")), "value");
        assert_eq!(arr(get(cover, "patches")).len(), 1);
    }
}
#[test]
fn multiple_read_local_keeps_hidden_and_unobserved_fields_distinct() {
    for missing in [false, true] {
        let dir = multiple_read_input(
            "local-multiple-read-needed",
            true,
            if missing { None } else { Some(true) },
            if missing { "t.flag,t.other" } else { "t.flag" },
        );
        let r = execute(
            &dir,
            "out",
            &[
                "a=build(Fixed,on=@fixed/s)",
                "l=localize($a.object)",
                "p=needed($l)",
                "v=evaluate(Fixed.current,on=$a.object,s=@fixed/s)",
            ],
        );
        assert_eq!(r.code, 2, "{} {}", r.stdout, r.stderr);
        let j = result_json(&dir, &r);
        let answer = &arr(get(&j, "answers"))[1];
        assert!(!has(get(answer, "outputs"), "system"));
        let plan = get(output(&j, 2, "plan"), "value");
        if missing {
            let requirements = arr(get(plan, "requirements"));
            assert_eq!(requirements.len(), 1);
            assert_eq!(
                s(get(get(&requirements[0], "field"), "field")),
                "Fixed.State.other"
            );
            assert!(arr(get(answer, "reasons"))
                .iter()
                .all(|r| s(get(r, "code")) != "visibility_insufficient"));
        } else {
            assert!(arr(get(plan, "requirements")).is_empty());
            assert!(arr(get(answer, "reasons"))
                .iter()
                .any(|r| s(get(r, "code")) == "visibility_insufficient"));
        }
        assert_eq!(
            get(output(&j, 3, "value"), "value").value,
            archsig::json::JValue::Bool(true)
        );
    }
}

#[test]
fn product_reads_preserve_the_typed_coordinate_and_each_component() {
    for reads in ["(t.flag,t.other)", "((t.flag,unit),(t,t.other))"] {
        for (left, right) in [(true, true), (true, false), (false, true)] {
            let dir = multiple_read_input("local-product", left, Some(right), reads);
            let r = execute(
                &dir,
                "out",
                &[
                    "a=build(Fixed,on=@fixed/s)",
                    "l=localize($a.object)",
                    "e=diagnose($l.system)",
                    "s=diagnose($l.system,side=semantic)",
                ],
            );
            assert_eq!(
                r.code,
                if left && right { 0 } else { 1 },
                "{} {}",
                r.stdout,
                r.stderr
            );
            let j = result_json(&dir, &r);
            for i in [2, 3] {
                assert_eq!(
                    s(get(&arr(get(&j, "answers"))[i], "status")),
                    if left && right {
                        "established"
                    } else {
                        "refuted"
                    }
                );
            }
            if left && right {
                let reused = run(
                    &dir,
                    &[
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
                        "--ask",
                        "a=build(Fixed,on=@fixed/s)",
                        "--ask",
                        "l=localize($a.object)",
                        "--ask",
                        "e=diagnose($l.system)",
                        "--ask",
                        "s=diagnose($l.system,side=semantic)",
                    ],
                );
                assert_eq!(reused.code, 0, "{} {}", reused.stdout, reused.stderr);
                let again = result_json(&dir, &reused);
                for field in ["answers", "nodes"] {
                    assert_eq!(get(&j, field).value, get(&again, field).value);
                }
            }
            let system = get(output(&j, 1, "system"), "value");
            let context = get(node(&j, &arr(get(system, "contexts"))[0]), "value");
            let readings = arr(get(context, "readings"));
            assert_eq!(readings.len(), 1);
            assert_eq!(s(&arr(get(&readings[0], "type"))[0]), "Tuple");
            assert_eq!(arr(get(context, "dependencies")).len(), 2);
            assert_eq!(arr(get(context, "carrier")).len(), 1);
            let image = get(node(&j, get(&readings[0], "domain")), "value");
            assert_eq!(arr(get(image, "elements")).len(), 1);
            let value = get(node(&j, &arr(get(image, "elements"))[0]), "value");
            let tuple = arr(value);
            if reads == "(t.flag,t.other)" {
                assert_eq!(tuple[0].value, archsig::json::JValue::Bool(left));
                assert_eq!(tuple[1].value, archsig::json::JValue::Bool(right));
            } else {
                assert_eq!(arr(&tuple[0])[0].value, archsig::json::JValue::Bool(left));
                assert_eq!(arr(&tuple[1])[1].value, archsig::json::JValue::Bool(right));
            }
        }
    }
}
#[test]
fn product_read_does_not_publish_a_references_fields_or_fill_a_missing_component() {
    for missing in [false, true] {
        let dir = multiple_read_input(
            "local-product-needed",
            true,
            if missing { None } else { Some(true) },
            if missing {
                "(t.flag,t.other)"
            } else {
                "(t.flag,t)"
            },
        );
        let r = execute(
            &dir,
            "out",
            &[
                "a=build(Fixed,on=@fixed/s)",
                "l=localize($a.object)",
                "p=needed($l)",
            ],
        );
        assert_eq!(r.code, 2, "{} {}", r.stdout, r.stderr);
        let j = result_json(&dir, &r);
        let answer = &arr(get(&j, "answers"))[1];
        assert!(!has(get(answer, "outputs"), "system"));
        let plan = get(output(&j, 2, "plan"), "value");
        if missing {
            let requirements = arr(get(plan, "requirements"));
            assert_eq!(requirements.len(), 1);
            assert_eq!(
                s(get(get(&requirements[0], "field"), "field")),
                "Fixed.State.other"
            );
        } else {
            assert!(arr(get(plan, "requirements")).is_empty());
            assert!(arr(get(answer, "reasons"))
                .iter()
                .any(|r| s(get(r, "code")) == "visibility_insufficient"));
        }
    }
}

fn diagnostic_compare_input(name: &str, identity: bool, valid: bool) -> std::path::PathBuf {
    #[path = "common/architecture_environment.rs"]
    mod fixture;
    use archsig::canonical::Json;
    let map = fixture::changed_map(|j| {
        if identity {
            for a in fixture::atoms(j) {
                let Json::Obj(o) = a else { panic!("atom") };
                match o.get("id") {
                    Some(Json::Str(id)) if id == "m-to" => {
                        o.insert(
                            "value".into(),
                            Json::Arr(vec![Json::str("v"), Json::str("A")]),
                        );
                    }
                    Some(Json::Str(id)) if id == "m-states" || id == "m-reserves" => {
                        let Json::Arr(pairs) = o.get_mut("value").unwrap() else {
                            panic!("pairs")
                        };
                        for pair in pairs {
                            let Json::Arr(p) = pair else { panic!("pair") };
                            p[1] = p[0].clone();
                        }
                    }
                    _ => {}
                }
            }
        }
    });
    let input = fixture::input(
        &format!(
            "law optional localValid(s:State):s.free={};",
            if valid { 2 } else { 3 }
        ),
        Some(&map),
    );
    let dir = workdir(name);
    for (name, bytes) in [
        ("d.json", input.definitions()[0].bytes()),
        ("l.law", input.law().bytes()),
        ("a.json", input.archmap().bytes()),
    ] {
        std::fs::write(dir.join(name), bytes).unwrap();
    }
    dir
}
#[test]
fn finite_diagnostics_compare_actual_identity_maps_on_both_sides_and_reuse() {
    for valid in [true, false] {
        for side in ["semantic", "equation"] {
            for degree in [0, 1] {
                let dir = diagnostic_compare_input(
                    &format!("diagnostic-compare-{valid}-{side}-{degree}"),
                    true,
                    valid,
                );
                let d1 = format!("d1=diagnose($l.system,side={side},degree={degree})");
                let d2 = format!("d2=diagnose($l.system,side={side},degree={degree})");
                let asks = [
                    "m=map(Reservations.Migration,on=@v/m,reading=Reservations)",
                    "l=localize($m.candidate.source,law=Reservations.localValid,s=@v/p)",
                    &d1,
                    &d2,
                    "c=compare($d1.diagnostic,to=$d2.diagnostic,kind=diagnostics,along=$m.operation)",
                ];
                let r = execute(&dir, "out", &asks);
                assert_eq!(
                    r.code,
                    if !valid && degree == 1 { 1 } else { 0 },
                    "{} {}",
                    r.stdout,
                    r.stderr
                );
                let result = result_json(&dir, &r);
                let answers = arr(get(&result, "answers"));
                assert_eq!(s(get(&answers[4], "status")), "established");
                let comparison = get(output(&result, 4, "comparison"), "value");
                assert_eq!(s(get(comparison, "kind")), "diagnostics");
                assert_eq!(
                    get(comparison, "along").value,
                    get(get(&answers[0], "outputs"), "operation").value
                );
                let finite = get(node(&result, get(comparison, "finite_map")), "value");
                assert_eq!(arr(get(finite, "pairs")).len(), usize::from(valid));
                assert_eq!(get(finite, "source").value, get(finite, "target").value);
                let conditions = arr(get(comparison, "conditions"));
                assert_eq!(conditions.len(), 3);
                for condition in conditions {
                    assert_eq!(
                        s(get(get(node(&result, condition), "judgment"), "status")),
                        "established"
                    );
                }
                let inverse = get(node(&result, &conditions[1]), "value");
                let operands = arr(get(inverse, "operands"));
                for reference in operands {
                    let map = get(node(&result, reference), "value");
                    assert_eq!(arr(get(map, "pairs")).len(), usize::from(valid));
                }
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
                for ask in asks {
                    args.extend(["--ask", ask]);
                }
                let reused = run(&dir, &args);
                assert_eq!(reused.code, r.code, "{} {}", reused.stdout, reused.stderr);
                let again = result_json(&dir, &reused);
                assert_eq!(get(&again, "answers").value, get(&result, "answers").value);
                assert_eq!(get(&again, "nodes").value, get(&result, "nodes").value);
            }
        }
    }
}
#[test]
fn finite_diagnostic_comparison_does_not_invent_general_transport() {
    let dir = diagnostic_compare_input("diagnostic-compare-unsupported", false, true);
    let r = execute(
        &dir,
        "out",
        &[
            "m=map(Reservations.Migration,on=@v/m,reading=Reservations)",
            "l=localize($m.candidate.source,law=Reservations.localValid,s=@v/p)",
            "d=diagnose($l.system)",
            "c=compare($d.diagnostic,to=$d.diagnostic,kind=diagnostics,along=$m.operation)",
            "v=evaluate(Reservations.no)",
        ],
    );
    assert_eq!(r.code, 2, "{} {}", r.stdout, r.stderr);
    let result = result_json(&dir, &r);
    let answers = arr(get(&result, "answers"));
    assert_eq!(s(get(&answers[3], "status")), "undetermined");
    assert!(!has(get(&answers[3], "outputs"), "comparison"));
    assert!(format!("{:?}", get(&answers[3], "reasons")).contains("unsupported_algorithm"));
    assert_eq!(s(get(&answers[4], "status")), "established");
}
#[test]
fn finite_diagnostic_comparison_rejects_incompatible_degree_side_and_non_operation() {
    let dir = diagnostic_compare_input("diagnostic-compare-signature", true, true);
    for (index, d2, along) in [
        (0, "d2=diagnose($l.system,degree=0)", "$m.operation"),
        (1, "d2=diagnose($l.system,side=semantic)", "$m.operation"),
        (2, "d2=diagnose($l.system)", "$m.candidate"),
    ] {
        let compare =
            format!("c=compare($d1.diagnostic,to=$d2.diagnostic,kind=diagnostics,along={along})");
        let r = execute(
            &dir,
            &format!("out{index}"),
            &[
                "m=map(Reservations.Migration,on=@v/m,reading=Reservations)",
                "l=localize($m.candidate.source,law=Reservations.localValid,s=@v/p)",
                "d1=diagnose($l.system)",
                d2,
                &compare,
            ],
        );
        assert_eq!(r.code, 64, "{} {}", r.stdout, r.stderr);
    }
}

#[test]
fn matching_display_values_do_not_replace_the_operation_action_or_system_identity() {
    use archsig::canonical::Json;
    #[path = "common/architecture_environment.rs"]
    mod fixture;
    let dir = diagnostic_compare_input("diagnostic-compare-moved-positions", true, true);
    let path = dir.join("a.json");
    let mut map = fixture::owned(&archsig::json::parse(&std::fs::read(&path).unwrap()).unwrap());
    for a in fixture::atoms(&mut map) {
        let Json::Obj(o) = a else { panic!("atom") };
        match o.get("id") {
            Some(Json::Str(id)) if id == "m-states" || id == "m-reserves" => {
                let Json::Arr(pairs) = o.get_mut("value").unwrap() else {
                    panic!("pairs")
                };
                for pair in pairs {
                    let Json::Arr(pair) = pair else {
                        panic!("pair")
                    };
                    let Json::Arr(target) = &mut pair[1] else {
                        panic!("ref")
                    };
                    let Json::Str(subject) = &target[1] else {
                        panic!("subject")
                    };
                    target[1] = Json::str(match subject.as_str() {
                        "p" => "q",
                        "q" => "p",
                        "e" => "h",
                        "h" => "e",
                        "k" => "h",
                        _ => panic!("unexpected subject"),
                    });
                }
            }
            // 両点の値を同じにしても、局所系の参照先を動かした事実は消えない。
            Some(Json::Str(id)) if id == "q-free" => {
                o.insert("value".into(), Json::str("2"));
            }
            Some(Json::Str(id)) if id == "q-held" => {
                o.insert("value".into(), Json::str("0"));
            }
            _ => {}
        }
    }
    std::fs::write(path, map.canonical()).unwrap();
    let r = execute(
        &dir,
        "out",
        &[
            "m=map(Reservations.Migration,on=@v/m,reading=Reservations)",
            "l=localize($m.candidate.source,law=Reservations.localValid,s=@v/p)",
            "d=diagnose($l.system)",
            "c=compare($d.diagnostic,to=$d.diagnostic,kind=diagnostics,along=$m.operation)",
        ],
    );
    assert_eq!(r.code, 2, "{} {}", r.stdout, r.stderr);
    let result = result_json(&dir, &r);
    let answers = arr(get(&result, "answers"));
    assert!(has(get(&answers[0], "outputs"), "operation"));
    assert_eq!(s(get(&answers[2], "status")), "established");
    assert_eq!(s(get(&answers[3], "status")), "undetermined");
    assert!(format!("{:?}", get(&answers[3], "reasons")).contains("unsupported_algorithm"));
    let dir = diagnostic_compare_input("diagnostic-compare-different-system", true, true);
    let r = execute(
        &dir,
        "out",
        &[
            "m=map(Reservations.Migration,on=@v/m,reading=Reservations)",
            "l=localize($m.candidate.source,law=Reservations.localValid,s=@v/p)",
            "k=localize($m.candidate.source,law=Reservations.localValid,s=@v/p)",
            "d1=diagnose($l.system)",
            "d2=diagnose($k.system)",
            "c=compare($d1.diagnostic,to=$d2.diagnostic,kind=diagnostics,along=$m.operation)",
        ],
    );
    assert_eq!(r.code, 2, "{} {}", r.stdout, r.stderr);
    let result = result_json(&dir, &r);
    let answer = &arr(get(&result, "answers"))[5];
    assert_eq!(s(get(answer, "status")), "undetermined");
    assert!(format!("{:?}", get(answer, "reasons")).contains("unsupported_algorithm"));
}

fn implicit_multiple_input(name: &str, left: bool, right: Option<bool>) -> std::path::PathBuf {
    let dir = multiple_read_input(name, left, right, "t.flag,t.other");
    let path = dir.join("l.law");
    let law = std::fs::read_to_string(&path).unwrap();
    std::fs::write(
        path,
        law.replace("local here(t:State) reads t.flag,t.other;", ""),
    )
    .unwrap();
    dir
}

#[test]
fn implicit_support_cover_has_actual_intersections_and_matching_families() {
    for (left, right) in [(true, true), (false, true), (true, false)] {
        let dir = implicit_multiple_input("implicit-cover", left, Some(right));
        let r = execute(
            &dir,
            "out",
            &[
                "a=build(Fixed,on=@fixed/s)",
                "l=localize($a.object)",
                "e=diagnose($l.system)",
                "s=diagnose($l.system,side=semantic)",
                "v=evaluate(Fixed.current,on=$e.diagnostic.global.domain.base,s=@fixed/s)",
            ],
        );
        assert_eq!(
            r.code,
            if left && right { 0 } else { 1 },
            "{} {}",
            r.stdout,
            r.stderr
        );
        let j = result_json(&dir, &r);
        let system = get(output(&j, 1, "system"), "value");
        assert_eq!(arr(get(system, "contexts")).len(), 4);
        assert_eq!(arr(get(system, "maps")).len(), 9);
        let cover = get(node(&j, get(system, "cover")), "value");
        let patches = arr(get(cover, "patches"));
        assert_eq!(patches.len(), 2);
        assert!(patches.iter().all(|p| p.value != get(cover, "base").value));
        assert_eq!(arr(get(cover, "overlaps")).len(), 4);
        let topology = get(node(&j, get(system, "topology")), "value");
        assert_eq!(arr(get(topology, "covering_sieves")).len(), 5);
        let bottom = arr(get(system, "contexts"))
            .iter()
            .map(|r| get(node(&j, r), "value"))
            .find(|v| arr(get(v, "dependencies")).is_empty())
            .unwrap();
        assert_eq!(arr(get(bottom, "carrier")).len(), 1);
        assert!(arr(get(bottom, "law_coordinates")).is_empty());
        for patch in patches {
            let p = get(node(&j, patch), "value");
            assert_eq!(arr(get(p, "dependencies")).len(), 1);
            assert_eq!(arr(get(p, "law_coordinates")).len(), 1);
        }
        for check in arr(get(system, "sheaf_checks")) {
            assert_eq!(
                s(get(
                    get(node(&j, get(check, "proposition")), "judgment"),
                    "status"
                )),
                "established"
            );
        }
        for i in [2, 3] {
            assert_eq!(
                s(get(&arr(get(&j, "answers"))[i], "status")),
                if left && right {
                    "established"
                } else {
                    "refuted"
                }
            );
            let diagnostic = get(output(&j, i, "diagnostic"), "value");
            let matching = get(node(&j, get(diagnostic, "matching")), "value");
            assert_eq!(
                arr(get(matching, "elements")).len(),
                usize::from(left && right)
            );
            if left && right {
                let tuple = node(&j, &arr(get(matching, "elements"))[0]);
                assert_eq!(arr(get(tuple, "value")).len(), 2);
            }
        }
        assert_eq!(
            get(output(&j, 4, "value"), "value").value,
            archsig::json::JValue::Bool(left)
        );
    }
}

#[test]
fn implicit_support_cover_preserves_missing_and_saved_reuse() {
    for right in [Some(true), None] {
        let dir = implicit_multiple_input("implicit-cover-reuse", true, right);
        let asks = [
            "a=build(Fixed,on=@fixed/s)",
            "l=localize($a.object)",
            "d=diagnose($l.system)",
            "n=needed($l)",
        ];
        let first = execute(&dir, "out", &asks);
        assert_eq!(
            first.code,
            if right.is_some() { 0 } else { 2 },
            "{} {}",
            first.stdout,
            first.stderr
        );
        let before = result_json(&dir, &first);
        if right.is_none() {
            assert!(!has(
                get(&arr(get(&before, "answers"))[1], "outputs"),
                "system"
            ));
            let plan = get(output(&before, 3, "plan"), "value");
            assert!(
                arr(get(plan, "requirements"))
                    .iter()
                    .any(|r| s(get(get(r, "field"), "field")) == "Fixed.State.other")
            );
        }
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
        ];
        for ask in asks {
            args.extend(["--ask", ask]);
        }
        let second = run(&dir, &args);
        assert_eq!(
            second.code, first.code,
            "{} {}",
            second.stdout, second.stderr
        );
        let after = result_json(&dir, &second);
        for field in ["answers", "nodes"] {
            assert_eq!(get(&before, field).value, get(&after, field).value);
        }
    }
}

#[test]
fn support_closure_stop_retains_completed_contexts_without_claiming_a_system() {
    use archsig::observed::{control::{Checkpoint,Control,Limits,Usage},evaluate::evaluate_observed_bytes,input::InputSources};
    use std::{cell::Cell,rc::Rc};
    let dir=implicit_multiple_input("implicit-closure-stop",true,Some(true));
    let sources=||InputSources::from_bytes(vec![std::fs::read(dir.join("d.json")).unwrap()],std::fs::read(dir.join("l.law")).unwrap(),std::fs::read(dir.join("a.json")).unwrap());
    let asks=["a=build(Fixed,on=@fixed/s)","l=localize($a.object)"];
    let seen=Rc::new(Cell::new(0usize)); let count=seen.clone();
    let mut control=Control::new(Limits::default(),move |point| {if point==Checkpoint::Localize {count.set(count.get()+1);} Usage::default()});
    let normal=evaluate_observed_bytes(sources(),&asks,&mut control).unwrap();
    assert_eq!(normal.status(),"complete");
    let total=seen.get();
    for mode in 0..3 {
        let mut retained=false;
        // 実際の実行長から途中位置を選ぶ。特定のcheckpoint件数を契約にしない。
        for stop in [total/4,total/2,total*3/4] {
            let mut count=0;
            let mut control=Control::new(Limits {time_ms:Some(1),memory_mib:Some(1)},move |point| {
                if point==Checkpoint::Localize {count+=1;}
                if count>=stop {match mode {
                    0=>Usage {elapsed_ms:2,..Usage::default()},
                    1=>Usage {memory_mib:2,..Usage::default()},
                    _=>Usage {signal:Some(archsig::result::Signal::Term),..Usage::default()},
                }}else{Usage::default()}
            });
            let partial=evaluate_observed_bytes(sources(),&asks,&mut control).unwrap();
            let j=archsig::json::parse(partial.wire().canonical().as_bytes()).unwrap();
            let answer=&arr(get(&j,"answers"))[1];
            let contexts=arr(get(&j,"nodes")).iter().filter(|n|s(get(get(n,"rule"),"name"))=="context").count();
            if !has(get(answer,"outputs"),"system") && contexts>0 {
                retained=true;
                assert_eq!(s(get(answer,"status")),"undetermined");
                assert!(!has(answer,"claim"));
                let reason=arr(get(answer,"reasons")).iter().find(|r|s(get(r,"code"))==if mode==2 {"cancelled"}else{"budget_exhausted"}).unwrap();
                assert!(!arr(get(reason,"dependencies")).is_empty());
                for r in arr(get(reason,"dependencies")) {node(&j,r);}
                assert!(arr(get(&j,"nodes")).iter().all(|n|s(get(get(n,"rule"),"name"))!="local_system"));
                break;
            }
        }
        assert!(retained,"mode {mode}, checkpoints {total}: closure fragments were lost");
    }
}
