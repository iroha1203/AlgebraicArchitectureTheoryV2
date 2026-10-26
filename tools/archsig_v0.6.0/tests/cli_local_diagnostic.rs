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
                let json = internal_graph(&dir, &json);
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
    let scope = get(&arr(get(&json, "answers"))[1], "scope");
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
        s(get(equation_solution, "type")),
        "EquationSolutionSet"
    );
    let cover = get(node(&json, get(system, "cover")), "value");
    for overlap in arr(get(cover, "overlaps")) {
        assert_eq!(s(get(node(&json, overlap), "type")), "Overlap");
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
fn universal_laws_localize_fixed_objects_without_enumerating_numbers() {
    for ty in ["Z", "Q"] {
        for explicit in [false,true] {
        for (predicate, truth) in [("z=z", true), ("z=w", false), ("(let a=z+w in a=w+z) and s.free=s.free", true)] {
            let dir=if ty=="Q" {rational_compare_input("universal-fixed-q",true)} else {diagnostic_compare_input("universal-fixed-z",true,true)};
            let digest=definition::check_definitions(&[("d",&std::fs::read(dir.join("d.json")).unwrap())]).unwrap().vocabularies["Reservations"].digest.clone();
            let local=if explicit {"local here(t:State) reads t.free;"} else {""};
            let law=format!("law \"archsig.law/2\" semantics \"archsig/0.6.0\"; reading Reservations {{ use vocabulary Reservations version \"1\" digest \"{digest}\"; view two():{ty}=2; {local} law required valid(z:{ty},s:State,w:{ty}):{predicate}; }}");
            std::fs::write(dir.join("l.law"),law).unwrap();
            let asks=["a=map(Reservations.Migration,on=@v/m,reading=Reservations)","l=localize($a.candidate.source)","e=diagnose($l.system,degree=0)","s=diagnose($l.system,side=semantic,degree=0)"];
            if predicate=="z=z" {
                let mut args=vec!["run","--atom-definition","d.json","--archmap","a.json","--law","l.law"];
                for ask in asks {args.extend(["--ask",ask]);}
                let normal=run(&dir,&args);assert_eq!(normal.code,0,"{}",normal.stdout);
                assert!(normal.stderr.is_empty());assert_eq!(std::fs::read_dir(&dir).unwrap().count(),3);
                assert_eq!(s(get(&normal.receipt,"format")),"archsig.summary/1");
                eprintln!("universal-fixed {ty} stdout={} bytes",normal.stdout.len());
            }
            let r=execute(&dir,"out",&asks);
            assert_eq!(r.code,0,"{ty} {predicate}: {} {}",r.stdout,r.stderr);
            let j=result_json(&dir,&r);
            let system=get(output(&j,1,"system"),"value");
            for (states,solutions) in [("equation_states","solutions"),("semantic_states","parameters")] {
                let state=&arr(get(system,states))[0];
                let values=get(node(&j,get(state,solutions)),"value");
                assert_eq!(arr(get(get(values,"representation"),"values")).is_empty(),!truth);
            }
            let scope=get(&arr(get(&j,"answers"))[1],"scope");
            for name in ["z","w"] {
                assert!(arr(get(scope,"quantifiers")).iter().any(|q|s(get(q,"name"))==name && !has(q,"domain")));
            }
            let mut args=vec!["run","--atom-definition","d.json","--archmap","a.json","--law","l.law","--out","again","--reuse","out"];
            for ask in asks {args.extend(["--ask",ask]);}
            let reused=run(&dir,&args);assert_eq!(reused.code,r.code,"{}",reused.stdout);
            let again=result_json(&dir,&reused);for field in ["answers","nodes"] {assert_eq!(get(&j,field).value,get(&again,field).value);}
            if predicate=="z=w" {
                let bound=execute(&dir,"bound",&[asks[0],"n=evaluate(Reservations.two,on=$a.candidate.source)","l=localize($a.candidate.source,law=Reservations.valid,z=$n.value,w=$n.value)","d=diagnose($l.system,degree=0)"]);
                assert_eq!(bound.code,0,"{}",bound.stdout);
                let j=result_json(&dir,&bound);
                let system=get(output(&j,2,"system"),"value");
                for (states,key) in [("equation_states","solutions"),("semantic_states","parameters")] {
                    let state=&arr(get(system,states))[0];let solution=get(node(&j,get(state,key)),"value");
                    assert_eq!(arr(get(get(solution,"representation"),"values")).len(),1);
                }
            }
        }
        }
    }
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
        assert!(!has(instance, "guard"));
        let internal = internal_graph(&dir, &result);
        let system = get(output(&internal, 1, "system"), "value");
        let context = get(node(&internal, &arr(get(system, "contexts"))[0]), "value");
        let instance = get(node(&internal, &arr(get(context, "law_coordinates"))[0]), "value");
        assert_eq!(
            s(get(node(&internal, get(instance, "guard")), "type")),
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
                    let result = internal_graph(&dir, &result);
                    let claim = node(&result, get(&arr(get(&result,"answers"))[index], "claim"));
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
fn matching_values_require_identity_action_while_repeated_plans_compare() {
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
    assert_eq!(r.code, 0, "{} {}", r.stdout, r.stderr);
    let result = result_json(&dir, &r);
    let answer = &arr(get(&result, "answers"))[5];
    assert_eq!(s(get(answer, "status")), "established");
    let cmp = get(output(&result, 5, "comparison"), "value");
    let map = get(node(&result, get(cmp, "finite_map")), "value");
    node(&result,get(map,"source")); node(&result,get(map,"target"));
    let pairs = arr(get(map, "pairs"));
    assert_eq!(pairs.len(), 1);
    let pair = arr(&pairs[0]);
    node(&result,&pair[0]); node(&result,&pair[1]);
    assert_eq!(get(node(&result, &pair[0]), "value").value,
        get(node(&result, &pair[1]), "value").value);
    for condition in arr(get(cmp, "conditions")) {
        assert_eq!(s(get(get(node(&result, condition), "judgment"), "status")), "established");
    }
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
    use archsig::observed::{
        control::{Checkpoint, Control, Limits, Usage},
        evaluate::evaluate_observed_bytes,
        input::InputSources,
    };
    use std::{cell::Cell, rc::Rc};
    for finite in [false, true] {
        let dir = implicit_multiple_input("implicit-closure-stop", true, Some(true));
        if finite {
            explicit_local(
                &dir,
                "change choose(t:State,b:Bool,c:Bool)=t with {flag=b,other=c};",
            );
        }
        let sources = || {
            InputSources::from_bytes(
                vec![std::fs::read(dir.join("d.json")).unwrap()],
                std::fs::read(dir.join("l.law")).unwrap(),
                std::fs::read(dir.join("a.json")).unwrap(),
            )
        };
        let asks = [
            "a=build(Fixed,on=@fixed/s)",
            if finite {
                "l=localize($a.object,using=Fixed.choose)"
            } else {
                "l=localize($a.object)"
            },
        ];
        let seen = Rc::new(Cell::new(0usize));
        let count = seen.clone();
        let mut control = Control::new(Limits::default(), move |point| {
            if point == Checkpoint::Localize {
                count.set(count.get() + 1);
            }
            Usage::default()
        });
        let normal = evaluate_observed_bytes(sources(), &asks, &mut control).unwrap();
        assert_eq!(normal.status(), "complete");
        let total = seen.get();
        for mode in 0..3 {
            let mut retained = false;
            // 実際の実行長から途中位置を選ぶ。特定のcheckpoint件数を契約にしない。
            for stop in 1..total {
                let mut count = 0;
                let mut control = Control::new(
                    Limits {
                        time_ms: Some(1),
                        memory_mib: Some(1),
                    },
                    move |point| {
                        if point == Checkpoint::Localize {
                            count += 1;
                        }
                        if count >= stop {
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
                let partial = evaluate_observed_bytes(sources(), &asks, &mut control).unwrap();
                let j = archsig::json::parse(partial.wire().canonical().as_bytes()).unwrap();
                let answer = &arr(get(&j, "answers"))[1];
                assert!(
                    arr(get(answer, "reasons"))
                        .iter()
                        .all(|r| s(get(r, "code")) != "internal"),
                    "stop {stop}/{total}: {answer:?}"
                );
                let contexts = arr(get(&j, "nodes"))
                    .iter()
                    .filter(|n| {
                        matches!(&get(n, "type").value, archsig::json::JValue::Str(t) if t == "Context")
                            && has(get(n, "value"), "readings")
                            && !arr(get(get(n, "value"), "readings")).is_empty()
                    })
                    .count();
                if !has(get(answer, "outputs"), "system") && contexts > 0 {
                    retained = true;
                    assert_eq!(s(get(answer, "status")), "undetermined");
                    assert!(!has(answer, "claim"));
                    let reason = arr(get(answer, "reasons"))
                        .iter()
                        .find(|r| {
                            s(get(r, "code"))
                                == if mode == 2 {
                                    "cancelled"
                                } else {
                                    "budget_exhausted"
                                }
                        })
                        .unwrap_or_else(|| panic!("stop {stop}/{total}: {answer:?}"));
                    assert!(!arr(get(reason, "dependencies")).is_empty());
                    for r in arr(get(reason, "dependencies")) {
                        node(&j, r);
                    }
                    assert!(
                        arr(get(&j, "nodes"))
                            .iter()
                            .all(|n| !matches!(&get(n, "type").value, archsig::json::JValue::Str(t) if t == "LocalSystem"))
                    );
                }
            }
            assert!(
                retained,
                "mode {mode}, checkpoints {total}: closure fragments were lost"
            );
        }
    }
}

#[test]
fn explicit_distinct_local_declarations_form_the_selected_cover() {
    for (left, right) in [(true, true), (true, false), (false, true)] {
        let dir = implicit_multiple_input("explicit-distinct-cover", left, Some(right));
        explicit_local(
            &dir,
            "local left(t:State) reads t.flag; local right(t:State) reads t.other; local skipped(t:State) when false reads t;",
        );
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
        let system = get(output(&j, 1, "system"), "value");
        assert_eq!(arr(get(system, "contexts")).len(), 4);
        let cover = get(node(&j, get(system, "cover")), "value");
        assert_eq!(arr(get(cover, "patches")).len(), 2);
        for patch in arr(get(cover, "patches")) {
            assert_ne!(patch.value, get(cover, "base").value);
            let context = get(node(&j, patch), "value");
            assert_eq!(arr(get(context, "locals")).len(), 1);
            assert_eq!(arr(get(context, "law_coordinates")).len(), 1);
            assert_eq!(arr(get(context, "readings")).len(), 1);
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
        }
        if left && right {
            let r = run(
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
            assert_eq!(r.code, 0, "{} {}", r.stdout, r.stderr);
            let after = result_json(&dir, &r);
            for field in ["answers", "nodes"] {
                assert_eq!(get(&j, field).value, get(&after, field).value);
            }
        }
    }
}

#[test]
fn explicit_cover_does_not_turn_union_dependencies_into_a_visible_law() {
    for hidden in [false, true] {
        let dir = implicit_multiple_input("explicit-cover-hidden", true, Some(true));
        let path = dir.join("l.law");
        let law = std::fs::read_to_string(&path)
            .unwrap()
            .replace("s.flag=true", "s.flag and s.other")
            .replace("law required second(s:State):s.other=true;", "");
        std::fs::write(path, law).unwrap();
        explicit_local(
            &dir,
            if hidden {
                "local left(t:State) when t.other reads t.flag; local right(t:State) reads t;"
            } else {
                "local left(t:State) reads t.flag; local right(t:State) reads t.other;"
            },
        );
        let r = execute(
            &dir,
            "out",
            &[
                "a=build(Fixed,on=@fixed/s)",
                "l=localize($a.object)",
                "n=needed($l)",
            ],
        );
        assert_eq!(r.code, 2, "{} {}", r.stdout, r.stderr);
        let j = result_json(&dir, &r);
        let answer = &arr(get(&j, "answers"))[1];
        assert!(!has(get(answer, "outputs"), "system"));
        assert!(
            arr(get(answer, "reasons"))
                .iter()
                .any(|r| s(get(r, "code")) == "visibility_insufficient")
        );
        let plan = get(output(&j, 2, "plan"), "value");
        assert!(arr(get(plan, "requirements")).is_empty());
    }
}

#[test]
fn tuple_intersections_retain_typed_component_projections() {
    for nested in [false, true] {
        for flag in [true, false] {
            let dir = implicit_multiple_input("tuple-intersection", flag, Some(true));
            let original = std::fs::read_to_string(dir.join("d.json")).unwrap();
            let definition = original.replace(
                r#""meaning":"別の観測値。"}"#,
                r#""meaning":"別の観測値。"},{"name":"third","type":"Bool","meaning":"第三の観測値。"}"#,
            );
            let old = definition::check_definitions(&[("d", original.as_bytes())]).unwrap();
            let new = definition::check_definitions(&[("d", definition.as_bytes())]).unwrap();
            std::fs::write(dir.join("d.json"), &definition).unwrap();
            for file in ["a.json", "l.law"] {
                let text = std::fs::read_to_string(dir.join(file)).unwrap()
                    .replace(&old.vocabularies["Fixed"].digest, &new.vocabularies["Fixed"].digest)
                    .replace("law required second(s:State):s.other=true;", "")
                    .replace(r#""atoms":["#, r#""atoms":[{"id":"third","subject":"s","field":"Fixed.State.third","value":true,"origin":"model"},"#);
                std::fs::write(dir.join(file), text).unwrap();
            }
            explicit_local(
                &dir,
                if nested {
                    "local left(t:State) reads ((t.flag,t.other),unit); local right(t:State) reads ((t.flag,t.third),unit);"
                } else {
                    "local left(t:State) reads (t.flag,t.other); local right(t:State) reads (t.flag,t.third);"
                },
            );
            let asks = [
                "a=build(Fixed,on=@fixed/s)",
                "l=localize($a.object)",
                "e=diagnose($l.system)",
                "s=diagnose($l.system,side=semantic)",
            ];
            let r = execute(&dir, "out", &asks);
            assert_eq!(
                r.code,
                if flag { 0 } else { 1 },
                "{} {}",
                r.stdout,
                r.stderr
            );
            let j = result_json(&dir, &r);
            let system = get(output(&j, 1, "system"), "value");
            assert_eq!(arr(get(system, "contexts")).len(), 4);
            let intersection = arr(get(system, "contexts"))
                .iter()
                .map(|r| get(node(&j, r), "value"))
                .find(|v| arr(get(v, "dependencies")).len() == 1)
                .unwrap();
            assert_eq!(
                s(get(&arr(get(intersection, "dependencies"))[0], "field")),
                "Fixed.State.flag"
            );
            assert_eq!(arr(get(intersection, "law_coordinates")).len(), 1);
            let readings = arr(get(intersection, "readings"));
            assert_eq!(readings.len(), if nested { 2 } else { 1 });
            let reading = readings
                .iter()
                .find(
                    |v| matches!(&get(v,"type").value, archsig::json::JValue::Str(t) if t=="Bool"),
                )
                .unwrap();
            let expression = get(node(&j, get(reading, "expression")), "value");
            assert_eq!(s(get(expression, "operation")), "project");
            let operand = get(node(&j, &arr(get(expression, "operands"))[0]), "value");
            if nested {
                assert_eq!(s(get(operand, "operation")), "project");
            }
            let image = get(node(&j, get(reading, "domain")), "value");
            assert_eq!(arr(get(image, "elements")).len(), 1);
            assert_eq!(
                get(node(&j, &arr(get(image, "elements"))[0]), "value").value,
                archsig::json::JValue::Bool(flag)
            );
            for i in [2, 3] {
                assert_eq!(
                    s(get(&arr(get(&j, "answers"))[i], "status")),
                    if flag { "established" } else { "refuted" }
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
            let reused = run(&dir, &args);
            assert_eq!(reused.code, r.code, "{} {}", reused.stdout, reused.stderr);
            let after = result_json(&dir, &reused);
            for field in ["answers", "nodes"] {
                assert_eq!(get(&j, field).value, get(&after, field).value);
            }
        }
    }
}

#[test]
fn tuple_component_support_excludes_other_bound_subjects() {
    for declaration in [
        "local left(t:State,u:Left[t]) reads (t.flag,u.flag); local right(t:State,v:Right[t]) reads (t.flag,v.flag);",
        "local left(t:State,u:Left[t]) reads t.flag,u.flag; local right(t:State,v:Right[t]) reads t.flag,v.flag;",
    ] {
        let dir = input("tuple-component-bindings", Some(true));
        let mut entities = String::new();
        for entity in ["Left", "Right"] {
            entities.push_str(&format!(r#"{{"kind":"entity","name":"Fixed.{entity}","meaning":"補助対象。","parameters":[{{"name":"owner","type":["Ref","Fixed.State"],"meaning":"所属。"}}],"fields":[{{"name":"flag","type":"Bool","meaning":"補助値。"}}],"alignments":[]}},"#));
        }
        let definition = D.replace(
            r#""declarations":["#,
            &format!(r#""declarations":[{entities}"#),
        );
        let old = definition::check_definitions(&[("d", D.as_bytes())]).unwrap();
        let new = definition::check_definitions(&[("d", definition.as_bytes())]).unwrap();
        std::fs::write(dir.join("d.json"), definition).unwrap();
        for file in ["a.json", "l.law"] {
            let mut text = std::fs::read_to_string(dir.join(file)).unwrap().replace(
                &old.vocabularies["Fixed"].digest,
                &new.vocabularies["Fixed"].digest,
            );
            if file == "a.json" {
                for (subject, ty) in [("u", "Left"), ("v", "Right")] {
                    text = text.replace(
                    r#""subjects":["#,
                    &format!(
                        r#""subjects":[{{"id":"{subject}","type":"Fixed.{ty}","origin":"model"}},"#
                    ),
                );
                    text = text.replace(r#""atoms":["#,&format!(r#""atoms":[{{"id":"{subject}-owner","subject":"{subject}","field":"Fixed.{ty}.owner","value":["fixed","s"],"origin":"model"}},{{"id":"{subject}-flag","subject":"{subject}","field":"Fixed.{ty}.flag","value":true,"origin":"model"}},"#));
                }
            }
            std::fs::write(dir.join(file), text).unwrap();
        }
        explicit_local(
            &dir,
            &format!(
                "view left_value(u:Left):Bool=u.flag; view right_value(v:Right):Bool=v.flag; {declaration}"
            ),
        );
        let r = execute(
            &dir,
            "out",
            &[
                "a=build(Fixed,on=@fixed/s)",
                "l=localize($a.object)",
                "e=diagnose($l.system)",
            ],
        );
        assert_eq!(r.code, 0, "{} {}", r.stdout, r.stderr);
        let j = result_json(&dir, &r);
        let system = get(output(&j, 1, "system"), "value");
        assert_eq!(arr(get(system, "contexts")).len(), 4);
        let intersection = arr(get(system, "contexts"))
            .iter()
            .map(|r| get(node(&j, r), "value"))
            .find(|v| arr(get(v, "carrier")).len() == 1)
            .unwrap();
        assert_eq!(arr(get(intersection, "law_coordinates")).len(), 1);
        assert_eq!(
            arr(get(intersection, "readings")).len(),
            if declaration.contains("reads (") {
                1
            } else {
                2
            }
        );
        let reading = &arr(get(intersection, "readings"))[0];
        assert_eq!(s(get(reading, "type")), "Bool");
        if declaration.contains("reads (") {
            assert_eq!(
                s(get(
                    get(node(&j, get(reading, "expression")), "value"),
                    "operation"
                )),
                "project"
            );
        }
        let image = get(node(&j, get(reading, "domain")), "value");
        assert_eq!(
            get(node(&j, &arr(get(image, "elements"))[0]), "value").value,
            archsig::json::JValue::Bool(true)
        );
    }
}

#[test]
fn finite_change_local_states_distinguish_the_action_image_from_free_equations() {
    for explicit in 0..3 {
    for correlated in [false, true] {
        let dir = implicit_multiple_input("finite-change-local", false, Some(false));
        explicit_local(
            &dir,
            if correlated {
                "change choose(t:State,b:Bool)=t with {flag=b,other=not b};"
            } else {
                "change choose(t:State,b:Bool,c:Bool)=t with {flag=b,other=c};"
            },
        );
        if explicit != 0 { explicit_local(&dir, if explicit == 1 { "local Flag(t:State) reads t.flag; local Other(t:State) reads t.other;" } else { "local Flag(t:State) reads t.flag; local Other(t:State) when (t.flag or not t.flag) reads t.other;" }); }
        let r = execute(
            &dir,
            "out",
            &[
                "a=build(Fixed,on=@fixed/s)",
                "l=localize($a.object,using=Fixed.choose)",
                "e=diagnose($l.system)",
                "s=diagnose($l.system,side=semantic)",
            ],
        );
        assert_eq!(
            r.code,
            if correlated { 1 } else { 0 },
            "{} {}",
            r.stdout,
            r.stderr
        );
        let j = result_json(&dir, &r);
        assert_eq!(s(get(&arr(get(&j, "answers"))[1], "status")), "established");
        assert_eq!(s(get(&arr(get(&j, "answers"))[2], "status")), "established");
        assert_eq!(
            s(get(&arr(get(&j, "answers"))[3], "status")),
            if correlated { "refuted" } else { "established" }
        );
        let system = get(output(&j, 1, "system"), "value");
        assert_eq!(s(get(system, "change")), "Fixed.choose");
        assert_eq!(arr(get(system, "contexts")).len(), 4);
        let sem = get(output(&j, 3, "diagnostic"), "value");
        let matching = get(node(&j, get(sem, "matching")), "value");
        assert_eq!(arr(get(matching, "elements")).len(), 1);
        let global = get(node(&j, get(sem, "global")), "value");
        assert_eq!(
            arr(get(get(global, "representation"), "values")).len(),
            if correlated { 0 } else { 1 }
        );
        let candidate = get(node(&j, get(global, "domain")), "value");
        let parameters = get(node(&j, get(candidate, "parameters")), "value");
        assert_eq!(
            arr(get(parameters, "elements")).len(),
            if correlated { 2 } else { 4 }
        );
        let cover = get(node(&j, get(system, "cover")), "value");
        for patch in arr(get(cover, "patches")) {
            let state = arr(get(system, "semantic_states"))
                .iter()
                .find(|v| get(v, "context").value == patch.value)
                .unwrap();
            let image = get(node(&j, get(state, "state_image")), "value");
            assert_eq!(arr(get(image, "elements")).len(), 1);
        }
        let fibers = arr(get(sem, "fibers"));
        assert_eq!(fibers.len(), 1);
        let fiber = get(node(&j, get(&fibers[0], "preimage")), "value");
        assert_eq!(
            arr(get(get(fiber, "representation"), "values")).len(),
            if correlated { 0 } else { 1 }
        );
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
                "l=localize($a.object,using=Fixed.choose)",
                "--ask",
                "e=diagnose($l.system)",
                "--ask",
                "s=diagnose($l.system,side=semantic)",
            ],
        );
        assert_eq!(reused.code, r.code, "{} {}", reused.stdout, reused.stderr);
        let after = result_json(&dir, &reused);
        for field in ["answers", "nodes"] {
            assert_eq!(get(&j, field).value, get(&after, field).value);
        }
        for scope in ["cover", "topology"] {
            let checks = arr(get(system, "sheaf_checks"));
            let _propositions = ["semantic", "equation"].map(|side| {
                let check = checks.iter().find(|v| s(get(v,"scope"))==scope && s(get(v,"side"))==side).unwrap();
                let proposition = get(node(&j,get(check,"proposition")),"value");
                let operands = arr(get(proposition,"operands"));
                let maps = arr(get(system,"restrictions")).iter().filter(|v| s(get(v,"side"))==side).map(|v| get(v,"map")).collect::<Vec<_>>();
                assert_eq!(operands.len(), maps.len()+1);
                for operand in &operands[1..] {
                    assert!(maps.iter().any(|map| map.value==operand.value));
                }
                proposition
            });
        }
        let check = arr(get(system, "sheaf_checks"))
            .iter()
            .find(|v| s(get(v, "scope")) == "cover" && s(get(v, "side")) == "semantic")
            .unwrap();
        assert_eq!(
            s(get(
                get(node(&j, get(check, "proposition")), "judgment"),
                "status"
            )),
            if correlated { "refuted" } else { "established" }
        );
    }
}
}

#[test]
fn finite_local_state_uniqueness_does_not_make_assignment_unique_or_fill_fixed_missing() {
    for missing in [false, true] {
        let dir = implicit_multiple_input(
            "finite-local-assignment",
            false,
            if missing { None } else { Some(true) },
        );
        explicit_local(
            &dir,
            "change choose(t:State,b:Bool,ignored:Bool)=t with {flag=b};",
        );
        let r = execute(
            &dir,
            "out",
            &[
                "a=build(Fixed,on=@fixed/s)",
                "l=localize($a.object,using=Fixed.choose)",
                "s=diagnose($l.system,side=semantic)",
                "n=needed($l)",
                "r=repair(Fixed.valid,on=$a.object,using=Fixed.choose)",
            ],
        );
        assert_eq!(
            r.code,
            if missing { 2 } else { 1 },
            "{} {}",
            r.stdout,
            r.stderr
        );
        let j = result_json(&dir, &r);
        if missing {
            assert!(!has(get(&arr(get(&j, "answers"))[1], "outputs"), "system"));
            let plan = get(output(&j, 3, "plan"), "value");
            assert!(
                arr(get(plan, "requirements"))
                    .iter()
                    .any(|v| s(get(get(v, "field"), "field")) == "Fixed.State.other")
            );
        } else {
            assert_eq!(s(get(&arr(get(&j, "answers"))[2], "status")), "established");
            let diagnostic = get(output(&j, 2, "diagnostic"), "value");
            let global = get(node(&j, get(diagnostic, "global")), "value");
            assert_eq!(arr(get(get(global, "representation"), "values")).len(), 2);
            let restriction = get(node(&j, get(diagnostic, "restriction")), "value");
            assert_eq!(arr(get(restriction, "pairs")).len(), 1);
            let repair = &arr(get(&j, "answers"))[4];
            assert_eq!(s(get(repair, "status")), "refuted");
            assert!(!has(get(repair, "outputs"), "object"));
        }
    }
}

#[test]
fn finite_matching_fibers_keep_original_assignments_for_each_state() {
    let dir = input("finite-local-fibers", Some(false));
    let path = dir.join("l.law");
    let law = std::fs::read_to_string(&path)
        .unwrap()
        .replace("s.flag=true", "s.flag=s.flag");
    std::fs::write(path, law).unwrap();
    explicit_local(
        &dir,
        "change choose(t:State,b:Bool,ignored:Bool)=t with {flag=b};",
    );
    let r = execute(
        &dir,
        "out",
        &[
            "a=build(Fixed,on=@fixed/s)",
            "l=localize($a.object,using=Fixed.choose)",
            "e=diagnose($l.system)",
            "s=diagnose($l.system,side=semantic)",
        ],
    );
    assert_eq!(r.code, 0, "{} {}", r.stdout, r.stderr);
    let j = result_json(&dir, &r);
    for (i, count) in [(2, 1), (3, 2)] {
        let diagnostic = get(output(&j, i, "diagnostic"), "value");
        let fibers = arr(get(diagnostic, "fibers"));
        assert_eq!(fibers.len(), 2);
        let mut all = vec![];
        for fiber in fibers {
            let preimage = get(node(&j, get(fiber, "preimage")), "value");
            let values = arr(get(get(preimage, "representation"), "values"));
            assert_eq!(values.len(), count);
            for value in values {
                assert!(!all.contains(&&value.value));
                all.push(&value.value);
            }
        }
        let global = get(node(&j, get(diagnostic, "global")), "value");
        assert_eq!(
            arr(get(get(global, "representation"), "values")).len(),
            all.len()
        );
    }
}

#[test]
fn finite_change_unknown_owner_keeps_the_observation_requirement() {
    #[path = "common/architecture_environment.rs"]
    mod fixture;
    let map = fixture::remove_atom("p-owner");
    let input = fixture::input(
        "law optional localValid(s:State):true=true; change choose(t:State,b:Bool)=t with {free=0};",
        Some(&map),
    );
    let dir = workdir("finite-local-owner-domain");
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
            "l=localize($m.candidate.source,law=Reservations.localValid,using=Reservations.choose)",
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
fn finite_change_short_circuit_keeps_fixed_missing_observations() {
    for expression in ["(s.other and false)=false", "(s.other or true)=true"] {
        for value in [None, Some(false), Some(true)] {
            let dir = implicit_multiple_input("finite-local-short", false, value);
            let path = dir.join("l.law");
            let law = std::fs::read_to_string(&path).unwrap().replace("s.other=true", expression);
            std::fs::write(path, law).unwrap();
            explicit_local(&dir, "change choose(t:State,b:Bool)=t with {flag=b};");
            let r = execute(&dir, "out", &[
                "a=build(Fixed,on=@fixed/s)",
                "l=localize($a.object,using=Fixed.choose)",
                "d=diagnose($l.system)",
                "n=needed($l)",
            ]);
            assert_eq!(r.code, if value.is_some() { 0 } else { 2 }, "{} {}", r.stdout, r.stderr);
            let j = result_json(&dir, &r);
            let answers = arr(get(&j, "answers"));
            if value.is_none() {
                assert!(!has(get(&answers[1], "outputs"), "system"));
                assert!(!has(get(&answers[2], "outputs"), "diagnostic"));
                assert_eq!(s(get(&answers[1], "status")), "undetermined");
                let plan = get(output(&j, 3, "plan"), "value");
                assert!(arr(get(plan, "requirements")).iter().any(|r| {
                    let f = get(r, "field");
                    s(get(f, "subject")) == "s" && s(get(f, "field")) == "Fixed.State.other"
                }));
            } else {
                assert_eq!(s(get(&answers[2], "status")), "established");
            }
        }
    }
}

#[test]
fn finite_change_preserves_unbound_law_domains_and_bound_selection_in_scope() {
    let dir = input("finite-local-quantifiers", Some(true));
    explicit_local(&dir, "law optional scoped(s:State,p:Bool) when p:s.flag; change choose(t:State,b:Bool)=t with {flag=b};");
    let asks = [
        "a=build(Fixed,on=@fixed/s)",
        "v=evaluate(Fixed.current,s=@fixed/s)",
        "all=localize($a.object,law=Fixed.scoped,using=Fixed.choose,s=@fixed/s)",
        "one=localize($a.object,law=Fixed.scoped,using=Fixed.choose,s=@fixed/s,p=$v.value)",
        "da=diagnose($all.system)",
        "do=diagnose($one.system)",
    ];
    let r = execute(&dir, "out", &asks);
    assert_eq!(r.code, 0, "{} {}", r.stdout, r.stderr);
    let result = result_json(&dir, &r);
    let answers = arr(get(&result, "answers"));
    let named = |index: usize| arr(get(get(&answers[index], "scope"), "quantifiers")).iter().filter(|q| s(get(q,"name")) == "p").collect::<Vec<_>>();
    let all = named(2);
    assert_eq!(all.len(), 1);
    assert!(named(3).is_empty());
    let added = all[0];
    assert_eq!(s(get(added, "kind")), "forall");
    let values = arr(get(get(node(&result, get(added,"domain")),"value"),"elements"));
    assert_eq!(values.len(), 2);
    assert!(values.iter().any(|r| matches!(get(node(&result,r),"value").value, archsig::json::JValue::Bool(false))));
    assert!(values.iter().any(|r| matches!(get(node(&result,r),"value").value, archsig::json::JValue::Bool(true))));
    for (index, count) in [(2, 2), (3, 1)] {
        assert_eq!(arr(get(get(output(&result,index,"system"),"value"),"laws")).len(), count);
    }
    let mut args = vec!["run","--atom-definition","d.json","--archmap","a.json","--law","l.law","--out","again","--reuse","out"];
    for ask in &asks { args.extend(["--ask", *ask]); }
    let r = run(&dir, &args);
    assert_eq!(r.code, 0, "{} {}", r.stdout, r.stderr);
    let after = result_json(&dir, &r);
    for field in ["answers", "nodes"] { assert_eq!(get(&result,field).value,get(&after,field).value); }
}

#[test]
fn unused_updated_field_has_a_typed_singleton_reading_and_actual_free_image() {
    for constant in [false, true] {
        let dir = implicit_multiple_input("finite-unused-slot", true, Some(false));
        let path = dir.join("l.law");
        let law = std::fs::read_to_string(&path).unwrap().replace("law required second(s:State):s.other=true;", "");
        std::fs::write(path,law).unwrap();
        explicit_local(&dir, if constant {
            "change choose(t:State,b:Bool)=t with {flag=b,other=false};"
        } else {
            "change choose(t:State,b:Bool,c:Bool)=t with {flag=b,other=c};"
        });
        let asks = ["a=build(Fixed,on=@fixed/s)","l=localize($a.object,using=Fixed.choose)","e=diagnose($l.system)","s=diagnose($l.system,side=semantic)"];
        let r = execute(&dir,"out",&asks);
        assert_eq!(r.code,0,"{} {}",r.stdout,r.stderr);
        let j = result_json(&dir,&r);
        let system = get(output(&j,1,"system"),"value");
        let cover = get(node(&j,get(system,"cover")),"value");
        let context = arr(get(cover,"patches")).iter().map(|r| get(node(&j,r),"value")).find(|v| {
            let deps = arr(get(v,"dependencies"));
            deps.len()==1 && s(get(&deps[0],"field"))=="Fixed.State.other"
        }).unwrap();
        let reading = arr(get(context,"readings")).iter().find(|r| {
            let e = get(node(&j,get(r,"expression")),"value");
            s(get(e,"kind"))=="source" && s(get(get(e,"location"),"input"))=="definition0"
        }).unwrap();
        assert_eq!(s(get(reading,"type")),"Bool");
        let expr = get(node(&j,get(reading,"expression")),"value");
        assert_eq!(s(get(get(expr,"location"),"pointer")),"/vocabularies/0/declarations/0/fields/1");
        let bindings = arr(get(expr,"bindings"));
        assert_eq!(bindings.len(),1);
        let subject = get(node(&j,get(&bindings[0],"value")),"value");
        assert_eq!(s(&arr(subject)[1]),"s");
        let image = get(node(&j,get(reading,"domain")),"value");
        let elements = arr(get(image,"elements"));
        assert_eq!(elements.len(),2);
        for expected in [false,true] {
            assert!(elements.iter().any(|r| matches!(get(node(&j,r),"value").value,archsig::json::JValue::Bool(v) if v==expected)));
        }
        for (i,count) in [(2,2),(3,if constant {1} else {2})] {
            let d = get(output(&j,i,"diagnostic"),"value");
            let global = get(node(&j,get(d,"global")),"value");
            assert_eq!(arr(get(get(global,"representation"),"values")).len(),count);
        }
        let mut args = vec!["run","--atom-definition","d.json","--archmap","a.json","--law","l.law","--out","again","--reuse","out"];
        for ask in &asks { args.extend(["--ask",*ask]); }
        let r = run(&dir,&args);
        assert_eq!(r.code,0,"{} {}",r.stdout,r.stderr);
        let after = result_json(&dir,&r);
        for field in ["answers","nodes"] { assert_eq!(get(&j,field).value,get(&after,field).value); }
    }
}

#[test]
fn finite_implicit_intersections_keep_only_the_read_expressions_bindings() {
    for (explicit, chain) in [(false,false),(true,false),(true,true)] {
        let dir = input("finite-read-bindings", Some(true));
        let mut entities = String::new();
        for entity in ["Left", "Right"] {
            entities.push_str(&format!(r#"{{"kind":"entity","name":"Fixed.{entity}","meaning":"補助対象。","parameters":[{{"name":"owner","type":["Ref","Fixed.State"],"meaning":"所属。"}}],"fields":[{{"name":"flag","type":"Bool","meaning":"補助値。"}}],"alignments":[]}},"#));
        }
        let definition = D.replace(
            r#""declarations":["#,
            &format!(r#""declarations":[{entities}"#),
        );
        let old = definition::check_definitions(&[("d", D.as_bytes())]).unwrap();
        let new = definition::check_definitions(&[("d", definition.as_bytes())]).unwrap();
        std::fs::write(dir.join("d.json"), definition).unwrap();
        for file in ["a.json", "l.law"] {
            let mut text = std::fs::read_to_string(dir.join(file)).unwrap().replace(
                &old.vocabularies["Fixed"].digest,
                &new.vocabularies["Fixed"].digest,
            );
            if file == "a.json" {
                for (subject, ty) in [("u", "Left"), ("v", "Right")] {
                    text = text.replace(
                    r#""subjects":["#,
                    &format!(
                        r#""subjects":[{{"id":"{subject}","type":"Fixed.{ty}","origin":"model"}},"#
                    ),
                );
                    text = text.replace(r#""atoms":["#,&format!(r#""atoms":[{{"id":"{subject}-owner","subject":"{subject}","field":"Fixed.{ty}.owner","value":["fixed","s"],"origin":"model"}},{{"id":"{subject}-flag","subject":"{subject}","field":"Fixed.{ty}.flag","value":true,"origin":"model"}},"#));
                }
            }
            std::fs::write(dir.join(file), text).unwrap();
        }

    let path=dir.join("l.law");
    let law=std::fs::read_to_string(&path).unwrap().replace("law required valid(s:State):s.flag=true;", "");
    std::fs::write(path,law).unwrap();
    explicit_local(&dir,"law required left(t:State,u:Left[t]):t.flag=u.flag; law required right(t:State,v:Right[t]):t.flag=v.flag; change choose(t:State,b:Bool)=t with {flag=b};");
    if explicit {
        let reads="local LeftRead(t:State,u:Left[t]) reads (t.flag,u.flag,u.owner); local RightRead(t:State,v:Right[t]) reads (t.flag,v.flag,v.owner);";
        let reads=if chain { reads.replacen("t.flag","u.owner.flag",1).replacen("t.flag","v.owner.flag",1) } else { reads.to_owned() };
        explicit_local(&dir,&reads);
    }
    let asks=["a=build(Fixed,on=@fixed/s)","l=localize($a.object,using=Fixed.choose)","e=diagnose($l.system)","s=diagnose($l.system,side=semantic)"];
    let r=execute(&dir,"out",&asks);
    let j=result_json(&dir,&r);
    assert_eq!(r.code,0,"{} {} {:?}",r.stdout,r.stderr,get(&j,"answers"));
    let system=get(output(&j,1,"system"),"value");
    let intersection=arr(get(system,"contexts")).iter().map(|r|get(node(&j,r),"value")).find(|v|arr(get(v,"carrier")).len()==1).unwrap();
    let readings=arr(get(intersection,"readings"));
    assert_eq!(readings.len(),if explicit {1} else {2});
    for reading in readings {
        assert_eq!(s(get(reading,"type")),"Bool");
        let expression=get(node(&j,get(reading,"expression")),"value");
        if explicit {
            if !chain { assert_eq!(s(get(expression,"operation")), "project"); }
            else {
                assert_eq!(s(get(expression,"kind")),"source");
                let binding=&arr(get(expression,"bindings"))[0];
                let subject=arr(get(node(&j,get(binding,"value")),"value"));
                assert_eq!((s(&subject[0]),s(&subject[1])),("fixed","s"));
                assert_eq!(s(get(get(expression,"location"),"pointer")),"/vocabularies/0/declarations/2/fields/0");
            }
        } else {
        let bindings=arr(get(expression,"bindings"));
        assert_eq!(bindings.len(),1);
        assert_eq!(s(get(&bindings[0],"name")),"t");
        let subject=get(node(&j,get(&bindings[0],"value")),"value");
        assert_eq!(s(&arr(subject)[1]),"s");
        }
        let image=get(node(&j,get(reading,"domain")),"value");
        let values=arr(get(image,"elements"));
        assert_eq!(values.len(),2);
        for expected in [false,true] {
            assert!(values.iter().any(|r|matches!(get(node(&j,r),"value").value,archsig::json::JValue::Bool(v) if v==expected)));
        }
    }
    let mut args=vec!["run","--atom-definition","d.json","--archmap","a.json","--law","l.law","--out","again","--reuse","out"];
    for ask in &asks {args.extend(["--ask",*ask]);}
    let r=run(&dir,&args);
    assert_eq!(r.code,0,"{} {}",r.stdout,r.stderr);
    let after=result_json(&dir,&r);
    for field in ["answers","nodes"] {assert_eq!(get(&j,field).value,get(&after,field).value);}
}
}

#[test]
fn finite_explicit_local_keeps_visibility_and_variable_guard_limits() {
    for (local, expected) in [
        ("local Flag(t:State) reads t.flag;", "visibility_insufficient"),
        ("local Flag(t:State) when t.flag reads t.flag; local Other(t:State) reads t.other;", "unsupported_algorithm"),
    ] {
        let dir = implicit_multiple_input("finite-explicit-limit", false, Some(false));
        explicit_local(&dir, &format!("{local} change choose(t:State,b:Bool,c:Bool)=t with {{flag=b,other=c}};"));
        let r = execute(&dir, "out", &["a=build(Fixed,on=@fixed/s)", "l=localize($a.object,using=Fixed.choose)", "n=needed($l)"]);
        assert_eq!(r.code, 2, "{} {}", r.stdout, r.stderr);
        let j = result_json(&dir,&r);
        let local = &arr(get(&j,"answers"))[1];
        assert!(!has(get(local,"outputs"),"system"));
        assert!(arr(get(local,"reasons")).iter().any(|reason| s(get(reason,"code")) == expected));
        let plan = get(output(&j,2,"plan"),"value");
        assert!(arr(get(plan,"requirements")).is_empty());
    }
}

#[test]
fn finite_explicit_read_keeps_a_missing_fixed_field_in_needed() {
    for failure in 0..6 {
    let dir = multiple_read_input("finite-explicit-missing", failure != 5, None, if failure == 2 { "t.other,not t.flag" } else { "t.flag,t.other" });
    let path=dir.join("l.law");
    let law=std::fs::read_to_string(&path).unwrap().replace("law required second(s:State):s.other=true;", "");
    std::fs::write(path,law).unwrap();
    explicit_local(&dir,"change choose(t:State,b:Bool)=t with {flag=b};");
    if failure == 1 { explicit_local(&dir,"local zzz(t:State) when t.flag reads t.flag;"); }
    if failure == 3 {
        let path=dir.join("l.law");
        let law=std::fs::read_to_string(&path).unwrap().replace("local here(t:State) reads t.flag,t.other;", "local here(t:State,b:Bool) when (not b or t.flag) reads (t.flag,t.other);");
        std::fs::write(path,law).unwrap();
    }
    if failure >= 4 {
        let path=dir.join("l.law");
        let guard = if failure == 4 { "(t.flag and t.other)" } else { "(if t.flag then t.other else false)" };
        let law=std::fs::read_to_string(&path).unwrap().replace("local here(t:State) reads t.flag,t.other;", &format!("local here(t:State) when {guard} reads t.flag;"));
        std::fs::write(path,law).unwrap();
    }
    let asks = ["a=build(Fixed,on=@fixed/s)", "l=localize($a.object,law=Fixed.valid,using=Fixed.choose)", "n=needed($l)"];
    let r=execute(&dir,"out",&asks);
    assert_eq!(r.code,2,"{} {}",r.stdout,r.stderr);
    let j=result_json(&dir,&r);
    let local=&arr(get(&j,"answers"))[1];
    assert!(!has(get(local,"outputs"),"system"));
    assert!(arr(get(local,"reasons")).iter().any(|r|s(get(r,"code"))=="missing_observation"));
    if failure != 0 { assert!(arr(get(local,"reasons")).iter().any(|r|s(get(r,"code"))=="unsupported_algorithm")); }
    let plan=get(output(&j,2,"plan"),"value");
    assert!(arr(get(plan,"requirements")).iter().any(|r|s(get(get(r,"field"),"field"))=="Fixed.State.other"));
    let mut args=vec!["run","--atom-definition","d.json","--archmap","a.json","--law","l.law","--out","again","--reuse","out"];
    for ask in asks {args.extend(["--ask",ask]);}
    let r=run(&dir,&args);
    assert_eq!(r.code,2,"{} {}",r.stdout,r.stderr);
    let after=result_json(&dir,&r);
    for field in ["answers","nodes"] {assert_eq!(get(&j,field).value,get(&after,field).value);}
}
}

#[test]
fn finite_explicit_read_stop_keeps_the_missing_field_already_observed() {
    use archsig::observed::{control::{Checkpoint, Control, Limits, Usage}, evaluate::evaluate_observed_bytes, input::InputSources};
    use std::{cell::Cell, rc::Rc};
    let dir = multiple_read_input("explicit-read-stop", true, None, "t.other");
    let path = dir.join("l.law");
    let law = std::fs::read_to_string(&path).unwrap().replace("law required second(s:State):s.other=true;", "");
    std::fs::write(path, law).unwrap();
    explicit_local(&dir, "change choose(t:State,b:Bool)=t with {flag=b};");
    let sources = || InputSources::from_bytes(vec![std::fs::read(dir.join("d.json")).unwrap()], std::fs::read(dir.join("l.law")).unwrap(), std::fs::read(dir.join("a.json")).unwrap());
    let asks = ["a=build(Fixed,on=@fixed/s)", "l=localize($a.object,law=Fixed.valid,using=Fixed.choose)"];
    let seen = Rc::new(Cell::new(0usize));
    let count = seen.clone();
    let mut control = Control::new(Limits::default(), move |point| {
        if point == Checkpoint::Localize { count.set(count.get()+1); }
        Usage::default()
    });
    let normal = evaluate_observed_bytes(sources(), &asks, &mut control).unwrap();
    let j = archsig::json::parse(normal.wire().canonical().as_bytes()).unwrap();
    assert!(arr(get(&arr(get(&j,"answers"))[1],"reasons")).iter().any(|r| s(get(r,"code")) == "missing_observation"));
    let missing = arr(get(&arr(get(&j,"answers"))[1],"reasons")).iter().find(|r| s(get(r,"code")) == "missing_observation").unwrap();
    let expression = s(get(&arr(get(missing,"dependencies"))[0],"node")).to_owned();
    // 読取り式の生成位置を求め、その後の式評価を経た次のstate境界で止める。
    let mut last = None;
    for stop in 1..seen.get() {
        let mut count = 0;
        let mut control = Control::new(Limits { time_ms: Some(1), memory_mib: None }, move |point| {
            if point == Checkpoint::Localize { count += 1; }
            Usage { elapsed_ms: if count >= stop { 2 } else { 0 }, ..Usage::default() }
        });
        let partial = evaluate_observed_bytes(sources(), &asks, &mut control).unwrap();
        let j = archsig::json::parse(partial.wire().canonical().as_bytes()).unwrap();
        if arr(get(&j,"nodes")).iter().any(|n| s(get(n,"id")) == expression) {
            last = Some(stop);
            break;
        }
    }
    let last = last.expect("読取り開始の停止点");
    for mode in 0..3 {
        let mut count = 0;
        let mut read_started = false;
        let mut stopped = false;
        let mut control = Control::new(Limits { time_ms: Some(1), memory_mib: Some(1) }, move |point| {
            if point == Checkpoint::Localize {
                count += 1;
                stopped |= read_started;
            } else if point == Checkpoint::FiniteIteration && count >= last {
                read_started = true;
            }
            if !stopped { return Usage::default(); }
            match mode {
                0 => Usage { elapsed_ms: 2, ..Usage::default() },
                1 => Usage { memory_mib: 2, ..Usage::default() },
                _ => Usage { signal: Some(archsig::result::Signal::Term), ..Usage::default() },
            }
        });
        let partial = evaluate_observed_bytes(sources(), &asks, &mut control).unwrap();
        let j = archsig::json::parse(partial.wire().canonical().as_bytes()).unwrap();
        let answer = &arr(get(&j,"answers"))[1];
        assert_eq!(s(get(answer,"status")), "undetermined");
        assert!(!has(get(answer,"outputs"),"system"));
        let reasons = arr(get(answer,"reasons"));
        assert!(reasons.iter().any(|r| s(get(r,"code")) == if mode == 2 { "cancelled" } else { "budget_exhausted" }));
        let missing = reasons.iter().find(|r| s(get(r,"code")) == "missing_observation").unwrap_or_else(|| panic!("mode {mode}: {answer:?}"));
        assert!(format!("{missing:?}").contains("Fixed.State.other"));
    }
}

#[test]
fn finite_explicit_local_keeps_unpublished_guard_dependencies_fixed() {
    let dir = multiple_read_input("explicit-fixed-guard", true, Some(false), "t.other");
    let path = dir.join("l.law");
    let law = std::fs::read_to_string(&path).unwrap().replace("local here(t:State) reads t.other;", "local here(t:State) when t.flag reads t.other;");
    std::fs::write(path,law).unwrap();
    explicit_local(&dir, "change choose(t:State,b:Bool)=t with {other=b};");
    let r = execute(&dir,"out", &["a=build(Fixed,on=@fixed/s)", "l=localize($a.object,law=Fixed.second,using=Fixed.choose)", "d=diagnose($l.system)"]);
    assert_eq!(r.code,0,"{} {}",r.stdout,r.stderr);
    let j = result_json(&dir,&r);
    let system = get(output(&j,1,"system"),"value");
    let context = get(node(&j,&arr(get(system,"contexts"))[0]),"value");
    assert!(arr(get(context,"dependencies")).iter().any(|slot| s(get(slot,"field"))=="Fixed.State.flag"));
    let diagnostic = get(output(&j,2,"diagnostic"),"value");
    let solutions = get(node(&j,get(diagnostic,"global")),"value");
    let equations = get(node(&j,get(solutions,"domain")),"value");
    assert!(arr(get(equations,"fixed")).iter().any(|slot| s(get(slot,"field"))=="Fixed.State.flag"));
    assert_eq!(arr(get(equations,"variables")).len(),1);
}

#[test]
fn explicit_local_reference_chain_reads_reach_actual_point_coordinates() {
    #[path = "common/three_edge.rs"]
    mod triangle;
    for (label, missing, atom) in [
        ("known",None,""),
        ("reference",Some("Coordinates.Shift.from"),r#",{"id":"a-Shift.from","subject":"a","field":"Coordinates.Shift.from","value":["triangle","p"],"origin":"model"}"#),
        ("value",Some("Coordinates.Point.coordinate"),r#",{"id":"p-Point.coordinate","subject":"p","field":"Coordinates.Point.coordinate","value":"0","origin":"model"}"#),
    ] {
        let input=triangle::input(Some(2));
        let dir=workdir(&format!("local-reference-chain-{label}"));
        for (name,bytes) in [("d.json",input.definitions()[0].bytes()),("l.law",input.law().bytes()),("a.json",input.archmap().bytes())] {
            let mut text=String::from_utf8(bytes.to_vec()).unwrap();
            if name=="a.json" && missing.is_some() {
                assert!(text.contains(atom));
                text=text.replace(atom,"");
            }
            std::fs::write(dir.join(name),text).unwrap();
        }
        let asks=["a=build(Coordinates,on=@triangle/root)","l=localize($a.object)","d=diagnose($l.system)","n=needed($l)"];
        let r=execute(&dir,"out",&asks);
        let j=result_json(&dir,&r);
        assert_eq!(r.code,if missing.is_some(){2}else{1},"{} {} {:?}",r.stdout,r.stderr,get(&j,"answers"));
        if let Some(field)=missing {
            let plan=get(output(&j,3,"plan"),"value");
            assert!(arr(get(plan,"requirements")).iter().any(|r|s(get(get(r,"field"),"field"))==field));
        } else {
            assert!(has(get(&arr(get(&j,"answers"))[1],"outputs"),"system"));
            assert!(has(get(&arr(get(&j,"answers"))[2],"outputs"),"diagnostic"));
            let system=get(output(&j,1,"system"),"value");
            let mut shared=std::collections::BTreeSet::new();
            for context in arr(get(system,"contexts")) {
                for reading in arr(get(get(node(&j,context),"value"),"readings")) {
                    let expression=get(node(&j,get(reading,"expression")),"value");
                    if !has(expression,"location") {continue;}
                    let location=get(expression,"location");
                    if !has(location,"pointer") || s(get(location,"pointer"))!="/vocabularies/0/declarations/1/fields/0" {continue;}
                    let binding=&arr(get(expression,"bindings"))[0];
                    let subject=arr(get(node(&j,get(binding,"value")),"value"));
                    shared.insert(s(&subject[1]).to_owned());
                    let image=get(node(&j,get(reading,"domain")),"value");
                    let values=arr(get(image,"elements"));
                    assert_eq!(values.len(),1);
                    assert_eq!(s(get(node(&j,&values[0]),"value")),"0");
                }
            }
            assert_eq!(shared, ["p","q","r"].into_iter().map(str::to_owned).collect());
            let diagnostic=get(output(&j,2,"diagnostic"),"value");
            let global=get(node(&j,get(diagnostic,"global")),"value");
            assert!(arr(get(get(global,"representation"),"values")).is_empty());
        }
        let mut args=vec!["run","--atom-definition","d.json","--archmap","a.json","--law","l.law","--out","again","--reuse","out","--time-ms","120000"];
        for ask in asks {args.extend(["--ask",ask]);}
        let reused=run(&dir,&args);
        assert_eq!(reused.code,r.code,"{} {}",reused.stdout,reused.stderr);
        let again=result_json(&dir,&reused);
        for field in ["answers","nodes"] {assert_eq!(get(&j,field).value,get(&again,field).value);}
    }
}

#[test]
fn integer_translation_local_system_generates_cech_group_and_actual_obstruction() {
    #[path = "common/three_edge.rs"]
    mod triangle;
    fn vector(j:&JNode,r:&JNode)->Vec<i64> {
        arr(get(get(node(j,r),"value"),"coordinates")).iter().map(|r|s(get(node(j,r),"value")).parse().unwrap()).collect()
    }
    fn columns(j:&JNode,r:&JNode)->Vec<Vec<i64>> {
        arr(get(get(node(j,r),"value"),"columns")).iter().map(|c|arr(c).iter().map(|r|s(get(node(j,r),"value")).parse().unwrap()).collect()).collect()
    }
    fn apply(columns:&[Vec<i64>],x:&[i64],rows:usize)->Vec<i64> {
        assert_eq!(columns.len(),x.len());
        (0..rows).map(|i|columns.iter().zip(x).map(|(c,x)|c[i]*x).sum()).collect()
    }
    for gamma in [2,3] {
        let input = triangle::input(Some(gamma));
        let dir = workdir(&format!("integer-local-cech-{gamma}"));
        for (name,bytes) in [("d.json",input.definitions()[0].bytes()),("l.law",input.law().bytes()),("a.json",input.archmap().bytes())] {
            let mut text=String::from_utf8(bytes.to_vec()).unwrap();
            if name=="l.law" {text=text.replace("change move(","view rank(n:Z):Z=n; change move(");}
            std::fs::write(dir.join(name),text).unwrap();
        }
        let asks = ["a=build(Coordinates,on=@triangle/root)","l=localize($a.object,using=Coordinates.move)",
            "d=diagnose($l.system)","s=diagnose($l.system,side=semantic)","z=diagnose($l.system,degree=0)","n=needed($d)","rank=evaluate(Coordinates.rank,on=$a.object,n=$d.space.module.free_rank)","owner=evaluate(Coordinates.rank,on=$a.object,n=$d.class.coordinates.module.free_rank)"];
        let r = execute(&dir,"out",&asks);
        assert_eq!(r.code,if gamma==2 {0}else{1},"{} {}",r.stdout,r.stderr);
        let j = result_json(&dir,&r);
        assert_eq!(s(get(&arr(get(&j,"answers"))[1],"status")),"established","{:?}",get(&j,"answers"));
        for i in [2,3] {
            let answer = &arr(get(&j,"answers"))[i];
            assert_eq!(s(get(answer,"status")),if gamma==2{"established"}else{"refuted"});
            let diagnostic = get(output(&j,i,"diagnostic"),"value");
            assert_eq!(s(get(diagnostic,"kind")),"affine_cech");
            let space = get(output(&j,i,"space"),"value");
            let group = get(node(&j,get(space,"module")),"value");
            assert_eq!(num(get(group,"free_rank")),1);
            assert!(arr(get(group,"torsion")).is_empty());
            let class = get(output(&j,i,"class"),"value");
            let coordinate_vector = get(node(&j,get(class,"coordinates")),"value");
            let values = arr(get(coordinate_vector,"coordinates")).iter().map(|r|s(get(node(&j,r),"value")).parse::<i64>().unwrap()).collect::<Vec<_>>();
            assert_eq!(values.len(),1);
            assert_eq!(values[0].abs(),if gamma==2{0}else{1});
            let complex=get(node(&j,get(diagnostic,"complex")),"value");
            assert_eq!(s(get(complex,"convention")),"ordered");
            let maps=arr(get(complex,"differentials"));
            let d0=columns(&j,&maps[0]); let d1=columns(&j,&maps[1]);
            let modules=arr(get(complex,"modules"));
            let last_rank=num(get(get(node(&j,&modules[2]),"value"),"free_rank")) as usize;
            for column in &d0 { assert!(apply(&d1,column,last_rank).iter().all(|x|*x==0)); }
            let representative=vector(&j,get(class,"representative"));
            assert!(apply(&d1,&representative,last_rank).iter().all(|x|*x==0));
            if gamma==2 { assert!(!has(answer,"counterexamples")); }
            if gamma==3 {
                let j = internal_graph(&dir, &j);
                let answer = &arr(get(&j,"answers"))[i];
                let proof=arr(get(answer,"evidence")).iter().map(|r|get(node(&j,r),"value"))
                    .find(|e|s(get(e,"kind"))=="linear_inconsistent").unwrap();
                let proof=get(proof,"data");
                let u=vector(&j,get(proof,"annihilator"));
                assert_eq!(columns(&j,get(proof,"map")),d0);
                for column in &d0 { assert_eq!(u.iter().zip(column).map(|(x,y)|x*y).sum::<i64>(),0); }
                let pairing=u.iter().zip(vector(&j,get(proof,"rhs"))).map(|(x,y)|x*y).sum::<i64>();
                assert_ne!(pairing,0);
                assert_eq!(pairing,s(get(node(&j,get(proof,"pairing")),"value")).parse::<i64>().unwrap());
            }
        }
        let system=get(output(&j,1,"system"),"value");
        let global=&arr(get(system,"equation_states"))[0];
        let space=get(node(&j,get(global,"space")),"value");
        assert_eq!(arr(get(space,"variables")).len(),3);
        let solution=get(node(&j,get(global,"solutions")),"value");
        let rep=get(solution,"representation");
        if gamma==2 {
            assert_eq!(s(get(rep,"kind")),"affine");
            let p=vector(&j,get(rep,"particular"));
            assert_eq!(p.len(),3); assert_eq!(p[1]-p[0],1); assert_eq!(p[2]-p[1],1);
            let kernel=columns(&j,get(rep,"embedding")); assert_eq!(kernel.len(),1);
            assert_eq!(kernel[0][0].abs(),1); assert!(kernel[0].iter().all(|x|*x==kernel[0][0]));
        } else { assert_eq!(s(get(rep,"kind")),"empty"); }
        for state in arr(get(system,"equation_states")) {
            let space=get(node(&j,get(state,"space")),"value");
            assert!(arr(get(space,"variables")).iter().all(|v|s(get(get(get(v,"position"),"field"),"field"))=="Coordinates.Point.coordinate"));
        }
        assert!(!has(get(&arr(get(&j,"answers"))[4],"outputs"),"class"));
        assert_eq!(s(get(output(&j,6,"value"),"value")),"1");
        assert_eq!(s(get(output(&j,7,"value"),"value")),"1");
        let internal = internal_graph(&dir, &j);
        for index in [6,7] {
            let evaluation=get(output(&internal,index,"evaluation"),"value");
            let projected=node(&internal,get(&arr(get(evaluation,"bindings"))[0],"value"));
            assert_eq!(s(get(projected,"value")),"1");
        }
        let invalid=execute(&dir,"invalid",&["a=build(Coordinates,on=@triangle/root)","l=localize($a.object,using=Coordinates.move)","d=diagnose($l.system)","bad=evaluate(Coordinates.rank,on=$a.object,n=$d.class.coordinates[0])"]);
        assert_eq!(invalid.code,64,"{} {}",invalid.stdout,invalid.stderr);
        let mut args=vec!["run","--atom-definition","d.json","--archmap","a.json","--law","l.law","--out","again","--reuse","out","--time-ms","120000"];
        for ask in asks {args.extend(["--ask",ask]);}
        let reused=run(&dir,&args); assert_eq!(reused.code,r.code,"{} {}",reused.stdout,reused.stderr);
        let again=result_json(&dir,&reused);
        for field in ["answers","nodes"] {assert_eq!(get(&j,field).value,get(&again,field).value);}
    }
}

#[test]
fn integer_local_missing_offset_keeps_its_original_field_for_needed() {
    #[path = "common/three_edge.rs"]
    mod triangle;
    let input=triangle::input(None); let dir=workdir("integer-local-missing");
    for (name,bytes) in [("d.json",input.definitions()[0].bytes()),("l.law",input.law().bytes()),("a.json",input.archmap().bytes())] {std::fs::write(dir.join(name),bytes).unwrap();}
    let asks=["a=build(Coordinates,on=@triangle/root)","l=localize($a.object,using=Coordinates.move)","d=diagnose($l.system)","s=diagnose($l.system,side=semantic)","n=needed($d)"];
    let r=execute(&dir,"out",&asks); assert_eq!(r.code,2,"{} {}",r.stdout,r.stderr);
    let j=result_json(&dir,&r); let answer=&arr(get(&j,"answers"))[1];
    assert!(has(get(answer,"outputs"),"system"));
    for index in [2,3] {
        let diagnostic=&arr(get(&j,"answers"))[index];assert_eq!(s(get(diagnostic,"status")),"undetermined");
        assert!(!has(get(diagnostic,"outputs"),"class"));
        let space=get(output(&j,index,"space"),"value");let group=get(node(&j,get(space,"module")),"value");
        assert_eq!(num(get(group,"free_rank")),1);
    }
    let system=get(output(&j,1,"system"),"value");assert!(!arr(get(system,"contexts")).is_empty());
    assert!(!arr(get(system,"coefficient_restrictions")).is_empty());
    assert!(arr(get(system,"equation_states")).iter().any(|state|s(get(get(get(node(&j,get(state,"solutions")),"value"),"representation"),"kind"))=="symbolic"));
    assert!(arr(get(answer,"reasons")).iter().any(|r|s(get(r,"code"))=="missing_observation"));
    let plan=get(output(&j,4,"plan"),"value");
    assert!(arr(get(plan,"requirements")).iter().any(|r| {
        let f=get(r,"field"); s(get(f,"field"))=="Coordinates.Shift.shift" && s(get(f,"subject"))=="c"
    }));
    let mut args=vec!["run","--atom-definition","d.json","--archmap","a.json","--law","l.law","--out","again","--reuse","out","--time-ms","120000"];
    for ask in asks {args.extend(["--ask",ask]);}
    let repeat=run(&dir,&args);assert_eq!(repeat.code,2,"{} {}",repeat.stdout,repeat.stderr);
    let again=result_json(&dir,&repeat);for field in ["answers","nodes"] {assert_eq!(get(&j,field).value,get(&again,field).value);}
}

#[test]
fn integer_local_equation_fibers_do_not_expand_the_allowed_even_translation_image() {
    #[path = "common/three_edge.rs"]
    mod triangle;
    let input=triangle::input(Some(2));let dir=workdir("integer-local-even-action");
    for (name,bytes) in [("d.json",input.definitions()[0].bytes()),("l.law",input.law().bytes()),("a.json",input.archmap().bytes())] {
        let mut text=String::from_utf8(bytes.to_vec()).unwrap();if name=="l.law" {text=text.replace("coordinate=p.coordinate+d","coordinate=p.coordinate+2*d");}
        std::fs::write(dir.join(name),text).unwrap();
    }
    let r=execute(&dir,"out",&["a=build(Coordinates,on=@triangle/root)","l=localize($a.object,using=Coordinates.move)","e=diagnose($l.system)","s=diagnose($l.system,side=semantic)","n=needed($s)"]);
    assert_eq!(r.code,2,"{} {}",r.stdout,r.stderr);
    let j=result_json(&dir,&r);
    assert!(has(get(&arr(get(&j,"answers"))[2],"outputs"),"class"));
    let semantic=&arr(get(&j,"answers"))[3];assert_eq!(s(get(semantic,"status")),"undetermined");assert!(!has(get(semantic,"outputs"),"class"));assert!(!has(semantic,"claim"));
    assert_eq!(s(get(&arr(get(&j,"answers"))[4],"status")),"established");
    assert!(has(get(&arr(get(&j,"answers"))[4],"outputs"),"plan"));
    let diagnostic=get(output(&j,3,"diagnostic"),"value");
    assert!(arr(get(diagnostic,"conditions")).iter().any(|r|s(get(get(node(&j,r),"judgment"),"status"))=="refuted"));
    let system=get(output(&j,1,"system"),"value");
    let global=&arr(get(system,"semantic_states"))[0];
    let solutions=get(node(&j,get(global,"parameters")),"value");assert_eq!(s(get(get(solutions,"representation"),"kind")),"empty");
}

#[test]
fn integer_local_stop_retains_completed_contexts_without_publishing_a_system() {
    use archsig::observed::{control::{Checkpoint,Control,Limits,Usage},evaluate::evaluate_observed_bytes};
    use std::{cell::Cell,rc::Rc};
    #[path = "common/three_edge.rs"]
    mod triangle;
    let asks=["a=build(Coordinates,on=@triangle/root)","l=localize($a.object,using=Coordinates.move)"];
    let total=Rc::new(Cell::new(0usize));let count=total.clone();
    let mut control=Control::new(Limits::default(),move |point| {if point==Checkpoint::Localize {count.set(count.get()+1);}Usage::default()});
    let full=evaluate_observed_bytes(triangle::input(Some(2)),&asks,&mut control).unwrap();
    let normal=archsig::json::parse(full.wire().canonical().as_bytes()).unwrap();
    assert!(has(get(&arr(get(&normal,"answers"))[1],"outputs"),"system"));
    let mut retained=false;
    for (mode,divisor) in [(0,8),(1,6),(2,4),(0,3)] {
        let stop=(total.get()/divisor).max(1);let mut count=0;
        let mut control=Control::new(Limits{time_ms:Some(1),memory_mib:Some(1)},move |point|{
            if point==Checkpoint::Localize {count+=1;}if count<stop {return Usage::default();}
            match mode {0=>Usage{elapsed_ms:2,..Usage::default()},1=>Usage{memory_mib:2,..Usage::default()},_=>Usage{signal:Some(archsig::result::Signal::Term),..Usage::default()}}
        });
        let partial=evaluate_observed_bytes(triangle::input(Some(2)),&asks,&mut control).unwrap();
        let j=archsig::json::parse(partial.wire().canonical().as_bytes()).unwrap();
        let answer=&arr(get(&j,"answers"))[1];assert_eq!(s(get(answer,"status")),"undetermined");
        assert!(!has(get(answer,"outputs"),"system"));
        assert!(arr(get(answer,"reasons")).iter().any(|r|s(get(r,"code"))==if mode==2{"cancelled"}else{"budget_exhausted"}));
        let nodes=arr(get(&j,"nodes"));
        retained|=nodes.iter().any(|n|matches!(&get(n,"type").value,archsig::json::JValue::Str(t) if t=="Context"));
        assert!(nodes.iter().all(|n|!matches!(&get(n,"type").value,archsig::json::JValue::Str(t) if t=="LocalSystem")));
    }
    assert!(retained,"整数局所系の完成済みcontextが失われた");
}

fn integer_local_variant(name:&str, edit:impl FnOnce(String)->String, remove:Option<(&str,&str)>) -> std::path::PathBuf {
    #[path = "common/three_edge.rs"] mod triangle;
    let input=triangle::input(Some(2));let dir=workdir(name);
    std::fs::write(dir.join("d.json"),input.definitions()[0].bytes()).unwrap();
    std::fs::write(dir.join("l.law"),edit(String::from_utf8(input.law().bytes().to_vec()).unwrap())).unwrap();
    let mut map=String::from_utf8(input.archmap().bytes().to_vec()).unwrap();
    if let Some((subject,field))=remove {
        let atom=format!(r#"{{"id":"{subject}-{field}","subject":"{subject}","field":"Coordinates.{field}","value":["triangle","root"],"origin":"model"}},"#);
        assert!(map.contains(&atom));map=map.replace(&atom,"");
    }
    std::fs::write(dir.join("a.json"),map).unwrap();dir
}

#[test]
fn integer_local_input_forms_keep_direct_implicit_guarded_and_tuple_readings() {
    let local="local Edge(e:Shift) reads e.shift,e.from.coordinate,e.to.coordinate;";
    for mode in ["implicit","direct","true-guard","tuple","empty-laws","let-law","let-subject","affine-read","joint-read","affine-tuple"] {
        let dir=integer_local_variant(&format!("integer-forms-{mode}"),|s|match mode {
            "implicit"=>s.replace(local,""),
            "joint-read"=>s.replace("reads e.shift,e.from.coordinate,e.to.coordinate","reads e.shift,e.from.coordinate+e.to.coordinate,e.from.coordinate"),
            "affine-tuple"=>s.replace("reads e.shift,e.from.coordinate,e.to.coordinate","reads e.shift,(2*e.from.coordinate,e.to.coordinate)"),
            "affine-read"=>s.replace("reads e.shift,e.from.coordinate,e.to.coordinate","reads e.shift,2*e.from.coordinate,e.to.coordinate"),
            "let-law"=>s.replace("e.to.coordinate-e.from.coordinate=e.shift;","let delta=e.to.coordinate-e.from.coordinate in delta=e.shift;"),
            "let-subject"=>s.replace("e.to.coordinate-e.from.coordinate=e.shift;","let endpoint=e.to in endpoint.coordinate-e.from.coordinate=e.shift;"),
            "direct"=>s.replace("law required aligned(e:Shift):e.to.coordinate-e.from.coordinate=e.shift;","law required zero(p:Point):p.coordinate=0;").replace(local,"local PointRead(p:Point) reads p.coordinate;"),
            "true-guard"=>s.replace("local Edge(e:Shift)","local Edge(e:Shift) when true").replace("change move(p:Point,d:Z)=","change move(p:Point,d:Z) when true="),
            "tuple"=>s.replace("reads e.shift,e.from.coordinate,e.to.coordinate","reads e.shift,(e.from.coordinate,e.from.coordinate,e.to.coordinate)"),
            _=>s.replace(local,"").replace("law required aligned(e:Shift):e.to.coordinate-e.from.coordinate=e.shift;","")
        },None);
        let r=execute(&dir,"out",&["a=build(Coordinates,on=@triangle/root)","l=localize($a.object,using=Coordinates.move)","d=diagnose($l.system)"]);
        assert_eq!(r.code,0,"{mode}: {} {}",r.stdout,r.stderr);let j=result_json(&dir,&r);
        let space=get(output(&j,2,"space"),"value");let group=get(node(&j,get(space,"module")),"value");
        assert_eq!(num(get(group,"free_rank")),if matches!(mode,"direct"|"empty-laws"){0}else{1},"{mode}");
        let system=get(output(&j,1,"system"),"value");
        for state in arr(get(system,"equation_states")) {
            for variable in arr(get(get(node(&j,get(state,"space")),"value"),"variables")) {
                let p=get(variable,"position");assert_eq!(s(get(p,"kind")),"observation");
                assert!(arr(get(p,"component")).is_empty());assert_eq!(s(get(get(p,"field"),"snapshot")),"triangle");
            }
        }
        if mode=="affine-read" {
            let mut scaled = false;
            for context in arr(get(system,"contexts")) {
                for read in arr(get(get(node(&j,context),"value"),"readings")) {
                    let domain = get(node(&j,get(read,"domain")),"value");
                    if s(get(domain,"kind")) != "image" { continue; }
                    let map = get(node(&j,get(domain,"map")),"value");
                    let linear = get(node(&j,get(map,"linear")),"value");
                    let columns = arr(get(linear,"columns"));
                    if columns.len()==1 && arr(&columns[0]).len()==1 {
                        assert_eq!(s(get(node(&j,&arr(&columns[0])[0]),"value")),"2");
                        scaled = true;
                    }
                }
            }
            assert!(scaled,"2Zを表す読取り像がない");
        }
        if mode=="tuple" {
            let mut checked=false;
            for context in arr(get(system,"contexts")) {for read in arr(get(get(node(&j,context),"value"),"readings")) {
                let domain=get(node(&j,get(read,"domain")),"value");
                if s(get(domain,"kind"))!="image" {continue;}
                let map=get(node(&j,get(domain,"map")),"value");let linear=get(node(&j,get(map,"linear")),"value");
                for column in arr(get(linear,"columns")) {let values=arr(column);assert_eq!(values.len(),3);assert_eq!(get(node(&j,&values[0]),"value").value,get(node(&j,&values[1]),"value").value);}
                checked=true;
            }}assert!(checked);
        }
    }
}

#[test]
fn integer_local_guards_and_visibility_keep_distinct_reasons() {
    for guard in [true,false] {
        let dir=integer_local_variant(if guard{"integer-local-guard"}else{"integer-local-visibility"},|s|if guard {
            s.replace("change move(p:Point,d:Z)=","change move(p:Point,d:Z) when d=0=")
        }else{s.replace("reads e.shift,e.from.coordinate,e.to.coordinate","reads e.shift,e.from.coordinate")},None);
        let asks=if guard {vec!["a=build(Coordinates,on=@triangle/root)","l=localize($a.object,using=Coordinates.move)","d=diagnose($l.system,side=semantic)","n=needed($d)"]}else{vec!["a=build(Coordinates,on=@triangle/root)","l=localize($a.object,using=Coordinates.move)","n=needed($l)"]};
        let r=execute(&dir,"out",&asks);assert_eq!(r.code,2,"{} {}",r.stdout,r.stderr);let j=result_json(&dir,&r);
        if guard {
            let d=&arr(get(&j,"answers"))[2];assert_eq!(s(get(d,"status")),"undetermined");assert!(!has(get(d,"outputs"),"class"));
            let system=get(output(&j,1,"system"),"value");let state=&arr(get(system,"semantic_states"))[0];
            let solutions=get(node(&j,get(state,"parameters")),"value");assert_eq!(s(get(get(solutions,"representation"),"kind")),"empty");
            let candidate=get(node(&j,get(solutions,"domain")),"value");assert_eq!(arr(get(candidate,"guards")).len(),3);
        } else {
            let l=&arr(get(&j,"answers"))[1];assert!(arr(get(l,"reasons")).iter().any(|r|s(get(r,"code"))=="visibility_insufficient"));
        }
        assert_eq!(s(get(arr(get(&j,"answers")).last().unwrap(),"status")),"established");
    }
}

#[test]
fn integer_local_owner_missing_reaches_needed_for_change_and_law_domains() {
    for (subject,field) in [("p","Point.owner"),("a","Shift.owner")] {
        let dir=integer_local_variant(&format!("integer-owner-{subject}"),|s|s,Some((subject,field)));
        let r=execute(&dir,"out",&["a=build(Coordinates,on=@triangle/root)","l=localize($a.object,using=Coordinates.move)","n=needed($l)"]);
        assert_eq!(r.code,2,"{} {}",r.stdout,r.stderr);let j=result_json(&dir,&r);
        assert!(arr(get(&arr(get(&j,"answers"))[1],"reasons")).iter().any(|r|s(get(r,"code"))=="missing_observation"));
        let plan=get(output(&j,2,"plan"),"value");
        assert!(arr(get(plan,"requirements")).iter().any(|r|{let f=get(r,"field");s(get(f,"subject"))==subject&&s(get(f,"field"))==format!("Coordinates.{field}")}));
    }
}

#[test]
fn integer_local_zero_class_survives_a_refuted_gluing_condition() {
    let definitions=r#"{"format":"archsig.atom-definition/1","semantics":"archsig/0.6.0","vocabularies":[{"semantics":"archsig/0.6.0","namespace":"Pair","version":"1","dependencies":[],"declarations":[{"kind":"entity","name":"Pair.State","meaning":"二つの整数座標。","parameters":[],"fields":[{"name":"x","type":"Z","meaning":"第一座標。"},{"name":"y","type":"Z","meaning":"第二座標。"}],"alignments":[]}]}]}"#;
    let checked=definition::check_definitions(&[("d",definitions.as_bytes())]).unwrap();let digest=&checked.vocabularies["Pair"].digest;
    let law=format!("law \"archsig.law/2\" semantics \"archsig/0.6.0\"; reading Pair {{ use vocabulary Pair version \"1\" digest \"{digest}\"; law required x(s:State):s.x=s.x; law required y(s:State):s.y=s.y; local X(s:State) reads s.x; local Y(s:State) reads s.y; change diagonal(s:State,t:Z)=s with{{x=t,y=t}}; }}");
    let map=format!(r#"{{"format":"archsig.archmap/2","semantics":"archsig/0.6.0","vocabularies":[{{"namespace":"Pair","version":"1","digest":"{digest}"}}],"sources":[],"origins":[{{"id":"model","mode":"specification","method":"対角作用の試験。","locations":[],"note":"二座標の原始値。"}}],"snapshots":[{{"id":"v","origin":"model","subjects":[{{"id":"s","type":"Pair.State","origin":"model"}}],"atoms":[{{"id":"x","subject":"s","field":"Pair.State.x","value":"0","origin":"model"}},{{"id":"y","subject":"s","field":"Pair.State.y","value":"0","origin":"model"}}]}}]}}"#);
    let dir=workdir("integer-class-without-gluing");for (name,text) in [("d.json",definitions),("l.law",&law),("a.json",&map)] {std::fs::write(dir.join(name),text).unwrap();}
    let r=execute(&dir,"out",&["a=build(Pair,on=@v/s)","l=localize($a.object,using=Pair.diagonal)","d=diagnose($l.system,side=semantic)"]);
    assert_eq!(r.code,0,"{} {}",r.stdout,r.stderr);let j=result_json(&dir,&r);
    let answer=&arr(get(&j,"answers"))[2];assert_eq!(s(get(answer,"status")),"established");assert!(has(get(answer,"outputs"),"class"));
    let space=get(output(&j,2,"space"),"value");assert_eq!(num(get(get(node(&j,get(space,"module")),"value"),"free_rank")),0);
    assert!(!has(answer,"counterexamples"));
    let diagnostic=get(output(&j,2,"diagnostic"),"value");assert!(arr(get(diagnostic,"conditions")).iter().any(|r|s(get(get(node(&j,r),"judgment"),"status"))=="refuted"));
}

#[test]
fn integer_local_missing_does_not_hide_a_nonlinear_law() {
    #[path = "common/three_edge.rs"] mod triangle;
    let input = triangle::input(None);
    let dir = workdir("integer-missing-nonlinear");
    std::fs::write(dir.join("d.json"),input.definitions()[0].bytes()).unwrap();
    std::fs::write(dir.join("a.json"),input.archmap().bytes()).unwrap();
    let law = String::from_utf8(input.law().bytes().to_vec()).unwrap().replace(
        "local Edge", "law required zz(p:Point):p.coordinate*p.coordinate=0; local Edge");
    std::fs::write(dir.join("l.law"),law).unwrap();
    let r = execute(&dir,"out",&["a=build(Coordinates,on=@triangle/root)",
        "l=localize($a.object,using=Coordinates.move)","n=needed($l)"]);
    assert_eq!(r.code,2,"{} {}",r.stdout,r.stderr);
    let j = result_json(&dir,&r);
    let reasons = arr(get(&arr(get(&j,"answers"))[1],"reasons"));
    for code in ["missing_observation","unsupported_algorithm"] {
        assert!(reasons.iter().any(|r|s(get(r,"code"))==code),"{code}: {reasons:?}");
    }
    let plan = get(output(&j,2,"plan"),"value");
    assert!(!arr(get(plan,"blockers")).is_empty());
}

#[test]
fn integer_local_empty_cover_has_zero_cohomology() {
    let dir = integer_local_variant("integer-empty-cover",|s|s
        .replace("law required aligned(e:Shift):e.to.coordinate-e.from.coordinate=e.shift;","")
        .replace("local Edge(e:Shift) reads e.shift,e.from.coordinate,e.to.coordinate;",""),None);
    let map = std::fs::read_to_string(dir.join("a.json")).unwrap();
    let prefix = map.split_once("\"subjects\":[").unwrap().0;
    std::fs::write(dir.join("a.json"),format!(r#"{prefix}"subjects":[{{"id":"root","type":"Coordinates.System","origin":"model"}}],"atoms":[]}}]}}"#)).unwrap();
    let r = execute(&dir,"out",&["a=build(Coordinates,on=@triangle/root)",
        "l=localize($a.object,using=Coordinates.move)","z=diagnose($l.system,degree=0)","d=diagnose($l.system)"]);
    assert_eq!(r.code,0,"{} {}",r.stdout,r.stderr);
    let j = result_json(&dir,&r);
    for i in [2,3] {
        let space = get(output(&j,i,"space"),"value");
        let module = get(node(&j,get(space,"module")),"value");
        assert_eq!(num(get(module,"free_rank")),0);
        assert!(arr(get(module,"torsion")).is_empty());
    }
    assert!(has(get(&arr(get(&j,"answers"))[3],"outputs"),"class"));
}

#[test]
fn integer_local_vectors_compare_only_in_the_same_module() {
    let dir = integer_local_variant("integer-vector-comparison",|s|s
        .replace("law required aligned(e:Shift):e.to.coordinate-e.from.coordinate=e.shift;","law required zero(p:Point):p.coordinate=0;")
        .replace("local Edge(e:Shift) reads e.shift,e.from.coordinate,e.to.coordinate;","local PointRead(p:Point) reads p.coordinate;"),None);
    let r = execute(&dir,"out",&["a=build(Coordinates,on=@triangle/root)",
        "l=localize($a.object,using=Coordinates.move)","d=diagnose($l.system)",
        "e=diagnose($l.system,side=semantic)",
        "same=compare($d.class.coordinates,to=$d.class.coordinates,kind=value)",
        "different=compare($d.class.coordinates,to=$e.class.coordinates,kind=value)"]);
    assert_eq!(r.code,2,"{} {}",r.stdout,r.stderr);
    let j = result_json(&dir,&r);
    let answers = arr(get(&j,"answers"));
    assert_eq!(s(get(&answers[4],"status")),"established");
    assert!(has(get(&answers[4],"outputs"),"comparison"));
    assert!(arr(get(&answers[5],"reasons")).iter().any(|r|s(get(r,"code"))=="condition_failed"));
    assert!(!has(get(&answers[5],"outputs"),"comparison"));
}

#[test]
fn integer_local_empty_cover_degree_iteration_observes_budget() {
    use archsig::observed::{control::{Checkpoint,Control,Limits,Usage},evaluate::evaluate_observed_bytes,input::InputSources};
    use std::{cell::Cell,rc::Rc};
    let dir=integer_local_variant("integer-empty-degree-budget",|s|s
        .replace("law required aligned(e:Shift):e.to.coordinate-e.from.coordinate=e.shift;","")
        .replace("local Edge(e:Shift) reads e.shift,e.from.coordinate,e.to.coordinate;",""),None);
    let map=std::fs::read_to_string(dir.join("a.json")).unwrap();
    let prefix=map.split_once("\"subjects\":[").unwrap().0;
    let map=format!(r#"{prefix}"subjects":[{{"id":"root","type":"Coordinates.System","origin":"model"}}],"atoms":[]}}]}}"#);
    let inputs=||InputSources::from_bytes(vec![std::fs::read(dir.join("d.json")).unwrap()],std::fs::read(dir.join("l.law")).unwrap(),map.as_bytes().to_vec());
    let asks=["a=build(Coordinates,on=@triangle/root)","l=localize($a.object,using=Coordinates.move)"];
    let total=Rc::new(Cell::new(0usize));let count=total.clone();
    let mut c=Control::new(Limits::default(),move |point|{if point==Checkpoint::Localize {count.set(count.get()+1);}Usage::default()});
    evaluate_observed_bytes(inputs(),&asks,&mut c).unwrap();
    let stop=total.get()+2;let mut count=0;
    let mut c=Control::new(Limits{time_ms:Some(1),memory_mib:None},move |point|{
        if point==Checkpoint::Localize {count+=1;}
        if count>=stop {Usage{elapsed_ms:2,..Usage::default()}}else{Usage::default()}
    });
    let result=evaluate_observed_bytes(inputs(),&[asks[0],asks[1],"d=diagnose($l.system,degree=20)"],&mut c).unwrap();
    let j=archsig::json::parse(result.wire().canonical().as_bytes()).unwrap();
    let d=&arr(get(&j,"answers"))[2];
    assert_eq!(s(get(d,"status")),"undetermined");
    assert!(!has(get(d,"outputs"),"space"));
    assert!(arr(get(d,"reasons")).iter().any(|r|s(get(r,"code"))=="budget_exhausted"));
}

#[test]
fn integer_local_noninjective_reads_keep_the_image_and_cover_conditions() {
    let definitions=r#"{"format":"archsig.atom-definition/1","semantics":"archsig/0.6.0","vocabularies":[{"semantics":"archsig/0.6.0","namespace":"Pair","version":"1","dependencies":[],"declarations":[{"kind":"entity","name":"Pair.State","meaning":"二つの整数座標。","parameters":[],"fields":[{"name":"x","type":"Z","meaning":"第一座標。"},{"name":"y","type":"Z","meaning":"第二座標。"}],"alignments":[]}]}]}"#;
    let checked=definition::check_definitions(&[("d",definitions.as_bytes())]).unwrap();let digest=&checked.vocabularies["Pair"].digest;
    for mode in ["sum-only","constrained","free","constrained-missing","free-missing","offset-missing"] {
        let extra=if mode=="sum-only" {""} else {"local Both(s:State) reads (s.x,s.y);"};
        let requirement=if mode.starts_with("free") {""} else {"law required total(s:State):s.x+s.y=0;"};
        let law=format!("law \"archsig.law/2\" semantics \"archsig/0.6.0\"; reading Pair {{ use vocabulary Pair version \"1\" digest \"{digest}\"; {requirement} local Sum(s:State) reads s.x+s.y; {extra} change movePair(s:State,a:Z,b:Z)=s with{{x=a,y=b}}; }}");
        let law=if mode=="offset-missing" {law.replace("x=a,y=b","x=s.x+a,y=b")} else {law};
        let map=format!(r#"{{"format":"archsig.archmap/2","semantics":"archsig/0.6.0","vocabularies":[{{"namespace":"Pair","version":"1","digest":"{digest}"}}],"sources":[],"origins":[{{"id":"model","mode":"specification","method":"合計の読取り試験。","locations":[],"note":"二座標の原始値。"}}],"snapshots":[{{"id":"v","origin":"model","subjects":[{{"id":"s","type":"Pair.State","origin":"model"}}],"atoms":[{{"id":"x","subject":"s","field":"Pair.State.x","value":"0","origin":"model"}},{{"id":"y","subject":"s","field":"Pair.State.y","value":"0","origin":"model"}}]}}]}}"#);
        let map=if mode.ends_with("missing") {
            map.replace(r#"{"id":"x","subject":"s","field":"Pair.State.x","value":"0","origin":"model"},"#, "")
        } else {map};
        let dir=workdir(&format!("integer-sum-{mode}"));for (name,text) in [("d.json",definitions),("l.law",&law),("a.json",&map)] {std::fs::write(dir.join(name),text).unwrap();}
        let mut asks=vec!["a=build(Pair,on=@v/s)","l=localize($a.object,using=Pair.movePair)"];
        if !matches!(mode,"sum-only"|"offset-missing") {asks.extend(["z=diagnose($l.system,degree=0)","d=diagnose($l.system)"]);}
        let r=execute(&dir,"out",&asks);
        if mode.ends_with("missing") {assert!(matches!(r.code,0|2),"{mode}: {} {}",r.stdout,r.stderr);}
        else {assert_eq!(r.code,if mode=="sum-only"{2}else{0},"{mode}: {} {}",r.stdout,r.stderr);}
        let j=result_json(&dir,&r);
        if mode=="sum-only" {
            let reasons=arr(get(&arr(get(&j,"answers"))[1],"reasons"));
            assert!(reasons.iter().any(|r|s(get(r,"code"))=="visibility_insufficient"));
            assert!(reasons.iter().all(|r|s(get(r,"code"))!="unsupported_algorithm"));
            continue;
        }
        if mode=="offset-missing" {
            let answer=&arr(get(&j,"answers"))[1];
            assert_eq!(s(get(answer,"status")),"undetermined");
            assert!(!has(get(answer,"outputs"),"system"));
            assert!(arr(get(answer,"reasons")).iter().any(|r|s(get(r,"code"))=="missing_observation"));
            continue;
        }
        for answer in &arr(get(&j,"answers"))[1..] {
            assert_eq!(s(get(answer,"status")),"established","{mode}: {answer:?}");
        }
        let system=get(output(&j,1,"system"),"value");
        let sum=arr(get(system,"contexts")).iter().find(|r|{
            let locals=arr(get(get(node(&j,r),"value"),"locals"));
            locals.len()==1 && s(get(&locals[0],"declaration"))=="Pair.Sum"
        }).expect("Sumだけの局所がない");
        let context=get(node(&j,sum),"value");assert_eq!(arr(get(context,"readings")).len(),1);
        for coefficient in arr(get(system,"coefficients")).iter().filter(|v|get(v,"context").value==sum.value) {
            assert_eq!(num(get(get(node(&j,get(coefficient,"module")),"value"),"free_rank")),if mode.starts_with("free"){1}else{0});
        }
        for (i,rank) in [(2,if mode.starts_with("free"){2}else{1}),(3,0)] {
            let space=get(output(&j,i,"space"),"value");
            assert_eq!(num(get(get(node(&j,get(space,"module")),"value"),"free_rank")),rank);
        }
    }
}

#[test]
fn integer_diagnostics_compare_identity_cochains_classes_and_public_maps() {
    for (side,degree) in [("equation",0),("equation",1),("equation",2),("semantic",0),("semantic",1)] {
        let dir=diagnostic_compare_input(&format!("integer-compare-{side}-{degree}"),true,true);
        let path=dir.join("l.law");let law=std::fs::read_to_string(&path).unwrap();
        std::fs::write(&path,law.replace("law optional localValid", "view rank(n:Z):Z=n; change move(s:State,d:Z)=s with{free=s.free+d}; law optional localValid")).unwrap();
        let d1=format!("d1=diagnose($l.system,side={side},degree={degree})");
        let d2=format!("d2=diagnose($l.system,side={side},degree={degree})");
        let asks=["m=map(Reservations.Migration,on=@v/m,reading=Reservations)",
            "l=localize($m.candidate.source,law=Reservations.localValid,s=@v/p,using=Reservations.move)",&d1,&d2,
            "c=compare($d1.diagnostic,to=$d2.diagnostic,kind=diagnostics,along=$m.operation)",
            "k=evaluate(Reservations.rank,on=$m.candidate.source,n=$c.comparison.kernel.free_rank)",
            "q=evaluate(Reservations.rank,on=$m.candidate.source,n=$c.comparison.cohomology_map.target.free_rank)"];
        let r=execute(&dir,"out",&asks);assert_eq!(r.code,0,"{} {}",r.stdout,r.stderr);
        let j=result_json(&dir,&r);let comparison=get(output(&j,4,"comparison"),"value");
        let cochain=get(node(&j,get(comparison,"cochain_map")),"value");
        assert_eq!(arr(get(cochain,"components")).len(),degree as usize+2);
        for map in arr(get(cochain,"components")).iter().chain(std::iter::once(get(comparison,"cohomology_map"))) {
            let map=get(node(&j,map),"value");
            let columns=arr(get(map,"columns"));
            let source=get(node(&j,get(map,"source")),"value");let target=get(node(&j,get(map,"target")),"value");
            assert_eq!(columns.len(),arr(get(source,"generators")).len());
            for (col,values) in columns.iter().enumerate() {
                assert_eq!(arr(values).len(),arr(get(target,"generators")).len());
                for (row,value) in arr(values).iter().enumerate() {assert_eq!(s(get(node(&j,value),"value")),if row==col{"1"}else{"0"});}
            }
        }
        for field in ["kernel","cokernel"] {
            let module=get(node(&j,get(comparison,field)),"value");
            assert_eq!(num(get(module,"free_rank")),0);assert!(arr(get(module,"torsion")).is_empty());
        }
        assert_eq!(has(comparison,"class_transport"),degree==1);
        if degree==1 {assert_eq!(s(get(get(node(&j,get(comparison,"class_transport")),"judgment"),"status")),"established");}
        assert_eq!(s(get(output(&j,5,"value"),"value")),"0");
        assert_eq!(s(get(output(&j,6,"value"),"value")),if degree==0 {"1"} else {"0"});
        let mut args=vec!["run","--atom-definition","d.json","--archmap","a.json","--law","l.law","--out","again","--reuse","out","--time-ms","120000"];
        for ask in asks {args.extend(["--ask",ask]);}
        let reused=run(&dir,&args);assert_eq!(reused.code,0,"{} {}",reused.stdout,reused.stderr);
        let again=result_json(&dir,&reused);for field in ["answers","nodes"] {assert_eq!(get(&j,field).value,get(&again,field).value);}
    }
}

#[test]
fn integer_diagnostic_comparison_keeps_unavailable_classes_and_transport_distinct() {
    for mode in ["empty","nonidentity","different-system"] {
        let dir=diagnostic_compare_input(&format!("integer-compare-{mode}"),mode!="nonidentity",mode!="empty");
        let path=dir.join("l.law");let law=std::fs::read_to_string(&path).unwrap();
        std::fs::write(&path,law.replace("law optional localValid", "change even(s:State,d:Z)=s with{free=s.free+2*d}; law optional localValid")).unwrap();
        let mut asks=vec!["m=map(Reservations.Migration,on=@v/m,reading=Reservations)",
            "l=localize($m.candidate.source,law=Reservations.localValid,s=@v/p,using=Reservations.even)"];
        if mode=="different-system" {asks.push("k=localize($m.candidate.source,law=Reservations.localValid,s=@v/p,using=Reservations.even)");}
        asks.push("d1=diagnose($l.system,side=semantic)");
        asks.push(if mode=="different-system" {"d2=diagnose($k.system,side=semantic)"} else {"d2=diagnose($l.system,side=semantic)"});
        let index=asks.len();
        asks.push("c=compare($d1.diagnostic,to=$d2.diagnostic,kind=diagnostics,along=$m.operation)");
        asks.push("n=needed($c)");
        let r=execute(&dir,"out",&asks);assert_eq!(r.code,2,"{mode}: {} {}",r.stdout,r.stderr);
        let j=result_json(&dir,&r);let answer=&arr(get(&j,"answers"))[index];
        assert_eq!(s(get(answer,"status")),"undetermined");
        assert!(!has(get(answer,"outputs"),"comparison"));
        let expected=if mode=="empty" {"dependency_blocked"} else {"unsupported_algorithm"};
        assert!(arr(get(answer,"reasons")).iter().any(|r|s(get(r,"code"))==expected),"{mode}: {answer:?}");
        assert_eq!(s(get(arr(get(&j,"answers")).last().unwrap(),"status")),"established");
    }
}

#[test]
fn integer_diagnostic_comparison_transports_a_nonzero_obstruction() {
    let dir=diagnostic_compare_input("integer-compare-nonzero",true,true);
    let path=dir.join("l.law");let law=std::fs::read_to_string(&path).unwrap();
    std::fs::write(&path,law.replace("law optional localValid",
        "law optional loopShift(e:Reserve):e.to.free-e.from.free=1; local Edge(e:Reserve) reads e.from.free,e.to.free; change move(s:State,d:Z)=s with{free=s.free+d}; law optional localValid")).unwrap();
    let r=execute(&dir,"out",&["m=map(Reservations.Migration,on=@v/m,reading=Reservations)",
        "l=localize($m.candidate.source,law=Reservations.loopShift,using=Reservations.move)",
        "d1=diagnose($l.system)","d2=diagnose($l.system)",
        "c=compare($d1.diagnostic,to=$d2.diagnostic,kind=diagnostics,along=$m.operation)"]);
    assert_eq!(r.code,1,"{} {}",r.stdout,r.stderr);
    let j=result_json(&dir,&r);
    for i in [2,3] {
        assert_eq!(s(get(&arr(get(&j,"answers"))[i],"status")),"refuted");
        let class=get(output(&j,i,"class"),"value");let vector=get(node(&j,get(class,"coordinates")),"value");
        assert!(arr(get(vector,"coordinates")).iter().any(|r|s(get(node(&j,r),"value"))!="0"));
    }
    let answer=&arr(get(&j,"answers"))[4];assert_eq!(s(get(answer,"status")),"established");
    let comparison=get(output(&j,4,"comparison"),"value");
    assert_eq!(s(get(get(node(&j,get(comparison,"class_transport")),"judgment"),"status")),"established");
}


#[test]
fn integer_local_actions_keep_parameter_kernel_stabilizer_and_effective_image_distinct() {
    let definitions=r#"{"format":"archsig.atom-definition/1","semantics":"archsig/0.6.0","vocabularies":[{"semantics":"archsig/0.6.0","namespace":"Motion","version":"1","dependencies":[],"declarations":[{"kind":"entity","name":"Motion.State","meaning":"整数状態。","parameters":[],"fields":[{"name":"x","type":"Z","meaning":"位置。"},{"name":"goal","type":"Z","meaning":"要求位置。"}],"alignments":[]}]}]}"#;
    let checked=definition::check_definitions(&[("d",definitions.as_bytes())]).unwrap();
    let digest=&checked.vocabularies["Motion"].digest;
    let law=format!("law \"archsig.law/2\" semantics \"archsig/0.6.0\"; reading Motion {{ use vocabulary Motion version \"1\" digest \"{digest}\"; law required reachesGoal(s:State):s.x=s.goal; local Read(s:State) reads (s.x,s.goal); change move(s:State,a:Z,b:Z)=s with{{x=2*a+2*b}}; }}");
    for (goal, guarded) in [(Some(2),false),(Some(1),false),(None,false),(Some(4),true),(Some(2),true)] {
        let law=if guarded {law.replace("b:Z)=s", "b:Z) when a=b=s")} else {law.clone()};
        let mut atoms=vec![r#"{"id":"x","subject":"s","field":"Motion.State.x","value":"0","origin":"model"}"#.to_string()];
        if let Some(goal)=goal {atoms.push(format!(r#"{{"id":"goal","subject":"s","field":"Motion.State.goal","value":"{goal}","origin":"model"}}"#));}
        let map=format!(r#"{{"format":"archsig.archmap/2","semantics":"archsig/0.6.0","vocabularies":[{{"namespace":"Motion","version":"1","digest":"{digest}"}}],"sources":[],"origins":[{{"id":"model","mode":"specification","method":"二つのparameterの同効果。","locations":[],"note":"偶数だけを移動先に持つ。"}}],"snapshots":[{{"id":"v","origin":"model","subjects":[{{"id":"s","type":"Motion.State","origin":"model"}}],"atoms":[{}]}}]}}"#,atoms.join(","));
        let dir=workdir(&format!("integer-actions-{goal:?}-{guarded}"));
        for (name,text) in [("d.json",definitions),("l.law",&law),("a.json",&map)] {std::fs::write(dir.join(name),text).unwrap();}
        let asks=["a=build(Motion,on=@v/s)","l=localize($a.object,using=Motion.move)","d=diagnose($l.system,side=semantic)"];
        let r=execute(&dir,"out",&asks);assert!(matches!(r.code,0|2),"{goal:?}: {} {}",r.stdout,r.stderr);
        let j=result_json(&dir,&r);let system=get(output(&j,1,"system"),"value");
        let mut nontrivial_allowed=false;let mut lawful=false;
        for action in arr(get(system,"actions")) {
            let action=get(node(&j,action),"value");
            let effective=get(node(&j,get(action,"effective")),"value");
            let stabilizer=get(node(&j,get(action,"stabilizer")),"value");
            let quotient=get(node(&j,get(action,"quotient")),"value");
            let kernel=get(node(&j,get(quotient,"source")),"value");
            let kr=num(get(kernel,"free_rank"));let er=num(get(effective,"free_rank"));let sr=num(get(stabilizer,"free_rank"));
            assert_eq!(kr,er+sr);
            assert_eq!(get(quotient,"target").value,get(action,"effective").value);
            for condition in arr(get(action,"conditions")) {assert_eq!(s(get(get(node(&j,condition),"judgment"),"status")),"established");}
            if s(get(action,"stage"))=="allowed" {
                assert!(!has(action,"parameter_kernel"));
                if er==1 {
                    assert_eq!((kr,sr),if guarded {(1,0)}else{(2,1)});nontrivial_allowed=true;
                    let map=get(node(&j,get(action,"map")),"value");
                    let linear=get(node(&j,get(map,"linear")),"value");
                    for column in arr(get(linear,"columns")) {
                        assert_eq!(arr(column).len(),1);
                        assert_eq!(s(get(node(&j,&arr(column)[0]),"value")),"2");
                    }
                }
            } else {
                assert_eq!(get(action,"parameter_kernel").value,get(quotient,"source").value);
                if er==0 && kr==u64::from(!guarded) {assert_eq!(sr,kr);lawful=true;}
            }
        }
        assert!(nontrivial_allowed,"{goal:?}");
        assert_eq!(lawful,goal==Some(if guarded {4}else{2}),"{goal:?}, guarded={guarded}");
        let mut args=vec!["run","--atom-definition","d.json","--archmap","a.json","--law","l.law","--out","again","--reuse","out","--time-ms","120000"];
        for ask in asks {args.extend(["--ask",ask]);}
        let reused=run(&dir,&args);assert_eq!(reused.code,r.code,"{} {}",reused.stdout,reused.stderr);
        let again=result_json(&dir,&reused);for field in ["answers","nodes"] {assert_eq!(get(&j,field).value,get(&again,field).value);}
    }
}


fn integer_transport_input(name: &str, reorder: bool) -> std::path::PathBuf {
    #[path = "common/architecture_environment.rs"] mod fixture;
    use archsig::canonical::Json;
    let dir=diagnostic_compare_input(name,false,true);
    let mut map=fixture::owned(&archsig::json::parse(&std::fs::read(dir.join("a.json")).unwrap()).unwrap());
    for atom in fixture::atoms(&mut map) {
        let Json::Obj(fields)=atom else{panic!("atom")};
        match fields.get("id") {
            Some(Json::Str(id)) if id=="r-free"=>{fields.insert("value".into(),Json::str("2"));},
            Some(Json::Str(id)) if id=="s-free"=>{fields.insert("value".into(),Json::str("1"));},
            _=>{},
        }
    }
    fn rename(j:&mut Json) {
        match j {
            Json::Str(s)=>{*s=match s.as_str(){"r"=>"transport_z","s"=>"transport_a","f"=>"transport_zz","l"=>"transport_ll","t"=>"transport_aa",_=>return}.into();},
            Json::Arr(xs)=>for x in xs{rename(x)},
            Json::Obj(xs)=>for x in xs.values_mut(){rename(x)}, _=>{},
        }
    }
    if reorder {rename(&mut map);}
    std::fs::write(dir.join("a.json"),map.canonical()).unwrap();
    let path=dir.join("l.law");let law=std::fs::read_to_string(&path).unwrap();
    std::fs::write(&path,law.replace("law optional localValid",
        "view rank(n:Z):Z=n; change move(s:State,d:Z)=s with{free=s.free+d}; law optional localValid")).unwrap();
    dir
}

#[test]
fn integer_diagnostics_transport_between_architectures_and_reordered_contexts() {
    for reorder in [false,true] {for (side,degree) in [("equation",0),("equation",1),("semantic",0),("semantic",1)] {
        let dir=integer_transport_input(&format!("integer-transport-{reorder}-{side}-{degree}"),reorder);
        let target=format!("r=localize($m.candidate.target,law=Reservations.localValid,s=@v/{},using=Reservations.move)",if reorder{"transport_z"}else{"r"});
        let ld=format!("d=diagnose($l.system,side={side},degree={degree})");let rd=format!("e=diagnose($r.system,side={side},degree={degree})");
        let asks=["m=map(Reservations.Migration,on=@v/m,reading=Reservations)",
            "l=localize($m.candidate.source,law=Reservations.localValid,s=@v/p,using=Reservations.move)",&target,&ld,&rd,
            "c=compare($d.diagnostic,to=$e.diagnostic,kind=diagnostics,along=$m.operation)",
            "q=evaluate(Reservations.rank,on=$m.candidate.source,n=$c.comparison.cohomology_map.target.free_rank)"];
        let r=execute(&dir,"out",&asks);assert_eq!(r.code,0,"{reorder}/{side}/{degree}: {} {}",r.stdout,r.stderr);
        let j=result_json(&dir,&r);let cmp=get(output(&j,5,"comparison"),"value");
        assert_eq!(s(get(&arr(get(&j,"answers"))[5],"status")),"established");
        assert_eq!(s(get(output(&j,6,"value"),"value")),if degree==0{"1"}else{"0"});
        let chain=get(node(&j,get(cmp,"cochain_map")),"value");
        assert_ne!(get(chain,"source").value,get(chain,"target").value);
        for field in ["kernel","cokernel"] {assert_eq!(num(get(get(node(&j,get(cmp,field)),"value"),"free_rank")),0);}
        assert_eq!(has(cmp,"class_transport"),degree==1);
        if degree==1{assert_eq!(s(get(get(node(&j,get(cmp,"class_transport")),"judgment"),"status")),"established");}
        let mut args=vec!["run","--atom-definition","d.json","--archmap","a.json","--law","l.law","--out","again","--reuse","out","--time-ms","120000"];
        for ask in asks {args.extend(["--ask",ask]);}
        let reused=run(&dir,&args);assert_eq!(reused.code,0,"{} {}",reused.stdout,reused.stderr);
        let again=result_json(&dir,&reused);for field in ["answers","nodes"] {assert_eq!(get(&j,field).value,get(&again,field).value);}
    }}
}


#[test]
fn integer_diagnostic_transport_moves_nonzero_classes_with_its_actual_matrix() {
    let dir=integer_transport_input("integer-transport-nonzero",true);
    let path=dir.join("l.law");let law=std::fs::read_to_string(&path).unwrap();
    std::fs::write(&path,law.replace("law optional localValid",
        "law optional loopShift(e:Reserve):e.to.free-e.from.free=1; local Edge(e:Reserve) reads e.from.free,e.to.free; law optional localValid")).unwrap();
    let r=execute(&dir,"out",&["m=map(Reservations.Migration,on=@v/m,reading=Reservations)",
        "l=localize($m.candidate.source,law=Reservations.loopShift,using=Reservations.move)",
        "r=localize($m.candidate.target,law=Reservations.loopShift,using=Reservations.move)",
        "d=diagnose($l.system)","e=diagnose($r.system)",
        "c=compare($d.diagnostic,to=$e.diagnostic,kind=diagnostics,along=$m.operation)"]);
    assert_eq!(r.code,1,"{} {}",r.stdout,r.stderr);let j=result_json(&dir,&r);
    let coordinates=|i| {
        let class=get(output(&j,i,"class"),"value");let vector=get(node(&j,get(class,"coordinates")),"value");
        arr(get(vector,"coordinates")).iter().map(|r|s(get(node(&j,r),"value")).parse::<i64>().unwrap()).collect::<Vec<_>>()
    };
    let x=coordinates(3);let y=coordinates(4);assert!(x.iter().any(|v|*v!=0));assert!(y.iter().any(|v|*v!=0));
    let cmp=get(output(&j,5,"comparison"),"value");
    assert_eq!(s(get(&arr(get(&j,"answers"))[5],"status")),"established");
    let map=get(node(&j,get(cmp,"cohomology_map")),"value");let columns=arr(get(map,"columns"));
    assert_eq!(columns.len(),x.len());
    let image=(0..y.len()).map(|i|columns.iter().zip(&x).map(|(column,x)|s(get(node(&j,&arr(column)[i]),"value")).parse::<i64>().unwrap()*x).sum::<i64>()).collect::<Vec<_>>();
    assert_eq!(image,y);
    let chain=get(node(&j,get(cmp,"cochain_map")),"value");let mut changed=false;
    for component in arr(get(chain,"components")) {
        let map=get(node(&j,component),"value");
        for (col,column) in arr(get(map,"columns")).iter().enumerate(){for (row,x) in arr(column).iter().enumerate(){
            let x=s(get(node(&j,x),"value")).parse::<i64>().unwrap();changed|=x!=i64::from(row==col);
        }}
    }
    assert!(changed,"patchの並び替えを反映するcochain成分がない");
}


#[test]
fn integer_diagnostic_transport_does_not_use_equal_ranks_as_a_state_map() {
    #[path = "common/architecture_environment.rs"] mod fixture;
    use archsig::canonical::Json;
    for image in [false,true] {
        let dir=integer_transport_input(&format!("integer-transport-mismatch-{image}"),false);
        let path=dir.join("l.law");let law=std::fs::read_to_string(&path).unwrap();
        std::fs::write(&path,law.replace("law optional localValid", "change even(s:State,d:Z)=s with{free=s.free+2*d}; law optional localValid")).unwrap();
        if !image {
            let mut map=fixture::owned(&archsig::json::parse(&std::fs::read(dir.join("a.json")).unwrap()).unwrap());
            for atom in fixture::atoms(&mut map){let Json::Obj(fields)=atom else{panic!("atom")};
                if fields.get("id")==Some(&Json::str("r-free")){fields.insert("value".into(),Json::str("3"));}
            }
            std::fs::write(dir.join("a.json"),map.canonical()).unwrap();
        }
        let target=format!("r=localize($m.candidate.target,law=Reservations.localValid,s=@v/r,using=Reservations.{})",if image{"even"}else{"move"});
        let r=execute(&dir,"out",&["m=map(Reservations.Migration,on=@v/m,reading=Reservations)",
            "l=localize($m.candidate.source,law=Reservations.localValid,s=@v/p,using=Reservations.move)",&target,
            "d=diagnose($l.system,side=semantic,degree=0)","e=diagnose($r.system,side=semantic,degree=0)",
            "c=compare($d.diagnostic,to=$e.diagnostic,kind=diagnostics,along=$m.operation)","n=needed($c)"]);
        assert_eq!(r.code,2,"{} {}",r.stdout,r.stderr);let j=result_json(&dir,&r);
        for i in [3,4] {let space=get(output(&j,i,"space"),"value");assert_eq!(num(get(get(node(&j,get(space,"module")),"value"),"free_rank")),1);}
        let answer=&arr(get(&j,"answers"))[5];assert_eq!(s(get(answer,"status")),"undetermined");
        assert!(!has(get(answer,"outputs"),"comparison"));
        assert!(arr(get(answer,"reasons")).iter().any(|r|s(get(r,"code"))=="unsupported_algorithm"));
        assert_eq!(s(get(&arr(get(&j,"answers"))[6],"status")),"established");
    }
}

#[test]
fn integer_diagnostic_inclusion_computes_torsion_cokernel_and_keeps_the_map() {
    for step in [0,2,3] { for degree in [0,1] {
        let dir=integer_transport_input(&format!("integer-inclusion-{step}-{degree}"),true);
        let path=dir.join("l.law");let law=std::fs::read_to_string(&path).unwrap();
        std::fs::write(&path,law.replace("law optional localValid",&format!("change stride(s:State,d:Z)=s with{{free=s.free+{step}*d}}; law optional localValid"))).unwrap();
        let ld=format!("d=diagnose($l.system,side=semantic,degree={degree})");
        let rd=format!("e=diagnose($r.system,side=semantic,degree={degree})");
        let asks=["m=map(Reservations.Migration,on=@v/m,reading=Reservations)",
            "l=localize($m.candidate.source,law=Reservations.localValid,s=@v/p,using=Reservations.stride)",
            "r=localize($m.candidate.target,law=Reservations.localValid,s=@v/transport_z,using=Reservations.move)",&ld,&rd,
            "c=compare($d.diagnostic,to=$e.diagnostic,kind=diagnostics,along=$m.operation)",
            "q=evaluate(Reservations.rank,on=$m.candidate.source,n=$c.comparison.cokernel.free_rank)"];
        let r=execute(&dir,"out",&asks);assert_eq!(r.code,if degree==0{1}else{0},"{step}/{degree}: {} {}",r.stdout,r.stderr);
        let j=result_json(&dir,&r);let cmp=get(output(&j,5,"comparison"),"value");
        assert_eq!(s(get(&arr(get(&j,"answers"))[5],"status")),if degree==0{"refuted"}else{"established"});
        let group=arr(get(cmp,"conditions")).iter().map(|r|node(&j,r)).find(|n| {
            let v=get(n,"value");
            s(get(v,"predicate"))=="equal" && matches!(&get(node(&j,&arr(get(v,"operands"))[0]),"value").value,archsig::json::JValue::Str(_))
        }).expect("整数値の等値として群の零条件を保持する");
        let operands=arr(get(get(group,"value"),"operands"));assert_eq!(operands.len(),2);
        assert_eq!(s(get(node(&j,&operands[0]),"value")),if degree==0{"1"}else{"0"});
        assert_eq!(s(get(node(&j,&operands[1]),"value")),"0");
        assert_eq!(s(get(get(group,"judgment"),"status")),if degree==0{"refuted"}else{"established"});
        let kernel=get(node(&j,get(cmp,"kernel")),"value");let cokernel=get(node(&j,get(cmp,"cokernel")),"value");
        assert_eq!(num(get(kernel,"free_rank")),0);assert!(arr(get(kernel,"torsion")).is_empty());
        assert_eq!(num(get(cokernel,"free_rank")),if step==0 && degree==0 {1}else{0});
        let torsion=arr(get(cokernel,"torsion")).iter().map(s).collect::<Vec<_>>();
        assert_eq!(torsion,if degree==0 && step!=0 {vec![step.to_string()]}else{vec![]});
        let hm=get(node(&j,get(cmp,"cohomology_map")),"value");
        if degree==0 && step!=0 { let columns=arr(get(hm,"columns"));assert_eq!(columns.len(),1);
            let coefficient=s(get(node(&j,&arr(&columns[0])[0]),"value")).parse::<i64>().unwrap();assert_eq!(coefficient.abs(),step);
            let relations=arr(get(cokernel,"relations"));assert_eq!(relations.len(),1);
            assert_eq!(s(get(node(&j,&arr(&relations[0])[0]),"value")),step.to_string());
        } else {assert!(arr(get(hm,"columns")).is_empty());
            if degree==1 {assert_eq!(s(get(get(node(&j,get(cmp,"class_transport")),"judgment"),"status")),"established");}}
        assert_eq!(s(get(output(&j,6,"value"),"value")),if step==0 && degree==0 {"1"}else{"0"});
        let mut args=vec!["run","--atom-definition","d.json","--archmap","a.json","--law","l.law","--out","again","--reuse","out","--time-ms","120000"];
        for ask in asks {args.extend(["--ask",ask]);}
        let reused=run(&dir,&args);assert_eq!(reused.code,r.code,"{} {}",reused.stdout,reused.stderr);
        let again=result_json(&dir,&reused);for field in ["answers","nodes"] {assert_eq!(get(&j,field).value,get(&again,field).value);}
    }}
}

#[test]
fn integer_diagnostic_inclusion_keeps_unavailable_classes_blocked() {
    let dir=integer_transport_input("integer-inclusion-missing-class",false);
    let path=dir.join("l.law");let law=std::fs::read_to_string(&path).unwrap();
    std::fs::write(&path,law.replace("law optional localValid",
        "change four(s:State,d:Z)=s with{free=s.free+4*d}; change two(s:State,d:Z)=s with{free=s.free+2*d}; law optional loopShift(e:Reserve):e.to.free-e.from.free=0; local Edge(e:Reserve) reads e.from.free,e.to.free; law optional localValid")).unwrap();
    let asks=["m=map(Reservations.Migration,on=@v/m,reading=Reservations)",
        "l=localize($m.candidate.source,law=Reservations.loopShift,using=Reservations.four)",
        "r=localize($m.candidate.target,law=Reservations.loopShift,using=Reservations.two)",
        "d=diagnose($l.system,side=semantic)","e=diagnose($r.system,side=semantic)",
        "c=compare($d.diagnostic,to=$e.diagnostic,kind=diagnostics,along=$m.operation)","n=needed($c)"];
    let r=execute(&dir,"out",&asks);assert_eq!(r.code,2,"{} {}",r.stdout,r.stderr);
    let j=result_json(&dir,&r);
    for i in [3,4] {assert!(!has(get(&arr(get(&j,"answers"))[i],"outputs"),"class"));}
    let answer=&arr(get(&j,"answers"))[5];
    assert_eq!(s(get(answer,"status")),"undetermined");
    assert!(!has(get(answer,"outputs"),"comparison"));
    assert!(arr(get(answer,"reasons")).iter().any(|r|s(get(r,"code"))=="dependency_blocked"));
    assert!(arr(get(answer,"reasons")).iter().any(|r|s(get(r,"code"))=="condition_failed"));
    assert_eq!(s(get(&arr(get(&j,"answers"))[6],"status")),"established");
}


fn finite_diagnostic_input(name: &str, valid: bool) -> std::path::PathBuf {
    let dir = diagnostic_compare_input(name, true, true);
    finite_diagnostic_input_at(dir, valid)
}
fn finite_diagnostic_input_at(dir: std::path::PathBuf, valid: bool) -> std::path::PathBuf {
    #[path = "common/architecture_environment.rs"]
    mod fixture;
    use archsig::canonical::Json;
    let old = std::fs::read_to_string(dir.join("d.json")).unwrap();
    let definitions = old.replace(
        r#""name": "free", "type": "Z""#,
        r#""name": "free", "type": "Bool""#,
    );
    assert_ne!(old, definitions);
    let checked = definition::check_definitions(&[("d", definitions.as_bytes())]).unwrap();
    let digest = &checked.vocabularies["Reservations"].digest;
    let old_digest = definition::check_definitions(&[("d", old.as_bytes())])
        .unwrap()
        .vocabularies["Reservations"]
        .digest
        .clone();
    let raw = std::fs::read_to_string(dir.join("a.json"))
        .unwrap()
        .replace(&old_digest, digest);
    let mut map = fixture::owned(&archsig::json::parse(raw.as_bytes()).unwrap());
    for atom in fixture::atoms(&mut map) {
        let Json::Obj(fields) = atom else {
            panic!("atom")
        };
        if fields.get("field") == Some(&Json::str("Reservations.State.free")) {
            fields.insert("value".into(), Json::Bool(true));
        }
    }
    let predicate = if valid {
        "s.free=true"
    } else {
        "s.free=true and s.free=false"
    };
    let law=format!("law \"archsig.law/2\" semantics \"archsig/0.6.0\"; reading Reservations {{ use vocabulary Reservations version \"1\" digest \"{digest}\"; change choose(s:State,b:Bool)=s with{{free=b}}; law optional localValid(s:State):{predicate}; }}");
    std::fs::write(dir.join("d.json"), definitions).unwrap();
    std::fs::write(dir.join("a.json"), map.canonical()).unwrap();
    std::fs::write(dir.join("l.law"), law).unwrap();
    dir
}

#[test]
fn finite_change_diagnostics_compare_the_selected_global_states_and_reuse() {
    for valid in [false,true] { for side in ["equation","semantic"] { for degree in [0,1] {
        let dir=finite_diagnostic_input(&format!("finite-change-compare-{valid}-{side}-{degree}"),valid);
        let d1=format!("d1=diagnose($l.system,side={side},degree={degree})");
        let d2=format!("d2=diagnose($l.system,side={side},degree={degree})");
        let asks=["m=map(Reservations.Migration,on=@v/m,reading=Reservations)",
            "l=localize($m.candidate.source,law=Reservations.localValid,s=@v/p,using=Reservations.choose)",&d1,&d2,
            "c=compare($d1.diagnostic,to=$d2.diagnostic,kind=diagnostics,along=$m.operation)","n=needed($c)"];
        let r=execute(&dir,"out",&asks);assert_eq!(r.code,if !valid && degree==1{1}else{0},"{valid}/{side}/{degree}: {} {}",r.stdout,r.stderr);
        let j=result_json(&dir,&r);let answer=&arr(get(&j,"answers"))[4];assert_eq!(s(get(answer,"status")),"established");
        let cmp=get(output(&j,4,"comparison"),"value");let map=get(node(&j,get(cmp,"finite_map")),"value");
        let d=get(output(&j,2,"diagnostic"),"value");let restriction=get(node(&j,get(d,"restriction")),"value");
        assert_eq!(get(map,"source").value,get(restriction,"source").value);assert_eq!(get(map,"source").value,get(map,"target").value);
        let pairs=arr(get(map,"pairs"));assert_eq!(pairs.len(),if valid{2}else{0});
        let mut states=vec![];
        for pair in pairs {let pair=arr(pair);assert_eq!(pair[0].value,pair[1].value);
            let value=get(node(&j,&pair[0]),"value");states.push(arr(value).iter().map(|n|match n.value {archsig::json::JValue::Bool(v)=>v,_=>panic!("Bool状態")}).collect::<Vec<_>>());}
        if valid {assert_eq!(states,vec![vec![true,false],vec![true,true]]);}
        for condition in arr(get(cmp,"conditions")){assert_eq!(s(get(get(node(&j,condition),"judgment"),"status")),"established");}
        assert_eq!(s(get(&arr(get(&j,"answers"))[5],"status")),"established");
        let mut args=vec!["run","--atom-definition","d.json","--archmap","a.json","--law","l.law","--out","again","--reuse","out","--time-ms","120000"];
        for ask in asks {args.extend(["--ask",ask]);}let reused=run(&dir,&args);assert_eq!(reused.code,r.code,"{} {}",reused.stdout,reused.stderr);
        let again=result_json(&dir,&reused);for field in ["answers","nodes"] {assert_eq!(get(&j,field).value,get(&again,field).value);}
    }}}
}

#[test]
fn repeated_finite_localization_uses_real_state_bijections() {
    for valid in [false, true] {
        for side in ["equation", "semantic"] {
            for degree in [0, 1] {
                let dir = finite_diagnostic_input(
                    &format!("repeat-local-{valid}-{side}-{degree}"),
                    valid,
                );
                let d1 = format!("d1=diagnose($l.system,side={side},degree={degree})");
                let d2 = format!("d2=diagnose($r.system,side={side},degree={degree})");
                let asks=["m=map(Reservations.Migration,on=@v/m,reading=Reservations)",
            "l=localize($m.candidate.source,law=Reservations.localValid,s=@v/p,using=Reservations.choose)",
            "r=localize($m.candidate.source,using=Reservations.choose,s=@v/p,law=Reservations.localValid)",&d1,&d2,
            "c=compare($d1.diagnostic,to=$d2.diagnostic,kind=diagnostics,along=$m.operation)","n=needed($c)"];
                let r = execute(&dir, "out", &asks);
                assert_eq!(
                    r.code,
                    if !valid && degree == 1 { 1 } else { 0 },
                    "{} {}",
                    r.stdout,
                    r.stderr
                );
                let j = result_json(&dir, &r);
                assert_eq!(s(get(&arr(get(&j, "answers"))[5], "status")), "established");
                let cmp = get(output(&j, 5, "comparison"), "value");
                let map = get(node(&j, get(cmp, "finite_map")), "value");
                node(&j,get(map,"source")); node(&j,get(map,"target"));
                let pairs = arr(get(map, "pairs"));
                assert_eq!(pairs.len(), if valid { 2 } else { 0 });
                for pair in pairs {
                    let pair = arr(pair);
                    node(&j,&pair[0]); node(&j,&pair[1]);
                    assert_eq!(
                        get(node(&j, &pair[0]), "value").value,
                        get(node(&j, &pair[1]), "value").value
                    );
                }
                for condition in arr(get(cmp, "conditions")) {
                    assert_eq!(
                        s(get(get(node(&j, condition), "judgment"), "status")),
                        "established"
                    );
                }
                assert_eq!(s(get(&arr(get(&j, "answers"))[6], "status")), "established");
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
                for field in ["answers", "nodes"] {
                    assert_eq!(get(&j, field).value, get(&again, field).value);
                }
            }
        }
    }
}

#[test]
fn different_finite_localization_plans_are_not_equal_by_shared_position_names() {
    let dir = finite_diagnostic_input("different-local-plans", true);
    let path = dir.join("l.law");
    let law = std::fs::read_to_string(&path).unwrap();
    std::fs::write(
        &path,
        law.replace(
            "law optional localValid",
            "change constant(s:State,b:Bool)=s with{free=true}; law optional localValid",
        ),
    )
    .unwrap();
    let r=execute(&dir,"out",&["m=map(Reservations.Migration,on=@v/m,reading=Reservations)",
        "l=localize($m.candidate.source,law=Reservations.localValid,s=@v/p,using=Reservations.choose)",
        "r=localize($m.candidate.source,law=Reservations.localValid,s=@v/p,using=Reservations.constant)",
        "d1=diagnose($l.system,side=semantic,degree=0)","d2=diagnose($r.system,side=semantic,degree=0)",
        "c=compare($d1.diagnostic,to=$d2.diagnostic,kind=diagnostics,along=$m.operation)","n=needed($c)"]);
    assert_eq!(r.code, 2, "{} {}", r.stdout, r.stderr);
    let j = result_json(&dir, &r);
    let answer = &arr(get(&j, "answers"))[5];
    assert_eq!(s(get(answer, "status")), "undetermined");
    assert!(!has(get(answer, "outputs"), "comparison"));
    assert!(arr(get(answer, "reasons"))
        .iter()
        .any(|r| s(get(r, "code")) == "unsupported_algorithm"));
    assert_eq!(s(get(&arr(get(&j, "answers"))[6], "status")), "established");
}

#[test]
fn finite_localization_without_required_laws_keeps_equation_and_action_states_distinct() {
    for explicit in [false, true] {
        for side in ["equation", "semantic"] {
            for degree in [0, 1] {
                let dir = finite_diagnostic_input(&format!("empty-local-laws-{explicit}-{side}-{degree}"), false);
                let path = dir.join("l.law");
                let law = std::fs::read_to_string(&path).unwrap();
                let extra = if explicit { "local each(s:State) reads s.free;" } else { "" };
                std::fs::write(&path, law.replace("law optional localValid", &format!(
                    "change constant(s:State,b:Bool)=s with{{free=true}}; {extra} law optional localValid"))).unwrap();
                let d = format!("d=diagnose($l.system,side={side},degree={degree})");
                let e = format!("e=diagnose($r.system,side={side},degree={degree})");
                let asks = ["m=map(Reservations.Migration,on=@v/m,reading=Reservations)",
                    "l=localize($m.candidate.source,using=Reservations.constant)",
                    "r=localize($m.candidate.source,using=Reservations.constant)", &d, &e,
                    "c=compare($d.diagnostic,to=$e.diagnostic,kind=diagnostics,along=$m.operation)",
                    "n=needed($c)"];
                let result = execute(&dir, "out", &asks);
                assert_eq!(result.code, 0, "{explicit}/{side}/{degree}: {} {}", result.stdout, result.stderr);
                let j = result_json(&dir, &result);
                for answer in arr(get(&j, "answers")) { assert_eq!(s(get(answer, "status")), "established"); }
                let diagnostic = get(output(&j, 3, "diagnostic"), "value");
                let restriction = get(node(&j, get(diagnostic, "restriction")), "value");
                let global = get(node(&j, get(restriction, "source")), "value");
                let elements = arr(get(global, "elements"));
                let states = elements.iter().map(|r| arr(get(node(&j, r), "value")).iter().map(|v| {
                    match v.value { archsig::json::JValue::Bool(value) => value, _ => panic!("Bool状態") }
                }).collect::<Vec<_>>()).collect::<Vec<_>>();
                assert_eq!(states, if side == "equation" {
                    vec![vec![false,false],vec![false,true],vec![true,false],vec![true,true]]
                } else { vec![vec![true,true]] });
                let matching = get(node(&j, get(diagnostic, "matching")), "value");
                assert_eq!(arr(get(matching, "elements")).len(), states.len());
                let comparison = get(output(&j, 5, "comparison"), "value");
                let map = get(node(&j, get(comparison, "finite_map")), "value");
                assert_eq!(arr(get(map, "pairs")).len(), states.len());
                let mut args = vec!["run", "--atom-definition", "d.json", "--archmap", "a.json", "--law", "l.law", "--out", "again", "--reuse", "out", "--time-ms", "120000"];
                for ask in asks { args.extend(["--ask", ask]); }
                let reused = run(&dir, &args);
                assert_eq!(reused.code, 0, "{} {}", reused.stdout, reused.stderr);
                let again = result_json(&dir, &reused);
                for field in ["answers", "nodes"] { assert_eq!(get(&j, field).value, get(&again, field).value); }
            }
        }
    }
}

#[test]
fn empty_local_law_family_keeps_change_expression_for_unsupported_followups() {
    let dir = finite_diagnostic_input("empty-local-laws-followups", false);
    let path = dir.join("l.law");
    let law = std::fs::read_to_string(&path).unwrap();
    std::fs::write(&path, law.replace("law optional localValid",
        "change constant(s:State,b:Bool)=s with{free=true}; law optional localValid")).unwrap();
    let asks = ["m=map(Reservations.Migration,on=@v/m,reading=Reservations)",
        "l=localize($m.candidate.source,using=Reservations.constant)",
        "r=localize($m.candidate.source,using=Reservations.choose)",
        "d=diagnose($l.system,side=semantic,degree=0)",
        "e=diagnose($r.system,side=semantic,degree=0)",
        "c=compare($d.diagnostic,to=$e.diagnostic,kind=diagnostics,along=$m.operation)",
        "h=diagnose($l.system,degree=2)", "n=needed($c)", "k=needed($h)"];
    let result = execute(&dir, "out", &asks);
    assert_eq!(result.code, 2, "{} {}", result.stdout, result.stderr);
    let j = result_json(&dir, &result);
    let answers = arr(get(&j, "answers"));
    for i in [1,2,3,4,7,8] { assert_eq!(s(get(&answers[i], "status")), "established"); }
    assert_eq!(s(get(&answers[5],"status")),"refuted");
    let internal = internal_graph(&dir, &j);
    for i in [6] {
        assert_eq!(s(get(&answers[i], "status")), "undetermined");
        let reason = arr(get(&arr(get(&internal,"answers"))[i], "reasons")).iter().find(|r| s(get(r,"code")) == "unsupported_algorithm").unwrap();
        let dependencies = arr(get(reason, "dependencies"));
        assert!(!dependencies.is_empty());
        let expression = dependencies.iter().map(|r| get(node(&internal, r), "value"))
            .find(|value| has(value, "kind") && s(get(value, "kind")) == "source").unwrap();
        assert_eq!(arr(get(expression, "parameters")).iter().map(|p| s(get(p, "name"))).collect::<Vec<_>>(), vec!["s", "b"]);
        assert!(arr(get(expression, "bindings")).is_empty());
    }
    let mut args = vec!["run", "--atom-definition", "d.json", "--archmap", "a.json", "--law", "l.law", "--out", "again", "--reuse", "out", "--time-ms", "120000"];
    for ask in asks { args.extend(["--ask", ask]); }
    let reused = run(&dir, &args);
    assert_eq!(reused.code, 2, "{} {}", reused.stdout, reused.stderr);
    let again = result_json(&dir, &reused);
    for field in ["answers", "nodes"] { assert_eq!(get(&j, field).value, get(&again, field).value); }
}

#[test]
fn empty_local_law_family_keeps_change_body_and_guard_missing_for_needed() {
    #[path = "common/architecture_environment.rs"] mod fixture;
    use archsig::canonical::Json;
    for guard in [false, true] {
        let dir = finite_diagnostic_input(&format!("empty-local-laws-missing-{guard}"), false);
        let path = dir.join("l.law");
        let law = std::fs::read_to_string(&path).unwrap();
        let change = if guard {
            "change observed(s:State,b:Bool) when s.held=1=s with{free=b};"
        } else { "change observed(s:State,b:Bool)=s with{free=s.held=0};" };
        std::fs::write(&path, law.replace("law optional localValid", &format!("{change} law optional localValid"))).unwrap();
        let path = dir.join("a.json");
        let mut map = fixture::owned(&archsig::json::parse(&std::fs::read(&path).unwrap()).unwrap());
        let atoms = fixture::atoms(&mut map);
        let before = atoms.len();
        atoms.retain(|atom| !matches!(atom, Json::Obj(fields) if fields.get("id") == Some(&Json::str("p-held"))));
        assert_eq!(before - atoms.len(), 1);
        std::fs::write(&path, map.canonical()).unwrap();
        let asks = ["m=map(Reservations.Migration,on=@v/m,reading=Reservations)",
            "l=localize($m.candidate.source,using=Reservations.observed)",
            "d=diagnose($l.system)", "n=needed($l)", "k=needed($d)"];
        let result = execute(&dir, "out", &asks);
        assert_eq!(result.code, 2, "{guard}: {} {}", result.stdout, result.stderr);
        let j = result_json(&dir, &result);
        let local = &arr(get(&j, "answers"))[1];
        assert_eq!(s(get(local, "status")), "undetermined");
        assert!(!has(get(local, "outputs"), "system"));
        assert!(arr(get(local, "reasons")).iter().any(|r| s(get(r, "code")) == "missing_observation"));
        for i in [3,4] {
            let plan = get(output(&j, i, "plan"), "value");
            assert!(arr(get(plan, "requirements")).iter().any(|r| {
                let field = get(r, "field");
                s(get(field, "field")) == "Reservations.State.held" && s(get(field, "subject")) == "p"
            }));
        }
        let mut args = vec!["run", "--atom-definition", "d.json", "--archmap", "a.json", "--law", "l.law", "--out", "again", "--reuse", "out", "--time-ms", "120000"];
        for ask in asks { args.extend(["--ask", ask]); }
        let reused = run(&dir, &args);
        assert_eq!(reused.code, 2, "{} {}", reused.stdout, reused.stderr);
        let again = result_json(&dir, &reused);
        for field in ["answers", "nodes"] { assert_eq!(get(&j, field).value, get(&again, field).value); }
    }
}

#[test]
fn fixed_localization_without_laws_keeps_one_state_and_reuses_comparisons() {
    for explicit in [false,true] { for side in ["equation","semantic"] { for degree in [0,1] {
        let dir = finite_diagnostic_input(&format!("empty-fixed-{explicit}-{side}-{degree}"), false);
        if explicit {
            let path=dir.join("l.law");let law=std::fs::read_to_string(&path).unwrap();
            std::fs::write(path,law.replace("law optional localValid","local each(s:State) reads s.free; law optional localValid")).unwrap();
        }
        let d=format!("d=diagnose($l.system,side={side},degree={degree})");
        let e=format!("e=diagnose($r.system,side={side},degree={degree})");
        let asks=["m=map(Reservations.Migration,on=@v/m,reading=Reservations)",
            "l=localize($m.candidate.source)","r=localize($m.candidate.source)",&d,&e,
            "c=compare($d.diagnostic,to=$e.diagnostic,kind=diagnostics,along=$m.operation)","n=needed($c)"];
        let result=execute(&dir,"out",&asks);assert_eq!(result.code,0,"{explicit}/{side}/{degree}: {} {}",result.stdout,result.stderr);
        let j=result_json(&dir,&result);
        for answer in arr(get(&j,"answers")) {assert_eq!(s(get(answer,"status")),"established");}
        let diagnostic=get(output(&j,3,"diagnostic"),"value");
        let matching=get(node(&j,get(diagnostic,"matching")),"value");assert_eq!(arr(get(matching,"elements")).len(),1);
        let restriction=get(node(&j,get(diagnostic,"restriction")),"value");assert_eq!(arr(get(restriction,"pairs")).len(),1);
        let cmp=get(output(&j,5,"comparison"),"value");let map=get(node(&j,get(cmp,"finite_map")),"value");
        assert_eq!(arr(get(map,"pairs")).len(),1);
        for condition in arr(get(cmp,"conditions")) {assert_eq!(s(get(get(node(&j,condition),"judgment"),"status")),"established");}
        let mut args=vec!["run","--atom-definition","d.json","--archmap","a.json","--law","l.law","--out","again","--reuse","out","--time-ms","120000"];
        for ask in asks {args.extend(["--ask",ask]);}let reused=run(&dir,&args);assert_eq!(reused.code,0,"{} {}",reused.stdout,reused.stderr);
        let again=result_json(&dir,&reused);for field in ["answers","nodes"] {assert_eq!(get(&j,field).value,get(&again,field).value);}
    }}}
}

#[test]
fn fixed_empty_law_diagnostics_keep_unsupported_dependencies_without_inventing_an_expression() {
    let dir=finite_diagnostic_input("empty-fixed-followups",false);
    let asks=["m=map(Reservations.Migration,on=@v/m,reading=Reservations)","l=localize($m.candidate.source)",
        "r=localize($m.candidate.source,using=Reservations.choose)",
        "d=diagnose($l.system,degree=0)","e=diagnose($r.system,degree=0)","h=diagnose($l.system,degree=2)",
        "c=compare($d.diagnostic,to=$e.diagnostic,kind=diagnostics,along=$m.operation)","n=needed($h)","k=needed($c)"];
    let result=execute(&dir,"out",&asks);assert_eq!(result.code,2,"{} {}",result.stdout,result.stderr);
    let j=result_json(&dir,&result);let answers=arr(get(&j,"answers"));
    for i in [1,2,3,4,7,8] {assert_eq!(s(get(&answers[i],"status")),"established");}
    let internal = internal_graph(&dir, &j);
    for i in [5,6] {
        assert_eq!(s(get(&answers[i],"status")),"undetermined");
        let reason=arr(get(&arr(get(&internal,"answers"))[i],"reasons")).iter().find(|r|s(get(r,"code"))=="unsupported_algorithm").unwrap();
        let deps=arr(get(reason,"dependencies"));assert!(!deps.is_empty());
        for dep in deps {let value=get(node(&internal,dep),"value");assert!(!has(value,"kind") || s(get(value,"kind"))!="source");}
    }
    let mut args=vec!["run","--atom-definition","d.json","--archmap","a.json","--law","l.law","--out","again","--reuse","out","--time-ms","120000"];
    for ask in asks {args.extend(["--ask",ask]);}let reused=run(&dir,&args);assert_eq!(reused.code,2,"{} {}",reused.stdout,reused.stderr);
    let again=result_json(&dir,&reused);for field in ["answers","nodes"] {assert_eq!(get(&j,field).value,get(&again,field).value);}
}

#[test]
fn fixed_empty_law_local_reads_keep_missing_observations() {
    #[path = "common/architecture_environment.rs"] mod fixture;
    use archsig::canonical::Json;
    let dir=finite_diagnostic_input("empty-fixed-missing",false);
    let path=dir.join("l.law");let law=std::fs::read_to_string(&path).unwrap();
    std::fs::write(path,law.replace("law optional localValid","local each(s:State) reads s.held; law optional localValid")).unwrap();
    let path=dir.join("a.json");let mut map=fixture::owned(&archsig::json::parse(&std::fs::read(&path).unwrap()).unwrap());
    let atoms=fixture::atoms(&mut map);let before=atoms.len();
    atoms.retain(|atom|!matches!(atom,Json::Obj(fields) if fields.get("id")==Some(&Json::str("p-held"))));assert_eq!(before-atoms.len(),1);
    std::fs::write(path,map.canonical()).unwrap();
    let asks=["m=map(Reservations.Migration,on=@v/m,reading=Reservations)","l=localize($m.candidate.source)","d=diagnose($l.system)","n=needed($l)","k=needed($d)"];
    let result=execute(&dir,"out",&asks);assert_eq!(result.code,2,"{} {}",result.stdout,result.stderr);
    let j=result_json(&dir,&result);let local=&arr(get(&j,"answers"))[1];
    assert_eq!(s(get(local,"status")),"undetermined");assert!(!has(get(local,"outputs"),"system"));
    assert!(arr(get(local,"reasons")).iter().any(|r|s(get(r,"code"))=="missing_observation"));
    for i in [3,4] {let plan=get(output(&j,i,"plan"),"value");assert!(arr(get(plan,"requirements")).iter().any(|r| {
        let field=get(r,"field");s(get(field,"field"))=="Reservations.State.held" && s(get(field,"subject"))=="p"
    }));}
    let mut args=vec!["run","--atom-definition","d.json","--archmap","a.json","--law","l.law","--out","again","--reuse","out","--time-ms","120000"];
    for ask in asks {args.extend(["--ask",ask]);}let reused=run(&dir,&args);assert_eq!(reused.code,2,"{} {}",reused.stdout,reused.stderr);
    let again=result_json(&dir,&reused);for field in ["answers","nodes"] {assert_eq!(get(&j,field).value,get(&again,field).value);}
}

#[test]
fn integer_diagnostic_transport_follows_compound_law_bindings() {
    for nested in [false,true] { for (side,degree) in [("equation",0),("semantic",1)] {
        let dir=integer_transport_input(&format!("integer-compound-{nested}-{side}-{degree}"),true);
        let (ty,body)=if nested {
            ("(Option<List<Set<State>>>,Z)","(some(list<Set<State>>[set<State>{s,t},set<State>{s}]),2)")
        } else { ("(State,Z)","(s,2)") };
        let path=dir.join("l.law");let law=std::fs::read_to_string(&path).unwrap();
        std::fs::write(&path,law.replace("law optional localValid",&format!(
            "view packed(s:State,t:State):{ty}={body}; law optional packedLaw(s:State,b:{ty}):s.free=b.1; law optional localValid"))).unwrap();
        let ld=format!("d=diagnose($l.system,side={side},degree={degree})");
        let rd=format!("e=diagnose($r.system,side={side},degree={degree})");
        let asks=["m=map(Reservations.Migration,on=@v/m,reading=Reservations)",
            "x=evaluate(Reservations.packed,on=$m.candidate.source,s=@v/p,t=@v/q)",
            "y=evaluate(Reservations.packed,on=$m.candidate.target,s=@v/transport_z,t=@v/transport_a)",
            "l=localize($m.candidate.source,law=Reservations.packedLaw,s=@v/p,b=$x.value,using=Reservations.move)",
            "r=localize($m.candidate.target,law=Reservations.packedLaw,s=@v/transport_z,b=$y.value,using=Reservations.move)",
            &ld,&rd,"c=compare($d.diagnostic,to=$e.diagnostic,kind=diagnostics,along=$m.operation)"];
        let r=execute(&dir,"out",&asks);assert_eq!(r.code,0,"{nested}/{side}/{degree}: {} {}",r.stdout,r.stderr);
        let j=result_json(&dir,&r);let cmp=get(output(&j,7,"comparison"),"value");
        assert_eq!(s(get(&arr(get(&j,"answers"))[7],"status")),"established");
        for field in ["kernel","cokernel"] {let group=get(node(&j,get(cmp,field)),"value");assert_eq!(num(get(group,"free_rank")),0);assert!(arr(get(group,"torsion")).is_empty());}
        assert_eq!(has(cmp,"class_transport"),degree==1);
        if degree==1 { assert_eq!(s(get(get(node(&j,get(cmp,"class_transport")),"judgment"),"status")),"established"); }
        let mut args=vec!["run","--atom-definition","d.json","--archmap","a.json","--law","l.law","--out","again","--reuse","out","--time-ms","120000"];
        for ask in asks { args.extend(["--ask",ask]); }
        let reused=run(&dir,&args);assert_eq!(reused.code,0,"{} {}",reused.stdout,reused.stderr);
        let again=result_json(&dir,&reused);for field in ["answers","nodes"] {assert_eq!(get(&j,field).value,get(&again,field).value);}
    }}
}

#[test]
fn integer_diagnostic_transport_rejects_a_different_compound_binding() {
    for wrong_value in [false,true] {
        let dir=integer_transport_input(&format!("integer-compound-mismatch-{wrong_value}"),true);
        let path=dir.join("l.law");let law=std::fs::read_to_string(&path).unwrap();
        std::fs::write(&path,law.replace("law optional localValid",
            "view packed(s:State):(State,Z)=(s,2); view other(s:State):(State,Z)=(s,3); law optional packedLaw(s:State,b:(State,Z)):s.free=b.1; law optional localValid")).unwrap();
        let target=if wrong_value {"y=evaluate(Reservations.other,on=$m.candidate.target,s=@v/transport_z)"} else {"y=evaluate(Reservations.packed,on=$m.candidate.target,s=@v/transport_a)"};
        let r=execute(&dir,"out",&["m=map(Reservations.Migration,on=@v/m,reading=Reservations)",
            "x=evaluate(Reservations.packed,on=$m.candidate.source,s=@v/p)",target,
            "l=localize($m.candidate.source,law=Reservations.packedLaw,s=@v/p,b=$x.value,using=Reservations.move)",
            "r=localize($m.candidate.target,law=Reservations.packedLaw,s=@v/transport_z,b=$y.value,using=Reservations.move)",
            "d=diagnose($l.system,degree=0)","e=diagnose($r.system,degree=0)",
            "c=compare($d.diagnostic,to=$e.diagnostic,kind=diagnostics,along=$m.operation)","n=needed($c)"]);
        assert_eq!(r.code,2,"{} {}",r.stdout,r.stderr);let j=result_json(&dir,&r);
        let answer=&arr(get(&j,"answers"))[7];assert_eq!(s(get(answer,"status")),"undetermined");
        assert!(!has(get(answer,"outputs"),"comparison"));
        assert!(arr(get(answer,"reasons")).iter().any(|r|s(get(r,"code"))=="unsupported_algorithm"));
        assert_eq!(s(get(&arr(get(&j,"answers"))[8],"status")),"established");
    }
}

#[test]
fn integer_local_laws_read_fields_through_bound_tuple_references() {
    for (side,degree) in [("equation",0),("equation",1),("semantic",0),("semantic",1)] {
        let dir=integer_transport_input(&format!("integer-projected-reference-{side}-{degree}"),true);
        let path=dir.join("l.law");let law=std::fs::read_to_string(&path).unwrap();
        std::fs::write(path,law.replace("law optional localValid",
            "view packed(s:State):(State,Z)=(s,2); law optional packedLaw(b:(State,Z)):b.0.free=b.1; law optional localValid")).unwrap();
        let ld=format!("d=diagnose($l.system,side={side},degree={degree})");let rd=format!("e=diagnose($r.system,side={side},degree={degree})");
        let asks=["m=map(Reservations.Migration,on=@v/m,reading=Reservations)",
            "x=evaluate(Reservations.packed,on=$m.candidate.source,s=@v/p)",
            "y=evaluate(Reservations.packed,on=$m.candidate.target,s=@v/transport_z)",
            "l=localize($m.candidate.source,law=Reservations.packedLaw,b=$x.value,using=Reservations.move)",
            "r=localize($m.candidate.target,law=Reservations.packedLaw,b=$y.value,using=Reservations.move)",
            &ld,&rd,"c=compare($d.diagnostic,to=$e.diagnostic,kind=diagnostics,along=$m.operation)"];
        let r=execute(&dir,"out",&asks);assert_eq!(r.code,0,"{side}/{degree}: {} {}",r.stdout,r.stderr);let j=result_json(&dir,&r);
        for i in [5,6] {
            let space=get(output(&j,i,"space"),"value");let group=get(node(&j,get(space,"module")),"value");
            assert_eq!(num(get(group,"free_rank")),if degree==0 {1}else{0});assert!(arr(get(group,"torsion")).is_empty());
        }
        let cmp=get(output(&j,7,"comparison"),"value");assert_eq!(s(get(&arr(get(&j,"answers"))[7],"status")),"established");
        for field in ["kernel","cokernel"] {let group=get(node(&j,get(cmp,field)),"value");assert_eq!(num(get(group,"free_rank")),0);assert!(arr(get(group,"torsion")).is_empty());}
        let mut args=vec!["run","--atom-definition","d.json","--archmap","a.json","--law","l.law","--out","again","--reuse","out","--time-ms","120000"];
        for ask in asks {args.extend(["--ask",ask]);}let reused=run(&dir,&args);assert_eq!(reused.code,0,"{} {}",reused.stdout,reused.stderr);
        let again=result_json(&dir,&reused);for field in ["answers","nodes"] {assert_eq!(get(&j,field).value,get(&again,field).value);}
    }
}

#[test]
fn integer_projected_reference_keeps_the_missing_field_in_needed() {
    #[path = "common/architecture_environment.rs"] mod fixture;
    use archsig::canonical::Json;
    let dir=integer_transport_input("integer-projected-reference-missing",false);
    let path=dir.join("l.law");let law=std::fs::read_to_string(&path).unwrap();
    std::fs::write(path,law.replace("law optional localValid",
        "view packed(s:State):(State,Z)=(s,2); law optional packedLaw(b:(State,Z)):b.0.free=b.0.held; law optional localValid")).unwrap();
    let mut map=fixture::owned(&archsig::json::parse(&std::fs::read(dir.join("a.json")).unwrap()).unwrap());
    fixture::atoms(&mut map).retain(|a| !matches!(a,Json::Obj(f) if f.get("id")==Some(&Json::str("p-held"))));
    std::fs::write(dir.join("a.json"),map.canonical()).unwrap();
    let r=execute(&dir,"out",&["a=build(Reservations,on=@v/A)","x=evaluate(Reservations.packed,on=$a.object,s=@v/p)",
        "l=localize($a.object,law=Reservations.packedLaw,b=$x.value,using=Reservations.move)","d=diagnose($l.system)","n=needed($d)"]);
    assert_eq!(r.code,2,"{} {}",r.stdout,r.stderr);let j=result_json(&dir,&r);
    assert!(!has(get(&arr(get(&j,"answers"))[3],"outputs"),"class"));
    let plan=get(output(&j,4,"plan"),"value");assert!(arr(get(plan,"requirements")).iter().any(|r|{
        let f=get(r,"field");s(get(f,"subject"))=="p"&&s(get(f,"field"))=="Reservations.State.held"
    }));
}

#[test]
fn finite_diagnostics_transport_actual_states_between_architectures() {
    for change in [false,true] {for side in ["equation","semantic"] {for degree in [0,1] {
        let dir=finite_diagnostic_input_at(integer_transport_input(&format!("finite-transport-{change}-{side}-{degree}"),true),true);
        let path=dir.join("l.law");let law=std::fs::read_to_string(&path).unwrap();
        std::fs::write(path,law.replace("law optional localValid","local each(s:State) reads s.free; law optional localValid")).unwrap();
        let using=if change{",using=Reservations.choose"}else{""};
        let left=format!("l=localize($m.candidate.source,law=Reservations.localValid,s=@v/p{using})");
        let right=format!("r=localize($m.candidate.target,law=Reservations.localValid,s=@v/transport_z{using})");
        let ld=format!("d=diagnose($l.system,side={side},degree={degree})");let rd=format!("e=diagnose($r.system,side={side},degree={degree})");
        let asks=["m=map(Reservations.Migration,on=@v/m,reading=Reservations)",&left,&right,&ld,&rd,
            "c=compare($d.diagnostic,to=$e.diagnostic,kind=diagnostics,along=$m.operation)","n=needed($c)"];
        let r=execute(&dir,"out",&asks);assert_eq!(r.code,0,"{change}/{side}/{degree}: {} {}",r.stdout,r.stderr);let j=result_json(&dir,&r);
        let cmp=get(output(&j,5,"comparison"),"value");assert_eq!(s(get(&arr(get(&j,"answers"))[5],"status")),"established");
        let map=get(node(&j,get(cmp,"finite_map")),"value");node(&j,get(map,"source"));node(&j,get(map,"target"));
        let pairs=arr(get(map,"pairs"));assert_eq!(pairs.len(),if change{2}else{1});
        for pair in pairs {let pair=arr(pair);let x=get(node(&j,&pair[0]),"value");let y=get(node(&j,&pair[1]),"value");
            if change{let x=arr(x);let y=arr(y);assert_eq!(x.len(),2);assert_eq!(y.len(),2);assert_eq!(x[0].value,y[1].value);assert_eq!(x[1].value,y[0].value);} }
        for condition in arr(get(cmp,"conditions")){assert_eq!(s(get(get(node(&j,condition),"judgment"),"status")),"established");}
        let mut args=vec!["run","--atom-definition","d.json","--archmap","a.json","--law","l.law","--out","again","--reuse","out","--time-ms","120000"];
        for ask in asks{args.extend(["--ask",ask]);}let reused=run(&dir,&args);assert_eq!(reused.code,0,"{} {}",reused.stdout,reused.stderr);
        let again=result_json(&dir,&reused);for field in ["answers","nodes"]{assert_eq!(get(&j,field).value,get(&again,field).value);}
    }}}
}

#[test]
fn finite_diagnostic_transport_rejects_unrelated_law_bindings() {
    for change in [false,true] {
        let dir=finite_diagnostic_input_at(integer_transport_input(&format!("finite-transport-binding-{change}"),true),true);
        let using=if change{",using=Reservations.choose"}else{""};
        let left=format!("l=localize($m.candidate.source,law=Reservations.localValid,s=@v/p{using})");
        let right=format!("r=localize($m.candidate.target,law=Reservations.localValid,s=@v/transport_a{using})");
        let r=execute(&dir,"out",&["m=map(Reservations.Migration,on=@v/m,reading=Reservations)",&left,&right,
            "d=diagnose($l.system)","e=diagnose($r.system)",
            "c=compare($d.diagnostic,to=$e.diagnostic,kind=diagnostics,along=$m.operation)","n=needed($c)"]);
        assert_eq!(r.code,2,"{} {}",r.stdout,r.stderr);let j=result_json(&dir,&r);
        let answer=&arr(get(&j,"answers"))[5];assert_eq!(s(get(answer,"status")),"undetermined");
        assert!(!has(get(answer,"outputs"),"comparison"));
        assert!(arr(get(answer,"reasons")).iter().any(|r|s(get(r,"code"))=="unsupported_algorithm"));
        assert_eq!(s(get(&arr(get(&j,"answers"))[6],"status")),"established");
    }
}

#[test]
fn finite_diagnostics_compare_different_changes_by_their_actual_states() {
    for constant in [false,true] {for side in ["equation","semantic"] {for degree in [0,1] {
        let dir=finite_diagnostic_input(&format!("finite-different-changes-{constant}-{side}-{degree}"),true);
        let path=dir.join("l.law");let law=std::fs::read_to_string(&path).unwrap();
        let body=if constant{"true"}else{"not b"};
        std::fs::write(path,law.replace("law optional localValid",&format!("change other(s:State,b:Bool)=s with{{free={body}}}; law optional localValid"))).unwrap();
        let ld=format!("d=diagnose($l.system,side={side},degree={degree})");let rd=format!("e=diagnose($r.system,side={side},degree={degree})");
        let asks=["m=map(Reservations.Migration,on=@v/m,reading=Reservations)",
            "l=localize($m.candidate.source,law=Reservations.localValid,s=@v/p,using=Reservations.choose)",
            "r=localize($m.candidate.source,law=Reservations.localValid,s=@v/p,using=Reservations.other)",
            &ld,&rd,"c=compare($d.diagnostic,to=$e.diagnostic,kind=diagnostics,along=$m.operation)","n=needed($c)"];
        let mismatch=constant&&side=="semantic";
        let r=execute(&dir,"out",&asks);assert_eq!(r.code,if mismatch{2}else{0},"{constant}/{side}/{degree}: {} {}",r.stdout,r.stderr);let j=result_json(&dir,&r);
        let answer=&arr(get(&j,"answers"))[5];
        if mismatch {
            assert_eq!(s(get(answer,"status")),"undetermined");assert!(!has(get(answer,"outputs"),"comparison"));
            assert!(arr(get(answer,"reasons")).iter().any(|r|s(get(r,"code"))=="unsupported_algorithm"));
        } else {
            assert_eq!(s(get(answer,"status")),"established");let cmp=get(output(&j,5,"comparison"),"value");
            let map=get(node(&j,get(cmp,"finite_map")),"value");node(&j,get(map,"source"));node(&j,get(map,"target"));
            let pairs=arr(get(map,"pairs"));assert_eq!(pairs.len(),2);
            let mut states=vec![];
            for pair in pairs {let pair=arr(pair);let x=get(node(&j,&pair[0]),"value");let y=get(node(&j,&pair[1]),"value");assert_eq!(x.value,y.value);
                states.push(arr(x).iter().map(|n|match n.value{archsig::json::JValue::Bool(v)=>v,_=>panic!("Bool状態")}).collect::<Vec<_>>());}
            assert_eq!(states,vec![vec![true,false],vec![true,true]]);
            for condition in arr(get(cmp,"conditions")){assert_eq!(s(get(get(node(&j,condition),"judgment"),"status")),"established");}
        }
        assert_eq!(s(get(&arr(get(&j,"answers"))[6],"status")),"established");
        let mut args=vec!["run","--atom-definition","d.json","--archmap","a.json","--law","l.law","--out","again","--reuse","out","--time-ms","120000"];
        for ask in asks{args.extend(["--ask",ask]);}let reused=run(&dir,&args);assert_eq!(reused.code,r.code,"{} {}",reused.stdout,reused.stderr);
        let again=result_json(&dir,&reused);for field in ["answers","nodes"]{assert_eq!(get(&j,field).value,get(&again,field).value);}
    }}}
}

#[test]
fn finite_diagnostic_inclusion_keeps_the_map_and_refutes_preservation() {
    for mode in 0..3 {for side in ["equation","semantic"] {for degree in [0,1] {
        let dir=finite_diagnostic_input(&format!("finite-diagnostic-inclusion-{mode}-{side}-{degree}"),mode!=1);
        let path=dir.join("l.law");let law=std::fs::read_to_string(&path).unwrap();
        let extra=if mode==2 {"local each(s:State) reads s.free; local together(s:State,t:State) reads s.free,t.free; law optional joint(s:State,t:State):s.free=true and t.free=true; "}else{""};
        std::fs::write(path,law.replace("law optional localValid",&format!("change constant(s:State,b:Bool)=s with{{free=true}}; {extra}law optional localValid"))).unwrap();
        let selection=if mode==2 {"law=Reservations.joint,s=@v/p,t=@v/q"}else{"law=Reservations.localValid,s=@v/p"};
        let left=format!("l=localize($m.candidate.source,{selection},using=Reservations.constant)");
        let right=format!("r=localize($m.candidate.source,{selection},using=Reservations.choose)");
        let ld=format!("d=diagnose($l.system,side={side},degree={degree})");let rd=format!("e=diagnose($r.system,side={side},degree={degree})");
        let asks=["m=map(Reservations.Migration,on=@v/m,reading=Reservations)",
            &left,&right,
            &ld,&rd,"c=compare($d.diagnostic,to=$e.diagnostic,kind=diagnostics,along=$m.operation)","n=needed($c)"];
        let proper=mode==0&&side=="semantic";let r=execute(&dir,"out",&asks);
        assert_eq!(r.code,if proper||(mode==1&&degree==1){1}else{0},"{mode}/{side}/{degree}: {} {}",r.stdout,r.stderr);let j=result_json(&dir,&r);
        assert_eq!(s(get(&arr(get(&j,"answers"))[5],"status")),if proper{"refuted"}else{"established"});
        let cmp=get(output(&j,5,"comparison"),"value");let map=get(node(&j,get(cmp,"finite_map")),"value");
        let target_size=match mode {1=>0,2=>1,_=>2};let source_size=if proper{1}else{target_size};
        assert_eq!(arr(get(get(node(&j,get(map,"source")),"value"),"elements")).len(),source_size);
        assert_eq!(arr(get(get(node(&j,get(map,"target")),"value"),"elements")).len(),target_size);
        let pairs=arr(get(map,"pairs"));assert_eq!(pairs.len(),source_size);
        for pair in pairs {let pair=arr(pair);let x=get(node(&j,&pair[0]),"value");let y=get(node(&j,&pair[1]),"value");assert_eq!(x.value,y.value);
            if proper||mode==2 {assert!(arr(x).iter().all(|v|matches!(v.value,archsig::json::JValue::Bool(true))));}}
        let conditions=arr(get(cmp,"conditions"));
        assert_eq!(conditions.iter().any(|r|s(get(get(node(&j,r),"judgment"),"status"))=="refuted"),proper);
        if proper {assert!(conditions.iter().all(|r|s(get(get(node(&j,r),"value"),"predicate"))!="inverse_maps"));}
        assert_eq!(s(get(&arr(get(&j,"answers"))[6],"status")),"established");
        let mut args=vec!["run","--atom-definition","d.json","--archmap","a.json","--law","l.law","--out","again","--reuse","out","--time-ms","120000"];
        for ask in asks{args.extend(["--ask",ask]);}let reused=run(&dir,&args);assert_eq!(reused.code,r.code,"{} {}",reused.stdout,reused.stderr);
        let again=result_json(&dir,&reused);for field in ["answers","nodes"]{assert_eq!(get(&j,field).value,get(&again,field).value);}
    }}}
}

#[test]
fn finite_diagnostic_identifies_positions_only_when_all_values_agree() {
    #[path = "common/architecture_environment.rs"]
    mod fixture;
    use archsig::canonical::Json;
    for linked in [true, false] {
        for side in ["equation", "semantic"] {
            for degree in [0, 1] {
                let dir = finite_diagnostic_input_at(
                    diagnostic_compare_input(
                        &format!("finite-identify-{linked}-{side}-{degree}"),
                        false,
                        true,
                    ),
                    true,
                );
                let old = std::fs::read_to_string(dir.join("d.json")).unwrap();
                let old_digest = definition::check_definitions(&[("d", old.as_bytes())])
                    .unwrap()
                    .vocabularies["Reservations"]
                    .digest
                    .clone();
                let mut definitions =
                    fixture::owned(&archsig::json::parse(old.as_bytes()).unwrap());
                let Json::Arr(vocabs) = fixture::field(&mut definitions, "vocabularies") else {
                    panic!("vocabularies")
                };
                let Json::Arr(declarations) = fixture::field(&mut vocabs[0], "declarations") else {
                    panic!("declarations")
                };
                for declaration in declarations {
                    if fixture::field(declaration, "name") == &Json::str("Reservations.System") {
                        let Json::Arr(fields) = fixture::field(declaration, "fields") else {
                            panic!("fields")
                        };
                        for name in ["left", "right"] {
                            fields.push(Json::obj([
                                ("name", Json::str(name)),
                                (
                                    "type",
                                    Json::Arr(vec![
                                        Json::str("Ref"),
                                        Json::str("Reservations.State"),
                                    ]),
                                ),
                                ("meaning", Json::str("比較する状態。")),
                            ]));
                        }
                    }
                }
                let definitions = definitions.canonical();
                let digest = definition::check_definitions(&[("d", definitions.as_bytes())])
                    .unwrap()
                    .vocabularies["Reservations"]
                    .digest
                    .clone();
                let raw = std::fs::read_to_string(dir.join("a.json"))
                    .unwrap()
                    .replace(&old_digest, &digest);
                let mut map = fixture::owned(&archsig::json::parse(raw.as_bytes()).unwrap());
                let Json::Arr(snapshots) = fixture::field(&mut map, "snapshots") else {
                    panic!("snapshots")
                };
                let Json::Arr(subjects) = fixture::field(&mut snapshots[0], "subjects") else {
                    panic!("subjects")
                };
                let removed = ["s", "n", "mm", "z"].map(Json::str);
                subjects.retain(|v| !matches!(v,Json::Obj(f) if removed.contains(&f["id"])));
                let atoms = fixture::atoms(&mut map);
                atoms.retain(|v| !matches!(v,Json::Obj(f) if removed.contains(&f["subject"])));
                for atom in atoms.iter_mut() {
                    let Json::Obj(fields) = atom else {
                        panic!("atom")
                    };
                    if fields["field"] == Json::str("Reservations.State.held") {
                        fields.insert("value".into(), Json::str("0"));
                    }
                    if ["f-to", "l-from", "t-to"]
                        .map(Json::str)
                        .contains(&fields["id"])
                    {
                        fields.insert(
                            "value".into(),
                            Json::Arr(vec![Json::str("v"), Json::str("r")]),
                        );
                    }
                    if fields["id"] == Json::str("m-states") {
                        let Json::Arr(pairs) = fields.get_mut("value").unwrap() else {
                            panic!("pairs")
                        };
                        let Json::Arr(pair) = &mut pairs[1] else {
                            panic!("pair")
                        };
                        pair[1] = Json::Arr(vec![Json::str("v"), Json::str("r")]);
                    }
                }
                for (owner, left, right) in [("A", "p", "q"), ("B", "r", "r")] {
                    for (field, target) in [("left", left), ("right", right)] {
                        atoms.push(Json::obj([
                            ("id", Json::str(format!("{owner}-{field}"))),
                            ("subject", Json::str(owner)),
                            ("field", Json::str(format!("Reservations.System.{field}"))),
                            ("value", Json::Arr(vec![Json::str("v"), Json::str(target)])),
                            ("origin", Json::str("model")),
                        ]));
                    }
                }
                let predicate = if linked {
                    "x.left.free=x.right.free"
                } else {
                    "x.left.free=x.left.free and x.right.free=x.right.free"
                };
                let law = format!(
                    "law \"archsig.law/2\" semantics \"archsig/0.6.0\"; reading Reservations {{ use vocabulary Reservations version \"1\" digest \"{digest}\"; change choose(s:State,b:Bool)=s with{{free=b}}; law optional linked(x:System):{predicate}; }}"
                );
                std::fs::write(dir.join("d.json"), definitions).unwrap();
                std::fs::write(dir.join("a.json"), map.canonical()).unwrap();
                std::fs::write(dir.join("l.law"), law).unwrap();
                let ld = format!("d=diagnose($l.system,side={side},degree={degree})");
                let rd = format!("e=diagnose($r.system,side={side},degree={degree})");
                let asks = [
                    "m=map(Reservations.Migration,on=@v/m,reading=Reservations)",
                    "l=localize($m.candidate.source,law=Reservations.linked,x=@v/A,using=Reservations.choose)",
                    "r=localize($m.candidate.target,law=Reservations.linked,x=@v/B,using=Reservations.choose)",
                    &ld,
                    &rd,
                    "c=compare($d.diagnostic,to=$e.diagnostic,kind=diagnostics,along=$m.operation)",
                    "n=needed($c)",
                ];
                let r = execute(&dir, "out", &asks);
                assert_eq!(
                    r.code,
                    if linked { 0 } else { 2 },
                    "{linked}/{side}/{degree}: {} {}",
                    r.stdout,
                    r.stderr
                );
                let j = result_json(&dir, &r);
                let answer = &arr(get(&j, "answers"))[5];
                assert!(has(
                    get(&arr(get(&j, "answers"))[0], "outputs"),
                    "operation"
                ));
                if linked {
                    assert_eq!(s(get(answer, "status")), "established");
                    let cmp = get(output(&j, 5, "comparison"), "value");
                    let map = get(node(&j, get(cmp, "finite_map")), "value");
                    let pairs = arr(get(map, "pairs"));
                    assert_eq!(pairs.len(), 2);
                    let mut observed = vec![];
                    for pair in pairs {
                        let pair = arr(pair);
                        let x = arr(get(node(&j, &pair[0]), "value"));
                        let y = arr(get(node(&j, &pair[1]), "value"));
                        assert_eq!(x.len(), 2);
                        assert_eq!(y.len(), 1);
                        assert_eq!(x[0].value, y[0].value);
                        assert_eq!(x[1].value, y[0].value);
                        observed.push(match y[0].value {
                            archsig::json::JValue::Bool(v) => v,
                            _ => panic!("Bool"),
                        });
                    }
                    observed.sort();
                    assert_eq!(observed, vec![false, true]);
                    for condition in arr(get(cmp, "conditions")) {
                        assert_eq!(
                            s(get(get(node(&j, condition), "judgment"), "status")),
                            "established"
                        );
                    }
                } else {
                    assert_eq!(s(get(answer, "status")), "undetermined");
                    assert!(!has(get(answer, "outputs"), "comparison"));
                    assert!(
                        arr(get(answer, "reasons"))
                            .iter()
                            .any(|r| s(get(r, "code")) == "unsupported_algorithm")
                    );
                }
                assert_eq!(s(get(&arr(get(&j, "answers"))[6], "status")), "established");
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
                for field in ["answers", "nodes"] {
                    assert_eq!(get(&j, field).value, get(&again, field).value);
                }
            }
        }
    }
}

fn finite_integer_local_system_cases(reads: Option<&str>) {
    let explicit = reads.is_some();
    for mode in [0, 1, 2] {
        for degree in [0, 1] {
            let dir = diagnostic_compare_input(
                &format!("finite-change-integer-fields-{explicit}-{mode}-{degree}"),
                true,
                true,
            );
            let path = dir.join("l.law");
            let digest = definition::check_definitions(&[(
                "d",
                &std::fs::read(dir.join("d.json")).unwrap(),
            )])
            .unwrap()
            .vocabularies["Reservations"]
                .digest
                .clone();
            let law = format!(
                "law \"archsig.law/2\" semantics \"archsig/0.6.0\"; reading Reservations {{ use vocabulary Reservations version \"1\" digest \"{digest}\"; change choose(s:State,b:Bool)=s with{{free=if b then 2 else 3}}; law optional localValid(s:State):s.free={}; }}",
                if mode == 1 { 4 } else { 2 }
            );
            let law = if let Some(reads) = reads { law.replace("change choose", &format!("local here(s:State) reads {reads}; change choose")) } else {law};
            std::fs::write(path, law).unwrap();
            let local = if mode == 2 {
                "l=localize($m.candidate.source,using=Reservations.choose)"
            } else {
                "l=localize($m.candidate.source,law=Reservations.localValid,s=@v/p,using=Reservations.choose)"
            };
            let eq = format!("d=diagnose($l.system,side=equation,degree={degree})");
            let sem = format!("e=diagnose($l.system,side=semantic,degree={degree})");
            let asks = [
                "m=map(Reservations.Migration,on=@v/m,reading=Reservations)",
                local,
                &eq,
                &sem,
                "c=compare($d.diagnostic,to=$d.diagnostic,kind=diagnostics,along=$m.operation)",
                "f=compare($e.diagnostic,to=$e.diagnostic,kind=diagnostics,along=$m.operation)",
                "n=needed($l)",
            ];
            let r = execute(&dir, "out", &asks);
            assert_eq!(
                r.code,
                if mode == 1 && degree == 1 { 1 } else { 0 },
                "{mode}/{degree}: {} {}",
                r.stdout,
                r.stderr
            );
            let j = result_json(&dir, &r);
            assert!(has(get(&arr(get(&j, "answers"))[1], "outputs"), "system"));
            let space = get(output(&j, 2, "space"), "value");
            let group = get(node(&j, get(space, "module")), "value");
            assert_eq!(
                num(get(group, "free_rank")),
                if degree == 1 {
                    0
                } else if mode == 2 {
                    2
                } else {
                    1
                }
            );
            assert!(arr(get(group, "torsion")).is_empty());
            let diagnostic = get(output(&j, 3, "diagnostic"), "value");
            let restriction = get(node(&j, get(diagnostic, "restriction")), "value");
            let domain = get(node(&j, get(restriction, "source")), "value");
            let values = arr(get(domain, "elements"));
            assert_eq!(
                values.len(),
                if mode == 1 {
                    0
                } else if mode == 2 {
                    4
                } else {
                    2
                }
            );
            let mut states = vec![];
            for v in values {
                states.push(
                    arr(get(node(&j, v), "value"))
                        .iter()
                        .map(|x| s(x).to_owned())
                        .collect::<Vec<_>>(),
                );
            }
            states.sort();
            if mode == 0 {
                assert_eq!(
                    states,
                    vec![
                        vec!["2".to_string(), "2".to_string()],
                        vec!["2".to_string(), "3".to_string()]
                    ]
                );
            }
            for i in [4, 5, 6] {
                assert_eq!(s(get(&arr(get(&j, "answers"))[i], "status")), "established");
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
            for field in ["answers", "nodes"] {
                assert_eq!(get(&j, field).value, get(&again, field).value);
            }
        }
    }
}

#[test]
fn finite_change_on_integer_fields_keeps_both_local_state_systems() {
    finite_integer_local_system_cases(None);
}
#[test]
fn finite_integer_localization_uses_declared_local_reads() {
    for reads in ["s.free,s.held", "(s.free,s.held)"] {
        finite_integer_local_system_cases(Some(reads));
    }
}

#[test]
fn finite_integer_localization_keeps_missing_fixed_fields() {
    #[path = "common/architecture_environment.rs"]
    mod fixture;
    use archsig::canonical::Json;
    let dir = diagnostic_compare_input("finite-integer-missing", true, true);
    let path = dir.join("l.law");
    let law = std::fs::read_to_string(&path).unwrap();
    std::fs::write(path,law.replace("law optional localValid","change choose(s:State,b:Bool)=s with{free=if b then 2 else 3}; law optional localValid").replace("localValid(s:State):s.free=2","localValid(s:State):s.free=s.held")).unwrap();
    let mut map =
        fixture::owned(&archsig::json::parse(&std::fs::read(dir.join("a.json")).unwrap()).unwrap());
    fixture::atoms(&mut map).retain(|a| !matches!(a,Json::Obj(f) if f["id"]==Json::str("p-held")));
    std::fs::write(dir.join("a.json"), map.canonical()).unwrap();
    let asks = [
        "m=map(Reservations.Migration,on=@v/m,reading=Reservations)",
        "l=localize($m.candidate.source,law=Reservations.localValid,s=@v/p,using=Reservations.choose)",
        "d=diagnose($l.system)",
        "n=needed($d)",
    ];
    let r = execute(&dir, "out", &asks);
    assert_eq!(r.code, 2, "{} {}", r.stdout, r.stderr);
    let j = result_json(&dir, &r);
    let a = &arr(get(&j, "answers"))[1];
    assert!(!has(get(a, "outputs"), "system"));
    assert!(
        arr(get(a, "reasons"))
            .iter()
            .any(|r| s(get(r, "code")) == "missing_observation")
    );
    let plan = get(output(&j, 3, "plan"), "value");
    assert!(arr(get(plan, "requirements")).iter().any(|r| {
        let f = get(r, "field");
        s(get(f, "subject")) == "p" && s(get(f, "field")) == "Reservations.State.held"
    }));
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
    assert_eq!(reused.code, 2, "{} {}", reused.stdout, reused.stderr);
    let again = result_json(&dir, &reused);
    for field in ["answers", "nodes"] {
        assert_eq!(get(&j, field).value, get(&again, field).value);
    }
}

fn finite_integer_repaired_fixed_values(explicit: bool) {
    let dir = diagnostic_compare_input(&format!("finite-integer-repaired-fixed-{explicit}"), true, true);
    let digest = definition::check_definitions(&[("d", &std::fs::read(dir.join("d.json")).unwrap())])
        .unwrap().vocabularies["Reservations"].digest.clone();
    std::fs::write(dir.join("l.law"), format!(
        "law \"archsig.law/2\" semantics \"archsig/0.6.0\"; reading Reservations {{ use vocabulary Reservations version \"1\" digest \"{digest}\"; change setHeld(s:State)=s with{{held=3}}; change choose(s:State,b:Bool)=s with{{free=if b then 2 else 3}}; law optional ready(s:State):s.held=3; law optional localValid(s:State):s.free=s.held; view held(s:State):Z=s.held; }}"
    )).unwrap();
    if explicit {
        let path=dir.join("l.law");
        let law=std::fs::read_to_string(&path).unwrap().replace("change setHeld", "local here(s:State) when s.held=3 reads 2*s.free+s.held,s.held; change setHeld");
        std::fs::write(path,law).unwrap();
    }
    let asks = [
        "a=map(Reservations.Migration,on=@v/m,reading=Reservations)",
        "r=repair(Reservations.ready,on=$a.candidate.source,using=Reservations.setHeld)",
        "l=localize($r.object,law=Reservations.localValid,s=@v/p,using=Reservations.choose)",
        "d=diagnose($l.system,side=equation,degree=0)",
        "e=diagnose($l.system,side=semantic,degree=0)",
        "n=needed($l)",
        "v=evaluate(Reservations.held,on=$r.object,s=@v/p)",
        "old=evaluate(Reservations.held,on=$a.candidate.source,s=@v/p)",
    ];
    let r = execute(&dir,"out",&asks);
    assert_eq!(r.code,0,"{} {}",r.stdout,r.stderr);
    let j=result_json(&dir,&r);
    if explicit {
        let system=get(output(&j,2,"system"),"value");
        let mut checked=false;
        for context in arr(get(system,"contexts")) {
            for read in arr(get(get(node(&j,context),"value"),"readings")) {
                let domain=get(node(&j,get(read,"domain")),"value");
                if s(get(domain,"kind"))!="image" {continue;}
                let map=get(node(&j,get(domain,"map")),"value");
                let linear=get(node(&j,get(map,"linear")),"value");
                let columns=arr(get(linear,"columns"));
                assert_eq!(columns.len(),1);
                assert_eq!(s(get(node(&j,&arr(&columns[0])[0]),"value")),"2");
                let offset=get(node(&j,get(map,"offset")),"value");
                assert_eq!(s(get(node(&j,&arr(get(offset,"coordinates"))[0]),"value")),"3");
                checked=true;
            }
        }
        assert!(checked,"修復値をoffsetとする整数read像がない");
    }
    assert_eq!(s(get(output(&j,6,"value"),"value")),"3");
    assert_eq!(s(get(output(&j,7,"value"),"value")),"0");
    let space=get(output(&j,3,"space"),"value");
    assert_eq!(num(get(get(node(&j,get(space,"module")),"value"),"free_rank")),1);
    let diagnostic=get(output(&j,4,"diagnostic"),"value");
    let restriction=get(node(&j,get(diagnostic,"restriction")),"value");
    let domain=get(node(&j,get(restriction,"source")),"value");
    let mut states=arr(get(domain,"elements")).iter().map(|v|
        arr(get(node(&j,v),"value")).iter().map(|x|s(x).to_owned()).collect::<Vec<_>>()
    ).collect::<Vec<_>>();
    states.sort();
    assert_eq!(states,vec![vec!["3".to_string(),"2".to_string()],vec!["3".to_string(),"3".to_string()]]);
    assert_eq!(s(get(&arr(get(&j,"answers"))[5],"status")),"established");
    let mut args=vec!["run","--atom-definition","d.json","--archmap","a.json","--law","l.law","--out","again","--reuse","out","--time-ms","120000"];
    for ask in asks {args.extend(["--ask",ask]);}
    let reused=run(&dir,&args);
    assert_eq!(reused.code,r.code,"{} {}",reused.stdout,reused.stderr);
    let again=result_json(&dir,&reused);
    for field in ["answers","nodes"] {assert_eq!(get(&j,field).value,get(&again,field).value);}
}

#[test]
fn finite_integer_localization_reads_repaired_fixed_values() {
    finite_integer_repaired_fixed_values(false);
}
#[test]
fn finite_integer_declared_read_keeps_repaired_guard_and_affine_offset() {
    finite_integer_repaired_fixed_values(true);
}

fn finite_integer_read_input(name: &str, known: bool, joint: bool) -> std::path::PathBuf {
    let definitions=r#"{"format":"archsig.atom-definition/1","semantics":"archsig/0.6.0","vocabularies":[{"semantics":"archsig/0.6.0","namespace":"Pair","version":"1","dependencies":[],"declarations":[{"kind":"entity","name":"Pair.State","meaning":"二つの自由整数と固定値。","parameters":[],"fields":[{"name":"x","type":"Z","meaning":"第一座標。"},{"name":"y","type":"Z","meaning":"第二座標。"},{"name":"z","type":"Z","meaning":"固定値。"}],"alignments":[]}]}]}"#;
    let checked=definition::check_definitions(&[("d",definitions.as_bytes())]).unwrap();
    let digest=&checked.vocabularies["Pair"].digest;
    let law=format!("law \"archsig.law/2\" semantics \"archsig/0.6.0\"; reading Pair {{ use vocabulary Pair version \"1\" digest \"{digest}\"; local Sum(s:State) reads s.x+s.y,s.z; change choose(s:State,b:Bool)=s with{{x=if b then 0 else 1,y=if b then 1 else 0}}; }}");
    let map=format!(r#"{{"format":"archsig.archmap/2","semantics":"archsig/0.6.0","vocabularies":[{{"namespace":"Pair","version":"1","digest":"{digest}"}}],"sources":[],"origins":[{{"id":"model","mode":"specification","method":"非単射readと欠測の独立試験。","locations":[],"note":"固定値zは未観測。"}}],"snapshots":[{{"id":"v","origin":"model","subjects":[{{"id":"s","type":"Pair.State","origin":"model"}}],"atoms":[{{"id":"x","subject":"s","field":"Pair.State.x","value":"0","origin":"model"}},{{"id":"y","subject":"s","field":"Pair.State.y","value":"0","origin":"model"}}]}}]}}"#);
    let law=if joint {law.replace("local Sum", "local Left(s:State) reads s.x; local Sum")} else {law};
    let map=if known {map.replace(r#""atoms":["#,r#""atoms":[{"id":"z","subject":"s","field":"Pair.State.z","value":"0","origin":"model"},"#)} else {map};
    let dir=workdir(name);
    for (name,text) in [("d.json",definitions),("l.law",&law),("a.json",&map)] {std::fs::write(dir.join(name),text).unwrap();}
    dir
}

#[test]
fn finite_integer_noninjective_read_retains_fixed_missing_requirement() {
    let dir=finite_integer_read_input("finite-integer-noninjective-missing",false,false);
    let asks=["a=build(Pair,on=@v/s)","l=localize($a.object,using=Pair.choose)","n=needed($l)"];
    let r=execute(&dir,"out",&asks);
    assert_eq!(r.code,2,"{} {}",r.stdout,r.stderr);
    let j=result_json(&dir,&r);
    let answer=&arr(get(&j,"answers"))[1];
    assert!(!has(get(answer,"outputs"),"system"));
    let reasons=arr(get(answer,"reasons"));
    for code in ["missing_observation"] {
        assert!(reasons.iter().any(|r|s(get(r,"code"))==code),"{code}: {reasons:?}");
    }
    assert!(reasons.iter().all(|r|s(get(r,"code"))!="unsupported_algorithm"));
    let plan=get(output(&j,2,"plan"),"value");
    assert!(arr(get(plan,"requirements")).iter().any(|r| {
        let field=get(r,"field");
        s(get(field,"snapshot"))=="v" && s(get(field,"subject"))=="s" && s(get(field,"field"))=="Pair.State.z"
    }));
    let mut args=vec!["run","--atom-definition","d.json","--archmap","a.json","--law","l.law","--out","again","--reuse","out","--time-ms","120000"];
    for ask in asks {args.extend(["--ask",ask]);}
    let reused=run(&dir,&args);
    assert_eq!(reused.code,r.code,"{} {}",reused.stdout,reused.stderr);
    let again=result_json(&dir,&reused);
    for field in ["answers","nodes"] {assert_eq!(get(&j,field).value,get(&again,field).value);}
}
fn rational_compare_input(name: &str, identity: bool) -> std::path::PathBuf {
    #[path = "common/architecture_environment.rs"]
    mod fixture;
    use archsig::canonical::Json;
    let dir = if identity {
        diagnostic_compare_input(name, true, true)
    } else {
        integer_transport_input(name, true)
    };
    let old = std::fs::read_to_string(dir.join("d.json")).unwrap();
    let d = old.replace("\"type\": \"Z\"", "\"type\": \"Q\"");
    let before = definition::check_definitions(&[("d", old.as_bytes())]).unwrap();
    let after = definition::check_definitions(&[("d", d.as_bytes())]).unwrap();
    let digest = &before.vocabularies["Reservations"].digest;
    let updated = &after.vocabularies["Reservations"].digest;
    let law = std::fs::read_to_string(dir.join("l.law"))
        .unwrap()
        .replace(digest, updated)
        .replace("(Z, Z)", "(Q, Q)")
        .replace("d:Z", "d:Q");
    let law = if identity {
        law.replace(
            "law optional localValid",
            "change move(s:State,d:Q)=s with{free=s.free+d}; law optional localValid",
        )
    } else {
        law
    };
    let text = std::fs::read_to_string(dir.join("a.json"))
        .unwrap()
        .replace(digest, updated);
    let mut map = fixture::owned(&archsig::json::parse(text.as_bytes()).unwrap());
    for atom in fixture::atoms(&mut map) {
        let Json::Obj(a) = atom else { panic!("atom") };
        if matches!(a.get("field"),Some(Json::Str(f)) if f=="Reservations.State.free"||f=="Reservations.State.held")
        {
            let v = a["value"].clone();
            a.insert("value".into(), Json::Arr(vec![v, Json::str("1")]));
        }
    }
    for (file, text) in [("d.json", d), ("l.law", law), ("a.json", map.canonical())] {
        std::fs::write(dir.join(file), text).unwrap();
    }
    dir
}
#[test]
fn rational_diagnostics_compare_actual_identity_maps_and_reuse() {
    for (side, degree) in [("equation", 0), ("equation", 1), ("semantic", 1)] {
        let dir = rational_compare_input(&format!("rational-compare-{side}-{degree}"), true);
        let d1 = format!("d1=diagnose($l.system,side={side},degree={degree})");
        let d2 = format!("d2=diagnose($l.system,side={side},degree={degree})");
        let asks=["m=map(Reservations.Migration,on=@v/m,reading=Reservations)","l=localize($m.candidate.source,law=Reservations.localValid,s=@v/p,using=Reservations.move)",&d1,&d2,"c=compare($d1.diagnostic,to=$d2.diagnostic,kind=diagnostics,along=$m.operation)"];
        let r = execute(&dir, "out", &asks);
        assert_eq!(r.code, 0, "{side}/{degree}: {} {}", r.stdout, r.stderr);
        let j = result_json(&dir, &r);
        let comparison = get(output(&j, 4, "comparison"), "value");
        let cochain = get(node(&j, get(comparison, "cochain_map")), "value");
        assert_eq!(arr(get(cochain, "components")).len(), degree as usize + 2);
        for map in arr(get(cochain, "components"))
            .iter()
            .chain(std::iter::once(get(comparison, "cohomology_map")))
        {
            let map = get(node(&j, map), "value");
            for (col, values) in arr(get(map, "columns")).iter().enumerate() {
                for (row, value) in arr(values).iter().enumerate() {
                    let value = arr(get(node(&j, value), "value"));
                    assert_eq!(s(&value[0]), if row == col { "1" } else { "0" });
                    assert_eq!(s(&value[1]), "1");
                }
            }
        }
        for key in ["kernel", "cokernel"] {
            let module = get(node(&j, get(comparison, key)), "value");
            assert_eq!(num(get(module, "free_rank")), 0);
            assert!(arr(get(module, "torsion")).is_empty());
            assert_eq!(
                s(get(get(node(&j, get(module, "ring")), "value"), "scalar")),
                "Q"
            );
        }
        assert_eq!(has(comparison, "class_transport"), degree == 1);
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
        let repeat = run(&dir, &args);
        assert_eq!(repeat.code, 0, "{} {}", repeat.stdout, repeat.stderr);
        let again = result_json(&dir, &repeat);
        for key in ["answers", "nodes"] {
            assert_eq!(get(&j, key).value, get(&again, key).value);
        }
    }
}

#[test]
fn rational_diagnostic_inclusion_has_field_cokernel_and_reuses_results() {
    for step in [0, 2, 3] {
        let dir = rational_compare_input(&format!("rational-inclusion-{step}"), false);
        let path = dir.join("l.law");
        let law = std::fs::read_to_string(&path).unwrap();
        std::fs::write(&path,law.replace("law optional localValid",&format!("change stride(s:State,d:Q)=s with{{free=s.free+{step}*d}}; law optional localValid"))).unwrap();
        let asks=["m=map(Reservations.Migration,on=@v/m,reading=Reservations)",
            "l=localize($m.candidate.source,law=Reservations.localValid,s=@v/p,using=Reservations.stride)",
            "r=localize($m.candidate.target,law=Reservations.localValid,s=@v/transport_z,using=Reservations.move)",
            "d=diagnose($l.system,side=semantic,degree=0)","e=diagnose($r.system,side=semantic,degree=0)",
            "c=compare($d.diagnostic,to=$e.diagnostic,kind=diagnostics,along=$m.operation)",
            "q=evaluate(Reservations.rank,on=$m.candidate.source,n=$c.comparison.cokernel.free_rank)"];
        let r = execute(&dir, "out", &asks);
        assert_eq!(
            r.code,
            i32::from(step == 0),
            "{step}: {} {}",
            r.stdout,
            r.stderr
        );
        let j = result_json(&dir, &r);
        let cmp = get(output(&j, 5, "comparison"), "value");
        assert_eq!(
            s(get(&arr(get(&j, "answers"))[5], "status")),
            if step == 0 { "refuted" } else { "established" }
        );
        for field in ["kernel", "cokernel"] {
            let module = get(node(&j, get(cmp, field)), "value");
            assert_eq!(
                num(get(module, "free_rank")),
                u64::from(step == 0 && field == "cokernel")
            );
            assert!(arr(get(module, "torsion")).is_empty());
            assert_eq!(
                s(get(get(node(&j, get(module, "ring")), "value"), "scalar")),
                "Q"
            );
        }
        assert_eq!(
            s(get(output(&j, 6, "value"), "value")),
            if step == 0 { "1" } else { "0" }
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
            "--time-ms",
            "120000",
        ];
        for ask in asks {
            args.extend(["--ask", ask]);
        }
        let reused = run(&dir, &args);
        assert_eq!(reused.code, r.code, "{} {}", reused.stdout, reused.stderr);
        let again = result_json(&dir, &reused);
        for field in ["answers", "nodes"] {
            assert_eq!(get(&j, field).value, get(&again, field).value);
        }
    }
}

#[test]
fn rational_diagnostic_transport_moves_fractional_classes_with_its_actual_matrix() {
    let dir = rational_compare_input("rational-transport-nonzero", false);
    let path = dir.join("l.law");
    let law = std::fs::read_to_string(&path).unwrap();
    std::fs::write(&path,law.replace("law optional localValid",
        "law optional loopShift(e:Reserve):e.to.free-e.from.free=rat(1,2); local Edge(e:Reserve) reads e.from.free,e.to.free; law optional localValid")).unwrap();
    let r = execute(
        &dir,
        "out",
        &[
            "m=map(Reservations.Migration,on=@v/m,reading=Reservations)",
            "l=localize($m.candidate.source,law=Reservations.loopShift,using=Reservations.move)",
            "r=localize($m.candidate.target,law=Reservations.loopShift,using=Reservations.move)",
            "d=diagnose($l.system)",
            "e=diagnose($r.system)",
            "c=compare($d.diagnostic,to=$e.diagnostic,kind=diagnostics,along=$m.operation)",
        ],
    );
    assert_eq!(r.code, 1, "{} {}", r.stdout, r.stderr);
    let j = result_json(&dir, &r);
    let twice = |v: &archsig::json::JNode| {
        let q = arr(v);
        let n = s(&q[0]).parse::<i64>().unwrap();
        let d = s(&q[1]).parse::<i64>().unwrap();
        assert_eq!(2 * n % d, 0);
        2 * n / d
    };
    let coordinates = |i| {
        let class = get(output(&j, i, "class"), "value");
        let vector = get(node(&j, get(class, "coordinates")), "value");
        arr(get(vector, "coordinates"))
            .iter()
            .map(|r| twice(get(node(&j, r), "value")))
            .collect::<Vec<_>>()
    };
    let x = coordinates(3);
    let y = coordinates(4);
    assert!(x.iter().any(|v| *v != 0));
    assert!(y.iter().any(|v| *v != 0));
    let cmp = get(output(&j, 5, "comparison"), "value");
    assert_eq!(s(get(&arr(get(&j, "answers"))[5], "status")), "established");
    let map = get(node(&j, get(cmp, "cohomology_map")), "value");
    let columns = arr(get(map, "columns"));
    assert_eq!(columns.len(), x.len());
    let image = (0..y.len())
        .map(|i| {
            columns
                .iter()
                .zip(&x)
                .map(|(column, x)| twice(get(node(&j, &arr(column)[i]), "value")) * x / 2)
                .sum::<i64>()
        })
        .collect::<Vec<_>>();
    assert_eq!(image, y);
    let chain = get(node(&j, get(cmp, "cochain_map")), "value");
    let mut changed = false;
    for component in arr(get(chain, "components")) {
        let map = get(node(&j, component), "value");
        for (col, column) in arr(get(map, "columns")).iter().enumerate() {
            for (row, x) in arr(column).iter().enumerate() {
                let x = twice(get(node(&j, x), "value"));
                changed |= x != 2 * i64::from(row == col);
            }
        }
    }
    assert!(changed, "patchの並び替えを反映するcochain成分がない");
}

#[test]
fn diagnostic_comparison_rejects_different_coefficient_rings() {
    #[path = "common/architecture_environment.rs"]
    mod fixture;
    use archsig::canonical::Json;
    let dir = diagnostic_compare_input("diagnostic-coefficient-rings", true, true);
    let old = std::fs::read_to_string(dir.join("d.json")).unwrap();
    let before = definition::check_definitions(&[("d", old.as_bytes())]).unwrap();
    let mut definitions = fixture::owned(&archsig::json::parse(old.as_bytes()).unwrap());
    fn field(j: &mut Json) {
        match j {
            Json::Obj(o) => {
                if o.get("name") == Some(&Json::str("held")) {
                    o.insert("type".into(), Json::str("Q"));
                }
                for v in o.values_mut() {
                    field(v);
                }
            }
            Json::Arr(xs) => {
                for x in xs {
                    field(x)
                }
            }
            _ => {}
        }
    }
    field(&mut definitions);
    let definitions = definitions.canonical();
    let after = definition::check_definitions(&[("d", definitions.as_bytes())]).unwrap();
    let digest = &after.vocabularies["Reservations"].digest;
    let text = std::fs::read_to_string(dir.join("a.json"))
        .unwrap()
        .replace(&before.vocabularies["Reservations"].digest, digest);
    let mut map = fixture::owned(&archsig::json::parse(text.as_bytes()).unwrap());
    for atom in fixture::atoms(&mut map) {
        let Json::Obj(a) = atom else { panic!("atom") };
        if a.get("field") == Some(&Json::str("Reservations.State.held")) {
            let v = a["value"].clone();
            a.insert("value".into(), Json::Arr(vec![v, Json::str("1")]));
        }
    }
    let law=format!("law \"archsig.law/2\" semantics \"archsig/0.6.0\"; reading Reservations {{ use vocabulary Reservations version \"1\" digest \"{digest}\"; law optional zi(s:State):s.free=s.free; law optional qi(s:State):s.held=s.held; change zm(s:State,d:Z)=s with{{free=s.free+d}}; change qm(s:State,d:Q)=s with{{held=s.held+d}}; }}");
    for (name, text) in [
        ("d.json", definitions),
        ("l.law", law),
        ("a.json", map.canonical()),
    ] {
        std::fs::write(dir.join(name), text).unwrap();
    }
    for side in ["equation", "semantic"] {
        for reverse in [false, true] {
            let d = format!("d=diagnose($l.system,side={side},degree=0)");
            let e = format!("e=diagnose($r.system,side={side},degree=0)");
            let mut asks = vec![
                "m=map(Reservations.Migration,on=@v/m,reading=Reservations)",
                "l=localize($m.candidate.source,law=Reservations.zi,s=@v/p,using=Reservations.zm)",
                "r=localize($m.candidate.source,law=Reservations.qi,s=@v/p,using=Reservations.qm)",
                &d,
                &e,
            ];
            let valid = execute(&dir, &format!("valid-{side}-{reverse}"), &asks);
            assert_eq!(valid.code, 0, "{} {}", valid.stdout, valid.stderr);
            asks.push(if reverse {
                "c=compare($e.diagnostic,to=$d.diagnostic,kind=diagnostics,along=$m.operation)"
            } else {
                "c=compare($d.diagnostic,to=$e.diagnostic,kind=diagnostics,along=$m.operation)"
            });
            let r = execute(&dir, &format!("out-{side}-{reverse}"), &asks);
            assert_eq!(r.code, 64, "{} {}", r.stdout, r.stderr);
        }
    }
}

#[test]
fn diagnostic_transport_keeps_path_bindings_and_named_compositions() {
    for mode in ["identity", "arrow", "composite", "nested", "fixed"] {
        for wrong in [false, true] {
            let dir = integer_transport_input(&format!("diagnostic-path-{mode}-{wrong}"), true);
            let path = dir.join("l.law");
            let law = std::fs::read_to_string(&path).unwrap();
            std::fs::write(&path,law.replace("law optional localValid","law optional pathLaw(s:State,p:Path<State,State>):s.free=2; law optional localValid")).unwrap();
            if mode == "nested" {
                let law=std::fs::read_to_string(&path).unwrap().replace("p:Path<State,State>","p:(Path<State,State>,Z)").replace("law optional pathLaw","view packedPath(s:State):(Path<State,State>,Z)=(identity(s),2); law optional pathLaw");
                std::fs::write(&path,law).unwrap();
            }
            let mut asks = vec!["m=map(Reservations.Migration,on=@v/m,reading=Reservations)"];
            if mode == "nested" {
                asks.extend(["x=evaluate(Reservations.packedPath,on=$m.candidate.source,s=@v/p)",if wrong {"y=evaluate(Reservations.packedPath,on=$m.candidate.target,s=@v/transport_a)"}else{"y=evaluate(Reservations.packedPath,on=$m.candidate.target,s=@v/transport_z)"}]);
            } else if mode == "identity" || mode == "fixed" {
                asks.extend([
                    "x=evaluate(Reservations.emptyPath,on=$m.candidate.source,s=@v/p)",
                    if wrong {
                        "y=evaluate(Reservations.emptyPath,on=$m.candidate.target,s=@v/transport_a)"
                    } else {
                        "y=evaluate(Reservations.emptyPath,on=$m.candidate.target,s=@v/transport_z)"
                    },
                ]);
            } else {
                asks.extend([
                    "x=evaluate(Reservations.route,on=$m.candidate.source,e=@v/e)",
                    if wrong {
                        "y=evaluate(Reservations.route,on=$m.candidate.target,e=@v/transport_aa)"
                    } else {
                        "y=evaluate(Reservations.route,on=$m.candidate.target,e=@v/transport_zz)"
                    },
                ]);
            }
            if mode == "composite" {
                asks.extend([
                    "u=evaluate(Reservations.route,on=$m.candidate.source,e=@v/h)",
                    "v=evaluate(Reservations.route,on=$m.candidate.target,e=@v/transport_ll)",
                    "xx=compose($x.value,then=$u.value)",
                    "yy=compose($y.value,then=$v.value)",
                ]);
            }
            let left = if mode == "fixed" {
                "l=localize($m.candidate.source,law=Reservations.pathLaw,s=@v/p,p=$x.value)"
            } else if mode == "composite" {
                "l=localize($m.candidate.source,law=Reservations.pathLaw,s=@v/p,p=$xx.operation,using=Reservations.move)"
            } else {
                "l=localize($m.candidate.source,law=Reservations.pathLaw,s=@v/p,p=$x.value,using=Reservations.move)"
            };
            let right = if mode == "fixed" {
                "r=localize($m.candidate.target,law=Reservations.pathLaw,s=@v/transport_z,p=$y.value)"
            } else if mode == "composite" {
                "r=localize($m.candidate.target,law=Reservations.pathLaw,s=@v/transport_z,p=$yy.operation,using=Reservations.move)"
            } else {
                "r=localize($m.candidate.target,law=Reservations.pathLaw,s=@v/transport_z,p=$y.value,using=Reservations.move)"
            };
            asks.extend([
                left,
                right,
                "d=diagnose($l.system,degree=0)",
                "e=diagnose($r.system,degree=0)",
                "c=compare($d.diagnostic,to=$e.diagnostic,kind=diagnostics,along=$m.operation)",
            ]);
            let r = execute(&dir, "out", &asks);
            assert_eq!(
                r.code,
                if wrong { 2 } else { 0 },
                "{mode}/{wrong}: {} {}",
                r.stdout,
                r.stderr
            );
            let j = result_json(&dir, &r);
            if wrong {
                let answer = arr(get(&j, "answers")).last().unwrap();
                assert!(!has(get(answer, "outputs"), "comparison"));
                assert!(arr(get(answer, "reasons"))
                    .iter()
                    .any(|r| s(get(r, "code")) == "unsupported_algorithm"));
            } else {
                let cmp = get(output(&j, asks.len() - 1, "comparison"), "value");
                for field in if mode=="fixed" {vec![]} else {vec!["kernel", "cokernel"]} {
                    let group = get(node(&j, get(cmp, field)), "value");
                    assert_eq!(num(get(group, "free_rank")), 0);
                    assert!(arr(get(group, "torsion")).is_empty());
                }
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
            let repeat = run(&dir, &args);
            assert_eq!(repeat.code, r.code, "{} {}", repeat.stdout, repeat.stderr);
            let again = result_json(&dir, &repeat);
            for field in ["answers", "nodes"] {
                assert_eq!(get(&j, field).value, get(&again, field).value);
            }
        }
    }
}

#[test]
fn diagnostic_transport_compares_term_bindings_by_their_values() {
    for mode in ["finite", "integer", "rational", "nested", "fixed"] {
        for wrong in [false, true] {
            let dir = integer_transport_input(&format!("diagnostic-term-{mode}-{wrong}"), true);
            let (ty, left, right) = match mode {
                "finite" => ("Term<(Bool)->Z>", "fn(b:Bool)=>if b then 2 else 3", if wrong {"fn(c:Bool)=>if c then 2 else 4"} else {"fn(c:Bool)=>if not c then 3 else 1+1"}),
                "rational" => ("Term<(Q)->Q>", "fn(x:Q)=>x+rat(1,2)", if wrong {"fn(y:Q)=>y+rat(1,3)"} else {"fn(y:Q)=>rat(2,4)+y"}),
                "nested" => ("(Term<(Z)->Z>,Z)", "(fn(x:Z)=>x+x,2)", if wrong {"(fn(y:Z)=>2*y+1,2)"} else {"(fn(y:Z)=>2*y,2)"}),
                _ => ("Term<(Z)->Z>", "fn(x:Z)=>x+x", if wrong {"fn(y:Z)=>2*y+1"} else {"fn(y:Z)=>2*y"}),
            };
            let path = dir.join("l.law");
            let law = std::fs::read_to_string(&path).unwrap();
            let added = format!("view termLeft():{ty} = {left}; view termRight():{ty} = {right}; law optional termLaw(s:State,p:{ty}):s.free=2; law optional localValid");
            std::fs::write(&path,law.replace("law optional localValid",&added)).unwrap();
            let mut asks = vec![
                "m=map(Reservations.Migration,on=@v/m,reading=Reservations)",
                "x=evaluate(Reservations.termLeft,on=$m.candidate.source)",
                "y=evaluate(Reservations.termRight,on=$m.candidate.target)",
            ];
            asks.extend(if mode=="fixed" { [
                "l=localize($m.candidate.source,law=Reservations.termLaw,s=@v/p,p=$x.value)",
                "r=localize($m.candidate.target,law=Reservations.termLaw,s=@v/transport_z,p=$y.value)",
            ] } else { [
                "l=localize($m.candidate.source,law=Reservations.termLaw,s=@v/p,p=$x.value,using=Reservations.move)",
                "r=localize($m.candidate.target,law=Reservations.termLaw,s=@v/transport_z,p=$y.value,using=Reservations.move)",
            ] });
            asks.extend([
                "d=diagnose($l.system,degree=0)",
                "e=diagnose($r.system,degree=0)",
                "c=compare($d.diagnostic,to=$e.diagnostic,kind=diagnostics,along=$m.operation)",
            ]);
            let r=execute(&dir,"out",&asks);
            assert_eq!(r.code,if wrong {2} else {0},"{mode}/{wrong}: {} {}",r.stdout,r.stderr);
            let j=result_json(&dir,&r);
            if wrong {
                let answer=arr(get(&j,"answers")).last().unwrap();
                assert!(!has(get(answer,"outputs"),"comparison"));
                assert!(arr(get(answer,"reasons")).iter().any(|r|s(get(r,"code"))=="unsupported_algorithm"));
            } else {
                let cmp=get(output(&j,7,"comparison"),"value");
                if mode!="fixed" {for field in ["kernel","cokernel"] {
                    let group=get(node(&j,get(cmp,field)),"value");
                    assert_eq!(num(get(group,"free_rank")),0);
                    assert!(arr(get(group,"torsion")).is_empty());
                }}
            }
            let mut args=vec!["run","--atom-definition","d.json","--archmap","a.json","--law","l.law","--out","again","--reuse","out","--time-ms","120000"];
            for ask in asks {args.extend(["--ask",ask]);}
            let repeat=run(&dir,&args);
            assert_eq!(repeat.code,r.code,"{} {}",repeat.stdout,repeat.stderr);
            let again=result_json(&dir,&repeat);
            for field in ["answers","nodes"] {assert_eq!(get(&j,field).value,get(&again,field).value);}
        }
    }
}

#[test]
fn finite_integer_noninjective_reads_use_their_images_and_joint_cover() {
    for mode in ["plain", "constrained", "tuple", "parallel"] {
    let dir=finite_integer_read_input(&format!("finite-integer-joint-images-{mode}"),true,true);
    let path=dir.join("l.law");let law=std::fs::read_to_string(&path).unwrap();
    let law=match mode {
        "constrained" => law.replace("local Left", "law required total(s:State):s.x+s.y=1; local Left"),
        "parallel" => law.replace("local Left(s:State) reads s.x;", "local Delta(s:State) reads s.x-s.y,s.z; local Both(s:State) reads (s.x,s.y),s.z;"),
        "tuple" => law.replace("reads s.x+s.y,s.z", "reads (s.x+s.y+3,s.z)"),
        _ => law,
    };std::fs::write(path,law).unwrap();
    let asks=["a=build(Pair,on=@v/s)","l=localize($a.object,using=Pair.choose)",
        "e=diagnose($l.system,side=equation,degree=0)","d=diagnose($l.system,side=equation,degree=1)",
        "s=diagnose($l.system,side=semantic,degree=0)"];
    let r=execute(&dir,"out",&asks);
    assert_eq!(r.code,0,"{} {}",r.stdout,r.stderr);
    let j=result_json(&dir,&r);
    let system=get(output(&j,1,"system"),"value");
    let sum=arr(get(system,"contexts")).iter().find(|r|{
        let locals=arr(get(get(node(&j,r),"value"),"locals"));
        locals.len()==1 && s(get(&locals[0],"declaration"))=="Pair.Sum"
    }).expect("Sumだけの局所がない");
    let mut count=0;
    for coefficient in arr(get(system,"coefficients")).iter().filter(|v|get(v,"context").value==sum.value) {
        count+=1;
        assert_eq!(num(get(get(node(&j,get(coefficient,"module")),"value"),"free_rank")),if mode=="constrained" {0} else {1});
    }
    assert!(count>0);
    if mode=="parallel" {
        let delta=arr(get(system,"contexts")).iter().find(|r| {
            let locals=arr(get(get(node(&j,r),"value"),"locals"));
            locals.len()==1 && s(get(&locals[0],"declaration"))=="Pair.Delta"
        }).expect("同じ支持で異なるreadが失われた");
        assert_ne!(sum.value,delta.value);
        let state=arr(get(system,"semantic_states")).iter().find(|x|get(x,"context").value==delta.value).unwrap();
        assert_eq!(arr(get(get(node(&j,get(state,"state_image")),"value"),"elements")).len(),2);
    }
    let sem=arr(get(system,"semantic_states")).iter().find(|x|get(x,"context").value==sum.value).unwrap();
    let image=get(node(&j,get(sem,"state_image")),"value");assert_eq!(arr(get(image,"elements")).len(),1);
    let parameters=get(node(&j,get(sem,"parameters")),"value");assert_eq!(arr(get(get(parameters,"representation"),"values")).len(),2);
    for (i,rank) in [(2,if mode=="constrained" {1} else {2}),(3,0)] {
        let space=get(output(&j,i,"space"),"value");
        assert_eq!(num(get(get(node(&j,get(space,"module")),"value"),"free_rank")),rank);
    }
    assert_eq!(s(get(&arr(get(&j,"answers"))[4],"status")),"established");
    let mut args=vec!["run","--atom-definition","d.json","--archmap","a.json","--law","l.law","--out","again","--reuse","out","--time-ms","120000"];
    for ask in asks {args.extend(["--ask",ask]);}
    let repeat=run(&dir,&args);assert_eq!(repeat.code,r.code,"{} {}",repeat.stdout,repeat.stderr);
    let again=result_json(&dir,&repeat);
    for field in ["answers","nodes"] {assert_eq!(get(&j,field).value,get(&again,field).value);}
    }
}

#[test]
fn finite_integer_noninjective_read_requires_joint_visibility() {
    let dir=finite_integer_read_input("finite-integer-sum-only",true,false);
    let r=execute(&dir,"out",&["a=build(Pair,on=@v/s)","l=localize($a.object,using=Pair.choose)","n=needed($l)"]);
    assert_eq!(r.code,2,"{} {}",r.stdout,r.stderr);
    let j=result_json(&dir,&r);
    let answer=&arr(get(&j,"answers"))[1];assert!(!has(get(answer,"outputs"),"system"));
    let reasons=arr(get(answer,"reasons"));
    assert!(reasons.iter().any(|r|s(get(r,"code"))=="visibility_insufficient"));
    assert!(reasons.iter().all(|r|s(get(r,"code"))!="unsupported_algorithm"));
    assert_eq!(s(get(&arr(get(&j,"answers"))[2],"status")),"established");
}

#[test]
fn finite_integer_diagnostics_transport_noninjective_read_images() {
    finite_affine_diagnostics_transport_noninjective_read_images(false);
}
#[test]
fn finite_rational_diagnostics_transport_noninjective_read_images() {
    finite_affine_diagnostics_transport_noninjective_read_images(true);
}
fn finite_affine_diagnostics_transport_noninjective_read_images(rational: bool) {
    for mode in ["plain","parallel","collapsed"] { for degree in [0,1] {
        let dir=workdir(&format!("finite-affine-read-transport-{rational}-{mode}-{degree}"));
        std::fs::write(dir.join("d.json"),include_str!("fixtures/reservations.atoms.json")).unwrap();
        let map=include_str!("fixtures/configuration-operation.archmap.json")
            .replace("\"id\":\"r-free\",\"subject\":\"r\",\"field\":\"Reservations.State.free\",\"value\":\"4\"", "\"id\":\"r-free\",\"subject\":\"r\",\"field\":\"Reservations.State.free\",\"value\":\"2\"")
            .replace("\"id\":\"s-free\",\"subject\":\"s\",\"field\":\"Reservations.State.free\",\"value\":\"3\"", "\"id\":\"s-free\",\"subject\":\"s\",\"field\":\"Reservations.State.free\",\"value\":\"1\"");
        std::fs::write(dir.join("a.json"),map).unwrap();
        let extra=if mode!="plain" { "local Delta(s:State) reads s.free-s.held;" } else { "" };
        let mut law=include_str!("fixtures/public-compose.law").replace("view holdings", &format!(
            "law optional localValid(s:State):s.free=2; local Sum(s:State) reads s.free+s.held; local Left(s:State) reads s.free; {extra} change choose(s:State,b:Bool)=s with{{free=if b then 2 else 3,held=if b then 0 else -1}}; view holdings"));
        if mode=="collapsed" {law=law.replace("free=if b then 2 else 3,held=if b then 0 else -1","free=2,held=0");}
        std::fs::write(dir.join("l.law"),law).unwrap();
        if rational {
            #[path = "common/architecture_environment.rs"] mod fixture;
            use archsig::canonical::Json;
            let old=std::fs::read_to_string(dir.join("d.json")).unwrap();
            let d=old.replace("\"type\": \"Z\"","\"type\": \"Q\"");
            let before=definition::check_definitions(&[("d",old.as_bytes())]).unwrap();
            let after=definition::check_definitions(&[("d",d.as_bytes())]).unwrap();
            let old_digest=&before.vocabularies["Reservations"].digest;let digest=&after.vocabularies["Reservations"].digest;
            let law=std::fs::read_to_string(dir.join("l.law")).unwrap().replace(old_digest,digest).replace("(Z, Z)","(Q, Q)");
            let text=std::fs::read_to_string(dir.join("a.json")).unwrap().replace(old_digest,digest);
            let mut map=fixture::owned(&archsig::json::parse(text.as_bytes()).unwrap());
            for atom in fixture::atoms(&mut map) {let Json::Obj(a)=atom else {panic!("atom")};
                if matches!(a.get("field"),Some(Json::Str(f)) if f=="Reservations.State.free"||f=="Reservations.State.held") {
                    let v=a["value"].clone();a.insert("value".into(),Json::Arr(vec![v,Json::str("1")]));
                }
            }
            for (file,text) in [("d.json",d),("l.law",law),("a.json",map.canonical())] {std::fs::write(dir.join(file),text).unwrap();}
        }
        let ld=format!("d=diagnose($l.system,side=semantic,degree={degree})");
        let rd=format!("e=diagnose($r.system,side=semantic,degree={degree})");
        let asks=["m=map(Reservations.Migration,on=@v/m,reading=Reservations)",
            "l=localize($m.candidate.source,law=Reservations.localValid,s=@v/p,using=Reservations.choose)",
            "r=localize($m.candidate.target,law=Reservations.localValid,s=@v/r,using=Reservations.choose)",
            &ld,&rd,"c=compare($d.diagnostic,to=$e.diagnostic,kind=diagnostics,along=$m.operation)"];
        let r=execute(&dir,"out",&asks); assert_eq!(r.code,0,"{mode}/{degree}: {} {}",r.stdout,r.stderr);
        let j=result_json(&dir,&r);let cmp=get(output(&j,5,"comparison"),"value");
        let map=get(node(&j,get(cmp,"finite_map")),"value");
        let pairs=arr(get(map,"pairs"));assert_eq!(pairs.len(),if mode=="collapsed"{1}else{2});
        for pair in pairs {let pair=arr(pair);assert_eq!(get(node(&j,&pair[0]),"value").value,get(node(&j,&pair[1]),"value").value);}
        for condition in arr(get(cmp,"conditions")){assert_eq!(s(get(get(node(&j,condition),"judgment"),"status")),"established");}
        let mut args=vec!["run","--atom-definition","d.json","--archmap","a.json","--law","l.law","--out","again","--reuse","out","--time-ms","120000"];
        for ask in asks {args.extend(["--ask",ask]);}let reused=run(&dir,&args);assert_eq!(reused.code,0,"{} {}",reused.stdout,reused.stderr);
        let again=result_json(&dir,&reused);for field in ["answers","nodes"] {assert_eq!(get(&j,field).value,get(&again,field).value);}
    }}
}

#[test]
fn finite_change_on_rational_fields_keeps_full_equation_fibers() {
    for mode in ["implicit","coordinate","noninjective"] {for selected in [false,true] {for degree in [0,1] {
        let dir=rational_compare_input(&format!("finite-change-rational-fields-{mode}-{selected}-{degree}"),true);
        let digest=definition::check_definitions(&[("d",&std::fs::read(dir.join("d.json")).unwrap())]).unwrap().vocabularies["Reservations"].digest.clone();
        let mut law=format!("law \"archsig.law/2\" semantics \"archsig/0.6.0\"; reading Reservations {{ use vocabulary Reservations version \"1\" digest \"{digest}\"; change choose(s:State,b:Bool)=s with{{free=if b then rat(1,2) else rat(3,2)}}; law optional localValid(s:State):s.free=rat(1,2); }}");
        if mode=="coordinate" {law=law.replace("change choose","local Here(s:State) reads s.free; change choose");}
        if mode=="noninjective" {law=law.replace("change choose","local Sum(s:State) reads s.free+s.held; local Left(s:State) reads s.free; change choose").replace("else rat(3,2)}","else rat(3,2),held=if b then 0 else -1}");}
        std::fs::write(dir.join("l.law"),law).unwrap();
        let local=if selected {"l=localize($m.candidate.source,law=Reservations.localValid,s=@v/p,using=Reservations.choose)"}else{"l=localize($m.candidate.source,using=Reservations.choose)"};
        let eq=format!("d=diagnose($l.system,side=equation,degree={degree})");
        let sem=format!("e=diagnose($l.system,side=semantic,degree={degree})");
        let asks=["m=map(Reservations.Migration,on=@v/m,reading=Reservations)",local,
            &eq,&sem,"c=compare($d.diagnostic,to=$d.diagnostic,kind=diagnostics,along=$m.operation)",
            "f=compare($e.diagnostic,to=$e.diagnostic,kind=diagnostics,along=$m.operation)"];
        let r=execute(&dir,"out",&asks);assert_eq!(r.code,0,"{mode}/{selected}/{degree}: {} {}",r.stdout,r.stderr);
        let j=result_json(&dir,&r);let space=get(output(&j,2,"space"),"value");
        let group=get(node(&j,get(space,"module")),"value");assert_eq!(num(get(group,"free_rank")),if degree==1{0}else{(if mode=="noninjective"{4}else{2})-u64::from(selected)});
        assert!(arr(get(group,"torsion")).is_empty());
        let diagnostic=get(output(&j,3,"diagnostic"),"value");let restriction=get(node(&j,get(diagnostic,"restriction")),"value");
        let domain=get(node(&j,get(restriction,"source")),"value");assert_eq!(arr(get(domain,"elements")).len(),if selected{2}else{4});
        for v in arr(get(domain,"elements")) {let values=arr(get(node(&j,v),"value"));assert!(values.iter().any(|q|s(&arr(q)[1])=="2"));}
        for i in [4,5] {assert_eq!(s(get(&arr(get(&j,"answers"))[i],"status")),"established");}
        let mut args=vec!["run","--atom-definition","d.json","--archmap","a.json","--law","l.law","--out","again","--reuse","out","--time-ms","120000"];
        for ask in asks {args.extend(["--ask",ask]);}let reused=run(&dir,&args);assert_eq!(reused.code,0,"{} {}",reused.stdout,reused.stderr);
        let again=result_json(&dir,&reused);for field in ["answers","nodes"] {assert_eq!(get(&j,field).value,get(&again,field).value);}
    }}}
}

#[test]
fn universal_laws_localize_integer_and_rational_affine_changes() {
    for rational in [false,true] {
        for (predicate, rank, empty) in [("z=z",2,false),("s.free+z=z+2",0,false),
            ("z=s.free",2,true),("(let a=z+w in a=w+z) and s.free=2",0,false)] {
            let dir = if rational { rational_compare_input("universal-affine-local-q",true) }
                else { diagnostic_compare_input("universal-affine-local-z",true,true) };
            let digest = definition::check_definitions(&[("d",&std::fs::read(dir.join("d.json")).unwrap())])
                .unwrap().vocabularies["Reservations"].digest.clone();
            let ty = if rational {"Q"} else {"Z"};
            let law = format!("law \"archsig.law/2\" semantics \"archsig/0.6.0\"; reading Reservations {{ use vocabulary Reservations version \"1\" digest \"{digest}\"; change choose(s:State,n:{ty})=s with{{free=n}}; law required symbolic(z:{ty},s:State,w:{ty}):{predicate}; }}");
            std::fs::write(dir.join("l.law"),law).unwrap();
            let asks = ["m=map(Reservations.Migration,on=@v/m,reading=Reservations)",
                "l=localize($m.candidate.source,using=Reservations.choose)",
                "d=diagnose($l.system,side=equation,degree=0)",
                "e=diagnose($l.system,side=semantic,degree=0)"];
            if predicate == "z=z" {
                let mut args = vec!["run","--atom-definition","d.json","--archmap","a.json","--law","l.law"];
                for ask in asks {args.extend(["--ask",ask]);}
                let normal = run(&dir,&args);
                assert_eq!(normal.code,0,"{} {}",normal.stdout,normal.stderr);
                assert!(normal.stderr.is_empty());
                assert_eq!(s(get(&normal.receipt,"format")),"archsig.summary/1");
                assert!(!has(&normal.receipt,"nodes"));
                assert_eq!(std::fs::read_dir(&dir).unwrap().count(),3);
                eprintln!("universal-affine rational={rational} stdout={} bytes",normal.stdout.len());
            }
            let r = execute(&dir,"out",&asks);
            assert_eq!(r.code,0,"{rational}/{predicate}: {} {}",r.stdout,r.stderr);
            let j = result_json(&dir,&r);
            for i in [2,3] {
                let space = get(output(&j,i,"space"),"value");
                assert_eq!(num(get(get(node(&j,get(space,"module")),"value"),"free_rank")),rank);
            }
            let system = get(output(&j,1,"system"),"value");
            for (side,key) in [("equation_states","solutions"),("semantic_states","parameters")] {
                let states = arr(get(system,side));
                assert!(!states.is_empty());
                assert_eq!(states.iter().any(|state| {
                    let value = get(node(&j,get(state,key)),"value");
                    s(get(get(value,"representation"),"kind")) == "empty"
                }),empty);
            }
            let qs = arr(get(get(&arr(get(&j,"answers"))[1],"scope"),"quantifiers"));
            for name in ["z","w"] { assert!(qs.iter().any(|q|s(get(q,"name"))==name && s(get(q,"kind"))=="forall" && !has(q,"domain"))); }
            let mut args = vec!["run","--atom-definition","d.json","--archmap","a.json","--law","l.law","--out","again","--reuse","out"];
            for ask in asks {args.extend(["--ask",ask]);}
            let reused = run(&dir,&args);
            assert_eq!(reused.code,0,"{} {}",reused.stdout,reused.stderr);
            let again = result_json(&dir,&reused);
            for field in ["answers","nodes"] {assert_eq!(get(&j,field).value,get(&again,field).value);}
        }
    }
}

#[test]
fn universal_local_laws_preserve_solutions_quantifiers_and_reuse() {
    for rational in [false, true] {
        for (predicate, count, rank) in [
            ("z=z", 4, 2),
            ("s.free+z=z+2", 1, 0),
            ("z=s.free", 0, 2),
            ("z+w=w+z and s.free+z=z+2", 1, 0),
            ("z=w", 0, 2),
            ("(let a=z in a=z)", 4, 2),
        ] {
            let dir = if rational { rational_compare_input("universal-local-q", true) }
                else { diagnostic_compare_input("universal-local-z", true, true) };
            let digest = definition::check_definitions(&[("d", &std::fs::read(dir.join("d.json")).unwrap())])
                .unwrap().vocabularies["Reservations"].digest.clone();
            let ty = if rational { "Q" } else { "Z" };
            // 数値parameterが束縛済みStateの前後にある場合も元binderを保つ。
            let law = format!("law \"archsig.law/2\" semantics \"archsig/0.6.0\"; reading Reservations {{ use vocabulary Reservations version \"1\" digest \"{digest}\"; change choose(s:State,b:Bool)=s with{{free=if b then 2 else 3}}; law required symbolic(z:{ty},s:State,w:{ty}):{predicate}; }}");
            std::fs::write(dir.join("l.law"), law).unwrap();
            let asks = ["m=map(Reservations.Migration,on=@v/m,reading=Reservations)",
                "l=localize($m.candidate.source,using=Reservations.choose)",
                "d=diagnose($l.system,side=equation,degree=0)",
                "e=diagnose($l.system,side=semantic,degree=0)"];
            let mut args = vec!["run", "--atom-definition", "d.json", "--archmap", "a.json", "--law", "l.law"];
            for ask in asks { args.extend(["--ask", ask]); }
            let files = || std::fs::read_dir(&dir).unwrap().map(|p| p.unwrap().file_name()).collect::<std::collections::BTreeSet<_>>();
            let before = files();
            let normal = run(&dir, &args);
            assert_eq!(normal.code, 0, "{rational}/{predicate}: {} {}", normal.stdout, normal.stderr);
            assert!(normal.stderr.is_empty());
            assert_eq!(files(), before);
            let summary = archsig::json::parse(normal.stdout.as_bytes()).unwrap();
            assert_eq!(s(get(&summary, "format")), "archsig.summary/1");
            assert!(!has(&summary, "nodes"));
            let saved = execute(&dir, "out", &asks);
            assert_eq!(saved.code, 0, "{} {}", saved.stdout, saved.stderr);
            let j = result_json(&dir, &saved);
            let diagnostic = get(output(&j, 3, "diagnostic"), "value");
            let restriction = get(node(&j, get(diagnostic, "restriction")), "value");
            let domain = get(node(&j, get(restriction, "source")), "value");
            assert_eq!(arr(get(domain, "elements")).len(), count, "{rational}/{predicate}");
            let space = get(output(&j, 2, "space"), "value");
            let module = get(node(&j, get(space, "module")), "value");
            assert_eq!(num(get(module, "free_rank")), rank, "{rational}/{predicate}");
            // 空のアフィン解と、その斉次方向の階数は別の結果。
            let system = get(output(&j, 1, "system"), "value");
            let equations = arr(get(system,"equation_states"));
            assert!(!equations.is_empty());
            let has_empty = equations.iter().any(|e| {
                let solution = get(node(&j,get(e,"solutions")),"value");
                s(get(get(solution,"representation"),"kind")) == "empty"
            });
            assert_eq!(has_empty, count == 0, "{rational}/{predicate}");
            let quantifiers = arr(get(get(&arr(get(&j,"answers"))[1],"scope"),"quantifiers"));
            for name in ["z", "w"] {
                let qs = quantifiers.iter().filter(|q| s(get(q,"name")) == name).collect::<Vec<_>>();
                assert!(!qs.is_empty());
                for q in qs { assert_eq!(s(get(q,"kind")),"forall"); assert!(!has(q,"domain")); }
            }
            args.extend(["--out", "again", "--reuse", "out"]);
            let reused = run(&dir, &args);
            assert_eq!(reused.code, 0, "{} {}", reused.stdout, reused.stderr);
            let again = result_json(&dir, &reused);
            for field in ["answers", "nodes"] { assert_eq!(get(&j,field).value, get(&again,field).value); }
        }
    }
}
