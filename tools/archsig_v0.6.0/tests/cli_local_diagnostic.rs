//! 固定対象の局所化と有限診断。Law成立と貼り合わせを区別する実CLI試験。
use crate::common::cli;
use archsig::{definition, json::JNode};
use cli::*;
use crate::common;
const D: &str = r#"{"format":"archsig.atom-definition/1","semantics":"archsig/0.6.0","vocabularies":[{"semantics":"archsig/0.6.0","namespace":"Fixed","version":"1","dependencies":[],"declarations":[{"kind":"entity","name":"Fixed.State","meaning":"固定状態。","parameters":[],"fields":[{"name":"flag","type":"Bool","meaning":"観測値。"}],"alignments":[]}]}]}"#;
fn input(name: &str, value: Option<bool>) -> std::path::PathBuf {
    let definitions = definition::check_definitions(&[("d", D.as_bytes())]).unwrap();
    let digest = &definitions.vocabularies()["Fixed"].digest;
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
        let mut asks = vec![
            "a=build(Fixed,on=@fixed/s)",
            "l=localize($a.object,law=Fixed.valid,s=@fixed/s)",
            "e=diagnose($l.system)",
            "s=diagnose($l.system,side=semantic)",
            "z=diagnose($l.system,degree=0)",
            "v=evaluate(Fixed.current,on=$l.system.base,s=@fixed/s)",
            "equationBase=evaluate(Fixed.current,on=$e.diagnostic.global.domain.base,s=@fixed/s)",
            "semanticBase=evaluate(Fixed.current,on=$s.diagnostic.global.domain.base,s=@fixed/s)",
        ];
        if value {
            // 局所系の根と診断の局所系を、後続の問いへ答えとして渡せる。
            asks.extend([
                "root=localize($a.object,law=Fixed.valid,s=$a.object.root)",
                "again=diagnose($e.diagnostic.system,degree=0)",
            ]);
        }
        let r = execute(&dir, "out", &asks);
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
        if value {
            for index in [8, 9] {
                assert_eq!(s(get(&arr(get(&json, "answers"))[index], "status")), "established");
            }
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
    // 数値parameterは域を列挙せず、全称のまま解の有無が述語の真偽に一致する。束縛すれば1解。
    let dir=diagnostic_compare_input("universal-fixed-z",true,true);
    let digest=definition::check_definitions(&[("d",&std::fs::read(dir.join("d.json")).unwrap())]).unwrap().vocabularies()["Reservations"].digest.clone();
    let law=format!("law \"archsig.law/2\" semantics \"archsig/0.6.0\"; reading Reservations {{ use vocabulary Reservations version \"1\" digest \"{digest}\"; view two():Z=2; law required valid(z:Z,s:State,w:Z):z=w; }}");
    std::fs::write(dir.join("l.law"),law).unwrap();
    let asks=["a=map(Reservations.Migration,on=@v/m,reading=Reservations)","l=localize($a.candidate.source)","e=diagnose($l.system,degree=0)","s=diagnose($l.system,side=semantic,degree=0)"];
    let r=execute(&dir,"out",&asks);
    assert_eq!(r.code,0,"{} {}",r.stdout,r.stderr);
    let j=result_json(&dir,&r);
    let system=get(output(&j,1,"system"),"value");
    for (states,solutions) in [("equation_states","solutions"),("semantic_states","parameters")] {
        let state=&arr(get(system,states))[0];
        let values=get(node(&j,get(state,solutions)),"value");
        assert!(arr(get(get(values,"representation"),"values")).is_empty());
    }
    let scope=get(&arr(get(&j,"answers"))[1],"scope");
    for name in ["z","w"] {
        assert!(arr(get(scope,"quantifiers")).iter().any(|q|s(get(q,"name"))==name && !has(q,"domain")));
    }
    let bound=execute(&dir,"bound",&[asks[0],"n=evaluate(Reservations.two,on=$a.candidate.source)","l=localize($a.candidate.source,law=Reservations.valid,z=$n.value,w=$n.value)","d=diagnose($l.system,degree=0)"]);
    assert_eq!(bound.code,0,"{}",bound.stdout);
    let j=result_json(&dir,&bound);
    let system=get(output(&j,2,"system"),"value");
    for (states,key) in [("equation_states","solutions"),("semantic_states","parameters")] {
        let state=&arr(get(system,states))[0];let solution=get(node(&j,get(state,key)),"value");
        assert_eq!(arr(get(get(solution,"representation"),"values")).len(),1);
    }
}
#[test]
fn localize_budget_and_signal_stop_keep_the_prior_architecture() {
    use archsig::{
        control::{Checkpoint, Control, Limits, Usage},
        input::InputSources,
        observed::evaluate::evaluate_observed_bytes,
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
fn localize_checks_answer_bound_owners_before_using_the_values() {
    let root = common::entity_json("W.Root", "[]", "[]");
    let owner = common::field_json("owner", r#"["Ref","W.Root"]"#);
    let item = common::entity_json("W.Item", &format!("[{owner}]"), "[]");
    let definition = common::definition_json(&format!(
        "[{}]",
        common::vocabulary_json("W", &format!("[{root},{item}]"), "[]")
    ));
    let definitions = common::definitions_ok(&[&definition]);
    let digest = &definitions.vocabularies()["W"].digest;
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
    // 観測ありの真偽はboolean_law_formsが確かめる。ここでは短絡が欠測を消さないことだけを見る。
    for (index, expression) in ["(s.flag and false)=false", "(s.flag or true)=true"]
        .iter()
        .enumerate()
    {
        let dir = input(&format!("local-short-{index}"), None);
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
        assert_eq!(r.code, 2, "{} {}", r.stdout, r.stderr);
        let result = result_json(&dir, &r);
        let answers = arr(get(&result, "answers"));
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
    // 式ごとに代表の観測値を1つ選ぶ(欠測はs.flagで見る)。
    for (index, body, value) in [
        (0, "s.flag", None),
        (1, "not s.flag", Some(false)),
        (2, "s.flag and true", Some(false)),
    ] {
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
        ("true", "s.flag", Some(false), "refuted"),
        ("false", "s.flag", Some(false), "established"),
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
    }
}

#[test]
fn required_laws_on_the_same_support_are_all_retained_and_checked() {
    // 一つでも偽なら両側で反証する行と、欠測の行。省略時はoptional Lawを選ばない。
    for (second, value, truth) in [
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
                    "law required also(t:State):{}; law optional ignored(s:State):not s.flag; view current",
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
            }
        } else {
            assert_eq!(s(get(&answers[1], "status")), "undetermined");
            assert!(!has(get(&answers[1], "outputs"), "system"));
            let reasons = arr(get(&answers[1], "reasons"));
            assert_eq!(reasons.len(), 1);
            assert_eq!(s(get(&reasons[0], "code")), "missing_observation");
            let missing = arr(get(&reasons[0], "missing"));
            assert_eq!(missing.len(), 1);
            assert_eq!(s(get(&missing[0], "field")), "Fixed.State.flag");
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
fn finite_law_parameters_are_universal_and_keep_each_binding() {
    // 欠測の扱いはrequired_laws_on_the_same_supportが確かめる。偽の観測で両instanceと反証を見る。
    let dir = input("local-finite-instances", Some(false));
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
        ],
    );
    assert_eq!(r.code, 1, "{} {}", r.stdout, r.stderr);
    let result = result_json(&dir, &r);
    let answers = arr(get(&result, "answers"));
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
        assert_eq!(s(get(&answers[index], "status")), "refuted");
    }
    let scope = get(&answers[1], "scope");
    let quantifiers = arr(get(scope, "quantifiers"));
    let p = quantifiers
        .iter()
        .find(|q| s(get(q, "name")) == "p")
        .unwrap();
    let domain = get(node(&result, get(p, "domain")), "value");
    assert_eq!(arr(get(domain, "elements")).len(), 2);
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
fn explicit_local_guard_missing_is_an_observation_requirement_and_true_guard_holds() {
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
    let digest = &definitions.vocabularies()["Fixed"].digest;
    let dir = input(name, Some(left));
    std::fs::write(dir.join("d.json"), &definition).unwrap();
    let old = definition::check_definitions(&[("d", D.as_bytes())]).unwrap();
    let old_digest = &old.vocabularies()["Fixed"].digest;
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
    for (left, right) in [(true, true), (true, false)] {
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
    for (reads, left, right) in [
        ("(t.flag,t.other)", true, false),
        ("((t.flag,unit),(t,t.other))", false, true),
    ] {
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
        let system = get(output(&j, 1, "system"), "value");
        let context = get(node(&j, &arr(get(system, "contexts"))[0]), "value");
        let readings = arr(get(context, "readings"));
        assert_eq!(readings.len(), 1);
        assert_eq!(s(&arr(get(&readings[0], "type"))[0]), "Tuple");
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
#[test]
fn product_read_does_not_publish_a_references_fields_or_fill_a_missing_component() {
    // 未観測成分のrequirementはmultiple_read_local_keeps_hidden_and_unobserved_fields_distinctと同じ。
    let dir = multiple_read_input("local-product-needed", true, Some(true), "(t.flag,t)");
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
    assert!(arr(get(plan, "requirements")).is_empty());
    assert!(arr(get(answer, "reasons"))
        .iter()
        .any(|r| s(get(r, "code")) == "visibility_insufficient"));
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
fn finite_diagnostics_compare_actual_identity_maps_on_both_sides() {
    // 成立の行と反証の行を一つずつ。sideとdegreeは比較の論理を分けない。
    for (valid, side, degree) in [(true, "semantic", 0), (false, "equation", 1)] {
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
    }
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
    for (left, right) in [(true, true), (false, true)] {
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
        let cover = get(node(&j, get(system, "cover")), "value");
        let patches = arr(get(cover, "patches"));
        assert_eq!(patches.len(), 2);
        assert!(patches.iter().all(|p| p.value != get(cover, "base").value));
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
fn explicit_distinct_local_declarations_form_the_selected_cover() {
    let dir = implicit_multiple_input("explicit-distinct-cover", true, Some(false));
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
    assert_eq!(r.code, 1, "{} {}", r.stdout, r.stderr);
    let j = result_json(&dir, &r);
    let system = get(output(&j, 1, "system"), "value");
    assert_eq!(arr(get(system, "contexts")).len(), 4);
    let cover = get(node(&j, get(system, "cover")), "value");
    assert_eq!(arr(get(cover, "patches")).len(), 2);
    for patch in arr(get(cover, "patches")) {
        assert_ne!(patch.value, get(cover, "base").value);
        let context = get(node(&j, patch), "value");
        assert_eq!(arr(get(context, "locals")).len(), 1);
    }
    for i in [2, 3] {
        assert_eq!(s(get(&arr(get(&j, "answers"))[i], "status")), "refuted");
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
    let dir = implicit_multiple_input("tuple-intersection", false, Some(true));
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
            .replace(&old.vocabularies()["Fixed"].digest, &new.vocabularies()["Fixed"].digest)
            .replace("law required second(s:State):s.other=true;", "")
            .replace(r#""atoms":["#, r#""atoms":[{"id":"third","subject":"s","field":"Fixed.State.third","value":true,"origin":"model"},"#);
        std::fs::write(dir.join(file), text).unwrap();
    }
    explicit_local(
        &dir,
        "local left(t:State) reads ((t.flag,t.other),unit); local right(t:State) reads ((t.flag,t.third),unit);",
    );
    let asks = [
        "a=build(Fixed,on=@fixed/s)",
        "l=localize($a.object)",
        "e=diagnose($l.system)",
        "s=diagnose($l.system,side=semantic)",
    ];
    let r = execute(&dir, "out", &asks);
    assert_eq!(r.code, 1, "{} {}", r.stdout, r.stderr);
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
    assert_eq!(readings.len(), 2);
    let reading = readings
        .iter()
        .find(
            |v| matches!(&get(v,"type").value, archsig::json::JValue::Str(t) if t=="Bool"),
        )
        .unwrap();
    let image = get(node(&j, get(reading, "domain")), "value");
    assert_eq!(arr(get(image, "elements")).len(), 1);
    assert_eq!(
        get(node(&j, &arr(get(image, "elements"))[0]), "value").value,
        archsig::json::JValue::Bool(false)
    );
    for i in [2, 3] {
        assert_eq!(s(get(&arr(get(&j, "answers"))[i], "status")), "refuted");
    }
}

#[test]
fn finite_change_local_states_distinguish_the_action_image_from_free_equations() {
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
    // 欠測だけの行と、未対応の理由が併発する行。
    for failure in 0..2 {
    let dir = multiple_read_input("finite-explicit-missing", true, None, "t.flag,t.other");
    let path=dir.join("l.law");
    let law=std::fs::read_to_string(&path).unwrap().replace("law required second(s:State):s.other=true;", "");
    std::fs::write(path,law).unwrap();
    explicit_local(&dir,"change choose(t:State,b:Bool)=t with {flag=b};");
    if failure == 1 { explicit_local(&dir,"local zzz(t:State) when t.flag reads t.flag;"); }
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
    // 仕様の三辺の例(検証仕様 §3)。γ=3で類は±1、方程式側の解は空、診断は反証。
    // γ=2の全解と、反証証拠の内部検査は実行時間のため外した。semantic側の三辺は
    // integer_local_equation_fibers_do_not_expand_the_allowed_even_translation_image、
    // degree=0の診断は integer_local_empty_cover_has_zero_cohomology が見る。
    let input = triangle::input(Some(3));
    let dir = workdir("integer-local-cech");
    for (name,bytes) in [("d.json",input.definitions()[0].bytes()),("l.law",input.law().bytes()),("a.json",input.archmap().bytes())] {
        let mut text=String::from_utf8(bytes.to_vec()).unwrap();
        if name=="l.law" {text=text.replace("change move(","view rank(n:Z):Z=n; change move(");}
        std::fs::write(dir.join(name),text).unwrap();
    }
    let asks = ["a=build(Coordinates,on=@triangle/root)","l=localize($a.object,using=Coordinates.move)",
        "d=diagnose($l.system)","n=needed($d)","rank=evaluate(Coordinates.rank,on=$a.object,n=$d.space.module.free_rank)","owner=evaluate(Coordinates.rank,on=$a.object,n=$d.class.coordinates.module.free_rank)"];
    let r = execute(&dir,"out",&asks);
    assert_eq!(r.code,1,"{} {}",r.stdout,r.stderr);
    let j = result_json(&dir,&r);
    assert_eq!(s(get(&arr(get(&j,"answers"))[1],"status")),"established","{:?}",get(&j,"answers"));
    let answer = &arr(get(&j,"answers"))[2];
    assert_eq!(s(get(answer,"status")),"refuted");
    let diagnostic = get(output(&j,2,"diagnostic"),"value");
    assert_eq!(s(get(diagnostic,"kind")),"affine_cech");
    let space = get(output(&j,2,"space"),"value");
    let group = get(node(&j,get(space,"module")),"value");
    assert_eq!(num(get(group,"free_rank")),1);
    assert!(arr(get(group,"torsion")).is_empty());
    let class = get(output(&j,2,"class"),"value");
    let coordinate_vector = get(node(&j,get(class,"coordinates")),"value");
    let values = arr(get(coordinate_vector,"coordinates")).iter().map(|r|s(get(node(&j,r),"value")).parse::<i64>().unwrap()).collect::<Vec<_>>();
    assert_eq!(values.len(),1);
    assert_eq!(values[0].abs(),1);
    let complex=get(node(&j,get(diagnostic,"complex")),"value");
    assert_eq!(s(get(complex,"convention")),"ordered");
    let maps=arr(get(complex,"differentials"));
    let d0=columns(&j,&maps[0]); let d1=columns(&j,&maps[1]);
    let modules=arr(get(complex,"modules"));
    let last_rank=num(get(get(node(&j,&modules[2]),"value"),"free_rank")) as usize;
    for column in &d0 { assert!(apply(&d1,column,last_rank).iter().all(|x|*x==0)); }
    let representative=vector(&j,get(class,"representative"));
    assert!(apply(&d1,&representative,last_rank).iter().all(|x|*x==0));
    let system=get(output(&j,1,"system"),"value");
    let global=&arr(get(system,"equation_states"))[0];
    let space=get(node(&j,get(global,"space")),"value");
    assert_eq!(arr(get(space,"variables")).len(),3);
    let solution=get(node(&j,get(global,"solutions")),"value");
    let rep=get(solution,"representation");
    assert_eq!(s(get(rep,"kind")),"empty");
    for state in arr(get(system,"equation_states")) {
        let space=get(node(&j,get(state,"space")),"value");
        assert!(arr(get(space,"variables")).iter().all(|v|s(get(get(get(v,"position"),"field"),"field"))=="Coordinates.Point.coordinate"));
    }
    assert_eq!(s(get(output(&j,4,"value"),"value")),"1");
    assert_eq!(s(get(output(&j,5,"value"),"value")),"1");
    let invalid=execute(&dir,"invalid",&["a=build(Coordinates,on=@triangle/root)","l=localize($a.object,using=Coordinates.move)","d=diagnose($l.system)","bad=evaluate(Coordinates.rank,on=$a.object,n=$d.class.coordinates[0])"]);
    assert_eq!(invalid.code,64,"{} {}",invalid.stdout,invalid.stderr);
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
    // equation側の三辺の類は integer_translation_local_system_generates_cech_group_and_actual_obstruction が見る。
    let r=execute(&dir,"out",&["a=build(Coordinates,on=@triangle/root)","l=localize($a.object,using=Coordinates.move)","s=diagnose($l.system,side=semantic)","n=needed($s)"]);
    assert_eq!(r.code,2,"{} {}",r.stdout,r.stderr);
    let j=result_json(&dir,&r);
    let semantic=&arr(get(&j,"answers"))[2];assert_eq!(s(get(semantic,"status")),"undetermined");assert!(!has(get(semantic,"outputs"),"class"));assert!(!has(semantic,"claim"));
    assert_eq!(s(get(&arr(get(&j,"answers"))[3],"status")),"established");
    assert!(has(get(&arr(get(&j,"answers"))[3],"outputs"),"plan"));
    let diagnostic=get(output(&j,2,"diagnostic"),"value");
    assert!(arr(get(diagnostic,"conditions")).iter().any(|r|s(get(get(node(&j,r),"judgment"),"status"))=="refuted"));
    let system=get(output(&j,1,"system"),"value");
    let global=&arr(get(system,"semantic_states"))[0];
    let solutions=get(node(&j,get(global,"parameters")),"value");assert_eq!(s(get(get(solutions,"representation"),"kind")),"empty");
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
    let checked=definition::check_definitions(&[("d",definitions.as_bytes())]).unwrap();let digest=&checked.vocabularies()["Pair"].digest;
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
    use archsig::{
        control::{Checkpoint, Control, Limits, Usage},
        input::InputSources,
        observed::evaluate::evaluate_observed_bytes,
    };
    use std::{cell::Cell, rc::Rc};
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
    let checked=definition::check_definitions(&[("d",definitions.as_bytes())]).unwrap();let digest=&checked.vocabularies()["Pair"].digest;
    for mode in ["sum-only","free","offset-missing"] {
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
        if mode=="offset-missing" {assert!(matches!(r.code,0|2),"{mode}: {} {}",r.stdout,r.stderr);}
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
fn integer_local_actions_keep_parameter_kernel_stabilizer_and_effective_image_distinct() {
    let definitions=r#"{"format":"archsig.atom-definition/1","semantics":"archsig/0.6.0","vocabularies":[{"semantics":"archsig/0.6.0","namespace":"Motion","version":"1","dependencies":[],"declarations":[{"kind":"entity","name":"Motion.State","meaning":"整数状態。","parameters":[],"fields":[{"name":"x","type":"Z","meaning":"位置。"},{"name":"goal","type":"Z","meaning":"要求位置。"}],"alignments":[]}]}]}"#;
    let checked=definition::check_definitions(&[("d",definitions.as_bytes())]).unwrap();
    let digest=&checked.vocabularies()["Motion"].digest;
    let law=format!("law \"archsig.law/2\" semantics \"archsig/0.6.0\"; reading Motion {{ use vocabulary Motion version \"1\" digest \"{digest}\"; law required reachesGoal(s:State):s.x=s.goal; local Read(s:State) reads (s.x,s.goal); change move(s:State,a:Z,b:Z)=s with{{x=2*a+2*b}}; }}");
    for (goal, guarded) in [(Some(2),false),(Some(2),true)] {
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
    // 像の作用が違う(move対even)と、rankが同じでも状態の対応がない。
    let dir=integer_transport_input("integer-transport-mismatch",false);
    let path=dir.join("l.law");let law=std::fs::read_to_string(&path).unwrap();
    std::fs::write(&path,law.replace("law optional localValid", "change even(s:State,d:Z)=s with{free=s.free+2*d}; law optional localValid")).unwrap();
    let r=execute(&dir,"out",&["m=map(Reservations.Migration,on=@v/m,reading=Reservations)",
        "l=localize($m.candidate.source,law=Reservations.localValid,s=@v/p,using=Reservations.move)",
        "r=localize($m.candidate.target,law=Reservations.localValid,s=@v/r,using=Reservations.even)",
        "d=diagnose($l.system,side=semantic,degree=0)","e=diagnose($r.system,side=semantic,degree=0)",
        "c=compare($d.diagnostic,to=$e.diagnostic,kind=diagnostics,along=$m.operation)","n=needed($c)"]);
    assert_eq!(r.code,2,"{} {}",r.stdout,r.stderr);let j=result_json(&dir,&r);
    for i in [3,4] {let space=get(output(&j,i,"space"),"value");assert_eq!(num(get(get(node(&j,get(space,"module")),"value"),"free_rank")),1);}
    let answer=&arr(get(&j,"answers"))[5];assert_eq!(s(get(answer,"status")),"undetermined");
    assert!(!has(get(answer,"outputs"),"comparison"));
    assert!(arr(get(answer,"reasons")).iter().any(|r|s(get(r,"code"))=="unsupported_algorithm"));
    assert_eq!(s(get(&arr(get(&j,"answers"))[6],"status")),"established");
}

#[test]
fn integer_diagnostic_inclusion_computes_torsion_cokernel_and_keeps_the_map() {
    // 包含のcokernelがZ/2のtorsionになる行。degree 1の類の移送はnonzero_classesが確かめる。
    let dir=integer_transport_input("integer-inclusion",true);
    let path=dir.join("l.law");let law=std::fs::read_to_string(&path).unwrap();
    std::fs::write(&path,law.replace("law optional localValid","change stride(s:State,d:Z)=s with{free=s.free+2*d}; law optional localValid")).unwrap();
    let asks=["m=map(Reservations.Migration,on=@v/m,reading=Reservations)",
        "l=localize($m.candidate.source,law=Reservations.localValid,s=@v/p,using=Reservations.stride)",
        "r=localize($m.candidate.target,law=Reservations.localValid,s=@v/transport_z,using=Reservations.move)",
        "d=diagnose($l.system,side=semantic,degree=0)","e=diagnose($r.system,side=semantic,degree=0)",
        "c=compare($d.diagnostic,to=$e.diagnostic,kind=diagnostics,along=$m.operation)",
        "q=evaluate(Reservations.rank,on=$m.candidate.source,n=$c.comparison.cokernel.free_rank)"];
    let r=execute(&dir,"out",&asks);assert_eq!(r.code,1,"{} {}",r.stdout,r.stderr);
    let j=result_json(&dir,&r);let cmp=get(output(&j,5,"comparison"),"value");
    assert_eq!(s(get(&arr(get(&j,"answers"))[5],"status")),"refuted");
    let group=arr(get(cmp,"conditions")).iter().map(|r|node(&j,r)).find(|n| {
        let v=get(n,"value");
        s(get(v,"predicate"))=="equal" && matches!(&get(node(&j,&arr(get(v,"operands"))[0]),"value").value,archsig::json::JValue::Str(_))
    }).expect("整数値の等値として群の零条件を保持する");
    let operands=arr(get(get(group,"value"),"operands"));assert_eq!(operands.len(),2);
    assert_eq!(s(get(node(&j,&operands[0]),"value")),"1");
    assert_eq!(s(get(node(&j,&operands[1]),"value")),"0");
    assert_eq!(s(get(get(group,"judgment"),"status")),"refuted");
    let kernel=get(node(&j,get(cmp,"kernel")),"value");let cokernel=get(node(&j,get(cmp,"cokernel")),"value");
    assert_eq!(num(get(kernel,"free_rank")),0);assert!(arr(get(kernel,"torsion")).is_empty());
    assert_eq!(num(get(cokernel,"free_rank")),0);
    let torsion=arr(get(cokernel,"torsion")).iter().map(s).collect::<Vec<_>>();
    assert_eq!(torsion,["2"]);
    let hm=get(node(&j,get(cmp,"cohomology_map")),"value");
    let columns=arr(get(hm,"columns"));assert_eq!(columns.len(),1);
    let coefficient=s(get(node(&j,&arr(&columns[0])[0]),"value")).parse::<i64>().unwrap();assert_eq!(coefficient.abs(),2);
    let relations=arr(get(cokernel,"relations"));assert_eq!(relations.len(),1);
    assert_eq!(s(get(node(&j,&arr(&relations[0])[0]),"value")),"2");
    assert_eq!(s(get(output(&j,6,"value"),"value")),"0");
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
    let digest = &checked.vocabularies()["Reservations"].digest;
    let old_digest = definition::check_definitions(&[("d", old.as_bytes())])
        .unwrap()
        .vocabularies()["Reservations"]
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
fn finite_localization_without_required_laws_keeps_equation_and_action_states_distinct() {
    // 同じ局所系の方程式側は自由な4状態、constant変更の意味側は実際の1状態。
    let dir = finite_diagnostic_input("empty-local-laws", false);
    let path = dir.join("l.law");
    let law = std::fs::read_to_string(&path).unwrap();
    std::fs::write(&path, law.replace("law optional localValid",
        "change constant(s:State,b:Bool)=s with{free=true}; law optional localValid")).unwrap();
    let asks = ["m=map(Reservations.Migration,on=@v/m,reading=Reservations)",
        "l=localize($m.candidate.source,using=Reservations.constant)",
        "d=diagnose($l.system,side=equation,degree=0)",
        "e=diagnose($l.system,side=semantic,degree=0)"];
    let result = execute(&dir, "out", &asks);
    assert_eq!(result.code, 0, "{} {}", result.stdout, result.stderr);
    let j = result_json(&dir, &result);
    for answer in arr(get(&j, "answers")) { assert_eq!(s(get(answer, "status")), "established"); }
    for (index, expected) in [
        (2, vec![vec![false,false],vec![false,true],vec![true,false],vec![true,true]]),
        (3, vec![vec![true,true]]),
    ] {
        let diagnostic = get(output(&j, index, "diagnostic"), "value");
        let restriction = get(node(&j, get(diagnostic, "restriction")), "value");
        let global = get(node(&j, get(restriction, "source")), "value");
        let elements = arr(get(global, "elements"));
        let states = elements.iter().map(|r| arr(get(node(&j, r), "value")).iter().map(|v| {
            match v.value { archsig::json::JValue::Bool(value) => value, _ => panic!("Bool状態") }
        }).collect::<Vec<_>>()).collect::<Vec<_>>();
        assert_eq!(states, expected);
        let matching = get(node(&j, get(diagnostic, "matching")), "value");
        assert_eq!(arr(get(matching, "elements")).len(), states.len());
    }
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
    }
}

#[test]
fn fixed_localization_without_laws_keeps_one_state_and_compares() {
    let dir = finite_diagnostic_input("empty-fixed", false);
    let asks=["m=map(Reservations.Migration,on=@v/m,reading=Reservations)",
        "l=localize($m.candidate.source)","r=localize($m.candidate.source)",
        "d=diagnose($l.system,side=equation,degree=0)","e=diagnose($r.system,side=equation,degree=0)",
        "c=compare($d.diagnostic,to=$e.diagnostic,kind=diagnostics,along=$m.operation)","n=needed($c)"];
    let result=execute(&dir,"out",&asks);assert_eq!(result.code,0,"{} {}",result.stdout,result.stderr);
    let j=result_json(&dir,&result);
    for answer in arr(get(&j,"answers")) {assert_eq!(s(get(answer,"status")),"established");}
    let diagnostic=get(output(&j,3,"diagnostic"),"value");
    let matching=get(node(&j,get(diagnostic,"matching")),"value");assert_eq!(arr(get(matching,"elements")).len(),1);
    let restriction=get(node(&j,get(diagnostic,"restriction")),"value");assert_eq!(arr(get(restriction,"pairs")).len(),1);
    let cmp=get(output(&j,5,"comparison"),"value");let map=get(node(&j,get(cmp,"finite_map")),"value");
    assert_eq!(arr(get(map,"pairs")).len(),1);
    for condition in arr(get(cmp,"conditions")) {assert_eq!(s(get(get(node(&j,condition),"judgment"),"status")),"established");}
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
    for i in [5,6] {
        assert_eq!(s(get(&answers[i],"status")),"undetermined");
        assert!(arr(get(&answers[i],"reasons")).iter().any(|r|s(get(r,"code"))=="unsupported_algorithm"));
    }
}

#[test]
fn integer_diagnostic_transport_rejects_a_different_compound_binding() {
    // 複合束縛値(State入りtuple)の値が対応しなければ、比較は写像を発明せずunsupported。
    let dir=integer_transport_input("integer-compound-mismatch",true);
    let path=dir.join("l.law");let law=std::fs::read_to_string(&path).unwrap();
    std::fs::write(&path,law.replace("law optional localValid",
        "view packed(s:State):(State,Z)=(s,2); view other(s:State):(State,Z)=(s,3); law optional packedLaw(s:State,b:(State,Z)):s.free=b.1; law optional localValid")).unwrap();
    let r=execute(&dir,"out",&["m=map(Reservations.Migration,on=@v/m,reading=Reservations)",
        "x=evaluate(Reservations.packed,on=$m.candidate.source,s=@v/p)",
        "y=evaluate(Reservations.other,on=$m.candidate.target,s=@v/transport_z)",
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

#[test]
fn integer_local_laws_read_fields_through_bound_tuple_references() {
    // 束縛したtuple値の中の参照(b.0)を通してfieldを読むLawを、両端で局所化して比較する。
    let dir=integer_transport_input("integer-projected-reference",true);
    let path=dir.join("l.law");let law=std::fs::read_to_string(&path).unwrap();
    std::fs::write(path,law.replace("law optional localValid",
        "view packed(s:State):(State,Z)=(s,2); law optional packedLaw(b:(State,Z)):b.0.free=b.1; law optional localValid")).unwrap();
    let asks=["m=map(Reservations.Migration,on=@v/m,reading=Reservations)",
        "x=evaluate(Reservations.packed,on=$m.candidate.source,s=@v/p)",
        "y=evaluate(Reservations.packed,on=$m.candidate.target,s=@v/transport_z)",
        "l=localize($m.candidate.source,law=Reservations.packedLaw,b=$x.value,using=Reservations.move)",
        "r=localize($m.candidate.target,law=Reservations.packedLaw,b=$y.value,using=Reservations.move)",
        "d=diagnose($l.system,side=equation,degree=0)","e=diagnose($r.system,side=equation,degree=0)",
        "c=compare($d.diagnostic,to=$e.diagnostic,kind=diagnostics,along=$m.operation)"];
    let r=execute(&dir,"out",&asks);assert_eq!(r.code,0,"{} {}",r.stdout,r.stderr);let j=result_json(&dir,&r);
    for i in [5,6] {
        let space=get(output(&j,i,"space"),"value");let group=get(node(&j,get(space,"module")),"value");
        assert_eq!(num(get(group,"free_rank")),1);assert!(arr(get(group,"torsion")).is_empty());
    }
    let cmp=get(output(&j,7,"comparison"),"value");assert_eq!(s(get(&arr(get(&j,"answers"))[7],"status")),"established");
    for field in ["kernel","cokernel"] {let group=get(node(&j,get(cmp,field)),"value");assert_eq!(num(get(group,"free_rank")),0);assert!(arr(get(group,"torsion")).is_empty());}
}

#[test]
fn finite_diagnostics_transport_actual_states_between_architectures() {
    let dir=finite_diagnostic_input_at(integer_transport_input("finite-transport",true),true);
    let path=dir.join("l.law");let law=std::fs::read_to_string(&path).unwrap();
    std::fs::write(path,law.replace("law optional localValid","local each(s:State) reads s.free; law optional localValid")).unwrap();
    let asks=["m=map(Reservations.Migration,on=@v/m,reading=Reservations)",
        "l=localize($m.candidate.source,law=Reservations.localValid,s=@v/p,using=Reservations.choose)",
        "r=localize($m.candidate.target,law=Reservations.localValid,s=@v/transport_z,using=Reservations.choose)",
        "d=diagnose($l.system,side=semantic,degree=1)","e=diagnose($r.system,side=semantic,degree=1)",
        "c=compare($d.diagnostic,to=$e.diagnostic,kind=diagnostics,along=$m.operation)","n=needed($c)"];
    let r=execute(&dir,"out",&asks);assert_eq!(r.code,0,"{} {}",r.stdout,r.stderr);let j=result_json(&dir,&r);
    let cmp=get(output(&j,5,"comparison"),"value");assert_eq!(s(get(&arr(get(&j,"answers"))[5],"status")),"established");
    let map=get(node(&j,get(cmp,"finite_map")),"value");node(&j,get(map,"source"));node(&j,get(map,"target"));
    let pairs=arr(get(map,"pairs"));assert_eq!(pairs.len(),2);
    for pair in pairs {let pair=arr(pair);let x=arr(get(node(&j,&pair[0]),"value"));let y=arr(get(node(&j,&pair[1]),"value"));
        assert_eq!(x.len(),2);assert_eq!(y.len(),2);assert_eq!(x[0].value,y[1].value);assert_eq!(x[1].value,y[0].value);}
    for condition in arr(get(cmp,"conditions")){assert_eq!(s(get(get(node(&j,condition),"judgment"),"status")),"established");}
}

#[test]
fn finite_diagnostic_inclusion_keeps_the_map_and_refutes_preservation() {
    // 真の包含(意味側)で保存条件を反証する行。
    let dir=finite_diagnostic_input("finite-diagnostic-inclusion",true);
    let path=dir.join("l.law");let law=std::fs::read_to_string(&path).unwrap();
    std::fs::write(path,law.replace("law optional localValid","change constant(s:State,b:Bool)=s with{free=true}; law optional localValid")).unwrap();
    let asks=["m=map(Reservations.Migration,on=@v/m,reading=Reservations)",
        "l=localize($m.candidate.source,law=Reservations.localValid,s=@v/p,using=Reservations.constant)",
        "r=localize($m.candidate.source,law=Reservations.localValid,s=@v/p,using=Reservations.choose)",
        "d=diagnose($l.system,side=semantic,degree=0)","e=diagnose($r.system,side=semantic,degree=0)",
        "c=compare($d.diagnostic,to=$e.diagnostic,kind=diagnostics,along=$m.operation)","n=needed($c)"];
    let r=execute(&dir,"out",&asks);
    assert_eq!(r.code,1,"{} {}",r.stdout,r.stderr);let j=result_json(&dir,&r);
    assert_eq!(s(get(&arr(get(&j,"answers"))[5],"status")),"refuted");
    let cmp=get(output(&j,5,"comparison"),"value");let map=get(node(&j,get(cmp,"finite_map")),"value");
    assert_eq!(arr(get(get(node(&j,get(map,"source")),"value"),"elements")).len(),1);
    assert_eq!(arr(get(get(node(&j,get(map,"target")),"value"),"elements")).len(),2);
    let pairs=arr(get(map,"pairs"));assert_eq!(pairs.len(),1);
    for pair in pairs {let pair=arr(pair);let x=get(node(&j,&pair[0]),"value");let y=get(node(&j,&pair[1]),"value");assert_eq!(x.value,y.value);
        assert!(arr(x).iter().all(|v|matches!(v.value,archsig::json::JValue::Bool(true))));}
    let conditions=arr(get(cmp,"conditions"));
    assert!(conditions.iter().any(|r|s(get(get(node(&j,r),"judgment"),"status"))=="refuted"));
    assert!(conditions.iter().all(|r|s(get(get(node(&j,r),"value"),"predicate"))!="inverse_maps"));
    assert_eq!(s(get(&arr(get(&j,"answers"))[6],"status")),"established");
}

#[test]
fn finite_diagnostic_identifies_positions_only_when_all_values_agree() {
    #[path = "common/architecture_environment.rs"]
    mod fixture;
    use archsig::canonical::Json;
    for linked in [true, false] {
        let dir = finite_diagnostic_input_at(
            diagnostic_compare_input(&format!("finite-identify-{linked}"), false, true),
            true,
        );
        let old = std::fs::read_to_string(dir.join("d.json")).unwrap();
        let old_digest = definition::check_definitions(&[("d", old.as_bytes())])
            .unwrap()
            .vocabularies()["Reservations"]
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
            .vocabularies()["Reservations"]
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
        let asks = [
            "m=map(Reservations.Migration,on=@v/m,reading=Reservations)",
            "l=localize($m.candidate.source,law=Reservations.linked,x=@v/A,using=Reservations.choose)",
            "r=localize($m.candidate.target,law=Reservations.linked,x=@v/B,using=Reservations.choose)",
            "d=diagnose($l.system,side=semantic,degree=0)",
            "e=diagnose($r.system,side=semantic,degree=0)",
            "c=compare($d.diagnostic,to=$e.diagnostic,kind=diagnostics,along=$m.operation)",
            "n=needed($c)",
        ];
        let r = execute(&dir, "out", &asks);
        assert_eq!(
            r.code,
            if linked { 0 } else { 2 },
            "{linked}: {} {}",
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
    }
}

#[test]
fn finite_change_on_integer_fields_keeps_both_local_state_systems() {
    // 方程式側は整数加群、意味側は有限状態の代表行。
    let dir = diagnostic_compare_input("finite-change-integer-fields", true, true);
    let path = dir.join("l.law");
    let digest = definition::check_definitions(&[(
        "d",
        &std::fs::read(dir.join("d.json")).unwrap(),
    )])
    .unwrap()
    .vocabularies()["Reservations"]
        .digest
        .clone();
    let law = format!(
        "law \"archsig.law/2\" semantics \"archsig/0.6.0\"; reading Reservations {{ use vocabulary Reservations version \"1\" digest \"{digest}\"; change choose(s:State,b:Bool)=s with{{free=if b then 2 else 3}}; law optional localValid(s:State):s.free=2; }}"
    );
    std::fs::write(path, law).unwrap();
    let asks = [
        "m=map(Reservations.Migration,on=@v/m,reading=Reservations)",
        "l=localize($m.candidate.source,law=Reservations.localValid,s=@v/p,using=Reservations.choose)",
        "d=diagnose($l.system,side=equation,degree=0)",
        "e=diagnose($l.system,side=semantic,degree=0)",
        "c=compare($d.diagnostic,to=$d.diagnostic,kind=diagnostics,along=$m.operation)",
        "f=compare($e.diagnostic,to=$e.diagnostic,kind=diagnostics,along=$m.operation)",
        "n=needed($l)",
    ];
    let r = execute(&dir, "out", &asks);
    assert_eq!(r.code, 0, "{} {}", r.stdout, r.stderr);
    let j = result_json(&dir, &r);
    assert!(has(get(&arr(get(&j, "answers"))[1], "outputs"), "system"));
    let space = get(output(&j, 2, "space"), "value");
    let group = get(node(&j, get(space, "module")), "value");
    assert_eq!(num(get(group, "free_rank")), 1);
    assert!(arr(get(group, "torsion")).is_empty());
    let diagnostic = get(output(&j, 3, "diagnostic"), "value");
    let restriction = get(node(&j, get(diagnostic, "restriction")), "value");
    let domain = get(node(&j, get(restriction, "source")), "value");
    let values = arr(get(domain, "elements"));
    assert_eq!(values.len(), 2);
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
    assert_eq!(
        states,
        vec![
            vec!["2".to_string(), "2".to_string()],
            vec!["2".to_string(), "3".to_string()]
        ]
    );
    for i in [4, 5, 6] {
        assert_eq!(s(get(&arr(get(&j, "answers"))[i], "status")), "established");
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
}

fn finite_integer_repaired_fixed_values(explicit: bool) {
    let dir = diagnostic_compare_input(&format!("finite-integer-repaired-fixed-{explicit}"), true, true);
    let digest = definition::check_definitions(&[("d", &std::fs::read(dir.join("d.json")).unwrap())])
        .unwrap().vocabularies()["Reservations"].digest.clone();
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
}

#[test]
fn finite_integer_declared_read_keeps_repaired_guard_and_affine_offset() {
    finite_integer_repaired_fixed_values(true);
}

fn finite_integer_read_input(name: &str, known: bool, joint: bool) -> std::path::PathBuf {
    let definitions=r#"{"format":"archsig.atom-definition/1","semantics":"archsig/0.6.0","vocabularies":[{"semantics":"archsig/0.6.0","namespace":"Pair","version":"1","dependencies":[],"declarations":[{"kind":"entity","name":"Pair.State","meaning":"二つの自由整数と固定値。","parameters":[],"fields":[{"name":"x","type":"Z","meaning":"第一座標。"},{"name":"y","type":"Z","meaning":"第二座標。"},{"name":"z","type":"Z","meaning":"固定値。"}],"alignments":[]}]}]}"#;
    let checked=definition::check_definitions(&[("d",definitions.as_bytes())]).unwrap();
    let digest=&checked.vocabularies()["Pair"].digest;
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
    let digest = &before.vocabularies()["Reservations"].digest;
    let updated = &after.vocabularies()["Reservations"].digest;
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
fn rational_diagnostic_inclusion_has_field_cokernel() {
    // Zならtorsionになるstepでも、Q係数のcokernelはtorsionを持たない。
    let dir = rational_compare_input("rational-inclusion", false);
    let path = dir.join("l.law");
    let law = std::fs::read_to_string(&path).unwrap();
    std::fs::write(&path,law.replace("law optional localValid","change stride(s:State,d:Q)=s with{free=s.free+2*d}; law optional localValid")).unwrap();
    let asks=["m=map(Reservations.Migration,on=@v/m,reading=Reservations)",
        "l=localize($m.candidate.source,law=Reservations.localValid,s=@v/p,using=Reservations.stride)",
        "r=localize($m.candidate.target,law=Reservations.localValid,s=@v/transport_z,using=Reservations.move)",
        "d=diagnose($l.system,side=semantic,degree=0)","e=diagnose($r.system,side=semantic,degree=0)",
        "c=compare($d.diagnostic,to=$e.diagnostic,kind=diagnostics,along=$m.operation)",
        "q=evaluate(Reservations.rank,on=$m.candidate.source,n=$c.comparison.cokernel.free_rank)"];
    let r = execute(&dir, "out", &asks);
    assert_eq!(r.code, 0, "{} {}", r.stdout, r.stderr);
    let j = result_json(&dir, &r);
    let cmp = get(output(&j, 5, "comparison"), "value");
    assert_eq!(s(get(&arr(get(&j, "answers"))[5], "status")), "established");
    for field in ["kernel", "cokernel"] {
        let module = get(node(&j, get(cmp, field)), "value");
        assert_eq!(num(get(module, "free_rank")), 0);
        assert!(arr(get(module, "torsion")).is_empty());
        assert_eq!(
            s(get(get(node(&j, get(module, "ring")), "value"), "scalar")),
            "Q"
        );
    }
    assert_eq!(s(get(output(&j, 6, "value"), "value")), "0");
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
    let digest = &after.vocabularies()["Reservations"].digest;
    let text = std::fs::read_to_string(dir.join("a.json"))
        .unwrap()
        .replace(&before.vocabularies()["Reservations"].digest, digest);
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
    let asks = [
        "m=map(Reservations.Migration,on=@v/m,reading=Reservations)",
        "l=localize($m.candidate.source,law=Reservations.zi,s=@v/p,using=Reservations.zm)",
        "r=localize($m.candidate.source,law=Reservations.qi,s=@v/p,using=Reservations.qm)",
        "d=diagnose($l.system,side=equation,degree=0)",
        "e=diagnose($r.system,side=equation,degree=0)",
        "c=compare($d.diagnostic,to=$e.diagnostic,kind=diagnostics,along=$m.operation)",
    ];
    let r = execute(&dir, "out", &asks);
    assert_eq!(r.code, 64, "{} {}", r.stdout, r.stderr);
}

// Path値を束縛した局所系を両端で診断し、操作に沿って比較する。対応しない束縛値はunsupported。
fn path_binding_comparison(name: &str, evaluations: &[&str], left: &str, right: &str, wrong: bool) {
    let dir = integer_transport_input(name, true);
    let path = dir.join("l.law");
    let law = std::fs::read_to_string(&path).unwrap();
    std::fs::write(&path,law.replace("law optional localValid","law optional pathLaw(s:State,p:Path<State,State>):s.free=2; law optional localValid")).unwrap();
    let mut asks = vec!["m=map(Reservations.Migration,on=@v/m,reading=Reservations)"];
    asks.extend_from_slice(evaluations);
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
        "{name}: {} {}",
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
        for field in ["kernel", "cokernel"] {
            let group = get(node(&j, get(cmp, field)), "value");
            assert_eq!(num(get(group, "free_rank")), 0);
            assert!(arr(get(group, "torsion")).is_empty());
        }
    }
}

#[test]
fn diagnostic_transport_keeps_identity_path_bindings() {
    for (target, wrong) in [("transport_z", false), ("transport_a", true)] {
        let y = format!("y=evaluate(Reservations.emptyPath,on=$m.candidate.target,s=@v/{target})");
        path_binding_comparison(
            &format!("diagnostic-path-identity-{wrong}"),
            &["x=evaluate(Reservations.emptyPath,on=$m.candidate.source,s=@v/p)", y.as_str()],
            "l=localize($m.candidate.source,law=Reservations.pathLaw,s=@v/p,p=$x.value,using=Reservations.move)",
            "r=localize($m.candidate.target,law=Reservations.pathLaw,s=@v/transport_z,p=$y.value,using=Reservations.move)",
            wrong,
        );
    }
}

#[test]
fn diagnostic_transport_keeps_named_path_compositions() {
    path_binding_comparison(
        "diagnostic-path-composite",
        &[
            "x=evaluate(Reservations.route,on=$m.candidate.source,e=@v/e)",
            "y=evaluate(Reservations.route,on=$m.candidate.target,e=@v/transport_zz)",
            "u=evaluate(Reservations.route,on=$m.candidate.source,e=@v/h)",
            "v=evaluate(Reservations.route,on=$m.candidate.target,e=@v/transport_ll)",
            "xx=compose($x.value,then=$u.value)",
            "yy=compose($y.value,then=$v.value)",
        ],
        "l=localize($m.candidate.source,law=Reservations.pathLaw,s=@v/p,p=$xx.operation,using=Reservations.move)",
        "r=localize($m.candidate.target,law=Reservations.pathLaw,s=@v/transport_z,p=$yy.operation,using=Reservations.move)",
        false,
    );
}

#[test]
fn diagnostic_transport_compares_term_bindings_by_their_values() {
    // Term束縛値はアフィン正規形の値で比較する(x+xと2*yは同じ)。
    let dir = integer_transport_input("diagnostic-term", true);
    let path = dir.join("l.law");
    let law = std::fs::read_to_string(&path).unwrap();
    let added = "view termLeft():Term<(Z)->Z> = fn(x:Z)=>x+x; view termRight():Term<(Z)->Z> = fn(y:Z)=>2*y; law optional termLaw(s:State,p:Term<(Z)->Z>):s.free=2; law optional localValid";
    std::fs::write(&path,law.replace("law optional localValid",added)).unwrap();
    let asks = [
        "m=map(Reservations.Migration,on=@v/m,reading=Reservations)",
        "x=evaluate(Reservations.termLeft,on=$m.candidate.source)",
        "y=evaluate(Reservations.termRight,on=$m.candidate.target)",
        "l=localize($m.candidate.source,law=Reservations.termLaw,s=@v/p,p=$x.value,using=Reservations.move)",
        "r=localize($m.candidate.target,law=Reservations.termLaw,s=@v/transport_z,p=$y.value,using=Reservations.move)",
        "d=diagnose($l.system,degree=0)",
        "e=diagnose($r.system,degree=0)",
        "c=compare($d.diagnostic,to=$e.diagnostic,kind=diagnostics,along=$m.operation)",
    ];
    let r=execute(&dir,"out",&asks);
    assert_eq!(r.code,0,"{} {}",r.stdout,r.stderr);
    let j=result_json(&dir,&r);
    let cmp=get(output(&j,7,"comparison"),"value");
    for field in ["kernel","cokernel"] {
        let group=get(node(&j,get(cmp,field)),"value");
        assert_eq!(num(get(group,"free_rank")),0);
        assert!(arr(get(group,"torsion")).is_empty());
    }
}

#[test]
fn finite_integer_noninjective_reads_use_their_images_and_joint_cover() {
    for mode in ["plain", "parallel"] {
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
    }
}

#[test]
fn universal_laws_localize_integer_and_rational_affine_changes() {
    // ZとQは局所化で経路が分かれる。Qは空の解を持つ行を代表に置く。
    for (rational, predicate, rank, empty) in [(false,"s.free+z=z+2",0,false),(false,"z=s.free",2,true),(true,"z=s.free",2,true)] {
        let dir = if rational { rational_compare_input("universal-affine-local-q",true) }
            else { diagnostic_compare_input("universal-affine-local-z",true,true) };
        let digest = definition::check_definitions(&[("d",&std::fs::read(dir.join("d.json")).unwrap())])
            .unwrap().vocabularies()["Reservations"].digest.clone();
        let ty = if rational {"Q"} else {"Z"};
        let law = format!("law \"archsig.law/2\" semantics \"archsig/0.6.0\"; reading Reservations {{ use vocabulary Reservations version \"1\" digest \"{digest}\"; change choose(s:State,n:{ty})=s with{{free=n}}; law required symbolic(z:{ty},s:State,w:{ty}):{predicate}; }}");
        std::fs::write(dir.join("l.law"),law).unwrap();
        let asks = ["m=map(Reservations.Migration,on=@v/m,reading=Reservations)",
            "l=localize($m.candidate.source,using=Reservations.choose)",
            "d=diagnose($l.system,side=equation,degree=0)",
            "e=diagnose($l.system,side=semantic,degree=0)"];
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
    }
}
