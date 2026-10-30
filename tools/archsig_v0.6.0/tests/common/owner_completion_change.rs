use super::*;
use archsig::observed::{
    control::{Control, Limits, Usage},
    input::InputSources,
};

fn sources(
    two_roots: bool,
    change_guard: &str,
    law_guard: &str,
    body: &str,
    empty_possible: bool,
) -> InputSources {
    let original = input();
    let map = String::from_utf8(original.sources().archmap().bytes().to_vec()).unwrap();
    let mut map = map.replace(r#"{"id":"oq","subject":"q","field":"Pattern.Part.owner","value":["v","root"],"origin":"model"},"#, "");
    assert_ne!(
        map,
        String::from_utf8(original.sources().archmap().bytes().to_vec()).unwrap()
    );
    if two_roots {
        map = map.replace(
            r#""subjects":["#,
            r#""subjects":[{"id":"root2","type":"Pattern.Root","origin":"model"},"#,
        );
    }
    if empty_possible {
        map = map.replace(
            r#""id":"op","subject":"p","field":"Pattern.Part.owner","value":["v","root"]"#,
            r#""id":"op","subject":"p","field":"Pattern.Part.owner","value":["v","root2"]"#,
        );
    }
    let law = String::from_utf8(original.sources().law().bytes().to_vec())
        .unwrap()
        .replace(
            "change choose(c:Part,b:Bool)=c",
            &format!("change choose(c:Part,b:Bool){change_guard}=c"),
        )
        .replace(
            "law required valid(c:Part):c.flag",
            &format!("law required valid(c:Part){law_guard}:{body}"),
        );
    InputSources::from_bytes(
        original
            .sources()
            .definitions()
            .iter()
            .map(|d| d.bytes().to_vec())
            .collect(),
        law.into_bytes(),
        map.into_bytes(),
    )
}
fn result(sources: InputSources, asks: &[&str]) -> archsig::json::JNode {
    let prepared = observed::prepare_observed(sources, asks, &mut control()).unwrap();
    let result = observed::evaluate_observed(prepared, &mut control());
    let evaluation = match result {
        Ok(evaluation) => {
            assert_eq!(evaluation.status(), "complete");
            evaluation
        }
        Err(observed::EvaluationFailure::NotImplemented { partial, feature, .. }) => {
            assert!(feature.contains("存在・一意性は検査済み"), "{feature}");
            *partial
        }
        Err(failure) => panic!("unexpected failure: {failure:?}"),
    };
    archsig::json::parse(evaluation.wire().canonical().as_bytes()).unwrap()
}
fn control() -> Control {
    Control::new(Limits::default(), |_| Usage::default())
}
fn evidence(j: &archsig::json::JNode) -> &archsig::json::JNode {
    arr(get(j, "nodes"))
        .iter()
        .find(|n| {
            has(n, "value")
                && matches!(&get(n, "value").value, archsig::json::JValue::Obj(_))
                && has(get(n, "value"), "kind")
                && s(get(get(n, "value"), "kind")) == "completion_fibers"
        })
        .unwrap()
}
fn unique(j: &archsig::json::JNode) -> &str {
    let n = arr(get(j, "nodes"))
        .iter()
        .find(|n| {
            has(n, "value")
                && matches!(&get(n, "value").value, archsig::json::JValue::Obj(_))
                && has(get(n, "value"), "predicate")
                && s(get(get(n, "value"), "predicate")) == "unique_solution"
        })
        .unwrap();
    s(get(get(n, "judgment"), "status"))
}
#[test]
fn finite_owner_completions_quantify_full_solution_fibers_and_keep_family_changes() {
    for (guard, body, existence, uniqueness, mut counts) in [
        ("", "c.flag", "established", "established", vec![1, 1]),
        ("", "false", "refuted", "refuted", vec![0, 0]),
        ("", "true", "established", "refuted", vec![2, 4]),
        (
            " when c.flag and b",
            "true",
            "undetermined",
            "undetermined",
            vec![0, 1],
        ),
        (
            " when c.flag",
            "true",
            "undetermined",
            "refuted",
            vec![0, 2],
        ),
    ] {
        let j = result(
            sources(true, guard, "", body, false),
            &["r=repair(Selected.valid,on=@v/root,using=Selected.choose)"],
        );
        let answer = answer(&j, "r");
        let outputs = get(answer, "outputs");
        let e = node(&j, get(outputs, "existence"));
        assert_eq!(s(get(get(e, "judgment"), "status")), existence);
        assert_eq!(unique(&j), uniqueness);
        assert!(
            !has(outputs, "repair")
                && !has(outputs, "object")
                && !has(outputs, "domain")
                && !has(outputs, "solutions")
        );
        let data = get(get(evidence(&j), "value"), "data");
        let cases = arr(get(data, "cases"));
        assert_eq!(cases.len(), 2);
        let mut actual = cases
            .iter()
            .map(|case| arr(get(case, "assignments")).len())
            .collect::<Vec<_>>();
        actual.sort();
        counts.sort();
        assert_eq!(actual, counts);
        let fields = arr(get(data, "fields"));
        assert_eq!(fields.len(), 1);
        assert_eq!(s(get(&fields[0], "subject")), "q");
        assert_eq!(s(get(&fields[0], "field")), "Pattern.Part.owner");
        let target = node(&j, get(data, "solutions"));
        assert_eq!(s(get(target, "state")), "blocked");
        assert!(!has(target, "value"));
        assert!(!arr(get(&j,"nodes")).iter().any(|n| matches!(&get(n,"type").value, archsig::json::JValue::Str(t) if t=="Assignment"||t=="Repair")));
        if body == "c.flag" {
            let mut widths = cases
                .iter()
                .map(|case| arr(&arr(get(case, "assignments"))[0]).len())
                .collect::<Vec<_>>();
            widths.sort();
            assert_eq!(widths, vec![1, 2]);
        }
    }
}
#[test]
fn finite_owner_completions_keep_empty_subject_product_and_guard_meanings() {
    let j = result(
        sources(true, "", "", "c.flag", true),
        &["r=repair(Selected.valid,on=@v/root,using=Selected.choose)"],
    );
    let cases = arr(get(get(get(evidence(&j), "value"), "data"), "cases"));
    let mut widths = cases
        .iter()
        .map(|case| {
            let solutions = arr(get(case, "assignments"));
            assert_eq!(solutions.len(), 1);
            arr(&solutions[0]).len()
        })
        .collect::<Vec<_>>();
    widths.sort();
    assert_eq!(widths, vec![0, 1]);
    assert_eq!(unique(&j), "established");
    for (change, law, expected) in [
        (" when false", "", "refuted"),
        ("", " when false", "established"),
    ] {
        let j = result(
            sources(true, change, law, "false", false),
            &["r=repair(Selected.valid,on=@v/root,using=Selected.choose)"],
        );
        let e = node(&j, get(get(answer(&j, "r"), "outputs"), "existence"));
        assert_eq!(s(get(get(e, "judgment"), "status")), expected);
    }
}

#[test]
fn finite_owner_completion_stop_does_not_publish_incomplete_exhaustion() {
    use archsig::observed::control::Checkpoint;
    use std::{cell::Cell, rc::Rc};
    for mode in 0..4 {
        let seen = Rc::new(Cell::new(false));
        let stage = seen.clone();
        let mut c = Control::new(
            Limits {
                time_ms: Some(1),
                memory_mib: Some(1),
            },
            move |point| {
                if point == Checkpoint::ChangeWitness {
                    stage.set(true);
                }
                if stage.get() && point == Checkpoint::Completion {
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
                            signal: Some(if mode == 2 {
                                archsig::result::Signal::Int
                            } else {
                                archsig::result::Signal::Term
                            }),
                            ..Usage::default()
                        },
                    }
                } else {
                    Usage::default()
                }
            },
        );
        let value = observed::evaluate_observed_bytes(
            sources(true, "", "", "c.flag", false),
            &[
                "v=evaluate(Selected.flag,c=@v/p)",
                "r=repair(Selected.valid,on=@v/root,using=Selected.choose)",
            ],
            &mut c,
        )
        .unwrap();
        assert!(seen.get());
        let j = archsig::json::parse(value.wire().canonical().as_bytes()).unwrap();
        assert_eq!(s(get(answer(&j, "v"), "status")), "established");
        assert_eq!(s(get(answer(&j, "r"), "status")), "undetermined");
        let archsig::json::JValue::Obj(outputs) = &get(answer(&j, "r"), "outputs").value else {
            panic!("outputs")
        };
        assert!(outputs.is_empty());
        let reason = format!("{:?}", get(answer(&j, "r"), "reasons"));
        for expected in match mode {
            0 => vec!["budget_exhausted", "time_ms"],
            1 => vec!["budget_exhausted", "memory_mib"],
            2 => vec!["cancelled", "SIGINT"],
            _ => vec!["cancelled", "SIGTERM"],
        } {
            assert!(reason.contains(expected), "{reason}");
        }
        assert!(!format!("{:?}", get(&j, "nodes")).contains("completion_fibers"));
    }
}

#[test]
fn finite_owner_completion_cli_preserves_claims_needed_reuse_and_unavailable_handles() {
    let input = sources(true, " when c.flag and b", "", "true", false);
    let dir = workdir("finite-owner-claims");
    for (name, bytes) in [
        ("d.json", input.definitions()[0].bytes()),
        ("l.law", input.law().bytes()),
        ("a.json", input.archmap().bytes()),
    ] {
        std::fs::write(dir.join(name), bytes).unwrap();
    }
    let asks = [
        "r=repair(Selected.valid,on=@v/root,using=Selected.choose)",
        "n=needed($r)",
        "blocked=evaluate(Selected.flag,on=$r.object,c=@v/p)",
        "later=solve(Selected.valid,on=$r.object,using=Selected.choose)",
    ];
    let call = |out: &str, reuse: bool| {
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
            "--time-ms",
            "120000",
        ];
        if reuse {
            args.extend(["--reuse", "out"]);
        }
        for ask in &asks {
            args.extend(["--ask", ask]);
        }
        run(&dir, &args)
    };
    let first = call("out", false);
    assert_eq!(first.code, 70, "{} {}", first.stdout, first.stderr);
    assert!(
        has(&first.receipt, "result"),
        "{} {:?}",
        first.stdout,
        first.receipt
    );
    let j = result_json(&dir, &first);
    assert_eq!(unique(&j), "undetermined");
    for id in ["blocked", "later"] {
        assert_eq!(s(get(answer(&j, id), "status")), "undetermined");
        assert!(format!("{:?}", get(answer(&j, id), "reasons")).contains("dependency_blocked"));
    }
    let plan = node(&j, get(get(answer(&j, "n"), "outputs"), "plan"));
    let requirements = arr(get(get(plan, "value"), "requirements"));
    assert_eq!(requirements.len(), 1);
    assert_eq!(s(get(get(&requirements[0], "field"), "subject")), "q");
    assert_eq!(
        s(get(get(&requirements[0], "field"), "field")),
        "Pattern.Part.owner"
    );
    assert!(!arr(get(&requirements[0], "dependents")).is_empty());
    assert!(format!("{:?}", get(get(plan, "value"), "blockers")).contains("not implemented"));
    let second = call("reuse", true);
    assert_eq!(second.code, 70, "{} {}", second.stdout, second.stderr);
    let reused = result_json(&dir, &second);
    assert!(warnings(&reused).is_empty(), "{:?}", warnings(&reused));
    for key in ["answers", "nodes"] {
        assert_eq!(get(&j, key).value, get(&reused, key).value);
    }
}

#[test]
fn finite_owner_completion_empty_observation_is_invalid_and_other_missing_is_not_exhausted() {
    let source = sources(false, "", "", "c.flag", false);
    let map=String::from_utf8(source.archmap().bytes().to_vec()).unwrap()
        .replace(r#"{"id":"root","type":"Pattern.Root","origin":"model"},"#,"")
        .replace(r#"{"id":"op","subject":"p","field":"Pattern.Part.owner","value":["v","root"],"origin":"model"},"#,"");
    let invalid = InputSources::from_bytes(
        source
            .definitions()
            .iter()
            .map(|d| d.bytes().to_vec())
            .collect(),
        source.law().bytes().to_vec(),
        map.into_bytes(),
    );
    let failure = observed::input::check_inputs(invalid, &mut control()).unwrap_err();
    assert!(
        failure.issues().iter().any(|issue| issue
            .canonical()
            .contains("\"code\":\"inconsistent_observation\"")),
        "{:?}",
        failure.issues()
    );
    for additional in [true, false] {
        let source = sources(false, "", "", "c.flag", false);
        let mut law = String::from_utf8(source.law().bytes().to_vec()).unwrap();
        let mut map = String::from_utf8(source.archmap().bytes().to_vec()).unwrap();
        if additional {
            law = law.replace(
                "change choose(c:Part,b:Bool)=",
                "change choose(c:Part,b:Bool) when c.flag=",
            );
            map=map.replace(r#"{"id":"fp","subject":"p","field":"Pattern.Part.flag","value":true,"origin":"model"},"#,"");
        } else {
            law = law.replace("b:Bool)=c with {flag=b}", "b:Z)=c with {flag=true}");
        }
        if additional {
            assert!(law.contains("when c.flag="), "{law}");
            assert!(!map.contains("\"id\":\"fp\""), "p flag must be missing");
        }
        let input = InputSources::from_bytes(
            source
                .definitions()
                .iter()
                .map(|d| d.bytes().to_vec())
                .collect(),
            law.into_bytes(),
            map.into_bytes(),
        );
        let failure = observed::evaluate_observed_bytes(
            input,
            &["r=repair(Selected.valid,on=@v/root,using=Selected.choose)"],
            &mut control(),
        )
        .unwrap_err();
        let observed::EvaluationFailure::NotImplemented {
            partial, feature, ..
        } = failure
        else {
            panic!("境界外を空解としない")
        };
        assert!(
            !feature.contains("存在・一意性は検査済み"),
            "additional={additional}: {feature}"
        );
        assert!(!partial.wire().canonical().contains("completion_fibers"));
    }
}

#[test]
fn finite_owner_completion_missing_guard_stays_uncompleted_without_an_excluding_sibling() {
    let source = sources(false, " when c.flag", "", "true", false);
    let original = String::from_utf8(source.archmap().bytes().to_vec()).unwrap();
    let map=original.replace(r#"{"id":"fp","subject":"p","field":"Pattern.Part.flag","value":true,"origin":"model"},"#, "")
        .replace(r#""id":"fq","subject":"q","field":"Pattern.Part.flag","value":false"#,r#""id":"fq","subject":"q","field":"Pattern.Part.flag","value":true"#);
    assert_ne!(map, original);
    assert!(!map.contains("\"id\":\"fp\""));
    let input = InputSources::from_bytes(
        source
            .definitions()
            .iter()
            .map(|d| d.bytes().to_vec())
            .collect(),
        source.law().bytes().to_vec(),
        map.into_bytes(),
    );
    let failure = observed::evaluate_observed_bytes(
        input,
        &["r=repair(Selected.valid,on=@v/root,using=Selected.choose)"],
        &mut control(),
    )
    .unwrap_err();
    let observed::EvaluationFailure::NotImplemented {
        partial, feature, ..
    } = failure
    else {
        panic!("未完のguardを全検査としない")
    };
    assert!(!feature.contains("存在・一意性は検査済み"), "{feature}");
    assert!(!partial.wire().canonical().contains("completion_fibers"));
}

fn owned(node: &archsig::json::JNode) -> archsig::canonical::Json {
    use archsig::{canonical::Json as J, json::JValue as V};
    match &node.value {
        V::Bool(v) => J::Bool(*v),
        V::Str(v) => J::str(v),
        V::Num(v) => J::Nat(v.parse().unwrap()),
        V::Arr(v) => J::Arr(v.iter().map(owned).collect()),
        V::Obj(v) => J::Obj(v.iter().map(|(k, v)| (k.clone(), owned(v))).collect()),
        V::Null => panic!("no null"),
    }
}
fn field_mut<'a>(
    node: &'a mut archsig::canonical::Json,
    key: &str,
) -> &'a mut archsig::canonical::Json {
    let archsig::canonical::Json::Obj(fields) = node else {
        panic!("record")
    };
    fields.get_mut(key).unwrap()
}
#[test]
fn finite_owner_completion_error_save_is_explicit_and_reuse_rejects_case_and_request_tamper() {
    use archsig::canonical::Json as J;
    let source = sources(true, "", "", "c.flag", false);
    let dir = workdir("owner-explicit-save");
    for (name, bytes) in [
        ("d.json", source.definitions()[0].bytes()),
        ("l.law", source.law().bytes()),
        ("a.json", source.archmap().bytes()),
    ] {
        std::fs::write(dir.join(name), bytes).unwrap();
    }
    let ask = "r=repair(Selected.valid,on=@v/root,using=Selected.choose)";
    let args = [
        "run",
        "--atom-definition",
        "d.json",
        "--law",
        "l.law",
        "--archmap",
        "a.json",
        "--ask",
        ask,
        "--time-ms",
        "120000",
    ];
    let no_out = run(&dir, &args);
    assert_eq!(no_out.code, 70, "{}", no_out.stdout);
    assert_eq!(s(get(&no_out.receipt, "status")), "error");
    let answer = &arr(get(&no_out.receipt, "answers"))[0];
    assert_eq!(s(get(answer, "uniqueness")), "established");
    assert_eq!(
        s(get(get(get(answer, "outputs"), "existence"), "status")),
        "established"
    );
    for trace in [
        "completion_fibers",
        "assignments",
        "\"node\":",
        "\"arguments\":",
    ] {
        assert!(!no_out.stdout.contains(trace), "{}", no_out.stdout);
    }
    assert_eq!(std::fs::read_dir(&dir).unwrap().count(), 3);
    let mut saved_args = args.to_vec();
    saved_args.extend(["--out", "out"]);
    let first = run(&dir, &saved_args);
    assert_eq!(first.code, 70, "{}", first.stdout);
    let original = result_json(&dir, &first);
    assert_eq!(s(get(&original, "status")), "error");
    assert_eq!(num(get(&original, "exit_code")), 70);
    assert_eq!(unique(&original), "established");
    let path = dir.join(s(get(&first.receipt, "result")));
    let saved = owned(&original);
    for mode in 0..4 {
        let mut damaged = saved.clone();
        let J::Arr(nodes) = field_mut(&mut damaged, "nodes") else {
            panic!("nodes")
        };
        let cert=nodes.iter_mut().find(|node| {
            let J::Obj(fields)=node else {return false};
            matches!(fields.get("value"),Some(J::Obj(value)) if value.get("kind")==Some(&J::str("completion_fibers")))
        }).unwrap();
        let data = field_mut(field_mut(cert, "value"), "data");
        if mode == 3 {
            *field_mut(data, "request") = J::str("different_request");
        } else {
            let J::Arr(cases) = field_mut(data, "cases") else {
                panic!("cases")
            };
            match mode {
                0 => {
                    cases.pop();
                }
                1 => cases.push(cases[0].clone()),
                _ => *field_mut(&mut cases[0], "assignments") = J::Arr(vec![]),
            }
        }
        std::fs::write(&path, damaged.canonical()).unwrap();
        let out = format!("rejected-{mode}");
        let mut repeated = args.to_vec();
        repeated.extend(["--out", &out, "--reuse", "out"]);
        let result = run(&dir, &repeated);
        assert_eq!(result.code, 70, "{}", result.stdout);
        let result = result_json(&dir, &result);
        assert!(
            warnings(&result)
                .iter()
                .any(|issue| s(get(issue, "code")) == "usage")
        );
        for key in ["answers", "nodes"] {
            assert_eq!(get(&original, key).value, get(&result, key).value);
        }
    }
    // 非ownerの未知guardは検査済み成果の資格を得ず、--outを指定しても保存しない。
    let source = sources(false, " when c.flag", "", "true", false);
    let map=String::from_utf8(source.archmap().bytes().to_vec()).unwrap().replace(r#"{"id":"fp","subject":"p","field":"Pattern.Part.flag","value":true,"origin":"model"},"#, "");
    std::fs::write(dir.join("l.law"), source.law().bytes()).unwrap();
    std::fs::write(dir.join("a.json"), map).unwrap();
    let mut rejected = args.to_vec();
    rejected.extend(["--out", "unqualified"]);
    let result = run(&dir, &rejected);
    assert_eq!(result.code, 70, "{}", result.stdout);
    assert!(!has(&result.receipt, "result"));
    assert!(!dir.join("unqualified").exists());
}

#[test]
fn finite_owner_completion_single_root_delivers_repair_and_reuses_checked_structure() {
    let source = sources(false, "", "", "c.flag", false);
    let dir = workdir("owner-concrete-repair");
    for (name, bytes) in [
        ("d.json", source.definitions()[0].bytes()),
        ("l.law", source.law().bytes()),
        ("a.json", source.archmap().bytes()),
    ] {
        std::fs::write(dir.join(name), bytes).unwrap();
    }
    let call = |out: &str, reuse: bool| {
        let mut args = vec![
            "run",
            "--atom-definition",
            "d.json",
            "--law",
            "l.law",
            "--archmap",
            "a.json",
            "--ask",
            "r=repair(Selected.valid,on=@v/root,using=Selected.choose)",
            "--ask",
            "applied=check(Selected.valid,on=$r.object,c=@v/q)",
            "--out",
            out,
            "--time-ms",
            "120000",
        ];
        if reuse {
            args.extend(["--reuse", "out"]);
        }
        run(&dir, &args)
    };
    let first = call("out", false);
    assert_eq!(first.code, 0, "{} {}", first.stdout, first.stderr);
    let original = result_json(&dir, &first);
    let outputs = get(answer(&original, "r"), "outputs");
    for field in ["repair", "object", "solutions"] {
        assert!(has(outputs, field), "{field}");
        assert_eq!(
            s(get(node(&original, get(outputs, field)), "state")),
            "value"
        );
    }
    assert_eq!(
        s(get(answer(&original, "applied"), "status")),
        "established"
    );
    let object = node(&original, get(outputs, "object"));
    assert!(
        arr(get(get(object, "value"), "overrides"))
            .iter()
            .all(|row| s(get(get(row, "slot"), "field")) == "Pattern.Part.flag")
    );
    let second = call("reuse", true);
    assert_eq!(second.code, 0, "{} {}", second.stdout, second.stderr);
    let reused = result_json(&dir, &second);
    assert!(warnings(&reused).is_empty());
    for field in ["answers", "nodes"] {
        assert_eq!(get(&original, field).value, get(&reused, field).value);
    }

    let mut damaged = owned(&original);
    let archsig::canonical::Json::Arr(nodes) = field_mut(&mut damaged, "nodes") else {
        panic!("nodes")
    };
    let configuration = nodes
        .iter_mut()
        .find(|node| {
            let archsig::canonical::Json::Obj(fields) = node else {
                return false;
            };
            fields.get("type") == Some(&archsig::canonical::Json::str("Configuration"))
        })
        .unwrap();
    let archsig::canonical::Json::Arr(family) =
        field_mut(field_mut(configuration, "value"), "family")
    else {
        panic!("family")
    };
    family.pop();
    std::fs::write(
        dir.join(s(get(&first.receipt, "result"))),
        damaged.canonical(),
    )
    .unwrap();
    let rejected = call("rechecked", true);
    assert_eq!(rejected.code, 0, "{}", rejected.stdout);
    let rechecked = result_json(&dir, &rejected);
    assert!(!warnings(&rechecked).is_empty());
    for field in ["answers", "nodes"] {
        assert_eq!(get(&original, field).value, get(&rechecked, field).value);
    }
    assert_eq!(
        std::fs::read(dir.join("a.json")).unwrap(),
        source.archmap().bytes()
    );
}

#[test]
fn finite_owner_definitive_repair_refutations_are_results_without_common_objects() {
    for (body, existence) in [("true", "established"), ("false", "refuted")] {
        let input = sources(true, "", "", body, false);
        let dir = workdir(&format!("owner-refuted-{body}"));
        for (name, bytes) in [
            ("d.json", input.definitions()[0].bytes()),
            ("l.law", input.law().bytes()),
            ("a.json", input.archmap().bytes()),
        ] {
            std::fs::write(dir.join(name), bytes).unwrap();
        }
        let run = run(
            &dir,
            &[
                "run",
                "--atom-definition",
                "d.json",
                "--law",
                "l.law",
                "--archmap",
                "a.json",
                "--ask",
                "r=repair(Selected.valid,on=@v/root,using=Selected.choose)",
                "--out",
                "out",
            ],
        );
        assert_eq!(run.code, 1, "{}", run.stdout);
        let saved = result_json(&dir, &run);
        assert_eq!(s(get(&saved, "status")), "complete");
        let answer = answer(&saved, "r");
        assert_eq!(s(get(answer, "status")), "refuted");
        let outputs = get(answer, "outputs");
        assert!(!has(outputs, "repair") && !has(outputs, "object"));
        let existence_node = node(&saved, get(outputs, "existence"));
        assert_eq!(s(get(get(existence_node, "judgment"), "status")), existence);
        assert!(
            arr(get(&saved, "issues"))
                .iter()
                .all(|issue| s(get(issue, "code")) != "internal")
        );
        let data = get(get(evidence(&saved), "value"), "data");
        let mut counts: Vec<_> = arr(get(data, "cases"))
            .iter()
            .map(|case| arr(get(case, "assignments")).len())
            .collect();
        counts.sort();
        assert_eq!(
            counts,
            if body == "true" {
                vec![2, 4]
            } else {
                vec![0, 0]
            }
        );
    }
}
