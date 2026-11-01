//! 対象族の保存を公開mapと、その後の利用まで検査する。
use crate::common::cli;
use archsig::json::JNode;
use cli::*;
use std::path::{Path, PathBuf};

fn inputs(name: &str) -> PathBuf {
    let dir = workdir(name);
    for (name, bytes) in [
        (
            "d.json",
            include_bytes!("fixtures/reservations.atoms.json").as_slice(),
        ),
        (
            "a.json",
            include_bytes!("fixtures/configuration-operation.archmap.json").as_slice(),
        ),
        (
            "l.law",
            include_bytes!("fixtures/public-compose.law").as_slice(),
        ),
    ] {
        std::fs::write(dir.join(name), bytes).unwrap();
    }
    dir
}
fn asks(dir: &Path, requests: &[&str]) -> Run {
    let mut args = vec![
        "run",
        "--atom-definition",
        "d.json",
        "--archmap",
        "a.json",
        "--law",
        "l.law",
        "--out",
        "out",
    ];
    for request in requests {
        args.extend(["--ask", request]);
    }
    run(dir, &args)
}
fn answer<'a>(result: &'a JNode, id: &str) -> &'a JNode {
    arr(get(result, "answers"))
        .iter()
        .find(|a| s(get(a, "id")) == id)
        .unwrap()
}
fn node<'a>(result: &'a JNode, reference: &JNode) -> &'a JNode {
    arr(get(result, "nodes"))
        .iter()
        .find(|n| s(get(n, "id")) == s(get(reference, "node")))
        .unwrap()
}
fn value<'a>(result: &'a JNode, reference: &JNode) -> &'a JNode {
    get(node(result, reference), "value")
}

fn assert_unsupported_map(dir: &Path, method: &str, operand: &str, original: &str) {
    let requests = [
        "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
        "same=compare($m.operation,to=$m.operation,kind=action)",
        "n=needed($m)",
    ];
    let run = asks(dir, &requests);
    assert_eq!(run.code, 2, "{}", run.stdout);
    let result = result_json(dir, &run);
    assert_eq!(s(get(&result, "status")), "partial");
    let map = answer(&result, "m");
    assert_eq!(s(get(map, "status")), "undetermined");
    let outputs = get(map, "outputs");
    assert!(has(outputs, "candidate"));
    assert!(has(outputs, "operation"));
    assert!(!has(outputs, "map"));
    let reason = arr(get(map, "reasons"))
        .iter()
        .find(|r| {
            s(get(r, "code")) == "unsupported_algorithm"
                && s(get(get(r, "details"), "method")) == method
        })
        .unwrap();
    let expected = archsig::json::parse(operand.as_bytes()).unwrap();
    assert!(
        arr(get(get(reason, "details"), "operand_types"))
            .iter()
            .any(|t| t.value == expected.value)
    );
    let location = get(reason, "location");
    assert_eq!(s(get(location, "input")), "law");
    let span = arr(get(location, "span"));
    let law = std::fs::read(dir.join("l.law")).unwrap();
    let source = std::str::from_utf8(&law[num(&span[0]) as usize..num(&span[1]) as usize]).unwrap();
    assert!(source.contains(original), "{source}");
    assert_eq!(s(get(answer(&result, "same"), "status")), "established");
    assert_eq!(s(get(answer(&result, "n"), "status")), "established");
    let plan = value(&result, get(get(answer(&result, "n"), "outputs"), "plan"));
    assert!(arr(get(plan, "requirements")).is_empty());
    assert!(
        arr(get(plan, "blockers"))
            .iter()
            .any(|r| r.value == reason.value)
    );
}

fn assert_refuted_value_map(dir: &Path) {
    let requests = [
        "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
        "same=compare($m.operation,to=$m.operation,kind=action)",
        "n=needed($m)",
    ];
    let run = asks(dir, &requests);
    assert_eq!(run.code, 1, "{}", run.stdout);
    let result = result_json(dir, &run);
    let map = answer(&result, "m");
    assert_eq!(s(get(map, "status")), "refuted");
    assert!(has(get(map, "outputs"), "operation"));
    assert!(!has(get(map, "outputs"), "map"));
    assert!(
        arr(get(map, "reasons"))
            .iter()
            .all(|r| s(get(r, "code")) != "unsupported_algorithm")
    );
    assert_eq!(s(get(answer(&result, "same"), "status")), "established");
    let plan = value(&result, get(get(answer(&result, "n"), "outputs"), "plan"));
    assert!(arr(get(plan, "requirements")).is_empty());
    assert!(arr(get(plan, "blockers")).is_empty());
}

fn reference_pairs(result: &JNode, map: &JNode) -> Vec<(String, String)> {
    let subject = |reference: &JNode| {
        let scalar = value(result, reference);
        let pair = arr(scalar);
        assert_eq!(pair.len(), 2);
        assert_eq!(s(&pair[0]), "v");
        s(&pair[1]).to_owned()
    };
    let mut pairs: Vec<_> = arr(get(map, "subjects")).iter().map(|pair| {
        let pair = arr(pair);
        assert_eq!(pair.len(), 2);
        (subject(&pair[0]), subject(&pair[1]))
    }).collect();
    pairs.sort();
    pairs
}
fn assert_reference_pairs(result: &JNode, map: &JNode, expected: &[(&str, &str)]) {
    let expected: Vec<_> = expected.iter().map(|(a,b)| (a.to_string(),b.to_string())).collect();
    assert_eq!(reference_pairs(result, map), expected);
}
fn assert_json(actual: &JNode, expected: &str) {
    assert_eq!(actual.value, archsig::json::parse(expected.as_bytes()).unwrap().value);
}
fn assert_local_clause(dir: &Path, result: &JNode, clause: &JNode, source: &str, target: &str, quantifiers: &[(&str, &str)]) {
    let law = std::fs::read(dir.join("l.law")).unwrap();
    for (key, expected) in [("source", source), ("target", target)] {
        let expression = value(result, get(clause, key));
        let location = get(expression, "location");
        assert_eq!(s(get(location, "input")), "law");
        let span = arr(get(location, "span"));
        assert_eq!(&law[num(&span[0]) as usize..num(&span[1]) as usize], expected.as_bytes());
    }
    let commutes = value(result, get(clause, "commutes"));
    let actual = arr(get(commutes, "quantifiers"));
    assert_eq!(actual.len(), quantifiers.len());
    for (q, (name, ty)) in actual.iter().zip(quantifiers) {
        assert_eq!(s(get(q, "kind")), "forall");
        assert_eq!(s(get(q, "name")), *name);
        assert_json(get(q, "type"), &format!(r#"["Ref","{ty}"]"#));
    }
}

// このfixtureの短い値を、保存結果の実値と照合する。
fn assert_summary_value(summary: &JNode, saved: &JNode, reference: &JNode) {
    let original = node(saved, reference);
    assert_eq!(get(summary, "type").value, get(original, "type").value);
    if get(original, "type").value == archsig::json::JValue::Str("Architecture".into()) {
        assert_eq!(
            num(get(summary, "laws_count")),
            arr(get(get(original, "value"), "laws")).len() as u64
        );
    } else {
        assert_eq!(get(summary, "value").value, get(original, "value").value);
    }
}

fn assert_map_summary(normal: &Run, saved: &JNode) {
    let summary = &normal.receipt;
    let archsig::json::JValue::Obj(fields) = &summary.value else {
        panic!("summary object");
    };
    assert_eq!(fields.len(), 4);
    assert_eq!(s(get(summary, "format")), "archsig.summary/1");
    assert_eq!(get(summary, "status").value, get(saved, "status").value);
    assert_eq!(num(get(summary, "exit_code")), normal.code as u64);
    assert_eq!(
        get(summary, "exit_code").value,
        get(saved, "exit_code").value
    );
    assert_eq!(arr(get(summary, "answers")).len(), 3);
    for trace in [
        r#""node":"#,
        r#"\"node\":"#,
        r#""evidence":"#,
        r#""rule":"#,
        r#""scope":"#,
        r#""dependencies":"#,
    ] {
        assert!(
            !normal.stdout.contains(trace),
            "unexpected internal trace: {trace}"
        );
    }
    for (id, question) in [("m", "map"), ("same", "compare"), ("n", "needed")] {
        let brief = answer(summary, id);
        let full = answer(saved, id);
        assert_eq!(s(get(brief, "question")), question);
        assert_eq!(get(brief, "status").value, get(full, "status").value);
        let archsig::json::JValue::Obj(outputs) = &get(brief, "outputs").value else {
            panic!("summary outputs");
        };
        assert_eq!(
            outputs.len(),
            ["candidate", "operation", "map", "comparison", "plan"]
                .iter()
                .filter(|field| has(get(full, "outputs"), field))
                .count()
        );
        let expected_reasons = arr(get(full, "reasons"))
            .iter()
            .filter(|reason| {
                s(get(brief, "status")) == "undetermined"
                    || s(get(reason, "code")) != "missing_observation"
            })
            .map(|reason| s(get(reason, "code")))
            .collect::<std::collections::BTreeSet<_>>();
        let reasons = if has(brief, "reasons") {
            arr(get(brief, "reasons"))
        } else {
            &[]
        };
        assert_eq!(
            reasons
                .iter()
                .map(|reason| s(get(reason, "code")))
                .collect::<std::collections::BTreeSet<_>>(),
            expected_reasons
        );
        for reason in reasons {
            assert!(!s(get(reason, "message")).is_empty());
        }
        for field in ["candidate", "operation", "map", "comparison", "plan"] {
            assert_eq!(
                has(get(brief, "outputs"), field),
                has(get(full, "outputs"), field)
            );
            if has(get(brief, "outputs"), field) {
                assert_eq!(
                    get(get(get(brief, "outputs"), field), "type").value,
                    get(node(saved, get(get(full, "outputs"), field)), "type").value
                );
            }
        }
        let expected = if has(full, "counterexamples") {
            arr(get(full, "counterexamples"))
        } else {
            &[]
        };
        if expected.is_empty() {
            assert!(!has(brief, "counterexamples"));
            assert!(!has(brief, "counterexamples_total"));
            continue;
        }
        assert_eq!(s(get(brief, "status")), "refuted");
        assert_eq!(
            num(get(brief, "counterexamples_total")),
            expected.len() as u64
        );
        let shown = arr(get(brief, "counterexamples"));
        assert_eq!(shown.len(), expected.len().min(3));
        for (example, reference) in shown.iter().zip(expected) {
            let data = get(value(saved, reference), "data");
            for side in ["left", "right"] {
                assert_summary_value(get(example, side), saved, get(data, side));
            }
            let bindings = arr(get(data, "bindings"));
            assert_eq!(num(get(example, "bindings_total")), bindings.len() as u64);
            let actual = arr(get(example, "bindings"));
            assert_eq!(actual.len(), bindings.len().min(3));
            for (actual, original) in actual.iter().zip(bindings) {
                assert_eq!(get(actual, "name").value, get(original, "name").value);
                assert_summary_value(get(actual, "value"), saved, get(original, "value"));
            }
            let facts = arr(get(data, "facts"));
            assert_eq!(num(get(example, "facts_total")), facts.len() as u64);
            let actual = arr(get(example, "facts"));
            assert_eq!(actual.len(), facts.len().min(3));
            for (actual, original) in actual.iter().zip(facts) {
                assert_eq!(actual.value, original.value);
            }
        }
    }
    assert_eq!(
        s(get(
            get(get(answer(summary, "same"), "outputs"), "comparison"),
            "kind"
        )),
        "action"
    );
}

#[test]
fn change_transport_preserves_candidate_domains_and_simultaneous_updates() {
    for (mode, parameter, sg, tg, left, right, missing, code, status) in [
        ("finite", "Bool", "", " when k or not k", "if n then s.free+1 else s.free", "if k then t.free+1 else t.free", false, 0, "established"),
        ("integer-refuted", "Z", "", "", "s.free+n", "t.free+2*k", false, 1, "refuted"),
        ("missing", "Z", "", "", "s.free+n", "t.free+k", true, 2, "undetermined"),
    ] {
        let dir = four_state_inputs(&format!("change-transport-{mode}"));
        let vocabulary = r#"use vocabulary Reservations version "1" digest "sha256:8427a2712c22d6eed1cdd5f48258bea102904173558a7087bb82c7d95665c9ff";"#;
        std::fs::write(dir.join("l.law"),format!(r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{vocabulary} change tune(s:State,n:{parameter}){sg}=s with {{free={left},held=s.free}};}}
reading After {{{vocabulary} change tune(t:State,k:{parameter}){tg}=t with {{held=t.free,free={right}}};}}"#)).unwrap();
        if missing {
            let text=std::fs::read_to_string(dir.join("a.json")).unwrap();
            std::fs::write(dir.join("a.json"),text.lines().filter(|line|!line.contains(r#""id":"p-free""#)).collect::<Vec<_>>().join("\n")).unwrap();
        }
        let requests=["m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)","same=compare($m.operation,to=$m.operation,kind=action)","n=needed($m)"];
        let run=asks(&dir,&requests);assert_eq!(run.code,code,"{mode}: {}",run.stdout);
        let result=result_json(&dir,&run);let m=answer(&result,"m");
        assert_eq!(s(get(m,"status")),status,"{mode}");assert_eq!(s(get(answer(&result,"same"),"status")),"established");
        assert_eq!(has(get(m,"outputs"),"map"),code==0);
        if code==0 {
            let map=value(&result,get(get(m,"outputs"),"map"));let transport=value(&result,&arr(get(map,"transports"))[0]);
            assert_eq!(s(get(transport,"kind")),"change");assert_json(get(transport,"parameters"),r#"[["s","t"],["n","k"]]"#);
        }
        if code==1 {let examples=arr(get(m,"counterexamples"));assert!(!examples.is_empty());
            let data=get(value(&result,&examples[0]),"data");let bindings=arr(get(data,"bindings"));assert_eq!(bindings.len(),2);
            assert_eq!(s(get(&bindings[1],"name")),"n");
            assert_eq!(s(value(&result,get(&bindings[1],"value"))),"1");
        }
        if code==2 {let plan=value(&result,get(get(answer(&result,"n"),"outputs"),"plan"));assert!(arr(get(plan,"requirements")).iter().any(|r|s(get(get(r,"field"),"subject"))=="p"));}
    }
}

#[test]
fn change_transport_uses_explicit_field_alignments_instead_of_same_names() {
    // 明記したalign(free↔held)が同名の対応に代わる。preserveはtargetのheldへ同じ更新を置く。
    for (mode, preserve, code) in [("align", true, 0), ("align-refuted", false, 1)] {
        let dir = four_state_inputs(&format!("change-fix-{mode}"));
        let old = "sha256:8427a2712c22d6eed1cdd5f48258bea102904173558a7087bb82c7d95665c9ff";
        let definition = std::fs::read_to_string(dir.join("d.json")).unwrap().replacen(r#""alignments": []"#,r#""alignments":[{"source":"Reservations.State.free","target":"Reservations.State.held","meaning":"数量位置の交換。"},{"source":"Reservations.State.held","target":"Reservations.State.free","meaning":"数量位置の交換。"}]"#,1);
        let checked = archsig::definition::check_definitions(&[("d", definition.as_bytes())]).unwrap();
        let digest = checked.vocabularies()["Reservations"].digest.clone();
        std::fs::write(dir.join("d.json"), definition).unwrap();
        let archmap = std::fs::read_to_string(dir.join("a.json")).unwrap().replace(old, &digest);
        let archmap = archmap.lines().map(|line| {
            let mut text = line.to_string();
            if line.contains("Reservations.State.free") || line.contains("Reservations.State.held") {
                for n in ["1", "2", "3", "4", "19"] {
                    text = text.replace(&format!(r#""value":"{n}""#), r#""value":"0""#);
                }
            }
            text
        }).collect::<Vec<_>>().join("\n");
        std::fs::write(dir.join("a.json"), archmap).unwrap();
        let (tf, th) = if preserve { ("0", "if k then 1 else 0") } else { ("if k then 1 else 0", "0") };
        std::fs::write(dir.join("l.law"), format!(r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{use vocabulary Reservations version "1" digest "{digest}";change tune(s:State,n:Bool)=s with {{free=if n then 1 else 0,held=0}};}}
reading After {{use vocabulary Reservations version "1" digest "{digest}";change tune(t:State,k:Bool)=t with {{free={tf},held={th}}};}}"#)).unwrap();
        let requests = ["m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)", "same=compare($m.operation,to=$m.operation,kind=action)", "n=needed($m)"];
        let run = asks(&dir, &requests);
        assert_eq!(run.code, code, "{mode}: {}", run.stdout);
        let result = result_json(&dir, &run);
        let m = answer(&result, "m");
        assert_eq!(s(get(m, "status")), if code == 0 { "established" } else { "refuted" });
        assert_eq!(s(get(answer(&result, "same"), "status")), "established");
        assert_eq!(has(get(m, "outputs"), "map"), code == 0);
        if code == 0 {
            let map = value(&result, get(get(m, "outputs"), "map"));
            let transport = value(&result, &arr(get(map, "transports"))[0]);
            let clause = &arr(get(transport, "clauses"))[1];
            let target = value(&result, get(clause, "target"));
            let span = arr(get(get(target, "location"), "span"));
            let law = std::fs::read(dir.join("l.law")).unwrap();
            assert_eq!(&law[num(&span[0]) as usize..num(&span[1]) as usize], th.as_bytes());
            let q = &arr(get(value(&result, get(clause, "commutes")), "quantifiers"))[0];
            let domain = value(&result, get(q, "domain"));
            assert_eq!(arr(get(domain, "elements")).len(), 2);
        } else {
            assert!(!arr(get(m, "counterexamples")).is_empty());
        }
    }
}

#[test]
fn change_transport_let_if_updates_keep_whole_sources_and_simultaneous_values() {
    let finite = "let old=s.free in if n then s with {free=old+s.held,held=old} else s with {held=old,free=old}";
    for (case, parameter, left, right, code) in [
        (
            "finite",
            "Bool",
            finite,
            "let prior=t.free in if not k then t with {held=prior,free=prior} else t with {held=prior,free=prior+t.held}",
            0,
        ),
        (
            "finite_refuted",
            "Bool",
            finite,
            "let prior=t.free in if not k then t with {held=prior,free=prior} else t with {held=prior,free=prior+t.held+1}",
            1,
        ),
        (
            "integer_if",
            "Z",
            "let delta=n+1 in if s.free=2 then s with {free=s.free+delta,held=s.free} else s with {free=s.free+n-1,held=s.free}",
            "let amount=k+1 in if not (t.free=2) then t with {held=t.free,free=t.free+k-1} else t with {held=t.free,free=t.free+amount}",
            0,
        ),
    ] {
        let dir = four_state_inputs(&format!("change-lexical-{case}"));
        let vocabulary = r#"use vocabulary Reservations version "1" digest "sha256:8427a2712c22d6eed1cdd5f48258bea102904173558a7087bb82c7d95665c9ff";"#;
        let law = format!(
            r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{ {vocabulary} change tune(s:State,n:{parameter})={left}; }}
reading After {{ {vocabulary} change tune(t:State,k:{parameter})={right}; }}"#
        );
        std::fs::write(dir.join("l.law"), &law).unwrap();
        let requests = [
            "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
            "same=compare($m.operation,to=$m.operation,kind=action)",
        ];
        let run = asks(&dir, &requests);
        assert_eq!(run.code, code, "{case}: {}", run.stdout);
        let result = result_json(&dir, &run);
        let map_answer = answer(&result, "m");
        assert_eq!(
            s(get(map_answer, "status")),
            if code == 0 { "established" } else { "refuted" },
            "{case}"
        );
        assert_eq!(s(get(answer(&result, "same"), "status")), "established");
        assert_eq!(has(get(map_answer, "outputs"), "map"), code == 0);
        if code == 0 {
            let map = value(&result, get(get(map_answer, "outputs"), "map"));
            let transport = value(&result, &arr(get(map, "transports"))[0]);
            let clauses = arr(get(transport, "clauses"));
            assert_eq!(clauses.len(), 3);
            assert_ne!(
                s(get(value(&result, get(&clauses[0], "source")), "kind")),
                "change_update"
            );
            for (clause, field) in clauses[1..].iter().zip(["free", "held"]) {
                for (side, body) in [("source", left), ("target", right)] {
                    let expression = value(&result, get(clause, side));
                    assert_eq!(s(get(expression, "kind")), "change_update");
                    assert_eq!(
                        s(get(expression, "field")),
                        format!("Reservations.State.{field}")
                    );
                    let original = value(&result, get(expression, "source"));
                    assert_eq!(s(get(original, "kind")), "source");
                    assert_eq!(
                        get(expression, "parameters").value,
                        get(original, "parameters").value
                    );
                    assert_eq!(
                        get(expression, "bindings").value,
                        get(original, "bindings").value
                    );
                    let span = arr(get(get(original, "location"), "span"));
                    assert_eq!(
                        &law.as_bytes()[num(&span[0]) as usize..num(&span[1]) as usize],
                        body.as_bytes()
                    );
                }
            }
        } else {
            let examples = arr(get(map_answer, "counterexamples"));
            assert!(!examples.is_empty());
            let data = get(value(&result, &examples[0]), "data");
            let bindings = arr(get(data, "bindings"));
            assert!(matches!(
                value(&result, get(&bindings[1], "value")).value,
                archsig::json::JValue::Bool(true)
            ));
        }
    }
}

#[test]
fn incomplete_endpoint_algebras_keep_configuration_operation_and_original_reasons() {
    for (mode, code, status) in [
        ("refuted", 1, "refuted"),
        ("unsupported", 2, "undetermined"),
    ] {
        let dir = four_state_inputs(&format!("endpoint-algebra-{mode}"));
        let old_digest = "sha256:8427a2712c22d6eed1cdd5f48258bea102904173558a7087bb82c7d95665c9ff";
        if mode == "refuted" {
            let definition = std::fs::read_to_string(dir.join("d.json")).unwrap().replace(r#"{"name": "free", "type": "Z""#, r#"{"name":"peer","type":["Ref","Reservations.State"],"meaning":"参照先。"}, {"name": "free", "type": "Z""#);
            let checked =
                archsig::definition::check_definitions(&[("d", definition.as_bytes())]).unwrap();
            let digest = &checked.vocabularies()["Reservations"].digest;
            std::fs::write(dir.join("d.json"), definition).unwrap();
            let mut a = std::fs::read_to_string(dir.join("a.json"))
                .unwrap()
                .replace(old_digest, digest);
            let mut facts = String::new();
            for (subject, peer) in [("p", "q"), ("q", "p"), ("r", "s"), ("s", "r")] {
                facts.push_str(&format!(r#"{{"id":"{subject}-peer","subject":"{subject}","field":"Reservations.State.peer","value":["v","{peer}"],"origin":"model"}},"#));
            }
            a = a.replace("\"atoms\":[", &format!("\"atoms\":[{facts}"));
            std::fs::write(dir.join("a.json"), a).unwrap();
            std::fs::write(dir.join("l.law"),format!(r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{use vocabulary Reservations version "1" digest "{digest}"; local here(s:State) reads s.peer;}}
reading After {{use vocabulary Reservations version "1" digest "{digest}"; local here(t:State) reads t.peer;}}"#)).unwrap();
        } else {
            let digest = old_digest;
            std::fs::write(dir.join("l.law"),format!(r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{use vocabulary Reservations version "1" digest "{digest}"; law required positive(s:State):s.free>0;}}
reading After {{use vocabulary Reservations version "1" digest "{digest}"; law required positive(t:State):t.free>0;}}"#)).unwrap();
        }
        let requests = [
            "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
            "same=compare($m.operation,to=$m.operation,kind=action)",
            "n=needed($m)",
        ];
        let run = asks(&dir, &requests);
        assert_eq!(run.code, code, "{}", run.stdout);
        let result = result_json(&dir, &run);
        let map = answer(&result, "m");
        assert_eq!(s(get(map, "status")), status);
        assert!(!has(get(map, "outputs"), "map"));
        assert!(
            has(get(map, "outputs"), "operation"),
            "{mode}: {}",
            run.stdout
        );
        assert_eq!(s(get(answer(&result, "same"), "status")), "established");
        assert!(!arr(get(map, "reasons")).is_empty());
        if mode == "refuted" {
            let examples = arr(get(map, "counterexamples"));
            for subject in ["p", "q", "r", "s"] {
                assert!(examples.iter().any(|example| {
                    arr(get(get(value(&result, example), "data"), "facts"))
                        .iter()
                        .any(|fact| {
                            s(get(fact, "subject")) == subject
                                && has(fact, "field")
                                && s(get(fact, "field")) == "Reservations.State.peer"
                        })
                }));
            }
            assert!(
                arr(get(map, "reasons"))
                    .iter()
                    .any(|r| s(get(r, "code")) == "condition_failed"
                        && s(get(get(r, "details"), "construction")) == "object_algebra")
            );
        } else {
            assert!(arr(get(map, "reasons")).iter().any(|r| s(get(r, "code"))
                == "unsupported_algorithm"
                && s(get(get(r, "details"), "method")) == "integer_order_equation_presentation"));
            let plan = value(&result, get(get(answer(&result, "n"), "outputs"), "plan"));
            assert!(arr(get(plan, "requirements")).is_empty());
        }
    }
}

#[test]
fn local_multiple_reference_parameters_keep_read_order_and_value_types() {
    let dir = inputs("local-multiple-reference-transport");
    let vocabulary = r#"use vocabulary Reservations version "1" digest "sha256:8427a2712c22d6eed1cdd5f48258bea102904173558a7087bb82c7d95665c9ff";"#;
    std::fs::write(dir.join("l.law"),format!(r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{vocabulary} local here(s:State,root:System,other:State) reads root,s,other,root;}}
reading After {{{vocabulary} local here(t:State,world:System,u:State) reads world,(t),u,world;}}"#)).unwrap();
    let request="m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)";
    let run=asks(&dir,&[request]);
    assert_eq!(run.code,0,"{}",run.stdout);
    let result=result_json(&dir,&run);
    let map=value(&result,get(get(answer(&result,"m"),"outputs"),"map"));
    let transport=value(&result,&arr(get(map,"transports"))[0]);
    assert_json(get(transport,"parameters"), r#"[["s","t"],["root","world"],["other","u"]]"#);
    let clauses=arr(get(transport,"clauses"));
    assert_eq!(clauses.len(),4);
    assert_eq!(get(&clauses[0],"values").value,get(&clauses[3],"values").value);
    assert_eq!(get(&clauses[1],"values").value,get(&clauses[2],"values").value);
    assert_ne!(get(&clauses[0],"values").value,get(&clauses[1],"values").value);
    let arguments=value(&result,get(&clauses[0],"arguments"));
    for key in ["source_type", "target_type"] {
        assert_json(get(arguments,key), r#"["Tuple",["Ref","Reservations.State"],["Ref","Reservations.System"],["Ref","Reservations.State"]]"#);
    }
    assert_reference_pairs(&result, arguments, &[("A","B"),("B","B"),("p","r"),("q","s"),("r","r"),("s","s")]);
    for (index, (source,target,ty)) in [("root","world","Reservations.System"),("s","(t)","Reservations.State"),("other","u","Reservations.State"),("root","world","Reservations.System")].iter().enumerate() {
        let clause = &clauses[index];
        assert_eq!(get(clause,"arguments").value,get(&clauses[0],"arguments").value);
        let values=value(&result,get(clause,"values"));
        for key in ["source_type","target_type"] {assert_json(get(values,key), &format!(r#"["Ref","{ty}"]"#));}
        if *ty == "Reservations.System" {
            assert_reference_pairs(&result,values,&[("A","B"),("B","B")]);
        } else {
            assert_reference_pairs(&result,values,&[("p","r"),("q","s"),("r","r"),("s","s")]);
        }
        assert_local_clause(&dir,&result,clause,source,target,&[("s","Reservations.State"),("root","Reservations.System"),("other","Reservations.State")]);
    }
}

#[test]
fn local_guard_domains_preserve_source_rows_and_keep_unknown_distinct() {
    for (mode, source, target, read, missing, code, status) in [
        ("expansion", "s.free=2", "t.free>0", "field", "", 0, "established"),
        ("guard-refuted", "s.free=2", "t.free=1", "reference", "", 1, "refuted"),
        ("source-missing", "s.free=2", "true", "reference", "p", 2, "undetermined"),
    ] {
        let dir = four_state_inputs(&format!("local-domain-{mode}"));
        let vocabulary = r#"use vocabulary Reservations version "1" digest "sha256:8427a2712c22d6eed1cdd5f48258bea102904173558a7087bb82c7d95665c9ff";"#;
        let (sr, tr) = if read == "reference" { ("s", "t") } else { ("s.free", "t.free") };
        std::fs::write(dir.join("l.law"), format!(r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{vocabulary} local here(s:State) when {source} reads {sr};}}
reading After {{{vocabulary} local here(t:State) when {target} reads {tr};}}"#)).unwrap();
        if !missing.is_empty() {
            let text = std::fs::read_to_string(dir.join("a.json")).unwrap();
            let text = text.lines().filter(|line| !line.contains(&format!(r#""id":"{missing}-free""#))).collect::<Vec<_>>().join("\n");
            std::fs::write(dir.join("a.json"), text).unwrap();
        }
        let requests = [
            "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
            "same=compare($m.operation,to=$m.operation,kind=action)",
            "n=needed($m)",
        ];
        let run = asks(&dir, &requests);
        assert_eq!(run.code, code, "{mode}: {}", run.stdout);
        let result = result_json(&dir, &run);
        let m = answer(&result, "m");
        assert_eq!(s(get(m, "status")), status, "{mode}");
        assert_eq!(s(get(answer(&result, "same"), "status")), "established", "{mode}");
        assert_eq!(has(get(m, "outputs"), "map"), code == 0);
        if code == 1 {
            let examples = arr(get(m, "counterexamples"));
            assert!(!examples.is_empty());
            let data = get(value(&result, &examples[0]), "data");
            assert_json(value(&result, get(data, "left")), "true");
            assert_json(value(&result, get(data, "right")), "false");
        }
        if code == 2 {
            let plan = value(&result, get(get(answer(&result, "n"), "outputs"), "plan"));
            assert!(arr(get(plan, "requirements")).iter().any(|r| s(get(get(r, "field"), "subject")) == missing));
        }
    }
}

#[test]
fn local_reference_fields_follow_the_map_instead_of_raw_equality() {
    let dir = four_state_inputs("local-reference-field-preserved");
    let old = std::fs::read_to_string(dir.join("d.json")).unwrap();
    let definition = old.replace(r#"{"name": "free", "type": "Z""#, r#"{"name":"other","type":["Ref","Reservations.State"],"meaning":"別の参照先。"}, {"name":"peer","type":["Ref","Reservations.State"],"meaning":"参照先。"}, {"name": "free", "type": "Z""#);
    let checked =
        archsig::definition::check_definitions(&[("d", definition.as_bytes())]).unwrap();
    let digest = &checked.vocabularies()["Reservations"].digest;
    std::fs::write(dir.join("d.json"), definition).unwrap();
    let old_digest = "sha256:8427a2712c22d6eed1cdd5f48258bea102904173558a7087bb82c7d95665c9ff";
    let mut a = std::fs::read_to_string(dir.join("a.json"))
        .unwrap()
        .replace(old_digest, digest);
    let mut facts = String::new();
    for (subject, peer) in [
        ("p", "p"),
        ("q", "p"),
        ("r", "r"),
        ("s", "r"),
    ] {
        facts.push_str(&format!(r#"{{"id":"{subject}-peer","subject":"{subject}","field":"Reservations.State.peer","value":["v","{peer}"],"origin":"model"}},"#));
        let other = match peer {
            "p" => "q",
            "r" => "s",
            _ => peer,
        };
        facts.push_str(&format!(r#"{{"id":"{subject}-other","subject":"{subject}","field":"Reservations.State.other","value":["v","{other}"],"origin":"model"}},"#));
    }
    a = a.replace("\"atoms\":[", &format!("\"atoms\":[{facts}"));
    // 内部操作の端点保存とは分けて、localの参照値移送を検査する。
    a = without_reserve_instances(&a);
    std::fs::write(dir.join("a.json"), a).unwrap();
    std::fs::write(dir.join("l.law"), format!(r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{use vocabulary Reservations version "1" digest "{digest}"; local here(s:State) reads s.peer;}}
reading After {{use vocabulary Reservations version "1" digest "{digest}"; local here(t:State) reads (t.peer);}}"#)).unwrap();
    let requests = [
        "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
        "same=compare($m.operation,to=$m.operation,kind=action)",
        "n=needed($m)",
    ];
    let mut args = vec![
        "run",
        "--atom-definition",
        "d.json",
        "--law",
        "l.law",
        "--archmap",
        "a.json",
    ];
    for request in requests {
        args.extend(["--ask", request]);
    }
    let normal = without_file_changes(&dir, || cli::run(&dir, &args));
    assert_eq!(normal.code, 0, "{}", normal.stdout);
    let run = asks(&dir, &requests);
    assert_eq!(run.code, 0, "{}", run.stdout);
    let result = result_json(&dir, &run);
    assert_map_summary(&normal, &result);
    assert_eq!(s(get(answer(&result, "m"), "status")), "established");
    assert_eq!(s(get(answer(&result, "same"), "status")), "established");
    let outputs = get(answer(&result, "m"), "outputs");
    let map = value(&result, get(outputs, "map"));
    let transport = value(&result, &arr(get(map, "transports"))[0]);
    let clause = &arr(get(transport, "clauses"))[0];
    assert_local_clause(
        &dir,
        &result,
        clause,
        "s.peer",
        "(t.peer)",
        &[("s", "Reservations.State")],
    );
    assert_reference_pairs(
        &result,
        value(&result, get(clause, "values")),
        &[("p", "r"), ("q", "s"), ("r", "r"), ("s", "s")],
    );
}

#[test]
fn object_map_keeps_all_objects_generators_and_public_source_consumption() {
    // 小さいfixtureの対象はA,p,q(Bはr,s)、生成元は予約操作e(Bはf)。
    let dir = small_inputs("public-object-map");
    let run = asks(
        &dir,
        &[
            "m=map(Reservations.Migration,on=@v/m,reading=Alternative,kind=object_algebra)",
            "base=map(Reservations.Migration,on=@v/m,reading=Alternative)",
            "same=compare($m.operation,to=$base.operation,kind=action)",
            "built=build(Alternative,on=$m.map.source.base.subject)",
        ],
    );
    assert_eq!(run.code, 0, "{}", run.stdout);
    let result = result_json(&dir, &run);
    assert_eq!(s(get(&result, "status")), "complete");
    for id in ["m", "base", "same", "built"] {
        assert_eq!(s(get(answer(&result, id), "status")), "established");
    }
    let reference = get(get(answer(&result, "m"), "outputs"), "map");
    assert_eq!(s(get(node(&result, reference), "type")), "ObjectAlgebraMap");
    let map = value(&result, reference);
    assert_eq!(arr(get(map, "object_maps")).len(), 3);
    assert_eq!(arr(get(map, "operation_maps")).len(), 1);
    let state_pair = arr(get(map, "declarations"))
        .iter()
        .find(|p| s(get(p, "source")) == "Reservations.State")
        .unwrap();
    assert_eq!(s(get(state_pair, "target")), "Reservations.State");
    assert_eq!(arr(get(state_pair, "parameters")).len(), 1);
    assert_eq!(
        arr(&arr(get(state_pair, "parameters"))[0])
            .iter()
            .map(s)
            .collect::<Vec<_>>(),
        ["owner", "owner"]
    );
    for field in ["Reservations.State.free", "Reservations.State.held"] {
        assert!(
            arr(get(state_pair, "fields"))
                .iter()
                .any(|p| arr(p).iter().map(s).collect::<Vec<_>>() == [field, field])
        );
    }
    assert!(!arr(get(node(&result, reference), "conditions")).is_empty());
    for row in arr(get(map, "object_maps")) {
        let map_node = node(&result, get(row, "map"));
        let conditions = arr(get(map_node, "conditions"));
        assert!(!conditions.is_empty());
        for condition in conditions {
            assert_eq!(
                s(get(get(node(&result, condition), "judgment"), "status")),
                "established"
            );
        }
    }
    let proposition = value(
        &result,
        get(get(answer(&result, "m"), "outputs"), "proposition"),
    );
    let label = &arr(get(proposition, "operands"))[0];
    assert_eq!(s(value(&result, label)), "object_algebra_map");
    for side in ["source", "target"] {
        let algebra = value(&result, get(map, side));
        assert_eq!(arr(get(algebra, "objects")).len(), 3);
        assert_eq!(arr(get(get(algebra, "operations"), "generators")).len(), 1);
    }
    std::fs::remove_dir_all(dir).unwrap();
}

#[test]
fn missing_declaration_keeps_the_configuration_operation_after_refutation() {
    let dir = inputs("public-object-map-missing-declaration");
    let run = asks(
        &dir,
        &[
            "m=map(Reservations.Migration,on=@v/m,reading=Reservations,to_reading=Alternative,kind=object_algebra)",
            "same=compare($m.operation,to=$m.operation,kind=action)",
            "plan=needed($m)",
        ],
    );
    assert_eq!(run.code, 1, "{}", run.stdout);
    let result = result_json(&dir, &run);
    assert_eq!(s(get(&result, "status")), "complete");
    assert_eq!(s(get(answer(&result, "m"), "status")), "refuted");
    assert_eq!(s(get(answer(&result, "same"), "status")), "established");
    assert_eq!(s(get(answer(&result, "plan"), "status")), "established");
    get(get(answer(&result, "m"), "outputs"), "operation");
    let outputs = get(answer(&result, "m"), "outputs");
    let archsig::json::JValue::Obj(fields) = &outputs.value else {
        panic!()
    };
    assert!(!fields.iter().any(|(name, _)| name == "map"));
    std::fs::remove_dir_all(dir).unwrap();
}

#[test]
fn reuse_recomputes_object_maps_and_rejects_an_omitted_object() {
    // 小さいfixture(状態4つ)とguardのないlocal一つのLawで、保存結果の照合だけを確かめる。
    let dir = four_state_inputs("public-object-map-reuse");
    let vocabulary = r#"use vocabulary Reservations version "1" digest "sha256:8427a2712c22d6eed1cdd5f48258bea102904173558a7087bb82c7d95665c9ff";"#;
    std::fs::write(dir.join("l.law"), format!(r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{vocabulary} local here(s:State) reads s.free;}}
reading After {{{vocabulary} local here(t:State) reads t.free;}}"#)).unwrap();
    let request = "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)";
    let first = asks(&dir, &[request]);
    assert_eq!(first.code, 0, "{}", first.stdout);
    let original = result_json(&dir, &first);
    let repeat = |out: &str| {
        run(
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
                out,
                "--reuse",
                "out",
                "--ask",
                request,
            ],
        )
    };
    let reused = repeat("reused");
    assert_eq!(reused.code, 0, "{}", reused.stdout);
    let result = result_json(&dir, &reused);
    assert!(warnings(&result).is_empty());
    let map = value(
        &original,
        get(get(answer(&original, "m"), "outputs"), "map"),
    );
    let objects = arr(get(map, "object_maps")).len();
    let row = &arr(get(map, "object_maps"))[1];
    // 改変するのは今回のCLIが書いた保存出力だけ。入力三点は変更しない。
    let row_text = format!(
        "{{\"map\":{{\"node\":\"{}\"}},\"source\":{{\"node\":\"{}\"}},\"target\":{{\"node\":\"{}\"}}}}",
        s(get(get(row, "map"), "node")),
        s(get(get(row, "source"), "node")),
        s(get(get(row, "target"), "node"))
    );
    let file = dir.join("out/result.json");
    let before = std::fs::read_to_string(&file).unwrap();
    let pattern = format!(",{row_text}");
    assert!(before.contains(&pattern));
    std::fs::write(file, before.replacen(&pattern, "", 1)).unwrap();
    let rejected = repeat("rejected");
    assert_eq!(rejected.code, 0, "{}", rejected.stdout);
    let result = result_json(&dir, &rejected);
    assert!(!warnings(&result).is_empty());
    assert!(!has(&result, "reuse"));
    let map = value(&result, get(get(answer(&result, "m"), "outputs"), "map"));
    assert_eq!(arr(get(map, "object_maps")).len(), objects);
    std::fs::remove_dir_all(dir).unwrap();
}

#[test]
fn interruption_during_additional_transport_keeps_the_checked_operation() {
    use archsig::result::Signal;
    use archsig::{
        control::{Checkpoint, Control},
        input::InputSources,
        observed::evaluate_observed_bytes,
    };
    // 停止理由の区別はcontrol層で確かめる。ここでは移送中の停止の1種だけを見る。
    let mut control = Control::new(|p| {
        let stop = p == Checkpoint::ConfigurationTransportGenerator;
        stop.then_some(Signal::Int)
    });
    let result = evaluate_observed_bytes(
        InputSources::from_bytes(
            vec![include_bytes!("fixtures/reservations.atoms.json").to_vec()],
            include_bytes!("fixtures/public-compose.law").to_vec(),
            four_state_map(false).into_bytes(),
        ),
        &["m=map(Reservations.Migration,on=@v/m,reading=Alternative,kind=object_algebra)"],
        &mut control,
    )
    .unwrap();
    assert_eq!(result.status(), "interrupted");
    let wire = archsig::json::parse(result.wire().canonical().as_bytes()).unwrap();
    let a = answer(&wire, "m");
    assert_eq!(s(get(a, "status")), "undetermined");
    assert!(has(get(a, "outputs"), "operation"));
    assert!(has(get(a, "outputs"), "candidate"));
    assert!(!has(get(a, "outputs"), "map"));
    assert!(!has(get(a, "outputs"), "proposition"));
    assert!(control.stop_reason().is_some());
}

// 状態4つ(A:p,q、B:r,s)と予約操作1つずつの小さいfixture。preserveはfreeの値をmで保つ。
fn four_state_map(preserve: bool) -> String {
    let mut a = include_str!("fixtures/object-configuration-map.archmap.json").to_string();
    if preserve {
        a = a.replace(r#""id":"r-free","subject":"r","field":"Reservations.State.free","value":"4""#, r#""id":"r-free","subject":"r","field":"Reservations.State.free","value":"2""#)
            .replace(r#""id":"s-free","subject":"s","field":"Reservations.State.free","value":"3""#, r#""id":"s-free","subject":"s","field":"Reservations.State.free","value":"1""#);
    }
    a.lines()
        .filter(|line| {
            !line.contains(r#""id":"u","type":"#)
                && !line.contains(r#""id":"w","type":"#)
                && !line.contains(r#""subject":"u""#)
                && !line.contains(r#""subject":"w""#)
        })
        .collect::<Vec<_>>()
        .join("\n")
        .replace(r#",[["v","u"],["v","w"]]"#, "")
        .replace(",\n]", "\n]")
}
// 公開composeのLawと小さいfixture(値はmで保たない)。
fn small_inputs(name: &str) -> PathBuf {
    let dir = inputs(name);
    std::fs::write(dir.join("a.json"), four_state_map(false)).unwrap();
    dir
}
fn four_state_inputs(name: &str) -> PathBuf {
    let dir = inputs(name);
    std::fs::write(dir.join("a.json"), four_state_map(true)).unwrap();
    let vocabulary = r#"use vocabulary Reservations version "1" digest "sha256:8427a2712c22d6eed1cdd5f48258bea102904173558a7087bb82c7d95665c9ff";"#;
    let law = format!(r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{
{vocabulary}
view choice(s: State, take: Bool, mode: Fp(2)): Z = if take then (if mode = 0 then s.free else s.held) else 0;
}}
reading After {{
{vocabulary}
view choice(s: State, keep: Bool, which: Fp(2)): Z = if keep then (if which = 0 then s.free else s.held) else 0;
view yes(): Bool = true;
view zero(): Fp(2) = 0;
view one(): Fp(2) = 1;
}}"#);
    std::fs::write(dir.join("l.law"), law).unwrap();
    dir
}

#[test]
fn mixed_numeric_guard_keeps_its_reason_and_checked_operation() {
    let (dir, vocabulary) = finite_local_parameter_inputs("mixed-numeric-guard-partial");
    std::fs::write(
        dir.join("l.law"),
        format!(
            r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{vocabulary} local here(z:Z,q:Q) when z=1 reads z;}}
reading After {{{vocabulary} local here(n:Z,r:Q) reads n;}}"#
        ),
    )
    .unwrap();
    assert_unsupported_map(
        &dir,
        "local_integer_guard_fiber",
        r#""Z""#,
        "when z=1 reads z",
    );
    let bytes = std::fs::read(dir.join("out/result.json")).unwrap();
    let result = archsig::json::parse(&bytes).unwrap();
    let reason = arr(get(answer(&result, "m"), "reasons"))
        .iter()
        .find(|r| s(get(r, "code")) == "unsupported_algorithm")
        .unwrap();
    let rational = archsig::json::parse(br#""Q""#).unwrap();
    assert!(
        arr(get(get(reason, "details"), "operand_types"))
            .iter()
            .any(|t| t.value == rational.value)
    );
    std::fs::remove_dir_all(dir).unwrap();
}

#[test]
fn reference_containers_do_not_use_same_nominal_type_identity() {
    let dir = four_state_inputs("reference-container-view");
    let vocabulary = r#"use vocabulary Reservations version "1" digest "sha256:8427a2712c22d6eed1cdd5f48258bea102904173558a7087bb82c7d95665c9ff";"#;
    std::fs::write(
        dir.join("l.law"),
        format!(
            r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{vocabulary} view refs(s:State):List<State> = list<State>[s];}}
reading After {{{vocabulary} view refs(s:State):List<State> = list<State>[s];}}"#
        ),
    )
    .unwrap();
    assert_refuted_value_map(&dir);
}

#[test]
fn relation_transport_keeps_named_words_empty_words_and_parameter_positions() {
    for case in ["unit", "alias"] {
        let dir = four_state_inputs(&format!("relation-transport-{case}"));
        if case == "alias" {
            let path = dir.join("a.json");
            let data=std::fs::read_to_string(&path).unwrap()
                .replace(r#""id":"e-to","subject":"e","field":"Reservations.Reserve.to","value":["v","q"]"#,r#""id":"e-to","subject":"e","field":"Reservations.Reserve.to","value":["v","p"]"#)
                .replace(r#""id":"f-to","subject":"f","field":"Reservations.Reserve.to","value":["v","s"]"#,r#""id":"f-to","subject":"f","field":"Reservations.Reserve.to","value":["v","r"]"#)
                .replace(r#"{"id":"f","type":"Reservations.Reserve","origin":"model"},"#,r#"{"id":"f","type":"Reservations.Reserve","origin":"model"},{"id":"g","type":"Reservations.Reserve","origin":"model"},"#)
                .replace(r#""atoms":["#,r#""atoms":[{"id":"g-owner","subject":"g","field":"Reservations.Reserve.owner","value":["v","B"],"origin":"model"},{"id":"g-from","subject":"g","field":"Reservations.Reserve.from","value":["v","r"],"origin":"model"},{"id":"g-to","subject":"g","field":"Reservations.Reserve.to","value":["v","r"],"origin":"model"},"#);
            std::fs::write(path, data).unwrap();
        }
        let (source, target) = if case == "unit" {
            (
                "relation paths(e:Reserve): path(e)=then(identity(source(path(e))),path(e));",
                "relation paths(t:Reserve): then(path(t),identity(target(path(t))))=path(t);",
            )
        } else {
            (
                "relation paths(e:Reserve,f:Reserve): path(e)=path(e);",
                "relation paths(u:Reserve,v:Reserve): path(v)=path(v);",
            )
        };
        let vocabulary = r#"use vocabulary Reservations version "1" digest "sha256:8427a2712c22d6eed1cdd5f48258bea102904173558a7087bb82c7d95665c9ff";"#;
        std::fs::write(
            dir.join("l.law"),
            format!(
                r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{ {vocabulary} {source} }}
reading After {{ {vocabulary} {target} }}"#
            ),
        )
        .unwrap();
        let run = asks(
            &dir,
            &[
                "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
                "same=compare($m.operation,to=$m.operation,kind=action)",
            ],
        );
        assert_eq!(
            run.code,
            if case == "unit" { 0 } else { 1 },
            "{case}: {}",
            run.stdout
        );
        let result = result_json(&dir, &run);
        assert_eq!(
            s(get(answer(&result, "m"), "status")),
            if case == "unit" {
                "established"
            } else {
                "refuted"
            },
            "{case}: {}",
            run.stdout
        );
        assert_eq!(s(get(answer(&result, "same"), "status")), "established");
        if case == "unit" {
            let map = value(&result, get(get(answer(&result, "m"), "outputs"), "map"));
            let transport = arr(get(map, "transports"))
                .iter()
                .map(|r| value(&result, r))
                .find(|t| s(get(t, "kind")) == "relation")
                .unwrap();
            for clause in arr(get(transport, "clauses")) {
                let moved = value(&result, get(clause, "values"));
                assert_reference_pairs(
                    &result,
                    moved,
                    &[
                        ("e", "f"),
                        ("f", "f"),
                        ("p", "r"),
                        ("q", "s"),
                        ("r", "r"),
                        ("s", "s"),
                    ],
                );
            }
        } else {
            assert!(!has(get(answer(&result, "m"), "outputs"), "map"));
            let examples = arr(get(answer(&result, "m"), "counterexamples"));
            assert!(!examples.is_empty());
            let data = get(value(&result, &examples[0]), "data");
            let names = |side: &str| {
                arr(get(value(&result, get(data, side)), "generators"))
                    .iter()
                    .map(|r| s(&arr(value(&result, r))[1]).to_owned())
                    .collect::<Vec<_>>()
            };
            assert_eq!(names("left"), ["f"]);
            assert_eq!(names("right"), ["g"]);
        }
    }
}

#[test]
fn relation_transport_keeps_missing_generator_actions_pending_and_independent_word_refutations() {
    for changed in [false, true] {
        let dir = four_state_inputs(if changed {
            "relation-missing-and-refuted"
        } else {
            "relation-missing"
        });
        let path = dir.join("a.json");
        let mut data = std::fs::read_to_string(&path).unwrap();
        if changed {
            data=data.replace(r#""id":"e-to","subject":"e","field":"Reservations.Reserve.to","value":["v","q"]"#,r#""id":"e-to","subject":"e","field":"Reservations.Reserve.to","value":["v","p"]"#)
                .replace(r#""id":"f-to","subject":"f","field":"Reservations.Reserve.to","value":["v","s"]"#,r#""id":"f-to","subject":"f","field":"Reservations.Reserve.to","value":["v","r"]"#);
        }
        data=data.replace(r#""subjects":["#,r#""subjects":[{"id":"C","type":"Reservations.System","origin":"model"},{"id":"x","type":"Reservations.State","origin":"model"},{"id":"h","type":"Reservations.Reserve","origin":"model"},"#)
            .replace(r#""atoms":["#,r#""atoms":[{"id":"x-owner","subject":"x","field":"Reservations.State.owner","value":["v","C"],"origin":"model"},{"id":"x-held","subject":"x","field":"Reservations.State.held","value":"0","origin":"model"},{"id":"h-owner","subject":"h","field":"Reservations.Reserve.owner","value":["v","C"],"origin":"model"},{"id":"h-from","subject":"h","field":"Reservations.Reserve.from","value":["v","x"],"origin":"model"},{"id":"h-to","subject":"h","field":"Reservations.Reserve.to","value":["v","x"],"origin":"model"},"#);
        std::fs::write(path, data).unwrap();
        let before = if changed {
            "identity(source(path(e)))"
        } else {
            "path(e)"
        };
        let vocabulary = r#"use vocabulary Reservations version "1" digest "sha256:8427a2712c22d6eed1cdd5f48258bea102904173558a7087bb82c7d95665c9ff";"#;
        std::fs::write(
            dir.join("l.law"),
            format!(
                r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{ {vocabulary} relation paths(e:Reserve): {before}={before}; }}
reading After {{ {vocabulary} relation paths(t:Reserve): path(t)=path(t); }}"#
            ),
        )
        .unwrap();
        let run = asks(
            &dir,
            &[
                "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
                "same=compare($m.operation,to=$m.operation,kind=action)",
                "n=needed($m)",
            ],
        );
        assert_eq!(run.code, if changed { 1 } else { 2 }, "{}", run.stdout);
        let result = result_json(&dir, &run);
        assert_eq!(
            s(get(answer(&result, "m"), "status")),
            if changed { "refuted" } else { "undetermined" },
            "{}",
            run.stdout
        );
        assert_eq!(s(get(answer(&result, "same"), "status")), "established");
        assert!(!has(get(answer(&result, "m"), "outputs"), "map"));
        if changed {
            assert!(!arr(get(answer(&result, "m"), "counterexamples")).is_empty());
        } else {
            let plan = value(&result, get(get(answer(&result, "n"), "outputs"), "plan"));
            assert!(arr(get(plan, "requirements")).iter().any(|r| s(get(
                get(r, "field"),
                "subject"
            )) == "x"
                && s(get(get(r, "field"), "field")) == "Reservations.State.free"));
            assert!(!has(answer(&result, "m"), "counterexamples"));
        }
    }
}

#[test]
fn relation_guard_transport_keeps_required_unknowns_and_ignores_target_extra_unknowns() {
    // targetのguardが必要な未知(target)は未決、追加適用行だけの未知(extra)は成立。
    for (case, sg, tg) in [
        ("target", "", "when u.free>0"),
        ("extra", "when take", "when if keep then true else u.free>0"),
    ] {
        let dir = four_state_inputs(&format!("relation-guard-missing-{case}"));
        let path = dir.join("a.json");
        let data=std::fs::read_to_string(&path).unwrap()
            .replace(r#""subjects":["#,r#""subjects":[{"id":"C","type":"Reservations.System","origin":"model"},{"id":"x","type":"Reservations.State","origin":"model"},"#)
            .replace(r#""atoms":["#,r#""atoms":[{"id":"x-owner","subject":"x","field":"Reservations.State.owner","value":["v","C"],"origin":"model"},{"id":"x-held","subject":"x","field":"Reservations.State.held","value":"0","origin":"model"},"#);
        std::fs::write(path, data).unwrap();
        let vocabulary = r#"use vocabulary Reservations version "1" digest "sha256:8427a2712c22d6eed1cdd5f48258bea102904173558a7087bb82c7d95665c9ff";"#;
        std::fs::write(
            dir.join("l.law"),
            format!(
                r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{ {vocabulary} relation paths(e:Reserve,s:State,take:Bool) {sg}:path(e)=path(e); }}
reading After {{ {vocabulary} relation paths(t:Reserve,u:State,keep:Bool) {tg}:path(t)=path(t); }}"#
            ),
        )
        .unwrap();
        let requests = [
            "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
            "same=compare($m.operation,to=$m.operation,kind=action)",
            "n=needed($m)",
        ];
        let run = asks(&dir, &requests);
        assert_eq!(
            run.code,
            if case == "extra" { 0 } else { 2 },
            "{case}: {}",
            run.stdout
        );
        let result = result_json(&dir, &run);
        assert_eq!(
            s(get(answer(&result, "m"), "status")),
            if case == "extra" {
                "established"
            } else {
                "undetermined"
            }
        );
        assert_eq!(s(get(answer(&result, "same"), "status")), "established");
        let plan = value(&result, get(get(answer(&result, "n"), "outputs"), "plan"));
        if case == "extra" {
            assert!(arr(get(plan, "requirements")).is_empty());
        } else {
            assert!(arr(get(plan, "requirements")).iter().any(|r| s(get(
                get(r, "field"),
                "subject"
            )) == "x"
                && s(get(get(r, "field"), "field")) == "Reservations.State.free"));
        }
    }
}

#[test]
fn relation_transport_reports_infinite_parameter_cases_as_pending() {
    for (name, source, target) in [
        (
            "infinite",
            "relation paths(e:Reserve,n:Z) when n>0:path(e)=path(e);",
            "relation paths(t:Reserve,k:Z) when k>0:path(t)=path(t);",
        ),
    ] {
        let dir = four_state_inputs(&format!("relation-unsupported-{name}"));
        let vocabulary = r#"use vocabulary Reservations version "1" digest "sha256:8427a2712c22d6eed1cdd5f48258bea102904173558a7087bb82c7d95665c9ff";"#;
        std::fs::write(
            dir.join("l.law"),
            format!(
                r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{ {vocabulary} {source} }} reading After {{ {vocabulary} {target} }}"#
            ),
        )
        .unwrap();
        let run = asks(
            &dir,
            &[
                "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
                "same=compare($m.operation,to=$m.operation,kind=action)",
                "n=needed($m)",
            ],
        );
        assert_eq!(run.code, 2, "{name}: {}", run.stdout);
        let result = result_json(&dir, &run);
        assert_eq!(s(get(answer(&result, "m"), "status")), "undetermined");
        assert!(!has(get(answer(&result, "m"), "outputs"), "map"));
        assert_eq!(s(get(answer(&result, "same"), "status")), "established");
        let plan = value(&result, get(get(answer(&result, "n"), "outputs"), "plan"));
        assert!(arr(get(plan, "requirements")).is_empty());
        assert!(!arr(get(plan, "blockers")).is_empty());
    }
}

#[test]
fn heterogeneous_relation_words_use_actual_reachable_generators_and_full_path_witnesses() {
    use archsig::canonical::Json;
    for case in ["preserved", "alias", "cycle", "missing", "endpoints"] {
        let dir = workdir(&format!("heterogeneous-relation-{case}"));
        let mut declarations = vec![];
        for name in ["X", "Y", "ZRoot"] {
            declarations.push(Json::obj([
                ("kind", Json::str("entity")),
                ("name", Json::str(format!("Flow.{name}"))),
                ("meaning", Json::str("有限経路の端点。")),
                ("parameters", Json::Arr(vec![])),
                ("fields", Json::Arr(vec![])),
                ("alignments", Json::Arr(vec![])),
            ]));
        }
        for (name, from, to) in [
            ("Stay", "X", "X"),
            ("XY", "X", "Y"),
            ("YZ", "Y", "ZRoot"),
            ("ZX", "ZRoot", "X"),
            ("XZ", "X", "ZRoot"),
            ("YX", "Y", "X"),
        ] {
            declarations.push(Json::obj([
                ("kind", Json::str("correspondence")),
                ("name", Json::str(format!("Flow.{name}"))),
                ("meaning", Json::str("型付き経路の生成元。")),
                (
                    "parameters",
                    Json::Arr(
                        [("from", from), ("to", to)]
                            .into_iter()
                            .map(|(name, ty)| {
                                Json::obj([
                                    ("name", Json::str(name)),
                                    (
                                        "type",
                                        Json::Arr(vec![
                                            Json::str("Ref"),
                                            Json::str(format!("Flow.{ty}")),
                                        ]),
                                    ),
                                    ("meaning", Json::str("経路端点。")),
                                ])
                            })
                            .collect(),
                    ),
                ),
                ("fields", Json::Arr(vec![])),
                ("alignments", Json::Arr(vec![])),
            ]));
        }
        let definition = Json::obj([
            ("format", Json::str("archsig.atom-definition/1")),
            ("semantics", Json::str("archsig/0.6.0")),
            (
                "vocabularies",
                Json::Arr(vec![Json::obj([
                    ("namespace", Json::str("Flow")),
                    ("version", Json::str("1")),
                    ("semantics", Json::str("archsig/0.6.0")),
                    ("dependencies", Json::Arr(vec![])),
                    ("declarations", Json::Arr(declarations)),
                ])]),
            ),
        ])
        .canonical();
        let checked =
            archsig::definition::check_definitions(&[("d", definition.as_bytes())]).unwrap();
        let digest = &checked.vocabularies()["Flow"].digest;
        std::fs::write(dir.join("d.json"), definition.as_bytes()).unwrap();
        let mut subjects = vec![];
        let mut atoms = vec![];
        for (name, ty) in [
            ("x", "X"),
            ("x2", "X"),
            ("y", "Y"),
            ("y2", "Y"),
            ("z", "ZRoot"),
            ("m", "Stay"),
            ("a", "XY"),
            ("b", "YZ"),
            ("c", "ZX"),
            ("d", "XZ"),
            ("q", "YX"),
        ] {
            subjects.push(Json::obj([
                ("id", Json::str(name)),
                ("type", Json::str(format!("Flow.{ty}"))),
                ("origin", Json::str("model")),
            ]));
        }
        for (id, ty, from, to) in [
            (
                "m",
                "Stay",
                "x",
                if case == "endpoints" { "x2" } else { "x" },
            ),
            ("a", "XY", "x", "y"),
            ("b", "YZ", "y", "z"),
            ("c", "ZX", "z", "x"),
            ("d", "XZ", "x", "z"),
            ("q", "YX", "y2", "x2"),
        ] {
            for (field, value) in [("from", from), ("to", to)] {
                if case == "missing" && id == "b" && field == "to" {
                    continue;
                }
                atoms.push(Json::obj([
                    ("id", Json::str(format!("{id}-{field}"))),
                    ("subject", Json::str(id)),
                    ("field", Json::str(format!("Flow.{ty}.{field}"))),
                    ("value", Json::Arr(vec![Json::str("v"), Json::str(value)])),
                    ("origin", Json::str("model")),
                ]));
            }
        }
        let archmap = Json::obj([
            ("format", Json::str("archsig.archmap/2")),
            ("semantics", Json::str("archsig/0.6.0")),
            (
                "vocabularies",
                Json::Arr(vec![Json::obj([
                    ("namespace", Json::str("Flow")),
                    ("version", Json::str("1")),
                    ("digest", Json::str(digest)),
                ])]),
            ),
            ("sources", Json::Arr(vec![])),
            (
                "origins",
                Json::Arr(vec![Json::obj([
                    ("id", Json::str("model")),
                    ("mode", Json::str("specification")),
                    ("method", Json::str("異種端点経由の有限生成元。")),
                    ("locations", Json::Arr(vec![])),
                    ("note", Json::str("実端点と名前付き語を検査する。")),
                ])]),
            ),
            (
                "snapshots",
                Json::Arr(vec![Json::obj([
                    ("id", Json::str("v")),
                    ("origin", Json::str("model")),
                    ("subjects", Json::Arr(subjects)),
                    ("atoms", Json::Arr(atoms)),
                ])]),
            ),
        ])
        .canonical();
        std::fs::write(dir.join("a.json"), archmap).unwrap();
        let (source, target) = match case {
            "alias" => (
                "relation paths(a:XY,b:YZ,d:XZ):then(path(a),path(b))=then(path(a),path(b));",
                "relation paths(u:XY,v:YZ,w:XZ):path(w)=path(w);",
            ),
            "cycle" => (
                "relation paths(m:Stay,a:XY,b:YZ,c:ZX):then(path(m),then(path(a),then(path(b),path(c))))=then(path(m),then(path(a),then(path(b),path(c))));",
                "relation paths(n:Stay,u:XY,v:YZ,w:ZX):then(then(path(u),then(path(v),path(w))),path(n))=then(then(path(u),then(path(v),path(w))),path(n));",
            ),
            _ => (
                "relation paths(a:XY,b:YZ):then(path(a),path(b))=then(path(a),path(b));",
                "relation paths(u:XY,v:YZ):then(identity(source(path(u))),then(path(u),path(v)))=then(path(u),path(v));",
            ),
        };
        let vocabulary = format!(r#"use vocabulary Flow version "1" digest "{digest}";"#);
        let law = format!(
            r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{ {vocabulary} {source} }} reading After {{ {vocabulary} {target} }}
reading Helpers {{ {vocabulary} view same(a:XY,b:YZ,d:XZ):Bool=then(path(a),path(b))=path(d); }}"#
        );
        std::fs::write(dir.join("l.law"), law).unwrap();
        let mut requests = vec![
            "m=map(Flow.Stay,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
            "same=compare($m.operation,to=$m.operation,kind=action)",
            "n=needed($m)",
        ];
        if case == "alias" {
            requests.push("action=evaluate(Helpers.same,a=@v/a,b=@v/b,d=@v/d)");
        }
        let code = match case {
            "preserved" => 0,
            "missing" => 2,
            _ => 1,
        };
        let run = asks(&dir, &requests);
        assert_eq!(run.code, code, "{case}: {}", run.stdout);
        let result = result_json(&dir, &run);
        assert_eq!(
            s(get(answer(&result, "m"), "status")),
            match case {
                "preserved" => "established",
                "missing" => "undetermined",
                _ => "refuted",
            }
        );
        assert_eq!(s(get(answer(&result, "same"), "status")), "established");
        if case == "preserved" {
            let map = value(&result, get(get(answer(&result, "m"), "outputs"), "map"));
            let transport = value(&result, &arr(get(map, "transports"))[0]);
            for clause in arr(get(transport, "clauses")) {
                let values = value(&result, get(clause, "values"));
                assert_json(
                    get(values, "source_type"),
                    r#"["Path","Flow.X","Flow.ZRoot"]"#,
                );
                let mut names = arr(get(values, "generators"))
                    .iter()
                    .map(|pair| s(&arr(value(&result, &arr(pair)[0]))[1]).to_owned())
                    .collect::<Vec<_>>();
                names.sort();
                assert_eq!(names, ["a", "b", "c", "d", "m"]); // q:y2→x2はXから到達しない。
            }
        } else {
            assert!(!has(get(answer(&result, "m"), "outputs"), "map"));
        }
        if case == "missing" {
            let plan = value(&result, get(get(answer(&result, "n"), "outputs"), "plan"));
            assert!(arr(get(plan, "requirements")).iter().any(|r| s(get(
                get(r, "field"),
                "subject"
            )) == "b"
                && s(get(get(r, "field"), "field")) == "Flow.YZ.to"));
        } else if code == 1 {
            let examples = arr(get(answer(&result, "m"), "counterexamples"));
            assert!(!examples.is_empty());
            let data = get(value(&result, &examples[0]), "data");
            if case == "endpoints" {
                assert_eq!(s(&arr(value(&result, get(data, "left")))[1]), "x2");
                assert_eq!(s(&arr(value(&result, get(data, "right")))[1]), "x");
                let source = value(&result, &arr(get(data, "paths"))[0]);
                assert_eq!(s(&arr(value(&result, get(source, "source")))[1]), "x");
                assert_eq!(s(&arr(value(&result, get(source, "target")))[1]), "z");
            } else {
                let word = |side: &str| {
                    arr(get(value(&result, get(data, side)), "generators"))
                        .iter()
                        .map(|r| s(&arr(value(&result, r))[1]).to_owned())
                        .collect::<Vec<_>>()
                };
                assert_eq!(
                    word("left"),
                    if case == "cycle" {
                        vec!["m", "a", "b", "c"]
                    } else {
                        vec!["a", "b"]
                    }
                );
                assert_eq!(
                    word("right"),
                    if case == "cycle" {
                        vec!["a", "b", "c", "m"]
                    } else {
                        vec!["d"]
                    }
                );
            }
        }
        if case == "alias" {
            assert!(matches!(
                value(
                    &result,
                    get(get(answer(&result, "action"), "outputs"), "value")
                )
                .value,
                archsig::json::JValue::Bool(true)
            ));
        }
    }
}

#[test]
fn relation_transport_restricts_integer_families_to_exact_guard_domains() {
    // source guardの整数fiber上で、target guardが外れる点を実際の反例として返す。
    let dir = four_state_inputs("relation-integer-domain-guard_refuted");
    let vocabulary = r#"use vocabulary Reservations version "1" digest "sha256:8427a2712c22d6eed1cdd5f48258bea102904173558a7087bb82c7d95665c9ff";"#;
    std::fs::write(dir.join("l.law"), format!(r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{ {vocabulary} relation paths(n:Z,e:Reserve,m:Z,take:Bool,extra:Z) when n+m=3:(path(e))=path(e); }}
reading After {{ {vocabulary} relation paths(k:Z,t:Reserve,j:Z,keep:Bool,last:Z) when k=0:(path(t))=path(t); }}"#)).unwrap();
    let requests = [
        "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
        "same=compare($m.operation,to=$m.operation,kind=action)",
        "n=needed($m)",
    ];
    let run = asks(&dir, &requests);
    assert_eq!(run.code, 1, "{}", run.stdout);
    let result = result_json(&dir, &run);
    assert_eq!(s(get(answer(&result, "m"), "status")), "refuted");
    assert_eq!(s(get(answer(&result, "same"), "status")), "established");
    assert!(!has(get(answer(&result, "m"), "outputs"), "map"));
    let examples = arr(get(answer(&result, "m"), "counterexamples"));
    assert!(!examples.is_empty());
    for example in examples {
        let data = get(value(&result, example), "data");
        let bindings = arr(get(data, "bindings"));
        assert_eq!(
            bindings
                .iter()
                .map(|b| s(get(b, "name")))
                .collect::<Vec<_>>(),
            ["n", "e", "m", "take", "extra"]
        );
        let n = s(value(&result, get(&bindings[0], "value")))
            .parse::<i64>()
            .unwrap();
        let m = s(value(&result, get(&bindings[2], "value")))
            .parse::<i64>()
            .unwrap();
        assert_eq!(n + m, 3);
        assert_ne!(n, 0);
    }
}

#[test]
fn local_boolean_only_parameters_use_the_whole_boolean_product() {
    for (case, target, code) in [
        ("preserved", "if keep then other else false", 0),
        ("refuted", "if keep then not other else false", 1),
    ] {
        let dir = four_state_inputs(&format!("local-only-bool-{case}"));
        let vocabulary = r#"use vocabulary Reservations version "1" digest "sha256:8427a2712c22d6eed1cdd5f48258bea102904173558a7087bb82c7d95665c9ff";"#;
        std::fs::write(
            dir.join("l.law"),
            format!(
                r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{vocabulary} local here(take:Bool,mode:Bool) reads if take then mode else false;}}
reading After {{{vocabulary} local here(keep:Bool,other:Bool) reads {target};}}"#
            ),
        )
        .unwrap();
        let run = asks(
            &dir,
            &[
                "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
            ],
        );
        assert_eq!(run.code, code, "{case}: {}", run.stdout);
        let result = result_json(&dir, &run);
        let m = answer(&result, "m");
        assert!(has(get(m, "outputs"), "operation"));
        if code == 1 {
            let data = get(value(&result, &arr(get(m, "counterexamples"))[0]), "data");
            let bs = arr(get(data, "bindings"));
            assert_eq!(bs.len(), 2);
            assert_eq!(s(get(&bs[0], "name")), "take");
            assert_json(value(&result, get(&bs[0], "value")), "true");
            assert_eq!(s(get(&bs[1], "name")), "mode");
            assert_json(value(&result, get(&bs[1], "value")), "false");
            assert_json(value(&result, get(data, "left")), "false");
            assert_json(value(&result, get(data, "right")), "true");
        }
    }
}

fn finite_local_parameter_inputs(name: &str) -> (PathBuf, String) {
    let dir = four_state_inputs(name);
    let old = std::fs::read_to_string(dir.join("d.json")).unwrap();
    let definition=old.replacen("\"declarations\": [",r#""declarations": [{"kind":"data","name":"Reservations.Choice","meaning":"有限選択値","constructors":[{"name":"Empty","arguments":[],"meaning":"空の選択"},{"name":"Full","arguments":["Bool"],"meaning":"真偽値を持つ選択"}]},"#,1);
    let before = archsig::definition::check_definitions(&[("d", old.as_bytes())]).unwrap();
    let after = archsig::definition::check_definitions(&[("d", definition.as_bytes())]).unwrap();
    let digest = &after.vocabularies()["Reservations"].digest;
    let map = std::fs::read_to_string(dir.join("a.json"))
        .unwrap()
        .replace(&before.vocabularies()["Reservations"].digest, digest);
    std::fs::write(dir.join("d.json"), definition).unwrap();
    std::fs::write(dir.join("a.json"), map).unwrap();
    (
        dir,
        format!(r#"use vocabulary Reservations version "1" digest "{digest}";"#),
    )
}

#[test]
fn local_finite_parameters_share_full_domain_transport_without_type_branches() {
    // 有限型引数は型によらず同じ全域移送を通る(型の差はfinite.rsの列挙だけ)。
    // 後ろの行だけが違う反例を、行数の少ないUnit型の引数で確かめる。
    let (dir, vocabulary) = finite_local_parameter_inputs("local-finite-unit-late-row");
    let (t_condition, u_condition) = ("@=unit", "@=unit");
    let pc = t_condition.replace('@', "p");
    let tc = t_condition.replace('@', "t");
    let qc = u_condition.replace('@', "q");
    let sr = format!("if {tc} then z.free else a.free");
    let base = format!("if {pc} then y.free else x.free");
    let tr = format!("if ({pc}) and ({qc}) and y.held=1 and x.free=2 then y.free+1 else {base}");
    std::fs::write(
        dir.join("l.law"),
        format!(
            r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{vocabulary} local here(t:Unit,z:State,u:Unit,a:State) reads {sr};}}
reading After {{{vocabulary} local here(p:Unit,y:State,q:Unit,x:State) reads {tr};}}"#
        ),
    )
    .unwrap();
    let requests = [
        "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
        "same=compare($m.operation,to=$m.operation,kind=action)",
    ];
    let run = asks(&dir, &requests);
    assert_eq!(run.code, 1, "{}", run.stdout);
    let result = result_json(&dir, &run);
    let m = answer(&result, "m");
    assert_eq!(s(get(m, "status")), "refuted");
    assert!(has(get(m, "outputs"), "operation"));
    assert!(!has(get(m, "outputs"), "map"));
    assert_eq!(s(get(answer(&result, "same"), "status")), "established");
    let examples = arr(get(m, "counterexamples"));
    assert_eq!(examples.len(), 1);
    let data = get(value(&result, &examples[0]), "data");
    let bs = arr(get(data, "bindings"));
    assert_eq!(bs.len(), 4);
    for ((b, name), expected) in bs.iter().zip(["t", "z", "u", "a"]).zip([
        "[]",
        r#"["v","q"]"#,
        "[]",
        r#"["v","p"]"#,
    ]) {
        assert_eq!(s(get(b, "name")), name);
        assert_json(value(&result, get(b, "value")), expected);
    }
    assert_json(value(&result, get(data, "left")), r#""1""#);
    assert_json(value(&result, get(data, "right")), r#""2""#);
}

#[test]
fn local_finite_parameters_preserve_directional_guards_and_missing_values() {
    // target guardがsource guardの適用行を外すと、その行を反例として返す。
    let (dir, vocabulary) = finite_local_parameter_inputs("local-finite-guard-refuted");
    let sg = "when choice=some(true) and mode=2";
    let tg = "when pick=some(true) and level=1";
    std::fs::write(dir.join("l.law"),format!(r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{vocabulary} local here(unitarg:Unit,z:State,choice:Option<Bool>,mode:Fp(3)) {sg} reads if choice=some(true) and mode=2 then z.free else 0;}}
reading After {{{vocabulary} local here(unused:Unit,y:State,pick:Option<Bool>,level:Fp(3)) {tg} reads if pick=some(true) and level=2 then y.free else 0;}}"#)).unwrap();
    let requests = [
        "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
        "same=compare($m.operation,to=$m.operation,kind=action)",
    ];
    let run = asks(&dir, &requests);
    assert_eq!(run.code, 1, "{}", run.stdout);
    let result = result_json(&dir, &run);
    let m = answer(&result, "m");
    assert_eq!(s(get(m, "status")), "refuted");
    assert!(has(get(m, "outputs"), "operation"));
    assert!(!has(get(m, "outputs"), "map"));
    assert_eq!(s(get(answer(&result, "same"), "status")), "established");
    let data = get(value(&result, &arr(get(m, "counterexamples"))[0]), "data");
    let bs = arr(get(data, "bindings"));
    assert_eq!(bs.len(), 4);
    for ((b, name), expected) in bs.iter().zip(["unitarg", "z", "choice", "mode"]).zip([
        "[]",
        r#"["v","p"]"#,
        r#"{"some":true}"#,
        r#""2""#,
    ]) {
        assert_eq!(s(get(b, "name")), name);
        assert_json(value(&result, get(b, "value")), expected);
    }
    assert_json(value(&result, get(data, "left")), "true");
    assert_json(value(&result, get(data, "right")), "false");
}

#[test]
fn unused_numeric_local_parameters_keep_constant_reads_decidable() {
    let (dir, vocabulary) = finite_local_parameter_inputs("unused-number-local");
    std::fs::write(
        dir.join("l.law"),
        format!(
            r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{vocabulary} local here(x:Q) reads 0+0;}}
reading After {{{vocabulary} local here(y:Q) reads 1;}}"#
        ),
    )
    .unwrap();
    let run = asks(
        &dir,
        &[
            "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
            "same=compare($m.operation,to=$m.operation,kind=action)",
            "n=needed($m)",
        ],
    );
    assert_eq!(run.code, 1, "{}", run.stdout);
    let result = result_json(&dir, &run);
    let map = answer(&result, "m");
    assert_eq!(s(get(map, "status")), "refuted");
    assert!(!has(get(map, "outputs"), "map"));
    assert!(
        arr(get(map, "reasons"))
            .iter()
            .all(|r| s(get(r, "code")) != "unsupported_algorithm")
    );
    assert_eq!(s(get(answer(&result, "same"), "status")), "established");
    let plan = value(&result, get(get(answer(&result, "n"), "outputs"), "plan"));
    assert!(arr(get(plan, "blockers")).is_empty());
    let example = get(value(&result, &arr(get(map, "counterexamples"))[0]), "data");
    assert_json(value(&result, get(example, "left")), r#""0""#);
    assert_json(value(&result, get(example, "right")), r#""1""#);
    std::fs::remove_dir_all(dir).unwrap();
}

#[test]
fn local_finite_parameter_extension_keeps_other_domains_unsupported() {
    // 未対応の引数型は同じ分岐を通るので、1型で確かめる。
    let (dir, vocabulary) = finite_local_parameter_inputs("local-finite-outside-tuple-integer");
    std::fs::write(
        dir.join("l.law"),
        format!(
            r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{vocabulary} local here(x:(State,Z)) reads 0+0;}}
reading After {{{vocabulary} local here(x:(State,Z)) reads 0+0;}}"#
        ),
    )
    .unwrap();
    let operand = r#"["Tuple",["Ref","Reservations.State"],"Z"]"#;
    let method = "local_parameter_domain_transport";
    assert_unsupported_map(&dir, method, operand, "reads 0+0");
}

#[test]
fn local_composite_argument_reads_keep_the_checked_full_domain_value_map() {
    // 有限合成型の引数はfinite.rsの列挙だけが型で分かれる。Data型で全域の値写像を確かめる。
    let wire_type = r#"["Data","Reservations.Choice"]"#;
    let (dir, vocabulary) = finite_local_parameter_inputs("local-composite-projection-data");
    std::fs::write(
        dir.join("l.law"),
        format!(
            r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{vocabulary} local here(z:State,choice:Choice,other:Choice) reads choice;}}
reading After {{{vocabulary} local here(y:State,pick:Choice,spare:Choice) reads pick;}}"#
        ),
    )
    .unwrap();
    let requests = [
        "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
        "same=compare($m.operation,to=$m.operation,kind=action)",
        "n=needed($m)",
    ];
    let run = asks(&dir, &requests);
    assert_eq!(run.code, 0, "{}", run.stdout);
    let result = result_json(&dir, &run);
    let m = answer(&result, "m");
    assert_eq!(s(get(m, "status")), "established");
    assert!(has(get(m, "outputs"), "operation"));
    assert_eq!(s(get(answer(&result, "same"), "status")), "established");
    let plan = value(&result, get(get(answer(&result, "n"), "outputs"), "plan"));
    assert!(arr(get(plan, "requirements")).is_empty());
    let map = value(&result, get(get(m, "outputs"), "map"));
    let transport = value(&result, &arr(get(map, "transports"))[0]);
    assert_json(
        get(transport, "parameters"),
        r#"[["z","y"],["choice","pick"],["other","spare"]]"#,
    );
    let clause = &arr(get(transport, "clauses"))[0];
    let values = value(&result, get(clause, "values"));
    assert_json(get(values, "source_type"), wire_type);
    assert_json(get(values, "target_type"), wire_type);
    assert!(arr(get(values, "subjects")).is_empty());
    let args = value(&result, get(clause, "arguments"));
    assert_reference_pairs(
        &result,
        args,
        &[("p", "r"), ("q", "s"), ("r", "r"), ("s", "s")],
    );
    assert_json(
        get(args, "source_type"),
        &format!(r#"["Tuple",["Ref","Reservations.State"],{wire_type},{wire_type}]"#),
    );
    for map in [args, values] {
        for family in [
            "Reservations.Choice",
            "Reservations.Choice.Empty",
            "Reservations.Choice.Full",
        ] {
            assert!(arr(get(map, "declarations")).iter().any(|pair| {
                arr(pair).iter().map(s).collect::<Vec<_>>() == [family, family]
            }));
        }
    }
}

#[test]
fn local_composite_argument_read_guards_use_actual_reference_images() {
    // 非単射の像(p→r, r→r)では、sourceで異なる参照がtargetで等しくなる。
    let (dir, vocabulary) = finite_local_parameter_inputs("local-composite-images");
    std::fs::write(dir.join("l.law"),format!(r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{vocabulary} local here(left:State,choice:Option<Bool>,right:State) when left!=right reads choice;}}
reading After {{{vocabulary} local here(a:State,pick:Option<Bool>,b:State) when a!=b reads pick;}}"#)).unwrap();
    let run = asks(
        &dir,
        &[
            "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
            "same=compare($m.operation,to=$m.operation,kind=action)",
        ],
    );
    assert_eq!(run.code, 1, "{}", run.stdout);
    let result = result_json(&dir, &run);
    let m = answer(&result, "m");
    assert_eq!(s(get(m, "status")), "refuted");
    assert!(has(get(m, "outputs"), "operation"));
    assert!(!has(get(m, "outputs"), "map"));
    assert_eq!(s(get(answer(&result, "same"), "status")), "established");
    let data = get(value(&result, &arr(get(m, "counterexamples"))[0]), "data");
    let bs = arr(get(data, "bindings"));
    assert_eq!(bs.len(), 3);
    for ((b, name), expected) in bs.iter().zip(["left", "choice", "right"]).zip([
        r#"["v","p"]"#,
        r#"{"none":true}"#,
        r#"["v","r"]"#,
    ]) {
        assert_eq!(s(get(b, "name")), name);
        assert_json(value(&result, get(b, "value")), expected);
    }
    assert_json(value(&result, get(data, "left")), "true");
    assert_json(value(&result, get(data, "right")), "false");
}

#[test]
fn local_reference_sets_use_direct_images_without_preserving_cardinality() {
    for (case, sr, tr, code) in [
        ("projection", "members", "chosen", 0),
        ("cardinality-read", "count(members)", "count(chosen)", 1),
    ] {
        let (dir, vocabulary) = finite_local_parameter_inputs(&format!("local-set-ref-{case}"));
        std::fs::write(
            dir.join("l.law"),
            format!(
                r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{vocabulary} local here(left:State,members:Set<State>,take:Bool) reads {sr};}}
reading After {{{vocabulary} local here(right:State,chosen:Set<State>,keep:Bool) reads {tr};}}"#
            ),
        )
        .unwrap();
        let requests = [
            "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
            "same=compare($m.operation,to=$m.operation,kind=action)",
            "n=needed($m)",
        ];
        let run = asks(&dir, &requests);
        assert_eq!(run.code, code, "{case}: {}", run.stdout);
        let result = result_json(&dir, &run);
        let m = answer(&result, "m");
        assert_eq!(
            s(get(m, "status")),
            if code == 0 { "established" } else { "refuted" }
        );
        assert!(has(get(m, "outputs"), "operation"));
        assert_eq!(has(get(m, "outputs"), "map"), code == 0);
        assert_eq!(s(get(answer(&result, "same"), "status")), "established");
        let plan = value(&result, get(get(answer(&result, "n"), "outputs"), "plan"));
        assert!(arr(get(plan, "requirements")).is_empty());
        if code == 1 {
            // 直接像は要素数を保たない: {p,r} は {r} へ写る。
            let data = get(value(&result, &arr(get(m, "counterexamples"))[0]), "data");
            let bindings = arr(get(data, "bindings"));
            assert_eq!(bindings.len(), 3);
            for (binding, name) in bindings.iter().zip(["left", "members", "take"]) {
                assert_eq!(s(get(binding, "name")), name);
            }
            assert_json(value(&result, get(&bindings[0], "value")), r#"["v","p"]"#);
            assert_json(
                value(&result, get(&bindings[1], "value")),
                r#"[["v","p"],["v","r"]]"#,
            );
            assert_json(value(&result, get(&bindings[2], "value")), "false");
            assert_json(value(&result, get(data, "left")), "\"2\"");
            assert_json(value(&result, get(data, "right")), "\"1\"");
        } else {
            let map = value(&result, get(get(m, "outputs"), "map"));
            let transport = value(&result, &arr(get(map, "transports"))[0]);
            assert_json(
                get(transport, "parameters"),
                r#"[["left","right"],["members","chosen"],["take","keep"]]"#,
            );
            let clause = &arr(get(transport, "clauses"))[0];
            let values = value(&result, get(clause, "values"));
            assert_json(
                get(values, "source_type"),
                r#"["Set",["Ref","Reservations.State"]]"#,
            );
            assert_json(
                get(values, "target_type"),
                r#"["Set",["Ref","Reservations.State"]]"#,
            );
            for map in [values, value(&result, get(clause, "arguments"))] {
                assert_reference_pairs(
                    &result,
                    map,
                    &[("p", "r"), ("q", "s"), ("r", "r"), ("s", "s")],
                );
            }
        }
    }
}

#[test]
fn local_reference_data_siblings_use_the_finite_value_map() {
    let (dir, vocabulary) = finite_local_parameter_inputs("local-reference-data-siblings");
    std::fs::write(
        dir.join("l.law"),
        format!(
            r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{vocabulary} local here(x:(State,Choice)) reads x;}}
reading After {{{vocabulary} local here(a:(State,Choice)) reads a;}}"#
        ),
    )
    .unwrap();
    let run = asks(
        &dir,
        &[
            "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
            "same=compare($m.operation,to=$m.operation,kind=action)",
        ],
    );
    assert_eq!(run.code, 0, "{}", run.stdout);
    let result = result_json(&dir, &run);
    let map = value(&result, get(get(answer(&result, "m"), "outputs"), "map"));
    let transport = value(&result, &arr(get(map, "transports"))[0]);
    let clause = &arr(get(transport, "clauses"))[0];
    for map in [
        value(&result, get(clause, "values")),
        value(&result, get(clause, "arguments")),
    ] {
        assert_reference_pairs(
            &result,
            map,
            &[("p", "r"), ("q", "s"), ("r", "r"), ("s", "s")],
        );
    }
    assert_eq!(s(get(answer(&result, "same"), "status")), "established");
}

fn finite_local_map_inputs(name: &str) -> (PathBuf, String) {
    let dir = four_state_inputs(name);
    let old = std::fs::read_to_string(dir.join("d.json")).unwrap();
    let definition = old.replacen("\"declarations\": [", r#""declarations": [{"kind":"entity","name":"Reservations.Key","meaning":"写像の固定キー","parameters":[],"fields":[],"alignments":[]},"#, 1);
    let before = archsig::definition::check_definitions(&[("d", old.as_bytes())]).unwrap();
    let after = archsig::definition::check_definitions(&[("d", definition.as_bytes())]).unwrap();
    let digest = &after.vocabularies()["Reservations"].digest;
    let map = std::fs::read_to_string(dir.join("a.json"))
        .unwrap()
        .replace(&before.vocabularies()["Reservations"].digest, digest)
        .replacen(
            "\"subjects\":[",
            r#""subjects":[{"id":"k","type":"Reservations.Key","origin":"model"},"#,
            1,
        );
    std::fs::write(dir.join("d.json"), definition).unwrap();
    std::fs::write(dir.join("a.json"), map).unwrap();
    (
        dir,
        format!(r#"use vocabulary Reservations version "1" digest "{digest}";"#),
    )
}

#[test]
fn local_map_arguments_preserve_total_images_reads_guards_and_missing() {
    for (case, sr, tr, code) in [
        ("projection", "table", "chosen", 0),
        ("infinite-refuted", "(table,left.free)", "(chosen,right.free+1)", 1),
    ] {
        let (dir, vocabulary) = finite_local_map_inputs(&format!("local-map-{case}"));
        let ty = if case == "projection" {
            "Option<(Map<Key,State>,Bool)>"
        } else {
            "Map<Key,State>"
        };
        std::fs::write(dir.join("l.law"),format!(r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{vocabulary} local here(left:State,table:{ty},take:Bool,key:Key) reads {sr};}}
reading After {{{vocabulary} local here(right:State,chosen:{ty},keep:Bool,which:Key) reads {tr};}}"#)).unwrap();
        let requests = [
            "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
            "same=compare($m.operation,to=$m.operation,kind=action)",
            "n=needed($m)",
        ];
        let run = asks(&dir, &requests);
        assert_eq!(run.code, code, "{case}: {}", run.stdout);
        let result = result_json(&dir, &run);
        let m = answer(&result, "m");
        assert_eq!(
            s(get(m, "status")),
            if code == 0 { "established" } else { "refuted" }
        );
        assert!(has(get(m, "outputs"), "operation"));
        assert_eq!(has(get(m, "outputs"), "map"), code == 0);
        assert_eq!(s(get(answer(&result, "same"), "status")), "established");
        let plan = value(&result, get(get(answer(&result, "n"), "outputs"), "plan"));
        assert!(arr(get(plan, "requirements")).is_empty());
        if code == 1 {
            let data = get(value(&result, &arr(get(m, "counterexamples"))[0]), "data");
            let bindings = arr(get(data, "bindings"));
            assert_eq!(bindings.len(), 4);
            assert_eq!(s(get(&bindings[0], "name")), "left");
            assert_json(value(&result, get(&bindings[0], "value")), r#"["v","p"]"#);
            assert_json(value(&result, get(data, "left")), r#"[[[["v","k"],["v","p"]]],"2"]"#);
            assert_json(value(&result, get(data, "right")), r#"[[[["v","k"],["v","r"]]],"3"]"#);
        } else {
            let map = value(&result, get(get(m, "outputs"), "map"));
            let transport = value(&result, &arr(get(map, "transports"))[0]);
            let clause = &arr(get(transport, "clauses"))[0];
            for map in [
                value(&result, get(clause, "values")),
                value(&result, get(clause, "arguments")),
            ] {
                assert_reference_pairs(
                    &result,
                    map,
                    &[("k", "k"), ("p", "r"), ("q", "s"), ("r", "r"), ("s", "s")],
                );
            }
        }
    }
}

#[test]
fn local_finite_expression_reads_share_identity_value_maps_for_sets() {
    // Setは要素の順序によらず等しい。
    let (dir, vocabulary) = finite_local_parameter_inputs("local-finite-expression-set");
    std::fs::write(
        dir.join("l.law"),
        format!(
            r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{vocabulary} local here(choice:Option<Bool>,take:Bool) reads if take then set<Bool>{{false,true}} else set<Bool>{{}};}}
reading After {{{vocabulary} local here(chosen:Option<Bool>,keep:Bool) reads if keep then set<Bool>{{true,false}} else set<Bool>{{}};}}"#
        ),
    )
    .unwrap();
    let run = asks(
        &dir,
        &[
            "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
        ],
    );
    assert_eq!(run.code, 0, "{}", run.stdout);
    let result = result_json(&dir, &run);
    let map = value(&result, get(get(answer(&result, "m"), "outputs"), "map"));
    let transport = value(&result, &arr(get(map, "transports"))[0]);
    let clause = &arr(get(transport, "clauses"))[0];
    let values = value(&result, get(clause, "values"));
    let wire = r#"["Set","Bool"]"#;
    assert_json(get(values, "source_type"), wire);
    assert_json(get(values, "target_type"), wire);
    assert!(arr(get(values, "subjects")).is_empty());
}

#[test]
fn local_read_type_maps_do_not_require_a_matching_parameter() {
    for (shape, body, empty, different, code) in [
        ("option", "some(left)", "none<State>", false, 0),
        ("set", "set<State>{left}", "set<State>{}", true, 1),
    ] {
        let (dir, vocabulary) = finite_local_parameter_inputs(&format!("read-type-{shape}-{code}"));
        let source_read = format!("if take then {body} else {empty}");
        let target_read = if different {
            empty.to_string()
        } else {
            source_read.clone()
        }
        .replace("left", "right")
        .replace("take", "keep");
        std::fs::write(dir.join("l.law"),format!(r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{vocabulary} local here(left:State,take:Bool) reads {source_read};}}
reading After {{{vocabulary} local here(right:State,keep:Bool) reads {target_read};}}"#)).unwrap();
        let requests = [
            "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
            "same=compare($m.operation,to=$m.operation,kind=action)",
        ];
        let run = asks(&dir, &requests);
        assert_eq!(run.code, code, "{shape}: {}", run.stdout);
        let result = result_json(&dir, &run);
        let m = answer(&result, "m");
        assert!(has(get(m, "outputs"), "operation"));
        assert_eq!(has(get(m, "outputs"), "map"), code == 0);
        assert_eq!(s(get(answer(&result, "same"), "status")), "established");
        if code == 0 {
            let map = value(&result, get(get(m, "outputs"), "map"));
            let transport = value(&result, &arr(get(map, "transports"))[0]);
            let clause = &arr(get(transport, "clauses"))[0];
            let values = value(&result, get(clause, "values"));
            assert_reference_pairs(
                &result,
                values,
                &[("p", "r"), ("q", "s"), ("r", "r"), ("s", "s")],
            );
            let ty = r#"["Option",["Ref","Reservations.State"]]"#;
            assert_json(get(values, "source_type"), ty);
            assert_json(get(values, "target_type"), ty);
        } else {
            let data = get(value(&result, &arr(get(m, "counterexamples"))[0]), "data");
            let bindings = arr(get(data, "bindings"));
            assert_eq!(bindings.len(), 2);
            assert_eq!(s(get(&bindings[0], "name")), "left");
            assert_eq!(s(get(&bindings[1], "name")), "take");
            assert_json(value(&result, get(&bindings[1], "value")), "true");
            assert_ne!(
                value(&result, get(data, "left")).value,
                value(&result, get(data, "right")).value
            );
        }
    }
}

#[test]
fn local_read_type_maps_check_the_whole_map_domain_before_reading_none() {
    // read型のMap域が保てなければ、guardが常に偽でも出力型全体の検査で反証する。
    let (dir, vocabulary) = finite_local_map_inputs("read-type-map-inactive-collision");
    let map = std::fs::read_to_string(dir.join("a.json"))
        .unwrap()
        .lines()
        .filter(|line| !line.contains(r#""id":"p-free""#) && !line.contains(r#""id":"r-free""#))
        .collect::<Vec<_>>()
        .join("\n");
    std::fs::write(dir.join("a.json"), map).unwrap();
    let source = "if left.free>0 then none<Map<State,State>> else none<Map<State,State>>";
    let target = source.replace("left", "right");
    std::fs::write(
        dir.join("l.law"),
        format!(
            r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{vocabulary} local here(left:State) when false reads {source};}}
reading After {{{vocabulary} local here(right:State) reads {target};}}"#
        ),
    )
    .unwrap();
    let run = asks(
        &dir,
        &[
            "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
        ],
    );
    assert_eq!(run.code, 1, "{}", run.stdout);
    let result = result_json(&dir, &run);
    let m = answer(&result, "m");
    assert!(has(get(m, "outputs"), "operation"));
    assert!(!has(get(m, "outputs"), "map"));
    assert!(!has(m, "counterexamples"));
    let reasons = arr(get(m, "reasons"));
    assert!(
        reasons
            .iter()
            .any(|r| s(get(r, "code")) == "condition_failed")
    );
    assert!(!reasons.iter().any(|r| matches!(
        s(get(r, "code")),
        "missing_observation" | "unsupported_algorithm"
    )));
}
#[test]
fn local_read_type_maps_handle_empty_argument_products() {
    let (dir, vocabulary) = finite_local_parameter_inputs("read-type-no-parameters");
    std::fs::write(
        dir.join("l.law"),
        format!(
            r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{vocabulary} local here() reads none<State>;}}
reading After {{{vocabulary} local here() reads none<State>;}}"#
        ),
    )
    .unwrap();
    let run = asks(
        &dir,
        &[
            "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
        ],
    );
    assert_eq!(run.code, 0, "{}", run.stdout);
    let result = result_json(&dir, &run);
    let map = value(&result, get(get(answer(&result, "m"), "outputs"), "map"));
    let transport = value(&result, &arr(get(map, "transports"))[0]);
    let values = value(&result, get(&arr(get(transport, "clauses"))[0], "values"));
    assert_json(
        get(values, "source_type"),
        r#"["Option",["Ref","Reservations.State"]]"#,
    );
    assert_reference_pairs(
        &result,
        values,
        &[("p", "r"), ("q", "s"), ("r", "r"), ("s", "s")],
    );
}

#[test]
fn local_read_type_maps_keep_the_operation_when_read_types_disagree() {
    // 型の不一致は欠測readより先に反証する。
    let body = "if left.free>0 then some(left) else none<State>";
    let (dir, vocabulary) = finite_local_parameter_inputs("read-type-mismatch-missing");
    let map = std::fs::read_to_string(dir.join("a.json"))
        .unwrap()
        .lines()
        .filter(|line| !line.contains(r#""id":"p-free""#) && !line.contains(r#""id":"r-free""#))
        .collect::<Vec<_>>()
        .join("\n");
    std::fs::write(dir.join("a.json"), map).unwrap();
    std::fs::write(
        dir.join("l.law"),
        format!(
            r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{vocabulary} local here(left:State,take:Bool) reads {body};}}
reading After {{{vocabulary} local here(right:State,keep:Bool) reads true;}}"#
        ),
    )
    .unwrap();
    let requests = [
        "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
        "same=compare($m.operation,to=$m.operation,kind=action)",
        "n=needed($m)",
    ];
    let run = asks(&dir, &requests);
    assert_eq!(run.code, 1, "{}", run.stdout);
    let result = result_json(&dir, &run);
    let m = answer(&result, "m");
    assert_eq!(s(get(m, "status")), "refuted");
    assert!(has(get(m, "outputs"), "operation"));
    assert!(!has(get(m, "outputs"), "map"));
    assert!(!has(m, "counterexamples"));
    let law = std::fs::read(dir.join("l.law")).unwrap();
    let condition = value(&result, get(get(m, "outputs"), "proposition"));
    for expected in [body, "true"] {
        assert!(arr(get(condition, "operands")).iter().any(|r| {
            let expression = value(&result, r);
            if !has(expression, "kind")
                || s(get(expression, "kind")) != "source"
                || !has(expression, "location")
            {
                return false;
            }
            let span = arr(get(get(expression, "location"), "span"));
            &law[num(&span[0]) as usize..num(&span[1]) as usize] == expected.as_bytes()
        }));
    }
    let reasons = arr(get(m, "reasons"));
    assert!(
        reasons
            .iter()
            .any(|r| s(get(r, "code")) == "condition_failed")
    );
    assert!(!reasons.iter().any(|r| matches!(
        s(get(r, "code")),
        "missing_observation" | "unsupported_algorithm"
    )));
    assert_eq!(s(get(answer(&result, "same"), "status")), "established");
    let plan = value(&result, get(get(answer(&result, "n"), "outputs"), "plan"));
    assert!(arr(get(plan, "requirements")).is_empty());
}

#[test]
fn local_infinite_compound_reads_use_identity_on_actual_values() {
    // 型ごとの差は値の等値だけ。Setの順序非依存(保存)とListの順序(反証)を確かめる。
    for (shape, body, alternate, expected, wire, case, code) in [
        (
            "set",
            "set<Z>{s.free,0}",
            "set<Z>{0,s.free,1}",
            r#"["2","0"]"#,
            r#"["Set","Z"]"#,
            "preserved",
            0,
        ),
        (
            "list",
            "list<Z>[s.free,0]",
            "list<Z>[0,s.free]",
            r#"["2","0"]"#,
            r#"["List","Z"]"#,
            "refuted",
            1,
        ),
    ] {
        let (dir, vocabulary) =
            finite_local_parameter_inputs(&format!("local-infinite-{shape}-{case}"));
        let read = format!("if take then {body} else {alternate}");
        let target = if case == "refuted" {
            alternate.to_owned()
        } else {
            read.clone()
        }
        .replace("s.", "t.")
        .replace("take", "keep")
        .replace("set<Z>{t.free,0}", "set<Z>{0,t.free}");
        std::fs::write(
            dir.join("l.law"),
            format!(
                r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{vocabulary} local here(s:State,take:Bool) reads {read};}}
reading After {{{vocabulary} local here(t:State,keep:Bool) reads {target};}}"#
            ),
        )
        .unwrap();
        let requests = [
            "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
            "same=compare($m.operation,to=$m.operation,kind=action)",
        ];
        let run = asks(&dir, &requests);
        assert_eq!(run.code, code, "{shape}/{case}: {}", run.stdout);
        let result = result_json(&dir, &run);
        let m = answer(&result, "m");
        assert_eq!(
            s(get(m, "status")),
            if code == 0 { "established" } else { "refuted" }
        );
        assert!(has(get(m, "outputs"), "operation"));
        assert_eq!(has(get(m, "outputs"), "map"), code == 0);
        assert_eq!(s(get(answer(&result, "same"), "status")), "established");
        if code == 1 {
            let data = get(value(&result, &arr(get(m, "counterexamples"))[0]), "data");
            let bindings = arr(get(data, "bindings"));
            assert_eq!(s(get(&bindings[0], "name")), "s");
            assert_json(value(&result, get(&bindings[0], "value")), r#"["v","p"]"#);
            assert_json(value(&result, get(&bindings[1], "value")), "true");
            assert_json(value(&result, get(data, "left")), expected);
        } else {
            let map = value(&result, get(get(m, "outputs"), "map"));
            let transport = value(&result, &arr(get(map, "transports"))[0]);
            let values = value(&result, get(&arr(get(transport, "clauses"))[0], "values"));
            assert_json(get(values, "source_type"), wire);
            assert_json(get(values, "target_type"), wire);
            assert!(arr(get(values, "subjects")).is_empty());
        }
    }
}

#[test]
fn local_reference_product_reads_extend_total_reference_maps_with_scalar_identity() {
    // Listの参照像は順序と重複を保つ(保存)。scalar成分の変化は参照像と別に反証する。
    for (shape, body, alternate, different, wire, witness, case, code) in [
        (
            "list",
            "list<(State,Z)>[(left,left.free),(other,other.free),(left,left.free)]",
            "list<(State,Z)>[]",
            "list<(State,Z)>[(left,left.free+1)]",
            r#"["List",["Tuple",["Ref","Reservations.State"],"Z"]]"#,
            r#"[[["v","p"],"2"],[["v","p"],"2"],[["v","p"],"2"]]"#,
            "preserved",
            0,
        ),
        (
            "tuple",
            "(left,left.free)",
            "(other,other.free)",
            "(left,left.free+1)",
            r#"["Tuple",["Ref","Reservations.State"],"Z"]"#,
            r#"[["v","p"],"2"]"#,
            "numeric-refuted",
            1,
        ),
    ] {
        let (dir, vocabulary) =
            finite_local_parameter_inputs(&format!("local-reference-product-{shape}-{case}"));
        let read = format!("if take then {body} else {alternate}");
        let target = if case == "numeric-refuted" {
            format!("if take then {different} else {alternate}")
        } else {
            read.clone()
        }
        .replace("left", "right")
        .replace("other", "spare")
        .replace("take", "keep");
        std::fs::write(dir.join("l.law"),format!(r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{vocabulary} local here(left:State,other:State,take:Bool) reads {read};}}
reading After {{{vocabulary} local here(right:State,spare:State,keep:Bool) reads {target};}}"#)).unwrap();
        let requests = [
            "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
            "same=compare($m.operation,to=$m.operation,kind=action)",
        ];
        let run = asks(&dir, &requests);
        assert_eq!(run.code, code, "{shape}/{case}: {}", run.stdout);
        let result = result_json(&dir, &run);
        let m = answer(&result, "m");
        assert_eq!(
            s(get(m, "status")),
            if code == 0 { "established" } else { "refuted" }
        );
        assert!(has(get(m, "outputs"), "operation"));
        assert_eq!(has(get(m, "outputs"), "map"), code == 0);
        assert_eq!(s(get(answer(&result, "same"), "status")), "established");
        if code == 1 {
            let data = get(value(&result, &arr(get(m, "counterexamples"))[0]), "data");
            let bindings = arr(get(data, "bindings"));
            assert_eq!(bindings.len(), 3);
            assert_eq!(s(get(&bindings[0], "name")), "left");
            assert_json(value(&result, get(&bindings[0], "value")), r#"["v","p"]"#);
            assert_json(value(&result, get(&bindings[1], "value")), r#"["v","p"]"#);
            assert_json(value(&result, get(&bindings[2], "value")), "true");
            assert_json(value(&result, get(data, "left")), witness);
        } else {
            let map = value(&result, get(get(m, "outputs"), "map"));
            let transport = value(&result, &arr(get(map, "transports"))[0]);
            let values = value(&result, get(&arr(get(transport, "clauses"))[0], "values"));
            assert_json(get(values, "source_type"), wire);
            assert_json(get(values, "target_type"), wire);
            assert_reference_pairs(
                &result,
                values,
                &[("p", "r"), ("q", "s"), ("r", "r"), ("s", "s")],
            );
        }
    }
}

#[test]
fn local_reference_products_check_unread_reference_values_before_false_guards() {
    for (case, external, mismatch, empty) in [
        ("total", false, false, "none<@>"),
        ("outside", true, false, "none<@>"),
        ("mismatch", false, true, "none<@>"),
        ("data-payload", false, true, "Bridge.Choice.Empty"),
    ] {
        let dir = workdir(&format!("local-reference-product-domain-{case}"));
        let left = include_bytes!("fixtures/configuration-map-left.atoms.json");
        let right = include_bytes!("fixtures/configuration-map-right.atoms.json");
        let checked =
            archsig::definition::check_definitions(&[("left", left), ("right", right)]).unwrap();
        let ld = &checked.vocabularies()["Left"].digest;
        let rd = &checked.vocabularies()["Right"].digest;
        let bridge = include_str!("fixtures/configuration-map-bridge.atoms.json")
            .replace("@LEFT_DIGEST@", ld)
            .replace("@RIGHT_DIGEST@", rd);
        let bridge = if case.starts_with("data-payload") {
            bridge.replacen(r#""declarations": ["#, r#""declarations": [{"kind":"data","name":"Bridge.Choice","meaning":"参照を持つ選択","constructors":[{"name":"Empty","arguments":[],"meaning":"空"},{"name":"Full","arguments":[["Ref","Left.Child"],"Z",["Data","Bridge.Choice"]],"meaning":"再帰payload"}]},"#, 1)
        } else { bridge };
        let checked = archsig::definition::check_definitions(&[
            ("left", left),
            ("right", right),
            ("bridge", bridge.as_bytes()),
        ])
        .unwrap();
        let bd = &checked.vocabularies()["Bridge"].digest;
        let imports = format!(
            r#"use vocabulary Left version "1" digest "{ld}"; use vocabulary Right version "1" digest "{rd}"; use vocabulary Bridge version "1" digest "{bd}";"#
        );
        let source_empty = empty.replace('@', "(Left.Child,Z)");
        let target_empty = empty.replace(
            '@',
            if mismatch {
                "(Right.Child,Q)"
            } else {
                "(Right.Child,Z)"
            },
        );
        let source_read = format!("if take then {source_empty} else {source_empty}");
        let target_read = format!("if keep then {target_empty} else {target_empty}");
        let law = format!(
            r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{imports} local here(take:Bool) when false reads {source_read};}}
reading After {{{imports} local here(keep:Bool) when false reads {target_read};}}"#
        );
        let mut map = include_str!("fixtures/reference-type.archmap.json")
            .replace("@LEFT_DIGEST@", ld)
            .replace("@RIGHT_DIGEST@", rd)
            .replace("@BRIDGE_DIGEST@", bd);
        if external {
            map = map
                .replace(
                    r#""subjects": ["#,
                    r#""subjects": [
{"id":"x","type":"Left.Root","origin":"model"},
{"id":"h","type":"Left.Child","origin":"model"},"#,
                )
                .replace(
                    r#""atoms": ["#,
                    r#""atoms": [
{"id":"x-count","subject":"x","field":"Left.Root.count","value":"0","origin":"model"},
{"id":"h-owner","subject":"h","field":"Left.Child.owner","value":["v","x"],"origin":"model"},
{"id":"h-count","subject":"h","field":"Left.Child.count","value":"0","origin":"model"},"#,
                );
        }
        for (name, bytes) in [
            ("left.json", left.as_slice()),
            ("right.json", right.as_slice()),
            ("bridge.json", bridge.as_bytes()),
            ("l.law", law.as_bytes()),
            ("a.json", map.as_bytes()),
        ] {
            std::fs::write(dir.join(name), bytes).unwrap();
        }
        let requests = [
            "m=map(Bridge.Move,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
            "same=compare($m.operation,to=$m.operation,kind=action)",
            "n=needed($m)",
        ];
        let mut args = vec![
            "run",
            "--atom-definition",
            "left.json",
            "--atom-definition",
            "right.json",
            "--atom-definition",
            "bridge.json",
            "--law",
            "l.law",
            "--archmap",
            "a.json",
            "--out",
            "out",
        ];
        for request in &requests {
            args.extend(["--ask", request]);
        }
        let run = cli::run(&dir, &args);
        assert_eq!(
            run.code,
            i32::from(external || mismatch),
            "{case}: {}",
            run.stdout
        );
        let result = result_json(&dir, &run);
        let m = answer(&result, "m");
        assert_eq!(
            s(get(m, "status")),
            if external || mismatch {
                "refuted"
            } else {
                "established"
            }
        );
        assert!(has(get(m, "outputs"), "operation"));
        assert_eq!(has(get(m, "outputs"), "map"), !external && !mismatch);
        assert!(!has(m, "counterexamples"));
        assert_eq!(s(get(answer(&result, "same"), "status")), "established");
        let plan = value(&result, get(get(answer(&result, "n"), "outputs"), "plan"));
        assert!(arr(get(plan, "requirements")).is_empty());
        if external || mismatch {
            assert!(
                arr(get(m, "reasons"))
                    .iter()
                    .any(|r| s(get(r, "code")) == "condition_failed")
            );
            assert!(
                !arr(get(m, "reasons"))
                    .iter()
                    .any(|r| matches!(s(get(r, "code")), "missing" | "unsupported_algorithm"))
            );
            let condition = value(&result, get(get(m, "outputs"), "proposition"));
            if external {
                assert!(
                    arr(get(condition, "operands"))
                        .iter()
                        .any(|r| value(&result, r).value
                            == archsig::json::parse(br#"["v","h"]"#).unwrap().value)
                );
            } else if case.starts_with("data-payload") {
                let domains: Vec<_> = arr(get(condition, "operands")).iter()
                    .map(|r| value(&result, r))
                    .filter(|v| has(v, "kind") && s(get(v, "kind")) == "type")
                    .collect();
                for ty in [r#"["Ref","Left.Child"]"#, r#"["Ref","Right.Child"]"#] {
                    let expected = archsig::json::parse(ty.as_bytes()).unwrap();
                    assert!(domains.iter().any(|v| get(v, "type").value == expected.value));
                }
            } else {
                for text in [&source_read, &target_read] {
                    assert!(arr(get(condition, "operands")).iter().any(|r| {
                        let expression = value(&result, r);
                        if !has(expression, "kind")
                            || s(get(expression, "kind")) != "source"
                            || !has(expression, "location")
                        {
                            return false;
                        }
                        let span = arr(get(get(expression, "location"), "span"));
                        &law.as_bytes()[num(&span[0]) as usize..num(&span[1]) as usize]
                            == text.as_bytes()
                    }));
                }
            }
        }
    }
}

fn without_reserve_instances(map: &str) -> String {
    map.lines()
        .filter(|l| {
            !l.contains(r#""type":"Reservations.Reserve""#)
                && !l.contains(r#""subject":"e""#)
                && !l.contains(r#""subject":"f""#)
        })
        .collect::<Vec<_>>()
        .join("\n")
        .replace(r#"[[["v","e"],["v","f"]]]"#, "[]")
}

#[test]
fn local_direct_compound_fields_share_evaluation_transport_and_missing() {
    // 直接field readとifで包んだ一般readは同じ比較を通る。Map fieldはここだけで確かめる。
    for (shape, wire, case, code, general) in [
        (
            "tuple",
            r#"["Tuple",["Ref","Reservations.State"],"Z","Bool",["Option","Bool"]]"#,
            "refuted",
            1,
            true,
        ),
        (
            "map",
            r#"["Map",["Ref","Reservations.Key"],["Ref","Reservations.State"]]"#,
            "preserved",
            0,
            false,
        ),
    ] {
        let name = format!("direct-compound-{shape}-{case}-{general}");
        let (dir, _) = if shape == "map" {
            finite_local_map_inputs(&name)
        } else {
            finite_local_parameter_inputs(&name)
        };
        let old = std::fs::read_to_string(dir.join("d.json")).unwrap();
        let definition=old.replace(r#"{"name": "free", "type": "Z""#,
            &format!(r#"{{"name":"box","type":{wire},"meaning":"複合値"}},{{"name":"alternate","type":{wire},"meaning":"別の複合値"}},{{"name": "free", "type": "Z""#));
        let before =
            archsig::definition::check_definitions(&[("d", old.as_bytes())]).unwrap();
        let checked =
            archsig::definition::check_definitions(&[("d", definition.as_bytes())])
                .unwrap();
        let digest = &checked.vocabularies()["Reservations"].digest;
        let mut map = std::fs::read_to_string(dir.join("a.json"))
            .unwrap()
            .replace(&before.vocabularies()["Reservations"].digest, digest);
        let mut atoms = String::new();
        for (subject, peer) in [("p", "q"), ("q", "p"), ("r", "s"), ("s", "r")] {
            let r = format!(r#"["v","{subject}"]"#);
            let other = format!(r#"["v","{peer}"]"#);
            let (value, alternate) = if shape == "tuple" {
                (
                    format!(r#"[{r},"0",false,{{"none":true}}]"#),
                    format!(r#"[{r},"1",false,{{"none":true}}]"#),
                )
            } else {
                (
                    format!(r#"[[["v","k"],{r}]]"#),
                    format!(r#"[[["v","k"],{other}]]"#),
                )
            };
            for (field, value) in [("box", value), ("alternate", alternate)] {
                atoms.push_str(&format!(r#"{{"id":"{subject}-{field}","subject":"{subject}","field":"Reservations.State.{field}","value":{value},"origin":"model"}},
"#));
            }
        }
        map = map.replacen("\"atoms\":[", &format!("\"atoms\":[\n{atoms}"), 1);

        // 追加fieldの移送だけを検査し、別の内部Reserve作用を課さない。
        map = without_reserve_instances(&map);
        let source_read = if general {
            "if take then left.box else left.box"
        } else {
            "left.box"
        };
        let target = if case == "refuted" {
            "right.alternate"
        } else {
            "right.box"
        };
        let target_read = if general {
            format!("if keep then {target} else {target}")
        } else {
            format!("({target})")
        };
        let vocabulary =
            format!(r#"use vocabulary Reservations version "1" digest "{digest}";"#);
        let law = format!(
            r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{vocabulary} local here(left:State,other:State,take:Bool) reads {source_read};}}
reading After {{{vocabulary} local here(right:State,spare:State,keep:Bool) reads {target_read};}}"#
        );
        std::fs::write(dir.join("d.json"), definition).unwrap();
        std::fs::write(dir.join("a.json"), map).unwrap();
        std::fs::write(dir.join("l.law"), law).unwrap();
        let requests = [
            "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
            "same=compare($m.operation,to=$m.operation,kind=action)",
        ];
        let run = asks(&dir, &requests);
        assert_eq!(run.code, code, "{shape}/{case}/{general}: {}", run.stdout);
        let result = result_json(&dir, &run);
        let m = answer(&result, "m");
        assert_eq!(
            s(get(m, "status")),
            if code == 0 { "established" } else { "refuted" }
        );
        assert!(
            has(get(m, "outputs"), "operation"),
            "{shape}/{case}/{general}: {}",
            run.stdout
        );
        assert_eq!(has(get(m, "outputs"), "map"), code == 0);
        assert_eq!(s(get(answer(&result, "same"), "status")), "established");
        if code == 1 {
            let data = get(value(&result, &arr(get(m, "counterexamples"))[0]), "data");
            let bindings = arr(get(data, "bindings"));
            assert_eq!(bindings.len(), 3);
            assert_json(value(&result, get(&bindings[0], "value")), r#"["v","p"]"#);
            assert_json(value(&result, get(&bindings[2], "value")), "false");
            assert_json(
                value(&result, get(data, "left")),
                r#"[["v","p"],"0",false,{"none":true}]"#,
            );
            assert_json(
                value(&result, get(data, "right")),
                r#"[["v","r"],"1",false,{"none":true}]"#,
            );
        } else {
            let mapped = value(&result, get(get(m, "outputs"), "map"));
            let transport = value(&result, &arr(get(mapped, "transports"))[0]);
            let values = value(&result, get(&arr(get(transport, "clauses"))[0], "values"));
            assert_json(get(values, "source_type"), wire);
            assert_reference_pairs(
                &result,
                values,
                &[("k", "k"), ("p", "r"), ("q", "s"), ("r", "r"), ("s", "s")],
            );
        }
    }
}

#[test]
fn local_integer_arguments_preserve_the_entire_source_guard_fiber() {
    for (name, sg, tg, sr, tr, code) in [
        ("broader", " when 2*n=34", "", "n", "17", 0),
        ("kernel-read", " when n+k=17", "", "n", "17", 1),
    ] {
        let (dir, vocabulary) = finite_local_parameter_inputs(&format!("local-integer-{name}"));
        std::fs::write(
            dir.join("l.law"),
            format!(
                r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{vocabulary} local here(n:Z,s:State,flag:Bool,k:Z){sg} reads {sr};}}
reading After {{{vocabulary} local here(m:Z,t:State,choice:Bool,j:Z){tg} reads {tr};}}"#
            ),
        )
        .unwrap();
        let requests = [
            "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
            "same=compare($m.operation,to=$m.operation,kind=action)",
        ];
        let run = asks(&dir, &requests);
        assert_eq!(run.code, code, "{name}: {}", run.stdout);
        let result = result_json(&dir, &run);
        let m = answer(&result, "m");
        assert_eq!(
            s(get(m, "status")),
            if code == 0 { "established" } else { "refuted" },
            "{name}"
        );
        assert!(has(get(m, "outputs"), "operation"));
        assert_eq!(has(get(m, "outputs"), "map"), code == 0);
        assert_eq!(s(get(answer(&result, "same"), "status")), "established");
        if code == 1 {
            let examples = arr(get(m, "counterexamples"));
            assert_eq!(examples.len(), 1, "{name}");
            let data = get(value(&result, &examples[0]), "data");
            let bindings = arr(get(data, "bindings"));
            assert_eq!(bindings.len(), 4);
            for (binding, name) in bindings.iter().zip(["n", "s", "flag", "k"]) {
                assert_eq!(s(get(binding, "name")), name);
            }
            let n: i64 = s(value(&result, get(&bindings[0], "value")))
                .parse()
                .unwrap();
            let k: i64 = s(value(&result, get(&bindings[3], "value")))
                .parse()
                .unwrap();
            assert_eq!(n + k, 17);
            assert_ne!(
                value(&result, get(data, "left")).value,
                value(&result, get(data, "right")).value
            );
        }
    }
}

#[test]
fn local_integer_missing_and_unsupported_conditions_remain_undetermined() {
    // 欠測(要求あり)と未対応(要求なし)は、どちらも反証にせず未決にする。
    for (name, sg, tg, sr, tr, missing, code) in [
        ("source-guard", " when n=s.free", "", "n", "m", true, 2),
        ("nonlinear-guard", " when n*n=1", "", "n", "m", false, 2),
    ] {
        let (dir, vocabulary) =
            finite_local_parameter_inputs(&format!("local-integer-unknown-{name}"));
        if missing {
            let map = std::fs::read_to_string(dir.join("a.json"))
                .unwrap()
                .lines()
                .filter(|line| !line.contains(r#""field":"Reservations.State.free""#))
                .collect::<Vec<_>>()
                .join("\n");
            std::fs::write(dir.join("a.json"), map).unwrap();
        }
        std::fs::write(
            dir.join("l.law"),
            format!(
                r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{vocabulary} local here(s:State,n:Z){sg} reads {sr};}}
reading After {{{vocabulary} local here(t:State,m:Z){tg} reads {tr};}}"#
            ),
        )
        .unwrap();
        let requests = [
            "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
            "same=compare($m.operation,to=$m.operation,kind=action)",
            "n=needed($m)",
        ];
        let run = asks(&dir, &requests);
        assert_eq!(run.code, code, "{name}: {}", run.stdout);
        let result = result_json(&dir, &run);
        let m = answer(&result, "m");
        assert_eq!(
            s(get(m, "status")),
            if code == 0 {
                "established"
            } else {
                "undetermined"
            },
            "{name}"
        );
        assert!(!has(m, "counterexamples") || arr(get(m, "counterexamples")).is_empty());
        assert!(has(get(m, "outputs"), "operation"));
        assert_eq!(has(get(m, "outputs"), "map"), code == 0);
        assert_eq!(s(get(answer(&result, "same"), "status")), "established");
        if missing && code == 2 {
            let plan = value(&result, get(get(answer(&result, "n"), "outputs"), "plan"));
            assert!(
                arr(get(plan, "requirements"))
                    .iter()
                    .any(|r| { s(get(get(r, "field"), "field")) == "Reservations.State.free" }),
                "{name}"
            );
        }
    }
}

#[test]
fn local_integer_only_arguments_keep_full_domains_and_actual_counterexamples() {
    let (dir, vocabulary) = finite_local_parameter_inputs("local-integer-only-different");
    std::fs::write(
        dir.join("l.law"),
        format!(
            r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{vocabulary} local here(n:Z) reads n;}} reading After {{{vocabulary} local here(m:Z) reads m+1;}}"#
        ),
    )
    .unwrap();
    let run = asks(
        &dir,
        &[
            "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
            "n=needed($m)",
        ],
    );
    assert_eq!(run.code, 1, "{}", run.stdout);
    let result = result_json(&dir, &run);
    let m = answer(&result, "m");
    assert_eq!(s(get(m, "status")), "refuted");
    let examples = arr(get(m, "counterexamples"));
    assert_eq!(examples.len(), 1);
    let data = get(value(&result, &examples[0]), "data");
    assert_eq!(arr(get(data, "bindings")).len(), 1);
    assert_json(value(&result, get(data, "left")), r#""0""#);
    assert_json(value(&result, get(data, "right")), r#""1""#);
}

fn rational_local_parameter_inputs(name: &str, missing: bool) -> (PathBuf, String) {
    use crate::common::architecture_environment as fixture;
    use archsig::canonical::Json;
    let (dir, _) = finite_local_parameter_inputs(name);
    let old = std::fs::read_to_string(dir.join("d.json")).unwrap();
    let definition = old.replace(
        r#""name": "free", "type": "Z""#,
        r#""name": "free", "type": "Q""#,
    );
    assert_ne!(old, definition);
    let before = archsig::definition::check_definitions(&[("d", old.as_bytes())]).unwrap();
    let after = archsig::definition::check_definitions(&[("d", definition.as_bytes())]).unwrap();
    let digest = &after.vocabularies()["Reservations"].digest;
    let text = std::fs::read_to_string(dir.join("a.json"))
        .unwrap()
        .replace(&before.vocabularies()["Reservations"].digest, digest);
    let mut map = fixture::owned(&archsig::json::parse(text.as_bytes()).unwrap());
    let atoms = fixture::atoms(&mut map);
    atoms.retain(|atom| !missing || !matches!(atom,Json::Obj(a) if matches!(a.get("field"),Some(Json::Str(field)) if field=="Reservations.State.free")));
    for atom in atoms {
        let Json::Obj(a) = atom else { panic!("atom") };
        if matches!(a.get("field"),Some(Json::Str(field)) if field=="Reservations.State.free") {
            let numerator = a["value"].clone();
            a.insert("value".into(), Json::Arr(vec![numerator, Json::str("3")]));
        }
    }
    std::fs::write(dir.join("d.json"), definition).unwrap();
    std::fs::write(dir.join("a.json"), map.canonical()).unwrap();
    (
        dir,
        format!(r#"use vocabulary Reservations version "1" digest "{digest}";"#),
    )
}

#[test]
fn local_rational_arguments_use_the_complete_rational_guard_fiber() {
    for (name, sg, tg, sr, tr, code) in [
        ("broader", " when 2*q=1", "", "q", "rat(1,2)", 0),
        (
            "kernel-read",
            " when 2*q+r=rat(1,2)",
            "",
            "q",
            "rat(1,4)",
            1,
        ),
    ] {
        let (dir, vocabulary) =
            rational_local_parameter_inputs(&format!("local-q-fiber-{name}"), false);
        std::fs::write(
            dir.join("l.law"),
            format!(
                r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{vocabulary} local here(q:Q,s:State,take:Bool,r:Q){sg} reads {sr};}}
reading After {{{vocabulary} local here(y:Q,t:State,keep:Bool,z:Q){tg} reads {tr};}}"#
            ),
        )
        .unwrap();
        let requests = [
            "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
            "same=compare($m.operation,to=$m.operation,kind=action)",
        ];
        let run = asks(&dir, &requests);
        assert_eq!(run.code, code, "{name}: {}", run.stdout);
        let result = result_json(&dir, &run);
        let m = answer(&result, "m");
        assert_eq!(
            s(get(m, "status")),
            if code == 0 { "established" } else { "refuted" }
        );
        assert!(has(get(m, "outputs"), "operation"));
        assert_eq!(has(get(m, "outputs"), "map"), code == 0);
        assert_eq!(s(get(answer(&result, "same"), "status")), "established");
        if code == 0 {
            let map = value(&result, get(get(m, "outputs"), "map"));
            let transport = value(&result, &arr(get(map, "transports"))[0]);
            let clause = &arr(get(transport, "clauses"))[0];
            let arguments = value(&result, get(clause, "arguments"));
            assert_json(
                get(arguments, "source_type"),
                r#"["Tuple","Q",["Ref","Reservations.State"],"Bool","Q"]"#,
            );
            let values = value(&result, get(clause, "values"));
            assert_json(get(values, "source_type"), r#""Q""#);
        } else {
            let examples = arr(get(m, "counterexamples"));
            assert_eq!(examples.len(), 1);
            let data = get(value(&result, &examples[0]), "data");
            let bindings = arr(get(data, "bindings"));
            assert_eq!(bindings.len(), 4);
            for (b, name) in bindings.iter().zip(["q", "s", "take", "r"]) {
                assert_eq!(s(get(b, "name")), name);
            }
            // 反例は source guard の有理fiber 2q+r=1/2 の上にある。
            let q = arr(value(&result, get(&bindings[0], "value")));
            let r = arr(value(&result, get(&bindings[3], "value")));
            let (qn, qd, rn, rd): (i64, i64, i64, i64) = (
                s(&q[0]).parse().unwrap(),
                s(&q[1]).parse().unwrap(),
                s(&r[0]).parse().unwrap(),
                s(&r[1]).parse().unwrap(),
            );
            assert_eq!(2 * (2 * qn * rd + rn * qd), qd * rd);
            assert_ne!(
                value(&result, get(data, "left")).value,
                value(&result, get(data, "right")).value
            );
        }
    }
}

#[test]
fn local_rational_only_arguments_keep_fraction_witnesses() {
    let (dir, vocabulary) = rational_local_parameter_inputs("local-q-only-fraction", false);
    std::fs::write(
        dir.join("l.law"),
        format!(
            r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{vocabulary} local here(q:Q) when 2*q=1 reads q;}} reading After {{{vocabulary} local here(y:Q) reads rat(0,1);}}"#
        ),
    )
    .unwrap();
    let run = asks(
        &dir,
        &[
            "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
            "n=needed($m)",
        ],
    );
    assert_eq!(run.code, 1, "{}", run.stdout);
    let result = result_json(&dir, &run);
    let m = answer(&result, "m");
    assert_eq!(s(get(m, "status")), "refuted");
    let examples = arr(get(m, "counterexamples"));
    assert_eq!(examples.len(), 1);
    let data = get(value(&result, &examples[0]), "data");
    let bindings = arr(get(data, "bindings"));
    assert_eq!(bindings.len(), 1);
    assert_json(value(&result, get(&bindings[0], "value")), r#"["1","2"]"#);
    assert_json(value(&result, get(data, "left")), r#"["1","2"]"#);
    assert_json(value(&result, get(data, "right")), r#"["0","1"]"#);
}

#[test]
fn local_mixed_numeric_guards_on_either_side_are_unsupported_with_a_reason() {
    // Z/Qを混ぜた引数のguard。target側のZのguardと、source側のQのguardの代表。
    for (params, source_guard, target_guard) in [
        ("q:Q,n:Z", "", " when n=0"),
        ("n:Z,q:Q", " when 2*q=1", ""),
    ] {
        let (dir, vocabulary) =
            rational_local_parameter_inputs(&format!("local-q-mixed-{}", params.starts_with('n')), false);
        std::fs::write(
            dir.join("l.law"),
            format!(
                r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{vocabulary} local here({params}){source_guard} reads q;}}
reading After {{{vocabulary} local here({params}){target_guard} reads q;}}"#
            ),
        )
        .unwrap();
        let run = asks(
            &dir,
            &["m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)"],
        );
        assert_eq!(run.code, 2, "{params}: {}", run.stdout);
        let result = result_json(&dir, &run);
        let m = answer(&result, "m");
        assert_eq!(s(get(m, "status")), "undetermined");
        assert!(
            arr(get(m, "reasons"))
                .iter()
                .any(|r| s(get(r, "code")) == "unsupported_algorithm")
        );
    }
}

#[test]
fn local_independent_mixed_numbers_keep_types_order_and_actual_witnesses() {
    for (reverse, name, left, right, code) in [
        (true, "both", "q,n+1", "y,m+1", 0),
        (false, "z-witness", "n", "0", 1),
        (true, "q-witness", "q", "rat(0,1)", 1),
    ] {
        let (dir, vocabulary) =
            rational_local_parameter_inputs(&format!("local-mixed-{reverse}-{name}"), false);
        let (sp, tp, names, types) = if reverse {
            (
                "q:Q,take:Bool,n:Z",
                "y:Q,keep:Bool,m:Z",
                ["q", "take", "n"],
                r#"["Tuple","Q","Bool","Z"]"#,
            )
        } else {
            (
                "n:Z,take:Bool,q:Q",
                "m:Z,keep:Bool,y:Q",
                ["n", "take", "q"],
                r#"["Tuple","Z","Bool","Q"]"#,
            )
        };
        std::fs::write(
            dir.join("l.law"),
            format!(
                r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{vocabulary} local here({sp}) reads {left};}}
reading After {{{vocabulary} local here({tp}) reads {right};}}"#
            ),
        )
        .unwrap();
        let run = asks(&dir, &[
            "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
            "same=compare($m.operation,to=$m.operation,kind=action)",
        ]);
        assert_eq!(
            run.code, code,
            "{name}/{reverse}: {}",
            run.stdout
        );
        let result = result_json(&dir, &run);
        let m = answer(&result, "m");
        assert_eq!(
            s(get(m, "status")),
            if code == 0 { "established" } else { "refuted" }
        );
        assert!(has(get(m, "outputs"), "operation"));
        assert_eq!(has(get(m, "outputs"), "map"), code == 0);
        assert_eq!(s(get(answer(&result, "same"), "status")), "established");
        if code == 0 {
            let map = value(&result, get(get(m, "outputs"), "map"));
            let transport = value(&result, &arr(get(map, "transports"))[0]);
            let clauses = arr(get(transport, "clauses"));
            assert_eq!(clauses.len(), 2);
            for clause in clauses {
                let args = value(&result, get(clause, "arguments"));
                assert_json(get(args, "source_type"), types);
                let qs = arr(get(value(&result, get(clause, "commutes")), "quantifiers"));
                assert_eq!(qs.len(), 3);
                for (q, name) in qs.iter().zip(names) {
                    assert_eq!(s(get(q, "name")), name);
                }
            }
        } else {
            let examples = arr(get(m, "counterexamples"));
            assert!(!examples.is_empty());
            for example in examples {
                let data = get(value(&result, example), "data");
                let bindings = arr(get(data, "bindings"));
                assert_eq!(bindings.len(), 3);
                for (binding, name) in bindings.iter().zip(names) {
                    assert_eq!(s(get(binding, "name")), name);
                }
                let n = value(
                    &result,
                    get(&bindings[if reverse { 2 } else { 0 }], "value"),
                );
                let q = value(
                    &result,
                    get(&bindings[if reverse { 0 } else { 2 }], "value"),
                );
                // 反例は読まない側の数を、その型の零へ復元する。
                if name == "z-witness" {
                    assert_ne!(s(n), "0");
                    assert_json(q, r#"["0","1"]"#);
                    assert_eq!(value(&result, get(data, "left")).value, n.value);
                } else {
                    assert_json(n, r#""0""#);
                    assert_ne!(s(&arr(q)[0]), "0");
                    assert_json(
                        value(&result, get(data, "left")),
                        &format!("[\"{}\",\"{}\"]", s(&arr(q)[0]), s(&arr(q)[1])),
                    );
                }
                assert_ne!(
                    value(&result, get(data, "left")).value,
                    value(&result, get(data, "right")).value
                );
            }
        }
    }
}

#[test]
fn local_mixed_numeric_reads_preserve_missing_and_nonlinear_reasons() {
    for (name, left, right, missing) in [
        ("missing", "s.free+q", "t.free+y", true),
        ("nonlinear", "q*q", "y*y", false),
    ] {
        let (dir, vocabulary) =
            rational_local_parameter_inputs(&format!("local-mixed-{name}"), missing);
        std::fs::write(
            dir.join("l.law"),
            format!(
                r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{vocabulary} local here(n:Z,s:State,q:Q) reads {left};}}
reading After {{{vocabulary} local here(m:Z,t:State,y:Q) reads {right};}}"#
            ),
        )
        .unwrap();
        let run=asks(&dir,&[
            "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
            "same=compare($m.operation,to=$m.operation,kind=action)",
            "n=needed($m)",
        ]);
        assert_eq!(run.code, 2, "{name}: {}", run.stdout);
        let result = result_json(&dir, &run);
        let m = answer(&result, "m");
        assert_eq!(s(get(m, "status")), "undetermined");
        assert!(has(get(m, "outputs"), "operation"));
        assert!(!has(get(m, "outputs"), "map"));
        assert!(!has(m, "counterexamples") || arr(get(m, "counterexamples")).is_empty());
        assert_eq!(s(get(answer(&result, "same"), "status")), "established");
        assert!(arr(get(m, "reasons"))
            .iter()
            .any(|reason| s(get(reason, "code"))
                == if missing {
                    "missing_observation"
                } else {
                    "unsupported_algorithm"
                }));
        let plan = value(&result, get(get(answer(&result, "n"), "outputs"), "plan"));
        let requirements = arr(get(plan, "requirements"));
        if missing {
            assert!(requirements
                .iter()
                .any(|r| s(get(get(r, "field"), "field")) == "Reservations.State.free"));
        } else {
            assert!(requirements.is_empty());
        }
    }
}

#[test]
fn local_mixed_numeric_tuple_witnesses_restore_all_axes() {
    for (name, left, right) in [
        ("integer", "pair.1.1", "0"),
        ("rational", "q", "rat(0,1)"),
    ] {
        let (dir, vocabulary) =
            rational_local_parameter_inputs(&format!("local-mixed-nested-{name}"), false);
        std::fs::write(
            dir.join("l.law"),
            format!(
                r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{vocabulary} local here(pair:(Z,(Z,Z)),q:Q) reads {left};}}
reading After {{{vocabulary} local here(next:(Z,(Z,Z)),y:Q) reads {right};}}"#
            ),
        )
        .unwrap();
        let request="m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)";
        let run = asks(&dir, &[request]);
        assert_eq!(run.code, 1, "{name}: {}", run.stdout);
        let result = result_json(&dir, &run);
        let m = answer(&result, "m");
        assert_eq!(s(get(m, "status")), "refuted");
        let data = get(value(&result, &arr(get(m, "counterexamples"))[0]), "data");
        let bindings = arr(get(data, "bindings"));
        assert_eq!(bindings.len(), 2);
        assert_eq!(s(get(&bindings[0], "name")), "pair");
        assert_eq!(s(get(&bindings[1], "name")), "q");
        let pair = arr(value(&result, get(&bindings[0], "value")));
        assert_eq!(pair.len(), 2);
        let tail = arr(&pair[1]);
        assert_eq!(tail.len(), 2);
        let q = value(&result, get(&bindings[1], "value"));
        if name == "integer" {
            assert_eq!(value(&result, get(data, "left")).value, tail[1].value);
            assert_ne!(s(&tail[1]), "0");
            assert_json(q, r#"["0","1"]"#);
        } else {
            assert_json(
                value(&result, get(&bindings[0], "value")),
                r#"["0",["0","0"]]"#,
            );
            assert_eq!(value(&result, get(data, "left")).value, q.value);
            assert_ne!(s(&arr(q)[0]), "0");
        }
        assert_ne!(
            value(&result, get(data, "left")).value,
            value(&result, get(data, "right")).value
        );
    }
}

#[test]
fn local_mixed_numeric_constant_guards_use_full_or_empty_domains() {
    // 恒真のguardは全域、恒偽のguardは空域として移送する。反例は両方の数を零へ復元する。
    for (name, reverse, integer, source_guard, target_guard, code) in [
        ("computed", false, true, "1+1=2", "not false", 0),
        ("source-empty", true, true, "false", "true", 0),
        ("target-empty", true, false, "true", "false", 1),
    ] {
        let (dir, vocabulary) = rational_local_parameter_inputs(
            &format!("mixed-constant-{reverse}-{integer}-{name}"),
            false,
        );
        let (sp, tp, names) = if reverse {
            ("q:Q,n:Z", "y:Q,m:Z", ["q", "n"])
        } else {
            ("n:Z,q:Q", "m:Z,y:Q", ["n", "q"])
        };
        let (left, right) = if integer { ("n", "m") } else { ("q", "y") };
        std::fs::write(
            dir.join("l.law"),
            format!(
                r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{vocabulary} local here({sp}) when {source_guard} reads {left};}}
reading After {{{vocabulary} local here({tp}) when {target_guard} reads {right};}}"#
            ),
        )
        .unwrap();
        let run = asks(
            &dir,
            &[
                "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
                "n=needed($m)",
            ],
        );
        assert_eq!(run.code, code, "{name}: {}", run.stdout);
        let j = result_json(&dir, &run);
        assert_eq!(s(get(&j, "status")), "complete");
        let m = answer(&j, "m");
        assert_eq!(
            s(get(m, "status")),
            if code == 0 { "established" } else { "refuted" }
        );
        assert!(has(get(m, "outputs"), "operation"));
        assert_eq!(has(get(m, "outputs"), "map"), code == 0);
        let plan = value(&j, get(get(answer(&j, "n"), "outputs"), "plan"));
        assert!(arr(get(plan, "requirements")).is_empty());
        if code == 1 {
            let examples = arr(get(m, "counterexamples"));
            assert!(!examples.is_empty());
            let data = get(value(&j, &examples[0]), "data");
            let bindings = arr(get(data, "bindings"));
            assert_eq!(bindings.len(), 2);
            for (binding, name) in bindings.iter().zip(names) {
                assert_eq!(s(get(binding, "name")), name);
                assert_json(
                    value(&j, get(binding, "value")),
                    if name == "n" {
                        r#""0""#
                    } else {
                        r#"["0","1"]"#
                    },
                );
            }
            assert_json(value(&j, get(data, "left")), "true");
            assert_json(value(&j, get(data, "right")), "false");
        }
    }
}

#[test]
fn local_mixed_numeric_guards_keep_only_needed_observations() {
    // free欠測のfixture。guardの判定に要る欠測だけを残し、恒偽のguardの下の読取りは要求しない。
    for (name, source_guard, target_guard, left, right, code) in [
        ("source-unknown", "s.free=0", "true", "q", "y", 2),
        ("known-false", "false and s.free=0", "true", "s.free+q", "t.free+y", 0),
    ] {
        let (dir, vocabulary) = rational_local_parameter_inputs(&format!("mixed-guard-{name}"), true);
        std::fs::write(dir.join("l.law"), format!(
            r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{vocabulary} local here(n:Z,s:State,q:Q) when {source_guard} reads {left};}}
reading After {{{vocabulary} local here(m:Z,t:State,y:Q) when {target_guard} reads {right};}}"#
        )).unwrap();
        let r = asks(&dir, &["m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
            "same=compare($m.operation,to=$m.operation,kind=action)", "n=needed($m)"]);
        assert_eq!(r.code, code, "{name}: {}", r.stdout);
        let j = result_json(&dir, &r);
        let m = answer(&j, "m");
        assert_eq!(s(get(m, "status")), if code == 0 { "established" } else { "undetermined" });
        assert!(has(get(m, "outputs"), "operation"));
        assert_eq!(has(get(m, "outputs"), "map"), code == 0);
        assert_eq!(s(get(answer(&j, "same"), "status")), "established");
        let plan = value(&j, get(get(answer(&j, "n"), "outputs"), "plan"));
        let requirements = arr(get(plan, "requirements"));
        assert_eq!(requirements.is_empty(), code == 0, "{name}");
        if code == 2 {
            assert!(requirements.iter().all(|r| s(get(get(r, "field"), "field")) == "Reservations.State.free"));
            assert!(arr(get(m, "reasons")).iter().any(|r| s(get(r, "code")) == "missing_observation"));
            assert!(!has(m, "counterexamples") || arr(get(m, "counterexamples")).is_empty());
        }
    }
}

#[test]
fn local_numeric_tuple_arguments_share_axes_without_domains() {
    // 平たいZのTuple引数は成分を無限軸として共有し、有限域を作らない。
    let dir = four_state_inputs("local-tuple-Z-identity");
    let vocabulary = r#"use vocabulary Reservations version "1" digest "sha256:8427a2712c22d6eed1cdd5f48258bea102904173558a7087bb82c7d95665c9ff";"#;
    std::fs::write(dir.join("l.law"),format!(r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{vocabulary} local here(pair:(Z,Z),s:State,take:Bool,last:Z,more:(Z,Z)) reads pair.0+pair.1+last+more.0+more.1;}}
reading After {{{vocabulary} local here(next:(Z,Z),t:State,keep:Bool,final:Z,tail:(Z,Z)) reads next.0+next.1+final+tail.0+tail.1;}}"#)).unwrap();
    let requests = [
        "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
        "same=compare($m.operation,to=$m.operation,kind=action)",
    ];
    let run = asks(&dir, &requests);
    assert_eq!(run.code, 0, "{}", run.stdout);
    let result = result_json(&dir, &run);
    let m = answer(&result, "m");
    assert_eq!(s(get(m, "status")), "established");
    assert_eq!(s(get(answer(&result, "same"), "status")), "established");
    let map = value(&result, get(get(m, "outputs"), "map"));
    let transport = value(&result, &arr(get(map, "transports"))[0]);
    for clause in arr(get(transport, "clauses")) {
        let args = value(&result, get(clause, "arguments"));
        let types = arr(get(args, "source_type"));
        assert_json(&types[1], r#"["Tuple","Z","Z"]"#);
        let qs = arr(get(value(&result, get(clause, "commutes")), "quantifiers"));
        assert_eq!(
            qs.iter().map(|q| s(get(q, "name"))).collect::<Vec<_>>(),
            ["pair", "s", "take", "last", "more"]
        );
        for index in [0, 3, 4] {
            assert_eq!(s(get(&qs[index], "kind")), "forall");
            assert!(!has(&qs[index], "domain"));
        }
    }
}

#[test]
fn local_nested_rational_tuple_arguments_restore_original_witnesses() {
    // 入れ子のQのTuple引数。反例はguardの有理fiber(pair.0.0+pair.1.1=3)の上で、元の入れ子の形に戻す。
    let dir = four_state_inputs("local-tuple-Q-nested-kernel-read");
    let vocabulary = r#"use vocabulary Reservations version "1" digest "sha256:8427a2712c22d6eed1cdd5f48258bea102904173558a7087bb82c7d95665c9ff";"#;
    std::fs::write(dir.join("l.law"),format!(r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{vocabulary} local here(pair:((Q,Q),(Q,Q)),s:State,take:Bool,last:Q,more:((Q,Q),(Q,Q))) when pair.0.0+pair.1.1=3 reads pair.0.0;}}
reading After {{{vocabulary} local here(next:((Q,Q),(Q,Q)),t:State,keep:Bool,final:Q,tail:((Q,Q),(Q,Q))) reads rat(0,1);}}"#)).unwrap();
    let requests = [
        "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
        "same=compare($m.operation,to=$m.operation,kind=action)",
    ];
    let run = asks(&dir, &requests);
    assert_eq!(run.code, 1, "{}", run.stdout);
    let result = result_json(&dir, &run);
    let m = answer(&result, "m");
    assert_eq!(s(get(m, "status")), "refuted");
    assert_eq!(s(get(answer(&result, "same"), "status")), "established");
    assert!(!has(get(m, "outputs"), "map"));
    let examples = arr(get(m, "counterexamples"));
    assert!(!examples.is_empty());
    let fraction = |v: &JNode| {
        let p = arr(v);
        (
            s(&p[0]).parse::<i64>().unwrap(),
            s(&p[1]).parse::<i64>().unwrap(),
        )
    };
    for example in examples {
        let data = get(value(&result, example), "data");
        let bs = arr(get(data, "bindings"));
        assert_eq!(
            bs.iter().map(|b| s(get(b, "name"))).collect::<Vec<_>>(),
            ["pair", "s", "take", "last", "more"]
        );
        let pair = arr(value(&result, get(&bs[0], "value")));
        let more = arr(value(&result, get(&bs[4], "value")));
        assert_eq!(pair.len(), 2);
        assert_eq!(more.len(), 2);
        for half in pair.iter().chain(more) {
            assert_eq!(arr(half).len(), 2);
        }
        let (a, ad) = fraction(&arr(&pair[0])[0]);
        let (b, bd) = fraction(&arr(&pair[1])[1]);
        assert_eq!(a * bd + b * ad, 3 * ad * bd);
        assert_ne!(a, 0);
        assert_ne!(
            value(&result, get(data, "left")).value,
            value(&result, get(data, "right")).value
        );
    }
}

#[test]
fn local_optional_expression_reads_require_only_the_selected_branch() {
    // 選ばれた枝(free)の欠測は未決、使われない枝(held・else)の欠測は決定を妨げない。
    for (case, sr, tr, drop_held, code) in [
        (
            "selected-missing",
            "if true then some(s.free>0) else some(s.held>0)",
            "if true then some(t.free>0) else some(t.held>0)",
            true,
            2,
        ),
        (
            "unused-missing",
            "if true then choice else some(s.free>0)",
            "if true then chosen else some(t.free>0)",
            false,
            0,
        ),
    ] {
        let (dir, vocabulary) =
            finite_local_parameter_inputs(&format!("local-optional-expression-{case}"));
        let map = std::fs::read_to_string(dir.join("a.json"))
            .unwrap()
            .lines()
            .filter(|line| {
                !line.contains(r#""id":"p-free""#)
                    && !line.contains(r#""id":"r-free""#)
                    && (!drop_held
                        || (!line.contains(r#""id":"p-held""#)
                            && !line.contains(r#""id":"r-held""#)))
            })
            .collect::<Vec<_>>()
            .join("\n");
        std::fs::write(dir.join("a.json"), map).unwrap();
        std::fs::write(
            dir.join("l.law"),
            format!(
                r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{vocabulary} local here(choice:Option<Bool>,take:Bool,s:State) reads {sr};}}
reading After {{{vocabulary} local here(chosen:Option<Bool>,keep:Bool,t:State) reads {tr};}}"#
            ),
        )
        .unwrap();
        let requests = [
            "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
            "same=compare($m.operation,to=$m.operation,kind=action)",
            "n=needed($m)",
        ];
        let run = asks(&dir, &requests);
        assert_eq!(run.code, code, "{case}: {}", run.stdout);
        let result = result_json(&dir, &run);
        let m = answer(&result, "m");
        assert_eq!(
            s(get(m, "status")),
            if code == 0 { "established" } else { "undetermined" }
        );
        assert!(has(get(m, "outputs"), "operation"));
        assert_eq!(has(get(m, "outputs"), "map"), code == 0);
        assert_eq!(s(get(answer(&result, "same"), "status")), "established");
        let plan = value(&result, get(get(answer(&result, "n"), "outputs"), "plan"));
        let requirements = arr(get(plan, "requirements"));
        assert_eq!(requirements.is_empty(), code == 0);
        if code == 2 {
            assert!(!has(m, "counterexamples"));
            assert!(
                requirements
                    .iter()
                    .all(|r| s(get(get(r, "field"), "field")) == "Reservations.State.free")
            );
            for subject in ["p", "r"] {
                assert!(
                    requirements
                        .iter()
                        .any(|r| s(get(get(r, "field"), "subject")) == subject)
                );
            }
        }
    }
}

#[test]
fn change_transport_compares_different_fieldsets_on_all_finite_arguments() {
    // 更新fieldの集合が違うchangeも、有限引数の全組で比較する。後ろの組(k,l)=(true,true)だけが違う。
    let dir = four_state_inputs("change-fieldsets-later-tuple");
    let vocabulary = r#"use vocabulary Reservations version "1" digest "sha256:8427a2712c22d6eed1cdd5f48258bea102904173558a7087bb82c7d95665c9ff";"#;
    std::fs::write(dir.join("l.law"), format!(r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{vocabulary} change tune(s:State,n:Bool,m:Bool)=s with {{free=s.free}};}}
reading After {{{vocabulary} change tune(t:State,k:Bool,l:Bool)=t with {{held=if k and l then t.held+1 else t.held,free=t.free}};}}"#)).unwrap();
    let requests = ["m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)", "same=compare($m.operation,to=$m.operation,kind=action)"];
    let run = asks(&dir, &requests);
    assert_eq!(run.code, 1, "{}", run.stdout);
    let result = result_json(&dir, &run);
    let map = answer(&result, "m");
    assert_eq!(s(get(map, "status")), "refuted");
    assert!(!has(get(map,"outputs"),"map"));
    assert_eq!(s(get(answer(&result,"same"),"status")), "established");
    let evidence = value(&result, &arr(get(map,"counterexamples"))[0]);
    let data = get(evidence,"data");
    let bindings = arr(get(data,"bindings"));
    assert_eq!(bindings.len(), 3);
    for binding in &bindings[1..] { assert_eq!(value(&result,get(binding,"value")).value, archsig::json::parse(b"true").unwrap().value); }
    let left = s(value(&result,get(data,"left"))).parse::<i64>().unwrap();
    let right = s(value(&result,get(data,"right"))).parse::<i64>().unwrap();
    assert_eq!(right, left+1);
}

#[test]
fn integer_change_keeps_earlier_missing_reads_when_a_later_update_is_unsupported() {
    let dir=four_state_inputs("integer-change-earlier-missing");
    let text=std::fs::read_to_string(dir.join("a.json")).unwrap();
    std::fs::write(dir.join("a.json"),text.lines().filter(|line|!line.contains(r#""id":"p-free""#)).collect::<Vec<_>>().join("\n")).unwrap();
    std::fs::write(dir.join("l.law"),r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {use vocabulary Reservations version "1" digest "sha256:8427a2712c22d6eed1cdd5f48258bea102904173558a7087bb82c7d95665c9ff";
change tune(s:State,n:Z)=s with {free=s.free,held=n*n};law required zero(s:State):s.held=0;}"#).unwrap();
    let run=asks(&dir,&["r=solve(Before.zero,on=@v/A,using=Before.tune)","n=needed($r)"]);
    assert_eq!(run.code,2,"{}",run.stdout);
    let result=result_json(&dir,&run);assert_eq!(s(get(answer(&result,"r"),"status")),"undetermined");
    let plan=value(&result,get(get(answer(&result,"n"),"outputs"),"plan"));
    assert!(arr(get(plan,"requirements")).iter().any(|r|{
        let pointer=get(r,"field");s(get(pointer,"subject"))=="p"&&s(get(pointer,"field"))=="Reservations.State.free"
    }));
}

#[test]
fn relation_transport_restricts_rational_families_to_exact_guard_domains() {
    // Qのguard fiber(2n=1)は整数点を持たない。反例は分数 n=1/2 で、語の違い(空語と生成元1つ)を返す。
    let dir = four_state_inputs("relation-rational-domain-word_refuted");
    let vocabulary = r#"use vocabulary Reservations version "1" digest "sha256:8427a2712c22d6eed1cdd5f48258bea102904173558a7087bb82c7d95665c9ff";"#;
    std::fs::write(dir.join("l.law"), format!(r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{ {vocabulary} relation paths(n:Q,e:Reserve,m:Q,take:Bool,extra:Q) when 2*n=1:(identity(source(path(e))))=path(e); }}
reading After {{ {vocabulary} relation paths(k:Q,t:Reserve,j:Q,keep:Bool,last:Q) when 2*k=1:(path(t))=path(t); }}"#)).unwrap();
    let requests = [
        "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
        "same=compare($m.operation,to=$m.operation,kind=action)",
    ];
    let run = asks(&dir, &requests);
    assert_eq!(run.code, 1, "{}", run.stdout);
    let result = result_json(&dir, &run);
    assert_eq!(s(get(answer(&result, "m"), "status")), "refuted");
    assert_eq!(s(get(answer(&result, "same"), "status")), "established");
    assert!(!has(get(answer(&result, "m"), "outputs"), "map"));
    let examples = arr(get(answer(&result, "m"), "counterexamples"));
    assert!(!examples.is_empty());
    for example in examples {
        let data = get(value(&result, example), "data");
        let bindings = arr(get(data, "bindings"));
        assert_eq!(
            bindings
                .iter()
                .map(|b| s(get(b, "name")))
                .collect::<Vec<_>>(),
            ["n", "e", "m", "take", "extra"]
        );
        let pair = arr(value(&result, get(&bindings[0], "value")));
        assert_eq!((s(&pair[0]), s(&pair[1])), ("1", "2"));
        assert!(arr(get(value(&result, get(data, "left")), "generators")).is_empty());
        assert_eq!(
            arr(get(value(&result, get(data, "right")), "generators")).len(),
            1
        );
    }
}

#[test]
fn local_parameter_positions_compare_all_finite_arguments_and_preserve_the_base_operation() {
    // 引数位置が違うreadは、全有限割当てで比べて反証する。
    let (dir, vocabulary) = finite_local_parameter_inputs("local-different-finite-positions");
    std::fs::write(
        dir.join("l.law"),
        format!(
            r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{vocabulary} local here(x:Option<Bool>,y:Option<Bool>) reads x;}}
reading After {{{vocabulary} local here(a:Option<Bool>,b:Option<Bool>) reads b;}}"#
        ),
    )
    .unwrap();
    let requests = [
        "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
        "same=compare($m.operation,to=$m.operation,kind=action)",
        "n=needed($m)",
    ];
    let run = asks(&dir, &requests);
    assert_eq!(run.code, 1, "{}", run.stdout);
    let result = result_json(&dir, &run);
    let m = answer(&result, "m");
    assert_eq!(s(get(m, "status")), "refuted");
    assert!(has(get(m, "outputs"), "operation"));
    assert!(!has(get(m, "outputs"), "map"));
    assert_eq!(s(get(answer(&result, "same"), "status")), "established");
    let data = get(value(&result, &arr(get(m, "counterexamples"))[0]), "data");
    let bindings = arr(get(data, "bindings"));
    assert_eq!(bindings.len(), 2);
    for ((binding, name), expected) in bindings
        .iter()
        .zip(["x", "y"])
        .zip([r#"{"none":true}"#, r#"{"some":false}"#])
    {
        assert_eq!(s(get(binding, "name")), name);
        assert_json(value(&result, get(binding, "value")), expected);
    }
    assert_json(value(&result, get(data, "left")), r#"{"none":true}"#);
    assert_json(value(&result, get(data, "right")), r#"{"some":false}"#);
    let plan = value(&result, get(get(answer(&result, "n"), "outputs"), "plan"));
    assert!(arr(get(plan, "requirements")).is_empty());
}

#[test]
fn numeric_view_parameters_use_exact_integer_and_rational_functions() {
    // 無限のZ/Q引数を持つviewの移送は、引数名が違っても関数として一致すれば成立する。
    for (case, ty, source, target) in [
        ("integer", "Z", "z", "renamed"),
        ("rational", "Q", "z+rat(1,3)", "renamed+rat(1,3)"),
    ] {
        let dir = inputs(&format!("numeric-view-parameter-{case}"));
        let uses = r#"use vocabulary Reservations version "1" digest "sha256:8427a2712c22d6eed1cdd5f48258bea102904173558a7087bb82c7d95665c9ff";"#;
        std::fs::write(
            dir.join("l.law"),
            format!(
                r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{uses} view affine(s:State,z:{ty}):{ty}={source};}}
reading After {{{uses} view affine(s:State,renamed:{ty}):{ty}={target};}}"#
            ),
        )
        .unwrap();
        let run = asks(
            &dir,
            &[
                "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
                "same=compare($m.operation,to=$m.operation,kind=action)",
            ],
        );
        assert_eq!(run.code, 0, "{case}: {}", run.stdout);
        let result = result_json(&dir, &run);
        assert_eq!(s(get(answer(&result, "m"), "status")), "established");
        assert_eq!(s(get(answer(&result, "same"), "status")), "established");
        let outputs = get(answer(&result, "m"), "outputs");
        assert!(has(outputs, "operation"));
        assert!(has(outputs, "map"));
        std::fs::remove_dir_all(dir).unwrap();
    }
}

#[test]
fn multiple_unsupported_views_keep_each_original_reason() {
    let dir = four_state_inputs("multiple-unsupported-views");
    let vocabulary = r#"use vocabulary Reservations version "1" digest "sha256:8427a2712c22d6eed1cdd5f48258bea102904173558a7087bb82c7d95665c9ff";"#;
    std::fs::write(dir.join("l.law"), format!(r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{vocabulary} view first(s:State,z:Z):Z=z*z;view second(s:State,z:Z):Z=z*z+1;}}
reading After {{{vocabulary} view first(s:State,z:Z):Z=z*z;view second(s:State,z:Z):Z=z*z+1;}}"#
        ),
    )
    .unwrap();
    let run = asks(
        &dir,
        &[
            "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
            "n=needed($m)",
        ],
    );
    assert_eq!(run.code, 2, "{}", run.stdout);
    let result = result_json(&dir, &run);
    let map = answer(&result, "m");
    let reasons = arr(get(map, "reasons"));
    let law = std::fs::read_to_string(dir.join("l.law")).unwrap();
    let plan = value(&result, get(get(answer(&result, "n"), "outputs"), "plan"));
    for expected in ["z*z", "z*z+1"] {
        let matching: Vec<_> = reasons
            .iter()
            .filter(|r| {
                if s(get(r, "code")) != "unsupported_algorithm"
                    || s(get(get(r, "details"), "method")) != "affine_numeric_view_transport"
                {
                    return false;
                }
                let span = arr(get(get(r, "location"), "span"));
                &law[num(&span[0]) as usize..num(&span[1]) as usize] == expected
            })
            .collect();
        assert!(!matching.is_empty(), "missing {expected}");
        assert!(matching.iter().all(|reason| {
            arr(get(plan, "blockers"))
                .iter()
                .any(|b| b.value == reason.value)
        }));
    }
    assert!(has(get(map, "outputs"), "operation"));
    assert!(!has(get(map, "outputs"), "map"));
    std::fs::remove_dir_all(dir).unwrap();
}

#[test]
fn numeric_view_functions_keep_nested_axes_and_exact_cancellation() {
    // affine viewの係数の違いを、parameterの実際の点 (a,b)=(0,1) で反証する。a-a は厳密に相殺する。
    let uses = r#"use vocabulary Reservations version "1" digest "sha256:8427a2712c22d6eed1cdd5f48258bea102904173558a7087bb82c7d95665c9ff";"#;
    let law = format!(
        r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{uses} view affine(s:State,a:Z,b:Z):(Z,Z)=(a+2*b,a-a);}}
reading After {{{uses} view affine(s:State,x:Z,y:Z):(Z,Z)=(x+3*y,0);}}"#
    );
    let result=archsig::observed::evaluate_observed_bytes(
        archsig::input::InputSources::from_bytes(
            vec![include_bytes!("fixtures/reservations.atoms.json").to_vec()],law.into_bytes(),
            four_state_map(false).into_bytes()),
        &["m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)"],
        &mut archsig::control::Control::unlimited(),
    ).unwrap();
    let j = archsig::json::parse(result.wire().canonical().as_bytes()).unwrap();
    let m = answer(&j, "m");
    assert_eq!(s(get(m, "status")), "refuted");
    assert!(has(get(m, "outputs"), "operation"));
    assert!(!has(get(m, "outputs"), "map"));
    let examples = arr(get(m, "evidence"));
    assert!(!examples.is_empty());
    for example in examples {
        let proof = value(&j, example);
        assert_eq!(s(get(proof, "kind")), "counterexample");
        let data = get(proof, "data");
        let bindings = arr(get(data, "bindings"));
        let parameter = |name: &str| {
            value(
                &j,
                get(
                    bindings.iter().find(|b| s(get(b, "name")) == name).unwrap(),
                    "value",
                ),
            )
        };
        assert_json(parameter("a"), r#""0""#);
        assert_json(parameter("b"), r#""1""#);
        assert_json(value(&j, get(data, "left")), r#"{"some":["2","0"]}"#);
        assert_json(value(&j, get(data, "right")), r#"{"some":["3","0"]}"#);
    }
}

#[test]
fn numeric_guarded_zero_map_refutes_a_different_application_domain() {
    // guardの違いで零集合の適用域が変わると、n=1 を反例として反証する。
    let dir = small_inputs("numeric-guarded-zero-different");
    let uses = r#"use vocabulary Reservations version "1" digest "sha256:8427a2712c22d6eed1cdd5f48258bea102904173558a7087bb82c7d95665c9ff";"#;
    std::fs::write(
        dir.join("l.law"),
        format!(
            r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{uses} law required equation(s:State,n:Z) when n=0: n-n=0;}}
reading After {{{uses} law required equation(s:State,x:Z) when true: x-x=0;}}"#
        ),
    )
    .unwrap();
    let run = asks(
        &dir,
        &[
            "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
            "same=compare($m.operation,to=$m.operation,kind=action)",
        ],
    );
    assert_eq!(run.code, 1, "{}", run.stdout);
    let j = result_json(&dir, &run);
    let m = answer(&j, "m");
    assert_eq!(s(get(m, "status")), "refuted");
    assert!(has(get(m, "outputs"), "operation"));
    assert!(!has(get(m, "outputs"), "map"));
    assert_eq!(s(get(answer(&j, "same"), "status")), "established");
    let examples = arr(get(m, "counterexamples"));
    assert!(!examples.is_empty());
    for example in examples {
        let data = get(value(&j, example), "data");
        let bindings = arr(get(data, "bindings"));
        let n = bindings.iter().find(|b| s(get(b, "name")) == "n").unwrap();
        assert_json(value(&j, get(n, "value")), r#""1""#);
        assert_json(value(&j, get(data, "left")), "false");
        assert_json(value(&j, get(data, "right")), "true");
    }
    std::fs::remove_dir_all(dir).unwrap();
}

#[test]
fn finite_reference_view_parameters_use_the_declared_entity_correspondence() {
    let dir = workdir("finite-reference-view-parameter-entities");
    let left = include_bytes!("fixtures/object-law-transport.atoms.json");
    let right = include_bytes!("fixtures/object-law-transport-right.atoms.json");
    let initial = archsig::definition::check_definitions(&[
        ("left", left.as_slice()),
        ("right", right.as_slice()),
    ])
    .unwrap();
    let ld = &initial.vocabularies()["Left"].digest;
    let rd = &initial.vocabularies()["Right"].digest;
    let bridge = include_str!("fixtures/object-law-transport-bridge.atoms.json")
        .replace("@LEFT_DIGEST@", ld)
        .replace("@RIGHT_DIGEST@", rd);
    let definitions = archsig::definition::check_definitions(&[
        ("left", left.as_slice()),
        ("right", right.as_slice()),
        ("bridge", bridge.as_bytes()),
    ])
    .unwrap();
    let bd = &definitions.vocabularies()["Bridge"].digest;
    for (name, bytes) in [
        ("left.json", left.as_slice()),
        ("right.json", right.as_slice()),
        ("bridge.json", bridge.as_bytes()),
    ] {
        std::fs::write(dir.join(name), bytes).unwrap();
    }
    let map = include_str!("fixtures/object-view-transport.archmap.json")
        .replace("@LEFT_DIGEST@", ld)
        .replace("@RIGHT_DIGEST@", rd)
        .replace("@BRIDGE_DIGEST@", bd);
    std::fs::write(dir.join("a.json"), map).unwrap();
    let uses = format!(
        r#"use vocabulary Left version "1" digest "{ld}";use vocabulary Right version "1" digest "{rd}";use vocabulary Bridge version "1" digest "{bd}";"#
    );
    std::fs::write(dir.join("l.law"),format!(r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{uses} view flag(c:Left.Child,candidate:Option<Left.Child>):Bool=candidate=some(c);}}
reading After {{{uses} view flag(d:Right.Child,renamed:Option<Right.Child>):Bool=renamed=some(d);}}"#)).unwrap();
    let run = cli::run(
        &dir,
        &[
            "run",
            "--atom-definition",
            "left.json",
            "--atom-definition",
            "right.json",
            "--atom-definition",
            "bridge.json",
            "--archmap",
            "a.json",
            "--law",
            "l.law",
            "--out",
            "out",
            "--ask",
            "m=map(Bridge.Move,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
            "--ask",
            "same=compare($m.operation,to=$m.operation,kind=action)",
        ],
    );
    assert_eq!(run.code, 0, "{}", run.stdout);
    let j = result_json(&dir, &run);
    let m = answer(&j, "m");
    assert_eq!(s(get(m, "status")), "established");
    assert!(has(get(m, "outputs"), "map"));
    assert_eq!(s(get(answer(&j, "same"), "status")), "established");
    std::fs::remove_dir_all(dir).unwrap();
}

#[test]
fn conditional_affine_missing_guard_retains_object_and_needed_for_following_check() {
    let dir = small_inputs("conditional-affine-missing-guard");
    let map = std::fs::read_to_string(dir.join("a.json"))
        .unwrap()
        .lines()
        .filter(|line| !line.contains("\"id\":\"p-free\""))
        .collect::<Vec<_>>()
        .join("\n");
    std::fs::write(dir.join("a.json"), map).unwrap();
    let uses = r#"use vocabulary Reservations version "1" digest "sha256:8427a2712c22d6eed1cdd5f48258bea102904173558a7087bb82c7d95665c9ff";"#;
    std::fs::write(
        dir.join("l.law"),
        format!(
            r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{uses} law required equation(s:State,n:Z) when n=s.free:n=1;}}"#
        ),
    )
    .unwrap();
    let run = asks(
        &dir,
        &[
            "b=build(Before,on=@v/A)",
            "c=check(Before.equation,on=$b.object,s=@v/p)",
            "n=needed($b)",
        ],
    );
    assert_eq!(run.code, 2, "{}", run.stdout);
    let j = result_json(&dir, &run);
    let b = answer(&j, "b");
    assert!(has(get(b, "outputs"), "object"));
    assert!(!has(get(b, "outputs"), "algebra"));
    for id in ["b", "c"] {
        let a = answer(&j, id);
        assert_eq!(s(get(a, "status")), "undetermined");
        let reasons = arr(get(a, "reasons"));
        assert!(
            !reasons
                .iter()
                .any(|r| s(get(r, "code")) == "unsupported_algorithm")
        );
        assert!(
            reasons
                .iter()
                .filter(|r| s(get(r, "code")) == "missing_observation")
                .flat_map(|r| arr(get(r, "missing")))
                .any(|f| s(get(f, "snapshot")) == "v"
                    && s(get(f, "subject")) == "p"
                    && s(get(f, "field")) == "Reservations.State.free")
        );
    }
    assert_eq!(s(get(answer(&j, "n"), "status")), "established");
    std::fs::remove_dir_all(dir).unwrap();
}

#[test]
fn nonlinear_numeric_guard_keeps_partial_build_and_original_needed_blocker() {
    let dir = small_inputs("nonlinear-numeric-guard-partial-build");
    let uses = r#"use vocabulary Reservations version "1" digest "sha256:8427a2712c22d6eed1cdd5f48258bea102904173558a7087bb82c7d95665c9ff";"#;
    std::fs::write(
        dir.join("l.law"),
        format!(
            r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{uses} law required equation(s:State,n:Z) when n*n=0:1=0;}}"#
        ),
    )
    .unwrap();
    let run = asks(&dir, &["b=build(Before,on=@v/A)", "n=needed($b)"]);
    assert_eq!(run.code, 2, "{}", run.stdout);
    let j = result_json(&dir, &run);
    let b = answer(&j, "b");
    assert_eq!(s(get(b, "status")), "undetermined");
    assert!(has(get(b, "outputs"), "object"));
    assert!(!has(get(b, "outputs"), "algebra"));
    let reasons = arr(get(b, "reasons"));
    assert!(
        reasons
            .iter()
            .any(|r| s(get(r, "code")) == "unsupported_algorithm")
    );
    let n = answer(&j, "n");
    assert_eq!(s(get(n, "status")), "established");
    let plan = value(&j, get(get(n, "outputs"), "plan"));
    assert!(arr(get(plan, "requirements")).is_empty());
    let blockers = arr(get(plan, "blockers"));
    for reason in reasons {
        assert!(
            blockers.contains(reason),
            "元の式・位置・依存を含む理由を保持する"
        );
    }
    std::fs::remove_dir_all(dir).unwrap();
}

#[test]
fn numeric_guard_algorithm_boundary_keeps_concrete_checks_and_needed() {
    let dir = small_inputs("numeric-guard-algorithm-boundary");
    let uses = r#"use vocabulary Reservations version "1" digest "sha256:8427a2712c22d6eed1cdd5f48258bea102904173558a7087bb82c7d95665c9ff";"#;
    std::fs::write(
        dir.join("l.law"),
        format!(
            r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{uses} view plus_one():Z=1; view minus_one():Z=-1; law required equation(s:State,n:Z) when n>0:1=0;}}"#
        ),
    )
    .unwrap();
    let run = asks(
        &dir,
        &[
            "b=build(Before,on=@v/A)",
            "p=evaluate(Before.plus_one,on=$b.object)",
            "m=evaluate(Before.minus_one,on=$b.object)",
            "c=check(Before.equation,on=$b.object,s=@v/p,n=$p.value)",
            "o=check(Before.equation,on=$b.object,s=@v/p,n=$m.value)",
            "n=needed($b)",
        ],
    );
    assert_eq!(run.code, 2, "{}", run.stdout);
    let j = result_json(&dir, &run);
    let b = answer(&j, "b");
    assert_eq!(s(get(b, "status")), "undetermined");
    assert!(has(get(b, "outputs"), "object"));
    assert!(!has(get(b, "outputs"), "algebra"));
    let reasons = arr(get(b, "reasons"));
    assert!(
        reasons
            .iter()
            .any(|r| s(get(r, "code")) == "unsupported_algorithm")
    );
    for (id, expected) in [("p", "1"), ("m", "-1")] {
        let a = answer(&j, id);
        assert_eq!(s(get(a, "status")), "established");
        assert_eq!(s(value(&j, get(get(a, "outputs"), "value"))), expected);
    }
    assert_eq!(s(get(answer(&j, "c"), "status")), "refuted");
    assert_eq!(s(get(answer(&j, "c"), "applicability")), "applicable");
    assert_eq!(s(get(answer(&j, "o"), "status")), "established");
    assert_eq!(s(get(answer(&j, "o"), "applicability")), "not_applicable");
    let n = answer(&j, "n");
    assert_eq!(s(get(n, "status")), "established");
    let plan = value(&j, get(get(n, "outputs"), "plan"));
    assert!(arr(get(plan, "requirements")).is_empty());
    for reason in reasons {
        assert!(arr(get(plan, "blockers")).contains(reason));
    }
    std::fs::remove_dir_all(dir).unwrap();
}

#[test]
fn equal_law_truth_does_not_hide_a_changed_zero_component() {
    // 閉じたLawの移送の代表。真偽が等しくても成分の零性が変われば反証する。
    let dir = small_inputs("public-law-map-component-refuted");
    let uses = r#"use vocabulary Reservations version "1" digest "sha256:8427a2712c22d6eed1cdd5f48258bea102904173558a7087bb82c7d95665c9ff";"#;
    std::fs::write(
        dir.join("l.law"),
        format!(
            r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{uses} law required zero(s:State):(s.free,s.held)=(0,0);}}
reading After {{{uses} law required zero(s:State):(s.held,s.free)=(0,0);}}"#
        ),
    )
    .unwrap();
    let run = asks(
        &dir,
        &[
            "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
        ],
    );
    assert_eq!(run.code, 1, "{}", run.stdout);
    let result = result_json(&dir, &run);
    assert_eq!(s(get(&result, "status")), "complete");
    let a = answer(&result, "m");
    assert_eq!(s(get(a, "status")), "refuted");
    assert!(has(get(a, "outputs"), "operation"));
    assert!(!has(get(a, "outputs"), "map"));
    // InvariantMapの成立の同値(equation_holds_iff)は保たれ、EquationMap.zerosの零性(residual_zero_iff)が反証する。
    let graph = internal_graph(&dir, &result);
    let mut holds = 0;
    let mut nonzero = 0;
    for n in arr(get(&graph, "nodes")) {
        if !matches!(&get(n, "type").value, archsig::json::JValue::Str(t) if t == "Proposition") {
            continue;
        }
        let predicate = s(get(get(n, "value"), "predicate"));
        if predicate == "equation_holds_iff" {
            holds += 1;
            assert_eq!(s(get(get(n, "judgment"), "status")), "established");
        }
        if predicate == "residual_zero_iff" && s(get(get(n, "judgment"), "status")) == "refuted" {
            nonzero += 1;
        }
    }
    assert!(holds > 0);
    assert!(nonzero > 0);
    std::fs::remove_dir_all(dir).unwrap();
}

#[test]
fn closed_view_map_refutes_changed_values_and_keeps_configuration_operation() {
    // 閉じたviewの移送の代表。viewの値が変わると反証し、configurationのoperationは残す。
    let dir = small_inputs("public-closed-view-changes");
    std::fs::write(dir.join("l.law"), r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Alternative {
use vocabulary Reservations version "1" digest "sha256:8427a2712c22d6eed1cdd5f48258bea102904173558a7087bb82c7d95665c9ff";
view holdings(s: State): (Z, Z) = (s.free,s.held);
}"#).unwrap();
    let run = asks(&dir, &[
        "m=map(Reservations.Migration,on=@v/m,reading=Alternative,kind=object_algebra)",
        "base=map(Reservations.Migration,on=@v/m,reading=Alternative)",
        "same=compare($m.operation,to=$base.operation,kind=action)",
    ]);
    assert_eq!(run.code, 1, "{}", run.stdout);
    let result = result_json(&dir, &run);
    let m = answer(&result, "m");
    assert_eq!(s(get(m, "status")), "refuted");
    assert!(!has(get(m, "outputs"), "map"));
    assert!(has(get(m, "outputs"), "operation"));
    assert_eq!(s(get(answer(&result, "same"), "status")), "established");
}

#[test]
fn numeric_law_zero_fibers_establish_equal_zero_sets() {
    numeric_law_zero_fibers_compare_all_points_and_recheck_actual_counterexamples(0);
}
#[test]
fn numeric_law_zero_fibers_refute_at_an_actual_counterexample() {
    numeric_law_zero_fibers_compare_all_points_and_recheck_actual_counterexamples(1);
}
fn numeric_law_zero_fibers_compare_all_points_and_recheck_actual_counterexamples(row: usize) {
    // parameterつきLawの移送の代表。零集合が全点で等しければ成立し、違えば実際の点で反証する。
    let (case, a, z, left, right, expected) = [
        ("proportional", "n:Z", "x:Z", "n=1", "2*x=2", "established"),
        (
            "both-universally-false",
            "n:Z",
            "x:Z",
            "n=1",
            "x=2",
            "refuted",
        ),
    ][row];
    let uses = r#"use vocabulary Reservations version "1" digest "sha256:8427a2712c22d6eed1cdd5f48258bea102904173558a7087bb82c7d95665c9ff";"#;
    let law = format!(
        r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{uses} law required equation(s:State,{a}):{left};}}
reading After {{{uses} law required equation(s:State,{z}):{right};}}"#
    );
    let result=archsig::observed::evaluate_observed_bytes(
        archsig::input::InputSources::from_bytes(
            vec![include_bytes!("fixtures/reservations.atoms.json").to_vec()],law.into_bytes(),
            four_state_map(false).into_bytes()),
        &["m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)"],
        &mut archsig::control::Control::unlimited(),
    ).unwrap_or_else(|e|panic!("{case}: {e:?}"));
    let j = archsig::json::parse(result.wire().canonical().as_bytes()).unwrap();
    let m = answer(&j, "m");
    assert_eq!(s(get(m, "status")), expected, "{case}");
    assert!(has(get(m, "outputs"), "operation"), "{case}");
    assert_eq!(
        has(get(m, "outputs"), "map"),
        expected == "established",
        "{case}"
    );
    if expected == "refuted" {
        let evidence = arr(get(m, "evidence"));
        assert!(!evidence.is_empty(), "{case}");
        for example in evidence {
            let example = value(&j, example);
            assert_eq!(s(get(example, "kind")), "counterexample");
            let data = get(example, "data");
            let left = value(&j, get(data, "left"));
            let right = value(&j, get(data, "right"));
            assert_json(left, r#""1""#);
            assert_json(right, r#""0""#);
            let bindings = arr(get(data, "bindings"));
            assert_eq!(bindings.len(), 2, "{case}");
            let n = bindings.iter().find(|b| s(get(b, "name")) == "n").unwrap();
            assert_json(value(&j, get(n, "value")), r#""2""#);
        }
    }
}

#[test]
fn a_changed_finite_parameter_row_refutes_the_whole_map() {
    // 有限parameterのview族の代表。keep=false の行だけが違っても、族全体を反証する。
    let dir = four_state_inputs("finite-parameter-changed-row");
    let vocabulary = r#"use vocabulary Reservations version "1" digest "sha256:8427a2712c22d6eed1cdd5f48258bea102904173558a7087bb82c7d95665c9ff";"#;
    let law = format!(
        r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{vocabulary} view choice(s: State, take: Bool): Z = if take then s.free else 0;}}
reading After {{{vocabulary} view choice(s: State, keep: Bool): Z = if keep then s.free else 1;}}"#
    );
    std::fs::write(dir.join("l.law"), law).unwrap();
    let r = asks(
        &dir,
        &[
            "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
        ],
    );
    assert_eq!(r.code, 1, "{}", r.stdout);
    let result = result_json(&dir, &r);
    assert_eq!(s(get(answer(&result, "m"), "status")), "refuted");
    assert!(has(get(answer(&result, "m"), "outputs"), "operation"));
    assert!(!has(get(answer(&result, "m"), "outputs"), "map"));
}
