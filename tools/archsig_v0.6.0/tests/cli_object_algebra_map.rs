//! 対象族の保存を公開mapと、その後の利用まで検査する。
#[allow(dead_code)]
#[path = "common/cli.rs"]
mod cli;
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
    asks_with_limit(dir, requests, "120000")
}
fn asks_with_limit(dir: &Path, requests: &[&str], time: &str) -> Run {
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
        "--time-ms",
        time,
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
        ("finite-refuted", "Bool", "", "", "if n then s.free+1 else s.free", "if k then t.free+2 else t.free", false, 1, "refuted"),
        ("integer", "Z", "", "", "s.free+n", "t.free+k", false, 0, "established"),
        ("integer-refuted", "Z", "", "", "s.free+n", "t.free+2*k", false, 1, "refuted"),
        ("integer-restricted", "Z", " when n=0", " when k=0", "s.free+n", "t.free+2*k", false, 0, "established"),
        ("integer-guard-refuted", "Z", " when n=0", " when k=1", "s.free+n", "t.free+k", false, 1, "refuted"),
        ("finite-missing", "Bool", "", "", "if n then s.free+1 else s.free", "if k then t.free+1 else t.free", true, 2, "undetermined"),
        ("integer-empty", "Z", " when false", " when false", "s.free+n", "t.free+k", true, 0, "established"),
        ("missing", "Z", "", "", "s.free+n", "t.free+k", true, 2, "undetermined"),
    ] {
        let dir = finite_view_inputs(&format!("change-transport-{mode}"), true);
        let vocabulary = r#"use vocabulary Reservations version "1" digest "sha256:8427a2712c22d6eed1cdd5f48258bea102904173558a7087bb82c7d95665c9ff";"#;
        std::fs::write(dir.join("l.law"),format!(r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{vocabulary} change tune(s:State,n:{parameter}){sg}=s with {{free={left},held=s.free}};}}
reading After {{{vocabulary} change tune(t:State,k:{parameter}){tg}=t with {{held=t.free,free={right}}};}}"#)).unwrap();
        if missing {
            let text=std::fs::read_to_string(dir.join("a.json")).unwrap();
            std::fs::write(dir.join("a.json"),text.lines().filter(|line|!line.contains(r#""id":"p-free""#)).collect::<Vec<_>>().join("\n")).unwrap();
        }
        let requests=["m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)","same=compare($m.operation,to=$m.operation,kind=action)","n=needed($m)"];
        let mut args=vec!["run","--atom-definition","d.json","--law","l.law","--archmap","a.json"];
        for request in requests {args.extend(["--ask",request]);}
        let normal=without_file_changes(&dir,||cli::run(&dir,&args));
        assert_eq!(normal.code,code,"{mode}: {}",normal.stdout);assert!(normal.stderr.is_empty());
        // 反証時は先頭3件の値も含む。確定・未決の上限は維持する。
        assert!(normal.stdout.len()<if code==1 {4000} else {1500});
        let run=asks(&dir,&requests);assert_eq!(run.code,code,"{mode}: {}",run.stdout);
        let result=result_json(&dir,&run);let m=answer(&result,"m");
        assert_eq!(s(get(m,"status")),status,"{mode}");assert_eq!(s(get(answer(&result,"same"),"status")),"established");
        assert_eq!(has(get(m,"outputs"),"map"),code==0);
        if code==0 {
            let map=value(&result,get(get(m,"outputs"),"map"));let transport=value(&result,&arr(get(map,"transports"))[0]);
            assert_eq!(s(get(transport,"kind")),"change");assert_json(get(transport,"parameters"),r#"[["s","t"],["n","k"]]"#);
            let clauses=arr(get(transport,"clauses"));assert_eq!(clauses.len(),3);
            assert_eq!(reference_pairs(&result,value(&result,get(&clauses[0],"arguments"))).len(),6);
            let law=std::fs::read(dir.join("l.law")).unwrap();
            for (clause,expected) in [(&clauses[1],left),(&clauses[2],"s.free")] {
                let expression=value(&result,get(clause,"source"));let span=arr(get(get(expression,"location"),"span"));
                assert_eq!(&law[num(&span[0]) as usize..num(&span[1]) as usize],expected.as_bytes());
                assert_eq!(arr(get(value(&result,get(clause,"commutes")),"quantifiers")).len(),2);
            }
        }
        if code==1 {let examples=arr(get(m,"counterexamples"));assert!(!examples.is_empty());
            let data=get(value(&result,&examples[0]),"data");let bindings=arr(get(data,"bindings"));assert_eq!(bindings.len(),2);
            assert_eq!(s(get(&bindings[1],"name")),"n");
            if mode=="integer-refuted" {assert_eq!(s(value(&result,get(&bindings[1],"value"))),"1");}
        }
        if code==2 {let plan=value(&result,get(get(answer(&result,"n"),"outputs"),"plan"));assert!(arr(get(plan,"requirements")).iter().any(|r|s(get(get(r,"field"),"subject"))=="p"));}
        args.extend(["--out","again","--reuse","out"]);let reused=cli::run(&dir,&args);assert_eq!(reused.code,code,"{mode}: {}",reused.stdout);
        let again=result_json(&dir,&reused);assert!(warnings(&again).is_empty());for key in ["answers","nodes"] {assert_eq!(get(&result,key).value,get(&again,key).value,"{mode}: {key}");}
    }
}

#[test]
fn change_transport_uses_field_alignments_and_keeps_known_refutations_with_missing_updates() {
    for (mode, integer, aligned, preserve, missing, collision, code) in [
        ("finite-align", false, true, true, false, false, 0),
        ("integer-align", true, true, true, false, false, 0),
        ("finite-align-refuted", false, true, false, false, false, 1),
        ("integer-align-refuted", true, true, false, false, false, 1),
        ("finite-partial", false, false, false, true, false, 1),
        ("integer-partial", true, false, false, true, false, 1),
        ("instance-collision", false, false, true, false, true, 2),
    ] {
        let dir=finite_view_inputs(&format!("change-fix-{mode}"),true);
        let old="sha256:8427a2712c22d6eed1cdd5f48258bea102904173558a7087bb82c7d95665c9ff";
        let mut digest=old.to_string();
        let mut archmap=std::fs::read_to_string(dir.join("a.json")).unwrap();
        if aligned {
            let definition=std::fs::read_to_string(dir.join("d.json")).unwrap().replacen(r#""alignments": []"#,r#""alignments":[{"source":"Reservations.State.free","target":"Reservations.State.held","meaning":"数量位置の交換。"},{"source":"Reservations.State.held","target":"Reservations.State.free","meaning":"数量位置の交換。"}]"#,1);
            let checked=archsig::definition::check_definitions(&[("d",definition.as_bytes())]).unwrap();digest=checked.vocabularies["Reservations"].digest.clone();
            std::fs::write(dir.join("d.json"),definition).unwrap();archmap=archmap.replace(old,&digest);
        }
        if collision {
            archmap=archmap.lines().filter(|line|!line.contains(r#""type":"Reservations.Reserve""#)&&!line.contains(r#""subject":"e""#)&&!line.contains(r#""subject":"f""#)).collect::<Vec<_>>().join("\n")
                .replace(r#"[[["v","e"],["v","f"]]]"#,"[]")
                .replace(r#"[["v","q"],["v","s"]]"#,r#"[["v","q"],["v","r"]]"#);
        }
        archmap=archmap.lines().filter(|line|!(missing&&line.contains("Reservations.State.free"))).map(|line|{
            let mut text=line.to_string();if line.contains("Reservations.State.free")||line.contains("Reservations.State.held") {for n in ["1","2","3","4","19"] {text=text.replace(&format!(r#""value":"{n}""#),r#""value":"0""#);}}text
        }).collect::<Vec<_>>().join("\n");std::fs::write(dir.join("a.json"),archmap).unwrap();
        let ty=if integer {"Z"} else {"Bool"};let left=if integer {"n"} else {"if n then 1 else 0"};let right=if integer {"k"} else {"if k then 1 else 0"};
        let (sf,sh,tf,th)=if missing {("s.free","0","t.free","1")} else if collision {("0","0","0","0")} else if preserve {(left,"0","0",right)} else {(left,"0",right,"0")};
        std::fs::write(dir.join("l.law"),format!(r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{use vocabulary Reservations version "1" digest "{digest}";change tune(s:State,n:{ty})=s with {{free={sf},held={sh}}};}}
reading After {{use vocabulary Reservations version "1" digest "{digest}";change tune(t:State,k:{ty})=t with {{free={tf},held={th}}};}}"#)).unwrap();
        let requests=["m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)","same=compare($m.operation,to=$m.operation,kind=action)","n=needed($m)"];
        let mut args=vec!["run","--atom-definition","d.json","--law","l.law","--archmap","a.json"];
        for request in requests {args.extend(["--ask",request]);}
        let normal=without_file_changes(&dir,||cli::run(&dir,&args));assert_eq!(normal.code,code,"{mode}: {}",normal.stdout);assert!(normal.stderr.is_empty());
        let run=asks(&dir,&requests);assert_eq!(run.code,code,"{mode}: {}",run.stdout);let result=result_json(&dir,&run);assert_map_summary(&normal,&result);let m=answer(&result,"m");
        assert_eq!(s(get(m,"status")),if code==0 {"established"} else if code==1 {"refuted"} else {"undetermined"});assert_eq!(s(get(answer(&result,"same"),"status")),"established");assert_eq!(has(get(m,"outputs"),"map"),code==0);
        if code==0 {let map=value(&result,get(get(m,"outputs"),"map"));let transport=value(&result,&arr(get(map,"transports"))[0]);let clause=&arr(get(transport,"clauses"))[1];
            let target=value(&result,get(clause,"target"));let span=arr(get(get(target,"location"),"span"));let law=std::fs::read(dir.join("l.law")).unwrap();assert_eq!(&law[num(&span[0]) as usize..num(&span[1]) as usize],th.as_bytes());
            let q=&arr(get(value(&result,get(clause,"commutes")),"quantifiers"))[0];let domain=value(&result,get(q,"domain"));assert_eq!(arr(get(domain,"elements")).len(),3);
        }
        if code==1 {let examples=arr(get(m,"counterexamples"));assert!(!examples.is_empty());if missing {assert!(examples.iter().any(|e|{let data=get(value(&result,e),"data");s(value(&result,get(data,"left")))=="0"&&s(value(&result,get(data,"right")))=="1"}));}}
        if missing {assert!(arr(get(m,"reasons")).iter().any(|r|s(get(r,"code"))=="missing_observation"&&!arr(get(r,"missing")).is_empty()));}
        if collision {assert!(arr(get(m,"reasons")).iter().any(|r|s(get(r,"code"))=="unsupported_algorithm"));}
        args.extend(["--out","again","--reuse","out"]);let reused=cli::run(&dir,&args);assert_eq!(reused.code,code,"{mode}: {}",reused.stdout);let again=result_json(&dir,&reused);assert!(warnings(&again).is_empty());for key in ["answers","nodes"] {assert_eq!(get(&result,key).value,get(&again,key).value,"{mode}: {key}");}
    }
}

#[test]
fn change_transport_checks_later_integer_directions_and_reverse_guard_inclusion() {
    for (mode, source_params, target_params, guard, left, right, expected_parameter) in [
        ("second-direction", "n:Z,m:Z", "k:Z,l:Z", "", "n", "k+l", "1"),
        ("integer-reverse", "n:Z", "k:Z", " when n=0", "0", "0", "1"),
        ("finite-reverse", "n:Bool", "k:Bool", " when n", "0", "0", "false"),
    ] {
        let dir=finite_view_inputs(&format!("change-audit-{mode}"),true);
        let vocabulary=r#"use vocabulary Reservations version "1" digest "sha256:8427a2712c22d6eed1cdd5f48258bea102904173558a7087bb82c7d95665c9ff";"#;
        std::fs::write(dir.join("l.law"),format!(r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{vocabulary} change tune(s:State,{source_params}){guard}=s with {{free={left}}};}}
reading After {{{vocabulary} change tune(t:State,{target_params})=t with {{free={right}}};}}"#)).unwrap();
        let requests=["m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)","same=compare($m.operation,to=$m.operation,kind=action)","n=needed($m)"];
        let mut args=vec!["run","--atom-definition","d.json","--law","l.law","--archmap","a.json"];
        for request in requests {args.extend(["--ask",request]);}
        let normal=without_file_changes(&dir,||cli::run(&dir,&args));assert_eq!(normal.code,1,"{mode}: {}",normal.stdout);assert!(normal.stderr.is_empty());
        let run=asks(&dir,&requests);assert_eq!(run.code,1,"{mode}: {}",run.stdout);let result=result_json(&dir,&run);assert_map_summary(&normal,&result);let m=answer(&result,"m");
        assert_eq!(s(get(m,"status")),"refuted");assert!(!has(get(m,"outputs"),"map"));assert_eq!(s(get(answer(&result,"same"),"status")),"established");
        let examples=arr(get(m,"counterexamples"));assert!(!examples.is_empty());let data=get(value(&result,&examples[0]),"data");let bindings=arr(get(data,"bindings"));
        assert_eq!(s(get(&bindings[1],"name")),"n");
        if mode=="second-direction" {
            assert_eq!(bindings.len(),3);assert_eq!(s(value(&result,get(&bindings[1],"value"))),"0");assert_eq!(s(get(&bindings[2],"name")),"m");
            assert_eq!(s(value(&result,get(&bindings[2],"value"))),expected_parameter);
            assert_eq!(s(value(&result,get(data,"left"))),"0");assert_eq!(s(value(&result,get(data,"right"))),"1");
        } else {
            assert_eq!(bindings.len(),2);
            if mode=="integer-reverse" {assert_eq!(s(value(&result,get(&bindings[1],"value"))),expected_parameter);} else {assert_json(value(&result,get(&bindings[1],"value")),expected_parameter);}
            assert_json(value(&result,get(data,"left")),"false");assert_json(value(&result,get(data,"right")),"true");
        }
        let plan=value(&result,get(get(answer(&result,"n"),"outputs"),"plan"));assert!(arr(get(plan,"requirements")).is_empty());
        args.extend(["--out","again","--reuse","out"]);let reused=cli::run(&dir,&args);assert_eq!(reused.code,1,"{mode}: {}",reused.stdout);let again=result_json(&dir,&reused);assert!(warnings(&again).is_empty());for key in ["answers","nodes"] {assert_eq!(get(&result,key).value,get(&again,key).value,"{mode}: {key}");}
    }
}

#[test]
fn unconditional_local_guards_preserve_reads_and_following_operations() {
    for (mode, source_guard, target_guard) in [
        ("source", " when true", ""),
        ("target", "", " when (true)"),
        ("both", " when (true)", " when ((true))"),
        ("boolean", " when not false", " when (true and true)"),
        (
            "let",
            " when let yes=true in yes",
            " when if true then true else false",
        ),
        ("parameters", " when s.free>0", " when t.free>0"),
    ] {
        let dir = finite_view_inputs(&format!("local-true-guard-{mode}"), true);
        let vocabulary = r#"use vocabulary Reservations version "1" digest "sha256:8427a2712c22d6eed1cdd5f48258bea102904173558a7087bb82c7d95665c9ff";"#;
        std::fs::write(
            dir.join("l.law"),
            format!(
                r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{vocabulary} local here(s:State){source_guard} reads (s),s.free;}}
reading After {{{vocabulary} local here(t:State){target_guard} reads t,(t.free);}}"#
            ),
        )
        .unwrap();
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
        let normal = cli::run(&dir, &args);
        assert_eq!(normal.code, 0, "{}", normal.stdout);
        assert!(normal.stderr.is_empty());
        assert!(normal.stdout.len() < 1000);
        assert_eq!(std::fs::read_dir(&dir).unwrap().count(), 3);
        let run = asks(&dir, &requests);
        assert_eq!(run.code, 0, "{}", run.stdout);
        let result = result_json(&dir, &run);
        for id in ["m", "same", "n"] {
            assert_eq!(s(get(answer(&result, id), "status")), "established");
        }
        let map = value(&result, get(get(answer(&result, "m"), "outputs"), "map"));
        let transport = value(&result, &arr(get(map, "transports"))[0]);
        let clauses = arr(get(transport, "clauses"));
        assert_eq!(clauses.len(), 2);
        assert_local_clause(
            &dir,
            &result,
            &clauses[0],
            "(s)",
            "t",
            &[("s", "Reservations.State")],
        );
        assert_local_clause(
            &dir,
            &result,
            &clauses[1],
            "s.free",
            "(t.free)",
            &[("s", "Reservations.State")],
        );
        assert_reference_pairs(
            &result,
            value(&result, get(&clauses[0], "values")),
            &[
                ("p", "r"),
                ("q", "s"),
                ("r", "r"),
                ("s", "s"),
                ("u", "w"),
                ("w", "w"),
            ],
        );
        assert_json(
            get(value(&result, get(&clauses[1], "values")), "source_type"),
            r#""Z""#,
        );
        args.extend(["--out", "again", "--reuse", "out"]);
        let reused = cli::run(&dir, &args);
        assert_eq!(reused.code, 0, "{}", reused.stdout);
        let again = result_json(&dir, &reused);
        assert!(warnings(&again).is_empty());
        assert_eq!(get(&result, "answers").value, get(&again, "answers").value);
        assert_eq!(get(&result, "nodes").value, get(&again, "nodes").value);
    }
}

#[test]
fn local_guard_domains_preserve_source_rows_and_keep_unknown_distinct() {
    for (mode, source, target, read, preserve, missing, code, status) in [
        ("expansion", "s.free=2", "t.free>0", "field", true, "", 0, "established"),
        ("reference-expansion", "s.free=2", "t.free>0", "reference", false, "", 0, "established"),
        ("empty", "false", "false", "field", false, "", 0, "established"),
        ("guard-refuted", "s.free=2", "t.free=1", "reference", true, "", 1, "refuted"),
        ("value-refuted", "s.free=2", "t.free>0", "field", false, "", 1, "refuted"),
        ("source-missing", "s.free=2", "true", "reference", true, "p", 2, "undetermined"),
        ("target-missing", "true", "t.free>0", "reference", true, "r", 2, "undetermined"),
        ("inactive-missing", "false", "t.free>0", "field", true, "r", 0, "established"),
        ("tuple-refuted", "a.free=1 and s.free=2", "b.free>0 and t.free>0", "field", false, "", 1, "refuted"),
    ] {
        let dir = finite_view_inputs(&format!("local-domain-{mode}"), preserve);
        let vocabulary = r#"use vocabulary Reservations version "1" digest "sha256:8427a2712c22d6eed1cdd5f48258bea102904173558a7087bb82c7d95665c9ff";"#;
        let (sp, tp) = if mode == "tuple-refuted" { ("a:State,s:State", "b:State,t:State") } else { ("s:State", "t:State") };
        let (sr, tr) = if read == "reference" { ("s", "t") } else { ("s.free", "t.free") };
        std::fs::write(dir.join("l.law"), format!(r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{vocabulary} local here({sp}) when {source} reads {sr};}}
reading After {{{vocabulary} local here({tp}) when {target} reads {tr};}}"#)).unwrap();
        if !missing.is_empty() {
            let text = std::fs::read_to_string(dir.join("a.json")).unwrap();
            // target欠測の前像に既知Atomを残すと、localより前のConfigurationMapが未決になる。
            let text = text.lines().filter(|line| !line.contains(&format!(r#""id":"{missing}-free""#))
                && !(missing == "r" && line.contains(r#""id":"p-free""#))).collect::<Vec<_>>().join("\n");
            std::fs::write(dir.join("a.json"), text).unwrap();
        }
        let requests = [
            "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
            "same=compare($m.operation,to=$m.operation,kind=action)",
            "n=needed($m)",
        ];
        let mut args = vec!["run", "--atom-definition", "d.json", "--law", "l.law", "--archmap", "a.json"];
        for request in requests { args.extend(["--ask", request]); }
        let normal = without_file_changes(&dir, || cli::run(&dir, &args));
        assert_eq!(normal.code, code, "{mode}: {}", normal.stdout);
        assert!(normal.stderr.is_empty());
        assert!(normal.stdout.len() < 1500);
        let run = asks(&dir, &requests);
        assert_eq!(run.code, code, "{mode}: {}", run.stdout);
        let result = result_json(&dir, &run);
        let m = answer(&result, "m");
        assert_eq!(s(get(m, "status")), status, "{mode}");
        assert_eq!(s(get(answer(&result, "same"), "status")), "established", "{mode}");
        assert_eq!(has(get(m, "outputs"), "map"), code == 0);
        if code == 0 {
            let map = value(&result, get(get(m, "outputs"), "map"));
            let transport = value(&result, &arr(get(map, "transports"))[0]);
            let clause = &arr(get(transport, "clauses"))[0];
            let arguments = value(&result, get(clause, "arguments"));
            assert_eq!(reference_pairs(&result, arguments).len(), 6);
        }
        if code == 1 {
            let examples = arr(get(m, "counterexamples"));
            assert!(!examples.is_empty());
            let data = get(value(&result, &examples[0]), "data");
            if mode == "guard-refuted" {
                assert_json(value(&result, get(data, "left")), "true");
                assert_json(value(&result, get(data, "right")), "false");
            } else {
                assert_eq!(s(value(&result, get(data, "left"))), "2");
                assert_eq!(s(value(&result, get(data, "right"))), "4");
            }
            if mode == "tuple-refuted" {
                let bindings = arr(get(data, "bindings"));
                assert_eq!(bindings.len(), 2);
                for (binding, name, subject) in [(&bindings[0], "a", "q"), (&bindings[1], "s", "p")] {
                    assert_eq!(s(get(binding, "name")), name);
                    assert_eq!(s(&arr(value(&result, get(binding, "value")))[1]), subject);
                }
            }
        }
        if code == 2 {
            let plan = value(&result, get(get(answer(&result, "n"), "outputs"), "plan"));
            assert!(arr(get(plan, "requirements")).iter().any(|r| s(get(get(r, "field"), "subject")) == missing));
        }
        args.extend(["--out", "again", "--reuse", "out"]);
        let reused = cli::run(&dir, &args);
        assert_eq!(reused.code, code, "{mode}: {}", reused.stdout);
        let again = result_json(&dir, &reused);
        assert!(warnings(&again).is_empty());
        for key in ["answers", "nodes"] { assert_eq!(get(&result, key).value, get(&again, key).value, "{mode}: {key}"); }
    }
}

#[test]
fn incomplete_endpoint_algebras_keep_configuration_operation_and_original_reasons() {
    for (mode, code, status) in [
        ("refuted", 1, "refuted"),
        ("unsupported", 2, "undetermined"),
    ] {
        let dir = finite_view_inputs(&format!("endpoint-algebra-{mode}"), true);
        let old_digest = "sha256:8427a2712c22d6eed1cdd5f48258bea102904173558a7087bb82c7d95665c9ff";
        if mode == "refuted" {
            let definition = std::fs::read_to_string(dir.join("d.json")).unwrap().replace(r#"{"name": "free", "type": "Z""#, r#"{"name":"peer","type":["Ref","Reservations.State"],"meaning":"参照先。"}, {"name": "free", "type": "Z""#);
            let checked =
                archsig::definition::check_definitions(&[("d", definition.as_bytes())]).unwrap();
            let digest = &checked.vocabularies["Reservations"].digest;
            std::fs::write(dir.join("d.json"), definition).unwrap();
            let mut a = std::fs::read_to_string(dir.join("a.json"))
                .unwrap()
                .replace(old_digest, digest);
            let mut facts = String::new();
            for (subject, peer) in [
                ("p", "q"),
                ("q", "p"),
                ("r", "s"),
                ("s", "r"),
                ("u", "u"),
                ("w", "w"),
            ] {
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
        assert_eq!(normal.code, code, "{}", normal.stdout);
        assert!(normal.stderr.is_empty());

        assert_eq!(std::fs::read_dir(&dir).unwrap().count(), 3);
        let run = asks(&dir, &requests);
        assert_eq!(run.code, code, "{}", run.stdout);
        let result = result_json(&dir, &run);
        assert_map_summary(&normal, &result);
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
        args.extend(["--out", "again", "--reuse", "out"]);
        let reused = cli::run(&dir, &args);
        assert_eq!(reused.code, code, "{}", reused.stdout);
        let again = result_json(&dir, &reused);
        assert!(warnings(&again).is_empty());
        assert_eq!(get(&result, "answers").value, get(&again, "answers").value);
        assert_eq!(get(&result, "nodes").value, get(&again, "nodes").value);
    }
}

#[test]
fn local_reference_fields_follow_the_map_instead_of_raw_equality() {
    for (mode, code, status) in [
        ("preserved", 0, "established"),
        ("changed", 1, "refuted"),
        ("identity-missing", 0, "established"),
    ] {
        let dir = finite_view_inputs(&format!("local-reference-field-{mode}"), true);
        let old = std::fs::read_to_string(dir.join("d.json")).unwrap();
        let definition = old.replace(r#"{"name": "free", "type": "Z""#, r#"{"name":"other","type":["Ref","Reservations.State"],"meaning":"別の参照先。"}, {"name":"peer","type":["Ref","Reservations.State"],"meaning":"参照先。"}, {"name": "free", "type": "Z""#);
        let checked =
            archsig::definition::check_definitions(&[("d", definition.as_bytes())]).unwrap();
        let digest = &checked.vocabularies["Reservations"].digest;
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
            ("u", "u"),
            ("w", "w"),
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
        a = a
            .lines()
            .filter(|line| {
                !line.contains("\"type\":\"Reservations.Reserve\"")
                    && !line.contains("\"subject\":\"e\"")
                    && !line.contains("\"subject\":\"f\"")
            })
            .collect::<Vec<_>>()
            .join("\n")
            .replace("[[[\"v\",\"e\"],[\"v\",\"f\"]]]", "[]");
        if mode == "identity-missing" {
            a = a.replace("[[[\"v\",\"p\"],[\"v\",\"r\"]],[[\"v\",\"q\"],[\"v\",\"s\"]],[[\"v\",\"u\"],[\"v\",\"w\"]]]", "[[[\"v\",\"p\"],[\"v\",\"p\"]],[[\"v\",\"q\"],[\"v\",\"q\"]],[[\"v\",\"u\"],[\"v\",\"u\"]]]")
                .replace(r#""id":"m-to","subject":"m","field":"Reservations.Migration.to","value":["v","B"]"#, r#""id":"m-to","subject":"m","field":"Reservations.Migration.to","value":["v","A"]"#)
                .replace("\"subjects\":[", r#""subjects":[{"id":"C","type":"Reservations.System","origin":"model"},{"id":"x","type":"Reservations.State","origin":"model"},"#)
                .replace("\"atoms\":[", r#""atoms":[{"id":"x-owner","subject":"x","field":"Reservations.State.owner","value":["v","C"],"origin":"model"},"#);
        }
        std::fs::write(dir.join("a.json"), a).unwrap();
        let target_field = if mode == "changed" { "other" } else { "peer" };
        std::fs::write(dir.join("l.law"), format!(r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{use vocabulary Reservations version "1" digest "{digest}"; local here(s:State) reads s.peer;}}
reading After {{use vocabulary Reservations version "1" digest "{digest}"; local here(t:State) reads (t.{target_field});}}"#)).unwrap();
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
        assert_eq!(normal.code, code, "{}", normal.stdout);
        assert!(normal.stderr.is_empty());

        assert_eq!(std::fs::read_dir(&dir).unwrap().count(), 3);
        let run = asks(&dir, &requests);
        assert_eq!(run.code, code, "{}", run.stdout);
        let result = result_json(&dir, &run);
        assert_map_summary(&normal, &result);
        assert_eq!(s(get(answer(&result, "m"), "status")), status);
        assert_eq!(s(get(answer(&result, "same"), "status")), "established");
        let outputs = get(answer(&result, "m"), "outputs");
        assert_eq!(has(outputs, "map"), mode != "changed");
        if mode != "changed" {
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
            if mode == "identity-missing" {
                assert_reference_pairs(
                    &result,
                    value(&result, get(clause, "values")),
                    &[
                        ("p", "p"),
                        ("q", "q"),
                        ("r", "r"),
                        ("s", "s"),
                        ("u", "u"),
                        ("w", "w"),
                        ("x", "x"),
                    ],
                );
                let plan = value(&result, get(get(answer(&result, "n"), "outputs"), "plan"));
                assert!(arr(get(plan, "requirements")).is_empty());
            } else {
                assert_reference_pairs(
                    &result,
                    value(&result, get(clause, "values")),
                    &[
                        ("p", "r"),
                        ("q", "s"),
                        ("r", "r"),
                        ("s", "s"),
                        ("u", "w"),
                        ("w", "w"),
                    ],
                );
            }
        } else if mode == "changed" {
            let examples = arr(get(answer(&result, "m"), "counterexamples"));
            let data = get(value(&result, &examples[0]), "data");
            assert_json(value(&result, get(data, "left")), r#"["v","p"]"#);
            assert_json(value(&result, get(data, "right")), r#"["v","s"]"#);
        }
        args.extend(["--out", "again", "--reuse", "out"]);
        let reused = cli::run(&dir, &args);
        assert_eq!(reused.code, code, "{}", reused.stdout);
        let again = result_json(&dir, &reused);
        assert!(warnings(&again).is_empty());
        assert_eq!(get(&result, "nodes").value, get(&again, "nodes").value);
        assert_eq!(get(&result, "answers").value, get(&again, "answers").value);
    }
}

#[test]
fn local_scalar_field_reads_keep_preservation_refutation_and_missing_distinct() {
    for (mode, preserve, missing, code, status) in [
        ("preserved", true, false, 0, "established"),
        ("changed", false, false, 1, "refuted"),
        ("missing", true, true, 2, "undetermined"),
    ] {
        let dir = finite_view_inputs(&format!("local-field-{mode}"), preserve);
        let vocabulary = r#"use vocabulary Reservations version "1" digest "sha256:8427a2712c22d6eed1cdd5f48258bea102904173558a7087bb82c7d95665c9ff";"#;
        std::fs::write(
            dir.join("l.law"),
            format!(
                r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{vocabulary} local here(root:System,s:State) when (s.free=s.free) and (root=root) reads s.free;}}
reading After {{{vocabulary} local here(world:System,t:State) when t.free=t.free reads (t.free);}}"#
            ),
        )
        .unwrap();
        if missing {
            let a=std::fs::read_to_string(dir.join("a.json")).unwrap().replace("{\"id\":\"p-free\",\"subject\":\"p\",\"field\":\"Reservations.State.free\",\"value\":\"2\",\"origin\":\"model\"},\n","");
            std::fs::write(dir.join("a.json"), a).unwrap();
        }
        let requests = [
            "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
            "same=compare($m.operation,to=$m.operation,kind=action)",
            "n=needed($m)",
        ];
        let before =
            ["d.json", "l.law", "a.json"].map(|name| std::fs::read(dir.join(name)).unwrap());
        let mut normal_args = vec![
            "run",
            "--atom-definition",
            "d.json",
            "--law",
            "l.law",
            "--archmap",
            "a.json",
        ];
        for request in requests {
            normal_args.extend(["--ask", request]);
        }
        let normal = cli::run(&dir, &normal_args);
        assert_eq!(normal.code, code, "{}", normal.stdout);
        assert!(normal.stderr.is_empty());
        assert!(!has(&normal.receipt, "result"));
        assert!(!has(&normal.receipt, "nodes"));
        assert_eq!(std::fs::read_dir(&dir).unwrap().count(), 3);
        for (name, bytes) in ["d.json", "l.law", "a.json"].into_iter().zip(before) {
            assert_eq!(std::fs::read(dir.join(name)).unwrap(), bytes);
        }
        eprintln!("scalar local {mode}: stdout {} bytes", normal.stdout.len());
        let run = asks(&dir, &requests);
        assert_eq!(run.code, code, "{}", run.stdout);
        let result = result_json(&dir, &run);
        assert_eq!(s(get(answer(&result, "m"), "status")), status);
        assert_eq!(s(get(answer(&result, "same"), "status")), "established");
        assert_eq!(
            has(get(answer(&result, "m"), "outputs"), "map"),
            preserve && !missing
        );
        if preserve && !missing {
            let map = value(&result, get(get(answer(&result, "m"), "outputs"), "map"));
            let transport = value(&result, &arr(get(map, "transports"))[0]);
            assert_json(
                get(transport, "parameters"),
                r#"[["root","world"],["s","t"]]"#,
            );
            let clauses = arr(get(transport, "clauses"));
            assert_eq!(clauses.len(), 1);
            assert_local_clause(
                &dir,
                &result,
                &clauses[0],
                "s.free",
                "(t.free)",
                &[("root", "Reservations.System"), ("s", "Reservations.State")],
            );
            let values = value(&result, get(&clauses[0], "values"));
            for key in ["source_type", "target_type"] {
                assert_json(get(values, key), r#""Z""#);
            }
        }
        if !preserve {
            let examples = arr(get(answer(&result, "m"), "counterexamples"));
            assert_eq!(examples.len(), 1);
            let data = get(value(&result, &examples[0]), "data");
            assert_eq!(s(value(&result, get(data, "left"))), "2");
            assert_eq!(s(value(&result, get(data, "right"))), "4");
            let bindings = arr(get(data, "bindings"));
            assert_eq!(bindings.len(), 2);
            for (binding, (name, subject)) in bindings.iter().zip([("root", "A"), ("s", "p")]) {
                assert_eq!(s(get(binding, "name")), name);
                assert_eq!(
                    arr(value(&result, get(binding, "value")))
                        .iter()
                        .map(s)
                        .collect::<Vec<_>>(),
                    ["v", subject]
                );
            }
        }
        if missing {
            let plan = value(&result, get(get(answer(&result, "n"), "outputs"), "plan"));
            assert!(arr(get(plan, "requirements")).iter().any(|r| s(get(
                get(r, "field"),
                "subject"
            )) == "p"
                && s(get(get(r, "field"), "field")) == "Reservations.State.free"));
        }
        let mut args = vec![
            "run",
            "--atom-definition",
            "d.json",
            "--law",
            "l.law",
            "--archmap",
            "a.json",
            "--out",
            "again",
            "--reuse",
            "out",
        ];
        for request in requests {
            args.extend(["--ask", request]);
        }
        let reused = cli::run(&dir, &args);
        assert_eq!(reused.code, code, "{}", reused.stdout);
        let again = result_json(&dir, &reused);
        assert!(warnings(&again).is_empty());
        for key in ["answers", "nodes"] {
            assert_eq!(get(&result, key).value, get(&again, key).value);
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
    let before=["d.json","l.law","a.json"].map(|name|std::fs::read(dir.join(name)).unwrap());
    let normal=cli::run(&dir,&["run","--atom-definition","d.json","--law","l.law","--archmap","a.json","--ask",request]);
    assert_eq!(normal.code,0,"{}",normal.stdout);
    assert!(normal.stderr.is_empty());
    assert!(!has(&normal.receipt,"nodes"));
    assert!(!has(&normal.receipt,"result"));
    assert_eq!(std::fs::read_dir(&dir).unwrap().count(),3);
    for (name,bytes) in ["d.json","l.law","a.json"].into_iter().zip(before) {assert_eq!(std::fs::read(dir.join(name)).unwrap(),bytes);}
    eprintln!("multiple local map stdout {} bytes",normal.stdout.len());
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
    let reused=cli::run(&dir,&["run","--atom-definition","d.json","--law","l.law","--archmap","a.json","--out","again","--reuse","out","--ask",request]);
    assert_eq!(reused.code,0,"{}",reused.stdout);
    let again=result_json(&dir,&reused);
    assert!(warnings(&again).is_empty());
    for key in ["answers","nodes"] {assert_eq!(get(&result,key).value,get(&again,key).value);}
}

#[test]
fn local_reference_reads_are_transported_by_the_actual_configuration_map() {
    let dir = inputs("local-reference-transport");
    let law = std::fs::read_to_string(dir.join("l.law")).unwrap();
    let at = law.rfind('}').unwrap();
    let mut law = law;
    law.insert_str(at, "local here(s:State) reads s;\n");
    law.push_str("reading Other {use vocabulary Reservations version \"1\" digest \"sha256:8427a2712c22d6eed1cdd5f48258bea102904173558a7087bb82c7d95665c9ff\";local here(t:State) reads (t);}");
    std::fs::write(dir.join("l.law"), law).unwrap();
    let request = "m=map(Reservations.Migration,on=@v/m,reading=Alternative,to_reading=Other,kind=object_algebra)";
    let before = ["d.json","l.law","a.json"].map(|name|std::fs::read(dir.join(name)).unwrap());
    let normal = cli::run(&dir, &["run","--atom-definition","d.json","--law","l.law","--archmap","a.json","--ask",request]);
    assert_eq!(normal.code, 0, "{}", normal.stdout);
    assert!(normal.stderr.is_empty());
    assert_eq!(std::fs::read_dir(&dir).unwrap().count(), 3);
    assert!(!has(&normal.receipt,"nodes"));
    assert!(!has(&normal.receipt,"result"));
    for (name,bytes) in ["d.json","l.law","a.json"].into_iter().zip(before) {assert_eq!(std::fs::read(dir.join(name)).unwrap(),bytes);}
    eprintln!("local map stdout {} bytes",normal.stdout.len());
    let run = asks(&dir, &[request]);
    assert_eq!(run.code, 0, "{}", run.stdout);
    let result = result_json(&dir, &run);
    let map = value(&result, get(get(answer(&result, "m"), "outputs"), "map"));
    assert_eq!(arr(get(map, "transports")).len(), 1);
    let transport = value(&result,&arr(get(map,"transports"))[0]);
    assert_eq!(s(get(transport,"kind")),"local");
    assert_eq!(s(get(transport,"source")),"Alternative.here");
    assert_eq!(s(get(transport,"target")),"Other.here");
    assert_json(get(transport,"parameters"), r#"[["s","t"]]"#);
    let clauses = arr(get(transport,"clauses"));
    assert_eq!(clauses.len(),1);
    let values = value(&result,get(&clauses[0],"values"));
    assert_reference_pairs(&result,values,&[("p","r"),("q","s"),("r","r"),("s","s")]);
    assert_local_clause(&dir,&result,&clauses[0],"s","(t)",&[("s","Reservations.State")]);
    // 非恒等対が残っていても、pの誤った行き先は拒否する。
    let pairs = arr(get(values,"subjects"));
    let pair = pairs.iter().find(|pair| s(&arr(value(&result,&arr(pair)[0]))[1]) == "p").unwrap();
    let target = s(get(&arr(pair)[1],"node")).to_owned();
    let mut wrong = result_json(&dir,&run);
    if let archsig::json::JValue::Obj(fields) = &mut wrong.value {
        let nodes = &mut fields.iter_mut().find(|(key,_)| key == "nodes").unwrap().1;
        if let archsig::json::JValue::Arr(nodes) = &mut nodes.value {
            let target = nodes.iter_mut().find(|n| s(get(n,"id")) == target).unwrap();
            if let archsig::json::JValue::Obj(fields) = &mut target.value {
                let scalar = &mut fields.iter_mut().find(|(key,_)| key == "value").unwrap().1;
                if let archsig::json::JValue::Arr(pair) = &mut scalar.value {
                    pair[1].value = archsig::json::JValue::Str("q".into());
                } else {panic!("参照値ではない");}
            }
        }
    }
    assert!(std::panic::catch_unwind(|| assert_reference_pairs(&wrong,values,&[("p","r"),("q","s"),("r","r"),("s","s")])).is_err());

    let again = cli::run(&dir,&["run","--atom-definition","d.json","--law","l.law","--archmap","a.json","--out","again","--reuse","out","--ask",request]);
    assert_eq!(again.code,0,"{}",again.stdout);
    let again = result_json(&dir,&again);
    assert!(warnings(&again).is_empty());
    for key in ["answers","nodes"] {assert_eq!(get(&result,key).value,get(&again,key).value);}
}

#[test]
fn object_map_keeps_all_objects_generators_and_public_source_consumption() {
    let dir = inputs("public-object-map");
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
    assert_eq!(arr(get(map, "operation_maps")).len(), 3);
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
        assert_eq!(arr(get(get(algebra, "operations"), "generators")).len(), 3);
    }
    for (from, to) in [
        ("d.json", "inputs/definitions/0.json"),
        ("a.json", "inputs/archmap.json"),
        ("l.law", "inputs/law.law"),
    ] {
        assert_eq!(
            std::fs::read(dir.join(from)).unwrap(),
            std::fs::read(dir.join("out").join(to)).unwrap()
        );
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
fn mapped_target_drives_named_reading_build_evaluation_and_check() {
    let dir = inputs("public-object-map-target");
    std::fs::write(
        dir.join("a.json"),
        include_bytes!("fixtures/object-configuration-map.archmap.json"),
    )
    .unwrap();
    let run = asks(
        &dir,
        &[
            "m=map(Reservations.Migration,on=@v/m,reading=Alternative,kind=object_algebra)",
            "b=build(Reservations,on=$m.map.target.base.subject)",
            "n=evaluate(Reservations.holdings,on=$b.object,s=@v/r)",
            "ok=check(Reservations.conserved,on=$b.object,e=@v/f)",
        ],
    );
    assert_eq!(run.code, 0, "{}", run.stdout);
    let result = result_json(&dir, &run);
    for id in ["m", "b", "n", "ok"] {
        assert_eq!(s(get(answer(&result, id), "status")), "established");
    }
    let map = value(&result, get(get(answer(&result, "m"), "outputs"), "map"));
    assert_eq!(arr(get(map, "object_maps")).len(), 4);
    assert_eq!(arr(get(map, "operation_maps")).len(), 1);
    let n = value(&result, get(get(answer(&result, "n"), "outputs"), "value"));
    assert_eq!(arr(n).iter().map(s).collect::<Vec<_>>(), ["4", "0"]);
    let component = value(&result, get(&arr(get(map, "object_maps"))[0], "target"));
    let subject = value(&result, get(component, "subject"));
    assert_eq!(arr(subject).iter().map(s).collect::<Vec<_>>(), ["v", "B"]);
    for row in arr(get(map, "operation_maps")) {
        let proposition = value(&result, get(row, "naturality"));
        assert_eq!(s(get(proposition, "predicate")), "naturality");
        let operands = arr(get(proposition, "operands"));
        let lhs = value(&result, &operands[0]);
        let rhs = value(&result, &operands[1]);
        assert_eq!(get(lhs, "images"), get(rhs, "images"));
        assert_eq!(arr(get(lhs, "images")).len(), 39);
    }
    std::fs::remove_dir_all(dir).unwrap();
}

#[test]
fn reuse_recomputes_object_maps_and_rejects_an_omitted_object() {
    let dir = inputs("public-object-map-reuse");
    let request = "m=map(Reservations.Migration,on=@v/m,reading=Alternative,kind=object_algebra)";
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
                "--time-ms",
                "120000",
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
    assert_eq!(arr(get(map, "object_maps")).len(), 3);
    std::fs::remove_dir_all(dir).unwrap();
}

#[test]
fn interruption_during_additional_transport_keeps_the_checked_operation() {
    use archsig::observed::{
        control::{Checkpoint, Control, Limits, Usage},
        evaluate_observed_bytes,
        input::InputSources,
    };
    use archsig::result::Signal;
    for mode in 0..4 {
        let mut control = Control::new(
            Limits {
                time_ms: (mode == 0).then_some(1),
                memory_mib: (mode == 1).then_some(1),
            },
            move |p| {
                let stop = p == Checkpoint::ConfigurationTransportGenerator;
                Usage {
                    elapsed_ms: u128::from(stop && mode == 0),
                    memory_mib: u128::from(stop && mode == 1),
                    signal: if stop {
                        match mode {
                            2 => Some(Signal::Int),
                            3 => Some(Signal::Term),
                            _ => None,
                        }
                    } else {
                        None
                    },
                }
            },
        );
        let result = evaluate_observed_bytes(
            InputSources::from_bytes(
                vec![include_bytes!("fixtures/reservations.atoms.json").to_vec()],
                include_bytes!("fixtures/public-compose.law").to_vec(),
                include_bytes!("fixtures/configuration-operation.archmap.json").to_vec(),
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
}

#[test]
fn closed_law_map_preserves_refutations_all_components_and_following_checks() {
    let dir = inputs("public-closed-law-map");
    std::fs::write(
        dir.join("a.json"),
        include_bytes!("fixtures/object-configuration-map.archmap.json"),
    )
    .unwrap();
    std::fs::write(dir.join("l.law"), r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Alternative {
use vocabulary Reservations version "1" digest "sha256:8427a2712c22d6eed1cdd5f48258bea102904173558a7087bb82c7d95665c9ff";
law required zero(s: State): (s.free, s.held) = (0, 0);
}"#).unwrap();
    let run = asks_with_limit(
        &dir,
        &[
            "m=map(Reservations.Migration,on=@v/m,reading=Alternative,kind=object_algebra)",
            "b=build(Alternative,on=$m.map.target.base.subject)",
            "bad=check(Alternative.zero,on=$b.object,s=@v/r)",
            "base=map(Reservations.Migration,on=@v/m,reading=Alternative)",
            "same=compare($m.operation,to=$base.operation,kind=action)",
        ],
        "360000",
    );
    assert_eq!(run.code, 1, "{}", run.stdout);
    let result = result_json(&dir, &run);
    assert_eq!(s(get(&result, "status")), "complete");
    for id in ["m", "b", "base", "same"] {
        assert_eq!(s(get(answer(&result, id), "status")), "established");
    }
    assert_eq!(s(get(answer(&result, "bad"), "status")), "refuted");
    let map = value(&result, get(get(answer(&result, "m"), "outputs"), "map"));
    let equations = value(&result, get(map, "equations"));
    assert_eq!(arr(get(equations, "indices")).len(), 3);
    for row in arr(get(equations, "indices")) {
        assert_eq!(arr(get(row, "holds")).len(), 4);
        assert_eq!(arr(get(row, "components")).len(), 2);
        for component in arr(get(row, "components")) {
            assert_eq!(arr(get(component, "zeros")).len(), 4);
        }
    }
    assert_eq!(arr(get(map, "circuits")).len(), 6);
    assert_eq!(arr(get(map, "invariants")).len(), 3);
    assert!(
        arr(get(map, "circuits"))
            .iter()
            .any(|r| !arr(get(value(&result, r), "cases")).is_empty())
    );
    std::fs::remove_dir_all(dir).unwrap();
}

#[test]
fn closed_law_map_refutes_changed_truth_without_losing_operation() {
    let dir = inputs("public-closed-law-map-refuted");
    std::fs::write(
        dir.join("a.json"),
        include_bytes!("fixtures/object-configuration-map.archmap.json"),
    )
    .unwrap();
    let uses = r#"use vocabulary Reservations version "1" digest "sha256:8427a2712c22d6eed1cdd5f48258bea102904173558a7087bb82c7d95665c9ff";"#;
    std::fs::write(
        dir.join("l.law"),
        format!(
            r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{uses} law required zero(s:State):s.free=0;}}
reading After {{{uses} law required zero(s:State):s.free=4;}}"#
        ),
    )
    .unwrap();
    let run = asks_with_limit(
        &dir,
        &[
            "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
            "same=compare($m.operation,to=$m.operation,kind=action)",
            "why=needed($m)",
        ],
        "360000",
    );
    assert_eq!(run.code, 1, "{}", run.stdout);
    let result = result_json(&dir, &run);
    assert_eq!(s(get(&result, "status")), "complete");
    assert_eq!(s(get(answer(&result, "m"), "status")), "refuted");
    for id in ["same", "why"] {
        assert_eq!(s(get(answer(&result, id), "status")), "established");
    }
    let outputs = get(answer(&result, "m"), "outputs");
    assert!(has(outputs, "operation"));
    assert!(!has(outputs, "map"));
    // Lawの反証条件は、独立に成立する空SignatureMapの成立条件ではない。
    for n in arr(get(&result, "nodes")) {
        if matches!(&get(n, "type").value, archsig::json::JValue::Str(t) if t == "SignatureMap") {
            if has(n, "conditions") {
                assert!(arr(get(n, "conditions")).is_empty());
            }
        }
    }
    let result=internal_graph(&dir,&result);
    let predicates = arr(get(&result, "nodes"))
        .iter()
        .filter(|n| matches!(&get(n, "type").value, archsig::json::JValue::Str(t) if t == "Proposition"))
        .collect::<Vec<_>>();
    assert!(
        predicates.iter().any(
            |n| s(get(get(n, "value"), "predicate")) == "equation_holds_iff"
                && s(get(get(n, "judgment"), "status")) == "refuted"
        )
    );
    assert!(predicates.iter().any(
        |n| s(get(get(n, "value"), "predicate")) == "residual_zero_iff"
            && s(get(get(n, "judgment"), "status")) == "refuted"
    ));

    std::fs::remove_dir_all(dir).unwrap();
}

#[test]
fn closed_law_transport_stop_keeps_operation_without_claiming_a_map() {
    use archsig::observed::{
        control::{Checkpoint, Control, Limits, Usage},
        evaluate_observed_bytes,
        input::InputSources,
    };
    let law = r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Alternative {
use vocabulary Reservations version "1" digest "sha256:8427a2712c22d6eed1cdd5f48258bea102904173558a7087bb82c7d95665c9ff";
law required zero(s:State):s.free=0;
}"#;
    let mut control = Control::new(Limits::default(), |point| Usage {
        elapsed_ms: 0,
        memory_mib: 0,
        signal: (point == Checkpoint::ObjectLawCircuitTransport)
            .then_some(archsig::result::Signal::Term),
    });
    let result = evaluate_observed_bytes(
        InputSources::from_bytes(
            vec![include_bytes!("fixtures/reservations.atoms.json").to_vec()],
            law.as_bytes().to_vec(),
            include_bytes!("fixtures/object-configuration-map.archmap.json").to_vec(),
        ),
        &["m=map(Reservations.Migration,on=@v/m,reading=Alternative,kind=object_algebra)"],
        &mut control,
    )
    .unwrap();
    assert_eq!(result.status(), "interrupted");
    let result = archsig::json::parse(result.wire().canonical().as_bytes()).unwrap();
    let a = answer(&result, "m");
    assert_eq!(s(get(a, "status")), "undetermined");
    assert!(has(get(a, "outputs"), "operation"));
    assert!(!has(get(a, "outputs"), "map"));
    assert!(!has(get(a, "outputs"), "proposition"));
}

#[test]
fn equal_law_truth_does_not_hide_a_changed_zero_component() {
    let dir = inputs("public-law-map-component-refuted");
    std::fs::write(
        dir.join("a.json"),
        include_bytes!("fixtures/object-configuration-map.archmap.json"),
    )
    .unwrap();
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
    let run = asks_with_limit(
        &dir,
        &[
            "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
        ],
        "360000",
    );
    assert_eq!(run.code, 1, "{}", run.stdout);
    let result = result_json(&dir, &run);
    assert_eq!(s(get(&result, "status")), "complete");
    let a = answer(&result, "m");
    assert_eq!(s(get(a, "status")), "refuted");
    assert!(!has(get(a, "outputs"), "map"));
    let result=internal_graph(&dir,&result);
    let mut holds = 0;
    let mut nonzero = 0;
    for n in arr(get(&result, "nodes")) {
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
    assert_eq!(holds, 12);
    assert!(nonzero > 0);
    std::fs::remove_dir_all(dir).unwrap();
}

#[test]
fn closed_law_map_refutes_required_status_and_component_type_changes() {
    for (name, role, body) in [
        ("required", "optional", "s.free=0"),
        ("component-type", "required", "rat(2,1)=rat(0,1)"),
    ] {
        let dir = inputs(&format!("public-law-map-{name}"));
        std::fs::write(
            dir.join("a.json"),
            include_bytes!("fixtures/object-configuration-map.archmap.json"),
        )
        .unwrap();
        let uses = r#"use vocabulary Reservations version "1" digest "sha256:8427a2712c22d6eed1cdd5f48258bea102904173558a7087bb82c7d95665c9ff";"#;
        std::fs::write(
            dir.join("l.law"),
            format!(
                r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{uses} law required zero(s:State):s.free=0;}}
reading After {{{uses} law {role} zero(s:State):{body};}}"#
            ),
        )
        .unwrap();
        let run = asks_with_limit(
            &dir,
            &[
                "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
                "same=compare($m.operation,to=$m.operation,kind=action)",
            ],
            "360000",
        );
        assert_eq!(run.code, 1, "{name}: {}", run.stdout);
        let result = result_json(&dir, &run);
        assert_eq!(s(get(&result, "status")), "complete");
        assert_eq!(s(get(answer(&result, "m"), "status")), "refuted");
        assert!(!has(get(answer(&result, "m"), "outputs"), "map"));
        assert_eq!(s(get(answer(&result, "same"), "status")), "established");
        std::fs::remove_dir_all(dir).unwrap();
    }
}

#[test]
fn closed_view_map_preserves_option_values_all_axes_and_following_queries() {
    let dir = inputs("public-closed-view-map");
    // sourceの三つの異なる実観測値を、対応先でも保存する入力。
    // 元fixtureの数量が変わる移送は次の負系でそのまま検査する。
    let archmap = include_str!("fixtures/object-configuration-map.archmap.json")
        .replace(r#""id":"r-free","subject":"r","field":"Reservations.State.free","value":"4""#,
                 r#""id":"r-free","subject":"r","field":"Reservations.State.free","value":"2""#)
        .replace(r#""id":"s-free","subject":"s","field":"Reservations.State.free","value":"3""#,
                 r#""id":"s-free","subject":"s","field":"Reservations.State.free","value":"1""#);
    std::fs::write(dir.join("a.json"), archmap).unwrap();
    std::fs::write(dir.join("l.law"), r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Alternative {
use vocabulary Reservations version "1" digest "sha256:8427a2712c22d6eed1cdd5f48258bea102904173558a7087bb82c7d95665c9ff";
view holdings(s: State): (Z, Z) = (s.free, s.held);
view enabled(s: State): Bool = s.free >= 0;
law required conserved(e: Reserve): e.to.free+e.to.held=e.from.free+e.from.held;
}"#).unwrap();
    let run = asks_with_limit(&dir, &[
        "m=map(Reservations.Migration,on=@v/m,reading=Alternative,kind=object_algebra)",
        "b=build(Alternative,on=$m.map.target.base.subject)",
        "n=evaluate(Alternative.holdings,on=$b.object,s=@v/r)",
        "flag=evaluate(Alternative.enabled,on=$b.object,s=@v/r)",
        "ok=check(Alternative.conserved,on=$b.object,e=@v/f)",
    ], "360000");
    assert_eq!(run.code, 0, "{}", run.stdout);
    let result = result_json(&dir, &run);
    assert_eq!(s(get(&result, "status")), "complete");
    for id in ["m", "b", "n", "flag", "ok"] {
        assert_eq!(s(get(answer(&result, id), "status")), "established");
    }
    assert_eq!(arr(value(&result, get(get(answer(&result, "n"), "outputs"), "value"))).iter().map(s).collect::<Vec<_>>(), vec!["2", "0"]);
    let map = value(&result, get(get(answer(&result, "m"), "outputs"), "map"));
    assert_eq!(arr(get(map, "invariants")).len(), 7);
    let signature = value(&result, get(map, "signature"));
    let axes = arr(get(signature, "axes"));
    assert_eq!(axes.len(), 6);
    for axis in axes {
        for name in ["source", "target", "coordinates", "selected"] {
            node(&result, get(axis, name));
        }
        assert_eq!(arr(get(axis, "checks")).len(), 4);
        assert_eq!(s(get(get(node(&result, get(axis, "selected")), "judgment"), "status")), "established");
        let equivalence = value(&result, get(axis, "coordinates"));
        for direction in ["forward", "inverse"] {
            let map = value(&result, get(equivalence, direction));
            for domain in ["source", "target"] {
                let domain = value(&result, get(map, domain));
                assert_eq!(s(get(domain, "kind")), "type");
                assert_eq!(s(&arr(get(domain, "type"))[0]), "Option");
            }
            assert!(arr(get(map, "subjects")).is_empty());
            assert!(arr(get(map, "generators")).is_empty());
        }
        for inverse in ["left_inverse", "right_inverse"] {
            let proof = value(&result, get(equivalence, inverse));
            assert_eq!(s(get(proof, "predicate")), "inverse_maps");
            assert!(!arr(get(proof, "quantifiers")).is_empty());
        }
        for row in arr(get(axis, "checks")) {
            assert_eq!(s(get(value(&result, get(row, "commutes")), "predicate")), "signature_transport");
        }
    }
    for r in arr(get(map, "invariants")) {
        let invariant = value(&result, r);
        if s(get(invariant, "kind")) == "function" {
            assert_eq!(arr(get(invariant, "checks")).len(), 4);
            for row in arr(get(invariant, "checks")) {
                assert_eq!(s(get(value(&result, get(row, "commutes")), "predicate")), "invariant_transport");
            }
        }
    }
}

#[test]
fn closed_view_map_refutes_changed_values_and_keeps_configuration_operation() {
    let dir = inputs("public-closed-view-changes");
    std::fs::write(dir.join("a.json"), include_bytes!("fixtures/object-configuration-map.archmap.json")).unwrap();
    std::fs::write(dir.join("l.law"), r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Alternative {
use vocabulary Reservations version "1" digest "sha256:8427a2712c22d6eed1cdd5f48258bea102904173558a7087bb82c7d95665c9ff";
view holdings(s: State): (Z, Z) = (s.free,s.held);
}"#).unwrap();
    let run = asks_with_limit(&dir, &[
        "m=map(Reservations.Migration,on=@v/m,reading=Alternative,kind=object_algebra)",
        "base=map(Reservations.Migration,on=@v/m,reading=Alternative)",
        "same=compare($m.operation,to=$base.operation,kind=action)",
    ], "360000");
    assert_eq!(run.code, 1, "{}", run.stdout);
    let result = result_json(&dir, &run);
    let m = answer(&result, "m");
    assert_eq!(s(get(m, "status")), "refuted");
    assert!(!has(get(m, "outputs"), "map"));
    assert!(has(get(m, "outputs"), "operation"));
    assert_eq!(s(get(answer(&result, "same"), "status")), "established");
    assert!(!arr(get(&result, "nodes")).iter().any(|n| {
        matches!(&get(n, "type").value, archsig::json::JValue::Str(t) if t == "SignatureMap")
    }));
    let result=internal_graph(&dir,&result);
    for name in ["invariant_transport", "signature_transport"] {
        assert!(arr(get(&result, "nodes")).iter().any(|n| {
            has(n, "value") && has(get(n, "value"), "predicate")
                && s(get(get(n, "value"), "predicate")) == name
                && s(get(get(n, "judgment"), "status")) == "refuted"
        }));
    }
}

#[test]
fn closed_view_transport_stop_retains_only_the_checked_operation() {
    use archsig::observed::{control::{Checkpoint, Control, Limits, Usage}, evaluate_observed_bytes, input::InputSources};
    let mut control = Control::new(Limits { time_ms: None, memory_mib: None }, |point| Usage {
        elapsed_ms: 0, memory_mib: 0,
        signal: (point == Checkpoint::ObjectViewTransport).then_some(archsig::result::Signal::Term),
    });
    let law = br#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Alternative {
use vocabulary Reservations version "1" digest "sha256:8427a2712c22d6eed1cdd5f48258bea102904173558a7087bb82c7d95665c9ff";
view holdings(s: State): (Z,Z) = (s.free,s.held);
}"#;
    let result = evaluate_observed_bytes(InputSources::from_bytes(
        vec![include_bytes!("fixtures/reservations.atoms.json").to_vec()], law.to_vec(),
        include_bytes!("fixtures/object-configuration-map.archmap.json").to_vec(),
    ), &["m=map(Reservations.Migration,on=@v/m,reading=Alternative,kind=object_algebra)"], &mut control).unwrap();
    assert_eq!(result.status(), "interrupted");
    let wire = archsig::json::parse(result.wire().canonical().as_bytes()).unwrap();
    let m = answer(&wire, "m");
    assert_eq!(s(get(m, "status")), "undetermined");
    assert!(has(get(m, "outputs"), "operation"));
    assert!(!has(get(m, "outputs"), "map"));
    assert!(!has(get(m, "outputs"), "proposition"));
}

fn finite_view_inputs(name: &str, preserve: bool) -> PathBuf {
    let dir = inputs(name);
    let mut a = include_str!("fixtures/object-configuration-map.archmap.json").to_string();
    if preserve {
        a = a.replace(r#""id":"r-free","subject":"r","field":"Reservations.State.free","value":"4""#, r#""id":"r-free","subject":"r","field":"Reservations.State.free","value":"2""#)
            .replace(r#""id":"s-free","subject":"s","field":"Reservations.State.free","value":"3""#, r#""id":"s-free","subject":"s","field":"Reservations.State.free","value":"1""#);
    }
    std::fs::write(dir.join("a.json"), a).unwrap();
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
fn finite_view_map_preserves_all_parameters_with_renamed_target_and_following_queries() {
    let dir = finite_view_inputs("finite-view-map", true);
    let run = asks_with_limit(&dir, &[
        "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
        "b=build(After,on=$m.map.target.base.subject)",
        "yes=evaluate(After.yes)", "zero=evaluate(After.zero)", "one=evaluate(After.one)",
        "free=evaluate(After.choice,on=$b.object,s=@v/r,keep=$yes.value,which=$zero.value)",
        "held=evaluate(After.choice,on=$b.object,s=@v/r,keep=$yes.value,which=$one.value)",
    ], "120000");
    assert_eq!(run.code, 0, "{}", run.stdout);
    let result = result_json(&dir, &run);
    assert_eq!(s(get(&result, "status")), "complete");
    for id in ["m", "b", "yes", "zero", "one", "free", "held"] {
        assert_eq!(s(get(answer(&result, id), "status")), "established");
    }
    for (id, expected) in [("free", "2"), ("held", "0")] {
        assert_eq!(s(value(&result, get(get(answer(&result, id), "outputs"), "value"))), expected);
    }
    let map = value(&result, get(get(answer(&result, "m"), "outputs"), "map"));
    let declaration = arr(get(map, "declarations")).iter().find(|d| s(get(d, "source")) == "Before.choice").unwrap();
    let pairs = arr(get(declaration, "parameters"));
    assert!(pairs.iter().any(|p| s(&arr(p)[0]) == "take" && s(&arr(p)[1]) == "keep"));
    assert!(pairs.iter().any(|p| s(&arr(p)[0]) == "mode" && s(&arr(p)[1]) == "which"));
    let invariants = arr(get(map, "invariants"));
    let axes = arr(get(value(&result, get(map, "signature")), "axes"));
    assert_eq!(invariants.len(), 3);
    assert_eq!(axes.len(), 3);
    for table in invariants.iter().map(|r| value(&result, r)).chain(axes.iter()) {
        let rows = arr(get(table, "checks"));
        assert_eq!(rows.len(), 4);
        for row in rows {
            let proof = value(&result, get(row, "commutes"));
            let quantifiers = arr(get(proof, "quantifiers"));
            assert_eq!(quantifiers.len(), 2);
            for name in ["take", "mode"] {
                assert!(quantifiers.iter().any(|q| s(get(q, "name")) == name && s(get(q, "kind")) == "forall" && !has(q, "domain")));
            }
        }
    }
}

#[test]
fn finite_view_map_refutes_a_changed_nonzero_parameter_row() {
    let dir = finite_view_inputs("finite-view-map-changed", false);
    let run = asks_with_limit(&dir, &[
        "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
        "same=compare($m.operation,to=$m.operation,kind=action)",
    ], "120000");
    assert_eq!(run.code, 1, "{}", run.stdout);
    let result = result_json(&dir, &run);
    assert_eq!(s(get(&result, "status")), "complete");
    assert_eq!(s(get(answer(&result, "m"), "status")), "refuted");
    assert!(!has(get(answer(&result, "m"), "outputs"), "map"));
    assert_eq!(s(get(answer(&result, "same"), "status")), "established");
}

fn mixed_view_inputs(name: &str, preserve: bool, parameter: bool) -> PathBuf {
    let dir = finite_view_inputs(name, preserve);
    let (source_parameter, target_parameter, source_value, target_value) = if parameter {
        (", take: Bool", ", keep: Bool", "(take,(if take then s.free else s.held,rat(3,2)),if take then 1 else 0)", "(keep,(if keep then s.free else s.held,rat(3,2)),if keep then 1 else 0)")
    } else {
        ("", "", "(s.free>=0,(s.free,rat(3,2)),if s.held=0 then 1 else 0)", "(s.free>=0,(s.free,rat(3,2)),if s.held=0 then 1 else 0)")
    };
    let vocabulary = r#"use vocabulary Reservations version "1" digest "sha256:8427a2712c22d6eed1cdd5f48258bea102904173558a7087bb82c7d95665c9ff";"#;
    let law = format!(r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{
{vocabulary}
view metrics(s: State{source_parameter}): (Bool,(Z,Q),Fp(2)) = {source_value};
}}
reading After {{
{vocabulary}
view metrics(s: State{target_parameter}): (Bool,(Z,Q),Fp(2)) = {target_value};
view yes(): Bool = true;
}}"#);
    std::fs::write(dir.join("l.law"), law).unwrap();
    dir
}
#[test]
fn mixed_product_views_map_build_and_evaluate_with_and_without_parameters() {
    for parameter in [false, true] {
        let dir = mixed_view_inputs(if parameter { "mixed-parameter-view" } else { "mixed-closed-view" }, true, parameter);
        let query = if parameter { "n=evaluate(After.metrics,on=$b.object,s=@v/r,keep=$yes.value)" } else { "n=evaluate(After.metrics,on=$b.object,s=@v/r)" };
        let run = asks_with_limit(&dir, &[
            "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
            "b=build(After,on=$m.map.target.base.subject)",
            "yes=evaluate(After.yes)", query,
        ], "120000");
        assert_eq!(run.code, 0, "{}", run.stdout);
        let result = result_json(&dir, &run);
        for id in ["m", "b", "yes", "n"] { assert_eq!(s(get(answer(&result, id), "status")), "established"); }
        let v = arr(value(&result, get(get(answer(&result, "n"), "outputs"), "value")));
        assert!(matches!(v[0].value, archsig::json::JValue::Bool(true)));
        assert_eq!(s(&arr(&v[1])[0]), "2");
        assert_eq!(arr(&arr(&v[1])[1]).iter().map(s).collect::<Vec<_>>(), vec!["3","2"]);
        assert_eq!(s(&v[2]), "1");
        let map = value(&result, get(get(answer(&result, "m"), "outputs"), "map"));
        let axes = arr(get(value(&result, get(map, "signature")), "axes"));
        assert_eq!(axes.len(), 3);
        for axis in axes { assert_eq!(arr(get(axis,"checks")).len(), 4); }
    }
}
#[test]
fn mixed_product_view_map_refutes_changed_numeric_coordinate() {
    let dir = mixed_view_inputs("mixed-view-changed", false, false);
    let run = asks_with_limit(&dir, &[
        "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
        "same=compare($m.operation,to=$m.operation,kind=action)",
    ], "120000");
    assert_eq!(run.code, 1, "{}", run.stdout);
    let result = result_json(&dir, &run);
    assert_eq!(s(get(answer(&result, "m"), "status")), "refuted");
    assert!(!has(get(answer(&result, "m"), "outputs"), "map"));
    assert_eq!(s(get(answer(&result, "same"), "status")), "established");
}

fn container_view_inputs(name: &str, preserve: bool, parameter: bool) -> PathBuf {
    let dir = finite_view_inputs(name, preserve);
    let (sp, tp, sc, tc) = if parameter {
        (",take:Bool", ",keep:Bool", "take", "keep")
    } else { ("", "", "s.free>1", "s.free>1") };
    let vocabulary = r#"use vocabulary Reservations version "1" digest "sha256:8427a2712c22d6eed1cdd5f48258bea102904173558a7087bb82c7d95665c9ff";"#;
    let body = |condition| format!(r#"(if {condition} then list<Z>[s.free,s.held] else list<Z>[],if {condition} then some(rat(3,2)) else none<Q>,if {condition} then set<Z>{{s.free,s.held}} else set<Z>{{}},if {condition} then "present" else "empty",unit)"#);
    let law = format!(r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{
{vocabulary}
view metrics(s:State{sp}):(List<Z>,Option<Q>,Set<Z>,Text,Unit)={};
}}
reading After {{
{vocabulary}
view metrics(s:State{tp}):(List<Z>,Option<Q>,Set<Z>,Text,Unit)={};
view yes():Bool=true;
view no():Bool=false;
}}"#, body(sc), body(tc));
    std::fs::write(dir.join("l.law"), law).unwrap();
    dir
}

#[test]
fn container_views_map_build_and_evaluate_known_empty_and_present_values() {
    for parameter in [false, true] {
        let dir = container_view_inputs(if parameter { "container-family-view" } else { "container-closed-view" }, true, parameter);
        let present = if parameter { "p=evaluate(After.metrics,on=$b.object,s=@v/r,keep=$yes.value)" } else { "p=evaluate(After.metrics,on=$b.object,s=@v/r)" };
        let empty = if parameter { "n=evaluate(After.metrics,on=$b.object,s=@v/r,keep=$no.value)" } else { "n=evaluate(After.metrics,on=$b.object,s=@v/s)" };
        let run = asks(&dir, &[
            "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
            "b=build(After,on=$m.map.target.base.subject)",
            "yes=evaluate(After.yes)", "no=evaluate(After.no)", present, empty,
        ]);
        assert_eq!(run.code, 0, "{}", run.stdout);
        let result = result_json(&dir, &run);
        for id in ["m", "b", "yes", "no", "p", "n"] { assert_eq!(s(get(answer(&result, id), "status")), "established"); }
        let p = arr(value(&result, get(get(answer(&result, "p"), "outputs"), "value")));
        assert_eq!(arr(&p[0]).iter().map(s).collect::<Vec<_>>(), vec!["2","0"]);
        assert_eq!(arr(get(&p[1], "some")).iter().map(s).collect::<Vec<_>>(), vec!["3","2"]);
        assert_eq!(arr(&p[2]).iter().map(s).collect::<std::collections::BTreeSet<_>>(), ["0","2"].into_iter().collect());
        assert_eq!(s(&p[3]), "present");
        assert!(arr(&p[4]).is_empty());
        let n = arr(value(&result, get(get(answer(&result, "n"), "outputs"), "value")));
        assert!(arr(&n[0]).is_empty());
        assert!(matches!(get(&n[1], "none").value, archsig::json::JValue::Bool(true)));
        assert!(arr(&n[2]).is_empty());
        assert_eq!(s(&n[3]), "empty");
        assert!(arr(&n[4]).is_empty());
        let map = value(&result, get(get(answer(&result, "m"), "outputs"), "map"));
        let axes = arr(get(value(&result, get(map, "signature")), "axes"));
        assert_eq!(axes.len(), 3);
        assert_eq!(arr(get(map, "invariants")).len(), 3);
        for table in arr(get(map, "invariants")).iter().map(|r| value(&result, r)).chain(axes.iter()) {
            let rows = arr(get(table, "checks"));
            assert_eq!(rows.len(), 4);
            for row in rows {
                let qs = arr(get(value(&result, get(row, "commutes")), "quantifiers"));
                assert_eq!(qs.len(), usize::from(parameter));
                if parameter {
                    assert_eq!(s(get(&qs[0], "name")), "take");
                    assert_eq!(s(get(&qs[0], "kind")), "forall");
                    assert!(!has(&qs[0], "domain"));
                }
            }
        }
    }
}

#[test]
fn container_view_map_refutes_changed_list_entries_and_keeps_the_operation() {
    let dir = container_view_inputs("container-view-changed", false, true);
    let run = asks(&dir, &[
        "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
        "same=compare($m.operation,to=$m.operation,kind=action)",
    ]);
    assert_eq!(run.code, 1, "{}", run.stdout);
    let result = result_json(&dir, &run);
    assert_eq!(s(get(answer(&result, "m"), "status")), "refuted");
    assert!(!has(get(answer(&result, "m"), "outputs"), "map"));
    assert_eq!(s(get(answer(&result, "same"), "status")), "established");
}

#[test]
fn reference_containers_do_not_use_same_nominal_type_identity() {
    let dir = finite_view_inputs("reference-container-view", true);
    let vocabulary = r#"use vocabulary Reservations version "1" digest "sha256:8427a2712c22d6eed1cdd5f48258bea102904173558a7087bb82c7d95665c9ff";"#;
    std::fs::write(dir.join("l.law"), format!(r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{vocabulary} view refs(s:State):List<State> = list<State>[s];}}
reading After {{{vocabulary} view refs(s:State):List<State> = list<State>[s];}}"#)).unwrap();
    let run = without_file_changes(&dir, || asks(&dir, &["m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)"]));
    notified(&dir, &run, "error", 70);
}

fn finite_container_parameter_inputs(name: &str, preserve: bool, kind: &str) -> PathBuf {
    let dir = finite_view_inputs(name, preserve);
    let (ty, source, target, empty, picked) = match kind {
        "Option" => ("Option<Bool>", "choice=some(true)", "keep=some(true)", "none<Bool>", "some(true)"),
        "Set" => ("Set<Bool>", "true in choice", "true in keep", "set<Bool>{}", "set<Bool>{true}"),
        "Unit" => ("Unit", "true", "true", "unit", "unit"),
        _ => panic!("finite parameter fixture"),
    };
    let vocabulary = r#"use vocabulary Reservations version "1" digest "sha256:8427a2712c22d6eed1cdd5f48258bea102904173558a7087bb82c7d95665c9ff";"#;
    std::fs::write(dir.join("l.law"), format!(r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{
{vocabulary}
view metrics(s:State,choice:{ty}):(Z,{ty})=(if {source} then s.free else s.held,choice);
}}
reading After {{
{vocabulary}
view metrics(s:State,keep:{ty}):(Z,{ty})=(if {target} then s.free else s.held,keep);
view empty():{ty} = {empty};
view picked():{ty} = {picked};
}}"#)).unwrap();
    dir
}

#[test]
fn finite_container_parameters_drive_map_build_and_following_values() {
    for kind in ["Option", "Set", "Unit"] {
        let dir = finite_container_parameter_inputs(&format!("finite-container-{kind}"), true, kind);
        let run = asks(&dir, &[
            "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
            "b=build(After,on=$m.map.target.base.subject)",
            "empty=evaluate(After.empty)", "picked=evaluate(After.picked)",
            "p=evaluate(After.metrics,on=$b.object,s=@v/r,keep=$picked.value)",
            "n=evaluate(After.metrics,on=$b.object,s=@v/r,keep=$empty.value)",
        ]);
        assert_eq!(run.code, 0, "{}", run.stdout);
        let result = result_json(&dir, &run);
        for id in ["m", "b", "empty", "picked", "p", "n"] { assert_eq!(s(get(answer(&result, id), "status")), "established"); }
        let p = arr(value(&result, get(get(answer(&result, "p"), "outputs"), "value")));
        let n = arr(value(&result, get(get(answer(&result, "n"), "outputs"), "value")));
        assert_eq!(s(&p[0]), "2");
        assert_eq!(s(&n[0]), if kind == "Unit" { "2" } else { "0" });
        match kind {
            "Option" => {
                assert!(matches!(get(&p[1], "some").value, archsig::json::JValue::Bool(true)));
                assert!(matches!(get(&n[1], "none").value, archsig::json::JValue::Bool(true)));
            }
            "Set" => {
                assert_eq!(arr(&p[1]).len(), 1);
                assert!(matches!(arr(&p[1])[0].value, archsig::json::JValue::Bool(true)));
                assert!(arr(&n[1]).is_empty());
            }
            "Unit" => { assert!(arr(&p[1]).is_empty()); assert!(arr(&n[1]).is_empty()); }
            _ => unreachable!(),
        }
        let map = value(&result, get(get(answer(&result, "m"), "outputs"), "map"));
        let axes = arr(get(value(&result, get(map, "signature")), "axes"));
        assert_eq!(axes.len(), 3);
        for axis in axes {
            assert_eq!(arr(get(axis, "checks")).len(), 4);
            for row in arr(get(axis, "checks")) {
                let qs = arr(get(value(&result, get(row, "commutes")), "quantifiers"));
                assert_eq!(qs.len(), 1);
                assert_eq!(s(get(&qs[0], "name")), "choice");
                assert_eq!(s(get(&qs[0], "kind")), "forall");
                assert!(!has(&qs[0], "domain"));
                let ty = get(&qs[0], "type");
                if kind == "Unit" { assert_eq!(s(ty), "Unit"); }
                else { assert_eq!(s(&arr(ty)[0]), kind); assert_eq!(s(&arr(ty)[1]), "Bool"); }
            }
        }
    }
}

#[test]
fn finite_container_parameter_map_checks_the_nonempty_parameter_rows() {
    for kind in ["Option", "Set", "Unit"] {
        let dir = finite_container_parameter_inputs(&format!("finite-container-changed-{kind}"), false, kind);
        let run = asks(&dir, &[
            "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
            "same=compare($m.operation,to=$m.operation,kind=action)",
        ]);
        assert_eq!(run.code, 1, "{}", run.stdout);
        let result = result_json(&dir, &run);
        assert_eq!(s(get(answer(&result, "m"), "status")), "refuted");
        assert!(!has(get(answer(&result, "m"), "outputs"), "map"));
        assert_eq!(s(get(answer(&result, "same"), "status")), "established");
    }
}

fn data_view_inputs(
    name: &str,
    preserve: bool,
    parameter: bool,
    reference_payload: bool,
) -> PathBuf {
    let dir = finite_view_inputs(name, preserve);
    let old = include_str!("fixtures/reservations.atoms.json");
    let extra = if reference_payload {
        r#",{"name":"Held","arguments":[["Ref","Reservations.System"]],"meaning":"参照を含む値"}"#
    } else {
        ""
    };
    let declaration = format!(
        r#""declarations": [{{"kind":"data","name":"Reservations.Packet","meaning":"値を区別するconstructor","constructors":[{{"name":"Empty","arguments":[],"meaning":"空"}},{{"name":"Full","arguments":["Z"],"meaning":"整数"}},{{"name":"Flag","arguments":["Bool"],"meaning":"真偽"}}{extra}]}},"#
    );
    let definition = old.replacen("\"declarations\": [", &declaration, 1);
    let old_checked =
        archsig::definition::check_definitions(&[("definition0", old.as_bytes())]).unwrap();
    let checked =
        archsig::definition::check_definitions(&[("definition0", definition.as_bytes())]).unwrap();
    let digest = &checked.vocabularies["Reservations"].digest;
    let map = std::fs::read_to_string(dir.join("a.json"))
        .unwrap()
        .replace(&old_checked.vocabularies["Reservations"].digest, digest);
    std::fs::write(dir.join("d.json"), definition).unwrap();
    std::fs::write(dir.join("a.json"), map).unwrap();
    let (sp, tp, sc, tc) = if parameter {
        (",take:Bool", ",keep:Bool", "take", "keep")
    } else {
        ("", "", "s.free>1", "s.free>1")
    };
    let body = |condition| {
        format!(
            "(if {condition} then Full(s.free) else Empty,list<Packet>[Full(s.free),Flag(false)],if {condition} then some(Full(s.held)) else none<Packet>,s.free)"
        )
    };
    let law = format!(
        r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{use vocabulary Reservations version "1" digest "{digest}";
view packets(s:State{sp}):(Packet,List<Packet>,Option<Packet>,Z)={};}}
reading After {{use vocabulary Reservations version "1" digest "{digest}";
view packets(s:State{tp}):(Packet,List<Packet>,Option<Packet>,Z)={};
view yes():Bool=true;view no():Bool=false;}}"#,
        body(sc),
        body(tc)
    );
    std::fs::write(dir.join("l.law"), law).unwrap();
    dir
}

#[test]
fn data_values_and_containers_map_build_and_feed_later_evaluation() {
    for parameter in [false, true] {
        let dir = data_view_inputs(
            if parameter {
                "data-family"
            } else {
                "data-closed"
            },
            true,
            parameter,
            false,
        );
        let p = if parameter {
            "p=evaluate(After.packets,on=$b.object,s=@v/r,keep=$yes.value)"
        } else {
            "p=evaluate(After.packets,on=$b.object,s=@v/r)"
        };
        let n = if parameter {
            "n=evaluate(After.packets,on=$b.object,s=@v/s,keep=$no.value)"
        } else {
            "n=evaluate(After.packets,on=$b.object,s=@v/s)"
        };
        let r = asks(
            &dir,
            &[
                "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
                "b=build(After,on=$m.map.target.base.subject)",
                "yes=evaluate(After.yes)",
                "no=evaluate(After.no)",
                p,
                n,
            ],
        );
        assert_eq!(r.code, 0, "{}", r.stdout);
        let result = result_json(&dir, &r);
        for id in ["m", "b", "p", "n"] {
            assert_eq!(s(get(answer(&result, id), "status")), "established");
        }
        let p = arr(value(
            &result,
            get(get(answer(&result, "p"), "outputs"), "value"),
        ));
        assert_eq!(s(get(&p[0], "tag")), "Full");
        assert_eq!(s(&arr(get(&p[0], "args"))[0]), "2");
        assert_eq!(s(get(&arr(&p[1])[1], "tag")), "Flag");
        assert_eq!(s(get(get(&p[2], "some"), "tag")), "Full");
        assert_eq!(s(&p[3]), "2");
        let n = arr(value(
            &result,
            get(get(answer(&result, "n"), "outputs"), "value"),
        ));
        assert_eq!(s(get(&n[0], "tag")), "Empty");
        assert!(matches!(
            get(&n[2], "none").value,
            archsig::json::JValue::Bool(true)
        ));
        let maps:Vec<_> = arr(get(&result,"nodes")).iter().filter(|node| matches!(&get(node,"type").value,archsig::json::JValue::Str(t) if t=="ValueMap")).collect();
        assert!(!maps.is_empty());
        for map in maps {
            let pairs = arr(get(get(map, "value"), "declarations"));
            let names: std::collections::BTreeSet<_> = pairs
                .iter()
                .map(|pair| {
                    let pair = arr(pair);
                    assert_eq!(s(&pair[0]), s(&pair[1]));
                    s(&pair[0])
                })
                .collect();
            assert_eq!(
                names,
                [
                    "Reservations.Packet",
                    "Reservations.Packet.Empty",
                    "Reservations.Packet.Flag",
                    "Reservations.Packet.Full"
                ]
                .into_iter()
                .collect()
            );
        }
    }
}

#[test]
fn changed_data_payload_refutes_map_and_preserves_configuration_operation() {
    let dir = data_view_inputs("data-changed", false, true, false);
    let r = asks(
        &dir,
        &[
            "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
            "same=compare($m.operation,to=$m.operation,kind=action)",
        ],
    );
    assert_eq!(r.code, 1, "{}", r.stdout);
    let result = result_json(&dir, &r);
    assert_eq!(s(get(answer(&result, "m"), "status")), "refuted");
    assert!(!has(get(answer(&result, "m"), "outputs"), "map"));
    assert!(has(get(answer(&result, "m"), "outputs"), "operation"));
    assert_eq!(s(get(answer(&result, "same"), "status")), "established");
}

#[test]
fn an_unused_reference_constructor_does_not_become_an_identity_value_map() {
    let dir = data_view_inputs("data-hidden-reference", true, false, true);
    let r = asks(
        &dir,
        &[
            "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
        ],
    );
    assert_eq!(r.code, 70, "{}", r.stdout);
    assert!(has(&r.receipt, "issues"));
}

fn finite_data_view_inputs(name: &str) -> PathBuf {
    let dir = data_view_inputs(name, true, true, false);
    let old = std::fs::read_to_string(dir.join("d.json")).unwrap();
    let definition = old.replacen("\"declarations\": [", r#""declarations": [{"kind":"data","name":"Reservations.Choice","meaning":"選択値","constructors":[{"name":"On","arguments":[],"meaning":"選択"},{"name":"Off","arguments":[],"meaning":"非選択"},{"name":"Other","arguments":[],"meaning":"別の非選択"}]},"#, 1);
    let old_checked =
        archsig::definition::check_definitions(&[("definition0", old.as_bytes())]).unwrap();
    let checked =
        archsig::definition::check_definitions(&[("definition0", definition.as_bytes())]).unwrap();
    let old_digest = &old_checked.vocabularies["Reservations"].digest;
    let digest = &checked.vocabularies["Reservations"].digest;
    let map = std::fs::read_to_string(dir.join("a.json"))
        .unwrap()
        .replace(old_digest, digest);
    let law = std::fs::read_to_string(dir.join("l.law"))
        .unwrap()
        .replace(old_digest, digest)
        .replace("take:Bool", "take:Choice")
        .replace("keep:Bool", "keep:Choice")
        .replace("if take then", "if take=On then")
        .replace("if keep then", "if keep=On then")
        .replace("yes():Bool=true", "yes():Choice=On")
        .replace("no():Bool=false", "no():Choice=Other");
    std::fs::write(dir.join("d.json"), definition).unwrap();
    std::fs::write(dir.join("a.json"), map).unwrap();
    std::fs::write(dir.join("l.law"), law).unwrap();
    dir
}

#[test]
fn finite_data_parameters_preserve_all_constructors_and_later_bindings() {
    let dir = finite_data_view_inputs("data-parameter");
    let r = asks(
        &dir,
        &[
            "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
            "b=build(After,on=$m.map.target.base.subject)",
            "yes=evaluate(After.yes)",
            "no=evaluate(After.no)",
            "p=evaluate(After.packets,on=$b.object,s=@v/r,keep=$yes.value)",
            "n=evaluate(After.packets,on=$b.object,s=@v/r,keep=$no.value)",
        ],
    );
    assert_eq!(r.code, 0, "{}", r.stdout);
    let result = result_json(&dir, &r);
    let p = arr(value(
        &result,
        get(get(answer(&result, "p"), "outputs"), "value"),
    ));
    let n = arr(value(
        &result,
        get(get(answer(&result, "n"), "outputs"), "value"),
    ));
    assert_eq!(s(get(&p[0], "tag")), "Full");
    assert_eq!(s(&arr(get(&p[0], "args"))[0]), "2");
    assert_eq!(s(get(&n[0], "tag")), "Empty");
    let m = value(&result, get(get(answer(&result, "m"), "outputs"), "map"));
    let invariant = value(&result, &arr(get(m, "invariants"))[0]);
    for row in arr(get(invariant, "checks")) {
        let qs = arr(get(value(&result, get(row, "commutes")), "quantifiers"));
        assert_eq!(qs.len(), 1);
        assert_eq!(s(get(&qs[0], "name")), "take");
        assert_eq!(
            arr(get(&qs[0], "type")).iter().map(s).collect::<Vec<_>>(),
            ["Data", "Reservations.Choice"]
        );
    }
}

#[test]
fn a_changed_third_data_parameter_row_refutes_the_whole_map() {
    let dir = finite_data_view_inputs("data-parameter-third-row");
    let law = std::fs::read_to_string(dir.join("l.law"))
        .unwrap()
        .replace("if keep=On then", "if keep!=Off then");
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

#[test]
fn relation_transport_keeps_named_words_empty_words_and_parameter_positions() {
    for case in ["unit", "empty", "alias", "order"] {
        let dir = finite_view_inputs(&format!("relation-transport-{case}"), true);
        if case != "unit" {
            let path = dir.join("a.json");
            let mut data=std::fs::read_to_string(&path).unwrap()
                .replace(r#""id":"e-to","subject":"e","field":"Reservations.Reserve.to","value":["v","q"]"#,r#""id":"e-to","subject":"e","field":"Reservations.Reserve.to","value":["v","p"]"#)
                .replace(r#""id":"f-to","subject":"f","field":"Reservations.Reserve.to","value":["v","s"]"#,r#""id":"f-to","subject":"f","field":"Reservations.Reserve.to","value":["v","r"]"#);
            if case == "alias" || case == "order" {
                data=data.replace(r#"{"id":"f","type":"Reservations.Reserve","origin":"model"},"#,r#"{"id":"f","type":"Reservations.Reserve","origin":"model"},{"id":"g","type":"Reservations.Reserve","origin":"model"},"#)
                    .replace(r#""atoms":["#,r#""atoms":[{"id":"g-owner","subject":"g","field":"Reservations.Reserve.owner","value":["v","B"],"origin":"model"},{"id":"g-from","subject":"g","field":"Reservations.Reserve.from","value":["v","r"],"origin":"model"},{"id":"g-to","subject":"g","field":"Reservations.Reserve.to","value":["v","r"],"origin":"model"},"#);
            }
            std::fs::write(path, data).unwrap();
        }
        let (source, target) = match case {
            "unit" => (
                "relation paths(e:Reserve): path(e)=then(identity(source(path(e))),path(e));",
                "relation paths(t:Reserve): then(path(t),identity(target(path(t))))=path(t);",
            ),
            "empty" => (
                "relation paths(e:Reserve): identity(source(path(e)))=identity(source(path(e)));",
                "relation paths(t:Reserve): path(t)=path(t);",
            ),
            "alias" => (
                "relation paths(e:Reserve,f:Reserve): path(e)=path(e);",
                "relation paths(u:Reserve,v:Reserve): path(v)=path(v);",
            ),
            _ => (
                "relation paths(root:System,e:Reserve[root],f:Reserve[root]): then(path(e),path(f))=then(path(e),path(f));",
                "relation paths(world:System,u:Reserve[world],v:Reserve[world]): then(path(v),path(u))=then(path(v),path(u));",
            ),
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
        let normal = cli::run(
            &dir,
            &[
                "run",
                "--atom-definition",
                "d.json",
                "--archmap",
                "a.json",
                "--law",
                "l.law",
                "--ask",
                "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
                "--ask",
                "same=compare($m.operation,to=$m.operation,kind=action)",
            ],
        );
        assert_eq!(
            normal.code,
            if case == "unit" { 0 } else { 1 },
            "{case}: {}",
            normal.stdout
        );
        assert!(normal.stderr.is_empty());
        assert_eq!(std::fs::read_dir(&dir).unwrap().count(), 3);
        eprintln!("relation {case}: stdout {} bytes", normal.stdout.len());
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
            assert_eq!(arr(get(transport, "clauses")).len(), 2);
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
                        ("u", "w"),
                        ("w", "w"),
                    ],
                );
                assert_eq!(arr(get(moved, "generators")).len(), 2);
                assert_eq!(
                    s(get(value(&result, get(clause, "source")), "kind")),
                    "source"
                );
                assert_eq!(
                    s(get(value(&result, get(clause, "target")), "kind")),
                    "source"
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
            let left = names("left");
            let right = names("right");
            match case {
                "empty" => {
                    assert!(left.is_empty());
                    assert_eq!(right.len(), 1);
                }
                "alias" => {
                    assert_eq!(left, ["f"]);
                    assert_eq!(right, ["g"]);
                }
                "order" => {
                    assert_eq!(left, ["f", "g"]);
                    assert_eq!(right, ["g", "f"]);
                }
                _ => unreachable!(),
            }
        }
        let reused = cli::run(
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
                "again",
                "--reuse",
                "out",
                "--ask",
                "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
                "--ask",
                "same=compare($m.operation,to=$m.operation,kind=action)",
            ],
        );
        assert_eq!(reused.code, run.code, "{}", reused.stdout);
        let again = result_json(&dir, &reused);
        assert!(warnings(&again).is_empty());
        for key in ["answers", "nodes"] {
            assert_eq!(get(&result, key).value, get(&again, key).value);
        }
    }
}

#[test]
fn relation_transport_keeps_missing_generator_actions_pending_and_independent_word_refutations() {
    for changed in [false, true] {
        let dir = finite_view_inputs(
            if changed {
                "relation-missing-and-refuted"
            } else {
                "relation-missing"
            },
            true,
        );
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
        let plan = value(&result, get(get(answer(&result, "n"), "outputs"), "plan"));
        if !changed {
            assert!(arr(get(plan, "requirements")).iter().any(|r| s(get(
                get(r, "field"),
                "subject"
            )) == "x"
                && s(get(get(r, "field"), "field")) == "Reservations.State.free"));
        }
        if changed {
            assert!(!arr(get(answer(&result, "m"), "counterexamples")).is_empty());
        } else {
            assert!(!has(answer(&result, "m"), "counterexamples"));
        }
        let again = cli::run(
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
                "again",
                "--reuse",
                "out",
                "--ask",
                "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
                "--ask",
                "same=compare($m.operation,to=$m.operation,kind=action)",
                "--ask",
                "n=needed($m)",
            ],
        );
        assert_eq!(again.code, run.code, "{}", again.stdout);
        let again = result_json(&dir, &again);
        assert!(warnings(&again).is_empty());
        for key in ["answers", "nodes"] {
            assert_eq!(get(&result, key).value, get(&again, key).value);
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
        let dir = finite_view_inputs(&format!("relation-unsupported-{name}"), true);
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
fn relation_guard_transport_preserves_active_rows_and_keeps_termwise_witnesses() {
    for (case, source, target, code, status) in [
        (
            "false_relation_preserved",
            "relation paths(e:Reserve,take:Bool) when take:path(e)=identity(source(path(e)));",
            "relation paths(t:Reserve,keep:Bool) when keep:path(t)=identity(source(path(t)));",
            0,
            "established",
        ),
        (
            "expanded",
            "relation paths(e:Reserve,take:Bool) when take:path(e)=(if take then path(e) else identity(source(path(e))));",
            "relation paths(t:Reserve,keep:Bool):path(t)=path(t);",
            0,
            "established",
        ),
        (
            "observed",
            "relation paths(e:Reserve) when source(path(e)).free>0:path(e)=path(e);",
            "relation paths(t:Reserve) when source(path(t)).free>0:path(t)=path(t);",
            0,
            "established",
        ),
        (
            "contracted",
            "relation paths(e:Reserve,take:Bool):path(e)=path(e);",
            "relation paths(t:Reserve,keep:Bool) when keep:path(t)=path(t);",
            1,
            "refuted",
        ),
        (
            "inactive",
            "relation paths(e:Reserve) when false:path(e)=identity(source(path(e)));",
            "relation paths(t:Reserve) when false:identity(source(path(t)))=path(t);",
            0,
            "established",
        ),
        (
            "word",
            "relation paths(e:Reserve,take:Bool) when take:identity(source(path(e)))=identity(source(path(e)));",
            "relation paths(t:Reserve,keep:Bool) when keep:path(t)=path(t);",
            1,
            "refuted",
        ),
        (
            "relation_refuted",
            "relation paths(e:Reserve,take:Bool) when take:path(e)=identity(source(path(e)));",
            "relation paths(t:Reserve,keep:Bool) when keep:path(t)=path(t);",
            1,
            "refuted",
        ),
    ] {
        let dir = finite_view_inputs(&format!("relation-guard-{case}"), true);
        let vocabulary = r#"use vocabulary Reservations version "1" digest "sha256:8427a2712c22d6eed1cdd5f48258bea102904173558a7087bb82c7d95665c9ff";"#;
        std::fs::write(
            dir.join("l.law"),
            format!(
                r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{ {vocabulary} {source} }} reading After {{ {vocabulary} {target} }}"#
            ),
        )
        .unwrap();
        let requests = [
            "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
            "same=compare($m.operation,to=$m.operation,kind=action)",
        ];
        if case == "expanded" || case == "contracted" {
            let normal = cli::run(
                &dir,
                &[
                    "run",
                    "--atom-definition",
                    "d.json",
                    "--archmap",
                    "a.json",
                    "--law",
                    "l.law",
                    "--ask",
                    requests[0],
                    "--ask",
                    requests[1],
                ],
            );
            assert_eq!(normal.code, code, "{case}: {}", normal.stdout);
            assert!(normal.stderr.is_empty());
            assert_eq!(std::fs::read_dir(&dir).unwrap().count(), 3);
            eprintln!(
                "relation guard {case}: stdout {} bytes",
                normal.stdout.len()
            );
        }
        let run = asks(&dir, &requests);
        assert_eq!(run.code, code, "{case}: {}", run.stdout);
        let result = result_json(&dir, &run);
        assert_eq!(s(get(answer(&result, "m"), "status")), status);
        assert_eq!(s(get(answer(&result, "same"), "status")), "established");
        if code == 0 {
            let map = value(&result, get(get(answer(&result, "m"), "outputs"), "map"));
            let transport = value(&result, &arr(get(map, "transports"))[0]);
            let clauses = arr(get(transport, "clauses"));
            assert_eq!(clauses.len(), 2);
            for clause in clauses {
                let arguments = value(&result, get(clause, "arguments"));
                let params = arr(get(arguments, "source_type"));
                assert_eq!(s(&params[0]), "Tuple");
                assert_eq!(
                    params.len(),
                    if matches!(case, "expanded" | "false_relation_preserved") {
                        3
                    } else {
                        2
                    }
                );
                assert_eq!(
                    arr(get(value(&result, get(clause, "commutes")), "quantifiers")).len(),
                    params.len() - 1
                );
            }
        } else {
            assert!(!has(get(answer(&result, "m"), "outputs"), "map"));
            let witnesses = arr(get(answer(&result, "m"), "counterexamples"));
            assert!(!witnesses.is_empty());
            for witness in witnesses {
                let data = get(value(&result, witness), "data");
                let bindings = arr(get(data, "bindings"));
                let take = value(
                    &result,
                    get(
                        bindings
                            .iter()
                            .find(|p| s(get(p, "name")) == "take")
                            .unwrap(),
                        "value",
                    ),
                );
                assert!(
                    matches!(take.value,archsig::json::JValue::Bool(v) if v==(case=="word"||case=="relation_refuted"))
                );
                if case == "contracted" {
                    assert!(matches!(
                        value(&result, get(data, "left")).value,
                        archsig::json::JValue::Bool(true)
                    ));
                    assert!(matches!(
                        value(&result, get(data, "right")).value,
                        archsig::json::JValue::Bool(false)
                    ));
                } else {
                    assert!(arr(get(value(&result, get(data, "left")), "generators")).is_empty());
                    assert_eq!(
                        arr(get(value(&result, get(data, "right")), "generators")).len(),
                        1
                    );
                }
            }
        }
        if case == "expanded" || case == "contracted" {
            let reused = cli::run(
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
                    "again",
                    "--reuse",
                    "out",
                    "--ask",
                    requests[0],
                    "--ask",
                    requests[1],
                ],
            );
            assert_eq!(reused.code, code, "{}", reused.stdout);
            let again = result_json(&dir, &reused);
            assert!(warnings(&again).is_empty());
            for key in ["answers", "nodes"] {
                assert_eq!(get(&result, key).value, get(&again, key).value);
            }
        }
    }
}

#[test]
fn relation_guard_transport_keeps_required_unknowns_and_ignores_target_extra_unknowns() {
    for case in ["source", "target", "extra", "conditional"] {
        let dir = finite_view_inputs(&format!("relation-guard-missing-{case}"), true);
        let path = dir.join("a.json");
        let data=std::fs::read_to_string(&path).unwrap()
            .replace(r#""subjects":["#,r#""subjects":[{"id":"C","type":"Reservations.System","origin":"model"},{"id":"x","type":"Reservations.State","origin":"model"},"#)
            .replace(r#""atoms":["#,r#""atoms":[{"id":"x-owner","subject":"x","field":"Reservations.State.owner","value":["v","C"],"origin":"model"},{"id":"x-held","subject":"x","field":"Reservations.State.held","value":"0","origin":"model"},"#);
        let data = if case == "conditional" {
            data.replace(r#""subjects":["#,r#""subjects":[{"id":"h","type":"Reservations.Reserve","origin":"model"},"#).replace(r#""atoms":["#,r#""atoms":[{"id":"h-owner","subject":"h","field":"Reservations.Reserve.owner","value":["v","C"],"origin":"model"},{"id":"h-from","subject":"h","field":"Reservations.Reserve.from","value":["v","x"],"origin":"model"},{"id":"h-to","subject":"h","field":"Reservations.Reserve.to","value":["v","x"],"origin":"model"},"#)
        } else {
            data
        };
        std::fs::write(path, data).unwrap();
        let (sg, tg) = match case {
            "source" => ("when s.free>0", ""),
            "target" => ("", "when u.free>0"),
            "conditional" => (
                "when if e.from=e.to then (let p=path(e) in true) else false",
                "when false",
            ),
            _ => ("when take", "when if keep then true else u.free>0"),
        };
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
        if case == "target" {
            let reused = cli::run(
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
                    "again",
                    "--reuse",
                    "out",
                    "--ask",
                    requests[0],
                    "--ask",
                    requests[1],
                    "--ask",
                    requests[2],
                ],
            );
            assert_eq!(reused.code, 2, "{}", reused.stdout);
            let again = result_json(&dir, &reused);
            assert!(warnings(&again).is_empty());
            for key in ["answers", "nodes"] {
                assert_eq!(get(&result, key).value, get(&again, key).value);
            }
        }
    }
}

#[test]
fn root_relation_paths_keep_correspondence_words_actions_and_endpoint_failures() {
    for case in [
        "preserved",
        "alias",
        "order",
        "empty",
        "endpoints",
        "missing",
    ] {
        let dir = finite_view_inputs(&format!("root-relation-{case}"), true);
        let path = dir.join("a.json");
        let mut data = std::fs::read_to_string(&path).unwrap();
        if case != "endpoints" {
            data=data.replace(r#""id":"m-to","subject":"m","field":"Reservations.Migration.to","value":["v","B"]"#,r#""id":"m-to","subject":"m","field":"Reservations.Migration.to","value":["v","A"]"#)
                .replace(r#""id":"m-reserves","subject":"m","field":"Reservations.Migration.reserves","value":[[["v","e"],["v","f"]]]"#,r#""id":"m-reserves","subject":"m","field":"Reservations.Migration.reserves","value":[[["v","e"],["v","e"]]]"#)
                .replace(r#""id":"m-states","subject":"m","field":"Reservations.Migration.states","value":[[["v","p"],["v","r"]],[["v","q"],["v","s"]],[["v","u"],["v","w"]]]"#,r#""id":"m-states","subject":"m","field":"Reservations.Migration.states","value":[[["v","p"],["v","p"]],[["v","q"],["v","q"]],[["v","u"],["v","u"]]]"#);
            let extra = data
                .lines()
                .filter(|l| l.contains(r#""subject":"m""#))
                .filter(|l| case != "missing" || !l.contains(r#""id":"m-states""#))
                .map(|l| {
                    l.replace(r#""id":"m-"#, r#""id":"n-"#)
                        .replace(r#""subject":"m""#, r#""subject":"n""#)
                })
                .collect::<Vec<_>>()
                .join("\n");
            data=data.replace(r#"{"id":"m","type":"Reservations.Migration","origin":"model"},"#,r#"{"id":"m","type":"Reservations.Migration","origin":"model"},{"id":"n","type":"Reservations.Migration","origin":"model"},"#)
                .replace(r#""atoms":["#,&format!("\"atoms\":[\n{extra}\n"));
        }
        std::fs::write(path, data).unwrap();
        let (source, target) = match case {
            "alias" => (
                "relation paths(a:Migration,b:Migration):path(a)=path(a);",
                "relation paths(u:Migration,v:Migration):path(v)=path(v);",
            ),
            "order" => (
                "relation paths(a:Migration,b:Migration):then(path(a),path(b))=then(path(a),path(b));",
                "relation paths(u:Migration,v:Migration):then(path(v),path(u))=then(path(v),path(u));",
            ),
            "empty" => (
                "relation paths(a:Migration):identity(source(path(a)))=identity(source(path(a)));",
                "relation paths(u:Migration):path(u)=path(u);",
            ),
            _ => (
                "relation paths(a:Migration):path(a)=then(identity(source(path(a))),path(a));",
                "relation paths(u:Migration):then(path(u),identity(target(path(u))))=path(u);",
            ),
        };
        let vocabulary = r#"use vocabulary Reservations version "1" digest "sha256:8427a2712c22d6eed1cdd5f48258bea102904173558a7087bb82c7d95665c9ff";"#;
        std::fs::write(
            dir.join("l.law"),
            format!(
                r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{ {vocabulary} {source} }} reading After {{ {vocabulary} {target} }}
reading Helpers {{ {vocabulary} view same(a:Migration,b:Migration):Bool=path(a)=path(b); }}"#
            ),
        )
        .unwrap();
        let mut requests = vec![
            "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
            "same=compare($m.operation,to=$m.operation,kind=action)",
            "n=needed($m)",
        ];
        if case == "alias" || case == "order" {
            requests.push("action=evaluate(Helpers.same,a=@v/m,b=@v/n)");
        }
        let code = match case {
            "preserved" => 0,
            "missing" => 2,
            _ => 1,
        };
        if case == "preserved" || case == "endpoints" || case == "missing" {
            let mut args = vec![
                "run",
                "--atom-definition",
                "d.json",
                "--archmap",
                "a.json",
                "--law",
                "l.law",
            ];
            for request in &requests {
                args.extend(["--ask", request]);
            }
            let normal = cli::run(&dir, &args);
            assert_eq!(normal.code, code, "{case}: {}", normal.stdout);
            assert!(normal.stderr.is_empty());
            assert_eq!(std::fs::read_dir(&dir).unwrap().count(), 3);
            eprintln!("root relation {case}: stdout {} bytes", normal.stdout.len());
        }
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
            assert_eq!(arr(get(transport, "clauses")).len(), 2);
            for clause in arr(get(transport, "clauses")) {
                let values = value(&result, get(clause, "values"));
                assert_json(
                    get(values, "source_type"),
                    r#"["Path","Reservations.System","Reservations.System"]"#,
                );
                assert_reference_pairs(
                    &result,
                    values,
                    &[("A", "A"), ("B", "B"), ("m", "m"), ("n", "n")],
                );
                assert_eq!(arr(get(values, "generators")).len(), 2);
            }
        } else {
            assert!(!has(get(answer(&result, "m"), "outputs"), "map"));
        }
        if case == "missing" {
            let plan = value(&result, get(get(answer(&result, "n"), "outputs"), "plan"));
            assert!(arr(get(plan, "requirements")).iter().any(|r| s(get(
                get(r, "field"),
                "subject"
            )) == "n"
                && s(get(get(r, "field"), "field")) == "Reservations.Migration.states"));
        } else if code == 1 {
            let examples = arr(get(answer(&result, "m"), "counterexamples"));
            assert!(!examples.is_empty());
            let data = get(value(&result, &examples[0]), "data");
            if case == "endpoints" {
                assert_eq!(s(&arr(value(&result, get(data, "left")))[1]), "B");
                assert_eq!(s(&arr(value(&result, get(data, "right")))[1]), "A");
                assert_eq!(arr(get(data, "paths")).len(), 2);
            } else {
                let word = |side: &str| {
                    arr(get(value(&result, get(data, side)), "generators"))
                        .iter()
                        .map(|r| s(&arr(value(&result, r))[1]).to_owned())
                        .collect::<Vec<_>>()
                };
                let left = word("left");
                let right = word("right");
                match case {
                    "alias" => {
                        assert_eq!(left, ["m"]);
                        assert_eq!(right, ["n"]);
                    }
                    "order" => {
                        assert_eq!(left, ["m", "n"]);
                        assert_eq!(right, ["n", "m"]);
                    }
                    "empty" => {
                        assert!(left.is_empty());
                        assert_eq!(right, ["m"]);
                    }
                    _ => unreachable!(),
                }
            }
        }
        if case == "alias" || case == "order" {
            assert!(matches!(
                value(
                    &result,
                    get(get(answer(&result, "action"), "outputs"), "value")
                )
                .value,
                archsig::json::JValue::Bool(true)
            ));
        }
        if case == "preserved" || case == "endpoints" || case == "missing" {
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
            for request in &requests {
                args.extend(["--ask", request]);
            }
            let reused = cli::run(&dir, &args);
            assert_eq!(reused.code, code, "{case}: {}", reused.stdout);
            let again = result_json(&dir, &reused);
            assert!(warnings(&again).is_empty());
            for key in ["answers", "nodes"] {
                assert_eq!(get(&result, key).value, get(&again, key).value);
            }
        }
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
        let digest = &checked.vocabularies["Flow"].digest;
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
        if case == "preserved" || case == "missing" || case == "endpoints" {
            let mut args = vec![
                "run",
                "--atom-definition",
                "d.json",
                "--archmap",
                "a.json",
                "--law",
                "l.law",
            ];
            for request in &requests {
                args.extend(["--ask", request]);
            }
            let normal = cli::run(&dir, &args);
            assert_eq!(normal.code, code, "{case}: {}", normal.stdout);
            assert!(normal.stderr.is_empty());
            assert_eq!(std::fs::read_dir(&dir).unwrap().count(), 3);
            eprintln!(
                "heterogeneous relation {case}: stdout {} bytes",
                normal.stdout.len()
            );
        }
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
        if case == "preserved" || case == "missing" || case == "endpoints" {
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
            for request in &requests {
                args.extend(["--ask", request]);
            }
            let reused = cli::run(&dir, &args);
            assert_eq!(reused.code, code, "{}", reused.stdout);
            let again = result_json(&dir, &reused);
            assert!(warnings(&again).is_empty());
            for key in ["answers", "nodes"] {
                assert_eq!(get(&result, key).value, get(&again, key).value);
            }
        }
    }
}

#[test]
fn unknown_path_condition_preserves_program_identity_instead_of_action_equality() {
    for same_word in [false, true] {
        let dir = finite_view_inputs(
            if same_word {
                "path-conditional-same-word"
            } else {
                "path-conditional-different-word"
            },
            true,
        );
        let path = dir.join("a.json");
        let data=std::fs::read_to_string(&path).unwrap()
            .replace(r#""id":"e-to","subject":"e","field":"Reservations.Reserve.to","value":["v","q"]"#,r#""id":"e-to","subject":"e","field":"Reservations.Reserve.to","value":["v","p"]"#)
            .replace(r#""id":"f-to","subject":"f","field":"Reservations.Reserve.to","value":["v","s"]"#,r#""id":"f-to","subject":"f","field":"Reservations.Reserve.to","value":["v","r"]"#)
            .replace(r#""subjects":["#,r#""subjects":[{"id":"C","type":"Reservations.System","origin":"model"},{"id":"x","type":"Reservations.State","origin":"model"},"#)
            .replace(r#""atoms":["#,r#""atoms":[{"id":"x-owner","subject":"x","field":"Reservations.State.owner","value":["v","C"],"origin":"model"},{"id":"x-held","subject":"x","field":"Reservations.State.held","value":"0","origin":"model"},"#);
        std::fs::write(path, data).unwrap();
        let alternative = if same_word {
            "then(identity(source(path(e))),path(e))"
        } else {
            "identity(source(path(e)))"
        };
        let vocabulary = r#"use vocabulary Reservations version "1" digest "sha256:8427a2712c22d6eed1cdd5f48258bea102904173558a7087bb82c7d95665c9ff";"#;
        std::fs::write(
            dir.join("l.law"),
            format!(
                r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{ {vocabulary} relation following(e:Reserve):path(e)=path(e); relation paths(e:Reserve,s:State):
(if s.free>0 then path(e) else {alternative})=(if s.free>0 then path(e) else {alternative}); }}
reading After {{ {vocabulary} relation following(t:Reserve):path(t)=path(t); relation paths(t:Reserve,u:State):path(t)=path(t); }}
reading Helpers {{ {vocabulary} view same(e:Reserve):Bool=path(e)=identity(source(path(e))); }}"#
            ),
        )
        .unwrap();
        let requests = [
            "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
            "same=compare($m.operation,to=$m.operation,kind=action)",
            "n=needed($m)",
            "action=evaluate(Helpers.same,e=@v/e)",
        ];
        let mut normal_args = vec![
            "run",
            "--atom-definition",
            "d.json",
            "--archmap",
            "a.json",
            "--law",
            "l.law",
        ];
        for request in &requests {
            normal_args.extend(["--ask", request]);
        }
        let normal = cli::run(&dir, &normal_args);
        assert_eq!(
            normal.code,
            if same_word { 0 } else { 2 },
            "{}",
            normal.stdout
        );
        assert!(normal.stderr.is_empty());
        assert_eq!(std::fs::read_dir(&dir).unwrap().count(), 3);
        eprintln!(
            "Path conditional same_word={same_word}: stdout {} bytes",
            normal.stdout.len()
        );
        let run = asks(&dir, &requests);
        assert_eq!(run.code, if same_word { 0 } else { 2 }, "{}", run.stdout);
        let result = result_json(&dir, &run);
        assert_eq!(
            s(get(answer(&result, "m"), "status")),
            if same_word {
                "established"
            } else {
                "undetermined"
            }
        );
        assert_eq!(s(get(answer(&result, "same"), "status")), "established");
        assert!(matches!(
            value(
                &result,
                get(get(answer(&result, "action"), "outputs"), "value")
            )
            .value,
            archsig::json::JValue::Bool(true)
        ));
        let plan = value(&result, get(get(answer(&result, "n"), "outputs"), "plan"));
        if same_word {
            assert!(arr(get(plan, "requirements")).is_empty());
            let map = value(&result, get(get(answer(&result, "m"), "outputs"), "map"));
            let names = arr(get(map, "transports"))
                .iter()
                .map(|r| s(get(value(&result, r), "source")))
                .collect::<Vec<_>>();
            assert_eq!(names, ["Before.following", "Before.paths"]);
        } else {
            assert!(!has(get(answer(&result, "m"), "outputs"), "map"));
            assert!(arr(get(plan, "requirements")).iter().any(|r| s(get(
                get(r, "field"),
                "subject"
            )) == "x"
                && s(get(get(r, "field"), "field")) == "Reservations.State.free"));
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
        for request in &requests {
            args.extend(["--ask", request]);
        }
        let reused = cli::run(&dir, &args);
        assert_eq!(reused.code, run.code, "{}", reused.stdout);
        let again = result_json(&dir, &reused);
        assert!(warnings(&again).is_empty());
        for key in ["answers", "nodes"] {
            assert_eq!(get(&result, key).value, get(&again, key).value);
        }
    }
}
#[test]
fn relation_transport_quantifies_numeric_families_without_sampling() {
    for (case, guard, left, target_guard, target_left, code, status) in [
        (
            "constant",
            "when (n+1=1+n) and (q-q=rat(0,1)) and (m-m=0)",
            "if take then path(e) else identity(source(path(e)))",
            "when (k-k=0) and (r+rat(1,2)=rat(1,2)+r)",
            "if keep then path(t) else identity(source(path(t)))",
            0,
            "established",
        ),
        (
            "expanded",
            "when false",
            "path(e)",
            "",
            "path(t)",
            0,
            "established",
        ),
        (
            "guard_refuted",
            "when n-n=0",
            "path(e)",
            "when false",
            "path(t)",
            1,
            "refuted",
        ),
        (
            "word_refuted",
            "when n-n=0",
            "identity(source(path(e)))",
            "",
            "path(t)",
            1,
            "refuted",
        ),
        (
            "condition_failed",
            "",
            "let unused=then(path(e),path(e)) in identity(source(path(e)))",
            "",
            "path(t)",
            2,
            "undetermined",
        ),
        (
            "separate_axes",
            "when n=m",
            "path(e)",
            "",
            "path(t)",
            2,
            "undetermined",
        ),
        (
            "varying_word",
            "",
            "if n=0 then path(e) else identity(source(path(e)))",
            "",
            "path(t)",
            2,
            "undetermined",
        ),
    ] {
        let dir = finite_view_inputs(&format!("relation-numeric-{case}"), true);
        if case == "varying_word" {
            let path = dir.join("a.json");
            let data = std::fs::read_to_string(&path).unwrap()
                .replace(r#""id":"e-to","subject":"e","field":"Reservations.Reserve.to","value":["v","q"]"#,r#""id":"e-to","subject":"e","field":"Reservations.Reserve.to","value":["v","p"]"#)
                .replace(r#""id":"f-to","subject":"f","field":"Reservations.Reserve.to","value":["v","s"]"#,r#""id":"f-to","subject":"f","field":"Reservations.Reserve.to","value":["v","r"]"#);
            std::fs::write(path, data).unwrap();
        }
        let vocabulary = r#"use vocabulary Reservations version "1" digest "sha256:8427a2712c22d6eed1cdd5f48258bea102904173558a7087bb82c7d95665c9ff";"#;
        std::fs::write(dir.join("l.law"), format!(r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{ {vocabulary} relation paths(n:Z,e:Reserve,q:Q,take:Bool,m:Z) {guard}:({left})=path(e); }}
reading After {{ {vocabulary} relation paths(k:Z,t:Reserve,r:Q,keep:Bool,l:Z) {target_guard}:({target_left})=path(t); }}"#)).unwrap();
        let requests = [
            "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
            "same=compare($m.operation,to=$m.operation,kind=action)",
            "n=needed($m)",
        ];
        let mut args = vec![
            "run",
            "--atom-definition",
            "d.json",
            "--archmap",
            "a.json",
            "--law",
            "l.law",
        ];
        for request in &requests {
            args.extend(["--ask", request]);
        }
        let normal = cli::run(&dir, &args);
        assert_eq!(
            normal.code, code,
            "{case}: {} {}",
            normal.stdout, normal.stderr
        );
        assert!(normal.stderr.is_empty());
        assert_eq!(std::fs::read_dir(&dir).unwrap().count(), 3);
        eprintln!(
            "numeric relation {case}: stdout {} bytes",
            normal.stdout.len()
        );
        let run = asks(&dir, &requests);
        assert_eq!(run.code, code, "{case}: {}", run.stdout);
        let result = result_json(&dir, &run);
        assert_eq!(s(get(answer(&result, "m"), "status")), status);
        assert_eq!(s(get(answer(&result, "same"), "status")), "established");
        if code == 0 {
            let map = value(&result, get(get(answer(&result, "m"), "outputs"), "map"));
            let transport = value(&result, &arr(get(map, "transports"))[0]);
            for clause in arr(get(transport, "clauses")) {
                let arguments = value(&result, get(clause, "arguments"));
                let types = arr(get(arguments, "source_type"));
                assert_eq!(types.len(), 6);
                assert_eq!(s(&types[1]), "Z");
                assert_eq!(s(&types[3]), "Q");
                assert_eq!(s(&types[5]), "Z");
                let proof = value(&result, get(clause, "commutes"));
                let qs = arr(get(proof, "quantifiers"));
                assert_eq!(qs.len(), 5);
                assert_eq!(
                    qs.iter().map(|q| s(get(q, "name"))).collect::<Vec<_>>(),
                    ["n", "e", "q", "take", "m"]
                );
                for index in [0, 2, 4] {
                    assert_eq!(s(get(&qs[index], "kind")), "forall");
                    assert!(!has(&qs[index], "domain"));
                }
            }
        } else {
            assert!(!has(get(answer(&result, "m"), "outputs"), "map"));
            if code == 1 {
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
                        ["n", "e", "q", "take", "m"]
                    );
                    for index in [0, 4] {
                        assert_eq!(s(value(&result, get(&bindings[index], "value"))), "0");
                    }
                    if case == "word_refuted" {
                        assert!(
                            arr(get(value(&result, get(data, "left")), "generators")).is_empty()
                        );
                        assert_eq!(
                            arr(get(value(&result, get(data, "right")), "generators")).len(),
                            1
                        );
                    }
                }
            } else {
                assert!(!has(answer(&result, "m"), "counterexamples"));
                let plan = value(&result, get(get(answer(&result, "n"), "outputs"), "plan"));
                assert!(arr(get(plan, "requirements")).is_empty());
                assert!(!arr(get(plan, "blockers")).is_empty());
            }
        }
        args.extend(["--out", "again", "--reuse", "out"]);
        let reused = cli::run(&dir, &args);
        assert_eq!(reused.code, code, "{case}: {}", reused.stdout);
        let again = result_json(&dir, &reused);
        assert!(warnings(&again).is_empty());
        for key in ["answers", "nodes"] {
            assert_eq!(
                get(&result, key).value,
                get(&again, key).value,
                "{case}: {key}"
            );
        }
    }
}

#[test]
fn relation_transport_restricts_integer_families_to_exact_guard_domains() {
    for (case, guard, left, target_guard, target_left, code, status) in [
        (
            "restricted",
            "when n+m=3",
            "if n+m=3 then path(e) else identity(source(path(e)))",
            "when k+j=3",
            "path(t)",
            0,
            "established",
        ),
        (
            "expanded",
            "when n+m=3",
            "path(e)",
            "",
            "path(t)",
            0,
            "established",
        ),
        (
            "empty",
            "when 2*n=1",
            "path(e)",
            "when false",
            "path(t)",
            0,
            "established",
        ),
        (
            "guard_refuted",
            "when n+m=3",
            "path(e)",
            "when k=0",
            "path(t)",
            1,
            "refuted",
        ),
        (
            "later_guard_refuted",
            "when n=1",
            "path(e)",
            "when last=0",
            "path(t)",
            1,
            "refuted",
        ),
        (
            "all_type_guard_refuted",
            "",
            "path(e)",
            "when k=0",
            "path(t)",
            1,
            "refuted",
        ),
        (
            "word_refuted",
            "when n=7",
            "identity(source(path(e)))",
            "when k=7",
            "path(t)",
            1,
            "refuted",
        ),
        (
            "varying_word",
            "when n+m=3",
            "if extra=0 then path(e) else identity(source(path(e)))",
            "when k+j=3",
            "path(t)",
            2,
            "undetermined",
        ),
    ] {
        let dir = finite_view_inputs(&format!("relation-integer-domain-{case}"), true);
        if case == "varying_word" {
            let path = dir.join("a.json");
            let data = std::fs::read_to_string(&path).unwrap()
                .replace(r#""id":"e-to","subject":"e","field":"Reservations.Reserve.to","value":["v","q"]"#,r#""id":"e-to","subject":"e","field":"Reservations.Reserve.to","value":["v","p"]"#)
                .replace(r#""id":"f-to","subject":"f","field":"Reservations.Reserve.to","value":["v","s"]"#,r#""id":"f-to","subject":"f","field":"Reservations.Reserve.to","value":["v","r"]"#);
            std::fs::write(path, data).unwrap();
        }
        let vocabulary = r#"use vocabulary Reservations version "1" digest "sha256:8427a2712c22d6eed1cdd5f48258bea102904173558a7087bb82c7d95665c9ff";"#;
        std::fs::write(dir.join("l.law"), format!(r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{ {vocabulary} relation paths(n:Z,e:Reserve,m:Z,take:Bool,extra:Z) {guard}:({left})=path(e); }}
reading After {{ {vocabulary} relation paths(k:Z,t:Reserve,j:Z,keep:Bool,last:Z) {target_guard}:({target_left})=path(t); }}"#)).unwrap();
        let requests = [
            "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
            "same=compare($m.operation,to=$m.operation,kind=action)",
            "n=needed($m)",
        ];
        let mut args = vec![
            "run",
            "--atom-definition",
            "d.json",
            "--archmap",
            "a.json",
            "--law",
            "l.law",
        ];
        for request in &requests {
            args.extend(["--ask", request]);
        }
        let normal = cli::run(&dir, &args);
        assert_eq!(
            normal.code, code,
            "{case}: {} {}",
            normal.stdout, normal.stderr
        );
        assert!(normal.stderr.is_empty());
        assert_eq!(std::fs::read_dir(&dir).unwrap().count(), 3);
        eprintln!(
            "integer domain relation {case}: stdout {} bytes",
            normal.stdout.len()
        );
        let run = asks(&dir, &requests);
        assert_eq!(run.code, code, "{case}: {}", run.stdout);
        let result = result_json(&dir, &run);
        assert_eq!(s(get(answer(&result, "m"), "status")), status);
        assert_eq!(s(get(answer(&result, "same"), "status")), "established");
        if code == 0 {
            let map = value(&result, get(get(answer(&result, "m"), "outputs"), "map"));
            let transport = value(&result, &arr(get(map, "transports"))[0]);
            for clause in arr(get(transport, "clauses")) {
                let arguments = value(&result, get(clause, "arguments"));
                let types = arr(get(arguments, "source_type"));
                assert_eq!(types.len(), 6);
                assert_eq!(s(&types[1]), "Z");
                assert_eq!(s(&types[3]), "Z");
                assert_eq!(s(&types[5]), "Z");
                let proof = value(&result, get(clause, "commutes"));
                let qs = arr(get(proof, "quantifiers"));
                assert_eq!(qs.len(), 5);
                assert_eq!(
                    qs.iter().map(|q| s(get(q, "name"))).collect::<Vec<_>>(),
                    ["n", "e", "m", "take", "extra"]
                );
                for index in [0, 2, 4] {
                    assert_eq!(s(get(&qs[index], "kind")), "forall");
                    assert!(!has(&qs[index], "domain"));
                }
            }
        } else {
            assert!(!has(get(answer(&result, "m"), "outputs"), "map"));
            if code == 1 {
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
                    if case == "guard_refuted" {
                        assert_eq!(n + m, 3);
                        assert_ne!(n, 0);
                    } else if case == "later_guard_refuted" {
                        assert_eq!(n, 1);
                        let extra = s(value(&result, get(&bindings[4], "value")))
                            .parse::<i64>()
                            .unwrap();
                        assert_ne!(extra, 0);
                    } else if case == "all_type_guard_refuted" {
                        assert_ne!(n, 0);
                    } else {
                        assert_eq!(n, 7);
                    }
                    if case == "word_refuted" {
                        assert!(
                            arr(get(value(&result, get(data, "left")), "generators")).is_empty()
                        );
                        assert_eq!(
                            arr(get(value(&result, get(data, "right")), "generators")).len(),
                            1
                        );
                    }
                }
            } else {
                assert!(!has(answer(&result, "m"), "counterexamples"));
                let plan = value(&result, get(get(answer(&result, "n"), "outputs"), "plan"));
                assert!(arr(get(plan, "requirements")).is_empty());
                assert!(!arr(get(plan, "blockers")).is_empty());
            }
        }
        args.extend(["--out", "again", "--reuse", "out"]);
        let reused = cli::run(&dir, &args);
        assert_eq!(reused.code, code, "{case}: {}", reused.stdout);
        let again = result_json(&dir, &reused);
        assert!(warnings(&again).is_empty());
        for key in ["answers", "nodes"] {
            assert_eq!(
                get(&result, key).value,
                get(&again, key).value,
                "{case}: {key}"
            );
        }
    }
}
#[test]
fn change_transport_let_if_updates_keep_whole_sources_and_simultaneous_values() {
    for (case, parameter, left, right, missing, code, status) in [
        (
            "finite",
            "Bool",
            "let old=s.free in if n then s with {free=old+s.held,held=old} else s with {held=old,free=old}",
            "let prior=t.free in if not k then t with {held=prior,free=prior} else t with {held=prior,free=prior+t.held}",
            false,
            0,
            "established",
        ),
        (
            "finite_refuted",
            "Bool",
            "let old=s.free in if n then s with {free=old+s.held,held=old} else s with {held=old,free=old}",
            "let prior=t.free in if not k then t with {held=prior,free=prior} else t with {held=prior,free=prior+t.held+1}",
            false,
            1,
            "refuted",
        ),
        (
            "integer_let",
            "Z",
            "let delta=n+1 in s with {free=s.free+delta,held=s.free}",
            "t with {held=t.free,free=t.free+(k+1)}",
            false,
            0,
            "established",
        ),
        (
            "integer_if",
            "Z",
            "let delta=n+1 in if s.free=2 then s with {free=s.free+delta,held=s.free} else s with {free=s.free+n-1,held=s.free}",
            "let amount=k+1 in if not (t.free=2) then t with {held=t.free,free=t.free+k-1} else t with {held=t.free,free=t.free+amount}",
            false,
            0,
            "established",
        ),
        (
            "integer_parameter_if",
            "Z",
            "if n>0 then s with {free=s.free+n,held=s.free} else s with {free=s.free-n,held=s.free}",
            "if k>0 then t with {held=t.free,free=t.free+k} else t with {held=t.free,free=t.free-k}",
            false,
            2,
            "undetermined",
        ),
        (
            "missing",
            "Bool",
            "let old=s.free in if n then s with {free=old+1,held=s.held} else s with {free=old,held=s.held}",
            "let prior=t.free in if k then t with {held=t.held,free=prior+1} else t with {held=t.held,free=prior}",
            true,
            2,
            "undetermined",
        ),
        (
            "missing_refuted",
            "Bool",
            "let old=s.free in if n then s with {free=old+1,held=s.held} else s with {free=old,held=s.held}",
            "let prior=t.free in if k then t with {held=t.held+1,free=prior+1} else t with {held=t.held+1,free=prior}",
            true,
            1,
            "refuted",
        ),
        (
            "unknown_condition",
            "Bool",
            "if s.free>0 then s with {free=1,held=2} else s with {free=3,held=4}",
            "if t.free>0 then t with {held=2,free=1} else t with {held=4,free=3}",
            true,
            2,
            "undetermined",
        ),
        (
            "unused_missing",
            "Bool",
            "let unused=s.free in s with {free=1,held=2}",
            "let unused=t.free in t with {held=2,free=1}",
            true,
            0,
            "established",
        ),
        (
            "different_fields",
            "Bool",
            "if n then s with {free=1} else s with {held=2}",
            "if k then t with {free=1} else t with {held=2}",
            false,
            2,
            "undetermined",
        ),
    ] {
        let dir = finite_view_inputs(&format!("change-lexical-{case}"), true);
        let vocabulary = r#"use vocabulary Reservations version "1" digest "sha256:8427a2712c22d6eed1cdd5f48258bea102904173558a7087bb82c7d95665c9ff";"#;
        let law = format!(
            r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{ {vocabulary} change tune(s:State,n:{parameter})={left}; }}
reading After {{ {vocabulary} change tune(t:State,k:{parameter})={right}; }}"#
        );
        std::fs::write(dir.join("l.law"), &law).unwrap();
        if missing {
            let data = std::fs::read_to_string(dir.join("a.json")).unwrap();
            std::fs::write(
                dir.join("a.json"),
                data.lines()
                    .filter(|line| !line.contains(r#""id":"p-free""#))
                    .collect::<Vec<_>>()
                    .join("\n"),
            )
            .unwrap();
        }
        let requests = [
            "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
            "same=compare($m.operation,to=$m.operation,kind=action)",
            "n=needed($m)",
        ];
        let mut args = vec![
            "run",
            "--atom-definition",
            "d.json",
            "--archmap",
            "a.json",
            "--law",
            "l.law",
            "--time-ms",
            "120000",
        ];
        for request in &requests {
            args.extend(["--ask", request]);
        }
        let normal = without_file_changes(&dir, || cli::run(&dir, &args));
        assert_eq!(
            normal.code, code,
            "{case}: {} {}",
            normal.stdout, normal.stderr
        );
        assert!(normal.stderr.is_empty());

        let run = asks(&dir, &requests);
        assert_eq!(run.code, code, "{case}: {}", run.stdout);
        let result = result_json(&dir, &run);
        assert_map_summary(&normal, &result);
        let map_answer = answer(&result, "m");
        assert_eq!(s(get(map_answer, "status")), status, "{case}");
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
                    if case == "integer_let" && side == "target" {
                        assert_eq!(s(get(expression, "kind")), "source");
                        let span = arr(get(get(expression, "location"), "span"));
                        let expected = if field == "free" {
                            "t.free+(k+1)"
                        } else {
                            "t.free"
                        };
                        assert_eq!(
                            &law.as_bytes()[num(&span[0]) as usize..num(&span[1]) as usize],
                            expected.as_bytes()
                        );
                        continue;
                    }
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
        }
        if code == 1 {
            let examples = arr(get(map_answer, "counterexamples"));
            assert!(!examples.is_empty());
            if case == "finite_refuted" {
                let data = get(value(&result, &examples[0]), "data");
                let bindings = arr(get(data, "bindings"));
                assert!(matches!(
                    value(&result, get(&bindings[1], "value")).value,
                    archsig::json::JValue::Bool(true)
                ));
            }
        }
        if code == 2 {
            assert!(!has(map_answer, "counterexamples"));
            let plan = value(&result, get(get(answer(&result, "n"), "outputs"), "plan"));
            if missing {
                assert!(
                    arr(get(plan, "requirements"))
                        .iter()
                        .any(|r| s(get(get(r, "field"), "subject")) == "p")
                );
            } else {
                assert!(!arr(get(plan, "blockers")).is_empty());
            }
        }
        let mut reuse = args.clone();
        reuse.extend(["--out", "again", "--reuse", "out"]);
        let again = cli::run(&dir, &reuse);
        assert_eq!(again.code, code, "{case}: {}", again.stdout);
        let again = result_json(&dir, &again);
        assert!(warnings(&again).is_empty());
        for key in ["answers", "nodes"] {
            assert_eq!(
                get(&result, key).value,
                get(&again, key).value,
                "{case}: {key}"
            );
        }
        if case == "finite" {
            let file = dir.join("out/result.json");
            let saved = std::fs::read_to_string(&file).unwrap();
            let needle = r#""field":"Reservations.State.free","kind":"change_update""#;
            assert!(saved.contains(needle));
            std::fs::write(
                file,
                saved.replacen(
                    needle,
                    r#""field":"Reservations.State.held","kind":"change_update""#,
                    1,
                ),
            )
            .unwrap();
            let mut rejected = args.clone();
            rejected.extend(["--out", "rejected", "--reuse", "out"]);
            let run = cli::run(&dir, &rejected);
            assert_eq!(run.code, 0, "{}", run.stdout);
            let correct = result_json(&dir, &run);
            assert!(!warnings(&correct).is_empty());
            for key in ["answers", "nodes"] {
                assert_eq!(get(&result, key).value, get(&correct, key).value);
            }
        }
    }
}

#[test]
fn local_integer_expression_reads_use_all_source_rows_and_actual_images() {
    for (case, source_guard, target_guard, target_read, missing, code) in [
        ("preserved", "", "", "1+t.free", false, 0),
        (
            "late-refutation",
            "true",
            "true",
            "if t.free=19 then 2+t.free else 1+t.free",
            false,
            1,
        ),
        ("expanded", "s.free=2", "t.free>0", "1+t.free", false, 0),
        ("missing-read", "true", "true", "1+t.free", true, 2),
        (
            "inactive-target-unknown",
            "s.held=1",
            "t.free>0",
            "1+t.free",
            true,
            0,
        ),
        ("observed-zero", "true", "true", "1+t.free", false, 0),
        (
            "observed-zero-refuted",
            "true",
            "true",
            "1+t.free",
            false,
            1,
        ),
    ] {
        let dir = finite_view_inputs(&format!("local-integer-expression-{case}"), true);
        let vocabulary = r#"use vocabulary Reservations version "1" digest "sha256:8427a2712c22d6eed1cdd5f48258bea102904173558a7087bb82c7d95665c9ff";"#;
        let source_read = if case.starts_with("observed-zero") {
            "s.free+0"
        } else {
            "s.free+1"
        };
        let target_read = if case == "observed-zero" {
            "0+t.free"
        } else {
            target_read
        };
        let source_guard = if source_guard.is_empty() {
            String::new()
        } else {
            format!("when {source_guard}")
        };
        let target_guard = if target_guard.is_empty() {
            String::new()
        } else {
            format!("when {target_guard}")
        };
        std::fs::write(
            dir.join("l.law"),
            format!(
                r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{vocabulary} local here(s:State) {source_guard} reads {source_read};}}
reading After {{{vocabulary} local here(t:State) {target_guard} reads {target_read};}}"#
            ),
        )
        .unwrap();
        let mut map = std::fs::read_to_string(dir.join("a.json")).unwrap();
        if missing {
            // 元と実像の両方を欠測にし、base mapの既知値保存と切り分ける。
            map = map
                .lines()
                .filter(|line| {
                    !line.contains(r#""id":"p-free""#) && !line.contains(r#""id":"r-free""#)
                })
                .collect::<Vec<_>>()
                .join("\n");
        }
        if case.starts_with("observed-zero") {
            for subject in ["p", "r"] {
                map = map.replace(&format!(r#""id":"{subject}-free","subject":"{subject}","field":"Reservations.State.free","value":"2""#),
                    &format!(r#""id":"{subject}-free","subject":"{subject}","field":"Reservations.State.free","value":"0""#));
            }
        }
        std::fs::write(dir.join("a.json"), map).unwrap();
        let mut requests = vec![
            "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
            "same=compare($m.operation,to=$m.operation,kind=action)",
            "n=needed($m)",
        ];
        if case == "preserved" {
            requests.push("b=build(After,on=$m.map.target.base.subject)");
        }
        let mut args = vec![
            "run",
            "--atom-definition",
            "d.json",
            "--law",
            "l.law",
            "--archmap",
            "a.json",
        ];
        for request in &requests {
            args.extend(["--ask", request]);
        }
        let delivery = matches!(case, "preserved" | "late-refutation" | "missing-read");
        if delivery {
            let normal = without_file_changes(&dir, || cli::run(&dir, &args));
            assert_eq!(normal.code, code, "{case}: {}", normal.stdout);
            assert!(normal.stderr.is_empty());
            assert!(
                normal.stdout.len() < 2000,
                "{case}: {}",
                normal.stdout.len()
            );
        }
        let run = asks(&dir, &requests);
        assert_eq!(run.code, code, "{case}: {}", run.stdout);
        let result = result_json(&dir, &run);
        let m = answer(&result, "m");
        assert_eq!(
            s(get(m, "status")),
            match code {
                0 => "established",
                1 => "refuted",
                _ => "undetermined",
            }
        );
        assert!(has(get(m, "outputs"), "operation"));
        assert_eq!(s(get(answer(&result, "same"), "status")), "established");
        assert_eq!(has(get(m, "outputs"), "map"), code == 0);
        if code == 0 {
            if case == "preserved" {
                assert_eq!(s(get(answer(&result, "b"), "status")), "established");
            }
            let map = value(&result, get(get(m, "outputs"), "map"));
            let transport = value(&result, &arr(get(map, "transports"))[0]);
            let clause = &arr(get(transport, "clauses"))[0];
            assert_local_clause(
                &dir,
                &result,
                clause,
                source_read,
                target_read,
                &[("s", "Reservations.State")],
            );
            let values = value(&result, get(clause, "values"));
            assert_json(get(values, "source_type"), r#""Z""#);
            assert_json(get(values, "target_type"), r#""Z""#);
        }
        if case == "late-refutation" {
            let examples = arr(get(m, "counterexamples"));
            assert_eq!(examples.len(), 1);
            let data = get(value(&result, &examples[0]), "data");
            assert_eq!(s(value(&result, get(data, "left"))), "20");
            assert_eq!(s(value(&result, get(data, "right"))), "21");
            let bindings = arr(get(data, "bindings"));
            assert_eq!(bindings.len(), 1);
            assert_eq!(s(get(&bindings[0], "name")), "s");
            assert_json(value(&result, get(&bindings[0], "value")), r#"["v","u"]"#);
            let subjects = arr(get(data, "facts"))
                .iter()
                .map(|fact| s(get(fact, "subject")))
                .collect::<Vec<_>>();
            assert_eq!(subjects, ["u", "w"]);
        }
        if case == "observed-zero-refuted" {
            let data = get(value(&result, &arr(get(m, "counterexamples"))[0]), "data");
            assert_eq!(s(value(&result, get(data, "left"))), "0");
            assert_eq!(s(value(&result, get(data, "right"))), "1");
        }
        if code == 2 {
            assert!(!has(m, "counterexamples"));
            let plan = value(&result, get(get(answer(&result, "n"), "outputs"), "plan"));
            assert!(arr(get(plan, "requirements")).iter().any(|r| {
                let field = get(r, "field");
                s(get(field, "subject")) == "p"
                    && s(get(field, "field")) == "Reservations.State.free"
            }));
        }
        if !delivery {
            continue;
        }
        args.extend(["--out", "again", "--reuse", "out"]);
        let reused = cli::run(&dir, &args);
        assert_eq!(reused.code, code, "{case}: {}", reused.stdout);
        let again = result_json(&dir, &reused);
        assert!(warnings(&again).is_empty());
        for key in ["answers", "nodes"] {
            assert_eq!(
                get(&result, key).value,
                get(&again, key).value,
                "{case}: {key}"
            );
        }
    }
}

fn four_state_inputs(name: &str) -> PathBuf {
    let dir = finite_view_inputs(name, true);
    let map = std::fs::read_to_string(dir.join("a.json"))
        .unwrap()
        .lines()
        .filter(|line| {
            !line.contains(r#""id":"u","type":"#)
                && !line.contains(r#""id":"w","type":"#)
                && !line.contains(r#""subject":"u""#)
                && !line.contains(r#""subject":"w""#)
        })
        .collect::<Vec<_>>()
        .join("\n")
        .replace(r#",[["v","u"],["v","w"]]"#, "")
        .replace(",\n]", "\n]");
    std::fs::write(dir.join("a.json"), map).unwrap();
    dir
}

#[test]
fn local_multiple_reference_integer_reads_check_cartesian_rows_in_parameter_order() {
    for (case, source_guard, target_guard, target_read, missing, code) in [
        ("preserved", "", "", "2*x.free+y.free", false, 0),
        (
            "cross-field",
            "z.free=a.free",
            "y.free=x.free",
            "x.free",
            false,
            0,
        ),
        ("cross-field-refuted", "", "", "x.free", false, 1),
        (
            "off-diagonal",
            "",
            "",
            "if y.held=1 and x.free=2 then 1+2*x.free+y.free else 2*x.free+y.free",
            false,
            1,
        ),
        (
            "expanded",
            "z.free=2 and a.held=1",
            "y.free>0",
            "2*x.free+y.free",
            false,
            0,
        ),
        (
            "guard-refuted",
            "z.held=1 and a.held=1",
            "y.free>1",
            "2*x.free+y.free",
            false,
            1,
        ),
        ("missing", "", "", "2*x.free+y.free", true, 2),
        (
            "inactive-target-unknown",
            "z.held=1 and a.held=1",
            "y.free>0 and x.free>0",
            "2*x.free+y.free",
            true,
            0,
        ),
        ("zero-refuted", "", "", "1+2*x.free+y.free", false, 1),
    ] {
        let source_read = if case.starts_with("cross-field") {
            "z.free"
        } else {
            "z.free+2*a.free"
        };
        let dir = four_state_inputs(&format!("local-multiple-integer-{case}"));
        let mut map = std::fs::read_to_string(dir.join("a.json")).unwrap();
        if missing {
            map = map
                .lines()
                .filter(|line| {
                    !line.contains(r#""id":"p-free""#) && !line.contains(r#""id":"r-free""#)
                })
                .collect::<Vec<_>>()
                .join("\n");
        }
        if case == "zero-refuted" {
            for subject in ["p", "r"] {
                map = map.replace(&format!(r#""id":"{subject}-free","subject":"{subject}","field":"Reservations.State.free","value":"2""#),
                    &format!(r#""id":"{subject}-free","subject":"{subject}","field":"Reservations.State.free","value":"0""#));
            }
        }
        std::fs::write(dir.join("a.json"), map).unwrap();
        let vocabulary = r#"use vocabulary Reservations version "1" digest "sha256:8427a2712c22d6eed1cdd5f48258bea102904173558a7087bb82c7d95665c9ff";"#;
        let source_guard = if source_guard.is_empty() {
            String::new()
        } else {
            format!("when {source_guard}")
        };
        let target_guard = if target_guard.is_empty() {
            String::new()
        } else {
            format!("when {target_guard}")
        };
        std::fs::write(
            dir.join("l.law"),
            format!(
                r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{vocabulary} local here(z:State,a:State) {source_guard} reads {source_read};}}
reading After {{{vocabulary} local here(y:State,x:State) {target_guard} reads {target_read};}}"#
            ),
        )
        .unwrap();
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
        for request in &requests {
            args.extend(["--ask", request]);
        }
        let delivery = matches!(case, "preserved" | "off-diagonal" | "missing");
        let normal = delivery.then(|| without_file_changes(&dir, || cli::run(&dir, &args)));
        let run = asks(&dir, &requests);
        assert_eq!(run.code, code, "{case}: {}", run.stdout);
        let result = result_json(&dir, &run);
        if let Some(normal) = &normal {
            assert_eq!(normal.code, code, "{case}: {}", normal.stdout);
            assert_map_summary(normal, &result);
            assert!(normal.stderr.is_empty());
        }
        let m = answer(&result, "m");
        assert_eq!(
            s(get(m, "status")),
            match code {
                0 => "established",
                1 => "refuted",
                _ => "undetermined",
            }
        );
        assert!(has(get(m, "outputs"), "operation"));
        assert_eq!(has(get(m, "outputs"), "map"), code == 0);
        assert_eq!(s(get(answer(&result, "same"), "status")), "established");
        if code == 0 {
            let map = value(&result, get(get(m, "outputs"), "map"));
            let transport = value(&result, &arr(get(map, "transports"))[0]);
            assert_json(get(transport, "parameters"), r#"[["z","y"],["a","x"]]"#);
            let clause = &arr(get(transport, "clauses"))[0];
            assert_local_clause(
                &dir,
                &result,
                clause,
                source_read,
                target_read,
                &[("z", "Reservations.State"), ("a", "Reservations.State")],
            );
            let arguments = value(&result, get(clause, "arguments"));
            assert_json(
                get(arguments, "source_type"),
                r#"["Tuple",["Ref","Reservations.State"],["Ref","Reservations.State"]]"#,
            );
            assert_reference_pairs(
                &result,
                arguments,
                &[("p", "r"), ("q", "s"), ("r", "r"), ("s", "s")],
            );
        }
        if matches!(
            case,
            "off-diagonal" | "zero-refuted" | "cross-field-refuted"
        ) {
            let examples = arr(get(m, "counterexamples"));
            assert_eq!(examples.len(), 1);
            let data = get(value(&result, &examples[0]), "data");
            let (left, right, subjects) = if case == "off-diagonal" {
                ("5", "6", ["q", "p"])
            } else if case == "cross-field-refuted" {
                ("2", "1", ["p", "q"])
            } else {
                ("0", "1", ["p", "p"])
            };
            assert_eq!(s(value(&result, get(data, "left"))), left);
            assert_eq!(s(value(&result, get(data, "right"))), right);
            let bindings = arr(get(data, "bindings"));
            assert_eq!(bindings.len(), 2);
            for ((binding, name), subject) in bindings.iter().zip(["z", "a"]).zip(subjects) {
                assert_eq!(s(get(binding, "name")), name);
                assert_json(
                    value(&result, get(binding, "value")),
                    &format!(r#"["v","{subject}"]"#),
                );
            }
            if case == "off-diagonal" {
                let facts = arr(get(data, "facts"));
                for subject in ["p", "q", "r", "s"] {
                    assert!(facts.iter().any(|fact| s(get(fact, "subject")) == subject
                        && s(get(fact, "field")) == "Reservations.State.free"));
                }
            }
        }
        if code == 2 {
            assert!(!has(m, "counterexamples"));
            let plan = value(&result, get(get(answer(&result, "n"), "outputs"), "plan"));
            assert!(arr(get(plan, "requirements")).iter().any(|r| {
                let field = get(r, "field");
                s(get(field, "subject")) == "p"
                    && s(get(field, "field")) == "Reservations.State.free"
            }));
        }
        if delivery {
            let mut reuse = args.clone();
            reuse.extend(["--out", "again", "--reuse", "out"]);
            let run = cli::run(&dir, &reuse);
            assert_eq!(run.code, code, "{case}: {}", run.stdout);
            let again = result_json(&dir, &run);
            assert!(warnings(&again).is_empty());
            for key in ["answers", "nodes"] {
                assert_eq!(
                    get(&result, key).value,
                    get(&again, key).value,
                    "{case}: {key}"
                );
            }
        }
        if case == "preserved" {
            args.extend([
                "--ask",
                "b=build(After,on=$m.map.target.base.subject)",
                "--out",
                "consumed",
            ]);
            let run = cli::run(&dir, &args);
            assert_eq!(run.code, 0, "{}", run.stdout);
            let consumed = result_json(&dir, &run);
            assert_eq!(s(get(answer(&consumed, "b"), "status")), "established");
        }
    }
}

#[test]
fn local_boolean_expression_reads_preserve_false_and_all_reference_tuples() {
    for (case, source_guard, target_guard, source_read, target_read, missing, code) in [
        (
            "preserved",
            "",
            "",
            "z.free<a.free",
            "y.free<x.free",
            false,
            0,
        ),
        (
            "off-diagonal",
            "",
            "",
            "z.free<a.free",
            "if y.held=1 and x.free=2 then false else y.free<x.free",
            false,
            1,
        ),
        ("false-held", "", "", "z.free<0", "y.free<0", false, 0),
        ("false-refuted", "", "", "z.free<0", "y.free>=0", false, 1),
        (
            "expanded",
            "z.free=2 and a.held=1",
            "y.free>0",
            "z.free<a.free",
            "y.free<x.free",
            false,
            0,
        ),
        ("missing", "", "", "z.free<a.free", "y.free<x.free", true, 2),
        (
            "inactive-target-unknown",
            "z.held=1 and a.held=1",
            "y.free>0 and x.free>0",
            "z.free<a.free",
            "y.free<x.free",
            true,
            0,
        ),
    ] {
        let dir = four_state_inputs(&format!("local-boolean-{case}"));
        if missing {
            let map = std::fs::read_to_string(dir.join("a.json"))
                .unwrap()
                .lines()
                .filter(|line| {
                    !line.contains(r#""id":"p-free""#) && !line.contains(r#""id":"r-free""#)
                })
                .collect::<Vec<_>>()
                .join("\n");
            std::fs::write(dir.join("a.json"), map).unwrap();
        }
        let vocabulary = r#"use vocabulary Reservations version "1" digest "sha256:8427a2712c22d6eed1cdd5f48258bea102904173558a7087bb82c7d95665c9ff";"#;
        let source_guard = if source_guard.is_empty() {
            String::new()
        } else {
            format!("when {source_guard}")
        };
        let target_guard = if target_guard.is_empty() {
            String::new()
        } else {
            format!("when {target_guard}")
        };
        std::fs::write(
            dir.join("l.law"),
            format!(
                r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{vocabulary} local here(z:State,a:State) {source_guard} reads {source_read};}}
reading After {{{vocabulary} local here(y:State,x:State) {target_guard} reads {target_read};}}"#
            ),
        )
        .unwrap();
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
        for request in &requests {
            args.extend(["--ask", request]);
        }
        let delivery = matches!(case, "preserved" | "off-diagonal" | "missing");
        let normal = delivery.then(|| without_file_changes(&dir, || cli::run(&dir, &args)));
        let run = asks(&dir, &requests);
        assert_eq!(run.code, code, "{case}: {}", run.stdout);
        let result = result_json(&dir, &run);
        if let Some(normal) = &normal {
            assert_eq!(normal.code, code, "{case}: {}", normal.stdout);
            assert_map_summary(normal, &result);
            assert!(normal.stderr.is_empty());
        }
        let m = answer(&result, "m");
        assert_eq!(
            s(get(m, "status")),
            match code {
                0 => "established",
                1 => "refuted",
                _ => "undetermined",
            }
        );
        assert!(has(get(m, "outputs"), "operation"));
        assert_eq!(has(get(m, "outputs"), "map"), code == 0);
        assert_eq!(s(get(answer(&result, "same"), "status")), "established");
        if code == 0 {
            let map = value(&result, get(get(m, "outputs"), "map"));
            let transport = value(&result, &arr(get(map, "transports"))[0]);
            assert_json(get(transport, "parameters"), r#"[["z","y"],["a","x"]]"#);
            let clause = &arr(get(transport, "clauses"))[0];
            assert_local_clause(
                &dir,
                &result,
                clause,
                source_read,
                target_read,
                &[("z", "Reservations.State"), ("a", "Reservations.State")],
            );
            let values = value(&result, get(clause, "values"));
            assert_json(get(values, "source_type"), r#""Bool""#);
            assert_json(get(values, "target_type"), r#""Bool""#);
            let arguments = value(&result, get(clause, "arguments"));
            assert_reference_pairs(
                &result,
                arguments,
                &[("p", "r"), ("q", "s"), ("r", "r"), ("s", "s")],
            );
        }
        if code == 1 {
            let examples = arr(get(m, "counterexamples"));
            assert_eq!(examples.len(), 1);
            let data = get(value(&result, &examples[0]), "data");
            let (left, right, subjects) = if case == "off-diagonal" {
                ("true", "false", ["q", "p"])
            } else {
                ("false", "true", ["p", "p"])
            };
            assert_json(value(&result, get(data, "left")), left);
            assert_json(value(&result, get(data, "right")), right);
            let bindings = arr(get(data, "bindings"));
            assert_eq!(bindings.len(), 2);
            for ((binding, name), subject) in bindings.iter().zip(["z", "a"]).zip(subjects) {
                assert_eq!(s(get(binding, "name")), name);
                assert_json(
                    value(&result, get(binding, "value")),
                    &format!(r#"["v","{subject}"]"#),
                );
            }
            if case == "off-diagonal" {
                let facts = arr(get(data, "facts"));
                for subject in ["p", "q", "r", "s"] {
                    assert!(facts.iter().any(|fact| s(get(fact, "subject")) == subject
                        && s(get(fact, "field")) == "Reservations.State.free"));
                }
            }
        }
        if code == 2 {
            assert!(!has(m, "counterexamples"));
            let plan = value(&result, get(get(answer(&result, "n"), "outputs"), "plan"));
            assert!(arr(get(plan, "requirements")).iter().any(|r| {
                let field = get(r, "field");
                s(get(field, "subject")) == "p"
                    && s(get(field, "field")) == "Reservations.State.free"
            }));
        }
        if delivery {
            let mut reuse = args.clone();
            reuse.extend(["--out", "again", "--reuse", "out"]);
            let run = cli::run(&dir, &reuse);
            assert_eq!(run.code, code, "{case}: {}", run.stdout);
            let again = result_json(&dir, &run);
            assert!(warnings(&again).is_empty());
            for key in ["answers", "nodes"] {
                assert_eq!(
                    get(&result, key).value,
                    get(&again, key).value,
                    "{case}: {key}"
                );
            }
        }
        if case == "preserved" {
            args.extend([
                "--ask",
                "b=build(After,on=$m.map.target.base.subject)",
                "--out",
                "consumed",
            ]);
            let run = cli::run(&dir, &args);
            assert_eq!(run.code, 0, "{}", run.stdout);
            let consumed = result_json(&dir, &run);
            assert_eq!(s(get(answer(&consumed, "b"), "status")), "established");
        }
    }
}

#[test]
fn local_rational_reads_compare_exact_values_on_all_reference_rows() {
    #[allow(dead_code)]
    #[path = "common/architecture_environment.rs"]
    mod fixture;
    use archsig::canonical::Json;
    for (case, source_guard, target_guard, target_read, missing, code) in [
        ("preserved", "", "", "x.free+y.free", false, 0),
        (
            "off-diagonal",
            "",
            "",
            "if y.held=1 and x.held=0 then x.free+y.free+rat(1,6) else x.free+y.free",
            false,
            1,
        ),
        (
            "guarded",
            "when z.held=1",
            "when y.held=1",
            "x.free+y.free",
            false,
            0,
        ),
        (
            "guard-refuted",
            "when z.held=1",
            "when y.held=0",
            "x.free+y.free",
            false,
            1,
        ),
        ("missing", "", "", "x.free+y.free", true, 2),
        (
            "inactive-missing",
            "when z.held=1 and a.held=1",
            "when y.held=1",
            "x.free+y.free",
            true,
            0,
        ),
        ("zero-refuted", "", "", "x.free+y.free+rat(1,6)", false, 1),
    ] {
        let dir = four_state_inputs(&format!("local-rational-{case}"));
        let old = std::fs::read_to_string(dir.join("d.json")).unwrap();
        let definition = old.replace(
            r#""name": "free", "type": "Z""#,
            r#""name": "free", "type": "Q""#,
        );
        assert_ne!(definition, old);
        let before = archsig::definition::check_definitions(&[("d", old.as_bytes())]).unwrap();
        let after =
            archsig::definition::check_definitions(&[("d", definition.as_bytes())]).unwrap();
        let digest = &after.vocabularies["Reservations"].digest;
        let text = std::fs::read_to_string(dir.join("a.json"))
            .unwrap()
            .replace(&before.vocabularies["Reservations"].digest, digest);
        let mut map = fixture::owned(&archsig::json::parse(text.as_bytes()).unwrap());
        let atoms = fixture::atoms(&mut map);
        atoms.retain(|atom| !missing || !matches!(atom, Json::Obj(a) if matches!(a.get("id"), Some(Json::Str(id)) if id=="p-free" || id=="r-free")));
        for atom in atoms {
            let Json::Obj(a) = atom else { panic!("atom") };
            if matches!(a.get("field"), Some(Json::Str(f)) if f=="Reservations.State.free") {
                let numerator = if case == "zero-refuted" {
                    Json::str("0")
                } else {
                    a["value"].clone()
                };
                a.insert("value".into(), Json::Arr(vec![numerator, Json::str(if case == "zero-refuted" { "1" } else { "3" })]));
            }
        }
        std::fs::write(dir.join("d.json"), definition).unwrap();
        std::fs::write(dir.join("a.json"), map.canonical()).unwrap();
        std::fs::write(dir.join("l.law"), format!(r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{use vocabulary Reservations version "1" digest "{digest}"; local here(z:State,a:State) {source_guard} reads z.free+a.free;}}
reading After {{use vocabulary Reservations version "1" digest "{digest}"; local here(y:State,x:State) {target_guard} reads {target_read};}}"#)).unwrap();
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
            match code {
                0 => "established",
                1 => "refuted",
                _ => "undetermined",
            }
        );
        assert!(has(get(m, "outputs"), "operation"));
        assert_eq!(has(get(m, "outputs"), "map"), code == 0);
        assert_eq!(s(get(answer(&result, "same"), "status")), "established");
        if code == 0 {
            let map = value(&result, get(get(m, "outputs"), "map"));
            let transport = value(&result, &arr(get(map, "transports"))[0]);
            assert_json(get(transport, "parameters"), r#"[["z","y"],["a","x"]]"#);
            let clause = &arr(get(transport, "clauses"))[0];
            assert_local_clause(
                &dir,
                &result,
                clause,
                "z.free+a.free",
                target_read,
                &[("z", "Reservations.State"), ("a", "Reservations.State")],
            );
            let values = value(&result, get(clause, "values"));
            assert_json(get(values, "source_type"), r#""Q""#);
            assert_json(get(values, "target_type"), r#""Q""#);
        }
        if matches!(case, "off-diagonal" | "zero-refuted") {
            let examples = arr(get(m, "counterexamples"));
            assert_eq!(examples.len(), 1);
            let data = get(value(&result, &examples[0]), "data");
            assert_json(
                value(&result, get(data, "left")),
                if case == "off-diagonal" {
                    r#"["1","1"]"#
                } else {
                    r#"["0","1"]"#
                },
            );
            assert_json(
                value(&result, get(data, "right")),
                if case == "off-diagonal" {
                    r#"["7","6"]"#
                } else {
                    r#"["1","6"]"#
                },
            );
            let bindings = arr(get(data, "bindings"));
            assert_eq!(bindings.len(), 2);
            for ((binding, name), subject) in
                bindings
                    .iter()
                    .zip(["z", "a"])
                    .zip(if case == "off-diagonal" {
                        ["q", "p"]
                    } else {
                        ["p", "p"]
                    })
            {
                assert_eq!(s(get(binding, "name")), name);
                assert_json(
                    value(&result, get(binding, "value")),
                    &format!(r#"["v","{subject}"]"#),
                );
            }
        }
        if code == 2 {
            assert!(!has(m, "counterexamples"));
            let plan = value(&result, get(get(answer(&result, "n"), "outputs"), "plan"));
            assert!(arr(get(plan, "requirements")).iter().any(|r| {
                let field = get(r, "field");
                s(get(field, "subject")) == "p"
                    && s(get(field, "field")) == "Reservations.State.free"
            }));
        }
        let mut args = vec![
            "run",
            "--atom-definition",
            "d.json",
            "--law",
            "l.law",
            "--archmap",
            "a.json",
        ];
        for request in &requests {
            args.extend(["--ask", request]);
        }
        let normal = without_file_changes(&dir, || cli::run(&dir, &args));
        assert_eq!(normal.code, code, "{case}: {}", normal.stdout);
        assert_map_summary(&normal, &result);
        assert!(normal.stderr.is_empty());
        args.extend(["--out", "again", "--reuse", "out"]);
        let reused = cli::run(&dir, &args);
        assert_eq!(reused.code, code, "{case}: {}", reused.stdout);
        let again = result_json(&dir, &reused);
        assert!(warnings(&again).is_empty());
        for key in ["answers", "nodes"] {
            assert_eq!(
                get(&result, key).value,
                get(&again, key).value,
                "{case}: {key}"
            );
        }
    }
}

#[test]
fn local_boolean_parameters_keep_mixed_positions_and_all_assignments() {
    let source_read = "if take then z.free else if mode then a.free else 0";
    let target_read = "if keep then y.free else if other then x.free else 0";
    for (case, sg, tg, sr, tr, missing, code) in [
        (
            "rational",
            "",
            "",
            "if take then rat(1,3) else rat(2,3)",
            "if keep then rat(1,3) else rat(2,3)",
            false,
            0,
        ),
        (
            "unknown-target",
            "when take",
            "when if keep then y.free>0 else false",
            source_read,
            target_read,
            true,
            2,
        ),
        ("preserved", "", "", source_read, target_read, false, 0),
        (
            "late-row",
            "",
            "",
            source_read,
            "if keep and not other and y.held=1 and x.free=2 then y.free+1 else if keep then y.free else if other then x.free else 0",
            false,
            1,
        ),
        ("projection", "", "", "take", "keep", false, 0),
        ("reference", "", "", "a", "x", false, 0),
        ("field", "", "", "a.free", "x.free", false, 0),
        (
            "false-refuted",
            "",
            "",
            "take and mode",
            "keep or other",
            false,
            1,
        ),
        (
            "expanded",
            "when take and z.held=1",
            "when keep or other",
            source_read,
            target_read,
            false,
            0,
        ),
        (
            "guard-refuted",
            "when take",
            "when keep and other",
            source_read,
            target_read,
            false,
            1,
        ),
        (
            "unknown-guard",
            "when if take then z.free>0 else false",
            "when keep",
            source_read,
            target_read,
            true,
            2,
        ),
        (
            "inactive-missing",
            "when take and z.held=1",
            "when if keep then y.free>0 else true",
            source_read,
            target_read,
            true,
            0,
        ),
        (
            "missing-read",
            "",
            "",
            "if take then z.free else 0",
            "if keep then y.free else 0",
            true,
            2,
        ),
    ] {
        let dir = four_state_inputs(&format!("local-bool-parameter-{case}"));
        if missing {
            let map = std::fs::read_to_string(dir.join("a.json"))
                .unwrap()
                .lines()
                .filter(|line| {
                    !line.contains(r#""id":"p-free""#) && !line.contains(r#""id":"r-free""#)
                })
                .collect::<Vec<_>>()
                .join("\n");
            std::fs::write(dir.join("a.json"), map).unwrap();
        }
        let vocabulary = r#"use vocabulary Reservations version "1" digest "sha256:8427a2712c22d6eed1cdd5f48258bea102904173558a7087bb82c7d95665c9ff";"#;
        std::fs::write(
            dir.join("l.law"),
            format!(
                r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{vocabulary} local here(z:State,take:Bool,a:State,mode:Bool) {sg} reads {sr};}}
reading After {{{vocabulary} local here(y:State,keep:Bool,x:State,other:Bool) {tg} reads {tr};}}"#
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
            match code {
                0 => "established",
                1 => "refuted",
                _ => "undetermined",
            }
        );
        assert!(has(get(m, "outputs"), "operation"));
        assert_eq!(has(get(m, "outputs"), "map"), code == 0);
        assert_eq!(s(get(answer(&result, "same"), "status")), "established");
        if code == 0 {
            let map = value(&result, get(get(m, "outputs"), "map"));
            let transport = value(&result, &arr(get(map, "transports"))[0]);
            assert_json(
                get(transport, "parameters"),
                r#"[["z","y"],["take","keep"],["a","x"],["mode","other"]]"#,
            );
            let clause = &arr(get(transport, "clauses"))[0];
            let arguments = value(&result, get(clause, "arguments"));
            assert_json(
                get(arguments, "source_type"),
                r#"["Tuple",["Ref","Reservations.State"],"Bool",["Ref","Reservations.State"],"Bool"]"#,
            );
            assert_reference_pairs(
                &result,
                arguments,
                &[("p", "r"), ("q", "s"), ("r", "r"), ("s", "s")],
            );
            let qs = arr(get(value(&result, get(clause, "commutes")), "quantifiers"));
            assert_eq!(qs.len(), 4);
            for ((q, name), ty) in qs.iter().zip(["z", "take", "a", "mode"]).zip([
                r#"["Ref","Reservations.State"]"#,
                r#""Bool""#,
                r#"["Ref","Reservations.State"]"#,
                r#""Bool""#,
            ]) {
                assert_eq!(s(get(q, "name")), name);
                assert_json(get(q, "type"), ty);
            }
            if case == "projection" {
                let values = value(&result, get(clause, "values"));
                assert_json(get(values, "source_type"), r#""Bool""#);
            }
        }
        if matches!(case, "late-row" | "false-refuted") {
            let examples = arr(get(m, "counterexamples"));
            assert_eq!(examples.len(), 1);
            let data = get(value(&result, &examples[0]), "data");
            let bs = arr(get(data, "bindings"));
            assert_eq!(bs.len(), 4);
            for (b, name) in bs.iter().zip(["z", "take", "a", "mode"]) {
                assert_eq!(s(get(b, "name")), name);
            }
            let late = case == "late-row";
            assert_json(
                value(&result, get(&bs[0], "value")),
                if late { r#"["v","q"]"# } else { r#"["v","p"]"# },
            );
            assert_json(
                value(&result, get(&bs[1], "value")),
                if late { "true" } else { "false" },
            );
            assert_json(value(&result, get(&bs[2], "value")), r#"["v","p"]"#);
            assert_json(
                value(&result, get(&bs[3], "value")),
                if late { "false" } else { "true" },
            );
            assert_json(
                value(&result, get(data, "left")),
                if late { r#""1""# } else { "false" },
            );
            assert_json(
                value(&result, get(data, "right")),
                if late { r#""2""# } else { "true" },
            );
        }
        if code == 2 {
            assert!(!has(m, "counterexamples"));
            let plan = value(&result, get(get(answer(&result, "n"), "outputs"), "plan"));
            assert!(arr(get(plan, "requirements")).iter().any(|r| {
                let f = get(r, "field");
                s(get(f, "subject")) == if case == "unknown-target" { "r" } else { "p" }
                    && s(get(f, "field")) == "Reservations.State.free"
            }));
        }
        if matches!(case, "preserved" | "late-row" | "missing-read") {
            let mut args = vec![
                "run",
                "--atom-definition",
                "d.json",
                "--law",
                "l.law",
                "--archmap",
                "a.json",
            ];
            for request in &requests {
                args.extend(["--ask", request]);
            }
            let normal = without_file_changes(&dir, || cli::run(&dir, &args));
            assert_eq!(normal.code, code, "{case}: {}", normal.stdout);
            assert!(normal.stderr.is_empty());
            assert_map_summary(&normal, &result);
            args.extend(["--out", "again", "--reuse", "out"]);
            let reused = cli::run(&dir, &args);
            assert_eq!(reused.code, code, "{case}: {}", reused.stdout);
            let again = result_json(&dir, &reused);
            assert!(warnings(&again).is_empty());
            for key in ["answers", "nodes"] {
                assert_eq!(
                    get(&result, key).value,
                    get(&again, key).value,
                    "{case}: {key}"
                );
            }
        }
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
    let digest = &after.vocabularies["Reservations"].digest;
    let map = std::fs::read_to_string(dir.join("a.json"))
        .unwrap()
        .replace(&before.vocabularies["Reservations"].digest, digest);
    std::fs::write(dir.join("d.json"), definition).unwrap();
    std::fs::write(dir.join("a.json"), map).unwrap();
    (
        dir,
        format!(r#"use vocabulary Reservations version "1" digest "{digest}";"#),
    )
}

#[test]
fn local_finite_parameters_share_full_domain_transport_without_type_branches() {
    for (name, ty, t_condition, u_condition, t_value, u_value, wire_type) in [
        ("unit", "Unit", "@=unit", "@=unit", "[]", "[]", r#""Unit""#),
        (
            "prime",
            "Fp(3)",
            "@=2",
            "@=1",
            r#""2""#,
            r#""1""#,
            r#"["Fp","3"]"#,
        ),
        (
            "option",
            "Option<Bool>",
            "@=some(true)",
            "@=some(false)",
            r#"{"some":true}"#,
            r#"{"some":false}"#,
            r#"["Option","Bool"]"#,
        ),
        (
            "set",
            "Set<Bool>",
            "true in @ and false in @",
            "false in @ and not (true in @)",
            "[false,true]",
            "[false]",
            r#"["Set","Bool"]"#,
        ),
        (
            "tuple",
            "(Bool,Fp(3))",
            "@.0 and @.1=2",
            "not @.0 and @.1=1",
            r#"[true,"2"]"#,
            r#"[false,"1"]"#,
            r#"["Tuple","Bool",["Fp","3"]]"#,
        ),
        (
            "data",
            "Choice",
            "@=Full(true)",
            "@=Empty",
            r#"{"args":[true],"tag":"Full"}"#,
            r#"{"args":[],"tag":"Empty"}"#,
            r#"["Data","Reservations.Choice"]"#,
        ),
    ] {
        for (case, code) in [("preserved", 0), ("late-row", 1)] {
            let (dir, vocabulary) =
                finite_local_parameter_inputs(&format!("local-finite-{name}-{case}"));
            let pc = t_condition.replace('@', "p");
            let tc = t_condition.replace('@', "t");
            let qc = u_condition.replace('@', "q");
            let sr = format!("if {tc} then z.free else a.free");
            let base = format!("if {pc} then y.free else x.free");
            let tr = if code == 0 {
                base
            } else {
                format!("if ({pc}) and ({qc}) and y.held=1 and x.free=2 then y.free+1 else {base}")
            };
            std::fs::write(
                dir.join("l.law"),
                format!(
                    r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{vocabulary} local here(t:{ty},z:State,u:{ty},a:State) reads {sr};}}
reading After {{{vocabulary} local here(p:{ty},y:State,q:{ty},x:State) reads {tr};}}"#
                ),
            )
            .unwrap();
            let requests = [
                "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
                "same=compare($m.operation,to=$m.operation,kind=action)",
                "n=needed($m)",
            ];
            let run = asks(&dir, &requests);
            assert_eq!(run.code, code, "{name}/{case}: {}", run.stdout);
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
                assert_json(
                    get(transport, "parameters"),
                    r#"[["t","p"],["z","y"],["u","q"],["a","x"]]"#,
                );
                let clause = &arr(get(transport, "clauses"))[0];
                let args = value(&result, get(clause, "arguments"));
                assert_json(
                    get(args, "source_type"),
                    &format!(
                        r#"["Tuple",{wire_type},["Ref","Reservations.State"],{wire_type},["Ref","Reservations.State"]]"#
                    ),
                );
                assert_reference_pairs(
                    &result,
                    args,
                    &[("p", "r"), ("q", "s"), ("r", "r"), ("s", "s")],
                );
                if name == "data" {
                    let declarations = arr(get(args, "declarations"));
                    for family in [
                        "Reservations.Choice",
                        "Reservations.Choice.Empty",
                        "Reservations.Choice.Full",
                    ] {
                        assert!(
                            declarations
                                .iter()
                                .any(|d| arr(d).iter().map(s).collect::<Vec<_>>()
                                    == [family, family])
                        );
                    }
                }
                let qs = arr(get(value(&result, get(clause, "commutes")), "quantifiers"));
                assert_eq!(qs.len(), 4);
                for (q, name) in qs.iter().zip(["t", "z", "u", "a"]) {
                    assert_eq!(s(get(q, "name")), name);
                }
                assert_json(get(&qs[0], "type"), wire_type);
                assert_json(get(&qs[2], "type"), wire_type);
            } else {
                let examples = arr(get(m, "counterexamples"));
                assert_eq!(examples.len(), 1);
                let data = get(value(&result, &examples[0]), "data");
                let bs = arr(get(data, "bindings"));
                assert_eq!(bs.len(), 4);
                for ((b, name), expected) in bs.iter().zip(["t", "z", "u", "a"]).zip([
                    t_value,
                    r#"["v","q"]"#,
                    u_value,
                    r#"["v","p"]"#,
                ]) {
                    assert_eq!(s(get(b, "name")), name);
                    assert_json(value(&result, get(b, "value")), expected);
                }
                assert_json(value(&result, get(data, "left")), r#""1""#);
                assert_json(value(&result, get(data, "right")), r#""2""#);
            }
            if matches!(
                (name, case),
                ("data", "preserved") | ("tuple", "late-row") | ("set", "late-row")
            ) {
                let mut args = vec![
                    "run",
                    "--atom-definition",
                    "d.json",
                    "--law",
                    "l.law",
                    "--archmap",
                    "a.json",
                ];
                for request in &requests {
                    args.extend(["--ask", request]);
                }
                let normal = without_file_changes(&dir, || cli::run(&dir, &args));
                assert_eq!(normal.code, code, "{name}/{case}: {}", normal.stdout);
                assert!(normal.stderr.is_empty());
                assert_map_summary(&normal, &result);
                args.extend(["--out", "again", "--reuse", "out"]);
                let reused = cli::run(&dir, &args);
                assert_eq!(reused.code, code, "{}", reused.stdout);
                let again = result_json(&dir, &reused);
                assert!(warnings(&again).is_empty());
                for key in ["answers", "nodes"] {
                    assert_eq!(
                        get(&result, key).value,
                        get(&again, key).value,
                        "{name}/{case}: {key}"
                    );
                }
            }
        }
    }
}

#[test]
fn local_finite_parameters_preserve_directional_guards_and_missing_values() {
    for (case, sg, tg, missing, code) in [
        (
            "expanded",
            "when choice=some(true) and mode=2 and z.held=1",
            "when pick!=none<Bool>",
            false,
            0,
        ),
        (
            "refuted",
            "when choice=some(true) and mode=2",
            "when pick=some(true) and level=1",
            false,
            1,
        ),
        (
            "unknown-source",
            "when if choice=some(true) and mode=2 then z.free>0 else false",
            "when pick=some(true) and level=2",
            true,
            2,
        ),
        (
            "unknown-target",
            "when choice=some(true) and mode=2",
            "when if level=2 then y.free>0 else false",
            true,
            2,
        ),
        (
            "inactive-missing",
            "when choice=some(true) and mode=2 and z.held=1",
            "when if level=2 then y.free>0 else false",
            true,
            0,
        ),
        (
            "missing-read",
            "when choice=some(true) and mode=2",
            "",
            true,
            2,
        ),
    ] {
        let (dir, vocabulary) =
            finite_local_parameter_inputs(&format!("local-finite-guard-{case}"));
        if missing {
            let map = std::fs::read_to_string(dir.join("a.json"))
                .unwrap()
                .lines()
                .filter(|line| {
                    !line.contains(r#""id":"p-free""#) && !line.contains(r#""id":"r-free""#)
                })
                .collect::<Vec<_>>()
                .join("\n");
            std::fs::write(dir.join("a.json"), map).unwrap();
        }
        std::fs::write(dir.join("l.law"),format!(r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{vocabulary} local here(unitarg:Unit,z:State,choice:Option<Bool>,mode:Fp(3)) {sg} reads if choice=some(true) and mode=2 then z.free else 0;}}
reading After {{{vocabulary} local here(unused:Unit,y:State,pick:Option<Bool>,level:Fp(3)) {tg} reads if pick=some(true) and level=2 then y.free else 0;}}"#)).unwrap();
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
            match code {
                0 => "established",
                1 => "refuted",
                _ => "undetermined",
            }
        );
        assert!(has(get(m, "outputs"), "operation"));
        assert_eq!(has(get(m, "outputs"), "map"), code == 0);
        assert_eq!(s(get(answer(&result, "same"), "status")), "established");
        if case == "refuted" {
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
        if code == 2 {
            assert!(!has(m, "counterexamples"));
            let plan = value(&result, get(get(answer(&result, "n"), "outputs"), "plan"));
            let subject = if case == "unknown-target" { "r" } else { "p" };
            assert!(arr(get(plan, "requirements")).iter().any(|r| {
                let f = get(r, "field");
                s(get(f, "subject")) == subject && s(get(f, "field")) == "Reservations.State.free"
            }));
        }
        if code == 2 || case == "refuted" {
            let mut args = vec![
                "run",
                "--atom-definition",
                "d.json",
                "--law",
                "l.law",
                "--archmap",
                "a.json",
            ];
            for request in &requests {
                args.extend(["--ask", request]);
            }
            let normal = without_file_changes(&dir, || cli::run(&dir, &args));
            assert_eq!(normal.code, code, "{}", normal.stdout);
            assert!(normal.stderr.is_empty());
            assert_map_summary(&normal, &result);
            args.extend(["--out", "again", "--reuse", "out"]);
            let reused = cli::run(&dir, &args);
            assert_eq!(reused.code, code, "{}", reused.stdout);
            let again = result_json(&dir, &reused);
            assert!(warnings(&again).is_empty());
            for key in ["answers", "nodes"] {
                assert_eq!(
                    get(&result, key).value,
                    get(&again, key).value,
                    "{case}: {key}"
                );
            }
        }
    }
}

#[test]
fn local_finite_parameter_extension_keeps_other_domains_unsupported() {
    for (name, ty, read) in [
        ("rational", "Q", "0+0"),
        ("text", "Text", "0+0"),
        ("list", "List<Bool>", "0+0"),
        ("tuple-integer", "(State,Z)", "0+0"),
        ("option-rational", "Option<(State,Q)>", "0+0"),
    ] {
        let (dir, vocabulary) =
            finite_local_parameter_inputs(&format!("local-finite-outside-{name}"));
        std::fs::write(
            dir.join("l.law"),
            format!(
                r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{vocabulary} local here(x:{ty}) reads {read};}}
reading After {{{vocabulary} local here(x:{ty}) reads {read};}}"#
            ),
        )
        .unwrap();
        let run = without_file_changes(&dir, || {
            cli::run(
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
                    "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
                ],
            )
        });
        assert_eq!(run.code, 70, "{name}: {}", run.stdout);
        assert!(run.stderr.is_empty());
        assert!(has(&run.receipt, "issues"));
    }
}

#[test]
fn local_finite_primitive_projections_use_the_checked_type_value_map() {
    for (name, ty, wire) in [
        ("unit", "Unit", r#""Unit""#),
        ("prime", "Fp(3)", r#"["Fp","3"]"#),
    ] {
        let (dir, vocabulary) =
            finite_local_parameter_inputs(&format!("local-finite-projection-{name}"));
        std::fs::write(
            dir.join("l.law"),
            format!(
                r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{vocabulary} local here(x:{ty}) reads x;}}
reading After {{{vocabulary} local here(y:{ty}) reads y;}}"#
            ),
        )
        .unwrap();
        let run = asks(
            &dir,
            &[
                "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
            ],
        );
        assert_eq!(run.code, 0, "{name}: {}", run.stdout);
        let result = result_json(&dir, &run);
        let m = answer(&result, "m");
        assert_eq!(s(get(m, "status")), "established");
        let map = value(&result, get(get(m, "outputs"), "map"));
        let transport = value(&result, &arr(get(map, "transports"))[0]);
        let clause = &arr(get(transport, "clauses"))[0];
        let values = value(&result, get(clause, "values"));
        assert_json(get(values, "source_type"), wire);
        assert_json(get(values, "target_type"), wire);
        assert!(arr(get(values, "subjects")).is_empty());
        assert!(arr(get(values, "declarations")).is_empty());
    }
}

#[test]
fn local_composite_argument_reads_keep_the_checked_full_domain_value_map() {
    for (name, ty, wire_type, identities) in [
        ("option", "Option<Bool>", r#"["Option","Bool"]"#, false),
        ("set", "Set<Bool>", r#"["Set","Bool"]"#, false),
        (
            "tuple",
            "(Bool,Fp(3))",
            r#"["Tuple","Bool",["Fp","3"]]"#,
            false,
        ),
        ("data", "Choice", r#"["Data","Reservations.Choice"]"#, true),
    ] {
        let (dir, vocabulary) =
            finite_local_parameter_inputs(&format!("local-composite-projection-{name}"));
        if name == "option" {
            let map = std::fs::read_to_string(dir.join("a.json"))
                .unwrap()
                .lines()
                .filter(|line| {
                    !line.contains(r#""id":"p-free""#) && !line.contains(r#""id":"r-free""#)
                })
                .collect::<Vec<_>>()
                .join("\n");
            std::fs::write(dir.join("a.json"), map).unwrap();
        }
        std::fs::write(
            dir.join("l.law"),
            format!(
                r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{vocabulary} local here(z:State,choice:{ty},other:{ty}) reads choice;}}
reading After {{{vocabulary} local here(y:State,pick:{ty},spare:{ty}) reads pick;}}"#
            ),
        )
        .unwrap();
        let requests = [
            "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
            "same=compare($m.operation,to=$m.operation,kind=action)",
            "n=needed($m)",
        ];
        let run = asks(&dir, &requests);
        assert_eq!(run.code, 0, "{name}: {}", run.stdout);
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
        for side in ["source", "target"] {
            let domain = value(&result, get(values, side));
            assert_eq!(s(get(domain, "kind")), "type");
            assert_json(get(domain, "type"), wire_type);
        }
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
        if identities {
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
        } else {
            assert!(arr(get(values, "declarations")).is_empty());
        }
        let law = std::fs::read(dir.join("l.law")).unwrap();
        for (side, name) in [("source", "choice"), ("target", "pick")] {
            let expr = value(&result, get(clause, side));
            let location = get(expr, "location");
            assert_eq!(s(get(location, "input")), "law");
            let span = arr(get(location, "span"));
            assert_eq!(
                &law[num(&span[0]) as usize..num(&span[1]) as usize],
                name.as_bytes()
            );
        }
        let qs = arr(get(value(&result, get(clause, "commutes")), "quantifiers"));
        assert_eq!(qs.len(), 3);
        for (q, name) in qs.iter().zip(["z", "choice", "other"]) {
            assert_eq!(s(get(q, "name")), name);
        }
        assert_json(get(&qs[1], "type"), wire_type);
        assert_json(get(&qs[2], "type"), wire_type);
        let mut args = vec![
            "run",
            "--atom-definition",
            "d.json",
            "--law",
            "l.law",
            "--archmap",
            "a.json",
        ];
        for request in &requests {
            args.extend(["--ask", request]);
        }
        let normal = without_file_changes(&dir, || cli::run(&dir, &args));
        assert_eq!(normal.code, 0, "{name}: {}", normal.stdout);
        assert!(normal.stderr.is_empty());
        assert_map_summary(&normal, &result);
        args.extend(["--out", "again", "--reuse", "out"]);
        let reused = cli::run(&dir, &args);
        assert_eq!(reused.code, 0, "{name}: {}", reused.stdout);
        let again = result_json(&dir, &reused);
        assert!(warnings(&again).is_empty());
        for key in ["answers", "nodes"] {
            assert_eq!(
                get(&result, key).value,
                get(&again, key).value,
                "{name}: {key}"
            );
        }
    }
}

#[test]
fn local_composite_argument_reads_keep_guard_direction_and_missing_distinct() {
    for (case, sg, tg, missing, code) in [
        (
            "expanded",
            "when choice=Full(true) and extra=some(false) and z.held=1",
            "when pick!=Empty",
            false,
            0,
        ),
        (
            "refuted",
            "when choice=Full(true) and extra=some(false)",
            "when pick=Full(false)",
            false,
            1,
        ),
        (
            "unknown-source",
            "when if choice=Full(true) and extra=some(false) then z.free>0 else false",
            "when pick=Full(true)",
            true,
            2,
        ),
        (
            "unknown-target",
            "when choice=Full(true) and extra=some(false)",
            "when if pick=Full(true) then y.free>0 else false",
            true,
            2,
        ),
        (
            "inactive-missing",
            "when choice=Full(true) and extra=some(false) and z.held=1",
            "when if pick=Full(true) then y.free>0 else false",
            true,
            0,
        ),
        ("false-source", "when false", "when y.free>0", true, 0),
        (
            "empty-source",
            "when choice=Full(true) and choice=Empty",
            "when false",
            false,
            0,
        ),
    ] {
        let (dir, vocabulary) =
            finite_local_parameter_inputs(&format!("local-composite-guard-{case}"));
        if missing {
            let map = std::fs::read_to_string(dir.join("a.json"))
                .unwrap()
                .lines()
                .filter(|line| {
                    !line.contains(r#""id":"p-free""#) && !line.contains(r#""id":"r-free""#)
                })
                .collect::<Vec<_>>()
                .join("\n");
            std::fs::write(dir.join("a.json"), map).unwrap();
        }
        std::fs::write(dir.join("l.law"),format!(r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{vocabulary} local here(choice:Choice,z:State,extra:Option<Bool>) {sg} reads choice;}}
reading After {{{vocabulary} local here(pick:Choice,y:State,spare:Option<Bool>) {tg} reads pick;}}"#)).unwrap();
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
            match code {
                0 => "established",
                1 => "refuted",
                _ => "undetermined",
            }
        );
        assert!(has(get(m, "outputs"), "operation"));
        assert_eq!(has(get(m, "outputs"), "map"), code == 0);
        assert_eq!(s(get(answer(&result, "same"), "status")), "established");
        if case == "refuted" {
            let data = get(value(&result, &arr(get(m, "counterexamples"))[0]), "data");
            let bs = arr(get(data, "bindings"));
            assert_eq!(bs.len(), 3);
            for ((b, name), expected) in bs.iter().zip(["choice", "z", "extra"]).zip([
                r#"{"args":[true],"tag":"Full"}"#,
                r#"["v","p"]"#,
                r#"{"some":false}"#,
            ]) {
                assert_eq!(s(get(b, "name")), name);
                assert_json(value(&result, get(b, "value")), expected);
            }
            assert_json(value(&result, get(data, "left")), "true");
            assert_json(value(&result, get(data, "right")), "false");
        }
        let plan = value(&result, get(get(answer(&result, "n"), "outputs"), "plan"));
        if code == 2 {
            assert!(!has(m, "counterexamples"));
            let subject = if case == "unknown-target" { "r" } else { "p" };
            assert!(arr(get(plan, "requirements")).iter().any(|r| {
                let f = get(r, "field");
                s(get(f, "subject")) == subject && s(get(f, "field")) == "Reservations.State.free"
            }));
        } else {
            assert!(arr(get(plan, "requirements")).is_empty());
        }
        if matches!(
            case,
            "refuted" | "unknown-source" | "unknown-target" | "inactive-missing"
        ) {
            let mut args = vec![
                "run",
                "--atom-definition",
                "d.json",
                "--law",
                "l.law",
                "--archmap",
                "a.json",
            ];
            for request in &requests {
                args.extend(["--ask", request]);
            }
            let normal = without_file_changes(&dir, || cli::run(&dir, &args));
            assert_eq!(normal.code, code, "{case}: {}", normal.stdout);
            assert!(normal.stderr.is_empty());
            assert_map_summary(&normal, &result);
            args.extend(["--out", "again", "--reuse", "out"]);
            let reused = cli::run(&dir, &args);
            assert_eq!(reused.code, code, "{case}: {}", reused.stdout);
            let again = result_json(&dir, &reused);
            assert!(warnings(&again).is_empty());
            for key in ["answers", "nodes"] {
                assert_eq!(
                    get(&result, key).value,
                    get(&again, key).value,
                    "{case}: {key}"
                );
            }
        }
    }
}

#[test]
fn local_composite_argument_read_guards_use_actual_reference_images() {
    for (condition, target_condition, code) in
        [("left=right", "a=b", 0), ("left!=right", "a!=b", 1)]
    {
        let (dir, vocabulary) =
            finite_local_parameter_inputs(&format!("local-composite-images-{code}"));
        std::fs::write(dir.join("l.law"),format!(r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{vocabulary} local here(left:State,choice:Option<Bool>,right:State) when {condition} reads choice;}}
reading After {{{vocabulary} local here(a:State,pick:Option<Bool>,b:State) when {target_condition} reads pick;}}"#)).unwrap();
        let run = asks(
            &dir,
            &[
                "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
                "same=compare($m.operation,to=$m.operation,kind=action)",
            ],
        );
        assert_eq!(run.code, code, "{}", run.stdout);
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
    }
}

#[test]
fn local_composite_reads_do_not_accept_unimplemented_expression_transports() {
    for (name, source_params, target_params, source_read, target_read) in [
        (
            "different-position",
            "x:Option<Bool>,y:Option<Bool>",
            "a:Option<Bool>,b:Option<Bool>",
            "x",
            "b",
        ),
        (
            "infinite-argument", "items:List<Z>,take:Bool", "items:List<Z>,keep:Bool",
            "if take then list<Z>[0] else items",
            "if keep then list<Z>[0] else items",
        ),
    ] {
        let (dir, vocabulary) =
            finite_local_parameter_inputs(&format!("local-composite-outside-{name}"));
        std::fs::write(
            dir.join("l.law"),
            format!(
                r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{vocabulary} local here({source_params}) reads {source_read};}}
reading After {{{vocabulary} local here({target_params}) reads {target_read};}}"#
            ),
        )
        .unwrap();
        let run = without_file_changes(&dir, || {
            cli::run(
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
                    "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
                ],
            )
        });
        assert_eq!(run.code, 70, "{name}: {}", run.stdout);
        assert!(run.stderr.is_empty());
        assert!(has(&run.receipt, "issues"));
    }
}

fn assert_local_structural_reference_arguments(
    shape: &str,
    ty: &str,
    condition: &str,
    target_condition: &str,
    choice_value: &str,
    other_value: &str,
) {
    for (case, source_guard, target_guard, source_read, target_read, code) in [
        ("projection", "", "", "choice", "pick", 0),
        ("expression", "", "", "if choice=other then other else choice", "if pick=spare then spare else pick", 0),
        ("expression-refuted", "", "", "if choice=other then other else choice", "spare", 1),
        ("expression-missing", "", "", "if z.free>0 then choice else other", "if y.free>0 then pick else spare", 2),
        (
            "actual-image",
            &format!(" when {condition}"),
            &format!(" when {target_condition}"),
            "choice",
            "pick",
            0,
        ),
        (
            "collision",
            " when choice!=other",
            " when pick!=spare",
            "choice",
            "pick",
            1,
        ),
        (
            "reverse",
            "",
            &format!(" when {target_condition}"),
            "choice",
            "pick",
            1,
        ),
        (
            "nonempty-row",
            "",
            "",
            &format!("if {condition} then 1 else 0"),
            "0",
            1,
        ),
        (
            "unknown-source",
            &format!(" when ({condition}) and z.free>0"),
            "",
            "choice",
            "pick",
            2,
        ),
        (
            "unknown-target",
            &format!(" when {condition}"),
            &format!(" when ({target_condition}) and y.free>0"),
            "choice",
            "pick",
            2,
        ),
        (
            "false-source",
            " when false",
            " when y.free>0",
            "choice",
            "pick",
            0,
        ),
        (
            "two-parameters",
            &format!(" when ({condition}) and other!=choice"),
            "",
            "1",
            "0",
            1,
        ),
    ] {
        let (dir, vocabulary) =
            finite_local_parameter_inputs(&format!("local-structural-ref-{shape}-{case}"));
        if case.starts_with("unknown-") || case == "false-source" || case == "expression-missing" {
            let map = std::fs::read_to_string(dir.join("a.json"))
                .unwrap()
                .lines()
                .filter(|line| {
                    !line.contains(r#""id":"p-free""#) && !line.contains(r#""id":"r-free""#)
                })
                .collect::<Vec<_>>()
                .join("\n");
            std::fs::write(dir.join("a.json"), map).unwrap();
        }
        std::fs::write(dir.join("l.law"), format!(r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{vocabulary} local here(z:State,choice:{ty},other:{ty}){source_guard} reads {source_read};}}
reading After {{{vocabulary} local here(y:State,pick:{ty},spare:{ty}){target_guard} reads {target_read};}}"#)).unwrap();
        let requests = [
            "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
            "same=compare($m.operation,to=$m.operation,kind=action)",
            "n=needed($m)",
        ];
        let run = asks(&dir, &requests);
        assert_eq!(run.code, code, "{shape}/{case}: {}", run.stdout);
        let result = result_json(&dir, &run);
        let m = answer(&result, "m");
        assert_eq!(
            s(get(m, "status")),
            match code {
                0 => "established",
                1 => "refuted",
                _ => "undetermined",
            }
        );
        assert!(has(get(m, "outputs"), "operation"));
        assert_eq!(s(get(answer(&result, "same"), "status")), "established");
        assert_eq!(has(get(m, "outputs"), "map"), code == 0);
        let plan = value(&result, get(get(answer(&result, "n"), "outputs"), "plan"));
        assert_eq!(arr(get(plan, "requirements")).is_empty(), code != 2);
        if code == 2 {
            assert!(!has(m, "counterexamples"));
        }
        if case == "expression-refuted" {
            let data = get(value(&result, &arr(get(m, "counterexamples"))[0]), "data");
            let bindings = arr(get(data, "bindings"));
            assert_eq!(bindings.len(), 3);
            for (binding, name) in bindings.iter().zip(["z", "choice", "other"]) {
                assert_eq!(s(get(binding, "name")), name);
            }
            let left = value(&result, get(data, "left"));
            let right = value(&result, get(data, "right"));
            assert_eq!(left.value, value(&result, get(&bindings[1], "value")).value);
            assert_ne!(left.value, right.value);
        }
        if case == "two-parameters" || case == "collision" {
            let data = get(value(&result, &arr(get(m, "counterexamples"))[0]), "data");
            let bindings = arr(get(data, "bindings"));
            assert_eq!(bindings.len(), 3);
            for (binding, name) in bindings.iter().zip(["z", "choice", "other"]) {
                assert_eq!(s(get(binding, "name")), name);
            }
            assert_json(value(&result, get(&bindings[0], "value")), r#"["v","p"]"#);
            assert_json(
                value(&result, get(&bindings[1], "value")),
                if case == "collision" {
                    match shape {
                        "tuple" => r#"[["v","p"],false]"#,
                        "nested" => r#"[{"some":["v","p"]},false]"#,
                        _ => choice_value,
                    }
                } else {
                    choice_value
                },
            );
            assert_json(
                value(&result, get(&bindings[2], "value")),
                if case == "collision" {
                    match shape {
                        "tuple" => r#"[["v","r"],false]"#,
                        "nested" => r#"[{"some":["v","r"]},false]"#,
                        _ => r#"{"some":["v","r"]}"#,
                    }
                } else {
                    other_value
                },
            );
        }
        if matches!(case, "projection" | "collision" | "unknown-target" | "expression" | "expression-refuted" | "expression-missing") {
            let mut args = vec![
                "run",
                "--atom-definition",
                "d.json",
                "--law",
                "l.law",
                "--archmap",
                "a.json",
            ];
            for request in &requests {
                args.extend(["--ask", request]);
            }
            let normal = without_file_changes(&dir, || cli::run(&dir, &args));
            assert_eq!(normal.code, code, "{shape}/{case}: {}", normal.stdout);
            assert!(normal.stderr.is_empty());
            assert_map_summary(&normal, &result);
            args.extend(["--out", "again", "--reuse", "out"]);
            let reused = cli::run(&dir, &args);
            assert_eq!(reused.code, code, "{shape}/{case}: {}", reused.stdout);
            let again = result_json(&dir, &reused);
            assert!(warnings(&again).is_empty());
            for key in ["answers", "nodes"] {
                assert_eq!(
                    get(&result, key).value,
                    get(&again, key).value,
                    "{shape}/{case}: {key}"
                );
            }
        }
        if code == 0 {
            let map = value(&result, get(get(m, "outputs"), "map"));
            let transport = value(&result, &arr(get(map, "transports"))[0]);
            let clause = &arr(get(transport, "clauses"))[0];
            let args = value(&result, get(clause, "arguments"));
            // p and r both map to r, q and s both map to s; target-only rows are permitted.
            assert_reference_pairs(
                &result,
                args,
                &[("p", "r"), ("q", "s"), ("r", "r"), ("s", "s")],
            );
            if case == "projection" || case == "expression" {
                let values = value(&result, get(clause, "values"));
                assert_reference_pairs(
                    &result,
                    values,
                    &[("p", "r"), ("q", "s"), ("r", "r"), ("s", "s")],
                );
            }
        }
    }
}

#[test]
fn local_structural_reference_arguments_follow_noninjective_images_and_all_source_rows() {
    for (shape, ty, condition, target_condition, choice_value, other_value) in [
        (
            "option",
            "Option<State>",
            "choice=some(z)",
            "pick=some(y)",
            r#"{"some":["v","p"]}"#,
            r#"{"none":true}"#,
        ),
        (
            "tuple",
            "(State,Bool)",
            "choice.0=z and choice.1",
            "pick.0=y and pick.1",
            r#"[["v","p"],true]"#,
            r#"[["v","p"],false]"#,
        ),
        (
            "nested",
            "(Option<State>,Bool)",
            "choice.0=some(z) and choice.1",
            "pick.0=some(y) and pick.1",
            r#"[{"some":["v","p"]},true]"#,
            r#"[{"none":true},false]"#,
        ),
    ] {
        assert_local_structural_reference_arguments(
            shape,
            ty,
            condition,
            target_condition,
            choice_value,
            other_value,
        );
    }
}

#[test]
fn local_reference_sets_use_direct_images_without_preserving_cardinality() {
    for (case, sg, tg, sr, tr, missing, code) in [
        ("projection", "", "", "members", "chosen", false, 0),
        ("expression", "", "", "if take then members else set<State>{}", "if keep then chosen else set<State>{}", false, 0),
        (
            "membership",
            " when left in members",
            " when right in chosen",
            "members",
            "chosen",
            false,
            0,
        ),
        (
            "cardinality-guard",
            " when count(members)=2",
            " when count(chosen)=2",
            "members",
            "chosen",
            false,
            1,
        ),
        (
            "reverse-membership",
            " when not(left in members)",
            " when not(right in chosen)",
            "members",
            "chosen",
            false,
            1,
        ),
        (
            "cardinality-read",
            "",
            "",
            "count(members)",
            "count(chosen)",
            false,
            1,
        ),
        (
            "empty-read",
            "",
            "",
            "count(members)=0",
            "count(chosen)=0",
            false,
            0,
        ),
        (
            "unknown-source",
            " when left in members and left.free>0",
            " when right in chosen",
            "members",
            "chosen",
            true,
            2,
        ),
        (
            "unknown-target",
            " when left in members",
            " when right in chosen and right.free>0",
            "members",
            "chosen",
            true,
            2,
        ),
        (
            "false-source",
            " when false",
            " when right.free>0",
            "members",
            "chosen",
            true,
            0,
        ),
        (
            "all-rows",
            " when take and count(members)=4",
            "",
            "1",
            "0",
            false,
            1,
        ),
    ] {
        let (dir, vocabulary) = finite_local_parameter_inputs(&format!("local-set-ref-{case}"));
        if missing {
            let map = std::fs::read_to_string(dir.join("a.json"))
                .unwrap()
                .lines()
                .filter(|line| {
                    !line.contains(r#""id":"p-free""#) && !line.contains(r#""id":"r-free""#)
                })
                .collect::<Vec<_>>()
                .join("\n");
            std::fs::write(dir.join("a.json"), map).unwrap();
        }
        std::fs::write(
            dir.join("l.law"),
            format!(
                r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{vocabulary} local here(left:State,members:Set<State>,take:Bool){sg} reads {sr};}}
reading After {{{vocabulary} local here(right:State,chosen:Set<State>,keep:Bool){tg} reads {tr};}}"#
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
            match code {
                0 => "established",
                1 => "refuted",
                _ => "undetermined",
            }
        );
        assert!(has(get(m, "outputs"), "operation"));
        assert_eq!(has(get(m, "outputs"), "map"), code == 0);
        assert_eq!(s(get(answer(&result, "same"), "status")), "established");
        let plan = value(&result, get(get(answer(&result, "n"), "outputs"), "plan"));
        assert_eq!(arr(get(plan, "requirements")).is_empty(), code != 2);
        if code == 2 {
            assert!(!has(m, "counterexamples"));
        }
        if code == 1 {
            let data = get(value(&result, &arr(get(m, "counterexamples"))[0]), "data");
            let bindings = arr(get(data, "bindings"));
            assert_eq!(bindings.len(), 3);
            for (binding, name) in bindings.iter().zip(["left", "members", "take"]) {
                assert_eq!(s(get(binding, "name")), name);
            }
            assert_json(value(&result, get(&bindings[0], "value")), r#"["v","p"]"#);
            assert_json(
                value(&result, get(&bindings[1], "value")),
                match case {
                    "reverse-membership" => r#"[["v","r"]]"#,
                    "all-rows" => r#"[["v","p"],["v","q"],["v","r"],["v","s"]]"#,
                    _ => r#"[["v","p"],["v","r"]]"#,
                },
            );
            assert_json(
                value(&result, get(&bindings[2], "value")),
                if case == "all-rows" { "true" } else { "false" },
            );
            let (left, right) = if case == "cardinality-read" {
                ("\"2\"", "\"1\"")
            } else if case == "all-rows" {
                ("\"1\"", "\"0\"")
            } else {
                ("true", "false")
            };
            assert_json(value(&result, get(data, "left")), left);
            assert_json(value(&result, get(data, "right")), right);
        }
        if case == "projection" {
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
        if matches!(case, "projection" | "cardinality-read" | "unknown-target" | "expression") {
            let mut args = vec![
                "run",
                "--atom-definition",
                "d.json",
                "--law",
                "l.law",
                "--archmap",
                "a.json",
            ];
            for request in &requests {
                args.extend(["--ask", request]);
            }
            let normal = without_file_changes(&dir, || cli::run(&dir, &args));
            assert_eq!(normal.code, code, "{case}: {}", normal.stdout);
            assert!(normal.stderr.is_empty());
            assert_map_summary(&normal, &result);
            args.extend(["--out", "again", "--reuse", "out"]);
            let reused = cli::run(&dir, &args);
            assert_eq!(reused.code, code, "{case}: {}", reused.stdout);
            let again = result_json(&dir, &reused);
            assert!(warnings(&again).is_empty());
            for key in ["answers", "nodes"] {
                assert_eq!(
                    get(&result, key).value,
                    get(&again, key).value,
                    "{case}: {key}"
                );
            }
        }
    }
}

#[test]
fn local_finite_data_arguments_follow_constructor_reference_images() {
    for (case, sg, tg, sr, tr, missing, code) in [
        ("projection", "", "", "packet", "chosen", false, 0),
        ("expression", "", "", "if take then packet else Empty", "if keep then chosen else Empty", false, 0),
        (
            "forward-guard",
            " when packet=Full(left)",
            " when chosen=Full(right)",
            "packet",
            "chosen",
            false,
            0,
        ),
        (
            "reverse-read",
            "",
            "",
            "packet=Full(left)",
            "chosen=Full(right)",
            false,
            1,
        ),
        (
            "late-row",
            " when take and left.free=3 and packet=Full(left)",
            "",
            "1",
            "0",
            false,
            1,
        ),
        (
            "target-guard",
            " when packet=Full(left)",
            " when keep",
            "packet",
            "chosen",
            false,
            1,
        ),
        (
            "missing-source",
            " when left.free>0",
            "",
            "packet",
            "chosen",
            true,
            2,
        ),
        (
            "missing-target",
            "",
            " when right.free>0",
            "packet",
            "chosen",
            true,
            2,
        ),
        (
            "false-source",
            " when false",
            " when right.free>0",
            "packet",
            "chosen",
            true,
            0,
        ),
    ] {
        let (dir, _) = finite_local_parameter_inputs(&format!("local-data-ref-{case}"));
        let old = std::fs::read_to_string(dir.join("d.json")).unwrap();
        let definition = old.replace(
            r#""arguments":["Bool"]"#,
            r#""arguments":[["Ref","Reservations.State"]]"#,
        );
        let before = archsig::definition::check_definitions(&[("d", old.as_bytes())]).unwrap();
        let after =
            archsig::definition::check_definitions(&[("d", definition.as_bytes())]).unwrap();
        let digest = &after.vocabularies["Reservations"].digest;
        let mut map = std::fs::read_to_string(dir.join("a.json"))
            .unwrap()
            .replace(&before.vocabularies["Reservations"].digest, digest);
        if case == "late-row" {
            map = map.replace(
                r#""id":"s-free","subject":"s","field":"Reservations.State.free","value":"1""#,
                r#""id":"s-free","subject":"s","field":"Reservations.State.free","value":"3""#,
            );
        }
        if missing {
            map = map
                .lines()
                .filter(|line| {
                    !line.contains(r#""id":"p-free""#) && !line.contains(r#""id":"r-free""#)
                })
                .collect::<Vec<_>>()
                .join("\n");
        }
        std::fs::write(dir.join("d.json"), definition).unwrap();
        std::fs::write(dir.join("a.json"), map).unwrap();
        let ty = if case == "projection" {
            "Option<(Choice,Bool)>"
        } else {
            "Choice"
        };
        let source_prefix = if case == "projection" {
            ""
        } else {
            "left:State,"
        };
        let target_prefix = if case == "projection" {
            ""
        } else {
            "right:State,"
        };
        std::fs::write(dir.join("l.law"), format!(r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{use vocabulary Reservations version "1" digest "{digest}"; local here({source_prefix}packet:{ty},take:Bool){sg} reads {sr};}}
reading After {{use vocabulary Reservations version "1" digest "{digest}"; local here({target_prefix}chosen:{ty},keep:Bool){tg} reads {tr};}}"#)).unwrap();
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
            match code {
                0 => "established",
                1 => "refuted",
                _ => "undetermined",
            }
        );
        assert!(has(get(m, "outputs"), "operation"));
        assert_eq!(has(get(m, "outputs"), "map"), code == 0);
        assert_eq!(s(get(answer(&result, "same"), "status")), "established");
        let plan = value(&result, get(get(answer(&result, "n"), "outputs"), "plan"));
        assert_eq!(arr(get(plan, "requirements")).is_empty(), code != 2);
        if code == 2 {
            assert!(!has(m, "counterexamples"));
        }
        if case == "reverse-read" || case == "late-row" {
            let data = get(value(&result, &arr(get(m, "counterexamples"))[0]), "data");
            let bindings = arr(get(data, "bindings"));
            assert_eq!(bindings.len(), 3);
            for (binding, name) in bindings.iter().zip(["left", "packet", "take"]) {
                assert_eq!(s(get(binding, "name")), name);
            }
            let late = case == "late-row";
            assert_json(
                value(&result, get(&bindings[0], "value")),
                if late { r#"["v","s"]"# } else { r#"["v","p"]"# },
            );
            assert_json(
                value(&result, get(&bindings[1], "value")),
                if late {
                    r#"{"args":[["v","s"]],"tag":"Full"}"#
                } else {
                    r#"{"args":[["v","r"]],"tag":"Full"}"#
                },
            );
            assert_json(
                value(&result, get(&bindings[2], "value")),
                if late { "true" } else { "false" },
            );
            assert_json(
                value(&result, get(data, "left")),
                if late { r#""1""# } else { "false" },
            );
            assert_json(
                value(&result, get(data, "right")),
                if late { r#""0""# } else { "true" },
            );
        }
        if case == "projection" {
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
                    &[("p", "r"), ("q", "s"), ("r", "r"), ("s", "s")],
                );
                for name in [
                    "Reservations.Choice",
                    "Reservations.Choice.Empty",
                    "Reservations.Choice.Full",
                ] {
                    assert!(
                        arr(get(map, "declarations")).iter().any(|pair| {
                            let pair = arr(pair);
                            s(&pair[0]) == name && s(&pair[1]) == name
                        }),
                        "{name}"
                    );
                }
            }
        }
        if matches!(case, "projection" | "reverse-read" | "missing-target" | "expression") {
            let mut args = vec![
                "run",
                "--atom-definition",
                "d.json",
                "--law",
                "l.law",
                "--archmap",
                "a.json",
            ];
            for request in &requests {
                args.extend(["--ask", request]);
            }
            let normal = without_file_changes(&dir, || cli::run(&dir, &args));
            assert_eq!(normal.code, code, "{case}: {}", normal.stdout);
            assert!(normal.stderr.is_empty());
            assert_map_summary(&normal, &result);
            args.extend(["--out", "again", "--reuse", "out"]);
            let reused = cli::run(&dir, &args);
            assert_eq!(reused.code, code, "{case}: {}", reused.stdout);
            let again = result_json(&dir, &reused);
            assert!(warnings(&again).is_empty());
            for key in ["answers", "nodes"] {
                assert_eq!(
                    get(&result, key).value,
                    get(&again, key).value,
                    "{case}: {key}"
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
    let digest = &after.vocabularies["Reservations"].digest;
    let map = std::fs::read_to_string(dir.join("a.json"))
        .unwrap()
        .replace(&before.vocabularies["Reservations"].digest, digest)
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
    for (case, sg, tg, sr, tr, missing, code) in [
        ("projection", "", "", "table", "chosen", false, 0),
        ("infinite-product", "", "", "(table,left.free)", "(chosen,right.free)", false, 0),
        ("infinite-recursive", "", "", "Choice.Full(table,left.free,Choice.Empty)", "Choice.Full(chosen,right.free,Choice.Empty)", false, 0),
        ("infinite-refuted", "", "", "(table,left.free)", "(chosen,right.free+1)", false, 1),
        ("infinite-missing", "", "", "(table,left.free)", "(chosen,right.free)", true, 2),
        ("infinite-false-source", " when false", " when right.free>0", "(table,left.free)", "(chosen,right.free)", true, 0),
        ("infinite-forward", " when take", "", "(table,left.free)", "(chosen,right.free)", false, 0),
        ("infinite-nested", "", "", "list<Option<(Map<Key,State>,Z)>>[some((table,left.free))]", "list<Option<(Map<Key,State>,Z)>>[some((chosen,right.free))]", false, 0),
        ("expression", "", "", "if take then table else other", "if keep then chosen else spare", false, 0),
        (
            "forward-guard",
            " when table(key)=left",
            " when chosen(which)=right",
            "table",
            "chosen",
            false,
            0,
        ),
        (
            "reverse-read",
            "",
            "",
            "table(key)=left",
            "chosen(which)=right",
            false,
            1,
        ),
        (
            "target-guard",
            " when table(key)=left",
            " when keep",
            "table",
            "chosen",
            false,
            1,
        ),
        (
            "missing-source",
            " when left.free>0",
            "",
            "table",
            "chosen",
            true,
            2,
        ),
        (
            "missing-target",
            "",
            " when right.free>0",
            "table",
            "chosen",
            true,
            2,
        ),
        (
            "false-source",
            " when false",
            " when right.free>0",
            "table",
            "chosen",
            true,
            0,
        ),
    ] {
        let (dir, mut vocabulary) = finite_local_map_inputs(&format!("local-map-{case}"));
        if case == "infinite-recursive" {
            let old = std::fs::read_to_string(dir.join("d.json")).unwrap();
            let definition = old.replacen(r#""declarations": ["#, r#""declarations": [{"kind":"data","name":"Reservations.Choice","meaning":"Mapを持つ再帰値","constructors":[{"name":"Empty","arguments":[],"meaning":"空"},{"name":"Full","arguments":[["Map",["Ref","Reservations.Key"],["Ref","Reservations.State"]],"Z",["Data","Reservations.Choice"]],"meaning":"再帰payload"}]},"#, 1);
            let prior = archsig::definition::check_definitions(&[("d",old.as_bytes())]).unwrap();
            let checked = archsig::definition::check_definitions(&[("d",definition.as_bytes())]).unwrap();
            let prior = &prior.vocabularies["Reservations"].digest;
            let digest = &checked.vocabularies["Reservations"].digest;
            let map = std::fs::read_to_string(dir.join("a.json")).unwrap().replace(prior,digest);
            std::fs::write(dir.join("d.json"),definition).unwrap();
            std::fs::write(dir.join("a.json"),map).unwrap();
            vocabulary = vocabulary.replace(prior,digest);
        }
        if missing {
            let map = std::fs::read_to_string(dir.join("a.json"))
                .unwrap()
                .lines()
                .filter(|line| {
                    !line.contains(r#""id":"p-free""#) && !line.contains(r#""id":"r-free""#)
                })
                .collect::<Vec<_>>()
                .join("\n");
            std::fs::write(dir.join("a.json"), map).unwrap();
        }
        let ty = if case == "projection" {
            "Option<(Map<Key,State>,Bool)>"
        } else {
            "Map<Key,State>"
        };
        let (source_extra, target_extra) = if case == "expression" {
            (",other:Map<Key,State>", ",spare:Map<Key,State>")
        } else {
            ("", "")
        };
        std::fs::write(dir.join("l.law"),format!(r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{vocabulary} local here(left:State,table:{ty},take:Bool,key:Key{source_extra}){sg} reads {sr};}}
reading After {{{vocabulary} local here(right:State,chosen:{ty},keep:Bool,which:Key{target_extra}){tg} reads {tr};}}"#)).unwrap();
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
            match code {
                0 => "established",
                1 => "refuted",
                _ => "undetermined",
            }
        );
        assert!(has(get(m, "outputs"), "operation"));
        assert_eq!(has(get(m, "outputs"), "map"), code == 0);
        assert_eq!(s(get(answer(&result, "same"), "status")), "established");
        let plan = value(&result, get(get(answer(&result, "n"), "outputs"), "plan"));
        assert_eq!(arr(get(plan, "requirements")).is_empty(), code != 2);
        if code == 2 {
            assert!(!has(m, "counterexamples"));
        }
        if case == "reverse-read" {
            let data = get(value(&result, &arr(get(m, "counterexamples"))[0]), "data");
            let bindings = arr(get(data, "bindings"));
            for (binding, name) in bindings.iter().zip(["left", "table", "take", "key"]) {
                assert_eq!(s(get(binding, "name")), name);
            }
            assert_eq!(bindings.len(), 4);
            assert_json(value(&result, get(&bindings[0], "value")), r#"["v","p"]"#);
            assert_json(
                value(&result, get(&bindings[1], "value")),
                r#"[[["v","k"],["v","r"]]]"#,
            );
            assert_json(value(&result, get(&bindings[2], "value")), "false");
            assert_json(value(&result, get(&bindings[3], "value")), r#"["v","k"]"#);
            assert_json(value(&result, get(data, "left")), "false");
            assert_json(value(&result, get(data, "right")), "true");
        }
        if case == "infinite-refuted" {
            let data = get(value(&result, &arr(get(m, "counterexamples"))[0]), "data");
            let bindings = arr(get(data, "bindings"));
            assert_eq!(bindings.len(), 4);
            assert_eq!(s(get(&bindings[0], "name")), "left");
            assert_json(value(&result, get(&bindings[0], "value")), r#"["v","p"]"#);
            assert_json(value(&result, get(data, "left")), r#"[[[["v","k"],["v","p"]]],"2"]"#);
            assert_json(value(&result, get(data, "right")), r#"[[[["v","k"],["v","r"]]],"3"]"#);
        }
        if case == "projection" || case == "infinite-product" {
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
        if case.starts_with("infinite") || matches!(case, "projection" | "reverse-read" | "missing-target" | "expression") {
            let mut args = vec![
                "run",
                "--atom-definition",
                "d.json",
                "--law",
                "l.law",
                "--archmap",
                "a.json",
            ];
            for request in &requests {
                args.extend(["--ask", request]);
            }
            let normal = without_file_changes(&dir, || cli::run(&dir, &args));
            assert_eq!(normal.code, code, "{case}: {}", normal.stdout);
            assert!(normal.stderr.is_empty());
            assert_map_summary(&normal, &result);
            args.extend(["--out", "again", "--reuse", "out"]);
            let reused = cli::run(&dir, &args);
            assert_eq!(reused.code, code, "{case}: {}", reused.stdout);
            let again = result_json(&dir, &reused);
            assert!(warnings(&again).is_empty());
            for key in ["answers", "nodes"] {
                assert_eq!(
                    get(&result, key).value,
                    get(&again, key).value,
                    "{case}: {key}"
                );
            }
        }
    }
}

#[test]
fn local_map_domain_failure_precedes_reads_guards_and_missing() {
    for (case, guard) in [
        ("constant", ""),
        ("expression", ""),
        ("false-source", " when false"),
        ("missing-source", " when left.free>0"),
    ] {
        let (dir, vocabulary) = finite_local_map_inputs(&format!("local-map-outside-{case}"));
        let map = std::fs::read_to_string(dir.join("a.json"))
            .unwrap()
            .lines()
            .filter(|line| !line.contains(r#""id":"p-free""#) && !line.contains(r#""id":"r-free""#))
            .collect::<Vec<_>>()
            .join("\n");
        std::fs::write(dir.join("a.json"), map).unwrap();
        let (source_read, target_read) = if case == "expression" {
            ("if left.free>0 then table else table", "if right.free>0 then chosen else chosen")
        } else {
            ("0", "0")
        };
        std::fs::write(
            dir.join("l.law"),
            format!(
                r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{vocabulary} local here(left:State,table:Map<State,State>){guard} reads {source_read};}}
reading After {{{vocabulary} local here(right:State,chosen:Map<State,State>) reads {target_read};}}"#
            ),
        )
        .unwrap();
        let requests = [
            "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
            "same=compare($m.operation,to=$m.operation,kind=action)",
            "n=needed($m)",
        ];
        let run = asks(&dir, &requests);
        assert_eq!(run.code, 1, "{case}: {}", run.stdout);
        let result = result_json(&dir, &run);
        let m = answer(&result, "m");
        assert_eq!(s(get(m, "status")), "refuted");
        assert!(has(get(m, "outputs"), "operation"));
        assert!(!has(get(m, "outputs"), "map"));
        assert!(!has(m, "counterexamples")); // readは比較していない。
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
        assert_eq!(s(get(answer(&result, "same"), "status")), "established");
        let plan = value(&result, get(get(answer(&result, "n"), "outputs"), "plan"));
        assert!(arr(get(plan, "requirements")).is_empty());
        let source = r#"[[["v","p"],["v","p"]],[["v","q"],["v","p"]],[["v","r"],["v","p"]],[["v","s"],["v","p"]]]"#;
        let expected = archsig::json::parse(source.as_bytes()).unwrap();
        let witness = arr(get(&result, "nodes"))
            .iter()
            .find(|n| get(n, "value").value == expected.value)
            .unwrap();
        let condition = value(&result, get(get(m, "outputs"), "proposition"));
        assert!(
            arr(get(condition, "operands"))
                .iter()
                .any(|reference| s(get(reference, "node")) == s(get(witness, "id")))
        );
        let mut args = vec![
            "run",
            "--atom-definition",
            "d.json",
            "--law",
            "l.law",
            "--archmap",
            "a.json",
        ];
        for request in &requests {
            args.extend(["--ask", request]);
        }
        let normal = without_file_changes(&dir, || cli::run(&dir, &args));
        assert_eq!(normal.code, 1, "{}", normal.stdout);
        assert!(normal.stderr.is_empty());
        args.extend(["--out", "again", "--reuse", "out"]);
        let reused = cli::run(&dir, &args);
        assert_eq!(reused.code, 1, "{}", reused.stdout);
        let again = result_json(&dir, &reused);
        assert!(warnings(&again).is_empty());
        for key in ["answers", "nodes"] {
            assert_eq!(
                get(&result, key).value,
                get(&again, key).value,
                "{case}: {key}"
            );
        }
    }
}

#[test]
fn local_optional_expression_reads_distinguish_absence_missing_and_selected_branches() {
    for case in [
        "preserved",
        "none-false",
        "false-true",
        "source-missing",
        "target-missing",
        "unused-missing",
        "selected-missing",
        "guard-selected-missing",
        "equal-branches",
        "forward-guard",
        "target-guard",
        "false-source",
    ] {
        let (dir, vocabulary) =
            finite_local_parameter_inputs(&format!("local-optional-expression-{case}"));
        let source = "if take then choice else none<Bool>";
        let target = "if keep then chosen else none<Bool>";
        let (sr, tr, sg, tg, code) = match case {
            "none-false" => (
                source,
                "if keep then some(false) else none<Bool>",
                "",
                "",
                1,
            ),
            "false-true" => (
                source,
                "if keep then some(true) else none<Bool>",
                " when choice=some(false) and take",
                " when chosen=some(false) and keep",
                1,
            ),
            "source-missing" => (
                "if take then choice else some(s.free>0)",
                target,
                " when take or s.held=0",
                " when keep or t.held=0",
                2,
            ),
            "target-missing" => (
                source,
                "if keep then chosen else some(t.free>0)",
                " when take or s.held=0",
                " when keep or t.held=0",
                2,
            ),
            "unused-missing" => (
                "if true then choice else some(s.free>0)",
                "if true then chosen else some(t.free>0)",
                "",
                "",
                0,
            ),
            "selected-missing" => (
                "if true then some(s.free>0) else some(s.held>0)",
                "if true then some(t.free>0) else some(t.held>0)",
                "",
                "",
                2,
            ),
            "guard-selected-missing" => (source, target,
                " when if true then s.free>0 else s.held>0",
                " when if true then t.free>0 else t.held>0", 2),
            "equal-branches" => (
                "if s.free>0 then choice else choice",
                "if t.free>0 then chosen else chosen",
                "",
                "",
                0,
            ),
            "forward-guard" => (
                source,
                "if keep then chosen else some(false)",
                " when take",
                "",
                0,
            ),
            "target-guard" => (source, target, " when take", " when not keep", 1),
            "false-source" => (
                "if true then some(s.free>0) else none<Bool>",
                "if true then some(t.free>0) else none<Bool>",
                " when false",
                " when t.free>0",
                0,
            ),
            _ => (source, target, "", "", 0),
        };
        if case.contains("missing") || case == "equal-branches" || case == "false-source" {
            let map = std::fs::read_to_string(dir.join("a.json"))
                .unwrap()
                .lines()
                .filter(|line| {
                    !line.contains(r#""id":"p-free""#)
                        && !line.contains(r#""id":"r-free""#)
                        && (!case.contains("selected-missing")
                            || (!line.contains(r#""id":"p-held""#)
                                && !line.contains(r#""id":"r-held""#)))
                })
                .collect::<Vec<_>>()
                .join("\n");
            std::fs::write(dir.join("a.json"), map).unwrap();
        }
        std::fs::write(
            dir.join("l.law"),
            format!(
                r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{vocabulary} local here(choice:Option<Bool>,take:Bool,s:State){sg} reads {sr};}}
reading After {{{vocabulary} local here(chosen:Option<Bool>,keep:Bool,t:State){tg} reads {tr};}}"#
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
            match code {
                0 => "established",
                1 => "refuted",
                _ => "undetermined",
            }
        );
        assert!(has(get(m, "outputs"), "operation"));
        assert_eq!(has(get(m, "outputs"), "map"), code == 0);
        assert_eq!(s(get(answer(&result, "same"), "status")), "established");
        let plan = value(&result, get(get(answer(&result, "n"), "outputs"), "plan"));
        let requirements = arr(get(plan, "requirements"));
        assert_eq!(requirements.is_empty(), code != 2);
        if code == 2 {
            assert!(!has(m, "counterexamples"));
            assert!(
                requirements
                    .iter()
                    .all(|r| s(get(get(r, "field"), "field")) == "Reservations.State.free")
            );
            if case == "target-missing" {
                assert!(
                    requirements
                        .iter()
                        .all(|r| s(get(get(r, "field"), "subject")) == "r")
                );
            }
        }
        if matches!(case, "source-missing" | "selected-missing" | "guard-selected-missing") {
            for subject in ["p", "r"] {
                assert!(
                    requirements
                        .iter()
                        .any(|r| s(get(get(r, "field"), "subject")) == subject)
                );
            }
        }
        if case == "target-guard" {
            let data = get(value(&result, &arr(get(m, "counterexamples"))[0]), "data");
            assert_json(value(&result, get(data, "left")), "true");
            assert_json(value(&result, get(data, "right")), "false");
        }
        if matches!(case, "none-false" | "false-true") {
            let data = get(value(&result, &arr(get(m, "counterexamples"))[0]), "data");
            let bindings = arr(get(data, "bindings"));
            assert_eq!(bindings.len(), 3);
            for (binding, name) in bindings.iter().zip(["choice", "take", "s"]) {
                assert_eq!(s(get(binding, "name")), name);
            }
            let input = if case == "none-false" {
                r#"{"none":true}"#
            } else {
                r#"{"some":false}"#
            };
            assert_json(value(&result, get(&bindings[0], "value")), input);
            assert_json(value(&result, get(&bindings[1], "value")), "true");
            assert_json(value(&result, get(&bindings[2], "value")), r#"["v","p"]"#);
            assert_json(value(&result, get(data, "left")), input);
            assert_json(
                value(&result, get(data, "right")),
                if case == "none-false" {
                    r#"{"some":false}"#
                } else {
                    r#"{"some":true}"#
                },
            );
        }
        if matches!(case, "preserved" | "none-false" | "selected-missing") {
            let mut args = vec![
                "run",
                "--atom-definition",
                "d.json",
                "--law",
                "l.law",
                "--archmap",
                "a.json",
            ];
            for request in &requests {
                args.extend(["--ask", request]);
            }
            let normal = without_file_changes(&dir, || cli::run(&dir, &args));
            assert_eq!(normal.code, code, "{case}: {}", normal.stdout);
            assert!(normal.stderr.is_empty());
            assert_map_summary(&normal, &result);
            args.extend(["--out", "again", "--reuse", "out"]);
            let reused = cli::run(&dir, &args);
            assert_eq!(reused.code, code, "{case}: {}", reused.stdout);
            let again = result_json(&dir, &reused);
            assert!(warnings(&again).is_empty());
            for key in ["answers", "nodes"] {
                assert_eq!(
                    get(&result, key).value,
                    get(&again, key).value,
                    "{case}: {key}"
                );
            }
        }
    }
}

#[test]
fn local_finite_expression_reads_share_identity_value_maps_for_composite_types() {
    for (name, source, target, wire) in [
        (
            "tuple",
            "if take then (choice,false) else (none<Bool>,true)",
            "if keep then (chosen,false) else (none<Bool>,true)",
            r#"["Tuple",["Option","Bool"],"Bool"]"#,
        ),
        (
            "set",
            "if take then set<Bool>{false,true} else set<Bool>{}",
            "if keep then set<Bool>{true,false} else set<Bool>{}",
            r#"["Set","Bool"]"#,
        ),
        (
            "data",
            "if take then Choice.Full(false) else Choice.Empty",
            "if keep then Choice.Full(false) else Choice.Empty",
            r#"["Data","Reservations.Choice"]"#,
        ),
    ] {
        let (dir, vocabulary) =
            finite_local_parameter_inputs(&format!("local-finite-expression-{name}"));
        std::fs::write(
            dir.join("l.law"),
            format!(
                r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{vocabulary} local here(choice:Option<Bool>,take:Bool) reads {source};}}
reading After {{{vocabulary} local here(chosen:Option<Bool>,keep:Bool) reads {target};}}"#
            ),
        )
        .unwrap();
        let run = asks(
            &dir,
            &[
                "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
            ],
        );
        assert_eq!(run.code, 0, "{name}: {}", run.stdout);
        let result = result_json(&dir, &run);
        let map = value(&result, get(get(answer(&result, "m"), "outputs"), "map"));
        let transport = value(&result, &arr(get(map, "transports"))[0]);
        let clause = &arr(get(transport, "clauses"))[0];
        let values = value(&result, get(clause, "values"));
        assert_json(get(values, "source_type"), wire);
        assert_json(get(values, "target_type"), wire);
        assert!(arr(get(values, "subjects")).is_empty());
        if name == "data" {
            for name in [
                "Reservations.Choice",
                "Reservations.Choice.Empty",
                "Reservations.Choice.Full",
            ] {
                assert!(arr(get(values, "declarations")).iter().any(|pair| {
                    let pair = arr(pair);
                    s(&pair[0]) == name && s(&pair[1]) == name
                }));
            }
        }
    }
}

#[test]
fn local_read_type_maps_do_not_require_a_matching_parameter() {
    for (shape, body, empty) in [
        ("option", "some(left)", "none<State>"),
        ("tuple", "(left,true)", "(left,false)"),
        ("set", "set<State>{left}", "set<State>{}"),
        ("data", "Choice.Full(left)", "Choice.Empty"),
    ] {
        for (case, sg, tg, read_missing, different, code) in [
            ("branch", "", "", false, false, 0),
            ("active", " when take", " when keep", false, false, 0),
            (
                "target-guard",
                " when take",
                " when not keep",
                false,
                false,
                1,
            ),
            ("refuted", "", "", false, true, 1),
            ("missing", "", "", true, false, 2),
            ("false-source", " when false", " when false", true, false, 0),
        ] {
            let (dir, _) = finite_local_parameter_inputs(&format!("read-type-{shape}-{case}"));
            let old = std::fs::read_to_string(dir.join("d.json")).unwrap();
            let definition = old.replace(
                r#""arguments":["Bool"]"#,
                r#""arguments":[["Ref","Reservations.State"]]"#,
            );
            let before = archsig::definition::check_definitions(&[("d", old.as_bytes())]).unwrap();
            let after =
                archsig::definition::check_definitions(&[("d", definition.as_bytes())]).unwrap();
            let digest = &after.vocabularies["Reservations"].digest;
            let mut map = std::fs::read_to_string(dir.join("a.json"))
                .unwrap()
                .replace(&before.vocabularies["Reservations"].digest, digest);
            if read_missing {
                map = map
                    .lines()
                    .filter(|line| {
                        !line.contains(r#""id":"p-free""#) && !line.contains(r#""id":"r-free""#)
                    })
                    .collect::<Vec<_>>()
                    .join("\n");
            }
            std::fs::write(dir.join("d.json"), definition).unwrap();
            std::fs::write(dir.join("a.json"), map).unwrap();
            let condition = if read_missing { "left.free>0" } else { "take" };
            let source_read = format!("if {condition} then {body} else {empty}");
            let target_read = if different {
                empty.to_string()
            } else {
                source_read.clone()
            }
            .replace("left", "right")
            .replace("take", "keep");
            std::fs::write(dir.join("l.law"),format!(r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{use vocabulary Reservations version "1" digest "{digest}"; local here(left:State,take:Bool){sg} reads {source_read};}}
reading After {{use vocabulary Reservations version "1" digest "{digest}"; local here(right:State,keep:Bool){tg} reads {target_read};}}"#)).unwrap();
            let requests = [
                "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
                "same=compare($m.operation,to=$m.operation,kind=action)",
                "n=needed($m)",
            ];
            let run = asks(&dir, &requests);
            assert_eq!(run.code, code, "{shape}/{case}: {}", run.stdout);
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
                let ty = match shape {
                    "option" => r#"["Option",["Ref","Reservations.State"]]"#,
                    "tuple" => r#"["Tuple",["Ref","Reservations.State"],"Bool"]"#,
                    "set" => r#"["Set",["Ref","Reservations.State"]]"#,
                    _ => r#"["Data","Reservations.Choice"]"#,
                };
                assert_json(get(values, "source_type"), ty);
                assert_json(get(values, "target_type"), ty);
            } else if code == 1 {
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
            } else {
                assert!(!has(m, "counterexamples"));
                assert!(
                    arr(get(m, "reasons"))
                        .iter()
                        .any(|r| s(get(r, "code")) == "missing_observation")
                );
            }
            if matches!(case, "branch" | "refuted" | "missing") {
                let mut args = vec![
                    "run",
                    "--atom-definition",
                    "d.json",
                    "--archmap",
                    "a.json",
                    "--law",
                    "l.law",
                ];
                for request in &requests {
                    args.extend(["--ask", request]);
                }
                let normal = without_file_changes(&dir, || cli::run(&dir, &args));
                assert_eq!(normal.code, code, "{}", normal.stdout);
                assert!(normal.stderr.is_empty());
                assert_map_summary(&normal, &result);
                args.extend(["--out", "again", "--reuse", "out"]);
                let reused = cli::run(&dir, &args);
                assert_eq!(reused.code, code, "{}", reused.stdout);
                let again = result_json(&dir, &reused);
                assert!(warnings(&again).is_empty());
                for key in ["answers", "nodes"] {
                    assert_eq!(get(&result, key).value, get(&again, key).value);
                }
            }
        }
    }
}

#[test]
fn local_read_type_maps_check_the_whole_map_domain_before_reading_none() {
    for (case, domain, guard, code) in [
        ("coherent", "Key", "", 0),
        ("collision", "State", "", 1),
        ("inactive-collision", "State", " when false", 1),
    ] {
        let (dir, vocabulary) = finite_local_map_inputs(&format!("read-type-map-{case}"));
        let map = std::fs::read_to_string(dir.join("a.json"))
            .unwrap()
            .lines()
            .filter(|line| !line.contains(r#""id":"p-free""#) && !line.contains(r#""id":"r-free""#))
            .collect::<Vec<_>>()
            .join("\n");
        std::fs::write(dir.join("a.json"), map).unwrap();
        let source =
            format!("if left.free>0 then none<Map<{domain},State>> else none<Map<{domain},State>>");
        let target = source.replace("left", "right");
        std::fs::write(
            dir.join("l.law"),
            format!(
                r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{vocabulary} local here(left:State){guard} reads {source};}}
reading After {{{vocabulary} local here(right:State) reads {target};}}"#
            ),
        )
        .unwrap();
        // Equal none branches remain known; the other cases fail on the whole output type before evaluation.
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
        assert_eq!(has(get(m, "outputs"), "map"), code == 0);
        assert!(!has(m, "counterexamples"));
        let reasons = arr(get(m, "reasons"));
        if code == 0 {
            assert!(reasons.is_empty());
        } else {
            assert!(
                reasons
                    .iter()
                    .any(|r| s(get(r, "code")) == "condition_failed")
            );
        }
        if code != 0 {
            assert!(!reasons.iter().any(|r| matches!(
                s(get(r, "code")),
                "missing_observation" | "unsupported_algorithm"
            )));
        }
        if code == 0 {
            let request = "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)";
            let args = [
                "run",
                "--atom-definition",
                "d.json",
                "--law",
                "l.law",
                "--archmap",
                "a.json",
                "--ask",
                request,
                "--out",
                "again",
                "--reuse",
                "out",
            ];
            let reused = cli::run(&dir, &args);
            assert_eq!(reused.code, 0, "{}", reused.stdout);
            let again = result_json(&dir, &reused);
            assert!(warnings(&again).is_empty());
            for key in ["answers", "nodes"] {
                assert_eq!(get(&result, key).value, get(&again, key).value);
            }
        }
    }
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
    for (case, guard, body) in [
        ("plain", "", "if take then some(left) else none<State>"),
        (
            "inactive",
            " when false",
            "if take then some(left) else none<State>",
        ),
        (
            "missing",
            "",
            "if left.free>0 then some(left) else none<State>",
        ),
    ] {
        let (dir, vocabulary) =
            finite_local_parameter_inputs(&format!("read-type-mismatch-{case}"));
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
reading Before {{{vocabulary} local here(left:State,take:Bool){guard} reads {body};}}
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
        assert_eq!(run.code, 1, "{case}: {}", run.stdout);
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
        let mut args = vec![
            "run",
            "--atom-definition",
            "d.json",
            "--law",
            "l.law",
            "--archmap",
            "a.json",
        ];
        for request in &requests {
            args.extend(["--ask", request]);
        }
        let normal = without_file_changes(&dir, || cli::run(&dir, &args));
        assert_eq!(normal.code, 1, "{}", normal.stdout);
        assert!(normal.stderr.is_empty());
        assert_map_summary(&normal, &result);
        args.extend(["--out", "again", "--reuse", "out"]);
        let reused = cli::run(&dir, &args);
        assert_eq!(reused.code, 1, "{}", reused.stdout);
        let again = result_json(&dir, &reused);
        assert!(warnings(&again).is_empty());
        for key in ["answers", "nodes"] {
            assert_eq!(get(&result, key).value, get(&again, key).value);
        }
    }
}

#[test]
fn local_infinite_compound_reads_use_identity_on_actual_values() {
    for (shape, body, alternate, expected, wire) in [
        (
            "list",
            "list<Z>[s.free,0]",
            "list<Z>[0,s.free]",
            r#"["2","0"]"#,
            r#"["List","Z"]"#,
        ),
        (
            "tuple",
            "(s.free,true)",
            "(s.free,false)",
            r#"["2",true]"#,
            r#"["Tuple","Z","Bool"]"#,
        ),
        (
            "option",
            "if s.free>0 then some(rat(3,2)) else none<Q>",
            "none<Q>",
            r#"{"some":["3","2"]}"#,
            r#"["Option","Q"]"#,
        ),
        (
            "set",
            "set<Z>{s.free,0}",
            "set<Z>{0,s.free,1}",
            r#"["2","0"]"#,
            r#"["Set","Z"]"#,
        ),
        (
            "data",
            "Choice.Full(s.free)",
            "Choice.Empty",
            r#"{"args":["2"],"tag":"Full"}"#,
            r#"["Data","Reservations.Choice"]"#,
        ),
        (
            "text",
            r#"if s.free>0 then "yes" else "no""#,
            r#""changed""#,
            r#""yes""#,
            r#""Text""#,
        ),
    ] {
        for (case, code) in [
            ("preserved", 0),
            ("refuted", 1),
            ("missing", 2),
            ("unused-missing", 0),
            ("false-source", 0),
            ("target-guard", 1),
        ] {
            let (dir, mut vocabulary) =
                finite_local_parameter_inputs(&format!("local-infinite-{shape}-{case}"));
            if shape == "data" {
                let old = std::fs::read_to_string(dir.join("d.json")).unwrap();
                let definition = old.replace(r#""arguments":["Bool"]"#, r#""arguments":["Z"]"#);
                let checked =
                    archsig::definition::check_definitions(&[("d", definition.as_bytes())])
                        .unwrap();
                let before =
                    archsig::definition::check_definitions(&[("d", old.as_bytes())]).unwrap();
                let digest = &checked.vocabularies["Reservations"].digest;
                let prior = &before.vocabularies["Reservations"].digest;
                let map = std::fs::read_to_string(dir.join("a.json"))
                    .unwrap()
                    .replace(prior, digest);
                std::fs::write(dir.join("d.json"), definition).unwrap();
                std::fs::write(dir.join("a.json"), map).unwrap();
                vocabulary = vocabulary.replace(prior, digest);
            }
            if case.contains("missing") || case == "false-source" {
                let map = std::fs::read_to_string(dir.join("a.json"))
                    .unwrap()
                    .lines()
                    .filter(|line| {
                        !line.contains(r#""id":"p-free""#) && !line.contains(r#""id":"r-free""#)
                    })
                    .collect::<Vec<_>>()
                    .join("\n");
                std::fs::write(dir.join("a.json"), map).unwrap();
            }
            let read = if case == "unused-missing" {
                format!(
                    "if false then {body} else {}",
                    alternate.replace("s.free", "0")
                )
            } else {
                format!("if take then {body} else {alternate}")
            };
            let target = if case == "refuted" {
                alternate.to_owned()
            } else {
                read.clone()
            }
            .replace("s.", "t.")
            .replace("take", "keep")
            .replace("set<Z>{t.free,0}", "set<Z>{0,t.free}");
            let (sg, tg) = match case {
                "false-source" => (" when false", " when t.free>0"),
                "target-guard" => (" when take", " when not keep"),
                _ => ("", ""),
            };
            std::fs::write(
                dir.join("l.law"),
                format!(
                    r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{vocabulary} local here(s:State,take:Bool){sg} reads {read};}}
reading After {{{vocabulary} local here(t:State,keep:Bool){tg} reads {target};}}"#
                ),
            )
            .unwrap();
            let requests = [
                "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
                "same=compare($m.operation,to=$m.operation,kind=action)",
                "n=needed($m)",
            ];
            let run = asks(&dir, &requests);
            assert_eq!(run.code, code, "{shape}/{case}: {}", run.stdout);
            assert!(run.stderr.is_empty());
            let result = result_json(&dir, &run);
            let m = answer(&result, "m");
            assert_eq!(
                s(get(m, "status")),
                match code {
                    0 => "established",
                    1 => "refuted",
                    _ => "undetermined",
                }
            );
            assert!(has(get(m, "outputs"), "operation"));
            assert_eq!(has(get(m, "outputs"), "map"), code == 0);
            assert_eq!(s(get(answer(&result, "same"), "status")), "established");
            let plan = value(&result, get(get(answer(&result, "n"), "outputs"), "plan"));
            assert_eq!(arr(get(plan, "requirements")).is_empty(), code != 2);
            if code == 2 {
                assert!(!has(m, "counterexamples"));
            }
            if case == "refuted" {
                let data = get(value(&result, &arr(get(m, "counterexamples"))[0]), "data");
                let bindings = arr(get(data, "bindings"));
                assert_eq!(s(get(&bindings[0], "name")), "s");
                assert_json(value(&result, get(&bindings[0], "value")), r#"["v","p"]"#);
                assert_json(value(&result, get(&bindings[1], "value")), "true");
                assert_json(value(&result, get(data, "left")), expected);
            }
            if case == "preserved" {
                let map = value(&result, get(get(m, "outputs"), "map"));
                let transport = value(&result, &arr(get(map, "transports"))[0]);
                let values = value(&result, get(&arr(get(transport, "clauses"))[0], "values"));
                assert_json(get(values, "source_type"), wire);
                assert_json(get(values, "target_type"), wire);
                assert!(arr(get(values, "subjects")).is_empty());
                let mut args = vec![
                    "run",
                    "--atom-definition",
                    "d.json",
                    "--law",
                    "l.law",
                    "--archmap",
                    "a.json",
                ];
                for request in &requests {
                    args.extend(["--ask", request]);
                }
                let normal = without_file_changes(&dir, || cli::run(&dir, &args));
                assert_eq!(normal.code, 0, "{}", normal.stdout);
                assert_map_summary(&normal, &result);
                args.extend(["--out", "again", "--reuse", "out"]);
                let reused = cli::run(&dir, &args);
                assert_eq!(reused.code, 0, "{}", reused.stdout);
                let again = result_json(&dir, &reused);
                assert!(warnings(&again).is_empty());
                for key in ["answers", "nodes"] {
                    assert_eq!(get(&result, key).value, get(&again, key).value);
                }
            }
        }
    }
}

#[test]
fn local_reference_product_reads_extend_total_reference_maps_with_scalar_identity() {
    for (shape, parameter, body, alternate, different, wire, witness, other) in [
        (
            "tuple",
            "State",
            "(left,left.free)",
            "(other,other.free)",
            "(left,left.free+1)",
            r#"["Tuple",["Ref","Reservations.State"],"Z"]"#,
            r#"[["v","p"],"2"]"#,
            "q",
        ),
        (
            "option",
            "State",
            "some((left,if left.free>0 then rat(3,2) else rat(0,1)))",
            "none<(State,Q)>",
            "some((left,rat(5,2)))",
            r#"["Option",["Tuple",["Ref","Reservations.State"],"Q"]]"#,
            r#"{"some":[["v","p"],["3","2"]]}"#,
            "p",
        ),
        (
            "return-only",
            "Reserve",
            "(left.from,left.from.free)",
            "(other.to,other.to.free)",
            "(left.from,left.from.free+1)",
            r#"["Tuple",["Ref","Reservations.State"],"Z"]"#,
            r#"[["v","p"],"2"]"#,
            "e",
        ),
        (
            "list",
            "State",
            "list<(State,Z)>[(left,left.free),(other,other.free),(left,left.free)]",
            "list<(State,Z)>[]",
            "list<(State,Z)>[(left,left.free+1)]",
            r#"["List",["Tuple",["Ref","Reservations.State"],"Z"]]"#,
            r#"[[["v","p"],"2"],[["v","p"],"2"],[["v","p"],"2"]]"#,
            "p",
        ),
        (
            "set",
            "State",
            "set<(State,Z)>{(left,left.free),(other,other.free)}",
            "set<(State,Z)>{}",
            "set<(State,Z)>{(left,left.free+1),(other,other.free)}",
            r#"["Set",["Tuple",["Ref","Reservations.State"],"Z"]]"#,
            r#"[[["v","p"],"2"]]"#,
            "p",
        ),
        (
            "data",
            "State",
            "Choice.Full(left,left.free)",
            "Choice.Empty",
            "Choice.Full(left,left.free+1)",
            r#"["Data","Reservations.Choice"]"#,
            r#"{"args":[["v","p"],"2"],"tag":"Full"}"#,
            "p",
        ),
        (
            "recursive-data",
            "Reserve",
            "Choice.Full(left.from,left.from.free,Choice.Full(other.to,0,Choice.Empty))",
            "Choice.Empty",
            "Choice.Full(left.from,left.from.free+1,Choice.Empty)",
            r#"["Data","Reservations.Choice"]"#,
            r#"{"args":[["v","p"],"2",{"args":[["v","q"],"0",{"args":[],"tag":"Empty"}],"tag":"Full"}],"tag":"Full"}"#,
            "e",
        ),
    ] {
        for (case, code) in [
            ("preserved", 0),
            ("refuted", 1),
            ("numeric-refuted", 1),
            ("missing", 2),
            ("unused-missing", 0),
            ("false-source", 0),
            ("forward", 0),
            ("target-guard", 1),
        ] {
            let (dir, mut vocabulary) =
                finite_local_parameter_inputs(&format!("local-reference-product-{shape}-{case}"));
            if shape.ends_with("data") {
                let old = std::fs::read_to_string(dir.join("d.json")).unwrap();
                let arguments = if shape == "data" {
                    r#""arguments":[["Ref","Reservations.State"],"Z"]"#
                } else {
                    r#""arguments":[["Ref","Reservations.State"],"Z",["Data","Reservations.Choice"]]"#
                };
                let definition = old.replace(r#""arguments":["Bool"]"#, arguments);
                let prior = archsig::definition::check_definitions(&[("d", old.as_bytes())]).unwrap();
                let checked = archsig::definition::check_definitions(&[("d", definition.as_bytes())]).unwrap();
                let digest = &checked.vocabularies["Reservations"].digest;
                let prior = &prior.vocabularies["Reservations"].digest;
                let map = std::fs::read_to_string(dir.join("a.json")).unwrap().replace(prior, digest);
                std::fs::write(dir.join("d.json"), definition).unwrap();
                std::fs::write(dir.join("a.json"), map).unwrap();
                vocabulary = vocabulary.replace(prior, digest);
            }
            if case.contains("missing") || case == "false-source" {
                let map = std::fs::read_to_string(dir.join("a.json"))
                    .unwrap()
                    .lines()
                    .filter(|line| {
                        !line.contains(r#""id":"p-free""#) && !line.contains(r#""id":"r-free""#)
                    })
                    .collect::<Vec<_>>()
                    .join("\n");
                std::fs::write(dir.join("a.json"), map).unwrap();
            }
            let read = if case == "unused-missing" {
                format!(
                    "if false then {body} else {}",
                    alternate
                        .replace("other.to.free", "0")
                        .replace("other.free", "0")
                )
            } else {
                format!("if take then {body} else {alternate}")
            };
            let target = match case {
                "refuted" => alternate.to_owned(),
                "numeric-refuted" => format!("if take then {different} else {alternate}"),
                "forward" => body.to_owned(),
                _ => read.clone(),
            }
            .replace("left", "right")
            .replace("other", "spare")
            .replace("take", "keep");
            let (sg, tg) = match case {
                "false-source" => (" when false", " when right.from.free>0"),
                "forward" => (" when take", ""),
                "target-guard" => (" when take", " when not keep"),
                _ => ("", ""),
            };
            let tg = if parameter == "State" {
                tg.replace("right.from.free", "right.free")
            } else {
                tg.to_owned()
            };
            std::fs::write(dir.join("l.law"),format!(r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{vocabulary} local here(left:{parameter},other:{parameter},take:Bool){sg} reads {read};}}
reading After {{{vocabulary} local here(right:{parameter},spare:{parameter},keep:Bool){tg} reads {target};}}"#)).unwrap();
            let requests = [
                "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
                "same=compare($m.operation,to=$m.operation,kind=action)",
                "n=needed($m)",
            ];
            let run = asks(&dir, &requests);
            assert_eq!(run.code, code, "{shape}/{case}: {}", run.stdout);
            assert!(run.stderr.is_empty());
            let result = result_json(&dir, &run);
            let m = answer(&result, "m");
            assert_eq!(
                s(get(m, "status")),
                match code {
                    0 => "established",
                    1 => "refuted",
                    _ => "undetermined",
                }
            );
            assert!(has(get(m, "outputs"), "operation"));
            assert_eq!(has(get(m, "outputs"), "map"), code == 0);
            assert_eq!(s(get(answer(&result, "same"), "status")), "established");
            let plan = value(&result, get(get(answer(&result, "n"), "outputs"), "plan"));
            let requirements = arr(get(plan, "requirements"));
            assert_eq!(requirements.is_empty(), code != 2);
            if code == 2 {
                assert!(!has(m, "counterexamples"));
                assert!(
                    requirements
                        .iter()
                        .all(|r| s(get(get(r, "field"), "field")) == "Reservations.State.free")
                );
            }
            if case == "refuted" || case == "numeric-refuted" {
                let data = get(value(&result, &arr(get(m, "counterexamples"))[0]), "data");
                let bindings = arr(get(data, "bindings"));
                assert_eq!(bindings.len(), 3);
                assert_eq!(s(get(&bindings[0], "name")), "left");
                let first = if parameter == "State" { "p" } else { "e" };
                assert_json(
                    value(&result, get(&bindings[0], "value")),
                    &format!(r#"["v","{first}"]"#),
                );
                let second = if case == "numeric-refuted" {
                    first
                } else if parameter == "Reserve" {
                    "e"
                } else {
                    other
                };
                assert_json(
                    value(&result, get(&bindings[1], "value")),
                    &format!(r#"["v","{second}"]"#),
                );
                assert_json(value(&result, get(&bindings[2], "value")), "true");
                assert_json(value(&result, get(data, "left")), witness);
            }
            if case == "preserved" {
                let map = value(&result, get(get(m, "outputs"), "map"));
                let transport = value(&result, &arr(get(map, "transports"))[0]);
                let values = value(&result, get(&arr(get(transport, "clauses"))[0], "values"));
                assert_json(get(values, "source_type"), wire);
                assert_json(get(values, "target_type"), wire);
                if shape.ends_with("data") {
                    for name in ["Reservations.Choice", "Reservations.Choice.Empty", "Reservations.Choice.Full"] {
                        let expected = archsig::json::parse(format!(r#"["{name}","{name}"]"#).as_bytes()).unwrap();
                        assert!(arr(get(values, "declarations")).iter().any(|p| p.value == expected.value));
                    }
                }
                assert_reference_pairs(
                    &result,
                    values,
                    &[("p", "r"), ("q", "s"), ("r", "r"), ("s", "s")],
                );
                let mut args = vec![
                    "run",
                    "--atom-definition",
                    "d.json",
                    "--law",
                    "l.law",
                    "--archmap",
                    "a.json",
                ];
                for request in &requests {
                    args.extend(["--ask", request]);
                }
                let normal = without_file_changes(&dir, || cli::run(&dir, &args));
                assert_eq!(normal.code, 0, "{}", normal.stdout);
                assert_map_summary(&normal, &result);
                args.extend(["--out", "again", "--reuse", "out"]);
                let reused = cli::run(&dir, &args);
                assert_eq!(reused.code, 0, "{}", reused.stdout);
                let again = result_json(&dir, &reused);
                assert!(warnings(&again).is_empty());
                for key in ["answers", "nodes"] {
                    assert_eq!(get(&result, key).value, get(&again, key).value);
                }
            }
        }
    }
}

#[test]
fn local_reference_products_check_unread_reference_values_before_false_guards() {
    for (case, external, mismatch, empty) in [
        ("total", false, false, "none<@>"),
        ("outside", true, false, "none<@>"),
        ("mismatch", false, true, "none<@>"),
        ("list-total", false, false, "list<@>[]"),
        ("list-outside", true, false, "list<@>[]"),
        ("list-mismatch", false, true, "list<@>[]"),
        ("set-total", false, false, "set<@>{}"),
        ("set-outside", true, false, "set<@>{}"),
        ("set-mismatch", false, true, "set<@>{}"),
        ("data-payload", false, true, "Bridge.Choice.Empty"),
        ("data-payload-option", false, true, "none<Bridge.Choice>"),
    ] {
        let dir = workdir(&format!("local-reference-product-domain-{case}"));
        let left = include_bytes!("fixtures/configuration-map-left.atoms.json");
        let right = include_bytes!("fixtures/configuration-map-right.atoms.json");
        let checked =
            archsig::definition::check_definitions(&[("left", left), ("right", right)]).unwrap();
        let ld = &checked.vocabularies["Left"].digest;
        let rd = &checked.vocabularies["Right"].digest;
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
        let bd = &checked.vocabularies["Bridge"].digest;
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
            "--time-ms",
            "120000",
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

#[test]
fn local_infinite_map_read_domains_are_checked_before_guards() {
    for (case, shape, guard, missing) in [
        ("none", "none<(Map<State,State>,Z)>", "", false),
        (
            "false-source",
            "none<(Map<State,State>,Z)>",
            " when false",
            false,
        ),
        (
            "missing",
            "none<(Map<State,State>,Z)>",
            " when left.free>0",
            true,
        ),
        (
            "nested",
            "list<Option<(Map<State,State>,Z)>>[]",
            " when false",
            false,
        ),
        ("recursive", "Choice.Empty", " when false", false),
    ] {
        let (dir, mut vocabulary) =
            finite_local_parameter_inputs(&format!("infinite-map-domain-{case}"));
        if case == "recursive" {
            let old = std::fs::read_to_string(dir.join("d.json")).unwrap();
            let definition = old.replace(r#""arguments":["Bool"]"#, r#""arguments":[["Map",["Ref","Reservations.State"],["Ref","Reservations.State"]],"Z",["Data","Reservations.Choice"]]"#);
            let prior = archsig::definition::check_definitions(&[("d", old.as_bytes())]).unwrap();
            let checked =
                archsig::definition::check_definitions(&[("d", definition.as_bytes())]).unwrap();
            let prior = &prior.vocabularies["Reservations"].digest;
            let digest = &checked.vocabularies["Reservations"].digest;
            let map = std::fs::read_to_string(dir.join("a.json"))
                .unwrap()
                .replace(prior, digest);
            std::fs::write(dir.join("d.json"), definition).unwrap();
            std::fs::write(dir.join("a.json"), map).unwrap();
            vocabulary = vocabulary.replace(prior, digest);
        }
        if missing {
            let map = std::fs::read_to_string(dir.join("a.json"))
                .unwrap()
                .lines()
                .filter(|l| !l.contains(r#""id":"p-free""#) && !l.contains(r#""id":"r-free""#))
                .collect::<Vec<_>>()
                .join("\n");
            std::fs::write(dir.join("a.json"), map).unwrap();
        }
        let law = format!(
            r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{vocabulary} local here(left:State){guard} reads if left=left then {shape} else {shape};}}
reading After {{{vocabulary} local here(right:State) reads if right=right then {shape} else {shape};}}"#
        );
        std::fs::write(dir.join("l.law"), law).unwrap();
        let requests = [
            "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
            "same=compare($m.operation,to=$m.operation,kind=action)",
            "n=needed($m)",
        ];
        let run = asks(&dir, &requests);
        assert_eq!(run.code, 1, "{case}: {}", run.stdout);
        assert!(run.stderr.is_empty());
        let result = result_json(&dir, &run);
        let m = answer(&result, "m");
        assert_eq!(s(get(m, "status")), "refuted");
        assert!(has(get(m, "outputs"), "operation"));
        assert!(!has(get(m, "outputs"), "map"));
        assert!(!has(m, "counterexamples"));
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
        assert_eq!(s(get(answer(&result, "same"), "status")), "established");
        let plan = value(&result, get(get(answer(&result, "n"), "outputs"), "plan"));
        assert!(arr(get(plan, "requirements")).is_empty());
        let condition = value(&result, get(get(m, "outputs"), "proposition"));
        // 全Map域から得た反例。実際のreadはnone/空Listだけである。
        let expected = archsig::json::parse(br#"[[["v","p"],["v","p"]],[["v","q"],["v","p"]],[["v","r"],["v","p"]],[["v","s"],["v","p"]]]"#).unwrap();
        assert!(
            arr(get(condition, "operands"))
                .iter()
                .any(|r| value(&result, r).value == expected.value)
        );
        let mut args = vec![
            "run",
            "--atom-definition",
            "d.json",
            "--law",
            "l.law",
            "--archmap",
            "a.json",
        ];
        for request in &requests {
            args.extend(["--ask", request]);
        }
        let normal = without_file_changes(&dir, || cli::run(&dir, &args));
        assert_eq!(normal.code, 1, "{case}: {}", normal.stdout);
        assert_map_summary(&normal, &result);
        args.extend(["--out", "again", "--reuse", "out"]);
        let reused = cli::run(&dir, &args);
        assert_eq!(reused.code, 1, "{case}: {}", reused.stdout);
        let again = result_json(&dir, &reused);
        assert!(warnings(&again).is_empty());
        for key in ["answers", "nodes"] {
            assert_eq!(get(&result, key).value, get(&again, key).value);
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
    for (shape, wire) in [
        (
            "tuple",
            r#"["Tuple",["Ref","Reservations.State"],"Z","Bool",["Option","Bool"]]"#,
        ),
        (
            "option",
            r#"["Option",["Tuple",["Ref","Reservations.State"],"Z"]]"#,
        ),
        (
            "list",
            r#"["List",["Tuple",["Ref","Reservations.State"],"Z"]]"#,
        ),
        (
            "set",
            r#"["Set",["Tuple",["Ref","Reservations.State"],"Z"]]"#,
        ),
        ("data", r#"["Data","Reservations.Choice"]"#),
        (
            "map",
            r#"["Map",["Ref","Reservations.Key"],["Ref","Reservations.State"]]"#,
        ),
    ] {
        for (case, code) in [
            ("preserved", 0),
            ("refuted", 1),
            ("missing", 2),
            ("false-source", 0),
            ("target-guard", 1),
            ("identity-missing", 0),
        ] {
            for general in [false, true] {
                if general && case == "identity-missing" {
                    continue;
                }
                let name = format!("direct-compound-{shape}-{case}-{general}");
                let (dir, _) = if shape == "map" {
                    finite_local_map_inputs(&name)
                } else {
                    finite_local_parameter_inputs(&name)
                };
                let old = std::fs::read_to_string(dir.join("d.json")).unwrap();
                let mut definition=old.replace(r#"{"name": "free", "type": "Z""#,
                    &format!(r#"{{"name":"box","type":{wire},"meaning":"複合値"}},{{"name":"alternate","type":{wire},"meaning":"別の複合値"}},{{"name": "free", "type": "Z""#));
                if shape == "data" {
                    definition=definition.replace(r#""arguments":["Bool"]"#,r#""arguments":[["Ref","Reservations.State"],"Z",["Data","Reservations.Choice"]]"#);
                }
                let before =
                    archsig::definition::check_definitions(&[("d", old.as_bytes())]).unwrap();
                let checked =
                    archsig::definition::check_definitions(&[("d", definition.as_bytes())])
                        .unwrap();
                let digest = &checked.vocabularies["Reservations"].digest;
                let mut map = std::fs::read_to_string(dir.join("a.json"))
                    .unwrap()
                    .replace(&before.vocabularies["Reservations"].digest, digest);
                let mut atoms = String::new();
                for (subject, peer) in [("p", "q"), ("q", "p"), ("r", "s"), ("s", "r")] {
                    let r = format!(r#"["v","{subject}"]"#);
                    let other = format!(r#"["v","{peer}"]"#);
                    let (value, alternate) = match shape {
                        "tuple" => (
                            format!(r#"[{r},"0",false,{{"none":true}}]"#),
                            format!(r#"[{r},"1",false,{{"none":true}}]"#),
                        ),
                        "option" => (
                            format!(r#"{{"some":[{r},"0"]}}"#),
                            r#"{"none":true}"#.into(),
                        ),
                        "list" => (
                            format!(r#"[[{r},"0"],[{other},"1"],[{r},"0"]]"#),
                            format!(r#"[[{other},"1"],[{r},"0"],[{r},"0"]]"#),
                        ),
                        "set" => (
                            format!(r#"[[{r},"0"],[{other},"1"]]"#),
                            format!(r#"[[{r},"2"],[{other},"1"]]"#),
                        ),
                        "data" => (
                            format!(
                                r#"{{"tag":"Full","args":[{r},"0",{{"tag":"Empty","args":[]}}]}}"#
                            ),
                            format!(
                                r#"{{"tag":"Full","args":[{other},"0",{{"tag":"Empty","args":[]}}]}}"#
                            ),
                        ),
                        _ => (
                            format!(r#"[[["v","k"],{r}]]"#),
                            format!(r#"[[["v","k"],{other}]]"#),
                        ),
                    };
                    for (field, value) in [("box", value), ("alternate", alternate)] {
                        atoms.push_str(&format!(r#"{{"id":"{subject}-{field}","subject":"{subject}","field":"Reservations.State.{field}","value":{value},"origin":"model"}},
"#));
                    }
                }
                map = map.replacen("\"atoms\":[", &format!("\"atoms\":[\n{atoms}"), 1);

                // 追加fieldの移送だけを検査し、別の内部Reserve作用を課さない。
                map = without_reserve_instances(&map);
                if matches!(case, "missing" | "identity-missing" | "false-source") {
                    // baseの写像を確定したまま、型域中の外部subjectのreadだけを欠測にする。
                    map=map.replacen("\"subjects\":[",r#""subjects":[{"id":"C","type":"Reservations.System","origin":"model"},{"id":"x","type":"Reservations.State","origin":"model"},"#,1)
                        .replacen("\"atoms\":[",r#""atoms":[{"id":"x-owner","subject":"x","field":"Reservations.State.owner","value":["v","C"],"origin":"model"},"#,1);
                }
                if case == "identity-missing" {
                    map=map.replace(r#"[[["v","p"],["v","r"]],[["v","q"],["v","s"]]]"#,r#"[[["v","p"],["v","p"]],[["v","q"],["v","q"]]]"#)
                        .replace(r#""id":"m-to","subject":"m","field":"Reservations.Migration.to","value":["v","B"]"#,r#""id":"m-to","subject":"m","field":"Reservations.Migration.to","value":["v","A"]"#)
;
                }
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
                let sg = if case == "false-source" {
                    " when false"
                } else {
                    ""
                };
                let tg = if case == "target-guard" {
                    " when spare.free=2"
                } else {
                    ""
                };
                let vocabulary =
                    format!(r#"use vocabulary Reservations version "1" digest "{digest}";"#);
                let law = format!(
                    r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{vocabulary} local here(left:State,other:State,take:Bool){sg} reads {source_read};}}
reading After {{{vocabulary} local here(right:State,spare:State,keep:Bool){tg} reads {target_read};}}"#
                );
                std::fs::write(dir.join("d.json"), definition).unwrap();
                std::fs::write(dir.join("a.json"), map).unwrap();
                std::fs::write(dir.join("l.law"), law).unwrap();
                let requests = [
                    "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
                    "same=compare($m.operation,to=$m.operation,kind=action)",
                    "n=needed($m)",
                ];
                let run = asks(&dir, &requests);
                assert_eq!(run.code, code, "{shape}/{case}/{general}: {}", run.stdout);
                assert!(run.stderr.is_empty());
                let result = result_json(&dir, &run);
                let m = answer(&result, "m");
                assert_eq!(
                    s(get(m, "status")),
                    match code {
                        0 => "established",
                        1 => "refuted",
                        _ => "undetermined",
                    }
                );
                assert!(
                    has(get(m, "outputs"), "operation"),
                    "{shape}/{case}/{general}: {}",
                    run.stdout
                );
                assert_eq!(has(get(m, "outputs"), "map"), code == 0);
                assert_eq!(s(get(answer(&result, "same"), "status")), "established");
                let plan = value(&result, get(get(answer(&result, "n"), "outputs"), "plan"));
                assert_eq!(arr(get(plan, "requirements")).is_empty(), code != 2);
                if code == 2 {
                    assert!(!has(m, "counterexamples"));
                    assert!(
                        arr(get(plan, "requirements"))
                            .iter()
                            .all(|r| s(get(get(r, "field"), "field")) == "Reservations.State.box")
                    );
                }
                if case == "refuted" {
                    let data = get(value(&result, &arr(get(m, "counterexamples"))[0]), "data");
                    let bindings = arr(get(data, "bindings"));
                    assert_eq!(bindings.len(), 3);
                    assert_json(value(&result, get(&bindings[0], "value")), r#"["v","p"]"#);
                    assert_json(value(&result, get(&bindings[2], "value")), "false");
                    let (left, right) = match shape {
                        "tuple" => (
                            r#"[["v","p"],"0",false,{"none":true}]"#,
                            r#"[["v","r"],"1",false,{"none":true}]"#,
                        ),
                        "option" => (r#"{"some":[["v","p"],"0"]}"#, r#"{"none":true}"#),
                        "list" => (
                            r#"[[["v","p"],"0"],[["v","q"],"1"],[["v","p"],"0"]]"#,
                            r#"[[["v","s"],"1"],[["v","r"],"0"],[["v","r"],"0"]]"#,
                        ),
                        "set" => (
                            r#"[[["v","p"],"0"],[["v","q"],"1"]]"#,
                            r#"[[["v","r"],"2"],[["v","s"],"1"]]"#,
                        ),
                        "data" => (
                            r#"{"args":[["v","p"],"0",{"args":[],"tag":"Empty"}],"tag":"Full"}"#,
                            r#"{"args":[["v","s"],"0",{"args":[],"tag":"Empty"}],"tag":"Full"}"#,
                        ),
                        _ => (r#"[[["v","k"],["v","p"]]]"#, r#"[[["v","k"],["v","s"]]]"#),
                    };
                    assert_json(value(&result, get(data, "left")), left);
                    assert_json(value(&result, get(data, "right")), right);
                }
                if case == "preserved" {
                    let mapped = value(&result, get(get(m, "outputs"), "map"));
                    let transport = value(&result, &arr(get(mapped, "transports"))[0]);
                    let values = value(&result, get(&arr(get(transport, "clauses"))[0], "values"));
                    assert_json(get(values, "source_type"), wire);
                    let mut pairs = vec![("p", "r"), ("q", "s"), ("r", "r"), ("s", "s")];
                    if shape == "map" {
                        pairs.insert(0, ("k", "k"));
                    }
                    assert_reference_pairs(&result, values, &pairs);
                }
                if !general
                    && matches!(
                        case,
                        "preserved" | "refuted" | "missing" | "identity-missing"
                    )
                {
                    let mut args = vec![
                        "run",
                        "--atom-definition",
                        "d.json",
                        "--law",
                        "l.law",
                        "--archmap",
                        "a.json",
                    ];
                    for request in &requests {
                        args.extend(["--ask", request]);
                    }
                    let normal = without_file_changes(&dir, || cli::run(&dir, &args));
                    assert_eq!(normal.code, code, "{}", normal.stdout);
                    assert_map_summary(&normal, &result);
                    args.extend(["--out", "again", "--reuse", "out"]);
                    let reused = cli::run(&dir, &args);
                    assert_eq!(reused.code, code, "{}", reused.stdout);
                    let again = result_json(&dir, &reused);
                    assert!(warnings(&again).is_empty());
                    for key in ["answers", "nodes"] {
                        assert_eq!(get(&result, key).value, get(&again, key).value);
                    }
                }
            }
        }
    }
}

#[test]
fn local_direct_map_fields_check_type_domains_before_reads_and_guards() {
    for guard in ["", " when false"] {
        let dir = four_state_inputs(&format!("direct-map-domain-{}", guard.is_empty()));
        let old = std::fs::read_to_string(dir.join("d.json")).unwrap();
        let definition=old.replacen(r#""declarations": ["#,r#""declarations": [{"kind":"entity","name":"Reservations.Observer","meaning":"外部の読取り対象","parameters":[{"name":"owner","type":["Ref","Reservations.System"],"meaning":"所属先"}],"fields":[{"name":"box","type":["Map",["Ref","Reservations.State"],["Ref","Reservations.State"]],"meaning":"全域Map値"}],"alignments":[]},"#,1);
        let definition=definition.replace(r#"{"name": "states", "type":"#,r#"{"name":"observers","type":["Map",["Owned","Reservations.Observer","from"],["Owned","Reservations.Observer","to"]],"meaning":"空の所属対象対応"},{"name": "states", "type":"#);
        let before = archsig::definition::check_definitions(&[("d", old.as_bytes())]).unwrap();
        let checked =
            archsig::definition::check_definitions(&[("d", definition.as_bytes())]).unwrap();
        let digest = &checked.vocabularies["Reservations"].digest;
        let mut map = std::fs::read_to_string(dir.join("a.json"))
            .unwrap()
            .replace(&before.vocabularies["Reservations"].digest, digest);
        // source/targetのbaseは既知。外部Observerのslotは未読・欠測のままにする。
        map=map.replacen("\"subjects\":[",r#""subjects":[{"id":"C","type":"Reservations.System","origin":"model"},{"id":"w","type":"Reservations.Observer","origin":"model"},"#,1)
            .replacen("\"atoms\":[",r#""atoms":[{"id":"m-observers","subject":"m","field":"Reservations.Migration.observers","value":[],"origin":"model"},{"id":"w-owner","subject":"w","field":"Reservations.Observer.owner","value":["v","C"],"origin":"model"},"#,1);
        let vocabulary = format!(r#"use vocabulary Reservations version "1" digest "{digest}";"#);
        let law = format!(
            r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{vocabulary} local here(s:Observer){guard} reads s.box;}}
reading After {{{vocabulary} local here(t:Observer) reads (t.box);}}"#
        );
        std::fs::write(dir.join("d.json"), definition).unwrap();
        std::fs::write(dir.join("a.json"), map).unwrap();
        std::fs::write(dir.join("l.law"), law).unwrap();
        let requests = [
            "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
            "same=compare($m.operation,to=$m.operation,kind=action)",
            "n=needed($m)",
        ];
        let run = asks(&dir, &requests);
        assert_eq!(run.code, 1, "{guard}: {}", run.stdout);
        assert!(run.stderr.is_empty());
        let result = result_json(&dir, &run);
        let m = answer(&result, "m");
        assert!(
            has(get(m, "outputs"), "operation"),
            "{guard}: {}",
            run.stdout
        );
        assert!(!has(get(m, "outputs"), "map"));
        assert!(!has(m, "counterexamples"));
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
        assert_eq!(s(get(answer(&result, "same"), "status")), "established");
        let plan = value(&result, get(get(answer(&result, "n"), "outputs"), "plan"));
        assert!(arr(get(plan, "requirements")).is_empty());
        let condition = value(&result, get(get(m, "outputs"), "proposition"));
        let witness=archsig::json::parse(br#"[[["v","p"],["v","p"]],[["v","q"],["v","p"]],[["v","r"],["v","p"]],[["v","s"],["v","p"]]]"#).unwrap();
        assert!(
            arr(get(condition, "operands"))
                .iter()
                .any(|r| value(&result, r).value == witness.value)
        );
    }
}

#[test]
fn local_integer_arguments_preserve_the_entire_source_guard_fiber() {
    for (name, sg, tg, sr, tr, code) in [
        ("identity", "", "", "n+k", "m+j+0", 0),
        ("large", " when n=1000000007", "", "n", "1000000007", 0),
        (
            "multi-equation",
            " when 2*n+k=5 and n-k=1",
            " when m+j=3",
            "n+k",
            "3",
            0,
        ),
        ("coefficient", "", "", "n", "2*m", 1),
        ("point", " when n=17", " when m=17", "n", "17", 0),
        ("broader", " when 2*n=34", "", "n", "17", 0),
        ("narrower", "", " when m=17", "n", "m", 1),
        ("empty", " when 2*n=1", " when false", "n", "0", 0),
        ("kernel", " when n+k=17", " when m+j=17", "n+k", "17", 0),
        ("kernel-read", " when n+k=17", "", "n", "17", 1),
        (
            "reference-late",
            "",
            "",
            "n+s.free",
            "if t.held=1 then m+t.free+1 else m+t.free",
            1,
        ),
        (
            "finite-guard",
            " when flag and n+k=17",
            " when choice and m+j=17",
            "n+k",
            "17",
            0,
        ),
        ("kernel-guard", " when n+k=17", " when m=17", "n+k", "17", 1),
        (
            "finite-late",
            "",
            "",
            "if flag then n else n+k",
            "if choice then m+1 else m+j",
            1,
        ),
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
        let mut requests = vec![
            "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
            "same=compare($m.operation,to=$m.operation,kind=action)",
            "n=needed($m)",
        ];
        if name == "identity" {
            requests.push("b=build(After,on=$m.map.target.base.subject)");
        }
        let run = asks(&dir, &requests);
        assert_eq!(run.code, code, "{name}: {} {}", run.stdout, run.stderr);
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
        if name == "identity" {
            assert_eq!(s(get(answer(&result, "b"), "status")), "established");
        }
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
            if name.starts_with("kernel-") {
                assert_eq!(n + k, 17);
            }
            if name == "kernel-guard" {
                assert_ne!(n, 17);
            }
            if name == "finite-late" {
                assert_json(value(&result, get(&bindings[2], "value")), "true");
            }
            if name == "reference-late" {
                assert_json(value(&result, get(&bindings[1], "value")), r#"["v","q"]"#);
            }
            if name == "coefficient" {
                assert_ne!(n, 0);
            }
            assert_ne!(
                value(&result, get(data, "left")).value,
                value(&result, get(data, "right")).value
            );
        }
        if matches!(name, "identity" | "coefficient" | "kernel-guard") {
            let mut args = vec![
                "run",
                "--atom-definition",
                "d.json",
                "--law",
                "l.law",
                "--archmap",
                "a.json",
            ];
            for request in &requests {
                args.extend(["--ask", request]);
            }
            let normal = without_file_changes(&dir, || cli::run(&dir, &args));
            assert_eq!(normal.code, code, "{}", normal.stdout);
            assert!(normal.stderr.is_empty());
            if name != "identity" {
                assert_map_summary(&normal, &result);
            } else {
                assert_eq!(arr(get(&normal.receipt, "answers")).len(), 4);
                assert_eq!(
                    s(get(answer(&normal.receipt, "b"), "status")),
                    "established"
                );
                for trace in ["\"evidence\":", "\"node\":", "\"rule\":"] {
                    assert!(!normal.stdout.contains(trace));
                }
            }
            args.extend(["--out", "again", "--reuse", "out"]);
            let reused = cli::run(&dir, &args);
            assert_eq!(reused.code, code, "{}", reused.stdout);
            let again = result_json(&dir, &reused);
            for key in ["answers", "nodes"] {
                assert_eq!(get(&result, key).value, get(&again, key).value);
            }
        }
    }
}

#[test]
fn local_integer_missing_and_unsupported_conditions_remain_undetermined() {
    for (name, sg, tg, sr, tr, missing, code) in [
        ("source-guard", " when n=s.free", "", "n", "m", true, 2),
        (
            "target-guard",
            " when n=17",
            " when m=t.free",
            "n",
            "m",
            true,
            2,
        ),
        (
            "source-branch",
            " when if s.free=0 then n=1 else n=2",
            "",
            "n",
            "m",
            true,
            2,
        ),
        (
            "target-branch",
            " when n=2",
            " when if t.free=0 then m=1 else m=2",
            "n",
            "m",
            true,
            2,
        ),
        (
            "observed-guard",
            " when n=s.free",
            " when m=t.free",
            "n",
            "m",
            false,
            0,
        ),
        (
            "observed-branch",
            " when if s.free=0 then n=1 else n=2",
            " when if t.free=0 then m=1 else m=2",
            "n",
            "m",
            false,
            0,
        ),
        ("read", "", "", "n+s.free", "m+t.free", true, 2),
        (
            "false-source",
            " when false",
            " when m=t.free",
            "n+s.free",
            "m+t.free",
            true,
            0,
        ),
        ("inequality", " when n>0", "", "n", "m", false, 2),
        ("nonlinear-read", "", "", "n*n", "m*m", false, 2),
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
        assert_eq!(run.code, code, "{name}: {} {}", run.stdout, run.stderr);
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
        if name == "source-branch" {
            let mut args = vec![
                "run",
                "--atom-definition",
                "d.json",
                "--law",
                "l.law",
                "--archmap",
                "a.json",
            ];
            for request in &requests {
                args.extend(["--ask", request]);
            }
            let normal = without_file_changes(&dir, || cli::run(&dir, &args));
            assert_eq!(normal.code, 2, "{}", normal.stdout);
            assert!(normal.stderr.is_empty());
            assert_map_summary(&normal, &result);
            args.extend(["--out", "again", "--reuse", "out"]);
            let reused = cli::run(&dir, &args);
            assert_eq!(reused.code, 2, "{}", reused.stdout);
            let again = result_json(&dir, &reused);
            for key in ["answers", "nodes"] {
                assert_eq!(get(&result, key).value, get(&again, key).value);
            }
        }
    }
}

#[test]
fn local_integer_only_arguments_keep_full_domains_and_actual_counterexamples() {
    for (name, source, target, code) in [
        (
            "same",
            "local here(n:Z) reads n+1;",
            "local here(m:Z) reads m+1;",
            0,
        ),
        (
            "different",
            "local here(n:Z) reads n;",
            "local here(m:Z) reads m+1;",
            1,
        ),
        (
            "empty",
            "local here(n:Z) when 2*n=1 reads n*n;",
            "local here(m:Z) when false reads m*m;",
            0,
        ),
    ] {
        let (dir, vocabulary) =
            finite_local_parameter_inputs(&format!("local-integer-only-{name}"));
        std::fs::write(
            dir.join("l.law"),
            format!(
                r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{vocabulary} {source}}} reading After {{{vocabulary} {target}}}"#
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
        assert_eq!(run.code, code, "{name}: {} {}", run.stdout, run.stderr);
        let result = result_json(&dir, &run);
        let m = answer(&result, "m");
        assert_eq!(
            s(get(m, "status")),
            if code == 0 { "established" } else { "refuted" }
        );
        if code == 1 {
            let examples = arr(get(m, "counterexamples"));
            assert_eq!(examples.len(), 1);
            let data = get(value(&result, &examples[0]), "data");
            assert_eq!(arr(get(data, "bindings")).len(), 1);
            assert_json(value(&result, get(data, "left")), r#""0""#);
            assert_json(value(&result, get(data, "right")), r#""1""#);
        }
    }
}

fn rational_local_parameter_inputs(name: &str, missing: bool) -> (PathBuf, String) {
    #[allow(dead_code)]
    #[path = "common/architecture_environment.rs"]
    mod fixture;
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
    let digest = &after.vocabularies["Reservations"].digest;
    let text = std::fs::read_to_string(dir.join("a.json"))
        .unwrap()
        .replace(&before.vocabularies["Reservations"].digest, digest);
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
        ("identity", "", "", "q+r", "y+z", 0),
        (
            "reference-coefficient",
            " when q=s.free",
            " when y=t.free",
            "q",
            "t.free",
            0,
        ),
        ("negative-read", " when 2*q=-1", "", "q", "rat(0,1)", 1),
        (
            "point",
            " when 4*q=2",
            " when y=rat(1,2)",
            "q",
            "rat(1,2)",
            0,
        ),
        ("fraction-read", " when 2*q=1", "", "q", "rat(0,1)", 1),
        ("fraction-guard", " when 2*q=1", " when y=0", "q", "y", 1),
        ("broader", " when 2*q=1", "", "q", "rat(1,2)", 0),
        (
            "kernel",
            " when 2*q+r=rat(1,2)",
            " when 2*y+z=rat(1,2)",
            "2*q+r",
            "rat(1,2)",
            0,
        ),
        (
            "kernel-read",
            " when 2*q+r=rat(1,2)",
            "",
            "q",
            "rat(1,4)",
            1,
        ),
        (
            "kernel-guard",
            " when q+r=rat(1,2)",
            " when y=rat(1,2)",
            "q+r",
            "rat(1,2)",
            1,
        ),
        (
            "empty",
            " when q=rat(1,2) and 2*q=0",
            " when false",
            "q*q",
            "y*y",
            0,
        ),
        (
            "finite-late",
            "",
            "",
            "if take then q else q+r",
            "if keep then y+rat(1,3) else y+z",
            1,
        ),
        (
            "reference-late",
            "",
            "",
            "q",
            "if t.held=1 then y+rat(1,3) else y",
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
        let mut requests = vec![
            "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
            "same=compare($m.operation,to=$m.operation,kind=action)",
            "n=needed($m)",
        ];
        if name == "identity" {
            requests.push("b=build(After,on=$m.map.target.base.subject)");
        }
        let run = asks(&dir, &requests);
        assert_eq!(run.code, code, "{name}: {} {}", run.stdout, run.stderr);
        let result = result_json(&dir, &run);
        let m = answer(&result, "m");
        assert_eq!(
            s(get(m, "status")),
            if code == 0 { "established" } else { "refuted" }
        );
        assert!(has(get(m, "outputs"), "operation"));
        assert_eq!(has(get(m, "outputs"), "map"), code == 0);
        assert_eq!(s(get(answer(&result, "same"), "status")), "established");
        if name == "identity" {
            assert_eq!(s(get(answer(&result, "b"), "status")), "established");
        }
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
            let qs = arr(get(value(&result, get(clause, "commutes")), "quantifiers"));
            for (q, name) in qs.iter().zip(["q", "s", "take", "r"]) {
                assert_eq!(s(get(q, "name")), name);
            }
            assert_eq!(qs.len(), 4);
        } else {
            let examples = arr(get(m, "counterexamples"));
            assert_eq!(examples.len(), 1);
            let data = get(value(&result, &examples[0]), "data");
            let bindings = arr(get(data, "bindings"));
            assert_eq!(bindings.len(), 4);
            for (b, name) in bindings.iter().zip(["q", "s", "take", "r"]) {
                assert_eq!(s(get(b, "name")), name);
            }
            if name.starts_with("fraction-") {
                assert_json(value(&result, get(&bindings[0], "value")), r#"["1","2"]"#);
            }
            if name == "negative-read" {
                assert_json(value(&result, get(&bindings[0], "value")), r#"["-1","2"]"#);
                assert_json(value(&result, get(data, "left")), r#"["-1","2"]"#);
                assert_json(value(&result, get(data, "right")), r#"["0","1"]"#);
            }
            if name == "fraction-read" {
                assert_json(value(&result, get(data, "left")), r#"["1","2"]"#);
                assert_json(value(&result, get(data, "right")), r#"["0","1"]"#);
            }
            if name == "kernel-read" || name == "kernel-guard" {
                let q = arr(value(&result, get(&bindings[0], "value")));
                let r = arr(value(&result, get(&bindings[3], "value")));
                let (qn, qd, rn, rd): (i64, i64, i64, i64) = (
                    s(&q[0]).parse().unwrap(),
                    s(&q[1]).parse().unwrap(),
                    s(&r[0]).parse().unwrap(),
                    s(&r[1]).parse().unwrap(),
                );
                let factor = if name == "kernel-read" { 2 } else { 1 };
                assert_eq!(2 * (factor * qn * rd + rn * qd), qd * rd);
            }
            if name == "finite-late" {
                assert_json(value(&result, get(&bindings[2], "value")), "true");
            }
            if name == "reference-late" {
                assert_json(value(&result, get(&bindings[1], "value")), r#"["v","q"]"#);
            }
            assert_ne!(
                value(&result, get(data, "left")).value,
                value(&result, get(data, "right")).value
            );
        }
        if matches!(name, "point" | "fraction-read" | "fraction-guard") {
            let mut args = vec![
                "run",
                "--atom-definition",
                "d.json",
                "--law",
                "l.law",
                "--archmap",
                "a.json",
            ];
            for request in &requests {
                args.extend(["--ask", request]);
            }
            let normal = without_file_changes(&dir, || cli::run(&dir, &args));
            assert_eq!(normal.code, code, "{}", normal.stdout);
            assert!(normal.stderr.is_empty());
            assert_map_summary(&normal, &result);
            args.extend(["--out", "again", "--reuse", "out"]);
            let reused = cli::run(&dir, &args);
            assert_eq!(reused.code, code, "{}", reused.stdout);
            let again = result_json(&dir, &reused);
            for key in ["answers", "nodes"] {
                assert_eq!(get(&result, key).value, get(&again, key).value);
            }
        }
    }
}

#[test]
fn local_rational_guard_missing_and_unsupported_algorithms_keep_their_reasons() {
    for (name, sg, tg, sr, tr, missing, code) in [
        (
            "source-coefficient",
            " when q=s.free",
            "",
            "q",
            "y",
            true,
            2,
        ),
        (
            "source-branch",
            " when if s.free=0 then 2*q=1 else q=1",
            "",
            "q",
            "y",
            true,
            2,
        ),
        (
            "target-branch",
            " when 2*q=1",
            " when if t.free=0 then y=1 else 2*y=1",
            "q",
            "y",
            true,
            2,
        ),
        (
            "observed-branch",
            " when if s.free=0 then q=1 else 2*q=1",
            " when if t.free=0 then y=1 else 2*y=1",
            "q",
            "y",
            false,
            0,
        ),
        (
            "read",
            "",
            "",
            "if s.free=0 then q else q+rat(1,2)",
            "if t.free=0 then y else y+rat(1,2)",
            true,
            2,
        ),
        (
            "inactive",
            " when false",
            " when if t.free=0 then y=1 else 2*y=1",
            "q",
            "y",
            true,
            0,
        ),
        ("inequality", " when q>0", "", "q", "y", false, 2),
        ("nonlinear-read", "", "", "q*q", "y*y", false, 2),
        ("nonlinear-guard", " when q*q=1", "", "q", "y", false, 2),
    ] {
        let (dir, vocabulary) =
            rational_local_parameter_inputs(&format!("local-q-unknown-{name}"), missing);
        std::fs::write(
            dir.join("l.law"),
            format!(
                r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{vocabulary} local here(s:State,q:Q){sg} reads {sr};}}
reading After {{{vocabulary} local here(t:State,y:Q){tg} reads {tr};}}"#
            ),
        )
        .unwrap();
        let requests = [
            "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
            "same=compare($m.operation,to=$m.operation,kind=action)",
            "n=needed($m)",
        ];
        let run = asks(&dir, &requests);
        assert_eq!(run.code, code, "{name}: {} {}", run.stdout, run.stderr);
        let result = result_json(&dir, &run);
        let m = answer(&result, "m");
        assert_eq!(
            s(get(m, "status")),
            if code == 0 {
                "established"
            } else {
                "undetermined"
            }
        );
        assert!(!has(m, "counterexamples") || arr(get(m, "counterexamples")).is_empty());
        assert!(has(get(m, "outputs"), "operation"));
        assert_eq!(has(get(m, "outputs"), "map"), code == 0);
        assert_eq!(s(get(answer(&result, "same"), "status")), "established");
        let plan = value(&result, get(get(answer(&result, "n"), "outputs"), "plan"));
        if missing && code == 2 {
            assert!(
                arr(get(plan, "requirements"))
                    .iter()
                    .any(|r| s(get(get(r, "field"), "field")) == "Reservations.State.free")
            );
        }
        if !missing {
            assert!(arr(get(plan, "requirements")).is_empty());
        }
        if name == "source-branch" {
            let mut args = vec![
                "run",
                "--atom-definition",
                "d.json",
                "--law",
                "l.law",
                "--archmap",
                "a.json",
            ];
            for request in &requests {
                args.extend(["--ask", request]);
            }
            let normal = without_file_changes(&dir, || cli::run(&dir, &args));
            assert_eq!(normal.code, 2, "{}", normal.stdout);
            assert_map_summary(&normal, &result);
            assert!(normal.stderr.is_empty());
            args.extend(["--out", "again", "--reuse", "out"]);
            let reused = cli::run(&dir, &args);
            assert_eq!(reused.code, 2, "{}", reused.stdout);
            let again = result_json(&dir, &reused);
            for key in ["answers", "nodes"] {
                assert_eq!(get(&result, key).value, get(&again, key).value);
            }
        }
    }
}

#[test]
fn local_rational_only_arguments_keep_fraction_witnesses_and_mixed_domains_unsupported() {
    for (name, source, target, code) in [
        (
            "identity",
            "local here(q:Q) reads q+1;",
            "local here(y:Q) reads y+1;",
            0,
        ),
        (
            "fraction",
            "local here(q:Q) when 2*q=1 reads q;",
            "local here(y:Q) reads rat(0,1);",
            1,
        ),
    ] {
        let (dir, vocabulary) =
            rational_local_parameter_inputs(&format!("local-q-only-{name}"), false);
        std::fs::write(
            dir.join("l.law"),
            format!(
                r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{vocabulary} {source}}} reading After {{{vocabulary} {target}}}"#
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
        assert_eq!(run.code, code, "{name}: {} {}", run.stdout, run.stderr);
        let result = result_json(&dir, &run);
        let m = answer(&result, "m");
        assert_eq!(
            s(get(m, "status")),
            if code == 0 { "established" } else { "refuted" }
        );
        if code == 1 {
            let examples = arr(get(m, "counterexamples"));
            assert_eq!(examples.len(), 1);
            let data = get(value(&result, &examples[0]), "data");
            let bindings = arr(get(data, "bindings"));
            assert_eq!(bindings.len(), 1);
            assert_json(value(&result, get(&bindings[0], "value")), r#"["1","2"]"#);
            assert_json(value(&result, get(data, "left")), r#"["1","2"]"#);
            assert_json(value(&result, get(data, "right")), r#"["0","1"]"#);
        }
    }
    for params in ["n:Z,q:Q", "q:Q,n:Z"] {
        let (dir, vocabulary) = rational_local_parameter_inputs(
            &format!("local-q-mixed-{}", params.starts_with('n')),
            false,
        );
        std::fs::write(
            dir.join("l.law"),
            format!(
                r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Before {{{vocabulary} local here({params}) reads q;}}
reading After {{{vocabulary} local here({params}) reads q;}}"#
            ),
        )
        .unwrap();
        let run = without_file_changes(&dir, || {
            cli::run(
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
                    "m=map(Reservations.Migration,on=@v/m,reading=Before,to_reading=After,kind=object_algebra)",
                ],
            )
        });
        assert_eq!(run.code, 70, "{params}: {}", run.stdout);
        assert!(run.stderr.is_empty());
        assert!(has(&run.receipt, "issues"));
    }
}
