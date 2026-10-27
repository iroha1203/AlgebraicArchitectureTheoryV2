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

#[test]
fn local_reference_fields_follow_the_map_instead_of_raw_equality() {
    for (mode, code, status) in [("preserved", 0, "established"), ("changed", 1, "refuted")] {
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
        let normal = cli::run(&dir, &args);
        assert_eq!(normal.code, code, "{}", normal.stdout);
        assert!(normal.stderr.is_empty());
        assert!(normal.stdout.len() < 1000);
        assert_eq!(std::fs::read_dir(&dir).unwrap().count(), 3);
        let run = asks(&dir, &requests);
        assert_eq!(run.code, code, "{}", run.stdout);
        let result = result_json(&dir, &run);
        assert_eq!(s(get(answer(&result, "m"), "status")), status);
        assert_eq!(s(get(answer(&result, "same"), "status")), "established");
        let outputs = get(answer(&result, "m"), "outputs");
        assert_eq!(has(outputs, "map"), mode == "preserved");
        if mode == "preserved" {
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
                &[
                    ("p", "r"),
                    ("q", "s"),
                    ("r", "r"),
                    ("s", "s"),
                    ("u", "w"),
                    ("w", "w"),
                ],
            );
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
reading Before {{{vocabulary} local here(root:System,s:State) reads s.free;}}
reading After {{{vocabulary} local here(world:System,t:State) reads (t.free);}}"#
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
