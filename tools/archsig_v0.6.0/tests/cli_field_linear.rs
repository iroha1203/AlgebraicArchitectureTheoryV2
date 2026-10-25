//! 有理線形系から元Assignmentと修復後の値を計算する公開経路。
#[allow(dead_code)]
#[path = "common/cli.rs"]
mod cli;
use archsig::{definition, json::JNode};
use cli::*;
fn node<'a>(j: &'a JNode, r: &JNode) -> &'a JNode {
    arr(get(j, "nodes"))
        .iter()
        .find(|n| s(get(n, "id")) == s(get(r, "node")))
        .unwrap()
}
fn output<'a>(j: &'a JNode, i: usize, key: &str) -> &'a JNode {
    node(j, get(get(&arr(get(j, "answers"))[i], "outputs"), key))
}
fn input(name: &str, body: &str) -> std::path::PathBuf {
    let d = r#"{"format":"archsig.atom-definition/1","semantics":"archsig/0.6.0","vocabularies":[{"semantics":"archsig/0.6.0","namespace":"Pair","version":"1","dependencies":[],"declarations":[{"kind":"entity","name":"Pair.State","meaning":"有理二座標。","parameters":[],"fields":[{"name":"x","type":"Q","meaning":"第一座標。"},{"name":"y","type":"Q","meaning":"第二座標。"}],"alignments":[]}]}]}"#;
    let checked = definition::check_definitions(&[("d", d.as_bytes())]).unwrap();
    let digest = &checked.vocabularies["Pair"].digest;
    let law = format!(
        "law \"archsig.law/2\" semantics \"archsig/0.6.0\"; reading Pair {{ use vocabulary Pair version \"1\" digest \"{digest}\"; {body} view x(s:State):Q=s.x; }}"
    );
    let map = format!(
        r#"{{"format":"archsig.archmap/2","semantics":"archsig/0.6.0","vocabularies":[{{"namespace":"Pair","version":"1","digest":"{digest}"}}],"sources":[],"origins":[{{"id":"model","mode":"specification","method":"有理線形系の独立入力。","locations":[],"note":"初期値だけを指定。"}}],"snapshots":[{{"id":"v","origin":"model","subjects":[{{"id":"s","type":"Pair.State","origin":"model"}}],"atoms":[{{"id":"x","subject":"s","field":"Pair.State.x","value":["0","1"],"origin":"model"}},{{"id":"y","subject":"s","field":"Pair.State.y","value":["0","1"],"origin":"model"}}]}}]}}"#
    );
    let dir = workdir(name);
    for (name, text) in [("d.json", d), ("l.law", &law), ("a.json", &map)] {
        std::fs::write(dir.join(name), text).unwrap();
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
#[test]
fn rational_unique_repair_keeps_exact_fraction_and_original_observations() {
    let dir = input(
        "rational-unique-repair",
        "change choose(s:State,a:Q,b:Q)=s with{x=a,y=b}; law required pinned(s:State):(s.x+s.y=1) and (s.x-s.y=0);",
    );
    let asks = [
        "r=repair(Pair.pinned,on=@v/s,using=Pair.choose)",
        "x=evaluate(Pair.x,on=$r.object,s=@v/s)",
        "c=check(Pair.pinned,on=$r.object)",
        "old=evaluate(Pair.x,s=@v/s)",
    ];
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
        "120000",
    ];
    for ask in asks {
        args.extend(["--ask", ask]);
    }
    let r = run(&dir, &args);
    assert_eq!(r.code, 0, "{} {}", r.stdout, r.stderr);
    let j = result_json(&dir, &r);
    assert_eq!(
        arr(get(output(&j, 1, "value"), "value"))
            .iter()
            .map(s)
            .collect::<Vec<_>>(),
        ["1", "2"]
    );
    assert_eq!(
        arr(get(output(&j, 3, "value"), "value"))
            .iter()
            .map(s)
            .collect::<Vec<_>>(),
        ["0", "1"]
    );
    assert_eq!(s(get(&arr(get(&j, "answers"))[2], "status")), "established");
    let mut again_args = vec![
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
        again_args.extend(["--ask", ask]);
    }
    let reused = run(&dir, &again_args);
    assert_eq!(reused.code, 0, "{} {}", reused.stdout, reused.stderr);
    let again = result_json(&dir, &reused);
    for field in ["answers", "nodes"] {
        assert_eq!(get(&j, field).value, get(&again, field).value);
    }
}

fn verify_inconsistent_wire(j: &JNode, proof: &JNode) {
    use num_bigint::BigInt;
    let scalar = |reference: &JNode| {
        let parts = arr(get(node(j, reference), "value"));
        (
            s(&parts[0]).parse::<BigInt>().unwrap(),
            s(&parts[1]).parse::<BigInt>().unwrap(),
        )
    };
    let data = get(proof, "data");
    let u = arr(get(
        get(node(j, get(data, "annihilator")), "value"),
        "coordinates",
    ))
    .iter()
    .map(&scalar)
    .collect::<Vec<_>>();
    let dot = |v: &[JNode]| {
        assert_eq!(v.len(), u.len());
        v.iter().zip(&u).fold(
            (BigInt::from(0), BigInt::from(1)),
            |(n, d), (x, (un, ud))| {
                let (xn, xd) = scalar(x);
                (n * &xd * ud + un * xn * &d, d * xd * ud)
            },
        )
    };
    let columns = arr(get(get(node(j, get(data, "map")), "value"), "columns"));
    for column in columns {
        assert_eq!(dot(arr(column)).0, BigInt::from(0));
    }
    let paired = dot(arr(get(
        get(node(j, get(data, "rhs")), "value"),
        "coordinates",
    )));
    assert_ne!(paired.0, BigInt::from(0));
    let claimed = scalar(get(data, "pairing"));
    assert_eq!(paired.0 * claimed.1, claimed.0 * paired.1);
}
#[test]
fn rational_fibers_keep_nonunique_assignments_and_inconsistency() {
    for (label, change, law, rank) in [
        (
            "line",
            "change choose(s:State,a:Q,b:Q)=s with{x=a,y=b};",
            "s.x+s.y=1",
            Some(1),
        ),
        (
            "same-effect",
            "change choose(s:State,a:Q,b:Q)=s with{x=a+b,y=a+b};",
            "s.x=1",
            Some(1),
        ),
        (
            "inconsistent",
            "change choose(s:State,a:Q,b:Q)=s with{x=a,y=b};",
            "s.x=0 and s.x=1",
            None,
        ),
        (
            "guard-empty",
            "change choose(s:State,a:Q,b:Q) when a=0 and a=1=s with{x=a,y=b};",
            "s.x=0",
            None,
        ),
    ] {
        let dir = input(
            label,
            &format!("{change} law required pinned(s:State):{law};"),
        );
        let r = execute(
            &dir,
            "out",
            &[
                "r=repair(Pair.pinned,on=@v/s,using=Pair.choose)",
                "s=solve(Pair.pinned,on=@v/s,using=Pair.choose)",
            ],
        );
        assert_eq!(r.code, 1, "{label}: {} {}", r.stdout, r.stderr);
        let j = result_json(&dir, &r);
        assert!(!has(get(&arr(get(&j, "answers"))[0], "outputs"), "object"));
        let repr = get(get(output(&j, 0, "solutions"), "value"), "representation");
        assert_eq!(
            s(get(
                get(get(output(&j, 1, "solutions"), "value"), "representation"),
                "kind"
            )),
            s(get(repr, "kind"))
        );
        if let Some(rank) = rank {
            assert_eq!(s(get(repr, "kind")), "affine");
            assert_eq!(
                num(get(
                    get(node(&j, get(repr, "directions")), "value"),
                    "free_rank"
                )),
                rank
            );
            assert_eq!(
                s(get(get(output(&j, 0, "existence"), "judgment"), "status")),
                "established"
            );
        } else {
            assert_eq!(s(get(repr, "kind")), "empty");
            let proof = get(node(&j, get(repr, "certificate")), "value");
            assert_eq!(s(get(proof, "kind")), "linear_inconsistent");
            verify_inconsistent_wire(&j, proof);
            assert_eq!(
                s(get(get(output(&j, 0, "existence"), "judgment"), "status")),
                "refuted"
            );
        }
    }
}
#[test]
fn rational_guard_and_missing_preserve_original_parameters_and_needed_field() {
    let dir = input(
        "rational-guard",
        "change choose(s:State,a:Q,b:Q) when a+b=1=s with{x=a,y=b}; law required pinned(s:State):s.x=s.y;",
    );
    let r = execute(
        &dir,
        "out",
        &[
            "r=repair(Pair.pinned,on=@v/s,using=Pair.choose)",
            "x=evaluate(Pair.x,on=$r.object,s=@v/s)",
        ],
    );
    assert_eq!(r.code, 0, "{} {}", r.stdout, r.stderr);
    let j = result_json(&dir, &r);
    assert_eq!(
        arr(get(output(&j, 1, "value"), "value"))
            .iter()
            .map(s)
            .collect::<Vec<_>>(),
        ["1", "2"]
    );
    let dir = input(
        "rational-missing",
        "change choose(s:State,a:Q)=s with{x=a}; law required pinned(s:State):s.x=s.y;",
    );
    let path = dir.join("a.json");
    let map = std::fs::read_to_string(&path).unwrap();
    let missing = map.replace(
        r#",{"id":"y","subject":"s","field":"Pair.State.y","value":["0","1"],"origin":"model"}"#,
        "",
    );
    assert_ne!(map, missing);
    std::fs::write(path, missing).unwrap();
    let r = execute(
        &dir,
        "out",
        &[
            "r=repair(Pair.pinned,on=@v/s,using=Pair.choose)",
            "n=needed($r)",
        ],
    );
    assert_eq!(r.code, 2, "{} {}", r.stdout, r.stderr);
    let j = result_json(&dir, &r);
    let plan = get(output(&j, 1, "plan"), "value");
    assert!(
        arr(get(plan, "requirements"))
            .iter()
            .any(|r| s(get(get(r, "field"), "field")) == "Pair.State.y")
    );
}

#[test]
fn rational_repair_stop_after_first_witness_keeps_existence_without_object() {
    use archsig::observed::{
        control::{Checkpoint, Control, Limits, Usage},
        evaluate::evaluate_observed_bytes,
        input::InputSources,
    };
    use std::{cell::Cell, rc::Rc};
    let dir = input(
        "rational-stop",
        "change choose(s:State,a:Q,b:Q)=s with{x=a,y=b};law required pinned(s:State):s.x+s.y=1;",
    );
    for mode in 0..3 {
        let seen = Rc::new(Cell::new(0));
        let count = seen.clone();
        let mut c = Control::new(
            Limits {
                time_ms: Some(1),
                memory_mib: Some(1),
            },
            move |point| {
                if point == Checkpoint::ChangeWitness {
                    count.set(count.get() + 1);
                }
                if count.get() == 2 {
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
        let source = InputSources::from_bytes(
            vec![std::fs::read(dir.join("d.json")).unwrap()],
            std::fs::read(dir.join("l.law")).unwrap(),
            std::fs::read(dir.join("a.json")).unwrap(),
        );
        let result = evaluate_observed_bytes(
            source,
            &[
                "r=repair(Pair.pinned,using=Pair.choose,on=@v/s,s=@v/s)",
                "later=check(Pair.pinned,s=@v/s)",
            ],
            &mut c,
        )
        .unwrap();
        assert_eq!(seen.get(), 2);
        let wire = archsig::json::parse(result.wire().canonical().as_bytes()).unwrap();
        let answers = arr(get(&wire, "answers"));
        let first = &answers[0];
        assert_eq!(s(get(first, "status")), "undetermined");
        assert!(!has(get(first, "outputs"), "object"));
        assert!(!has(get(first, "outputs"), "repair"));
        assert!(!has(get(first, "outputs"), "proposition"));
        assert_eq!(
            s(get(
                get(output(&wire, 0, "existence"), "judgment"),
                "status"
            )),
            "established"
        );
        assert_eq!(s(get(&answers[1], "status")), "undetermined");
        let code = if mode == 2 {
            "cancelled"
        } else {
            "budget_exhausted"
        };
        for answer in answers {
            assert!(
                arr(get(answer, "reasons"))
                    .iter()
                    .any(|r| s(get(r, "code")) == code)
            );
        }
    }
}

#[test]
fn rational_missing_conditions_keep_source_binding_and_needed_field() {
    let mut failures = vec![];
    for (guard, body, parameter_count) in [
        (
            "s.y=0",
            "change choose(s:State,a:Q)=s with{x=a};law required pinned(s:State) when s.y=0:s.x=0;",
            0,
        ),
        (
            "s.y=0 and s.x=0",
            "change choose(s:State,a:Q)=s with{x=a};law required pinned(s:State) when s.y=0 and s.x=0:s.x=0;",
            0,
        ),
        (
            "s.y=0",
            "change choose(s:State,a:Q)=if s.y=0 then s with{x=a} else s with{x=a};law required pinned(s:State):s.x=0;",
            1,
        ),
        (
            "s.y>0",
            "change choose(s:State,a:Q) when s.y>0=s with{x=a};law required pinned(s:State):s.x=0;",
            1,
        ),
        (
            "(if s.y>0 then true else false)",
            "change choose(s:State,a:Q) when (if s.y>0 then true else false)=s with{x=a};law required pinned(s:State):s.x=0;",
            1,
        ),
        (
            "positive(s)",
            "view positive(s:State):Bool=s.y>0;change choose(s:State,a:Q) when positive(s)=s with{x=a};law required pinned(s:State):s.x=0;",
            1,
        ),
        (
            "(let b=s.y>0 in b)",
            "change choose(s:State,a:Q) when (let b=s.y>0 in b)=s with{x=a};law required pinned(s:State):s.x=0;",
            1,
        ),
    ] {
        let dir = input("rational-missing-conditions", body);
        let path = dir.join("a.json");
        let map = std::fs::read_to_string(&path).unwrap();
        let missing=map.replace(r#",{"id":"y","subject":"s","field":"Pair.State.y","value":["0","1"],"origin":"model"}"#,"");
        assert_ne!(map, missing);
        std::fs::write(path, missing).unwrap();
        let asks = [
            "r=repair(Pair.pinned,on=@v/s,using=Pair.choose)",
            "n=needed($r)",
        ];
        let r = execute(&dir, "out", &asks);
        if r.code != 2 {
            failures.push(format!("{guard}: {} {}", r.stdout, r.stderr));
            continue;
        }
        let j = result_json(&dir, &r);
        let answer = &arr(get(&j, "answers"))[0];
        let reason = arr(get(answer, "reasons"))
            .iter()
            .find(|r| s(get(r, "code")) == "missing_observation")
            .unwrap();
        let expression = get(node(&j, &arr(get(reason, "dependencies"))[0]), "value");
        let span = arr(get(get(expression, "location"), "span"));
        let law = std::fs::read_to_string(dir.join("l.law")).unwrap();
        assert_eq!(&law[num(&span[0]) as usize..num(&span[1]) as usize], guard);
        let binding = arr(get(expression, "bindings"))
            .iter()
            .find(|b| s(get(b, "name")) == "s")
            .unwrap();
        assert_eq!(
            arr(get(node(&j, get(binding, "value")), "value"))
                .iter()
                .map(s)
                .collect::<Vec<_>>(),
            ["v", "s"]
        );
        assert_eq!(arr(get(expression, "parameters")).len(), parameter_count);
        let plan = get(output(&j, 1, "plan"), "value");
        assert!(
            arr(get(plan, "requirements"))
                .iter()
                .any(|r| s(get(get(r, "field"), "field")) == "Pair.State.y")
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
        assert_eq!(reused.code, 2, "{} {}", reused.stdout, reused.stderr);
        let again = result_json(&dir, &reused);
        for field in ["answers", "nodes"] {
            assert_eq!(get(&j, field).value, get(&again, field).value);
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

#[test]
fn rational_quotient_keeps_candidate_solution_domains_and_law_descent() {
    let dir = input("rational-quotient", "change choose(s:State,a:Q,b:Q) when a+b=1=s with{x=a,y=b}; law required pinned(s:State):s.x=s.y; view total(s:State):Q=s.x+s.y; law optional total_law(s:State):s.x+s.y=1;");
    let asks=[
        "s=solve(Pair.pinned,on=@v/s,using=Pair.choose)",
        "q=quotient(Pair.total,on=$s.domain,s=@v/s,law=Pair.total_law)",
        "bad=quotient(Pair.total,on=$s.domain,s=@v/s,law=Pair.pinned)",
        "good=quotient(Pair.total,on=$s.solutions,s=@v/s,law=Pair.pinned)",
    ];
    let r=execute(&dir,"out",&asks);
    assert_eq!(r.code,1,"{} {}",r.stdout,r.stderr);
    let j=result_json(&dir,&r);
    for (i,status) in [(1,"established"),(2,"refuted"),(3,"established")] {
        assert_eq!(s(get(&arr(get(&j,"answers"))[i],"status")),status);
    }
    let bad=&arr(get(&j,"answers"))[2];
    let proof=get(node(&j,&arr(get(bad,"evidence"))[0]),"value");
    assert_eq!(s(get(proof,"kind")),"separating_pair");
    let data=get(proof,"data");let views=arr(get(data,"view_values"));let laws=arr(get(data,"law_values"));
    assert_eq!(get(node(&j,&views[0]),"value").value,get(node(&j,&views[1]),"value").value);
    assert_ne!(get(node(&j,&laws[0]),"value").value,get(node(&j,&laws[1]),"value").value);
    assert_ne!(get(node(&j,get(data,"first")),"value").value,get(node(&j,get(data,"second")),"value").value);
    let q=get(output(&j,1,"quotient"),"value");
    let rep=get(q,"representation");
    assert_eq!(s(get(rep,"kind")),"affine");
    let offset=get(node(&j,get(rep,"offset")),"value");
    let scalar=node(&j,&arr(get(offset,"coordinates"))[0]);
    assert_eq!(arr(get(scalar,"value")).iter().map(s).collect::<Vec<_>>(),["1","1"]);
}

fn qcoordinates(j:&JNode,reference:&JNode)->Vec<Vec<String>> {
    arr(get(get(node(j,reference),"value"),"coordinates")).iter().map(|r|arr(get(node(j,r),"value")).iter().map(|v|s(v).to_owned()).collect()).collect()
}
#[test]
fn rational_quotient_image_and_descent_keep_fractional_coordinates_and_reuse() {
    let dir=input("rational-quotient-image","change choose(s:State,a:Q,b:Q)=s with{x=rat(1,2)*a+rat(1,3),y=b}; law required total(s:State):s.x+s.y=1; view twice(s:State):Q=2*s.x; law optional same(s:State):s.x=s.x;");
    let asks=["s=solve(Pair.total,on=@v/s,using=Pair.choose)","q=quotient(Pair.twice,on=$s.domain,s=@v/s,law=Pair.same)","sum=quotient(Pair.x,on=$s.solutions,s=@v/s)"];
    let r=execute(&dir,"out",&asks);assert_eq!(r.code,0,"{} {}",r.stdout,r.stderr);let j=result_json(&dir,&r);
    let q=get(output(&j,1,"quotient"),"value");let rep=get(q,"representation");
    assert_eq!(qcoordinates(&j,get(rep,"offset")),vec![vec!["2".to_owned(),"3".to_owned()]]);
    let image=get(node(&j,get(rep,"image")),"value");assert_eq!(num(get(image,"free_rank")),1);
    let descent=get(node(&j,get(q,"descent")),"value");
    assert_eq!(qcoordinates(&j,get(descent,"offset")),vec![vec!["1".to_owned(),"3".to_owned()];2]);
    let columns=arr(get(get(node(&j,get(descent,"linear")),"value"),"columns"));assert_eq!(columns.len(),1);
    for v in arr(&columns[0]) {assert_eq!(arr(get(node(&j,v),"value")).iter().map(s).collect::<Vec<_>>(),["1","2"]);}
    let mut args=vec!["run","--atom-definition","d.json","--archmap","a.json","--law","l.law","--out","again","--reuse","out","--time-ms","120000"];
    for ask in asks {args.extend(["--ask",ask]);}let reused=run(&dir,&args);assert_eq!(reused.code,0,"{} {}",reused.stdout,reused.stderr);let again=result_json(&dir,&reused);for key in ["answers","nodes"]{assert_eq!(get(&j,key).value,get(&again,key).value);}
}
#[test]
fn rational_quotient_empty_and_missing_do_not_become_a_constant_class() {
    for (label,guard,law,on) in [("guard"," when a=0 and a=1","s.x=0","$s.domain"),("solution","","s.x=0 and s.x=1","$s.solutions")] {
        let dir=input(label,&format!("change choose(s:State,a:Q){guard}=s with{{x=a}};law required impossible(s:State):{law};view fixed(s:State):Q=7;"));
        let q=format!("q=quotient(Pair.fixed,on={on},s=@v/s)");let r=execute(&dir,"out",&["s=solve(Pair.impossible,on=@v/s,using=Pair.choose)",&q]);assert_eq!(r.code,1,"{} {}",r.stdout,r.stderr);let j=result_json(&dir,&r);let q=get(output(&j,1,"quotient"),"value");assert!(arr(get(get(q,"representation"),"fibers")).is_empty());
    }
    let dir=input("rational-quotient-missing","change choose(s:State,a:Q)=s with{x=a};law required first(s:State):s.x=0;view second(s:State):Q=s.y;law optional same(s:State):s.y=s.y;");
    let path=dir.join("a.json");let old=std::fs::read_to_string(&path).unwrap();let new=old.replace(r#",{"id":"y","subject":"s","field":"Pair.State.y","value":["0","1"],"origin":"model"}"#,"");assert_ne!(new,old);std::fs::write(path,new).unwrap();
    for (label,ask) in [("view","q=quotient(Pair.second,on=$s.domain,s=@v/s)"),("law","q=quotient(Pair.x,on=$s.domain,s=@v/s,law=Pair.same)")] {
        let r=execute(&dir,label,&["s=solve(Pair.first,on=@v/s,using=Pair.choose)",ask]);assert_eq!(r.code,2,"{} {}",r.stdout,r.stderr);let j=result_json(&dir,&r);let answer=&arr(get(&j,"answers"))[1];assert_eq!(s(get(answer,"status")),"undetermined");assert!(!has(get(answer,"outputs"),"quotient"));assert!(arr(get(answer,"reasons")).iter().any(|r|s(get(r,"code"))=="missing_observation"));
    }
}

#[test]
fn rational_tuple_quotient_retains_nested_image_and_law_family() {
    let dir=input("rational-tuple-quotient","change choose(s:State,a:Q,b:Q)=s with{x=a,y=b};law required total(s:State):s.x+s.y=1;law optional same(s:State):s.x=s.x;view pair(s:State):(Q,(Q,Q))=(s.x,(s.y,rat(1,3)));view combined(s:State):(Q,Q)=(s.x+s.y,2*(s.x+s.y));");
    let asks=["s=solve(Pair.total,on=@v/s,using=Pair.choose)","good=quotient(Pair.pair,on=$s.domain,s=@v/s,law=Pair.same)","bad=quotient(Pair.combined,on=$s.domain,s=@v/s,law=Pair.same)","solutions=quotient(Pair.pair,on=$s.solutions,s=@v/s,law=Pair.total)"];
    let r=execute(&dir,"out",&asks);
    assert_eq!(r.code,1,"{} {}",r.stdout,r.stderr);let j=result_json(&dir,&r);
    for (i,status) in [(1,"established"),(2,"refuted"),(3,"established")] {assert_eq!(s(get(&arr(get(&j,"answers"))[i],"status")),status);}
    let q=get(output(&j,1,"quotient"),"value");let rep=get(q,"representation");let image=get(node(&j,get(rep,"image")),"value");assert_eq!(num(get(image,"free_rank")),2);
    let generator=get(&arr(get(image,"generators"))[0],"value");assert_eq!(arr(generator).len(),2);assert_eq!(arr(&arr(generator)[1]).len(),2);
    assert_eq!(qcoordinates(&j,get(rep,"offset")),vec![vec!["0".to_owned(),"1".to_owned()],vec!["0".to_owned(),"1".to_owned()],vec!["1".to_owned(),"3".to_owned()]]);
    let proof=get(node(&j,&arr(get(&arr(get(&j,"answers"))[2],"evidence"))[0]),"value");
    let data=get(proof,"data");let views=arr(get(data,"view_values"));let laws=arr(get(data,"law_values"));
    assert_eq!(get(node(&j,&views[0]),"value").value,get(node(&j,&views[1]),"value").value);
    assert_ne!(get(node(&j,&laws[0]),"value").value,get(node(&j,&laws[1]),"value").value);
    assert_eq!(arr(get(node(&j,&views[0]),"value")).len(),2);
    let mut args=vec!["run","--atom-definition","d.json","--archmap","a.json","--law","l.law","--out","again","--reuse","out","--time-ms","120000"];
    for ask in asks {args.extend(["--ask",ask]);}let reused=run(&dir,&args);assert_eq!(reused.code,1,"{} {}",reused.stdout,reused.stderr);let again=result_json(&dir,&reused);for key in ["answers","nodes"]{assert_eq!(get(&j,key).value,get(&again,key).value);}

}

#[test]
fn rational_tuple_quotient_missing_component_is_not_dropped() {
    let dir=input("rational-tuple-missing","change choose(s:State,a:Q)=s with{x=a};law required first(s:State):s.x=0;view pair(s:State):(Q,(Q,Q))=(s.x,(s.y,rat(1,3)));");
    let path=dir.join("a.json");let old=std::fs::read_to_string(&path).unwrap();let new=old.replace(r#",{"id":"y","subject":"s","field":"Pair.State.y","value":["0","1"],"origin":"model"}"#,"");assert_ne!(new,old);std::fs::write(path,new).unwrap();
    let r=execute(&dir,"out",&["s=solve(Pair.first,on=@v/s,using=Pair.choose)","q=quotient(Pair.pair,on=$s.domain,s=@v/s)"]);assert_eq!(r.code,2,"{} {}",r.stdout,r.stderr);let j=result_json(&dir,&r);let answer=&arr(get(&j,"answers"))[1];assert_eq!(s(get(answer,"status")),"undetermined");assert!(!has(get(answer,"outputs"),"quotient"));assert!(arr(get(answer,"reasons")).iter().any(|r|s(get(r,"code"))=="missing_observation"));
}

#[test]
fn rational_tuple_law_descent_keeps_operand_components_and_counterexample() {
    let dir=input("rational-tuple-law","change choose(s:State,a:Q,b:Q)=s with{x=a,y=b};law required total(s:State):s.x+s.y=1;view combined(s:State):Q=s.x+s.y;view pair(s:State):(Q,Q)=(s.x,s.y);law optional nested(s:State):(s.x,(s.y,rat(1,3)))=(s.x,(s.y,rat(1,3)));");
    let asks=["s=solve(Pair.total,on=@v/s,using=Pair.choose)","good=quotient(Pair.pair,on=$s.domain,s=@v/s,law=Pair.nested)","bad=quotient(Pair.combined,on=$s.domain,s=@v/s,law=Pair.nested)"];
    let r=execute(&dir,"out",&asks);
    assert_eq!(r.code,1,"{} {}",r.stdout,r.stderr);let j=result_json(&dir,&r);assert_eq!(s(get(&arr(get(&j,"answers"))[1],"status")),"established");assert_eq!(s(get(&arr(get(&j,"answers"))[2],"status")),"refuted");
    let q=get(output(&j,1,"quotient"),"value");let descent=get(node(&j,get(q,"descent")),"value");let map=get(node(&j,get(descent,"linear")),"value");let family=get(node(&j,get(map,"target")),"value");assert_eq!(num(get(family,"free_rank")),6);
    let labels=arr(get(family,"generators")).iter().map(|g|s(&arr(get(g,"value"))[1])).collect::<Vec<_>>();assert_eq!(labels,["lhs.0","lhs.1.0","lhs.1.1","rhs.0","rhs.1.0","rhs.1.1"]);
    for (column,expected) in arr(get(map,"columns")).iter().zip([["1","0","0","1","0","0"],["0","1","0","0","1","0"]]) {assert_eq!(arr(column).len(),6);for (r,n) in arr(column).iter().zip(expected){assert_eq!(arr(get(node(&j,r),"value")).iter().map(s).collect::<Vec<_>>(),[n,"1"]);}}
    assert_eq!(arr(get(map,"columns")).len(),2);
    let offsets=qcoordinates(&j,get(descent,"offset"));assert_eq!(offsets.len(),6);for (i,v) in offsets.iter().enumerate(){assert_eq!(v, &if i%3==2{vec!["1".to_owned(),"3".to_owned()]}else{vec!["0".to_owned(),"1".to_owned()]});}
    let proof=get(node(&j,&arr(get(&arr(get(&j,"answers"))[2],"evidence"))[0]),"value");let data=get(proof,"data");let views=arr(get(data,"view_values"));let laws=arr(get(data,"law_values"));assert_eq!(get(node(&j,&views[0]),"value").value,get(node(&j,&views[1]),"value").value);assert_ne!(get(node(&j,&laws[0]),"value").value,get(node(&j,&laws[1]),"value").value);
    let mut args=vec!["run","--atom-definition","d.json","--archmap","a.json","--law","l.law","--out","again","--reuse","out","--time-ms","120000"];for ask in asks{args.extend(["--ask",ask]);}let reuse=run(&dir,&args);assert_eq!(reuse.code,1,"{} {}",reuse.stdout,reuse.stderr);let again=result_json(&dir,&reuse);for key in ["answers","nodes"]{assert_eq!(get(&j,key).value,get(&again,key).value);}

}

#[test]
fn rational_tuple_law_missing_and_empty_keep_the_original_family_type() {
    let body="change choose(s:State,a:Q)=s with{x=a};law required first(s:State):s.x=0;law optional impossible(s:State):s.x=0 and s.x=1;law optional nested(s:State):(s.x,(s.y,rat(1,3)))=(s.x,(s.y,rat(1,3)));";
    let empty=input("tuple-law-empty",body);let r=execute(&empty,"out",&["s=solve(Pair.impossible,on=@v/s,using=Pair.choose)","q=quotient(Pair.x,on=$s.solutions,s=@v/s,law=Pair.nested)"]);assert_eq!(r.code,1,"{} {}",r.stdout,r.stderr);let j=result_json(&empty,&r);let q=get(output(&j,1,"quotient"),"value");assert!(arr(get(get(q,"representation"),"fibers")).is_empty());let d=get(node(&j,get(q,"descent")),"value");assert!(arr(get(d,"pairs")).is_empty());
    let dir=input("tuple-law-missing",body);let path=dir.join("a.json");let old=std::fs::read_to_string(&path).unwrap();let new=old.replace(r#",{"id":"y","subject":"s","field":"Pair.State.y","value":["0","1"],"origin":"model"}"#,"");assert_ne!(new,old);std::fs::write(path,new).unwrap();let r=execute(&dir,"out",&["s=solve(Pair.first,on=@v/s,using=Pair.choose)","q=quotient(Pair.x,on=$s.domain,s=@v/s,law=Pair.nested)"]);assert_eq!(r.code,2,"{} {}",r.stdout,r.stderr);let j=result_json(&dir,&r);let answer=&arr(get(&j,"answers"))[1];assert!(!has(get(answer,"outputs"),"quotient"));assert!(arr(get(answer,"reasons")).iter().any(|r|s(get(r,"code"))=="missing_observation"));
}

#[test]
fn rational_quotient_finite_law_instances_keep_guard_false_keys() {
    let dir=input("rational-finite-law-family","change choose(s:State,a:Q,b:Q)=s with{x=a,y=b};law required total(s:State):s.x+s.y=1;view pair(s:State):(Q,Q)=(s.x,s.y);view combined(s:State):Q=s.x+s.y;law optional indexed(s:State,b:Bool) when b:s.x=s.x;");
    let asks=["s=solve(Pair.total,on=@v/s,using=Pair.choose)","good=quotient(Pair.pair,on=$s.domain,s=@v/s,law=Pair.indexed)","bad=quotient(Pair.combined,on=$s.domain,s=@v/s,law=Pair.indexed)"];
    let r=execute(&dir,"out",&asks);assert_eq!(r.code,1,"{} {}",r.stdout,r.stderr);let j=result_json(&dir,&r);
    let q=get(output(&j,1,"quotient"),"value");let descent=get(node(&j,get(q,"descent")),"value");let map=get(node(&j,get(descent,"linear")),"value");let family=get(node(&j,get(map,"target")),"value");assert_eq!(num(get(family,"free_rank")),2);
    let pattern=&arr(get(get(family,"construction"),"arguments"))[1];let tags=arr(get(node(&j,pattern),"value"));assert_eq!(tags.len(),2);assert!(tags.iter().any(|v|get_bool(&arr(v)[1])==false));assert!(tags.iter().any(|v|get_bool(&arr(v)[1])));
    let answer=&arr(get(&j,"answers"))[2];assert_eq!(s(get(answer,"status")),"refuted");let evidence=get(node(&j,&arr(get(answer,"evidence"))[0]),"value");let data=get(evidence,"data");let values=arr(get(data,"law_values"));for reference in values {let rows=arr(get(node(&j,reference),"value"));assert_eq!(rows.len(),2);assert_eq!(rows.iter().filter(|row|has(&arr(row)[1],"none")).count(),1);assert_eq!(rows.iter().filter(|row|has(&arr(row)[1],"some")).count(),1);}
    let mut args=vec!["run","--atom-definition","d.json","--archmap","a.json","--law","l.law","--out","again","--reuse","out","--time-ms","120000"];for ask in asks{args.extend(["--ask",ask]);}let reuse=run(&dir,&args);assert_eq!(reuse.code,1,"{} {}",reuse.stdout,reuse.stderr);let again=result_json(&dir,&reuse);for key in ["answers","nodes"]{assert_eq!(get(&j,key).value,get(&again,key).value);}

}

fn get_bool(value:&JNode)->bool {if let archsig::json::JValue::Bool(value)=value.value{value}else{panic!("Boolが必要")}}
#[test]
fn rational_quotient_guards_are_restricted_to_the_selected_solution_fiber() {
    let dir=input("rational-fixed-guard","change choose(s:State,a:Q,b:Q)=s with{x=a,y=b};law required total(s:State):s.x+s.y=1;view combined(s:State):Q=s.x+s.y;law optional active(s:State) when s.x+s.y=1:s.x=s.x;law optional inactive(s:State) when s.x+s.y=2:s.x=s.x;");
    let r=execute(&dir,"out",&["s=solve(Pair.total,on=@v/s,using=Pair.choose)","a=quotient(Pair.combined,on=$s.solutions,s=@v/s,law=Pair.active)","b=quotient(Pair.combined,on=$s.solutions,s=@v/s,law=Pair.inactive)"]);assert_eq!(r.code,1,"{} {}",r.stdout,r.stderr);let j=result_json(&dir,&r);assert_eq!(s(get(&arr(get(&j,"answers"))[1],"status")),"refuted");assert_eq!(s(get(&arr(get(&j,"answers"))[2],"status")),"established");
    let q=get(output(&j,2,"quotient"),"value");let descent=get(node(&j,get(q,"descent")),"value");let map=get(node(&j,get(descent,"linear")),"value");let family=get(node(&j,get(map,"target")),"value");assert_eq!(num(get(family,"free_rank")),0);let tags=arr(get(node(&j,&arr(get(get(family,"construction"),"arguments"))[1]),"value"));assert_eq!(tags.len(),1);assert!(!get_bool(&arr(&tags[0])[1]));
}
#[test]
fn rational_quotient_missing_guard_does_not_drop_its_instances() {
    let dir=input("rational-missing-guard","change choose(s:State,a:Q)=s with{x=a};law required first(s:State):s.x=0;law optional guarded(s:State,b:Bool) when s.y>0:s.x=s.x;");let path=dir.join("a.json");let old=std::fs::read_to_string(&path).unwrap();let new=old.replace(r#",{"id":"y","subject":"s","field":"Pair.State.y","value":["0","1"],"origin":"model"}"#,"");assert_ne!(new,old);std::fs::write(path,new).unwrap();let r=execute(&dir,"out",&["s=solve(Pair.first,on=@v/s,using=Pair.choose)","q=quotient(Pair.x,on=$s.domain,s=@v/s,law=Pair.guarded)","n=needed($q)"]);assert_eq!(r.code,2,"{} {}",r.stdout,r.stderr);let j=result_json(&dir,&r);let answer=&arr(get(&j,"answers"))[1];assert!(!has(get(answer,"outputs"),"quotient"));assert!(arr(get(answer,"reasons")).iter().any(|r|s(get(r,"code"))=="missing_observation"));
    let reason=arr(get(answer,"reasons")).iter().find(|r|s(get(r,"code"))=="missing_observation").unwrap();
    let law=std::fs::read_to_string(dir.join("l.law")).unwrap();
    assert!(arr(get(reason,"dependencies")).iter().any(|reference| {
        let expression=get(node(&j,reference),"value");let span=arr(get(get(expression,"location"),"span"));
        &law[num(&span[0]) as usize..num(&span[1]) as usize]=="s.y>0" && arr(get(expression,"parameters")).len()==1
    }));
    let plan=get(output(&j,2,"plan"),"value");
    assert!(arr(get(plan,"requirements")).iter().any(|r|s(get(get(r,"field"),"field"))=="Pair.State.y"));

}

#[test]
fn rational_quotient_unguarded_and_empty_instance_families() {
    let dir=input("rational-unguarded-instances","change choose(s:State,a:Q,b:Q)=s with{x=a,y=b};law required total(s:State):s.x+s.y=1;view pair(s:State):(Q,Q)=(s.x,s.y);law optional indexed(s:State,b:Bool):(if b then s.x else s.y)=0;");
    let r=execute(&dir,"out",&["s=solve(Pair.total,on=@v/s,using=Pair.choose)","good=quotient(Pair.pair,on=$s.domain,s=@v/s,law=Pair.indexed)","bad=quotient(Pair.x,on=$s.domain,s=@v/s,law=Pair.indexed)"]);assert_eq!(r.code,1,"{} {}",r.stdout,r.stderr);let j=result_json(&dir,&r);
    let q=get(output(&j,1,"quotient"),"value");let descent=get(node(&j,get(q,"descent")),"value");let map=get(node(&j,get(descent,"linear")),"value");let family=get(node(&j,get(map,"target")),"value");assert_eq!(num(get(family,"free_rank")),4);
    let bad=&arr(get(&j,"answers"))[2];assert_eq!(s(get(bad,"status")),"refuted");let proof=get(node(&j,&arr(get(bad,"evidence"))[0]),"value");for reference in arr(get(get(proof,"data"),"law_values")){let rows=arr(get(node(&j,reference),"value"));assert_eq!(rows.len(),2);assert!(rows.iter().all(|row|has(&arr(row)[1],"some")));}

    let dir=input("rational-empty-instances","change choose(s:State,a:Q)=s with{x=a};law required first(s:State):s.x=0;law optional empty(s:State,t:Ghost):s.x=s.x;");
    let path=dir.join("d.json");let old=std::fs::read_to_string(&path).unwrap();let before=definition::check_definitions(&[("d",old.as_bytes())]).unwrap();
    let new=old.replace(r#""alignments":[]}]}]}"#,r#""alignments":[]},{"kind":"entity","name":"Pair.Ghost","meaning":"観測個体のない型。","parameters":[],"fields":[],"alignments":[]}]}]}"#);assert_ne!(new,old);
    let after=definition::check_definitions(&[("d",new.as_bytes())]).unwrap();std::fs::write(path,new).unwrap();
    for name in ["a.json","l.law"]{let path=dir.join(name);let text=std::fs::read_to_string(&path).unwrap().replace(&before.vocabularies["Pair"].digest,&after.vocabularies["Pair"].digest);std::fs::write(path,text).unwrap();}
    let r=execute(&dir,"out",&["s=solve(Pair.first,on=@v/s,using=Pair.choose)","q=quotient(Pair.x,on=$s.domain,s=@v/s,law=Pair.empty)"]);assert_eq!(r.code,0,"{} {}",r.stdout,r.stderr);let j=result_json(&dir,&r);let q=get(output(&j,1,"quotient"),"value");let descent=get(node(&j,get(q,"descent")),"value");let map=get(node(&j,get(descent,"linear")),"value");let family=get(node(&j,get(map,"target")),"value");assert_eq!(num(get(family,"free_rank")),0);assert!(arr(get(family,"generators")).is_empty());assert_eq!(arr(get(get(family,"construction"),"arguments")).len(),1);
}

#[test]
fn rational_quotient_composed_fixed_guards_keep_the_selected_domain() {
    for (label,guard) in [("and","(s.x+s.y=1) and b"),("or","(s.x+s.y=2) or b"),("not","not (s.x+s.y!=1) and b"),("let","let fixed=s.x+s.y=1 in fixed and b"),("if","if s.x+s.y=1 then b else false"),("view","fixed(s) and b")] {
        let dir=input(label,&format!("change choose(s:State,a:Q,b:Q)=s with{{x=a,y=b}};law required total(s:State):s.x+s.y=1;view pair(s:State):(Q,Q)=(s.x,s.y);view combined(s:State):Q=s.x+s.y;view fixed(s:State):Bool=s.x+s.y=1;law optional indexed(s:State,b:Bool) when ({guard}):s.x=s.x;"));
        let r=execute(&dir,"out",&["s=solve(Pair.total,on=@v/s,using=Pair.choose)","good=quotient(Pair.pair,on=$s.solutions,s=@v/s,law=Pair.indexed)","bad=quotient(Pair.combined,on=$s.solutions,s=@v/s,law=Pair.indexed)"]);assert_eq!(r.code,1,"{label}: {} {}",r.stdout,r.stderr);let j=result_json(&dir,&r);assert_eq!(s(get(&arr(get(&j,"answers"))[1],"status")),"established");let bad=&arr(get(&j,"answers"))[2];assert_eq!(s(get(bad,"status")),"refuted");let proof=get(node(&j,&arr(get(bad,"evidence"))[0]),"value");for reference in arr(get(get(proof,"data"),"law_values")){let rows=arr(get(node(&j,reference),"value"));assert_eq!(rows.len(),2);assert_eq!(rows.iter().filter(|row|has(&arr(row)[1],"none")).count(),1);assert_eq!(rows.iter().filter(|row|has(&arr(row)[1],"some")).count(),1);}
    }
}

#[test]
fn rational_quotient_varying_guard_is_not_fixed_by_an_arbitrary_assignment() {
    let dir=input("rational-varying-guard","change choose(s:State,a:Q,b:Q)=s with{x=a,y=b};law required total(s:State):s.x+s.y=1;law optional indexed(s:State,b:Bool) when (s.x+s.y=1) and b:s.x=s.x;");
    let r=execute(&dir,"out",&["s=solve(Pair.total,on=@v/s,using=Pair.choose)","q=quotient(Pair.x,on=$s.domain,s=@v/s,law=Pair.indexed)"]);assert_eq!(r.code,70,"{} {}",r.stdout,r.stderr);assert!(arr(get(&r.receipt,"issues")).iter().any(|issue| has(get(issue,"details"),"operation") && s(get(get(issue,"details"),"operation")).contains("商の候補域で変化するLaw guard")));let j=result_json(&dir,&r);assert!(!has(get(&arr(get(&j,"answers"))[1],"outputs"),"quotient"));
}

#[test]
fn rational_local_system_keeps_exact_equation_and_semantic_fibers() {
    let dir=input("rational-local","change choose(s:State,a:Q,b:Q)=s with{x=rat(1,2)*a,y=b};law required total(s:State):s.x+s.y=1;");
    let asks=["a=build(Pair,on=@v/s)","l=localize($a.object,using=Pair.choose)","e=diagnose($l.system)","m=diagnose($l.system,side=semantic)","z=diagnose($l.system,degree=0)"];
    let r=execute(&dir,"out",&asks);assert_eq!(r.code,0,"{} {}",r.stdout,r.stderr);let j=result_json(&dir,&r);
    for i in [2,3,4] {let space=get(output(&j,i,"space"),"value");let module=get(node(&j,get(space,"module")),"value");let ring=get(node(&j,get(module,"ring")),"value");assert_eq!(s(get(ring,"scalar")),"Q");assert!(arr(get(module,"torsion")).is_empty());assert_eq!(num(get(module,"free_rank")),if i==4{1}else{0});}
    assert!(!has(get(&arr(get(&j,"answers"))[4],"outputs"),"class"));
    let mut args=vec!["run","--atom-definition","d.json","--archmap","a.json","--law","l.law","--out","again","--reuse","out","--time-ms","120000"];for ask in asks {args.extend(["--ask",ask]);}let reuse=run(&dir,&args);assert_eq!(reuse.code,0,"{} {}",reuse.stdout,reuse.stderr);let again=result_json(&dir,&reuse);for key in ["answers","nodes"]{assert_eq!(get(&j,key).value,get(&again,key).value);}
}
#[path="common/three_edge.rs"] mod rational_triangle_source;
fn rational_triangle(name:&str,gamma:Option<i64>)->std::path::PathBuf {
    let original=rational_triangle_source::input(gamma);
    let before=std::str::from_utf8(original.definitions()[0].bytes()).unwrap();
    let d=before.replace("\"type\":\"Z\"","\"type\":\"Q\"");
    let old=definition::check_definitions(&[("d",before.as_bytes())]).unwrap();
    let new=definition::check_definitions(&[("d",d.as_bytes())]).unwrap();
    let digest=&old.vocabularies["Coordinates"].digest;
    let new_digest=&new.vocabularies["Coordinates"].digest;
    let law=std::str::from_utf8(original.law().bytes()).unwrap().replace(digest,new_digest).replace("d:Z","d:Q");
    let mut map=std::str::from_utf8(original.archmap().bytes()).unwrap().replace(digest,new_digest);
    for (n,q) in [("0",r#"["0","1"]"#),("1",r#"["1","2"]"#),("2",r#"["1","1"]"#),("3",r#"["3","2"]"#)] {
        map=map.replace(&format!(r#""value":"{n}""#),&format!(r#""value":{q}"#));
    }
    let dir=workdir(name);
    for (name,text) in [("d.json",d),("l.law",law),("a.json",map)]{std::fs::write(dir.join(name),text).unwrap();}
    dir
}
#[test]
fn rational_local_triangle_distinguishes_gluing_obstruction_and_missing() {
    for gamma in [Some(2),Some(3),None] {
        let dir=rational_triangle(&format!("rational-triangle-{gamma:?}"),gamma);
        let asks=["a=build(Coordinates,on=@triangle/root)","l=localize($a.object,using=Coordinates.move)","d=diagnose($l.system)","s=diagnose($l.system,side=semantic)","n=needed($d)"];
        let r=execute(&dir,"out",&asks);assert_eq!(r.code,match gamma{Some(2)=>0,Some(3)=>1,_=>2},"{} {}",r.stdout,r.stderr);
        let j=result_json(&dir,&r);
        for i in [2,3] {
            let answer=&arr(get(&j,"answers"))[i];
            assert_eq!(s(get(answer,"status")),match gamma{Some(2)=>"established",Some(3)=>"refuted",_=>"undetermined"});
            let space=get(output(&j,i,"space"),"value");let module=get(node(&j,get(space,"module")),"value");
            assert_eq!(num(get(module,"free_rank")),1);assert!(arr(get(module,"torsion")).is_empty());
            assert_eq!(s(get(get(node(&j,get(module,"ring")),"value"),"scalar")),"Q");
            if gamma.is_none(){assert!(!has(get(answer,"outputs"),"class"));continue;}
            let class=get(output(&j,i,"class"),"value");let coordinates=qcoordinates(&j,get(class,"coordinates"));assert_eq!(coordinates.len(),1);
            if gamma==Some(2){
                assert_eq!(coordinates[0],vec!["0","1"]);
                let proof=arr(get(answer,"evidence")).iter().map(|r|get(node(&j,r),"value")).find(|e|s(get(e,"kind"))=="gluing").unwrap();
                let data=get(proof,"data");assert_eq!(arr(get(data,"rechecks")).len(),3);
                for check in arr(get(data,"rechecks")){assert_eq!(s(get(get(node(&j,check),"judgment"),"status")),"established");}
            }else{
                assert_ne!(coordinates[0][0],"0");
                let proof=arr(get(answer,"evidence")).iter().map(|r|get(node(&j,r),"value")).find(|e|s(get(e,"kind"))=="linear_inconsistent").unwrap();
                let pairing=arr(get(node(&j,get(get(proof,"data"),"pairing")),"value"));assert_ne!(s(&pairing[0]),"0");
            }
        }
        if gamma.is_none(){let plan=get(output(&j,4,"plan"),"value");assert!(arr(get(plan,"requirements")).iter().any(|r|{let f=get(r,"field");s(get(f,"field"))=="Coordinates.Shift.shift"&&s(get(f,"subject"))=="c"}));}
        assert!(!arr(get(&j,"nodes")).iter().any(|n|has(n,"construction")&&s(get(n,"construction"))=="evidence"&&s(get(get(n,"value"),"kind"))=="smith"));
    }
}
#[test]
fn rational_local_equations_do_not_expand_the_change_image() {
    let dir=input("rational-local-image","change choose(s:State,a:Q)=s with{x=a,y=0};law required total(s:State):s.x+s.y=1;");
    let asks=["a=build(Pair,on=@v/s)","l=localize($a.object,using=Pair.choose)","e=diagnose($l.system,degree=0)","m=diagnose($l.system,degree=0,side=semantic)"];
    let r=execute(&dir,"out",&asks);assert_eq!(r.code,0,"{} {}",r.stdout,r.stderr);let j=result_json(&dir,&r);
    for (i,rank) in [(2,1),(3,0)]{let space=get(output(&j,i,"space"),"value");let module=get(node(&j,get(space,"module")),"value");assert_eq!(num(get(module,"free_rank")),rank);}
}
