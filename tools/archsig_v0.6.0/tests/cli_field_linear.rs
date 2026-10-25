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
        assert_eq!(r.code, 2, "{} {}", r.stdout, r.stderr);
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
}
