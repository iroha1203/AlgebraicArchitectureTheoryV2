//! 整数全解、元Assignmentの非一意・一意、修復後の通常評価。
#[allow(dead_code)]
#[path = "common/cli.rs"]
mod cli;
#[allow(dead_code)]
#[path = "common/object_view_compatibility_data.rs"]
mod local_fixture;
use archsig::{definition, json::JNode};
use cli::*;
const D: &str = r#"{"format":"archsig.atom-definition/1","semantics":"archsig/0.6.0","vocabularies":[{"semantics":"archsig/0.6.0","namespace":"Pair","version":"1","dependencies":[],"declarations":[{"kind":"entity","name":"Pair.State","meaning":"整数対。","parameters":[],"fields":[{"name":"x","type":"Z","meaning":"第一座標。"},{"name":"y","type":"Z","meaning":"第二座標。"}],"alignments":[]}]}]}"#;
fn input(name: &str, change: &str) -> std::path::PathBuf {
    let d = definition::check_definitions(&[("d", D.as_bytes())]).unwrap();
    let digest = &d.vocabularies["Pair"].digest;
    let a=r#"{"format":"archsig.archmap/2","semantics":"archsig/0.6.0","vocabularies":[{"namespace":"Pair","version":"1","digest":"@D@"}],"sources":[],"origins":[{"id":"model","mode":"specification","method":"整数対の独立試験。","locations":[],"note":"全整数の修復。"}],"snapshots":[{"id":"pair","origin":"model","subjects":[{"id":"s","type":"Pair.State","origin":"model"}],"atoms":[{"id":"x","subject":"s","field":"Pair.State.x","value":"0","origin":"model"},{"id":"y","subject":"s","field":"Pair.State.y","value":"0","origin":"model"}]}]}"#.replace("@D@",digest);
    let law = format!(
        "law \"archsig.law/2\" semantics \"archsig/0.6.0\"; reading Pair {{use vocabulary Pair version \"1\" digest \"{digest}\"; {change} law required total(s:State):s.x+s.y=1;law optional pinned(s:State):s.x+s.y=1 and s.x=0;view first(s:State):Z=s.x;}}"
    );
    let dir = workdir(name);
    for (name, content) in [
        ("d.json", D),
        ("a.json", a.as_str()),
        ("l.law", law.as_str()),
    ] {
        std::fs::write(dir.join(name), content).unwrap();
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
fn node<'a>(result: &'a JNode, reference: &JNode) -> &'a JNode {
    arr(get(result, "nodes"))
        .iter()
        .find(|n| s(get(n, "id")) == s(get(reference, "node")))
        .unwrap()
}
fn output<'a>(result: &'a JNode, index: usize, key: &str) -> &'a JNode {
    node(
        result,
        get(get(&arr(get(result, "answers"))[index], "outputs"), key),
    )
}
#[test]
fn integer_total_and_pinned_keep_full_fibers_and_only_unique_repair_objects() {
    let dir = input(
        "integer-pair",
        "change setpair(s:State,a:Z,b:Z)=s with{x=a,y=b};",
    );
    let r = execute(
        &dir,
        "total",
        &["r=repair(Pair.total,using=Pair.setpair,on=@pair/s,s=@pair/s)"],
    );
    assert_eq!(r.code, 1, "{} {}", r.stdout, r.stderr);
    let total = result_json(&dir, &r);
    assert_module_owners(&total);
    let answers = arr(get(&total, "answers"));
    assert!(!has(get(&answers[0], "outputs"), "object"));
    let representation = get(
        get(output(&total, 0, "solutions"), "value"),
        "representation",
    );
    assert_eq!(s(get(representation, "kind")), "affine");
    let directions = node(&total, get(representation, "directions"));
    assert_eq!(num(get(get(directions, "value"), "free_rank")), 1);
    assert_eq!(
        s(get(
            get(output(&total, 0, "existence"), "judgment"),
            "status"
        )),
        "established"
    );
    let r = execute(
        &dir,
        "blocked",
        &[
            "r=repair(Pair.total,using=Pair.setpair,on=@pair/s,s=@pair/s)",
            "x=evaluate(Pair.first,on=$r.object,s=@pair/s)",
        ],
    );
    assert_eq!(r.code, 2, "{} {}", r.stdout, r.stderr);
    let r = execute(
        &dir,
        "pinned",
        &[
            "r=repair(Pair.pinned,using=Pair.setpair,on=@pair/s,s=@pair/s)",
            "x=evaluate(Pair.first,on=$r.object,s=@pair/s)",
            "c=check(Pair.pinned,on=$r.object,s=@pair/s)",
        ],
    );
    assert_eq!(r.code, 0, "{} {}", r.stdout, r.stderr);
    let pinned = result_json(&dir, &r);
    assert_module_owners(&pinned);
    assert_eq!(s(get(output(&pinned, 1, "value"), "value")), "0");
    let representation = get(
        get(output(&pinned, 0, "solutions"), "value"),
        "representation",
    );
    let directions = node(&pinned, get(representation, "directions"));
    assert_eq!(num(get(get(directions, "value"), "free_rank")), 0);
    assert!(
        arr(get(&pinned, "answers"))
            .iter()
            .all(|a| s(get(a, "status")) == "established")
    );
}
#[test]
fn integer_obstruction_and_same_effect_assignments_are_not_rational_or_unique_repairs() {
    let dir = input(
        "integer-even",
        "change setpair(s:State,a:Z,b:Z)=s with{x=2*a,y=2*b};",
    );
    let r = execute(
        &dir,
        "out",
        &["r=repair(Pair.total,using=Pair.setpair,on=@pair/s,s=@pair/s)"],
    );
    assert_eq!(r.code, 1, "{} {}", r.stdout, r.stderr);
    let empty = result_json(&dir, &r);
    assert_eq!(
        s(get(
            get(
                get(output(&empty, 0, "solutions"), "value"),
                "representation"
            ),
            "kind"
        )),
        "empty"
    );
    assert_eq!(
        s(get(
            get(output(&empty, 0, "existence"), "judgment"),
            "status"
        )),
        "refuted"
    );
    let dir = input(
        "integer-same-effect",
        "change setpair(s:State,a:Z,b:Z)=s with{x=0,y=1};",
    );
    let r = execute(
        &dir,
        "out",
        &["r=repair(Pair.pinned,using=Pair.setpair,on=@pair/s,s=@pair/s)"],
    );
    assert_eq!(r.code, 1, "{} {}", r.stdout, r.stderr);
    let nonunique = result_json(&dir, &r);
    assert!(!has(
        get(&arr(get(&nonunique, "answers"))[0], "outputs"),
        "object"
    ));
    let representation = get(
        get(output(&nonunique, 0, "solutions"), "value"),
        "representation",
    );
    assert_eq!(
        num(get(
            get(node(&nonunique, get(representation, "directions")), "value"),
            "free_rank"
        )),
        2
    );
}

#[test]
fn integer_repair_reuse_rechecks_the_same_full_solution() {
    let dir = input(
        "integer-reuse",
        "change setpair(s:State,a:Z,b:Z)=s with{x=a,y=b};",
    );
    let asks = [
        "r=repair(Pair.pinned,using=Pair.setpair,on=@pair/s,s=@pair/s)",
        "x=evaluate(Pair.first,on=$r.object,s=@pair/s)",
    ];
    let first = execute(&dir, "out", &asks);
    assert_eq!(first.code, 0, "{}", first.stdout);
    let original = result_json(&dir, &first);
    let repeated = run(
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
            "out2",
            "--reuse",
            "out",
            "--time-ms",
            "120000",
            "--ask",
            asks[0],
            "--ask",
            asks[1],
        ],
    );
    assert_eq!(repeated.code, 0, "{}", repeated.stdout);
    let result = result_json(&dir, &repeated);
    assert_eq!(
        get(get(&result, "reuse"), "requested").value,
        archsig::json::JValue::Bool(true)
    );
    for field in ["answers", "nodes"] {
        assert_eq!(get(&result, field).value, get(&original, field).value);
    }
}

#[test]
fn integer_local_instances_have_independent_parameter_axes() {
    let dir = workdir("integer-local");
    let definitions = local_fixture::D;
    let d = definition::check_definitions(&[("d", definitions.as_bytes())]).unwrap();
    let digest = &d.vocabularies["Pattern"].digest;
    let map=local_fixture::A.replace("@DIGEST@",digest)
        .replace(r#"{"id":"p","type":"Pattern.Part","origin":"model"}"#,r#"{"id":"p","type":"Pattern.Part","origin":"model"},{"id":"q","type":"Pattern.Part","origin":"model"}"#)
        .replace(r#"{"id":"quantity-p","subject":"p","field":"Pattern.Part.quantity","value":"2","origin":"model"}"#,r#"{"id":"quantity-p","subject":"p","field":"Pattern.Part.quantity","value":"2","origin":"model"},{"id":"owner-q","subject":"q","field":"Pattern.Part.owner","value":["v","root"],"origin":"model"},{"id":"quantity-q","subject":"q","field":"Pattern.Part.quantity","value":"5","origin":"model"}"#);
    let law = format!(
        "law \"archsig.law/2\" semantics \"archsig/0.6.0\";reading Selected{{use vocabulary Pattern version \"1\" digest \"{digest}\";change choose(c:Part,a:Z)=c with{{quantity=a}};law required valid(c:Part):c.quantity=3;view quantity(c:Part):Z=c.quantity;}}"
    );
    for (name, content) in [
        ("d.json", definitions),
        ("a.json", map.as_str()),
        ("l.law", law.as_str()),
    ] {
        std::fs::write(dir.join(name), content).unwrap();
    }
    let r = execute(
        &dir,
        "out",
        &[
            "r=repair(Selected.valid,using=Selected.choose,on=@v/root)",
            "p=evaluate(Selected.quantity,on=$r.object,c=@v/p)",
            "q=evaluate(Selected.quantity,on=$r.object,c=@v/q)",
        ],
    );
    assert_eq!(r.code, 0, "{} {}", r.stdout, r.stderr);
    let result = result_json(&dir, &r);
    for index in [1, 2] {
        assert_eq!(s(get(output(&result, index, "value"), "value")), "3");
    }
    let representation = get(
        get(output(&result, 0, "solutions"), "value"),
        "representation",
    );
    let particular = node(&result, get(representation, "particular"));
    assert_eq!(arr(get(get(particular, "value"), "coordinates")).len(), 2);
}

#[test]
fn nonlinear_change_is_not_misreported_as_an_integer_affine_solution() {
    let dir = input(
        "integer-nonlinear",
        "change setpair(s:State,a:Z,b:Z)=s with{x=a*a,y=b};",
    );
    let r = execute(
        &dir,
        "out",
        &["s=solve(Pair.total,using=Pair.setpair,on=@pair/s,s=@pair/s)"],
    );
    assert_eq!(r.code, 70, "{} {}", r.stdout, r.stderr);
}

#[test]
fn repeated_integer_repair_uses_the_previous_state_in_its_affine_offset() {
    let dir = input(
        "integer-repeat",
        "change setpair(s:State,a:Z,b:Z)=s with{x=s.x+a,y=s.y+b};",
    );
    let law = std::fs::read_to_string(dir.join("l.law")).unwrap().replace(
        "view first",
        "law optional shifted(s:State):s.x+s.y=3 and s.x=2;view first",
    );
    std::fs::write(dir.join("l.law"), law).unwrap();
    let r = execute(
        &dir,
        "out",
        &[
            "a=repair(Pair.pinned,using=Pair.setpair,on=@pair/s,s=@pair/s)",
            "b=repair(Pair.shifted,using=Pair.setpair,on=$a.object,s=@pair/s)",
            "x=evaluate(Pair.first,on=$b.object,s=@pair/s)",
        ],
    );
    assert_eq!(r.code, 0, "{} {}", r.stdout, r.stderr);
    let result = result_json(&dir, &r);
    assert_eq!(s(get(output(&result, 2, "value"), "value")), "2");
    let repair = get(output(&result, 1, "repair"), "value");
    let assignment = get(node(&result, get(repair, "parameters")), "value");
    let parameters = arr(get(&arr(get(assignment, "entries"))[0], "parameters"));
    assert_eq!(s(get(node(&result, &parameters[0]), "value")), "2");
    assert_eq!(s(get(node(&result, &parameters[1]), "value")), "0");
}

fn assert_module_owners(result: &JNode) {
    let mut maps = 0;
    let mut vectors = 0;
    for n in arr(get(result, "nodes")) {
        if !has(n, "value") { continue; }
        let value = get(n, "value");
        let fields: &[&str] = if has(value, "columns") && has(value, "source") {
            maps += 1;
            &["source", "target"]
        } else if has(value, "coordinates") && has(value, "module") {
            vectors += 1;
            &["module"]
        } else { continue; };
        let ty = arr(get(n, "type"));
        assert_eq!(s(&ty[0]), if fields.len() == 2 { "ModuleMap" } else { "Vector" });
        assert_eq!(ty.len(), fields.len() + 1);
        for (i, field) in fields.iter().enumerate() {
            assert_eq!(s(get(&ty[i + 1], "node")), s(get(get(value, field), "node")));
            assert_eq!(s(get(node(result, &ty[i + 1]), "type")), "Module");
        }
    }
    assert!(maps > 0 && vectors > 0);
}

#[test]
fn integer_repair_stop_after_first_witness_keeps_existence_without_object() {
    use archsig::observed::{control::{Checkpoint, Control, Limits, Usage},
        input::InputSources, evaluate::evaluate_observed_bytes};
    use std::{cell::Cell, rc::Rc};
    let dir = input("integer-stop", "change setpair(s:State,a:Z,b:Z)=s with{x=a,y=b};");
    for mode in 0..3 {
        let seen = Rc::new(Cell::new(0));
        let count = seen.clone();
        let mut c = Control::new(Limits {time_ms: Some(1), memory_mib: Some(1)}, move |point| {
            if point == Checkpoint::ChangeWitness { count.set(count.get() + 1); }
            if count.get() == 2 {
                match mode {
                    0 => Usage {elapsed_ms: 2, ..Usage::default()},
                    1 => Usage {memory_mib: 2, ..Usage::default()},
                    _ => Usage {signal: Some(archsig::result::Signal::Term), ..Usage::default()},
                }
            } else { Usage::default() }
        });
        let source = InputSources::from_bytes(vec![std::fs::read(dir.join("d.json")).unwrap()],
            std::fs::read(dir.join("l.law")).unwrap(),std::fs::read(dir.join("a.json")).unwrap());
        let result = evaluate_observed_bytes(source, &[
            "r=repair(Pair.total,using=Pair.setpair,on=@pair/s,s=@pair/s)",
            "later=check(Pair.total,s=@pair/s)"], &mut c).unwrap();
        assert_eq!(seen.get(), 2);
        let wire = archsig::json::parse(result.wire().canonical().as_bytes()).unwrap();
        let answers = arr(get(&wire, "answers"));
        let first = &answers[0];
        assert_eq!(s(get(first,"status")), "undetermined");
        assert!(!has(get(first,"outputs"), "object"));
        assert!(!has(get(first,"outputs"), "repair"));
        assert!(!has(get(first,"outputs"), "proposition"));
        assert_eq!(s(get(get(output(&wire,0,"existence"),"judgment"),"status")), "established");
        assert_eq!(s(get(&answers[1],"status")), "undetermined");
        let code = if mode == 2 {"cancelled"} else {"budget_exhausted"};
        for answer in answers {
            assert!(arr(get(answer,"reasons")).iter().any(|r| s(get(r,"code")) == code));
        }
    }
}

fn coordinates(result: &JNode, vector: &JNode) -> Vec<i64> {
    arr(get(get(node(result, vector), "value"), "coordinates"))
        .iter()
        .map(|r| s(get(node(result, r), "value")).parse().unwrap())
        .collect()
}
#[test]
fn integer_guard_restores_original_parameters_for_solve_repair_and_followup() {
    for (name, guard, expected) in [
        ("guard-zero", "a=0 and b=1", vec![0, 1]),
        ("guard-nonunit", "2*a-3*b=2", vec![1, 0]),
    ] {
        let dir = input(
            name,
            &format!("change setpair(s:State,a:Z,b:Z) when {guard}=s with{{x=a,y=b}};"),
        );
        let run = execute(
            &dir,
            "out",
            &[
                "s=solve(Pair.total,using=Pair.setpair,on=@pair/s,s=@pair/s)",
                "r=repair(Pair.total,using=Pair.setpair,on=@pair/s,s=@pair/s)",
                "x=evaluate(Pair.first,on=$r.object,s=@pair/s)",
                "c=check(Pair.total,on=$r.object,s=@pair/s)",
            ],
        );
        assert_eq!(run.code, 0, "{} {}", run.stdout, run.stderr);
        let result = result_json(&dir, &run);
        assert_module_owners(&result);
        for index in [0, 1] {
            let rep = get(
                get(output(&result, index, "solutions"), "value"),
                "representation",
            );
            assert_eq!(coordinates(&result, get(rep, "particular")), expected);
            let directions = node(&result, get(rep, "directions"));
            assert_eq!(num(get(get(directions, "value"), "free_rank")), 0);
        }
        assert_eq!(
            s(get(output(&result, 2, "value"), "value")),
            expected[0].to_string()
        );
        assert!(
            arr(get(&result, "answers"))
                .iter()
                .all(|a| s(get(a, "status")) == "established")
        );
    }
}
#[test]
fn integer_guard_keeps_original_free_direction_and_rejects_empty_integer_fiber() {
    let dir = input(
        "guard-free",
        "change setpair(s:State,a:Z,b:Z) when a+b=1=s with{x=0,y=1};",
    );
    let run = execute(
        &dir,
        "out",
        &["r=repair(Pair.total,using=Pair.setpair,on=@pair/s,s=@pair/s)"],
    );
    assert_eq!(run.code, 1, "{} {}", run.stdout, run.stderr);
    let result = result_json(&dir, &run);
    assert!(!has(
        get(&arr(get(&result, "answers"))[0], "outputs"),
        "object"
    ));
    let rep = get(
        get(output(&result, 0, "solutions"), "value"),
        "representation",
    );
    let p = coordinates(&result, get(rep, "particular"));
    assert_eq!(p.len(), 2);
    assert_eq!(p.iter().sum::<i64>(), 1);
    let embedding = node(&result, get(rep, "embedding"));
    let cols = arr(get(get(embedding, "value"), "columns"));
    assert_eq!(cols.len(), 1);
    let k = arr(&cols[0])
        .iter()
        .map(|r| s(get(node(&result, r), "value")).parse::<i64>().unwrap())
        .collect::<Vec<_>>();
    assert_eq!(k.len(), 2);
    assert_eq!(k.iter().sum::<i64>(), 0);
    assert!(k.iter().any(|x| *x != 0));
    let dir = input(
        "guard-empty",
        "change setpair(s:State,a:Z,b:Z) when 2*a=1=s with{x=a,y=b};",
    );
    let run = execute(
        &dir,
        "out",
        &["s=solve(Pair.total,using=Pair.setpair,on=@pair/s,s=@pair/s)"],
    );
    assert_eq!(run.code, 1, "{} {}", run.stdout, run.stderr);
    let result = result_json(&dir, &run);
    assert_eq!(
        s(get(
            get(
                get(output(&result, 0, "solutions"), "value"),
                "representation"
            ),
            "kind"
        )),
        "empty"
    );
}

#[test]
fn guarded_integer_repair_reuse_preserves_restored_solution_and_followup() {
    let dir = input("guard-reuse", "change setpair(s:State,a:Z,b:Z) when 2*a-3*b=2=s with{x=a,y=b};");
    let asks = ["r=repair(Pair.total,using=Pair.setpair,on=@pair/s,s=@pair/s)",
        "x=evaluate(Pair.first,on=$r.object,s=@pair/s)"];
    let first = execute(&dir, "out", &asks);
    assert_eq!(first.code, 0, "{} {}", first.stdout, first.stderr);
    let original = result_json(&dir, &first);
    let repeated = run(&dir, &["run", "--atom-definition", "d.json", "--archmap", "a.json",
        "--law", "l.law", "--out", "out2", "--reuse", "out", "--time-ms", "120000",
        "--ask", asks[0], "--ask", asks[1]]);
    assert_eq!(repeated.code, 0, "{} {}", repeated.stdout, repeated.stderr);
    let reused = result_json(&dir, &repeated);
    for field in ["answers", "nodes"] { assert_eq!(get(&original, field).value, get(&reused, field).value); }
}
