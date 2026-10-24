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
