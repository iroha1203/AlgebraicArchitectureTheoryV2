//! 整数全解、元Assignmentの非一意・一意、修復後の通常評価。
use crate::common::cli;
use crate::common::helpers::execute;
use crate::common::object_view_compatibility_data as local_fixture;
use archsig::{definition, json::JNode};
use cli::*;
const D: &str = r#"{"format":"archsig.atom-definition/1","semantics":"archsig/0.6.0","vocabularies":[{"semantics":"archsig/0.6.0","namespace":"Pair","version":"1","dependencies":[],"declarations":[{"kind":"entity","name":"Pair.State","meaning":"整数対。","parameters":[],"fields":[{"name":"x","type":"Z","meaning":"第一座標。"},{"name":"y","type":"Z","meaning":"第二座標。"}],"alignments":[]}]}]}"#;
fn input(name: &str, change: &str) -> std::path::PathBuf {
    let d = definition::check_definitions(&[("d", D.as_bytes())]).unwrap();
    let digest = &d.vocabularies()["Pair"].digest;
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
fn parameter_product_repairs_keep_full_quantifiers_and_original_assignments() {
    for (label, change, parameter, predicate) in [
        (
            "direct",
            "change setpair(s:State,a:Z)=s with{x=a,y=0};",
            "z",
            "z*(s.x+s.y)=z",
        ),
        (
            "let",
            "change setpair(s:State,a:Z)=s with{x=a,y=0};",
            "z",
            "let k=z in k*(s.x+s.y)=z",
        ),
        (
            "let-and",
            "change setpair(s:State,a:Z)=s with{x=a,y=0};",
            "z",
            "let k=s.x in z*k=z and s.y=0",
        ),
        (
            "helper-and",
            "change setpair(s:State,a:Z)=s with{x=a,y=0};view valid(k:Z,t:State):Bool=let q=t.x in k*q=k and t.y=0;",
            "z",
            "valid(z,s)",
        ),
        (
            "let-and-reference",
            "change setpair(s:State,a:Z)=s with{x=a,y=0};",
            "z",
            "let k=s.x in z*k=z and s=s",
        ),
        (
            "helper",
            "change setpair(s:State,a:Z)=s with{x=a,y=0};view scaled(k:Z,t:State):Z=k*(t.x+t.y);",
            "z",
            "scaled(z,s)=z",
        ),
        (
            "same-name",
            "change setpair(s:State,a:Z)=s with{x=a,y=0};",
            "a",
            "a*(s.x+s.y)=a",
        ),
        (
            "finite",
            "change setpair(s:State,b:Bool)=s with{x=if b then 1 else 0,y=0};",
            "z",
            "z*(s.x+s.y)=z",
        ),
    ] {
        let dir = product_input(label, change, &format!("{parameter}:Z,"), predicate, false);
        let asks = [
            "a=solve(Pair.total,using=Pair.setpair,on=@pair/s)",
            "r=repair(Pair.total,using=Pair.setpair,on=@pair/s)",
            "x=evaluate(Pair.first,on=$r.object,s=@pair/s)",
            "c=check(Pair.total,on=$r.object)",
        ];
        let result = execute(&dir, "out", &asks);
        assert_eq!(result.code, 0, "{label}: {}", result.stdout);
        let j = result_json(&dir, &result);
        assert_eq!(s(get(output(&j, 2, "value"), "value")), "1");
        let scope = get(&arr(get(&j, "answers"))[0], "scope");
        assert!(
            arr(get(scope, "quantifiers"))
                .iter()
                .any(|q| s(get(q, "name")) == parameter
                    && s(get(q, "kind")) == "forall"
                    && !has(q, "domain"))
        );
    }
}
#[test]
fn parameter_product_explicit_forall_repairs_keep_binder_scope() {
    for (label, helper, predicate) in [
        ("forall", "", "forall z:Z. z*(s.x+s.y)=z"),
        ("forall-let", "", "let k=s.x in forall z:Z. z*k=z and s.y=0"),
        (
            "forall-helper",
            "view valid(t:State):Bool=forall z:Z. z*(t.x+t.y)=z;",
            "valid(s)",
        ),
        ("forall-two", "", "forall z:Z. forall w:Z. z*s.x+w*s.y=z"),
        (
            "forall-sibling",
            "",
            "(forall z:Z. z*(s.x+s.y)=z) and (forall w:Z. w*s.y=0)",
        ),
    ] {
        let change = format!("change setpair(s:State,a:Z)=s with{{x=a,y=0}};{helper}");
        let dir = product_input(label, &change, "", predicate, false);
        let asks = [
            "a=solve(Pair.total,using=Pair.setpair,on=@pair/s)",
            "r=repair(Pair.total,using=Pair.setpair,on=@pair/s)",
            "x=evaluate(Pair.first,on=$r.object,s=@pair/s)",
            "c=check(Pair.total,on=$r.object)",
        ];
        let result = execute(&dir, "out", &asks);
        assert_eq!(result.code, 0, "{label}: {}", result.stdout);
        let j = result_json(&dir, &result);
        assert_eq!(s(get(output(&j, 2, "value"), "value")), "1");
        assert!(
            arr(get(&j, "answers"))
                .iter()
                .all(|a| s(get(a, "status")) == "established")
        );
    }
}
fn product_input(
    name: &str,
    change: &str,
    parameters: &str,
    predicate: &str,
    missing: bool,
) -> std::path::PathBuf {
    let dir = input(&format!("parameter-product-{name}"), change);
    let path = dir.join("l.law");
    let law = std::fs::read_to_string(&path).unwrap().replace(
        "total(s:State):s.x+s.y=1",
        &format!("total({parameters}s:State):{predicate}"),
    );
    std::fs::write(path, law).unwrap();
    if missing {
        let map = std::fs::read_to_string(dir.join("a.json"))
            .unwrap()
            .replace(
                r#",{"id":"y","subject":"s","field":"Pair.State.y","value":"0","origin":"model"}"#,
                "",
            );
        std::fs::write(dir.join("a.json"), map).unwrap();
    }
    dir
}
#[test]
fn parameter_product_coefficients_keep_nonunique_integer_repairs() {
    for (label, change) in [
        (
            "nonunique",
            "change setpair(s:State,a:Z,b:Z)=s with{x=a,y=b};",
        ),
        (
            "same-state",
            "change setpair(s:State,a:Z,b:Z)=s with{x=a,y=0};",
        ),
    ] {
        let dir = product_input(label, change, "z:Z,", "z*(s.x+s.y)=z", false);
        let asks = ["r=repair(Pair.total,using=Pair.setpair,on=@pair/s)"];
        let result = execute(&dir, "out", &asks);
        assert_eq!(result.code, 1, "{}", result.stdout);
        let j = result_json(&dir, &result);
        assert!(!has(get(&arr(get(&j, "answers"))[0], "outputs"), "object"));
        assert_eq!(
            s(get(get(output(&j, 0, "existence"), "judgment"), "status")),
            "established"
        );
        let representation = get(get(output(&j, 0, "solutions"), "value"), "representation");
        assert_eq!(s(get(representation, "kind")), "affine");
        assert_eq!(
            num(get(
                get(node(&j, get(representation, "directions")), "value"),
                "free_rank"
            )),
            1
        );
    }
}
#[test]
fn parameter_product_coefficients_keep_independent_universal_axes() {
    for (label, parameters, predicate) in [
        ("two-axes", "z:Z,w:Z,", "z*s.x+w*s.y=z+2*w"),
        (
            "two-explicit-axes",
            "",
            "forall z:Z. forall w:Z. z*s.x+w*s.y=z+2*w",
        ),
        ("mixed-axes", "z:Z,", "forall w:Z. z*s.x+w*s.y=z+2*w"),
    ] {
        let dir = product_input(
            label,
            "change setpair(s:State,a:Z,b:Z)=s with{x=a,y=b};view second(s:State):Z=s.y;",
            parameters,
            predicate,
            false,
        );
        let asks = [
            "r=repair(Pair.total,using=Pair.setpair,on=@pair/s)",
            "x=evaluate(Pair.first,on=$r.object,s=@pair/s)",
            "y=evaluate(Pair.second,on=$r.object,s=@pair/s)",
            "c=check(Pair.total,on=$r.object)",
        ];
        let result = execute(&dir, "out", &asks);
        assert_eq!(result.code, 0, "{}", result.stdout);
        let j = result_json(&dir, &result);
        assert_eq!(s(get(output(&j, 1, "value"), "value")), "1");
        assert_eq!(s(get(output(&j, 2, "value"), "value")), "2");
    }
}
#[test]
fn parameter_product_missing_unmodified_field_is_not_zero() {
    for (label, change, code) in [
        (
            "reset-missing",
            "change setpair(s:State,a:Z)=s with{x=a,y=0};",
            0,
        ),
        (
            "keep-missing",
            "change setpair(s:State,a:Z)=s with{x=a};",
            2,
        ),
    ] {
        let dir = product_input(label, change, "z:Z,", "z*(s.x+s.y)=z", true);
        let asks = [
            "r=repair(Pair.total,using=Pair.setpair,on=@pair/s)",
            "n=needed($r)",
        ];
        let result = execute(&dir, "out", &asks);
        assert_eq!(result.code, code, "{label}: {}", result.stdout);
        let j = result_json(&dir, &result);
        let outputs = get(&arr(get(&j, "answers"))[0], "outputs");
        assert_eq!(has(outputs, "object"), code == 0);
        if code == 2 {
            assert!(
                arr(get(&arr(get(&j, "answers"))[0], "reasons"))
                    .iter()
                    .any(|r| s(get(r, "code")) == "missing_observation")
            );
            let plan = get(output(&j, 1, "plan"), "value");
            assert!(
                arr(get(plan, "requirements"))
                    .iter()
                    .any(|r| s(get(get(r, "field"), "field")) == "Pair.State.y")
            );
        }
    }
}
#[test]
fn parameter_product_lexical_conjunction_keeps_inconsistent_constraints() {
    for (label, parameters, predicate) in [
        ("inconsistent-and", "z:Z,", "let k=s.x in z*k=z and z*k=2*z"),
        (
            "inconsistent-forall",
            "",
            "forall z:Z. let k=s.x in z*k=z and z*k=2*z",
        ),
    ] {
        let dir = product_input(
            label,
            "change setpair(s:State,a:Z)=s with{x=a,y=0};",
            parameters,
            predicate,
            false,
        );
        let asks = ["r=repair(Pair.total,using=Pair.setpair,on=@pair/s)"];
        let result = execute(&dir, "out", &asks);
        assert_eq!(result.code, 1, "{}", result.stdout);
        let j = result_json(&dir, &result);
        assert!(!has(get(&arr(get(&j, "answers"))[0], "outputs"), "object"));
        assert_eq!(
            s(get(get(output(&j, 0, "existence"), "judgment"), "status")),
            "refuted"
        );
        assert_eq!(
            s(get(
                get(get(output(&j, 0, "solutions"), "value"), "representation"),
                "kind"
            )),
            "empty"
        );
    }
}
#[test]
fn parameter_product_nonlinear_coefficients_preserve_the_algorithm_reason() {
    let dir = product_input(
        "nonlinear-coefficient",
        "change setpair(s:State,a:Z)=s with{x=a,y=0};",
        "z:Z,",
        "z*s.x*s.x=z",
        false,
    );
    let asks = [
        "r=repair(Pair.total,using=Pair.setpair,on=@pair/s)",
        "n=needed($r)",
    ];
    let result = execute(&dir, "out", &asks);
    assert_eq!(result.code, 2, "{}", result.stdout);
    let j = result_json(&dir, &result);
    assert_eq!(s(get(&j, "status")), "partial");
    let answers = arr(get(&j, "answers"));
    assert_eq!(s(get(&answers[0], "status")), "undetermined");
    assert!(!has(get(&answers[0], "outputs"), "object"));
    let reason = &arr(get(&answers[0], "reasons"))[0];
    assert_eq!(s(get(reason, "code")), "unsupported_algorithm");
    let details = get(reason, "details");
    assert_eq!(s(get(details, "method")), "numeric_change_condition");
    assert_eq!(s(get(details, "question")), "repair");
    assert_eq!(arr(get(details, "operand_types")).len(), 1);
    assert_eq!(s(&arr(get(details, "operand_types"))[0]), "Z");
    let location = get(reason, "location");
    assert_eq!(s(get(location, "input")), "law");
    let span = arr(get(location, "span"));
    let law = std::fs::read(dir.join("l.law")).unwrap();
    assert_eq!(
        &law[num(&span[0]) as usize..num(&span[1]) as usize],
        b"z*s.x*s.x=z"
    );
    assert_eq!(s(get(&answers[1], "status")), "established");
    let plan = output(&j, 1, "plan");
    assert!(
        arr(get(get(plan, "value"), "blockers"))
            .iter()
            .any(|r| r.value == reason.value)
    );
}
#[test]
fn universal_integer_law_repairs_finite_and_integer_changes() {
    for change in [
        "change setpair(s:State,b:Bool)=s with{x=if b then 1 else 0,y=0};",
        "change setpair(s:State,a:Z)=s with{x=a,y=0};",
    ] {
        let dir = input("universal-integer-repair", change);
        let path = dir.join("l.law");
        let law = std::fs::read_to_string(&path).unwrap().replace(
            "total(s:State):s.x+s.y=1",
            "total(z:Z,s:State):s.x+s.y+z=z+1",
        );
        std::fs::write(path, law).unwrap();
        let asks = [
            "a=solve(Pair.total,using=Pair.setpair,on=@pair/s)",
            "r=repair(Pair.total,using=Pair.setpair,on=@pair/s)",
            "x=evaluate(Pair.first,on=$r.object,s=@pair/s)",
            "c=check(Pair.total,on=$r.object)",
        ];
        let result = execute(&dir, "out", &asks);
        assert_eq!(result.code, 0, "{}", result.stdout);
        let j = result_json(&dir, &result);
        assert_eq!(s(get(output(&j, 2, "value"), "value")), "1");
        let scope = get(&arr(get(&j, "answers"))[0], "scope");
        let quantifiers = arr(get(scope, "quantifiers"));
        assert!(quantifiers.iter().any(|q| s(get(q, "name")) == "z"
            && s(get(q, "kind")) == "forall"
            && !has(q, "domain")));
    }
}

#[test]
fn universal_integer_law_keeps_empty_and_nonunique_repairs_distinct() {
    for finite in [false, true] {
        for predicate in ["z=z", "z=s.x"] {
            let change = if finite {
                "change setpair(s:State,b:Bool)=s with{x=if b then 1 else 0,y=0};"
            } else {
                "change setpair(s:State,a:Z)=s with{x=a,y=0};"
            };
            let dir = input("universal-integer-empty-nonunique", change);
            let path = dir.join("l.law");
            let law = std::fs::read_to_string(&path).unwrap().replace(
                "total(s:State):s.x+s.y=1",
                &format!("total(z:Z,s:State):{predicate}"),
            );
            std::fs::write(path, law).unwrap();
            let result = execute(
                &dir,
                "out",
                &["r=repair(Pair.total,on=@pair/s,using=Pair.setpair)"],
            );
            assert_eq!(result.code, 1, "{}", result.stdout);
            let j = result_json(&dir, &result);
            assert!(!has(get(&arr(get(&j, "answers"))[0], "outputs"), "object"));
            let all = predicate == "z=z";
            assert_eq!(
                s(get(get(output(&j, 0, "existence"), "judgment"), "status")),
                if all { "established" } else { "refuted" }
            );
            let repr = get(get(output(&j, 0, "solutions"), "value"), "representation");
            assert_eq!(
                s(get(repr, "kind")),
                if !all {
                    "empty"
                } else if finite {
                    "finite"
                } else {
                    "affine"
                }
            );
            if all && finite {
                assert_eq!(arr(get(repr, "values")).len(), 2);
            }
            if all && !finite {
                assert_eq!(
                    num(get(
                        get(node(&j, get(repr, "directions")), "value"),
                        "free_rank"
                    )),
                    1
                );
            }
        }
    }
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
    assert_eq!(r.code, 1, "{}", r.stdout);
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
    assert_eq!(r.code, 2, "{}", r.stdout);
    let r = execute(
        &dir,
        "pinned",
        &[
            "r=repair(Pair.pinned,using=Pair.setpair,on=@pair/s,s=@pair/s)",
            "x=evaluate(Pair.first,on=$r.object,s=@pair/s)",
            "c=check(Pair.pinned,on=$r.object,s=@pair/s)",
        ],
    );
    assert_eq!(r.code, 0, "{}", r.stdout);
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
    assert_eq!(r.code, 1, "{}", r.stdout);
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
    assert_eq!(r.code, 1, "{}", r.stdout);
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
            "--ask",
            asks[0],
            "--ask",
            asks[1],
        ],
    );
    assert_eq!(repeated.code, 0, "{}", repeated.stdout);
    let result = result_json(&dir, &repeated);
    assert!(!has(&result, "reuse"));
    for field in ["answers", "nodes"] {
        assert_eq!(get(&result, field).value, get(&original, field).value);
    }
}

#[test]
fn integer_local_instances_have_independent_parameter_axes() {
    let dir = workdir("integer-local");
    let definitions = local_fixture::D;
    let d = definition::check_definitions(&[("d", definitions.as_bytes())]).unwrap();
    let digest = &d.vocabularies()["Pattern"].digest;
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
    assert_eq!(r.code, 0, "{}", r.stdout);
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
fn nonlinear_change_preserves_unsupported_reason_source_and_completed_answers() {
    let dir = input(
        "integer-nonlinear",
        "change setpair(s:State,a:Z,b:Z)=s with{x=a*a,y=b};",
    );
    let sources = archsig::input::InputSources::from_bytes(
        vec![std::fs::read(dir.join("d.json")).unwrap()],
        std::fs::read(dir.join("l.law")).unwrap(),
        std::fs::read(dir.join("a.json")).unwrap(),
    );
    let observed = archsig::observed::evaluate_observed_bytes(
        sources,
        &["s=solve(Pair.total,using=Pair.setpair,on=@pair/s,s=@pair/s)"],
        &mut archsig::control::Control::unlimited(),
    )
    .unwrap();
    assert_eq!(observed.status(), "partial");
    let internal = archsig::json::parse(observed.wire().canonical().as_bytes()).unwrap();
    let reason = &arr(get(&arr(get(&internal, "answers"))[0], "reasons"))[0];
    let source = node(&internal, &arr(get(reason, "dependencies"))[0]);
    let parameters = arr(get(get(source, "value"), "parameters"));
    assert_eq!(
        parameters
            .iter()
            .map(|p| s(get(p, "name")))
            .collect::<Vec<_>>(),
        ["a", "b"]
    );
    assert!(parameters.iter().all(|p| s(get(p, "type")) == "Z"));
    for (case, prior) in [
        ("alone", false),
        ("after-value", true),
        ("after-missing", true),
    ] {
        if case == "after-missing" {
            let map=std::fs::read_to_string(dir.join("a.json")).unwrap().replace(r#"{"id":"x","subject":"s","field":"Pair.State.x","value":"0","origin":"model"},"#, "");
            std::fs::write(dir.join("a.json"), map).unwrap();
        }
        let mut asks = vec![];
        if prior {
            asks.push("v=evaluate(Pair.first,s=@pair/s)");
        }
        asks.extend([
            "s=solve(Pair.total,using=Pair.setpair,on=@pair/s,s=@pair/s)",
            "n=needed($s)",
        ]);
        let r = execute(&dir, case, &asks);
        assert_eq!(r.code, 2, "{}", r.stdout);
        let j = result_json(&dir, &r);
        assert_eq!(s(get(&j, "status")), "partial");
        let answers = arr(get(&j, "answers"));
        let solver = &answers[usize::from(prior)];
        assert_eq!(s(get(solver, "status")), "undetermined");
        assert!(!has(get(solver, "outputs"), "object"));
        let unsupported = arr(get(solver, "reasons"))
            .iter()
            .find(|r| s(get(r, "code")) == "unsupported_algorithm")
            .unwrap();
        let details = get(unsupported, "details");
        assert_eq!(s(get(details, "method")), "nonlinear_numeric_change");
        assert_eq!(s(&arr(get(details, "operand_types"))[0]), "Z");
        assert!(has(unsupported, "location"));
        assert!(arr(get(unsupported, "dependencies")).is_empty());
        assert!(
            !arr(get(&j, "issues"))
                .iter()
                .any(|r| s(get(r, "code")) == "internal")
        );
        let needed = &answers[usize::from(prior) + 1];
        assert_eq!(s(get(needed, "status")), "established");
        assert!(
            format!("{:?}", node(&j, get(get(needed, "outputs"), "plan")))
                .contains("nonlinear_numeric_change")
        );
        if prior {
            let v = &answers[0];
            if case == "after-value" {
                assert_eq!(s(get(v, "status")), "established");
                assert_eq!(
                    s(get(node(&j, get(get(v, "outputs"), "value")), "value")),
                    "0"
                );
            } else {
                assert_eq!(s(get(v, "status")), "undetermined");
                assert!(format!("{:?}", get(v, "reasons")).contains("missing_observation"));
            }
        }
    }
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
    assert_eq!(r.code, 0, "{}", r.stdout);
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
        if !has(n, "value") {
            continue;
        }
        let value = get(n, "value");
        let fields: &[&str] = if has(value, "columns") && has(value, "source") {
            maps += 1;
            &["source", "target"]
        } else if has(value, "coordinates") && has(value, "module") {
            vectors += 1;
            &["module"]
        } else {
            continue;
        };
        let ty = arr(get(n, "type"));
        assert_eq!(
            s(&ty[0]),
            if fields.len() == 2 {
                "ModuleMap"
            } else {
                "Vector"
            }
        );
        assert_eq!(ty.len(), fields.len() + 1);
        for (i, field) in fields.iter().enumerate() {
            assert_eq!(
                s(get(&ty[i + 1], "node")),
                s(get(get(value, field), "node"))
            );
            assert_eq!(s(get(node(result, &ty[i + 1]), "type")), "Module");
        }
    }
    assert!(maps > 0 && vectors > 0);
}

#[test]
fn integer_repair_stop_after_first_witness_keeps_existence_without_object() {
    use archsig::{
        control::{Checkpoint, Control},
        input::InputSources,
        observed::evaluate::evaluate_observed_bytes,
    };
    use std::{cell::Cell, rc::Rc};
    let dir = input(
        "integer-stop",
        "change setpair(s:State,a:Z,b:Z)=s with{x=a,y=b};",
    );
    let seen = Rc::new(Cell::new(0));
    let count = seen.clone();
    let mut c = Control::new(move |point| {
        if point == Checkpoint::ChangeWitness {
            count.set(count.get() + 1);
        }
        (count.get() == 2).then_some(archsig::result::Signal::Term)
    });
    let source = InputSources::from_bytes(
        vec![std::fs::read(dir.join("d.json")).unwrap()],
        std::fs::read(dir.join("l.law")).unwrap(),
        std::fs::read(dir.join("a.json")).unwrap(),
    );
    let result = evaluate_observed_bytes(
        source,
        &[
            "r=repair(Pair.total,using=Pair.setpair,on=@pair/s,s=@pair/s)",
            "later=check(Pair.total,s=@pair/s)",
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
    for answer in answers {
        assert!(
            arr(get(answer, "reasons"))
                .iter()
                .any(|r| s(get(r, "code")) == "cancelled")
        );
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
        assert_eq!(run.code, 0, "{}", run.stdout);
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
    assert_eq!(run.code, 1, "{}", run.stdout);
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
    assert_eq!(run.code, 1, "{}", run.stdout);
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

fn quotient_representation(result: &JNode, index: usize) -> &JNode {
    get(
        get(output(result, index, "quotient"), "value"),
        "representation",
    )
}
fn integer_columns(result: &JNode, map: &JNode) -> Vec<Vec<i64>> {
    arr(get(get(node(result, map), "value"), "columns"))
        .iter()
        .map(|column| {
            arr(column)
                .iter()
                .map(|v| s(get(node(result, v), "value")).parse().unwrap())
                .collect()
        })
        .collect()
}
#[test]
fn integer_quotient_uses_actual_image_offset_and_solution_parameter_domain() {
    let dir = input(
        "integer-quotient-image",
        "change setpair(s:State,a:Z,b:Z)=s with{x=2*a+1,y=b};view combined(s:State):Z=s.x+s.y;",
    );
    let asks = [
        "s=solve(Pair.total,on=@pair/s,using=Pair.setpair,s=@pair/s)",
        "all=quotient(Pair.first,on=$s.domain,s=@pair/s)",
        "good=quotient(Pair.combined,on=$s.solutions,s=@pair/s)",
    ];
    let r = execute(&dir, "out", &asks);
    assert_eq!(r.code, 0, "{}", r.stdout);
    let result = result_json(&dir, &r);
    assert_module_owners(&result);
    let all = quotient_representation(&result, 1);
    assert_eq!(s(get(all, "kind")), "affine");
    assert_eq!(
        integer_columns(&result, get(all, "map")),
        vec![vec![2], vec![0]]
    );
    assert_eq!(coordinates(&result, get(all, "offset")), vec![1]);
    for (field, rank) in [("image", 1), ("kernel", 1)] {
        assert_eq!(
            num(get(
                get(node(&result, get(all, field)), "value"),
                "free_rank"
            )),
            rank
        );
    }
    let image_module = get(node(&result, get(all, "image")), "value");
    assert_eq!(
        s(get(&arr(get(image_module, "generators"))[0], "value"))
            .parse::<i64>()
            .unwrap()
            .abs(),
        2
    );
    let original_map = get(node(&result, get(all, "map")), "value");
    let inclusions = arr(get(&result, "nodes"))
        .iter()
        .filter(|n| {
            if !has(n, "value") {
                return false;
            }
            let v = get(n, "value");
            has(v, "columns")
                && get(v, "source").value == get(all, "image").value
                && get(v, "target").value == get(original_map, "target").value
        })
        .collect::<Vec<_>>();
    assert_eq!(inclusions.len(), 1, "実像の包含ModuleMapが必要");
    let coefficient = s(get(
        node(
            &result,
            &arr(&arr(get(get(inclusions[0], "value"), "columns"))[0])[0],
        ),
        "value",
    ))
    .parse::<i64>()
    .unwrap();
    assert_eq!(
        coefficient,
        s(get(&arr(get(image_module, "generators"))[0], "value"))
            .parse::<i64>()
            .unwrap()
    );

    let kernel_inclusions = arr(get(&result, "nodes"))
        .iter()
        .filter(|n| {
            if !has(n, "value") {
                return false;
            }
            let v = get(n, "value");
            has(v, "columns")
                && get(v, "source").value == get(all, "kernel").value
                && get(v, "target").value == get(original_map, "source").value
        })
        .collect::<Vec<_>>();
    assert_eq!(kernel_inclusions.len(), 1, "核の包含ModuleMapが必要");
    let kernel_column = arr(&arr(get(get(kernel_inclusions[0], "value"), "columns"))[0])
        .iter()
        .map(|r| s(get(node(&result, r), "value")).parse::<i64>().unwrap())
        .collect::<Vec<_>>();
    let kernel_module = get(node(&result, get(all, "kernel")), "value");
    let kernel_generator = arr(get(&arr(get(kernel_module, "generators"))[0], "value"))
        .iter()
        .map(|v| s(v).parse::<i64>().unwrap())
        .collect::<Vec<_>>();
    assert_eq!(kernel_column, kernel_generator);
    for n in arr(get(&result, "nodes")) {
        for key in ["rule", "arguments", "evidence", "support"] {
            assert!(!has(n, key));
        }
    }

    let classes = node(
        &result,
        get(get(output(&result, 1, "quotient"), "value"), "classes"),
    );
    assert_eq!(s(get(get(classes, "value"), "kind")), "image");
    let actual_map = node(&result, get(get(classes, "value"), "map"));
    assert_eq!(
        get(get(actual_map, "value"), "linear").value,
        get(all, "map").value
    );
    assert_eq!(
        get(get(actual_map, "value"), "offset").value,
        get(all, "offset").value
    );
    let good = quotient_representation(&result, 2);
    assert_eq!(integer_columns(&result, get(good, "map")), vec![vec![0]]);
    assert_eq!(coordinates(&result, get(good, "offset")), vec![1]);
    assert_eq!(
        num(get(
            get(node(&result, get(good, "image")), "value"),
            "free_rank"
        )),
        0
    );
}
#[test]
fn integer_quotient_distinguishes_empty_solutions_from_one_class() {
    for (label, law, empty) in [
        ("empty", "Pair.pinned", true),
        ("nonempty", "Pair.total", false),
    ] {
        let dir = input(
            &format!("integer-quotient-{label}"),
            "change setpair(s:State,a:Z,b:Z)=s with{x=2*a+1,y=b};view constant(s:State):Z=7;",
        );
        let solve = format!("s=solve({law},on=@pair/s,using=Pair.setpair,s=@pair/s)");
        let r = execute(
            &dir,
            "out",
            &[
                &solve,
                "q=quotient(Pair.constant,on=$s.solutions,s=@pair/s)",
            ],
        );
        assert_eq!(r.code, if empty { 1 } else { 0 }, "{}", r.stdout);
        let result = result_json(&dir, &r);
        let rep = quotient_representation(&result, 1);
        if empty {
            assert_eq!(s(get(rep, "kind")), "finite");
            assert!(arr(get(rep, "fibers")).is_empty());
            let q = get(output(&result, 1, "quotient"), "value");
            let classes = get(node(&result, get(q, "classes")), "value");
            assert!(arr(get(classes, "elements")).is_empty());
            assert!(has(classes, "type"));
        } else {
            assert_eq!(s(get(rep, "kind")), "affine");
            assert_eq!(coordinates(&result, get(rep, "offset")), vec![7]);
            assert_eq!(
                num(get(
                    get(node(&result, get(rep, "image")), "value"),
                    "free_rank"
                )),
                0
            );
        }
    }
}
#[test]
fn integer_quotient_respects_guard_fiber_and_empty_candidate_domain() {
    for (label, guard, empty) in [("line", "a=b", false), ("empty", "2*a=1", true)] {
        let dir = input(
            &format!("integer-quotient-guard-{label}"),
            &format!(
                "change setpair(s:State,a:Z,b:Z) when {guard}=s with{{x=a,y=b}};view combined(s:State):Z=s.x+s.y;"
            ),
        );
        let r = execute(
            &dir,
            "out",
            &[
                "s=solve(Pair.total,on=@pair/s,using=Pair.setpair,s=@pair/s)",
                "q=quotient(Pair.combined,on=$s.domain,s=@pair/s)",
            ],
        );
        assert_eq!(r.code, 1, "{}", r.stdout);
        let result = result_json(&dir, &r);
        let rep = quotient_representation(&result, 1);
        if empty {
            assert_eq!(s(get(rep, "kind")), "finite");
            assert!(arr(get(rep, "fibers")).is_empty());
        } else {
            let columns = integer_columns(&result, get(rep, "map"));
            assert_eq!(columns.len(), 1);
            assert_eq!(columns[0][0].abs(), 2);
            assert_eq!(coordinates(&result, get(rep, "offset")), vec![0]);
        }
    }
}

#[test]
fn integer_quotient_keeps_repaired_architecture_offset() {
    let dir = input(
        "integer-quotient-repaired",
        "change setpair(s:State,a:Z,b:Z)=s with{x=s.x+a,y=s.y+b};view combined(s:State):Z=s.x+s.y;",
    );
    let r = execute(
        &dir,
        "out",
        &[
            "r=repair(Pair.pinned,on=@pair/s,using=Pair.setpair,s=@pair/s)",
            "s=solve(Pair.total,on=$r.object,using=Pair.setpair,s=@pair/s)",
            "q=quotient(Pair.combined,on=$s.domain,s=@pair/s)",
        ],
    );
    assert_eq!(r.code, 0, "{}", r.stdout);
    let result = result_json(&dir, &r);
    let rep = quotient_representation(&result, 2);
    assert_eq!(coordinates(&result, get(rep, "offset")), vec![1]);
    assert_eq!(
        integer_columns(&result, get(rep, "map")),
        vec![vec![1], vec![1]]
    );
}
#[test]
fn integer_quotient_stop_keeps_solve_and_never_publishes_partial_image() {
    use archsig::{
        control::{Checkpoint, Control},
        input::InputSources,
        observed::evaluate::evaluate_observed_bytes,
    };
    use std::{cell::Cell, rc::Rc};
    let dir = input(
        "integer-quotient-stop",
        "change setpair(s:State,a:Z,b:Z)=s with{x=a,y=b};",
    );
    let seen = Rc::new(Cell::new(0));
    let count = seen.clone();
    let mut c = Control::new(move |point| {
        if point == Checkpoint::Quotient {
            count.set(count.get() + 1);
        }
        (count.get() == 2).then_some(archsig::result::Signal::Term)
    });
    let sources = InputSources::from_bytes(
        vec![std::fs::read(dir.join("d.json")).unwrap()],
        std::fs::read(dir.join("l.law")).unwrap(),
        std::fs::read(dir.join("a.json")).unwrap(),
    );
    let result = evaluate_observed_bytes(
        sources,
        &[
            "s=solve(Pair.total,on=@pair/s,using=Pair.setpair,s=@pair/s)",
            "q=quotient(Pair.first,on=$s.domain,s=@pair/s)",
        ],
        &mut c,
    )
    .unwrap();
    let wire = archsig::json::parse(result.wire().canonical().as_bytes()).unwrap();
    let answers = arr(get(&wire, "answers"));
    assert_eq!(seen.get(), 2);
    assert_eq!(s(get(&answers[0], "status")), "established");
    assert!(has(get(&answers[0], "outputs"), "solutions"));
    assert!(!has(get(&answers[1], "outputs"), "quotient"));
    assert_eq!(s(get(&answers[1], "status")), "undetermined");
    assert!(
        arr(get(&answers[1], "reasons"))
            .iter()
            .any(|r| s(get(r, "code")) == "cancelled")
    );
}

#[test]
fn integer_quotient_missing_unmodified_view_field_is_not_a_zero_image() {
    let dir = input(
        "integer-quotient-missing",
        "change setpair(s:State,a:Z)=s with{x=a};law optional first_zero(s:State):s.x=0;view second(s:State):Z=s.y;",
    );
    let path = dir.join("a.json");
    let before = std::fs::read_to_string(&path).unwrap();
    let after = before.replace(
        r#",{"id":"y","subject":"s","field":"Pair.State.y","value":"0","origin":"model"}"#,
        "",
    );
    assert_ne!(before, after);
    std::fs::write(path, after).unwrap();
    let r = execute(
        &dir,
        "out",
        &[
            "s=solve(Pair.first_zero,on=@pair/s,using=Pair.setpair,s=@pair/s)",
            "q=quotient(Pair.second,on=$s.domain,s=@pair/s)",
            "later=evaluate(Pair.first,s=@pair/s)",
        ],
    );
    assert_eq!(r.code, 2, "{}", r.stdout);
    let result = result_json(&dir, &r);
    let answers = arr(get(&result, "answers"));
    assert_eq!(s(get(&answers[1], "status")), "undetermined");
    assert!(!has(get(&answers[1], "outputs"), "quotient"));
    assert!(
        arr(get(&answers[1], "reasons"))
            .iter()
            .any(|r| s(get(r, "code")) == "missing_observation"
                && !arr(get(r, "missing")).is_empty())
    );
    assert_eq!(s(get(&answers[2], "status")), "established");
}

#[test]
fn integer_law_descent_uses_value_pairs_and_the_actual_image_basis() {
    let dir = input(
        "integer-law-descent",
        "change setpair(s:State,a:Z,b:Z)=s with{x=a,y=b};view twice(s:State):Z=2*s.x;view combined(s:State):Z=s.x+s.y;law optional same(s:State):s.x=s.x;law optional unequal(s:State):1=2;",
    );
    let asks = [
        "s=solve(Pair.total,on=@pair/s,using=Pair.setpair,s=@pair/s)",
        "good=quotient(Pair.twice,on=$s.domain,s=@pair/s,law=Pair.same)",
        "bad=quotient(Pair.combined,on=$s.domain,s=@pair/s,law=Pair.same)",
        "solutions=quotient(Pair.combined,on=$s.solutions,s=@pair/s,law=Pair.total)",
        "false_law=quotient(Pair.combined,on=$s.domain,s=@pair/s,law=Pair.unequal)",
    ];
    let r = execute(&dir, "out", &asks);
    assert_eq!(r.code, 1, "{}", r.stdout);
    let result = result_json(&dir, &r);
    assert_module_owners(&result);
    let answers = arr(get(&result, "answers"));
    for i in [1, 3, 4] {
        assert_eq!(s(get(&answers[i], "status")), "established");
        assert!(has(get(&answers[i], "outputs"), "proposition"));
    }
    let quotient = get(output(&result, 1, "quotient"), "value");
    let descent = get(node(&result, get(quotient, "descent")), "value");
    let map = get(node(&result, get(descent, "linear")), "value");
    assert_eq!(
        get(map, "source").value,
        get(get(quotient, "representation"), "image").value
    );
    let columns = integer_columns(&result, get(descent, "linear"));
    assert_eq!(columns.len(), 1);
    assert_eq!(columns[0].len(), 2);
    let image_module = get(node(&result, get(map, "source")), "value");
    let image_generator = s(get(&arr(get(image_module, "generators"))[0], "value"))
        .parse::<i64>()
        .unwrap();
    assert_eq!(image_generator.abs(), 2);
    assert_eq!(columns[0], vec![image_generator / 2, image_generator / 2]);
    assert_eq!(coordinates(&result, get(descent, "offset")), vec![0, 0]);
    let family = get(node(&result, get(map, "target")), "value");
    let labels = arr(get(family, "generators"));
    assert_eq!(labels.len(), 2);
    for (label, side) in labels.iter().zip(["lhs", "rhs"]) {
        let label = arr(get(label, "value"));
        assert_eq!(s(&label[1]), side);
        let key = arr(&label[0]);
        assert_eq!(key.len(), 1);
        assert_eq!(
            key[0].value,
            archsig::json::parse(br#"["pair","s"]"#).unwrap().value
        );
    }
    assert_eq!(s(get(&answers[2], "status")), "refuted");
    let evidence = get(
        node(&result, &arr(get(&answers[2], "counterexamples"))[0]),
        "value",
    );
    assert_eq!(s(get(evidence, "kind")), "separating_pair");
    let data = get(evidence, "data");
    let views = arr(get(data, "view_values"));
    assert_eq!(
        get(node(&result, &views[0]), "value").value,
        get(node(&result, &views[1]), "value").value
    );
    let values = arr(get(data, "law_values"));
    assert_ne!(
        get(node(&result, &values[0]), "value").value,
        get(node(&result, &values[1]), "value").value
    );
    assert_ne!(
        get(node(&result, get(data, "first")), "value").value,
        get(node(&result, get(data, "second")), "value").value
    );
    let bad = get(output(&result, 2, "quotient"), "value");
    assert!(!has(bad, "descent"));
    assert_eq!(arr(get(bad, "evaluations")).len(), 2);
    for evaluation in arr(get(bad, "evaluations")) {
        let evaluation = get(node(&result, evaluation), "value");
        assert_eq!(
            get(node(&result, get(evaluation, "value")), "value").value,
            archsig::json::JValue::Bool(true)
        );
        assert!(has(evaluation, "environment"));
        assert!(!has(evaluation, "parts"));
    }
    for (i, expected) in [(3, vec![1, 1]), (4, vec![1, 2])] {
        let q = get(output(&result, i, "quotient"), "value");
        let d = get(node(&result, get(q, "descent")), "value");
        assert_eq!(coordinates(&result, get(d, "offset")), expected);
        for column in integer_columns(&result, get(d, "linear")) {
            assert_eq!(column, vec![0, 0]);
        }
    }
}
#[test]
fn integer_law_descent_preserves_guard_origin_extra_binding_and_empty_domain() {
    let dir = input(
        "integer-law-guard",
        "change setpair(s:State,a:Z,b:Z) when a=b=s with{x=a,y=b};law optional sum_two(s:State):s.x+s.y=2;law optional comparison(s:State,k:Z):s.x=k;view twice(s:State):Z=2*s.x;view threshold(s:State):Z=3;",
    );
    let r = execute(
        &dir,
        "out",
        &[
            "s=solve(Pair.sum_two,on=@pair/s,using=Pair.setpair,s=@pair/s)",
            "k=evaluate(Pair.threshold,s=@pair/s)",
            "q=quotient(Pair.twice,on=$s.solutions,s=@pair/s,law=Pair.comparison,k=$k.value)",
            "e=solve(Pair.total,on=@pair/s,using=Pair.setpair,s=@pair/s)",
            "empty=quotient(Pair.twice,on=$e.solutions,s=@pair/s,law=Pair.comparison,k=$k.value)",
        ],
    );
    assert_eq!(r.code, 1, "{}", r.stdout);
    let result = result_json(&dir, &r);
    let q = get(output(&result, 2, "quotient"), "value");
    let descent = get(node(&result, get(q, "descent")), "value");
    assert_eq!(coordinates(&result, get(descent, "offset")), vec![1, 3]);
    assert!(integer_columns(&result, get(descent, "linear")).is_empty());
    let map = get(node(&result, get(descent, "linear")), "value");
    let family = get(node(&result, get(map, "target")), "value");
    for generator in arr(get(family, "generators")) {
        let label = arr(get(generator, "value"));
        let key = arr(&label[0]);
        assert_eq!(key.len(), 2);
        assert_eq!(s(&key[1]), "3");
    }
    let empty = get(output(&result, 4, "quotient"), "value");
    let descent = get(node(&result, get(empty, "descent")), "value");
    assert_eq!(s(get(descent, "kind")), "finite");
    assert!(arr(get(descent, "pairs")).is_empty());
    assert_eq!(
        s(get(&arr(get(&result, "answers"))[4], "status")),
        "established"
    );
}
#[test]
fn integer_law_descent_missing_operands_do_not_become_a_true_constant_family() {
    let dir = input(
        "integer-law-missing",
        "change setpair(s:State,a:Z)=s with{x=a};law optional first_zero(s:State):s.x=0;law optional same_second(s:State):s.y=s.y;",
    );
    let path = dir.join("a.json");
    let before = std::fs::read_to_string(&path).unwrap();
    let after = before.replace(
        r#",{"id":"y","subject":"s","field":"Pair.State.y","value":"0","origin":"model"}"#,
        "",
    );
    assert_ne!(before, after);
    std::fs::write(path, after).unwrap();
    let r = execute(
        &dir,
        "out",
        &[
            "s=solve(Pair.first_zero,on=@pair/s,using=Pair.setpair,s=@pair/s)",
            "q=quotient(Pair.first,on=$s.domain,s=@pair/s,law=Pair.same_second)",
            "later=evaluate(Pair.first,s=@pair/s)",
        ],
    );
    assert_eq!(r.code, 2, "{}", r.stdout);
    let result = result_json(&dir, &r);
    let answers = arr(get(&result, "answers"));
    assert_eq!(s(get(&answers[1], "status")), "undetermined");
    assert!(!has(get(&answers[1], "outputs"), "quotient"));
    assert!(
        arr(get(&answers[1], "reasons"))
            .iter()
            .any(|r| s(get(r, "code")) == "missing_observation")
    );
    assert_eq!(s(get(&answers[2], "status")), "established");
}

#[test]
fn integer_law_descent_stop_during_counterexample_keeps_prior_solve() {
    use archsig::{
        control::{Checkpoint, Control},
        input::InputSources,
        observed::evaluate::evaluate_observed_bytes,
    };
    use std::{cell::Cell, rc::Rc};
    let dir = input(
        "integer-law-stop",
        "change setpair(s:State,a:Z,b:Z)=s with{x=a,y=b};view combined(s:State):Z=s.x+s.y;law optional same(s:State):s.x=s.x;",
    );
    let armed = Rc::new(Cell::new(false));
    let seen = Rc::new(Cell::new(false));
    let active = armed.clone();
    let stopped = seen.clone();
    let mut c = Control::new(move |point| {
        if point == Checkpoint::Quotient {
            active.set(true);
        }
        if active.get() && point == Checkpoint::FiniteLawOperand {
            stopped.set(true);
        }
        stopped.get().then_some(archsig::result::Signal::Term)
    });
    let sources = InputSources::from_bytes(
        vec![std::fs::read(dir.join("d.json")).unwrap()],
        std::fs::read(dir.join("l.law")).unwrap(),
        std::fs::read(dir.join("a.json")).unwrap(),
    );
    let result = evaluate_observed_bytes(
        sources,
        &[
            "s=solve(Pair.total,on=@pair/s,using=Pair.setpair,s=@pair/s)",
            "q=quotient(Pair.combined,on=$s.domain,s=@pair/s,law=Pair.same)",
        ],
        &mut c,
    )
    .unwrap();
    assert!(seen.get());
    let wire = archsig::json::parse(result.wire().canonical().as_bytes()).unwrap();
    let answers = arr(get(&wire, "answers"));
    assert_eq!(s(get(&answers[0], "status")), "established");
    assert!(has(get(&answers[0], "outputs"), "solutions"));
    assert_eq!(s(get(&answers[1], "status")), "undetermined");
    assert!(!has(get(&answers[1], "outputs"), "quotient"));
    assert!(!has(get(&answers[1], "outputs"), "proposition"));
    assert!(
        arr(get(&answers[1], "reasons"))
            .iter()
            .any(|r| s(get(r, "code")) == "cancelled")
    );
}

#[test]
fn three_edge_integer_repair_keeps_translation_freedom() {
    three_edge_integer_repair_keeps_translation_freedom_obstruction_and_missing_shift(0);
}
#[test]
fn three_edge_integer_repair_keeps_the_obstruction() {
    three_edge_integer_repair_keeps_translation_freedom_obstruction_and_missing_shift(1);
}
#[test]
fn three_edge_integer_repair_keeps_the_missing_shift() {
    three_edge_integer_repair_keeps_translation_freedom_obstruction_and_missing_shift(2);
}
fn three_edge_integer_repair_keeps_translation_freedom_obstruction_and_missing_shift(row: usize) {
    use crate::common::three_edge as triangle;
    let gamma = [Some(2), Some(3), None][row];
    let input = triangle::input(gamma);
    let asks = [
        "a=build(Coordinates,on=@triangle/root)",
        "r=repair(Coordinates.aligned,on=$a.object,using=Coordinates.move)",
        "n=needed($r)",
    ];
    if gamma == Some(3) {
        // 反証の証拠(Smith変換)は内部graphにだけあるので、同じ三入力を一度だけ内部で評価する。
        // 公開結果がSmith証書を持たないことは cli_summary の empty_integer_solutions_are_saved_without_smith_certificates が見る。
        let result = archsig::observed::evaluate_observed_bytes(
            input,
            &asks,
            &mut archsig::control::Control::unlimited(),
        )
        .unwrap();
        assert_eq!(result.status(), "complete");
        let j = archsig::json::parse(result.wire().canonical().as_bytes()).unwrap();
        let answer = &arr(get(&j, "answers"))[1];
        assert!(!has(get(answer, "outputs"), "object"));
        let representation = get(get(output(&j, 1, "solutions"), "value"), "representation");
        assert_eq!(s(get(representation, "kind")), "empty");
        assert_eq!(
            s(get(get(output(&j, 1, "existence"), "judgment"), "status")),
            "refuted"
        );
        let proof = get(
            get(node(&j, get(representation, "certificate")), "value"),
            "data",
        );
        let columns = integer_columns(&j, get(proof, "map"));
        assert_eq!(
            columns,
            vec![vec![-1, 0, -1], vec![1, -1, 0], vec![0, 1, 1]]
        );
        let left = integer_columns(&j, get(proof, "left"));
        let transformed = coordinates(&j, get(proof, "transformed_rhs"));
        let mut found = false;
        for i in 0..3 {
            let lambda = (0..3).map(|k| left[k][i]).collect::<Vec<_>>();
            if columns
                .iter()
                .all(|column| column.iter().zip(&lambda).map(|(a, b)| a * b).sum::<i64>() == 0)
            {
                assert!(lambda == vec![1, 1, -1] || lambda == vec![-1, -1, 1]);
                let value = lambda[0] + lambda[1] + 3 * lambda[2];
                assert_ne!(value, 0);
                assert_eq!(transformed[i], value);
                found = true;
            }
        }
        assert!(
            found,
            "published Smith transform must exhibit the integer obstruction"
        );
        return;
    }
    let dir = workdir("integer-three-edge");
    for (name, bytes) in [
        ("d.json", input.definitions()[0].bytes()),
        ("l.law", input.law().bytes()),
        ("a.json", input.archmap().bytes()),
    ] {
        std::fs::write(dir.join(name), bytes).unwrap();
    }
    let r = execute(&dir, "out", &asks);
    assert_eq!(
        r.code,
        if gamma.is_some() { 1 } else { 2 },
        "gamma {gamma:?}: {}",
        r.stdout
    );
    let j = result_json(&dir, &r);
    let answer = &arr(get(&j, "answers"))[1];
    assert!(!has(get(answer, "outputs"), "object"));
    if gamma.is_some() {
        let representation = get(get(output(&j, 1, "solutions"), "value"), "representation");
        assert_eq!(s(get(representation, "kind")), "affine");
        assert_eq!(
            s(get(get(output(&j, 1, "existence"), "judgment"), "status")),
            "established"
        );
        let directions = get(node(&j, get(representation, "directions")), "value");
        assert_eq!(num(get(directions, "free_rank")), 1);
        let point = coordinates(&j, get(representation, "particular"));
        assert_eq!(point.len(), 3);
        assert_eq!((point[1] - point[0], point[2] - point[0]), (1, 2));
        let kernel = integer_columns(&j, get(representation, "embedding"));
        assert_eq!(kernel.len(), 1);
        assert_eq!(kernel[0].len(), 3);
        assert_eq!(kernel[0][0].abs(), 1);
        assert!(kernel[0].iter().all(|v| *v == kernel[0][0]));
    } else {
        assert_eq!(s(get(answer, "status")), "undetermined");
        assert!(!has(answer, "claim"));
        assert!(
            arr(get(answer, "reasons"))
                .iter()
                .any(|r| s(get(r, "code")) == "unsupported_algorithm")
        );
        let plan = get(output(&j, 2, "plan"), "value");
        assert!(arr(get(plan, "requirements")).iter().any(|r| {
            let field = get(r, "field");
            s(get(field, "subject")) == "c" && s(get(field, "field")) == "Coordinates.Shift.shift"
        }));
    }
}

#[test]
fn missing_integer_change_keeps_the_cause_expression_and_subject_binding() {
    for (label, change, expected) in [
        (
            "update",
            "change setpair(s:State,a:Z)=s with{x=s.y+a};law optional first_zero(s:State):s.x=0;",
            "s.y+a",
        ),
        (
            "guard",
            "change setpair(s:State,a:Z) when a=s.y=s with{x=a};law optional first_zero(s:State):s.x=0;",
            "a=s.y",
        ),
        (
            "law",
            "change setpair(s:State,a:Z)=s with{x=a};law optional first_zero(s:State):s.x=s.y;",
            "s.x=s.y",
        ),
    ] {
        let dir = input(label, change);
        let map = std::fs::read_to_string(dir.join("a.json"))
            .unwrap()
            .replace(
                r#",{"id":"y","subject":"s","field":"Pair.State.y","value":"0","origin":"model"}"#,
                "",
            );
        std::fs::write(dir.join("a.json"), map).unwrap();
        let asks = [
            "r=repair(Pair.first_zero,using=Pair.setpair,on=@pair/s,s=@pair/s)",
            "n=needed($r)",
        ];
        let result = execute(&dir, "out", &asks);
        assert_eq!(result.code, 2, "{label}: {}", result.stdout);
        let j = result_json(&dir, &result);
        let internal = internal_graph(&dir, &j);
        let answer = &arr(get(&internal, "answers"))[0];
        let reason = arr(get(answer, "reasons"))
            .iter()
            .find(|r| s(get(r, "code")) == "missing_observation")
            .unwrap();
        let expression = get(
            node(&internal, &arr(get(reason, "dependencies"))[0]),
            "value",
        );
        let law = std::fs::read_to_string(dir.join("l.law")).unwrap();
        let span = arr(get(get(expression, "location"), "span"));
        let text = &law[num(&span[0]) as usize..num(&span[1]) as usize];
        assert!(text.contains(expected), "{label}: dependency {text}");
        let binding = arr(get(expression, "bindings"))
            .iter()
            .find(|b| s(get(b, "name")) == "s")
            .expect("subject binding");
        let subject = arr(get(node(&internal, get(binding, "value")), "value"));
        assert_eq!((s(&subject[0]), s(&subject[1])), ("pair", "s"));
        assert_eq!(
            arr(get(expression, "parameters")).len(),
            if label == "law" { 0 } else { 1 }
        );
        let plan = get(output(&j, 1, "plan"), "value");
        assert!(
            arr(get(plan, "requirements"))
                .iter()
                .any(|r| s(get(get(r, "field"), "field")) == "Pair.State.y")
        );
    }
}

#[test]
fn integer_tuple_quotient_keeps_lattice_image_and_nested_view_values() {
    let dir = input(
        "integer-tuple-quotient",
        "change setpair(s:State,a:Z,b:Z)=s with{x=2*a+1,y=b};view pair(s:State):(Z,(Z,Z))=(s.x,(s.y,7));view coupled(s:State):(Z,Z)=(s.x+s.y,2*(s.x+s.y));law optional same(s:State):s.x=s.x;",
    );
    let r = execute(
        &dir,
        "out",
        &[
            "s=solve(Pair.total,on=@pair/s,using=Pair.setpair,s=@pair/s)",
            "q=quotient(Pair.pair,on=$s.domain,s=@pair/s,law=Pair.same)",
            "bad=quotient(Pair.coupled,on=$s.domain,s=@pair/s,law=Pair.same)",
        ],
    );
    assert_eq!(r.code, 1, "{}", r.stdout);
    let j = result_json(&dir, &r);
    assert_module_owners(&j);
    let rep = quotient_representation(&j, 1);
    assert_eq!(coordinates(&j, get(rep, "offset")), vec![1, 0, 7]);
    assert_eq!(
        integer_columns(&j, get(rep, "map")),
        vec![vec![2, 0, 0], vec![0, 1, 0]]
    );
    let image = get(node(&j, get(rep, "image")), "value");
    assert_eq!(num(get(image, "free_rank")), 2);
    let generators = arr(get(image, "generators"));
    assert_eq!(generators.len(), 2);
    let mut xs = vec![];
    for g in generators {
        let v = arr(get(g, "value"));
        assert_eq!(v.len(), 2);
        assert_eq!(arr(&v[1]).len(), 2);
        xs.push(s(&v[0]).parse::<i64>().unwrap().abs());
    }
    xs.sort();
    assert_eq!(xs, vec![0, 2]);
    assert_eq!(s(get(&arr(get(&j, "answers"))[1], "status")), "established");
    assert_eq!(s(get(&arr(get(&j, "answers"))[2], "status")), "refuted");
}

#[test]
fn integer_tuple_law_descent_uses_all_values_on_the_lattice_image() {
    let dir = input(
        "integer-tuple-law",
        "change setpair(s:State,a:Z,b:Z)=s with{x=2*a+1,y=b};view pair(s:State):(Z,Z)=(s.x,s.y);law optional nested(s:State):(s.x,(s.y,7))=(s.x,(s.y,7));",
    );
    let r = execute(
        &dir,
        "out",
        &[
            "s=solve(Pair.total,on=@pair/s,using=Pair.setpair,s=@pair/s)",
            "good=quotient(Pair.pair,on=$s.domain,s=@pair/s,law=Pair.nested)",
            "bad=quotient(Pair.first,on=$s.domain,s=@pair/s,law=Pair.nested)",
        ],
    );
    assert_eq!(r.code, 1, "{}", r.stdout);
    let j = result_json(&dir, &r);
    assert_module_owners(&j);
    let q = get(output(&j, 1, "quotient"), "value");
    let d = get(node(&j, get(q, "descent")), "value");
    assert_eq!(coordinates(&j, get(d, "offset")), vec![1, 0, 7, 1, 0, 7]);
    let columns = integer_columns(&j, get(d, "linear"));
    assert_eq!(columns.len(), 2);
    for column in columns {
        assert_eq!(column.len(), 6);
        assert_eq!(&column[..3], &column[3..]);
        assert_eq!(column[2], 0);
        assert_eq!(column[0] % 2, 0);
    }
    assert_eq!(s(get(&arr(get(&j, "answers"))[1], "status")), "established");
    assert_eq!(s(get(&arr(get(&j, "answers"))[2], "status")), "refuted");
}

#[test]
fn integer_quotient_finite_law_instances_preserve_lattice_and_false_keys() {
    let dir = input(
        "integer-finite-law",
        "change setpair(s:State,a:Z,b:Z)=s with{x=2*a+1,y=b};view pair(s:State):(Z,Z)=(s.x,s.y);law optional indexed(s:State,b:Bool) when b:s.y=s.y;",
    );
    let r = execute(
        &dir,
        "out",
        &[
            "s=solve(Pair.total,on=@pair/s,using=Pair.setpair,s=@pair/s)",
            "good=quotient(Pair.pair,on=$s.domain,s=@pair/s,law=Pair.indexed)",
            "bad=quotient(Pair.first,on=$s.domain,s=@pair/s,law=Pair.indexed)",
        ],
    );
    assert_eq!(r.code, 1, "{}", r.stdout);
    let j = result_json(&dir, &r);
    assert_module_owners(&j);
    assert_eq!(s(get(&arr(get(&j, "answers"))[1], "status")), "established");
    let bad = &arr(get(&j, "answers"))[2];
    assert_eq!(s(get(bad, "status")), "refuted");
    let proof = get(node(&j, &arr(get(bad, "counterexamples"))[0]), "value");
    let data = get(proof, "data");
    let views = arr(get(data, "view_values"));
    assert_eq!(
        get(node(&j, &views[0]), "value").value,
        get(node(&j, &views[1]), "value").value
    );
    let laws = arr(get(data, "law_values"));
    assert_ne!(
        get(node(&j, &laws[0]), "value").value,
        get(node(&j, &laws[1]), "value").value
    );
    for reference in laws {
        let rows = arr(get(node(&j, reference), "value"));
        assert_eq!(rows.len(), 2);
        assert_eq!(
            rows.iter().filter(|row| has(&arr(row)[1], "none")).count(),
            1
        );
        assert_eq!(
            rows.iter().filter(|row| has(&arr(row)[1], "some")).count(),
            1
        );
    }
}

#[test]
fn integer_quotient_composed_guard_uses_the_candidate_lattice() {
    let dir = input(
        "integer-composed-guard",
        "change setpair(s:State,a:Z,b:Z) when a+b=1=s with{x=2*a+1,y=2*b};view pair(s:State):(Z,Z)=(s.x,s.y);view combined(s:State):Z=s.x+s.y;law optional indexed(s:State,b:Bool) when (let fixed=s.x+s.y=3 in fixed and b):s.x=s.x;",
    );
    let asks = [
        "s=solve(Pair.total,on=@pair/s,using=Pair.setpair,s=@pair/s)",
        "good=quotient(Pair.pair,on=$s.domain,s=@pair/s,law=Pair.indexed)",
        "bad=quotient(Pair.combined,on=$s.domain,s=@pair/s,law=Pair.indexed)",
    ];
    let r = execute(&dir, "out", &asks);
    assert_eq!(r.code, 1, "{}", r.stdout);
    let j = result_json(&dir, &r);
    assert_module_owners(&j);
    assert_eq!(s(get(&arr(get(&j, "answers"))[1], "status")), "established");
    let bad = &arr(get(&j, "answers"))[2];
    assert_eq!(s(get(bad, "status")), "refuted");
    let proof = get(node(&j, &arr(get(bad, "counterexamples"))[0]), "value");
    let data = get(proof, "data");
    let views = arr(get(data, "view_values"));
    for reference in views {
        assert_eq!(s(get(node(&j, reference), "value")), "3");
    }
    let laws = arr(get(data, "law_values"));
    assert_ne!(
        get(node(&j, &laws[0]), "value").value,
        get(node(&j, &laws[1]), "value").value
    );
}

#[test]
fn integer_conjunction_build_keeps_required_and_optional_equations() {
    let dir = input(
        "integer-conjunction-build",
        "change setpair(s:State,a:Z,b:Z)=s with{x=a,y=b};",
    );
    let r = execute(
        &dir,
        "out",
        &[
            "b=build(Pair,on=@pair/s)",
            "r=repair(Pair.pinned,on=$b.object,using=Pair.setpair)",
            "x=evaluate(Pair.first,on=$r.object,s=@pair/s)",
            "c=check(Pair.pinned,on=$r.object)",
        ],
    );
    assert_eq!(r.code, 0, "{}", r.stdout);
    let j = result_json(&dir, &r);
    let answers = arr(get(&j, "answers"));
    assert!(
        answers
            .iter()
            .all(|answer| s(get(answer, "status")) == "established")
    );
    assert_eq!(
        arr(get(get(output(&j, 0, "algebra"), "value"), "circuits")).len(),
        3
    );
    assert_eq!(s(get(output(&j, 2, "value"), "value")), "0");
}
#[test]
fn quotient_integer_infeasible_guard_preserves_inapplicable_family() {
    let dir = input(
        "integer-infeasible-quotient-guard",
        "change choose(s:State,a:Z,b:Z)=s with{x=a,y=b};law optional inactive(s:State) when 2*s.x=1:s.y=s.y;",
    );
    let r = execute(
        &dir,
        "out",
        &[
            "s=solve(Pair.total,on=@pair/s,using=Pair.choose)",
            "q=quotient(Pair.first,on=$s.domain,s=@pair/s,law=Pair.inactive)",
        ],
    );
    assert_eq!(r.code, 0, "{}", r.stdout);
    let j = result_json(&dir, &r);
    assert_eq!(s(get(&arr(get(&j, "answers"))[1], "status")), "established");
    let q = get(output(&j, 1, "quotient"), "value");
    let descent = get(node(&j, get(q, "descent")), "value");
    let linear = get(node(&j, get(descent, "linear")), "value");
    let family = get(node(&j, get(linear, "target")), "value");
    assert_eq!(num(get(family, "free_rank")), 0);
    let tags = arr(get(node(&j, get(family, "applicability")), "value"));
    assert_eq!(tags.len(), 1);
    assert!(matches!(
        arr(&tags[0])[1].value,
        archsig::json::JValue::Bool(false)
    ));
}
#[test]
fn integer_guarded_quotient_keeps_actual_image_offset_and_binding_order() {
    use archsig::{
        control::Control, input::InputSources, observed::evaluate::evaluate_observed_bytes,
    };
    // Argument order is (b,a), while the state is (x,y)=(a,b).
    let dir = input(
        "integer-conditional-image",
        "change choose(s:State,b:Z,a:Z)=s with{x=a,y=b};view odd(s:State):Z=2*s.x+1;law optional active(s:State) when s.x=1:s.x=s.x;law optional bad(s:State) when s.x=1:s.y=s.y;",
    );
    let sources = InputSources::from_bytes(
        vec![std::fs::read(dir.join("d.json")).unwrap()],
        std::fs::read(dir.join("l.law")).unwrap(),
        std::fs::read(dir.join("a.json")).unwrap(),
    );
    let result = evaluate_observed_bytes(
        sources,
        &[
            "s=solve(Pair.total,on=@pair/s,using=Pair.choose)",
            "q=quotient(Pair.odd,on=$s.domain,s=@pair/s,law=Pair.active)",
            "bad=quotient(Pair.odd,on=$s.domain,s=@pair/s,law=Pair.bad)",
        ],
        &mut Control::unlimited(),
    );
    let Ok(result) = result else {
        panic!("integer conditional quotient must complete")
    };
    let j = archsig::json::parse(result.wire().canonical().as_bytes()).unwrap();
    assert_eq!(s(get(&arr(get(&j, "answers"))[1], "status")), "established");
    let q = get(output(&j, 1, "quotient"), "value");
    let rep = get(q, "representation");
    assert_eq!(coordinates(&j, get(rep, "offset")), vec![1]);
    let d = get(node(&j, get(q, "descent")), "value");
    assert_eq!(s(get(d, "kind")), "guarded_affine");
    assert_eq!(get(d, "coordinates").value, get(rep, "image").value);
    let image = get(node(&j, get(d, "coordinates")), "value");
    let generators = arr(get(image, "generators"));
    assert_eq!(generators.len(), 1);
    assert_eq!(
        s(get(&generators[0], "value"))
            .parse::<i64>()
            .unwrap()
            .abs(),
        2
    );
    let rows = arr(get(d, "instances"));
    assert_eq!(rows.len(), 1);
    let guard = get(&rows[0], "guard");
    let a = integer_columns(&j, get(guard, "linear"));
    let b = coordinates(&j, get(guard, "offset"));
    assert_eq!(a.len(), 1);
    assert_eq!(a[0][0].abs(), 1);
    assert_eq!(b, vec![-1]);
    // The active actual view value is 3. In image coordinates it is 1/a,
    // and lhs/rhs are both 1 there, rather than a map on every integer view.
    let active = 1 / a[0][0];
    assert_eq!(1 + 2 * a[0][0] * active, 3);
    let values = get(&rows[0], "values");
    let values_a = integer_columns(&j, get(values, "linear"));
    let values_b = coordinates(&j, get(values, "offset"));
    assert_eq!(
        values_a[0]
            .iter()
            .zip(values_b)
            .map(|(a, b)| a * active + b)
            .collect::<Vec<_>>(),
        vec![1, 1]
    );
    let bad = &arr(get(&j, "answers"))[2];
    assert_eq!(s(get(bad, "status")), "refuted");
    let proof = get(node(&j, &arr(get(bad, "evidence"))[0]), "value");
    let data = get(proof, "data");
    let points = ["first", "second"].map(|key| arr(get(node(&j, get(data, key)), "value")));
    for point in points {
        assert_eq!(point.len(), 2);
        assert_eq!(s(&point[1]), "1");
    }
    assert_ne!(points[0][0].value, points[1][0].value);
    let views = arr(get(data, "view_values"));
    for view in views {
        assert_eq!(s(get(node(&j, view), "value")), "3");
    }
    let families = arr(get(data, "law_values"));
    assert_ne!(
        get(node(&j, &families[0]), "value").value,
        get(node(&j, &families[1]), "value").value
    );
}

#[test]
fn numeric_conditions_outside_affine_fibers_keep_their_original_unknown_reason() {
    for (case, change, requirement) in [
        (
            "nonlinear-law",
            "change setpair(s:State,a:Z,b:Z)=s with{x=a,y=b};",
            "law required total(s:State):s.x*s.x+s.y=1;",
        ),
        (
            "conditional-law",
            "change setpair(s:State,a:Z,b:Z)=s with{x=a,y=b};",
            "law required total(s:State) when (s.x>0):s.x+s.y=1;",
        ),
        (
            "conditional-law-universal",
            "change setpair(s:State,a:Z,b:Z)=s with{x=a,y=b};",
            "law required total(c:State,z:Z) when (c.x>z):c.x+c.y=1;",
        ),
        (
            "conditional-change",
            "change setpair(s:State,a:Z,b:Z)=if (a>0) then s with{x=a,y=b} else s with{x=b,y=a};",
            "law required total(s:State):s.x+s.y=1;",
        ),
    ] {
        let dir = input(case, change);
        let law = std::fs::read_to_string(dir.join("l.law"))
            .unwrap()
            .replace("law required total(s:State):s.x+s.y=1;", requirement);
        std::fs::write(dir.join("l.law"), &law).unwrap();
        let query = if case.ends_with("universal") {
            "s=solve(Pair.total,using=Pair.setpair,on=@pair/s,c=@pair/s)"
        } else {
            "s=solve(Pair.total,using=Pair.setpair,on=@pair/s,s=@pair/s)"
        };
        if case.starts_with("conditional-") {
            let sources = archsig::input::InputSources::from_bytes(
                vec![std::fs::read(dir.join("d.json")).unwrap()],
                law.as_bytes().to_vec(),
                std::fs::read(dir.join("a.json")).unwrap(),
            );
            let evaluated = archsig::observed::evaluate_observed_bytes(
                sources,
                &[query],
                &mut archsig::control::Control::unlimited(),
            )
            .unwrap();
            let internal = archsig::json::parse(evaluated.wire().canonical().as_bytes()).unwrap();
            let a = &arr(get(&internal, "answers"))[0];
            let reason = arr(get(a, "reasons"))
                .iter()
                .find(|r| s(get(r, "code")) == "unsupported_algorithm")
                .unwrap();
            let source = get(
                node(&internal, &arr(get(reason, "dependencies"))[0]),
                "value",
            );
            assert_eq!(
                get(get(source, "location"), "span"),
                get(get(reason, "location"), "span")
            );
            let span = arr(get(get(source, "location"), "span"));
            let expression = &law[num(&span[0]) as usize..num(&span[1]) as usize];
            assert!(
                expression.contains(if case == "conditional-change" {
                    "a>0"
                } else if case.ends_with("universal") {
                    "c.x>"
                } else {
                    "s.x>"
                }),
                "{expression}"
            );
            let params = arr(get(source, "parameters"));
            assert_eq!(
                params.iter().map(|p| s(get(p, "name"))).collect::<Vec<_>>(),
                if case == "conditional-change" {
                    vec!["a", "b"]
                } else if case.ends_with("universal") {
                    vec!["z"]
                } else {
                    vec![]
                }
            );
            assert!(params.iter().all(|p| s(get(p, "type")) == "Z"));
            assert_eq!(
                s(get(&arr(get(source, "bindings"))[0], "name")),
                if case.ends_with("universal") {
                    "c"
                } else {
                    "s"
                }
            );
        }
        let r = execute(&dir, "out", &[query, "n=needed($s)"]);
        assert_eq!(r.code, 2, "{case}: {}", r.stdout);
        let j = result_json(&dir, &r);
        let a = &arr(get(&j, "answers"))[0];
        let reason = arr(get(a, "reasons"))
            .iter()
            .find(|r| s(get(r, "code")) == "unsupported_algorithm")
            .unwrap();
        assert_eq!(
            s(get(get(reason, "details"), "method")),
            "numeric_change_condition"
        );
        assert!(has(reason, "location"));
        assert!(
            !arr(get(&j, "issues"))
                .iter()
                .any(|r| s(get(r, "code")) == "internal")
        );
    }
}
