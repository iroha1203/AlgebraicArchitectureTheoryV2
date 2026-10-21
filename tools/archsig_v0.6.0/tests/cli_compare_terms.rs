//! 閉じたTermの公開等値を独立三入力から確認する。
mod common;
#[path = "common/public_term_compare.rs"]
mod fixture;
use common::cli::*;
use std::path::{Path, PathBuf};
fn inputs(name: &str) -> PathBuf {
    setup(name, "", false)
}
fn setup(name: &str, extra: &str, missing: bool) -> PathBuf {
    let dir = workdir(name);
    let input = fixture::input(extra, missing, "public-term-comparison");
    for (name, bytes) in [
        ("d.json", input.definitions()[0].bytes()),
        ("l.law", input.law().bytes()),
        ("a.json", input.archmap().bytes()),
    ] {
        std::fs::write(dir.join(name), bytes).unwrap();
    }
    dir
}
fn asks(dir: &Path, qs: &[&str]) -> Run {
    let mut args = vec![
        "run",
        "--atom-definition",
        "d.json",
        "--law",
        "l.law",
        "--archmap",
        "a.json",
        "--out",
        "out",
    ];
    for q in qs {
        args.extend(["--ask", q]);
    }
    run(dir, &args)
}
fn answer<'a>(j: &'a archsig::json::JNode, id: &str) -> &'a archsig::json::JNode {
    arr(get(j, "answers"))
        .iter()
        .find(|a| s(get(a, "id")) == id)
        .unwrap()
}
#[test]
fn finite_and_affine_term_values_compare_by_all_assignments_with_concrete_evidence() {
    let dir = inputs("compare-terms-first");
    let r = asks(
        &dir,
        &[
            "g=evaluate(Terms.observed,s=@v/s)",
            "same=evaluate(Terms.finiteSame)",
            "other=evaluate(Terms.finiteOther)",
            "f=evaluate(Terms.read,s=@v/s)",
            "equiv=evaluate(Terms.affineSame)",
            "shift=evaluate(Terms.affineShift)",
            "slope=evaluate(Terms.affineSlope)",
            "finite_equal=compare($g.value,to=$same.value,kind=value)",
            "finite_different=compare($g.value,to=$other.value,kind=value)",
            "affine_equal=compare($f.value,to=$equiv.value,kind=value)",
            "affine_zero=compare($f.value,to=$shift.value,kind=value)",
            "affine_unit=compare($f.value,to=$slope.value,kind=value)",
        ],
    );
    assert_eq!(r.code, 1, "{}", r.stdout);
    assert_eq!(s(get(&r.receipt, "status")), "complete");
    let j = result_json(&dir, &r);
    for (id, status) in [
        ("finite_equal", "established"),
        ("finite_different", "refuted"),
        ("affine_equal", "established"),
        ("affine_zero", "refuted"),
        ("affine_unit", "refuted"),
    ] {
        let a = answer(&j, id);
        assert_eq!(s(get(a, "status")), status, "{id}");
        assert!(has(get(a, "outputs"), "comparison"));
        assert!(!arr(get(a, "evidence")).is_empty(), "{id}");
    }
    std::fs::remove_dir_all(dir).unwrap();
}

fn node<'a>(j: &'a archsig::json::JNode, r: &archsig::json::JNode) -> &'a archsig::json::JNode {
    arr(get(j, "nodes"))
        .iter()
        .find(|n| get(n, "id") == get(r, "node"))
        .unwrap()
}
fn evidence<'a>(
    j: &'a archsig::json::JNode,
    id: &str,
    kind: &str,
) -> Vec<&'a archsig::json::JNode> {
    arr(get(answer(j, id), "evidence"))
        .iter()
        .map(|r| node(j, r))
        .filter(|n| s(get(get(n, "value"), "kind")) == kind)
        .collect()
}
#[test]
fn term_evidence_retains_the_finite_domain_normal_forms_and_reapplied_zero_unit_points() {
    let dir = inputs("compare-terms-evidence");
    let r = asks(
        &dir,
        &[
            "g=evaluate(Terms.observed,s=@v/s)",
            "same=evaluate(Terms.finiteSame)",
            "other=evaluate(Terms.finiteOther)",
            "f=evaluate(Terms.read,s=@v/s)",
            "equiv=evaluate(Terms.affineSame)",
            "shift=evaluate(Terms.affineShift)",
            "slope=evaluate(Terms.affineSlope)",
            "finite_equal=compare($g.value,to=$same.value,kind=value)",
            "finite_different=compare($g.value,to=$other.value,kind=value)",
            "affine_equal=compare($f.value,to=$equiv.value,kind=value)",
            "affine_zero=compare($f.value,to=$shift.value,kind=value)",
            "affine_unit=compare($f.value,to=$slope.value,kind=value)",
        ],
    );
    assert_eq!(r.code, 1, "{}", r.stdout);
    let j = result_json(&dir, &r);
    for n in arr(get(&j, "nodes")) {
        if !has(n, "value")
            || !has(get(n, "value"), "kind")
            || s(get(get(n, "value"), "kind")) != "counterexample"
        {
            continue;
        }
        let data = get(get(n, "value"), "data");
        for binding in arr(get(data, "bindings")) {
            let archsig::json::JValue::Obj(fields) = &binding.value else {
                panic!("Binding is a record")
            };
            assert_eq!(
                fields
                    .iter()
                    .map(|(name, _)| name.as_str())
                    .collect::<Vec<_>>(),
                ["name", "value"]
            );
            assert!(has(node(&j, get(binding, "value")), "type"));
        }
    }
    let ex = evidence(&j, "finite_equal", "finite_exhaustion");
    assert_eq!(ex.len(), 1);
    let data = get(get(ex[0], "value"), "data");
    assert_eq!(num(get(data, "checked")), 2);
    assert_eq!(arr(get(data, "instances")).len(), 2);
    let domain = get(node(&j, get(data, "domain")), "value");
    assert_eq!(s(get(domain, "type")), "Bool");
    let elements = arr(get(domain, "elements"));
    assert_eq!(elements.len(), 2);
    assert_eq!(
        get(node(&j, &elements[0]), "value"),
        &archsig::json::parse(b"false").unwrap()
    );
    assert_eq!(
        get(node(&j, &elements[1]), "value"),
        &archsig::json::parse(b"true").unwrap()
    );
    let norms = evidence(&j, "affine_equal", "normalization");
    assert_eq!(norms.len(), 2);
    let expected = archsig::json::parse(br#"[[["0","0"],["0",["2","-1"]]]]"#).unwrap();
    for e in norms {
        let data = get(get(e, "value"), "data");
        assert_eq!(get(node(&j, get(data, "after")), "value"), &expected);
        let steps = arr(get(data, "steps"));
        assert_eq!(steps.len(), 1);
        let step = node(&j, &steps[0]);
        assert_eq!(s(get(step, "type")), "Expression");
        assert_eq!(s(get(get(step, "value"), "operation")), "equal");
    }
    for (id, expected_bindings, left, right) in [
        ("affine_zero", vec!["0", "0"], "0", "1"),
        ("affine_unit", vec!["0", "1"], "-1", "-2"),
    ] {
        let es = evidence(&j, id, "counterexample");
        assert_eq!(es.len(), 1);
        let data = get(get(es[0], "value"), "data");
        let bindings = arr(get(data, "bindings"));
        assert_eq!(bindings.len(), 2);
        for (binding, value) in bindings.iter().zip(expected_bindings) {
            assert_eq!(s(get(node(&j, get(binding, "value")), "value")), value);
            assert_eq!(s(get(node(&j, get(binding, "value")), "type")), "Z");
        }
        assert_eq!(s(get(node(&j, get(data, "left")), "value")), left);
        assert_eq!(s(get(node(&j, get(data, "right")), "value")), right);
    }
    let finite = evidence(&j, "finite_different", "counterexample");
    assert!(finite.iter().any(|e| {
        let data = get(get(e, "value"), "data");
        let bindings = arr(get(data, "bindings"));
        bindings.len() == 1
            && get(node(&j, get(&bindings[0], "value")), "value")
                == &archsig::json::parse(b"true").unwrap()
    }));
    std::fs::remove_dir_all(dir).unwrap();
}
#[test]
fn nested_term_values_and_term_returning_terms_use_extensional_equality() {
    let dir = inputs("compare-terms-nested");
    let r = asks(
        &dir,
        &[
            "packed=evaluate(Terms.packed,s=@v/s)",
            "same=evaluate(Terms.packedSame)",
            "other=evaluate(Terms.packedOther)",
            "same_pack=compare($packed.value,to=$same.value,kind=value)",
            "different_pack=compare($packed.value,to=$other.value,kind=value)",
            "h=evaluate(Terms.higherLeft)",
            "h_same=evaluate(Terms.higherSame)",
            "h_other=evaluate(Terms.higherOther)",
            "higher_same=compare($h.value,to=$h_same.value,kind=value)",
            "higher_other=compare($h.value,to=$h_other.value,kind=value)",
        ],
    );
    assert_eq!(r.code, 1, "{}", r.stdout);
    assert_eq!(s(get(&r.receipt, "status")), "complete");
    let j = result_json(&dir, &r);
    for (id, status) in [
        ("same_pack", "established"),
        ("different_pack", "refuted"),
        ("higher_same", "established"),
        ("higher_other", "refuted"),
    ] {
        assert_eq!(s(get(answer(&j, id), "status")), status, "{id}");
        assert!(!arr(get(answer(&j, id), "evidence")).is_empty());
    }
    std::fs::remove_dir_all(dir).unwrap();
}
#[test]
fn unsupported_nonlinear_equality_missing_terms_and_a_structural_refutation_remain_distinct() {
    let dir = setup("compare-terms-unsupported", "", true);
    let r = asks(
        &dir,
        &[
            "n=evaluate(Terms.nonlinear)",
            "m=evaluate(Terms.nonlinearSame)",
            "self_equal=compare($n.value,to=$n.value,kind=value)",
            "opaque=compare($n.value,to=$m.value,kind=value)",
            "a=evaluate(Terms.opaqueLeft)",
            "b=evaluate(Terms.opaqueOther)",
            "known_difference=compare($a.value,to=$b.value,kind=value)",
            "g=evaluate(Terms.observed,s=@v/s)",
            "same=evaluate(Terms.finiteSame)",
            "missing=compare($g.value,to=$same.value,kind=value)",
            "opaque_plan=needed($opaque)",
            "missing_plan=needed($missing)",
        ],
    );
    assert_eq!(r.code, 2, "{}", r.stdout);
    assert_eq!(s(get(&r.receipt, "status")), "partial");
    let j = result_json(&dir, &r);
    for (id, status) in [
        ("self_equal", "established"),
        ("opaque", "undetermined"),
        ("known_difference", "refuted"),
        ("missing", "undetermined"),
        ("opaque_plan", "established"),
        ("missing_plan", "established"),
    ] {
        assert_eq!(s(get(answer(&j, id), "status")), status, "{id}");
    }
    let reasons = arr(get(answer(&j, "opaque"), "reasons"));
    assert!(reasons
        .iter()
        .any(|r| s(get(r, "code")) == "unsupported_algorithm"));
    assert!(has(get(answer(&j, "opaque"), "outputs"), "comparison"));
    assert!(arr(get(answer(&j, "known_difference"), "reasons")).is_empty());
    assert!(arr(get(answer(&j, "missing"), "reasons"))
        .iter()
        .any(|r| s(get(r, "code")) == "missing_observation"));
    std::fs::remove_dir_all(dir).unwrap();
}
#[test]
fn finite_term_domains_are_exhausted_for_zero_unit_fp_data_tuple_and_multiple_parameters() {
    let dir = setup(
        "compare-terms-finite-domains",
        r#"
view zeroLeft():Term<()->Z> = fn()=>3;
view zeroRight():Term<()->Z> = fn()=>1+2;
view unitLeft():Term<(Unit)->Q> = fn(u:Unit)=>rat(1,2);
view unitRight():Term<(Unit)->Q> = fn(v:Unit)=>rat(2,4);
view fpLeft():Term<(Fp(3))->Fp(3)> = fn(x:Fp(3))=>x+x;
view fpRight():Term<(Fp(3))->Fp(3)> = fn(y:Fp(3))=>2*y;
view dataLeft():Term<(Flag)->Z> = fn(x:Flag)=>match x {Off=>0;On(b)=>if b then 1 else 2;};
view dataRight():Term<(Flag)->Z> = fn(y:Flag)=>match y {Off=>1-1;On(c)=>if not c then 2 else 1;};
view tupleLeft():Term<((Bool,Option<Unit>,Set<Unit>))->Z> = fn(t:(Bool,Option<Unit>,Set<Unit>))=>(if t.0 then 1 else 0)+(if t.1=some(unit) then 2 else 0)+count(t.2);
view tupleRight():Term<((Bool,Option<Unit>,Set<Unit>))->Z> = fn(u:(Bool,Option<Unit>,Set<Unit>))=>count(u.2)+(if u.1=some(unit) then 2 else 0)+(if u.0 then 1 else 0);
view multiLeft():Term<(Bool,Option<Unit>,Set<Unit>)->Z> = fn(b:Bool,o:Option<Unit>,s:Set<Unit>)=>(if b then 1 else 0)+(if o=some(unit) then 2 else 0)+count(s);
view multiRight():Term<(Bool,Option<Unit>,Set<Unit>)->Z> = fn(x:Bool,y:Option<Unit>,z:Set<Unit>)=>count(z)+(if y=some(unit) then 2 else 0)+(if x then 1 else 0);
"#,
        false,
    );
    let mut qs = vec![];
    for name in ["zero", "unit", "fp", "data", "tuple", "multi"] {
        qs.push(format!("{name}_left=evaluate(Terms.{name}Left)"));
        qs.push(format!("{name}_right=evaluate(Terms.{name}Right)"));
        qs.push(format!(
            "{name}_cmp=compare(${name}_left.value,to=${name}_right.value,kind=value)"
        ));
    }
    let r = asks(&dir, &qs.iter().map(String::as_str).collect::<Vec<_>>());
    assert_eq!(r.code, 0, "{}", r.stdout);
    let j = result_json(&dir, &r);
    for (name, size) in [
        ("zero", 1),
        ("unit", 1),
        ("fp", 3),
        ("data", 3),
        ("tuple", 8),
        ("multi", 8),
    ] {
        let id = format!("{name}_cmp");
        assert_eq!(s(get(answer(&j, &id), "status")), "established");
        let es = evidence(&j, &id, "finite_exhaustion");
        assert_eq!(es.len(), 1);
        let data = get(get(es[0], "value"), "data");
        assert_eq!(num(get(data, "checked")), size);
        assert_eq!(arr(get(data, "instances")).len() as u64, size);
        for r in arr(get(data, "instances")) {
            assert_eq!(
                s(get(get(node(&j, r), "judgment"), "status")),
                "established"
            );
        }
        let domain = get(node(&j, get(data, "domain")), "value");
        assert_eq!(arr(get(domain, "elements")).len() as u64, size);
    }
    std::fs::remove_dir_all(dir).unwrap();
}
#[test]
fn affine_terms_use_exact_q_coefficients_and_finite_times_tuple_axes() {
    let dir = setup(
        "compare-terms-affine-axes",
        r#"
view mixedLeft():Term<(Bool,Z)->Z> = fn(b:Bool,x:Z)=>if b then x+x else x+1;
view mixedRight():Term<(Bool,Z)->Z> = fn(c:Bool,y:Z)=>if not c then 1+y else 2*y;
view tupleLeft():Term<((Z,Q))->(Z,Q)> = fn(t:(Z,Q))=>(t.0+t.0,t.1+rat(1,2)+rat(1,2));
view tupleRight():Term<((Z,Q))->(Z,Q)> = fn(u:(Z,Q))=>(2*u.0,u.1+1);
view tupleOther():Term<((Z,Q))->(Z,Q)> = fn(u:(Z,Q))=>(2*u.0,2*u.1+1);
view bigLeft():Term<(Z)->Z> = fn(x:Z)=>1234567890123456789012345678901234567890*x+1;
view bigRight():Term<(Z)->Z> = fn(y:Z)=>y*1234567890123456789012345678901234567889+y+1;
"#,
        false,
    );
    let r = asks(
        &dir,
        &[
            "q=evaluate(Terms.rationalLeft)",
            "q_same=evaluate(Terms.rationalSame)",
            "q_other=evaluate(Terms.rationalOther)",
            "q_equal=compare($q.value,to=$q_same.value,kind=value)",
            "q_difference=compare($q.value,to=$q_other.value,kind=value)",
            "m=evaluate(Terms.mixedLeft)",
            "mr=evaluate(Terms.mixedRight)",
            "mixed=compare($m.value,to=$mr.value,kind=value)",
            "t=evaluate(Terms.tupleLeft)",
            "tr=evaluate(Terms.tupleRight)",
            "tx=evaluate(Terms.tupleOther)",
            "tuple_equal=compare($t.value,to=$tr.value,kind=value)",
            "tuple_difference=compare($t.value,to=$tx.value,kind=value)",
            "b=evaluate(Terms.bigLeft)",
            "br=evaluate(Terms.bigRight)",
            "big=compare($b.value,to=$br.value,kind=value)",
        ],
    );
    assert_eq!(r.code, 1, "{}", r.stdout);
    let j = result_json(&dir, &r);
    for (id, status) in [
        ("q_equal", "established"),
        ("q_difference", "refuted"),
        ("mixed", "established"),
        ("tuple_equal", "established"),
        ("tuple_difference", "refuted"),
        ("big", "established"),
    ] {
        assert_eq!(s(get(answer(&j, id), "status")), status, "{id}");
        assert_eq!(evidence(&j, id, "normalization").len(), 2);
    }
    let e = evidence(&j, "q_difference", "counterexample");
    let data = get(get(e[0], "value"), "data");
    assert_eq!(
        get(node(&j, get(data, "left")), "value"),
        &archsig::json::parse(br#"["5","6"]"#).unwrap()
    );
    assert_eq!(
        get(node(&j, get(data, "right")), "value"),
        &archsig::json::parse(br#"["1","1"]"#).unwrap()
    );
    let e = evidence(&j, "tuple_difference", "counterexample");
    let data = get(get(e[0], "value"), "data");
    let bs = arr(get(data, "bindings"));
    assert_eq!(bs.len(), 1);
    assert_eq!(
        get(node(&j, get(&bs[0], "value")), "value"),
        &archsig::json::parse(br#"["0",["1","1"]]"#).unwrap()
    );
    std::fs::remove_dir_all(dir).unwrap();
}
#[test]
fn term_dynamic_projections_keep_actual_types_conditions_and_needed_separate() {
    let dir=setup("compare-terms-dynamic","view dynamic():FnBox=Wrap(fn(b:Bool)=>if b then 4 else 9); view plain():FnBox=Plain(false); view vacant():FnBox=Vacant; view dynNo():Bool=false;",false);
    let r = asks(
        &dir,
        &[
            "d=evaluate(Terms.dynamic)",
            "b=evaluate(Terms.plain)",
            "e=evaluate(Terms.vacant)",
            "s=evaluate(Terms.finiteSame)",
            "n=evaluate(Terms.dynNo)",
            "left=compare($d.value[0],to=$s.value,kind=value)",
            "right=compare($s.value,kind=value,to=$d.value[0])",
            "both=compare($d.value[0],to=$d.value[0],kind=value)",
            "mismatch=compare($d.value[0],to=$b.value[0],kind=value)",
            "branch=compare($b.value[0],to=$s.value,kind=value)",
            "absent=compare($e.value[0],to=$s.value,kind=value)",
            "boolean=compare($b.value[0],to=$n.value,kind=value)",
            "needed=needed($mismatch)",
            "absent_plan=needed($absent)",
        ],
    );
    assert_eq!(r.code, 2, "{}", r.stdout);
    let j = result_json(&dir, &r);
    for id in ["left", "right", "both", "boolean", "needed", "absent_plan"] {
        assert_eq!(s(get(answer(&j, id), "status")), "established", "{id}");
    }
    for id in ["mismatch", "branch", "absent"] {
        let a = answer(&j, id);
        assert_eq!(s(get(a, "status")), "undetermined");
        assert!(!has(get(a, "outputs"), "comparison"));
        for reason in ["condition_failed", "dependency_blocked"] {
            assert!(
                arr(get(a, "reasons"))
                    .iter()
                    .any(|r| s(get(r, "code")) == reason),
                "{id} {reason}"
            );
        }
    }
    std::fs::remove_dir_all(dir).unwrap();
}
#[test]
fn term_static_signature_mismatches_are_usage_errors_without_published_results() {
    for (name, extra, query) in [
        (
            "arity",
            "view x():Term<(Bool,Bool)->Z> =fn(a:Bool,b:Bool)=>0;",
            "c=compare($l.value,to=$x.value,kind=value)",
        ),
        (
            "return",
            "view x():Term<(Bool)->Bool> =fn(a:Bool)=>a;",
            "c=compare($l.value,to=$x.value,kind=value)",
        ),
        (
            "ground",
            "view x():Bool=false;",
            "c=compare($l.value,to=$x.value,kind=value)",
        ),
    ] {
        let dir = setup(&format!("compare-terms-signature-{name}"), extra, false);
        let r = asks(
            &dir,
            &["l=evaluate(Terms.finiteSame)", "x=evaluate(Terms.x)", query],
        );
        assert_eq!(r.code, 64, "{}", r.stdout);
        assert!(!has(&r.receipt, "result"));
        assert!(!dir.join("out").exists());
        assert!(!arr(get(&r.receipt, "issues")).is_empty());
        std::fs::remove_dir_all(dir).unwrap();
    }
}
#[test]
fn reused_term_proofs_reject_mutations_and_recompute_current_terms() {
    let dir = inputs("compare-terms-reuse");
    let qs = [
        "g=evaluate(Terms.observed,s=@v/s)",
        "s=evaluate(Terms.finiteSame)",
        "c=compare($g.value,to=$s.value,kind=value)",
        "f=evaluate(Terms.read,s=@v/s)",
        "a=evaluate(Terms.affineSame)",
        "affine=compare($f.value,to=$a.value,kind=value)",
    ];
    let r = asks(&dir, &qs);
    assert_eq!(r.code, 0, "{}", r.stdout);
    let original = result_json(&dir, &r);
    let path = dir.join(s(get(&r.receipt, "result")));
    let raw = std::fs::read_to_string(&path).unwrap();
    for (i, (from, to)) in [
        ("\"checked\":2", "\"checked\":1"),
        ("\"kind\":\"normalization\"", "\"kind\":\"counterexample\""),
        ("\"kind\":\"value\"", "\"kind\":\"word\""),
    ]
    .iter()
    .enumerate()
    {
        let forged = raw.replace(from, to);
        assert_ne!(forged, raw);
        std::fs::write(&path, forged).unwrap();
        let out = format!("again{i}");
        let mut args = vec![
            "run",
            "--atom-definition",
            "d.json",
            "--law",
            "l.law",
            "--archmap",
            "a.json",
            "--out",
            out.as_str(),
            "--reuse",
            "out",
        ];
        for q in qs {
            args.extend(["--ask", q]);
        }
        let r = run(&dir, &args);
        assert_eq!(r.code, 0, "{}", r.stdout);
        let j = result_json(&dir, &r);
        assert_eq!(num(get(get(&j, "reuse"), "accepted_nodes")), 0);
        assert!(!arr(get(get(&j, "reuse"), "rejected")).is_empty());
        assert_eq!(get(&j, "answers"), get(&original, "answers"));
        assert_eq!(get(&j, "nodes"), get(&original, "nodes"));
    }
    std::fs::write(&path, &raw).unwrap();
    let mut args = vec![
        "run",
        "--atom-definition",
        "d.json",
        "--law",
        "l.law",
        "--archmap",
        "a.json",
        "--out",
        "valid",
        "--reuse",
        "out",
    ];
    for q in qs {
        args.extend(["--ask", q]);
    }
    let r = run(&dir, &args);
    assert_eq!(r.code, 0, "{}", r.stdout);
    let j = result_json(&dir, &r);
    assert_eq!(get(&j, "answers"), get(&original, "answers"));
    let map = std::fs::read_to_string(dir.join("a.json")).unwrap();
    std::fs::write(
        dir.join("a.json"),
        map.replace("if b then 4 else 9", "if b then 5 else 9"),
    )
    .unwrap();
    args[8] = "changed";
    let r = run(&dir, &args);
    assert_eq!(r.code, 1, "{}", r.stdout);
    let j = result_json(&dir, &r);
    assert_eq!(s(get(answer(&j, "c"), "status")), "refuted");
    assert_eq!(num(get(get(&j, "reuse"), "accepted_nodes")), 0);
    std::fs::remove_dir_all(dir).unwrap();
}
#[test]
fn malformed_observed_terms_are_invalid_inputs_with_concrete_stdout_issues() {
    for (name, from, to) in [
        ("return", "if b then 4 else 9", "if b then true else false"),
        ("free", "if b then 4 else 9", "if missingName then 4 else 9"),
    ] {
        let dir = inputs(&format!("compare-terms-invalid-{name}"));
        let map = std::fs::read_to_string(dir.join("a.json")).unwrap();
        assert!(map.contains(from));
        std::fs::write(dir.join("a.json"), map.replace(from, to)).unwrap();
        let r = asks(
            &dir,
            &[
                "g=evaluate(Terms.observed,s=@v/s)",
                "c=compare($g.value,to=$g.value,kind=value)",
            ],
        );
        assert_eq!(r.code, 65, "{}", r.stdout);
        assert_eq!(s(get(&r.receipt, "status")), "invalid");
        assert!(!arr(get(&r.receipt, "issues")).is_empty());
        assert!(!has(&r.receipt, "result"));
        assert!(!dir.join("out").exists());
        std::fs::remove_dir_all(dir).unwrap();
    }
}
