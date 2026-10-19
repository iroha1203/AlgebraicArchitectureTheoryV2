#[allow(dead_code)]
#[path = "common/affine_field_chains.rs"]
mod fixture;
use archsig::{
    canonical::Json,
    observed::{
        control::{Control, Limits, Usage},
        evaluate_observed_bytes,
    },
};
fn f<'a>(j: &'a Json, key: &str) -> &'a Json {
    let Json::Obj(xs) = j else { panic!("object") };
    xs.get(key).unwrap_or_else(|| panic!("{key}"))
}
fn arr(j: &Json) -> &[Json] {
    let Json::Arr(xs) = j else { panic!("array") };
    xs
}
fn node<'a>(w: &'a Json, r: &Json) -> &'a Json {
    arr(f(w, "nodes"))
        .iter()
        .find(|n| f(n, "id") == f(r, "node"))
        .unwrap()
}
fn answer<'a>(w: &'a Json, id: &str) -> &'a Json {
    arr(f(w, "answers"))
        .iter()
        .find(|a| f(a, "id") == &Json::str(id))
        .unwrap()
}
fn refs(j: &Json, out: &mut Vec<String>) {
    match j {
        Json::Obj(xs) if xs.len() == 1 && xs.contains_key("node") => {
            let Json::Str(id) = &xs["node"] else { panic!() };
            out.push(id.clone())
        }
        Json::Obj(xs) => {
            for v in xs.values() {
                refs(v, out)
            }
        }
        Json::Arr(xs) => {
            for v in xs {
                refs(v, out)
            }
        }
        _ => {}
    }
}
fn run(
    script: &str,
    number: &str,
    omitted: &[&str],
    revision: &str,
    asks: &[&str],
    status: &str,
) -> Json {
    let input = fixture::input(script, number, omitted, revision);
    let r = evaluate_observed_bytes(
        input.clone(),
        asks,
        &mut Control::new(Limits::default(), |_| Usage::default()),
    )
    .unwrap();
    let w = r.wire();
    assert_eq!(r.status(), status, "{:?}", f(&w, "issues"));
    assert_eq!(r.prepared().inputs().sources(), &input);
    let mut earlier = std::collections::BTreeSet::new();
    for n in arr(f(&w, "nodes")) {
        let mut used = vec![];
        refs(n, &mut used);
        assert!(used.iter().all(|id| earlier.contains(id)));
        let Json::Str(id) = f(n, "id") else { panic!() };
        assert!(earlier.insert(id.clone()));
    }
    w
}
fn claim(w: &Json, id: &str, status: &str) {
    let a = answer(w, id);
    assert_eq!(f(a, "status"), &Json::str(status));
    let c = node(w, f(a, "claim"));
    assert_eq!(f(c, "type"), &Json::str("Proposition"));
    assert_eq!(f(f(c, "judgment"), "status"), f(a, "status"));
    assert_eq!(f(f(c, "judgment"), "evidence"), f(a, "evidence"));
    assert!(!arr(f(a, "evidence")).is_empty());
}
fn evaluations<'a>(w: &'a Json, law: &[u8], text: &str) -> Vec<&'a Json> {
    arr(f(w, "nodes"))
        .iter()
        .filter(|n| f(n, "type") == &Json::str("Evaluation"))
        .filter(|n| {
            let s = node(w, f(f(n, "value"), "expression"));
            let Json::Obj(v) = f(s, "value") else {
                return false;
            };
            let Some(location) = v.get("location") else {
                return false;
            };
            let span = arr(f(location, "span"));
            let (Json::Nat(a), Json::Nat(b)) = (&span[0], &span[1]) else {
                panic!()
            };
            &law[*a as usize..*b as usize] == text.as_bytes()
        })
        .collect()
}
fn zero_residual(w: &Json, id: &str, number: &str) {
    let e = node(w, f(f(answer(w, id), "outputs"), "evaluation"));
    let p = &arr(f(f(e, "value"), "parts"))[0];
    let residual = node(w, f(p, "residual"));
    let value = node(w, f(f(residual, "value"), "value"));
    assert_eq!(f(value, "type"), &Json::str(number));
    assert_eq!(
        f(value, "value"),
        &if number == "Z" {
            Json::str("0")
        } else {
            Json::Arr(vec![Json::str("0"), Json::str("1")])
        }
    );
    let q = &arr(f(f(e, "scope"), "quantifiers"))[0];
    assert_eq!(
        f(q, "name"),
        &Json::str(if number == "Z" { "z" } else { "q" })
    );
    let d = node(w, f(q, "domain"));
    assert_eq!(f(f(d, "value"), "kind"), &Json::str("type"));
    assert_eq!(f(f(d, "value"), "type"), &Json::str(number));
}
#[test]
fn finite_comprehension_inside_all_integer_assignments_keeps_original_derivation() {
    let script = "law required finite(z:Z):z+count(set{x|x in list<Z>[1,2]})=z+2;";
    let w = run(
        script,
        "Z",
        &[],
        "r1",
        &["a=check(Walk.finite)"],
        "complete",
    );
    claim(&w, "a", "established");
    zero_residual(&w, "a", "Z");
    let input = fixture::input(script, "Z", &[], "r1");
    let law = input.law().bytes();
    let cs = evaluations(&w, law, "set{x|x in list<Z>[1,2]}");
    assert_eq!(cs.len(), 1);
    let children = arr(f(&arr(f(f(cs[0], "value"), "parts"))[0], "children"));
    assert_eq!(children.len(), 3);
    let value = node(&w, f(f(cs[0], "value"), "value"));
    assert_eq!(
        f(value, "type"),
        &Json::Arr(vec![Json::str("Set"), Json::str("Z")])
    );
    assert_eq!(
        f(value, "value"),
        &Json::Arr(vec![Json::str("1"), Json::str("2")])
    );
    let count = evaluations(&w, law, "count(set{x|x in list<Z>[1,2]})");
    assert_eq!(count.len(), 1);
    assert_eq!(
        f(node(&w, f(f(count[0], "value"), "value")), "value"),
        &Json::str("2")
    );
    let xs = evaluations(&w, law, "x");
    assert_eq!(xs.len(), 2);
    let got: Vec<_> = xs
        .iter()
        .map(|x| f(node(&w, f(f(x, "value"), "value")), "value").clone())
        .collect();
    assert_eq!(got, vec![Json::str("1"), Json::str("2")]);
}
#[test]
fn finite_explicit_domain_quantification_inside_all_integer_assignments() {
    for (domain, body, expected) in [
        (
            "list<Z>[1,1,2]",
            "x>0",
            vec![Json::str("1"), Json::str("2")],
        ),
        ("set<Z>{2,1}", "x>0", vec![Json::str("1"), Json::str("2")]),
        ("list<Z>[]", "x>0", vec![]),
    ] {
        let script = format!(
            "law required finite(z:Z):z+(if (forall x in {domain} . {body}) then 2 else 3)=z+2;"
        );
        let w = run(
            &script,
            "Z",
            &[],
            "r1",
            &["a=check(Walk.finite)"],
            "complete",
        );
        claim(&w, "a", "established");
        zero_residual(&w, "a", "Z");
        let domains:Vec<_>=arr(f(&w,"nodes")).iter().filter(|n|f(n,"type")==&Json::str("Domain")&&matches!(f(n,"value"),Json::Obj(v)if v.get("kind")==Some(&Json::str("finite")))).collect();
        assert_eq!(domains.len(), 1);
        let elements = arr(f(f(domains[0], "value"), "elements"));
        assert_eq!(elements.len(), expected.len());
        assert_eq!(
            elements
                .iter()
                .map(|r| f(node(&w, r), "value").canonical())
                .collect::<std::collections::BTreeSet<_>>(),
            expected.iter().map(Json::canonical).collect()
        );
        if domain == "list<Z>[1,1,2]" {
            let input = fixture::input(&script, "Z", &[], "r1");
            let es = evaluations(&w, input.law().bytes(), domain);
            assert_eq!(es.len(), 1);
            assert_eq!(
                f(node(&w, f(f(es[0], "value"), "value")), "value"),
                &Json::Arr(vec![Json::str("1"), Json::str("1"), Json::str("2")])
            );
        }
        let exhaust:Vec<_>=arr(f(&w,"nodes")).iter().filter(|n|matches!(f(n,"value"),Json::Obj(v)if v.get("kind")==Some(&Json::str("finite_exhaustion")))).collect();
        assert_eq!(exhaust.len(), 1);
        assert_eq!(
            f(f(f(exhaust[0], "value"), "data"), "checked"),
            &Json::Nat(elements.len() as u64)
        );
        assert_eq!(
            arr(f(f(f(exhaust[0], "value"), "data"), "instances")).len(),
            elements.len()
        );
    }
}
#[test]
fn finite_type_quantifiers_and_empty_existentials_keep_full_domains() {
    for (expr, len, ty) in [
        ("forall b:Bool . b or not b", 2, "Bool"),
        ("forall u:Unit . true", 1, "Unit"),
        ("forall r:Fp(3) . r=r", 3, "Fp(3)"),
        ("not (exists x in list<Z>[] . x>0)", 0, "Z"),
    ] {
        let script = format!("law required finite(z:Z):z+(if ({expr}) then 2 else 3)=z+2;");
        let w = run(
            &script,
            "Z",
            &[],
            "r1",
            &["a=check(Walk.finite)"],
            "complete",
        );
        claim(&w, "a", "established");
        zero_residual(&w, "a", "Z");
        let domains:Vec<_>=arr(f(&w,"nodes")).iter().filter(|n|f(n,"type")==&Json::str("Domain")&&matches!(f(n,"value"),Json::Obj(v)if v.get("kind")==Some(&Json::str("finite")))).collect();
        assert_eq!(domains.len(), 1);
        assert_eq!(
            f(f(domains[0], "value"), "type"),
            &if ty == "Fp(3)" {
                Json::Arr(vec![Json::str("Fp"), Json::str("3")])
            } else {
                Json::str(ty)
            }
        );
        assert_eq!(arr(f(f(domains[0], "value"), "elements")).len(), len);
    }
}
#[test]
fn filtered_duplicate_empty_and_called_comprehensions_keep_exact_integer_and_rational_values() {
    let script = "view parts():Set<Z> =let items=list<Z>[2,1,2,0] in set{x+1|x in items where x>0}; view total():Z=count(parts()); law required finite(z:Z):z+total()=z+2; law required empty(z:Z):z+count(set{x|x in list<Z>[1,2] where false})=z;";
    let w = run(
        script,
        "Z",
        &[],
        "r1",
        &["a=check(Walk.finite)", "empty=check(Walk.empty)"],
        "complete",
    );
    for id in ["a", "empty"] {
        claim(&w, id, "established");
        zero_residual(&w, id, "Z");
    }
    let script = "law required finite(q:Q):q+sum(set{rat(1,2)|x in list<Z>[1,1,2] where x>1})=q+rat(1,2); law required wrong(q:Q):q+sum(set{rat(1,2)|x in list<Z>[1,1,2] where x>1})=q+1;";
    let w = run(
        script,
        "Q",
        &[],
        "r1",
        &["a=check(Walk.finite)", "bad=check(Walk.wrong)"],
        "complete",
    );
    claim(&w, "a", "established");
    zero_residual(&w, "a", "Q");
    claim(&w, "bad", "refuted");
    let bad = node(&w, f(f(answer(&w, "bad"), "outputs"), "evaluation"));
    let part = &arr(f(f(bad, "value"), "parts"))[0];
    let residual = node(&w, f(part, "residual"));
    let value = node(&w, f(f(residual, "value"), "value"));
    assert_eq!(f(value, "type"), &Json::str("Q"));
    assert_eq!(
        f(value, "value"),
        &Json::Arr(vec![Json::str("-1"), Json::str("2")])
    );
    assert!(
        arr(f(&w, "nodes"))
            .iter()
            .any(|n| f(n, "type") == &Json::str("Q")
                && f(n, "value") == &Json::Arr(vec![Json::str("1"), Json::str("2")]))
    );
}
#[test]
fn finite_parts_keep_missing_reasons_nonlinear_boundary_and_independent_results() {
    let script = "view current(n:Node):Bool=forall z:Z . z+sum(set{x+n.mark|x in list<Z>[1,2]})=z+7; view need(b:Bool):Bool=b; law required nonlinear(z:Z):z*z+count(set{x|x in list<Z>[1,2]})=z;";
    let w = run(
        script,
        "Z",
        &["p-mark"],
        "r1",
        &[
            "seed=evaluate(Walk.seed)",
            "prior=check(Walk.prior)",
            "v=evaluate(Walk.current,n=@v/p)",
            "later=evaluate(Walk.need,b=$v.value)",
            "nonlinear=check(Walk.nonlinear)",
        ],
        "partial",
    );
    claim(&w, "prior", "refuted");
    assert_eq!(
        f(
            node(&w, f(f(answer(&w, "seed"), "outputs"), "value")),
            "value"
        ),
        &Json::str("1")
    );
    for id in ["v", "later", "nonlinear"] {
        let a = answer(&w, id);
        assert_eq!(f(a, "status"), &Json::str("undetermined"));
        let Json::Obj(outputs) = f(a, "outputs") else {
            panic!()
        };
        assert!(!outputs.contains_key("value"));
        assert!(
            arr(f(a, "reasons"))
                .iter()
                .any(|r| f(r, "code") == &Json::str("unsupported_algorithm"))
        );
    }
    for id in ["v", "later"] {
        assert!(arr(f(answer(&w, id), "reasons")).iter().any(|r| {
            f(r, "code") == &Json::str("missing_observation")
                && arr(f(r, "missing")).iter().any(|m| {
                    f(m, "snapshot") == &Json::str("v")
                        && f(m, "subject") == &Json::str("p")
                        && f(m, "field") == &Json::str("Paths.Node.mark")
                })
        }));
    }
    assert!(
        arr(f(answer(&w, "later"), "reasons"))
            .iter()
            .any(|r| f(r, "code") == &Json::str("dependency_blocked"))
    );
    assert!(arr(f(&w,"nodes")).iter().flat_map(|n|arr(f(n,"support"))).all(|s|!matches!(s,Json::Obj(v)if v.get("field")==Some(&Json::str("Paths.Node.mark"))&&v.get("subject")==Some(&Json::str("p")))));
}
#[test]
fn finite_subexpressions_preserve_current_observation_provenance() {
    let script =
        "view current(n:Node):Bool=forall z:Z . z+sum(set{x+n.mark|x in list<Z>[1,2]})=z+7;";
    let mut pair = vec![];
    for revision in ["r1", "r2"] {
        let w = run(
            script,
            "Z",
            &[],
            revision,
            &["a=evaluate(Walk.current,n=@v/p)"],
            "complete",
        );
        assert_eq!(f(answer(&w, "a"), "status"), &Json::str("established"));
        assert_eq!(
            f(node(&w, f(f(answer(&w, "a"), "outputs"), "value")), "value"),
            &Json::Bool(true)
        );
        let input = fixture::input(script, "Z", &[], revision);
        let checked = archsig::observed::input::check_inputs(
            input,
            &mut Control::new(Limits::default(), |_| Usage::default()),
        )
        .unwrap();
        let map = checked.archmap();
        let slot = map
            .snapshots
            .iter()
            .find(|s| s.id == "v")
            .unwrap()
            .subjects
            .iter()
            .find(|s| s.id == "p")
            .unwrap()
            .fields
            .iter()
            .find(|f| f.name == "Paths.Node.mark")
            .unwrap();
        let archsig::archmap::Slot::Known { atom, origin, .. } = &slot.slot else {
            panic!()
        };
        assert!(arr(f(&w,"nodes")).iter().flat_map(|n|arr(f(n,"support"))).any(|fact|matches!(fact,Json::Obj(fs)if fs.get("field")==Some(&Json::str("Paths.Node.mark"))&&fs.get("subject")==Some(&Json::str("p"))&&fs.get("atom")==Some(&Json::str(atom)))));
        let origin = map.origins.iter().find(|o| &o.id == origin).unwrap();
        assert!(!origin.locations.is_empty());
        for loc in &origin.locations {
            let src = map.sources.iter().find(|s| s.id == loc.source).unwrap();
            assert_eq!(src.revision, revision);
            assert_eq!(
                loc.span,
                Some(if revision == "r1" { (0, 1) } else { (10, 11) })
            );
        }
        pair.push(w);
    }
    assert_ne!(f(&pair[0], "inputs"), f(&pair[1], "inputs"));
    assert_eq!(f(&pair[0], "answers"), f(&pair[1], "answers"));
    assert_eq!(f(&pair[0], "nodes"), f(&pair[1], "nodes"));
}

#[test]
fn nested_finite_parts_keep_enclosing_local_numeric_binders_and_iteration_captures() {
    for script in [
        "law required finite(z:Z):z+(if (forall u:Z . u+count(set{x|x in list<Z>[1,2]})=u+2) then 2 else 3)=z+2;",
        "view amount():Z=sum(set{sum(set{x+y|y in list<Z>[1,2]})|x in list<Z>[1,2]}); law required finite(z:Z):z+amount()=z+12;",
    ] {
        let w = run(
            script,
            "Z",
            &[],
            "r1",
            &["a=check(Walk.finite)"],
            "complete",
        );
        claim(&w, "a", "established");
        zero_residual(&w, "a", "Z");
    }
}

#[test]
fn finite_quantified_symbolic_bodies_decide_all_assignments_from_actual_cases() {
    for (domain, kind) in [
        ("list<Bool>[true]", "forall"),
        ("list<Bool>[true]", "exists"),
        ("list<Bool>[true,false]", "forall"),
    ] {
        let script = format!(
            "view inner(x:Q):Bool=forall y:Q . x+y=y; law required finite(z:Q):{kind} b in {domain} . inner(z);"
        );
        let w = run(
            &script,
            "Z",
            &[],
            "r1",
            &["a=check(Walk.finite)"],
            "complete",
        );
        claim(&w, "a", "refuted");
        let whole = node(&w, f(f(answer(&w, "a"), "outputs"), "evaluation"));
        let scope = arr(f(f(whole, "scope"), "quantifiers"));
        assert!(scope.iter().any(|q| f(q, "name") == &Json::str("b")
            && matches!(q, Json::Obj(o) if o.contains_key("domain"))));
        let proof = node(&w, &arr(f(whole, "evidence"))[0]);
        assert_eq!(arr(f(f(f(proof, "value"), "data"), "steps")).len(), 1);
    }
}
