//! 元Termのアフィン全域と実引数の相関を三入力bytesから確認する。
#[path = "common/affine_terms.rs"]
mod fixture;
use archsig::{
    canonical::Json,
    definition::check_definitions,
    observed::{
        control::{Control, Limits, Usage},
        evaluate_observed_bytes,
        input::InputSources,
    },
};
fn quiet() -> Control {
    Control::new(Limits::default(), |_| Usage::default())
}
fn sources() -> InputSources {
    sources_at("r1")
}
fn sources_at(revision: &str) -> InputSources {
    let defs = fixture::definitions();
    let d = check_definitions(&[("definition0", defs.as_bytes())]).unwrap();
    let digest = &d.vocabularies["Terms"].digest;
    InputSources::from_bytes(
        vec![defs.into_bytes()],
        fixture::law(digest).into_bytes(),
        fixture::archmap(digest, revision).into_bytes(),
    )
}
fn get<'a>(j: &'a Json, k: &str) -> &'a Json {
    let Json::Obj(m) = j else { panic!("object") };
    &m[k]
}
fn arr(j: &Json) -> &[Json] {
    let Json::Arr(a) = j else { panic!("array") };
    a
}
fn answer<'a>(w: &'a Json, id: &str) -> &'a Json {
    arr(get(w, "answers"))
        .iter()
        .find(|a| get(a, "id") == &Json::str(id))
        .unwrap()
}
fn value<'a>(w: &'a Json, id: &str) -> &'a Json {
    let a = answer(w, id);
    assert_eq!(get(a, "status"), &Json::str("established"), "{a:?}");
    let r = get(get(get(a, "outputs"), "value"), "node");
    let n = arr(get(w, "nodes"))
        .iter()
        .find(|n| get(n, "id") == r)
        .unwrap();
    get(n, "value")
}
#[test]
fn affine_terms_compare_original_integer_rational_tuple_and_mixed_domains() {
    let r = evaluate_observed_bytes(
        sources(),
        &[
            "e=evaluate(Terms.same,s=@v/s)",
            "d=evaluate(Terms.different,s=@v/s)",
            "q=evaluate(Terms.rational)",
            "t=evaluate(Terms.tuple)",
            "m=evaluate(Terms.mixed)",
            "p=check(Terms.equality,s=@v/s)",
            "c=check(Terms.unequal,s=@v/s)",
        ],
        &mut quiet(),
    )
    .unwrap();
    assert_eq!(r.status(), "complete", "{:?}", get(&r.wire(), "issues"));
    let w = r.wire();
    for id in ["e", "d", "q", "t", "m"] {
        assert_eq!(value(&w, id), &Json::Bool(true));
    }
    assert_eq!(get(answer(&w, "p"), "status"), &Json::str("established"));
    assert_eq!(get(answer(&w, "c"), "status"), &Json::str("refuted"));
}
#[test]
fn affine_terms_reapply_coefficient_counterexamples_and_keep_tuple_and_finite_body_operations() {
    let r = evaluate_observed_bytes(
        sources(),
        &[
            "z=evaluate(Terms.coefficient,s=@v/s)",
            "q=evaluate(Terms.qCoefficient)",
            "t=evaluate(Terms.tupleCoefficient)",
            "a=evaluate(Terms.tupleArithmetic)",
            "s=evaluate(Terms.aggregation)",
            "f=evaluate(Terms.finiteBody)",
        ],
        &mut quiet(),
    )
    .unwrap();
    assert_eq!(r.status(), "complete", "{:?}", get(&r.wire(), "issues"));
    let w = r.wire();
    for id in ["z", "q", "t", "a", "s", "f"] {
        assert_eq!(value(&w, id), &Json::Bool(true));
    }
}
#[test]
fn affine_term_application_keeps_original_missing_slots_and_cancels_only_shared_symbols() {
    let r = evaluate_observed_bytes(
        sources(),
        &[
            "a=evaluate(Terms.cancel,s=@v/s)",
            "d=evaluate(Terms.delta,s=@v/s)",
            "i=evaluate(Terms.cancelEquality,s=@v/s)",
            "x=evaluate(Terms.independent,s=@v/s)",
            "q=evaluate(Terms.qcancel,s=@v/s)",
            "t=evaluate(Terms.tupleCancel,s=@v/s)",
        ],
        &mut quiet(),
    )
    .unwrap();
    assert_eq!(r.status(), "partial");
    let w = r.wire();
    assert_eq!(value(&w, "a"), &Json::str("0"));
    assert_eq!(value(&w, "d"), &Json::str("2"));
    assert_eq!(value(&w, "i"), &Json::Bool(true));
    assert_eq!(
        value(&w, "q"),
        &Json::Arr(vec![Json::str("0"), Json::str("1")])
    );
    assert_eq!(
        value(&w, "t"),
        &Json::Arr(vec![
            Json::str("0"),
            Json::Arr(vec![Json::str("0"), Json::str("1")])
        ])
    );
    let a = answer(&w, "x");
    assert_eq!(get(a, "status"), &Json::str("undetermined"));
    for field in ["Terms.Sample.h", "Terms.Sample.k"] {
        assert!(
            arr(get(a, "reasons"))
                .iter()
                .flat_map(|r| arr(get(r, "missing")))
                .any(|m| get(m, "field") == &Json::str(field))
        );
    }
}
#[test]
fn affine_term_application_connects_implicit_and_explicit_original_universal_parameters() {
    let r = evaluate_observed_bytes(
        sources(),
        &[
            "p=check(Terms.universal,s=@v/s)",
            "q=evaluate(Terms.explicit,s=@v/s)",
        ],
        &mut quiet(),
    )
    .unwrap();
    assert_eq!(r.status(), "complete", "{:?}", get(&r.wire(), "issues"));
    let w = r.wire();
    assert_eq!(get(answer(&w, "p"), "status"), &Json::str("established"));
    assert_eq!(value(&w, "q"), &Json::Bool(true));
}
#[test]
fn nonlinear_terms_keep_typed_algorithm_obligations_and_exact_concrete_or_finite_values() {
    let r = evaluate_observed_bytes(
        sources(),
        &[
            "o=evaluate(Terms.opaque)",
            "t=evaluate(Terms.opaqueText)",
            "m=evaluate(Terms.opaqueMissing,s=@v/s)",
            "n=evaluate(Terms.concreteNonlinear)",
            "f=evaluate(Terms.finiteNonlinear)",
            "u=check(Terms.outside,s=@v/s)",
        ],
        &mut quiet(),
    )
    .unwrap();
    assert_eq!(r.status(), "partial");
    let w = r.wire();
    assert_eq!(value(&w, "n"), &Json::str("9"));
    assert_eq!(value(&w, "f"), &Json::Bool(true));
    for id in ["o", "t", "m", "u"] {
        let a = answer(&w, id);
        assert_eq!(get(a, "status"), &Json::str("undetermined"));
        assert!(
            arr(get(a, "reasons"))
                .iter()
                .any(|r| get(r, "code") == &Json::str("unsupported_algorithm")),
            "{a:?}"
        );
        let Json::Obj(outputs) = get(a, "outputs") else {
            panic!("outputs")
        };
        assert!(!outputs.contains_key("value"));
    }
    assert!(
        arr(get(answer(&w, "m"), "reasons"))
            .iter()
            .flat_map(|r| arr(get(r, "missing")))
            .any(|m| get(m, "field") == &Json::str("Terms.Sample.h"))
    );
    assert!(!format!("{:?}", get(&w, "issues")).contains("internal"));
    for id in ["o", "t", "m", "u"] {
        let r = arr(get(answer(&w, id), "reasons"))
            .iter()
            .find(|r| get(r, "code") == &Json::str("unsupported_algorithm"))
            .unwrap();
        assert!(!arr(get(get(r, "details"), "operand_types")).is_empty());
        assert!(!arr(get(r, "dependencies")).is_empty());
        assert_eq!(get(get(r, "location"), "input"), &Json::str("law"));
    }
    let domains: Vec<_> = arr(get(&w, "nodes"))
        .iter()
        .filter(|n| {
            get(n, "type") == &Json::str("Domain")
                && get(get(n, "value"), "kind") == &Json::str("type")
                && get(get(n, "value"), "type") == &Json::str("Z")
        })
        .collect();
    assert!(!domains.is_empty());
    let descriptors = arr(get(get(answer(&w, "u"), "scope"), "quantifiers"));
    assert!(descriptors.iter().any(|q| {
        let Json::Obj(q) = q else {
            panic!("quantifier")
        };
        q.get("domain")
            .is_some_and(|r| domains.iter().any(|d| get(d, "id") == get(r, "node")))
    }));
}
fn value_node<'a>(w: &'a Json, id: &str) -> &'a Json {
    let r = get(get(get(answer(w, id), "outputs"), "value"), "node");
    arr(get(w, "nodes"))
        .iter()
        .find(|n| get(n, "id") == r)
        .unwrap()
}
fn audit_current_sources(r: &archsig::observed::ObservedEvaluation, revision: &str) {
    let w = r.wire();
    let inputs = r.prepared().inputs();
    let ns = arr(get(&w, "nodes"));
    fn refs(j: &Json, out: &mut Vec<String>) {
        match j {
            Json::Obj(m) => {
                if let Some(Json::Str(id)) = m.get("node") {
                    out.push(id.clone())
                }
                for v in m.values() {
                    refs(v, out)
                }
            }
            Json::Arr(a) => {
                for v in a {
                    refs(v, out)
                }
            }
            _ => {}
        }
    }
    for (index, n) in ns.iter().enumerate() {
        let Json::Obj(m) = n else { panic!("node") };
        assert!(get(n, "type") == &Json::str("Proposition") || !m.contains_key("judgment"));
        let mut references = Vec::new();
        for (k, v) in m {
            if k != "id" {
                refs(v, &mut references)
            }
        }
        for id in references {
            assert!(ns[..index].iter().any(|n| get(n, "id") == &Json::str(&id)))
        }
        for fact in arr(get(n, "support")) {
            let (Json::Str(snapshot), Json::Str(subject)) =
                (get(fact, "snapshot"), get(fact, "subject"))
            else {
                panic!("fact")
            };
            let sub = inputs
                .archmap()
                .snapshots
                .iter()
                .find(|s| s.id == *snapshot)
                .unwrap()
                .subjects
                .iter()
                .find(|s| s.id == *subject)
                .unwrap();
            let Json::Obj(f) = fact else { panic!("fact") };
            let origin = if let Some(Json::Str(field)) = f.get("field") {
                let slot = &sub.fields.iter().find(|f| f.name == *field).unwrap().slot;
                let archsig::archmap::Slot::Known { atom, origin, .. } = slot else {
                    panic!("known support")
                };
                assert_eq!(get(fact, "atom"), &Json::str(atom));
                origin
            } else {
                &sub.origin
            };
            let origin = inputs
                .archmap()
                .origins
                .iter()
                .find(|o| o.id == *origin)
                .unwrap();
            assert!(!origin.locations.is_empty());
            for l in &origin.locations {
                let source = inputs
                    .archmap()
                    .sources
                    .iter()
                    .find(|s| s.id == l.source)
                    .unwrap();
                assert_eq!(source.uri, "urn:fixture:terms");
                assert_eq!(source.revision, revision);
            }
        }
    }
}
#[test]
fn affine_term_provenance_pair_preserves_mathematical_types_values_inputs_and_current_sources() {
    let asks = [
        "e=evaluate(Terms.same,s=@v/s)",
        "a=evaluate(Terms.cancel,s=@v/s)",
        "q=evaluate(Terms.qcancel,s=@v/s)",
        "t=evaluate(Terms.tupleCancel,s=@v/s)",
        "p=check(Terms.universal,s=@v/s)",
    ];
    let src = sources_at("r1");
    let before = archsig::observed::input::check_inputs(src.clone(), &mut quiet()).unwrap();
    let a = evaluate_observed_bytes(src, &asks, &mut quiet()).unwrap();
    let b = evaluate_observed_bytes(sources_at("r2"), &asks, &mut quiet()).unwrap();
    let (aw, bw) = (a.wire(), b.wire());
    assert_eq!(a.status(), "complete");
    assert_eq!(b.status(), "complete");
    assert_eq!(get(&aw, "answers"), get(&bw, "answers"));
    for (id, ty) in [
        ("e", Json::str("Bool")),
        ("a", Json::str("Z")),
        ("q", Json::str("Q")),
        (
            "t",
            Json::Arr(vec![Json::str("Tuple"), Json::str("Z"), Json::str("Q")]),
        ),
    ] {
        assert_eq!(value(&aw, id), value(&bw, id));
        for w in [&aw, &bw] {
            assert_eq!(get(value_node(w, id), "type"), &ty);
        }
    }
    assert_eq!(value(&aw, "e"), &Json::Bool(true));
    assert_eq!(value(&aw, "a"), &Json::str("0"));
    assert_eq!(
        value(&aw, "q"),
        &Json::Arr(vec![Json::str("0"), Json::str("1")])
    );
    assert_eq!(get(answer(&aw, "p"), "status"), &Json::str("established"));
    assert_ne!(
        a.prepared().inputs().metadata_wire(),
        b.prepared().inputs().metadata_wire()
    );
    assert_eq!(
        format!("{:?}", before.definitions()),
        format!("{:?}", a.prepared().inputs().definitions())
    );
    assert_eq!(
        format!("{:?}", before.law()),
        format!("{:?}", a.prepared().inputs().law())
    );
    assert_eq!(
        format!("{:?}", before.archmap()),
        format!("{:?}", a.prepared().inputs().archmap())
    );
    assert_eq!(before.sources(), a.prepared().inputs().sources());
    audit_current_sources(&a, "r1");
    audit_current_sources(&b, "r2");
}
#[test]
fn affine_term_missing_callee_keeps_original_slots_without_a_default_program() {
    let src = sources();
    let before = archsig::observed::input::check_inputs(src.clone(), &mut quiet()).unwrap();
    let r = evaluate_observed_bytes(src, &["m=evaluate(Terms.needMissing,s=@v/s)"], &mut quiet())
        .unwrap();
    assert_eq!(r.status(), "partial");
    let w = r.wire();
    let a = answer(&w, "m");
    assert_eq!(get(a, "status"), &Json::str("undetermined"));
    let Json::Obj(outputs) = get(a, "outputs") else {
        panic!("outputs")
    };
    assert!(!outputs.contains_key("value"));
    for field in ["Terms.Sample.missing", "Terms.Sample.h"] {
        assert!(
            arr(get(a, "reasons"))
                .iter()
                .flat_map(|r| arr(get(r, "missing")))
                .any(|m| get(m, "field") == &Json::str(field))
        );
    }
    assert!(
        !arr(get(a, "reasons"))
            .iter()
            .any(|r| get(r, "code") == &Json::str("unsupported_algorithm"))
    );
    assert_eq!(before.sources(), r.prepared().inputs().sources());
    assert_eq!(
        format!("{:?}", before.archmap()),
        format!("{:?}", r.prepared().inputs().archmap())
    );
    audit_current_sources(&r, "r1");
}

#[test]
fn affine_term_application_keeps_view_let_and_finite_completion_contexts() {
    let r = evaluate_observed_bytes(
        sources(),
        &[
            "v=check(Terms.viaView,s=@v/s)",
            "l=evaluate(Terms.letCancel,s=@v/s)",
            "c=evaluate(Terms.affineStable,s=@v/s)",
        ],
        &mut quiet(),
    )
    .unwrap();
    assert_eq!(r.status(), "complete", "{:?}", get(&r.wire(), "issues"));
    let w = r.wire();
    assert_eq!(get(answer(&w, "v"), "status"), &Json::str("established"));
    assert_eq!(value(&w, "l"), &Json::str("0"));
    assert_eq!(value(&w, "c"), &Json::str("1"));
    assert!(
        !arr(get(answer(&w, "c"), "reasons"))
            .iter()
            .any(|r| get(r, "code") == &Json::str("unsupported_algorithm"))
    );
    assert!(
        arr(get(answer(&w, "c"), "reasons"))
            .iter()
            .flat_map(|r| arr(get(r, "missing")))
            .any(|m| get(m, "field") == &Json::str("Terms.Sample.p"))
    );
    audit_current_sources(&r, "r1");
}

#[test]
fn affine_tuple_comparison_handles_known_and_symbolic_output_representations() {
    let r = evaluate_observed_bytes(
        sources(),
        &[
            "a=evaluate(Terms.tupleKnownAdd)",
            "r=evaluate(Terms.tupleKnownReverse)",
            "c=evaluate(Terms.tupleKnownLet)",
            "n=evaluate(Terms.tupleKnownNested)",
        ],
        &mut quiet(),
    )
    .unwrap();
    assert_eq!(r.status(), "complete", "{:?}", get(&r.wire(), "issues"));
    for id in ["a", "r", "c", "n"] {
        assert_eq!(value(&r.wire(), id), &Json::Bool(false));
    }
}
#[test]
fn affine_tuple_actuals_preserve_let_view_arithmetic_projection_and_universal_components() {
    let r = evaluate_observed_bytes(
        sources(),
        &[
            "l=evaluate(Terms.viaTupleLet,s=@v/s)",
            "v=evaluate(Terms.viaTupleView,s=@v/s)",
            "o=evaluate(Terms.viaTupleOutput,s=@v/s)",
            "a=evaluate(Terms.viaTupleArithmetic,s=@v/s)",
            "p=evaluate(Terms.viaTupleProjection,s=@v/s)",
            "u=check(Terms.viaUniversalTuple,s=@v/s)",
            "c=evaluate(Terms.viaTupleChoice,s=@v/s)",
            "k=evaluate(Terms.tupleCache,s=@v/s)",
            "d=evaluate(Terms.tupleDifference,s=@v/s)",
        ],
        &mut quiet(),
    )
    .unwrap();
    assert_eq!(r.status(), "complete", "{:?}", get(&r.wire(), "issues"));
    let w = r.wire();
    let q = Json::Arr(vec![Json::str("0"), Json::str("1")]);
    for id in ["l", "o", "c"] {
        assert_eq!(value(&w, id), &Json::str("0"));
    }
    for id in ["v", "p"] {
        assert_eq!(value(&w, id), &q);
    }
    assert_eq!(value(&w, "a"), &Json::Arr(vec![Json::str("0"), q.clone()]));
    assert_eq!(value(&w, "d"), &Json::Arr(vec![Json::str("0"), q]));
    assert_eq!(get(answer(&w, "u"), "status"), &Json::str("established"));
    assert_eq!(value(&w, "k"), &Json::Bool(true));
    for id in ["l", "v", "o", "a", "p", "c"] {
        let a = answer(&w, id);
        assert!(
            arr(get(a, "reasons"))
                .iter()
                .flat_map(|r| arr(get(r, "missing")))
                .any(|m| get(m, "field") == &Json::str("Terms.Sample.h")
                    || get(m, "field") == &Json::str("Terms.Sample.q"))
        );
        assert!(
            !arr(get(a, "reasons"))
                .iter()
                .any(|r| get(r, "code") == &Json::str("unsupported_algorithm"))
        );
    }
}
#[test]
fn nonlinear_tuple_term_application_keeps_algorithm_and_original_missing_reasons() {
    let r = evaluate_observed_bytes(
        sources(),
        &[
            "t=evaluate(Terms.tupleOutside,s=@v/s)",
            "n=evaluate(Terms.tupleNestedOutside,s=@v/s)",
        ],
        &mut quiet(),
    )
    .unwrap();
    assert_eq!(r.status(), "partial", "{:?}", get(&r.wire(), "issues"));
    let w = r.wire();
    for id in ["t", "n"] {
        let a = answer(&w, id);
        assert_eq!(get(a, "status"), &Json::str("undetermined"));
        let Json::Obj(outputs) = get(a, "outputs") else {
            panic!("outputs")
        };
        assert!(!outputs.contains_key("value"));
        let reasons = arr(get(a, "reasons"));
        assert!(
            reasons
                .iter()
                .any(|r| get(r, "code") == &Json::str("unsupported_algorithm")),
            "{a:?}"
        );
        for reason in reasons
            .iter()
            .filter(|r| get(r, "code") == &Json::str("unsupported_algorithm"))
        {
            assert!(!arr(get(reason, "dependencies")).is_empty());
            assert!(
                matches!(get(reason,"location"),Json::Obj(m) if m.get("input")==Some(&Json::str("law")))
            );
            let types = arr(get(get(reason, "details"), "operand_types"));
            assert!(
                matches!(types.first(),Some(Json::Arr(t)) if t.first()==Some(&Json::str("Term")))
            );
            assert!(
                matches!(types.first(),Some(Json::Arr(t)) if matches!(t.last(),Some(Json::Arr(tuple)) if tuple.first()==Some(&Json::str("Tuple"))))
            );
        }

        assert!(
            reasons
                .iter()
                .flat_map(|r| arr(get(r, "missing")))
                .any(|m| get(m, "field") == &Json::str("Terms.Sample.h"))
        );
    }
}
#[test]
fn affine_term_comparison_retains_normal_forms_and_reapplied_original_points() {
    let r = evaluate_observed_bytes(
        sources(),
        &[
            "e=evaluate(Terms.same,s=@v/s)",
            "d=check(Terms.unequal,s=@v/s)",
            "q=evaluate(Terms.qCoefficient)",
            "t=evaluate(Terms.tupleSameNormal)",
        ],
        &mut quiet(),
    )
    .unwrap();
    assert_eq!(r.status(), "complete");
    let w = r.wire();
    let nodes = arr(get(&w, "nodes"));
    let target = |reference: &Json| {
        nodes
            .iter()
            .find(|n| get(n, "id") == get(reference, "node"))
            .unwrap()
    };
    let proofs:Vec<_>=nodes.iter().filter(|n| matches!(n,Json::Obj(m) if m.get("type")==Some(&Json::str("Evidence")) && m.get("value").is_some_and(|v|matches!(v,Json::Obj(m) if m.get("kind")==Some(&Json::str("normalization")))))).collect();
    assert_eq!(proofs.len(), 8);
    let matrices: Vec<_> = proofs
        .iter()
        .map(|n| {
            let data = get(get(n, "value"), "data");
            let before = target(get(data, "before"));
            assert!(
                matches!(get(before,"type"),Json::Arr(t) if t.first()==Some(&Json::str("Term")))
            );
            let steps = arr(get(data, "steps"));
            assert_eq!(steps.len(), 1);
            assert_eq!(get(target(&steps[0]), "type"), &Json::str("Expression"));
            let after = target(get(data, "after"));
            assert!(
                matches!(get(after,"type"),Json::Arr(t) if t.first()==Some(&Json::str("List")))
            );
            get(after, "value")
        })
        .collect();
    assert_eq!(matrices[0], matrices[1]);
    assert_eq!(matrices[6], matrices[7]);
    let row = arr(&arr(matrices[0])[0]);
    assert_eq!(row[0], Json::Arr(vec![Json::str("0"), Json::str("0")]));
    assert_eq!(
        row[1],
        Json::Arr(vec![
            Json::str("0"),
            Json::Arr(vec![Json::str("2"), Json::str("-1")])
        ])
    );
    let counters:Vec<_>=nodes.iter().filter(|n|matches!(n,Json::Obj(m) if m.get("type")==Some(&Json::str("Evidence")) && m.get("value").is_some_and(|v|matches!(v,Json::Obj(m) if m.get("kind")==Some(&Json::str("counterexample")))))).collect();
    let counters: Vec<_> = counters
        .into_iter()
        .filter(|n| {
            arr(get(get(get(n, "value"), "data"), "bindings"))
                .first()
                .is_some_and(|b| matches!(get(b,"name"),Json::Str(name) if name=="x"||name=="q"))
        })
        .collect();
    assert_eq!(counters.len(), 2);
    for (index, n) in counters.iter().enumerate() {
        let data = get(get(n, "value"), "data");
        let bindings = arr(get(data, "bindings"));
        assert_eq!(bindings.len(), if index == 0 { 2 } else { 1 });
        let expected = if index == 0 {
            Json::str("0")
        } else {
            Json::Arr(vec![Json::str("1"), Json::str("1")])
        };
        for (position, binding) in bindings.iter().enumerate() {
            assert_eq!(
                get(binding, "name"),
                &Json::str(if index == 1 {
                    "q"
                } else if position == 0 {
                    "x"
                } else {
                    "y"
                })
            );
            assert_eq!(
                get(target(get(binding, "value")), "type"),
                &Json::str(if index == 0 { "Z" } else { "Q" })
            );
            assert_eq!(get(target(get(binding, "value")), "value"), &expected);
        }
        let (left, right) = (
            get(target(get(data, "left")), "value"),
            get(target(get(data, "right")), "value"),
        );
        if index == 0 {
            assert_eq!(left, &Json::str("0"));
            assert_eq!(right, &Json::str("1"));
        } else {
            assert_eq!(left, &Json::Arr(vec![Json::str("3"), Json::str("2")]));
            assert_eq!(right, &Json::Arr(vec![Json::str("5"), Json::str("3")]));
        }
        assert_ne!(left, right);
        assert_eq!(get(data, "paths"), &Json::Arr(vec![]));
        let reference = Json::obj([("node", get(n, "id").clone())]);
        assert!(
            nodes
                .iter()
                .any(|v| arr(get(v, "evidence")).contains(&reference))
        );
    }
}

#[test]
fn affine_term_evidence_uses_the_fixed_result_two_keys_and_typed_prior_refs() {
    use std::collections::BTreeSet;
    let r = evaluate_observed_bytes(
        sources(),
        &[
            "e=evaluate(Terms.same,s=@v/s)",
            "d=check(Terms.unequal,s=@v/s)",
            "q=evaluate(Terms.qCoefficient)",
        ],
        &mut quiet(),
    )
    .unwrap();
    assert_eq!(r.status(), "complete");
    let w = r.wire();
    let nodes = arr(get(&w, "nodes"));
    let node_id = |r: &Json| {
        let Json::Str(id) = get(r, "node") else {
            panic!("Ref")
        };
        id.clone()
    };
    let mut seen = BTreeSet::<String>::new();
    let mut counts = [0, 0];
    for n in nodes {
        let Json::Obj(m) = n else { panic!("node") };
        if m.get("type") == Some(&Json::str("Evidence")) {
            let value = get(n, "value");
            let kind = get(value, "kind");
            if kind == &Json::str("normalization") || kind == &Json::str("counterexample") {
                let Json::Obj(d) = get(value, "data") else {
                    panic!("data")
                };
                let expected = if kind == &Json::str("normalization") {
                    counts[0] += 1;
                    vec!["before", "after", "steps"]
                } else {
                    counts[1] += 1;
                    vec!["bindings", "paths", "left", "right", "facts"]
                };
                assert_eq!(
                    d.keys().map(String::as_str).collect::<BTreeSet<_>>(),
                    expected.into_iter().collect()
                );
                let keys = if kind == &Json::str("normalization") {
                    vec!["before", "after"]
                } else {
                    vec!["left", "right"]
                };
                for key in keys {
                    assert!(seen.contains(&node_id(get(get(value, "data"), key))));
                }
                if kind == &Json::str("normalization") {
                    for step in arr(get(get(value, "data"), "steps")) {
                        let id = get(step, "node");
                        let target = nodes.iter().find(|n| get(n, "id") == id).unwrap();
                        assert_eq!(get(target, "type"), &Json::str("Expression"));
                        assert!(seen.contains(&node_id(step)));
                    }
                }
            }
        }
        // Ordered Ref identities, without giving IDs mathematical meaning.
        let Json::Str(id) = get(n, "id") else {
            panic!("node id")
        };
        seen.insert(id.clone());
    }
    assert!(counts[0] > 0 && counts[1] > 0);
}
#[test]
fn affine_term_tuple_outer_comparisons_preserve_each_missing_component() {
    let r = evaluate_observed_bytes(
        sources(),
        &[
            "e=evaluate(Terms.tupleEq,s=@v/s)",
            "n=evaluate(Terms.tupleNe,s=@v/s)",
            "o=evaluate(Terms.tupleOffset,s=@v/s)",
            "l=check(Terms.tupleEqLaw,s=@v/s)",
        ],
        &mut quiet(),
    )
    .unwrap();
    assert_eq!(r.status(), "complete", "{:?}", get(&r.wire(), "issues"));
    let w = r.wire();
    assert_eq!(get(answer(&w, "l"), "status"), &Json::str("established"));
    assert_eq!(value(&w, "e"), &Json::Bool(true));
    for id in ["n", "o"] {
        assert_eq!(value(&w, id), &Json::Bool(false));
    }
}
#[test]
fn affine_term_single_missing_tuple_slot_keeps_paths_and_whole_slot_completions() {
    let r = evaluate_observed_bytes(
        sources(),
        &[
            "z=evaluate(Terms.tupleSlot,s=@v/s)",
            "e=evaluate(Terms.tupleSlotEq,s=@v/s)",
            "u=check(Terms.tupleSlotUniversal,s=@v/s)",
            "d=evaluate(Terms.tupleSlotsIndependent,s=@v/s)",
            "c=evaluate(Terms.tupleComponentsIndependent,s=@v/s)",
            "v=check(Terms.tupleSlotVary,s=@v/s)",
        ],
        &mut quiet(),
    )
    .unwrap();
    assert_eq!(r.status(), "partial", "{:?}", get(&r.wire(), "issues"));
    let w = r.wire();
    assert_eq!(
        value(&w, "z"),
        &Json::Arr(vec![
            Json::str("0"),
            Json::Arr(vec![Json::str("0"), Json::str("1")])
        ])
    );
    assert_eq!(value(&w, "e"), &Json::Bool(true));
    assert_eq!(get(answer(&w, "u"), "status"), &Json::str("established"));
    for (id, fields) in [
        ("z", vec!["Terms.Sample.t"]),
        ("d", vec!["Terms.Sample.t", "Terms.Sample.u"]),
        ("c", vec!["Terms.Sample.zz"]),
        ("v", vec!["Terms.Sample.zz"]),
    ] {
        let a = answer(&w, id);
        let reasons = arr(get(a, "reasons"));
        for field in fields {
            assert!(
                reasons
                    .iter()
                    .flat_map(|r| arr(get(r, "missing")))
                    .any(|m| get(m, "field") == &Json::str(field))
            );
        }
        assert!(
            !reasons
                .iter()
                .any(|r| get(r, "code") == &Json::str("unsupported_algorithm")),
            "{a:?}"
        );
    }
    for id in ["d", "c", "v"] {
        assert_eq!(get(answer(&w, id), "status"), &Json::str("undetermined"));
    }
    let nodes = arr(get(&w, "nodes"));
    let pair=nodes.iter().find(|n|matches!(n,Json::Obj(m) if m.get("type")==Some(&Json::str("Evidence"))&&m.get("value").is_some_and(|v|matches!(v,Json::Obj(m) if m.get("kind")==Some(&Json::str("completion_pair")))))).unwrap();
    let data = get(get(pair, "value"), "data");
    let fields = arr(get(data, "fields"));
    assert_eq!(fields.len(), 1);
    assert_eq!(get(&fields[0], "field"), &Json::str("Terms.Sample.zz"));
    let mut slot_values = vec![];
    for side in ["first", "second"] {
        let refs = arr(get(data, side));
        assert_eq!(refs.len(), 1);
        let n = nodes
            .iter()
            .find(|n| get(n, "id") == get(&refs[0], "node"))
            .unwrap();
        slot_values.push(get(n, "value").clone());
    }
    assert_eq!(
        slot_values,
        vec![
            Json::Arr(vec![Json::str("0"), Json::str("0")]),
            Json::Arr(vec![Json::str("1"), Json::str("0")])
        ]
    );
}

#[test]
fn partial_nonlinear_term_comparison_keeps_a_typed_algorithm_reason_instead_of_internal() {
    let r = evaluate_observed_bytes(
        sources(),
        &[
            "seed=evaluate(Terms.seed)",
            "prior=check(Terms.prior)",
            "x=evaluate(Terms.partialNonlinearTuple)",
            "f=evaluate(Terms.partialNonlinearFinite)",
            "l=evaluate(Terms.partialNonlinearList)",
        ],
        &mut quiet(),
    )
    .unwrap();
    assert_eq!(r.status(), "partial", "{:?}", get(&r.wire(), "issues"));
    let w = r.wire();
    assert_eq!(value(&w, "seed"), &Json::str("1"));
    assert_eq!(get(answer(&w, "prior"), "status"), &Json::str("refuted"));
    for id in ["x", "f", "l"] {
        let a = answer(&w, id);
        assert_eq!(get(a, "status"), &Json::str("undetermined"));
        assert!(!format!("{:?}", get(&w, "issues")).contains("internal"));
        let Json::Obj(outputs) = get(a, "outputs") else {
            panic!("outputs")
        };
        assert!(!outputs.contains_key("value"));
        let reason = arr(get(a, "reasons"))
            .iter()
            .find(|r| get(r, "code") == &Json::str("unsupported_algorithm"))
            .unwrap();
        assert!(!arr(get(reason, "dependencies")).is_empty());
        assert_eq!(get(get(reason, "location"), "input"), &Json::str("law"));
        let parameters = if id == "f" {
            vec![Json::str("Bool"), Json::str("Z")]
        } else {
            vec![Json::str("Z")]
        };
        let returns = match id {
            "x" => Json::Arr(vec![Json::str("Tuple"), Json::str("Z"), Json::str("Z")]),
            "f" => Json::str("Z"),
            "l" => Json::Arr(vec![Json::str("List"), Json::str("Z")]),
            _ => unreachable!(),
        };
        let ty = Json::Arr(vec![Json::str("Term"), Json::Arr(parameters), returns]);
        assert_eq!(
            get(get(reason, "details"), "operand_types"),
            &Json::Arr(vec![ty.clone(), ty])
        );
    }
}
#[test]
fn canceled_missing_tuple_keeps_whole_typed_values_in_another_slots_universal_completion_pair() {
    let r = evaluate_observed_bytes(
        sources(),
        &["x=check(Terms.canceledTupleWithMissing,s=@v/s)"],
        &mut quiet(),
    )
    .unwrap();
    assert_eq!(r.status(), "partial", "{:?}", get(&r.wire(), "issues"));
    let w = r.wire();
    let a = answer(&w, "x");
    assert_eq!(get(a, "status"), &Json::str("undetermined"));
    assert!(!format!("{:?}", get(&w, "issues")).contains("internal"));
    for field in ["Terms.Sample.h", "Terms.Sample.t"] {
        assert!(
            arr(get(a, "reasons"))
                .iter()
                .flat_map(|r| arr(get(r, "missing")))
                .any(|m| get(m, "field") == &Json::str(field))
        );
    }
    let nodes = arr(get(&w, "nodes"));
    let node = |reference: &Json| {
        nodes
            .iter()
            .find(|n| get(n, "id") == get(reference, "node"))
            .unwrap()
    };
    let pairs:Vec<_>=nodes.iter().filter(|n|matches!(n,Json::Obj(m) if m.get("type")==Some(&Json::str("Evidence"))&&m.get("value").is_some_and(|v|matches!(v,Json::Obj(m) if m.get("kind")==Some(&Json::str("completion_pair")))))).collect();
    assert_eq!(pairs.len(), 1);
    let data = get(get(pairs[0], "value"), "data");
    assert_eq!(
        arr(get(data, "fields"))
            .iter()
            .map(|f| get(f, "field").clone())
            .collect::<Vec<_>>(),
        vec![Json::str("Terms.Sample.h"), Json::str("Terms.Sample.t")]
    );
    for (side, h) in [("first", "0"), ("second", "1")] {
        let values = arr(get(data, side));
        assert_eq!(values.len(), 2);
        let t = node(&values[1]);
        assert_eq!(
            get(t, "type"),
            &Json::Arr(vec![Json::str("Tuple"), Json::str("Z"), Json::str("Q")])
        );
        assert_eq!(
            get(t, "value"),
            &Json::Arr(vec![
                Json::str("0"),
                Json::Arr(vec![Json::str("0"), Json::str("1")])
            ])
        );
        assert_eq!(get(node(&values[0]), "value"), &Json::str(h));
    }
    for (key, wanted) in [("first_result", true), ("second_result", false)] {
        let evaluation = node(get(data, key));
        assert_eq!(
            get(node(get(get(evaluation, "value"), "value")), "value"),
            &Json::Bool(wanted)
        );
    }
}
