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
    let proofs:Vec<_>=nodes.iter().filter(|n| matches!(n,Json::Obj(m) if m.get("value").is_some_and(|v|matches!(v,Json::Obj(m) if matches!(m.get("data"),Some(Json::Obj(d)) if d.contains_key("term_comparison")))))).collect();
    assert_eq!(proofs.len(), 4);
    for (index, n) in proofs.iter().enumerate() {
        let proof = get(n, "value");
        let data = get(proof, "data");
        let certificate = get(data, "term_comparison");
        let cases = arr(get(certificate, "cases"));
        assert_eq!(cases.len(), 1);
        let args = arr(get(&cases[0], "arguments"));
        assert_eq!(args.len(), if index < 2 { 2 } else { 1 });
        for (position, arg) in args.iter().enumerate() {
            assert_eq!(
                get(arg, "type"),
                &Json::str(if index == 2 { "Q" } else { "Z" })
            );
            let coefficients = arr(get(arg, "coefficients"));
            assert_eq!(coefficients.len(), 1);
            assert_eq!(
                get(get(&coefficients[0], "coordinate"), "argument"),
                &Json::Nat(position as u64)
            );
            assert_eq!(
                get(get(&coefficients[0], "coordinate"), "component"),
                &Json::Arr(vec![])
            );
        }
        for key in ["source", "left", "right"] {
            let node = get(get(data, key), "node");
            assert!(nodes.iter().any(|n| get(n, "id") == node));
        }
        let reference = Json::obj([("node", get(n, "id").clone())]);
        assert!(
            nodes
                .iter()
                .any(|v| arr(get(v, "evidence")).contains(&reference))
        );
        if index == 3 {
            assert_eq!(get(proof, "kind"), &Json::str("normalization"));
            assert_eq!(get(&cases[0], "left"), get(&cases[0], "right"));
        } else if index == 0 {
            assert_eq!(get(proof, "kind"), &Json::str("normalization"));
            assert_eq!(get(&cases[0], "left"), get(&cases[0], "right"));
            let Json::Obj(c) = certificate else {
                panic!("certificate")
            };
            assert!(!c.contains_key("counterexample"));
            let coefficients = arr(get(get(&cases[0], "left"), "coefficients"));
            assert_eq!(
                coefficients
                    .iter()
                    .map(|v| get(v, "value").clone())
                    .collect::<Vec<_>>(),
                vec![Json::str("2"), Json::str("-1")]
            );
        } else {
            assert_eq!(get(proof, "kind"), &Json::str("counterexample"));
            let point = get(certificate, "counterexample");
            let arguments = arr(get(point, "arguments"));
            if index == 1 {
                assert_eq!(arguments.len(), 2);
                for a in arguments {
                    assert_eq!(get(a, "type"), &Json::str("Z"));
                    assert_eq!(get(a, "value"), &Json::str("0"));
                }
                assert_eq!(get(get(point, "left"), "value"), &Json::str("0"));
                assert_eq!(get(get(point, "right"), "value"), &Json::str("1"));
            } else {
                assert_eq!(arguments.len(), 1);
                assert_eq!(get(&arguments[0], "type"), &Json::str("Q"));
                assert_eq!(
                    get(&arguments[0], "value"),
                    &Json::Arr(vec![Json::str("1"), Json::str("1")])
                );
                assert_eq!(
                    get(get(point, "left"), "value"),
                    &Json::Arr(vec![Json::str("3"), Json::str("2")])
                );
                assert_eq!(
                    get(get(point, "right"), "value"),
                    &Json::Arr(vec![Json::str("5"), Json::str("3")])
                );
            }
            assert_ne!(get(point, "left"), get(point, "right"));
        }
    }
}
