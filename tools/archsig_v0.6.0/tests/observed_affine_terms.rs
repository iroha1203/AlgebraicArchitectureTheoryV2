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
