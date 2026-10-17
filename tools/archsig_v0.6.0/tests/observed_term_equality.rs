//! 有限な引数型の全値域で、元の閉じた関数の外延を比較する。
#[path = "common/term_equality.rs"]
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
fn sources(revision: &str) -> InputSources {
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
    assert_eq!(get(a, "status"), &Json::str("established"));
    let reference = get(get(get(a, "outputs"), "value"), "node");
    let node = arr(get(w, "nodes"))
        .iter()
        .find(|n| get(n, "id") == reference)
        .unwrap();
    get(node, "value")
}
#[test]
fn finite_term_equality_compares_the_entire_bool_domain_from_original_bodies() {
    let r = evaluate_observed_bytes(
        sources("r1"),
        &[
            "e=evaluate(Terms.eq,s=@v/s)",
            "n=evaluate(Terms.ne,s=@v/s)",
            "p=check(Terms.same,s=@v/s)",
            "c=check(Terms.different,s=@v/s)",
        ],
        &mut quiet(),
    )
    .unwrap();
    assert_eq!(r.status(), "complete");
    let w = r.wire();
    assert_eq!(value(&w, "e"), &Json::Bool(true));
    assert_eq!(value(&w, "n"), &Json::Bool(true));
    assert_eq!(get(answer(&w, "p"), "status"), &Json::str("established"));
    assert_eq!(get(answer(&w, "c"), "status"), &Json::str("refuted"));
}

#[test]
fn finite_term_domains_keep_zero_unit_fp_data_tuple_and_parameter_products() {
    let r = evaluate_observed_bytes(
        sources("r1"),
        &[
            "z=evaluate(Terms.zero)",
            "u=evaluate(Terms.one)",
            "f=evaluate(Terms.fp)",
            "d=evaluate(Terms.finiteData)",
            "t=evaluate(Terms.tuple)",
            "m=evaluate(Terms.multi)",
        ],
        &mut quiet(),
    )
    .unwrap();
    assert_eq!(r.status(), "complete");
    let w = r.wire();
    for id in ["z", "u", "f", "d", "t", "m"] {
        assert_eq!(value(&w, id), &Json::Bool(true));
    }
}
#[test]
fn finite_term_equality_recurses_through_containers_membership_and_functions() {
    let r = evaluate_observed_bytes(
        sources("r1"),
        &[
            "p=evaluate(Terms.packed,s=@v/s)",
            "m=evaluate(Terms.member,s=@v/s)",
            "a=evaluate(Terms.arg,s=@v/s)",
            "h=evaluate(Terms.higher)",
        ],
        &mut quiet(),
    )
    .unwrap();
    assert_eq!(r.status(), "complete");
    let w = r.wire();
    for id in ["p", "m", "a", "h"] {
        assert_eq!(value(&w, id), &Json::Bool(true));
    }
}
#[test]
fn finite_term_values_use_extensional_equality_in_unknown_branches_and_completions() {
    let r = evaluate_observed_bytes(
        sources("r1"),
        &[
            "b=evaluate(Terms.branch,s=@v/s)",
            "s=evaluate(Terms.stable,s=@v/s)",
            "u=evaluate(Terms.unstable,s=@v/s)",
            "x=evaluate(Terms.unresolved,s=@v/s)",
        ],
        &mut quiet(),
    )
    .unwrap();
    assert_eq!(r.status(), "partial");
    let w = r.wire();
    let g = Json::obj([
        ("params", Json::Arr(vec![Json::str("b")])),
        ("body", Json::str("if b then 4 else 9")),
    ]);
    let alpha = Json::obj([
        ("params", Json::Arr(vec![Json::str("t")])),
        ("body", Json::str("if not t then 9 else 4")),
    ]);
    assert_eq!(value(&w, "b"), &alpha);
    assert_eq!(value(&w, "s"), &g);
    assert_eq!(get(answer(&w, "u"), "status"), &Json::str("undetermined"));
    for id in ["b", "s"] {
        let proof = evidence(&w, id, "finite_exhaustion");
        assert_eq!(proof.len(), 1);
        assert_eq!(get(get(proof[0], "data"), "checked"), &Json::Nat(2));
        assert!(evidence(&w, id, "completion_pair").is_empty());
    }
    assert_eq!(evidence(&w, "u", "completion_pair").len(), 1);
    let unknown = answer(&w, "x");
    assert_eq!(get(unknown, "status"), &Json::str("undetermined"));
    assert!(evidence(&w, "x", "completion_pair").is_empty());
    assert!(
        arr(get(unknown, "reasons"))
            .iter()
            .any(|r| get(r, "code") == &Json::str("unsupported_algorithm"))
    );
    assert!(
        arr(get(unknown, "reasons"))
            .iter()
            .flat_map(|r| arr(get(r, "missing")))
            .any(|m| get(m, "field") == &Json::str("Terms.Sample.p"))
    );
    assert!(!format!("{:?}", get(&w, "issues")).contains("internal"));
}

fn evidence<'a>(w: &'a Json, id: &str, kind: &str) -> Vec<&'a Json> {
    arr(get(answer(w, id), "evidence"))
        .iter()
        .filter_map(|reference| {
            let n = arr(get(w, "nodes"))
                .iter()
                .find(|n| get(n, "id") == get(reference, "node"))
                .unwrap();
            let v = get(n, "value");
            if get(v, "kind") == &Json::str(kind) {
                Some(v)
            } else {
                None
            }
        })
        .collect()
}

fn audit(r: &archsig::observed::ObservedEvaluation, revision: &str) {
    let w = r.wire();
    let ns = arr(get(&w, "nodes"));
    let inputs = r.prepared().inputs();
    fn refs(j: &Json, ids: &mut Vec<String>) {
        match j {
            Json::Obj(m) => {
                if let Some(Json::Str(n)) = m.get("node") {
                    ids.push(n.clone());
                }
                for v in m.values() {
                    refs(v, ids);
                }
            }
            Json::Arr(a) => {
                for v in a {
                    refs(v, ids)
                }
            }
            _ => {}
        }
    }
    for (index, n) in ns.iter().enumerate() {
        let Json::Obj(object) = n else { panic!("node") };
        assert!(get(n, "type") == &Json::str("Proposition") || !object.contains_key("judgment"));
        let mut references = Vec::new();
        for (key, v) in object {
            if key != "id" {
                refs(v, &mut references);
            }
        }
        for id in references {
            assert!(ns[..index].iter().any(|n| get(n, "id") == &Json::str(&id)));
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
                let slot = &sub.fields.iter().find(|s| s.name == *field).unwrap().slot;
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
fn finite_term_provenance_pair_keeps_mathematical_values_and_current_sources() {
    let asks = [
        "e=evaluate(Terms.eq,s=@v/s)",
        "s=evaluate(Terms.stable,s=@v/s)",
        "c=check(Terms.different,s=@v/s)",
    ];
    let src = sources("r1");
    let before = archsig::observed::input::check_inputs(src.clone(), &mut quiet()).unwrap();
    let a = evaluate_observed_bytes(src, &asks, &mut quiet()).unwrap();
    let b = evaluate_observed_bytes(sources("r2"), &asks, &mut quiet()).unwrap();
    let (aw, bw) = (a.wire(), b.wire());
    assert_eq!(get(&aw, "answers"), get(&bw, "answers"));
    for id in ["e", "s"] {
        assert_eq!(value(&aw, id), value(&bw, id));
    }
    for (id, ty) in [
        ("e", Json::str("Bool")),
        (
            "s",
            Json::Arr(vec![
                Json::str("Term"),
                Json::Arr(vec![Json::str("Bool")]),
                Json::str("Z"),
            ]),
        ),
    ] {
        for w in [&aw, &bw] {
            let reference = get(get(get(answer(w, id), "outputs"), "value"), "node");
            let node = arr(get(w, "nodes"))
                .iter()
                .find(|n| get(n, "id") == reference)
                .unwrap();
            assert_eq!(get(node, "type"), &ty);
        }
    }
    assert_eq!(value(&aw, "e"), &Json::Bool(true));
    assert_eq!(
        value(&aw, "s"),
        &Json::obj([
            ("params", Json::Arr(vec![Json::str("b")])),
            ("body", Json::str("if b then 4 else 9"))
        ])
    );
    assert_eq!(get(answer(&aw, "c"), "status"), &Json::str("refuted"));
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
    audit(&a, "r1");
    audit(&b, "r2");
}
#[test]
fn finite_term_missing_function_keeps_its_original_slot_and_inputs() {
    let good = sources("r1");
    let original = std::str::from_utf8(good.archmap().bytes()).unwrap();
    let marker = r#",{"id":"g","subject":"s","field":"Terms.Sample.g","value":{"params":["b"],"body":"if b then 4 else 9"},"origin":"base"}"#;
    assert_eq!(original.matches(marker).count(), 1);
    let missing = original.replace(marker, "");
    assert_ne!(original, missing);
    let src = InputSources::from_bytes(
        good.definitions()
            .iter()
            .map(|b| b.bytes().to_vec())
            .collect(),
        good.law().bytes().to_vec(),
        missing.into_bytes(),
    );
    let before = archsig::observed::input::check_inputs(src.clone(), &mut quiet()).unwrap();
    let field = before.archmap().snapshots[0].subjects[0]
        .fields
        .iter()
        .find(|f| f.name == "Terms.Sample.g")
        .unwrap();
    assert!(matches!(field.slot, archsig::archmap::Slot::Missing));
    let r = evaluate_observed_bytes(src, &["e=evaluate(Terms.eq,s=@v/s)"], &mut quiet()).unwrap();
    assert_eq!(r.status(), "partial");
    let w = r.wire();
    let a = answer(&w, "e");
    assert_eq!(get(a, "status"), &Json::str("undetermined"));
    let Json::Obj(outputs) = get(a, "outputs") else {
        panic!("outputs")
    };
    assert!(!outputs.contains_key("value"));
    assert!(
        arr(get(a, "reasons"))
            .iter()
            .flat_map(|r| arr(get(r, "missing")))
            .any(|m| get(m, "field") == &Json::str("Terms.Sample.g"))
    );
    assert_eq!(
        format!("{:?}", before.definitions()),
        format!("{:?}", r.prepared().inputs().definitions())
    );
    assert_eq!(
        format!("{:?}", before.law()),
        format!("{:?}", r.prepared().inputs().law())
    );
    assert_eq!(
        format!("{:?}", before.archmap()),
        format!("{:?}", r.prepared().inputs().archmap())
    );
    assert_eq!(before.sources(), r.prepared().inputs().sources());
    audit(&r, "r1");
}
