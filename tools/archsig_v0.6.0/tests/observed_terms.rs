//! 閉じたTermの元bodyと実引数から値を計算する。
#[path = "common/terms.rs"]
mod terms;
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
    let d = check_definitions(&[("definition0", terms::DEFINITIONS.as_bytes())]).unwrap();
    let digest = &d.vocabularies["Terms"].digest;
    InputSources::from_bytes(
        vec![terms::DEFINITIONS.as_bytes().to_vec()],
        terms::law(digest).into_bytes(),
        terms::archmap(digest, revision).into_bytes(),
    )
}
fn obj(j: &Json) -> &std::collections::BTreeMap<String, Json> {
    let Json::Obj(m) = j else { panic!("object") };
    m
}
fn arr(j: &Json) -> &[Json] {
    let Json::Arr(a) = j else { panic!("array") };
    a
}
fn get<'a>(j: &'a Json, k: &str) -> &'a Json {
    &obj(j)[k]
}
fn result_value<'a>(w: &'a Json, id: &str) -> &'a Json {
    let a = arr(get(w, "answers"))
        .iter()
        .find(|a| get(a, "id") == &Json::str(id))
        .unwrap();
    assert_eq!(get(a, "status"), &Json::str("established"));
    let id = get(get(get(a, "outputs"), "value"), "node");
    let n = arr(get(w, "nodes"))
        .iter()
        .find(|n| get(n, "id") == id)
        .unwrap();
    get(n, "value")
}
#[test]
fn observed_closed_term_uses_declared_argument_order_and_original_body() {
    let r = evaluate_observed_bytes(
        sources("r1"),
        &["a=evaluate(Terms.applied,s=@v/s)"],
        &mut quiet(),
    )
    .unwrap();
    assert_eq!(r.status(), "complete");
    assert_eq!(result_value(&r.wire(), "a"), &Json::str("11"));
}

#[test]
fn inline_closed_terms_keep_exact_rationals_zero_arguments_and_booleans() {
    let r = evaluate_observed_bytes(
        sources("r1"),
        &[
            "q=evaluate(Terms.inline)",
            "z=evaluate(Terms.constant)",
            "b=evaluate(Terms.no)",
            "p=check(Terms.falseTerm)",
            "f=evaluate(Terms.fp)",
        ],
        &mut quiet(),
    )
    .unwrap();
    let w = r.wire();
    assert_eq!(r.status(), "complete");
    assert_eq!(
        result_value(&w, "q"),
        &Json::Arr(vec![Json::str("1"), Json::str("1")])
    );
    assert_eq!(result_value(&w, "z"), &Json::str("3"));
    assert_eq!(result_value(&w, "b"), &Json::Bool(false));
    assert_eq!(result_value(&w, "f"), &Json::str("1"));
    let p = arr(get(&w, "answers"))
        .iter()
        .find(|a| get(a, "id") == &Json::str("p"))
        .unwrap();
    assert_eq!(get(p, "status"), &Json::str("refuted"));
}
#[test]
fn closed_term_values_survive_views_let_and_primitive_containers() {
    let r = evaluate_observed_bytes(
        sources("r1"),
        &[
            "f=evaluate(Terms.read,s=@v/s)",
            "w=evaluate(Terms.wrapped,s=@v/s)",
            "a=evaluate(Terms.viaTuple,s=@v/s)",
            "b=evaluate(Terms.chosen,s=@v/s)",
        ],
        &mut quiet(),
    )
    .unwrap();
    let w = r.wire();
    let f = Json::obj([
        ("params", Json::Arr(vec![Json::str("x"), Json::str("y")])),
        ("body", Json::str("let twice=2*x in twice-y")),
    ]);
    assert_eq!(result_value(&w, "f"), &f);
    assert_eq!(
        result_value(&w, "w"),
        &Json::Arr(vec![
            f.clone(),
            Json::obj([("some", f.clone())]),
            Json::Arr(vec![f.clone(), f])
        ])
    );
    assert_eq!(result_value(&w, "a"), &Json::str("11"));
    assert_eq!(result_value(&w, "b"), &Json::str("9"));
}
#[test]
fn closed_term_uses_original_constructor_and_pattern_resolution() {
    let r = evaluate_observed_bytes(
        sources("r1"),
        &[
            "a=evaluate(Terms.matched,s=@v/s)",
            "b=evaluate(Terms.zeroConstructor,s=@v/s)",
        ],
        &mut quiet(),
    )
    .unwrap();
    let w = r.wire();
    assert_eq!(result_value(&w, "a"), &Json::str("6"));
    assert_eq!(result_value(&w, "b"), &Json::str("0"));
}
#[test]
fn closed_term_body_evaluates_finite_quantification_and_containers() {
    let r = evaluate_observed_bytes(
        sources("r1"),
        &["q=evaluate(Terms.finite)", "c=evaluate(Terms.containers)"],
        &mut quiet(),
    )
    .unwrap();
    let w = r.wire();
    assert_eq!(result_value(&w, "q"), &Json::Bool(true));
    assert_eq!(
        result_value(&w, "c"),
        &Json::Arr(vec![
            Json::str("4"),
            Json::Arr(vec![Json::str("3")]),
            Json::obj([("some", Json::Arr(vec![Json::str("1"), Json::str("2")]))])
        ])
    );
}

fn audit_inputs(r: &archsig::observed::ObservedEvaluation, revision: &str) {
    let w = r.wire();
    let inputs = r.prepared().inputs();
    let ns = arr(get(&w, "nodes"));
    fn references(j: &Json, out: &mut Vec<String>) {
        match j {
            Json::Obj(m) if m.len() == 1 && m.contains_key("node") => {
                let Json::Str(id) = &m["node"] else {
                    panic!("ref")
                };
                out.push(id.clone());
            }
            Json::Obj(m) => {
                for v in m.values() {
                    references(v, out)
                }
            }
            Json::Arr(a) => {
                for v in a {
                    references(v, out)
                }
            }
            _ => {}
        }
    }
    for (i, n) in ns.iter().enumerate() {
        assert!(get(n, "type") == &Json::str("Proposition") || !obj(n).contains_key("judgment"));
        let mut rs = Vec::new();
        for (k, v) in obj(n) {
            if k != "id" {
                references(v, &mut rs)
            }
        }
        for id in rs {
            assert!(ns[..i].iter().any(|n| get(n, "id") == &Json::str(&id)));
        }
        for f in arr(get(n, "support")) {
            let Json::Str(snapshot) = get(f, "snapshot") else {
                panic!("snapshot")
            };
            let Json::Str(subject) = get(f, "subject") else {
                panic!("subject")
            };
            let snap = inputs
                .archmap()
                .snapshots
                .iter()
                .find(|s| s.id == *snapshot)
                .unwrap();
            let sub = snap.subjects.iter().find(|s| s.id == *subject).unwrap();
            let origin = if let Some(Json::Str(field)) = obj(f).get("field") {
                let slot = &sub.fields.iter().find(|s| s.name == *field).unwrap().slot;
                let archsig::archmap::Slot::Known { atom, origin, .. } = slot else {
                    panic!("support is known")
                };
                assert_eq!(get(f, "atom"), &Json::str(atom));
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
fn closed_term_missing_callee_and_argument_preserve_the_original_slots() {
    let s = sources("r1");
    let before = archsig::observed::input::check_inputs(s.clone(), &mut quiet()).unwrap();
    let r = evaluate_observed_bytes(
        s,
        &[
            "f=evaluate(Terms.absent,s=@v/s)",
            "h=evaluate(Terms.unknown,s=@v/s)",
        ],
        &mut quiet(),
    )
    .unwrap();
    assert_eq!(r.status(), "partial");
    let w = r.wire();
    for (id, field) in [("f", "Terms.Sample.missing"), ("h", "Terms.Sample.h")] {
        let a = arr(get(&w, "answers"))
            .iter()
            .find(|a| get(a, "id") == &Json::str(id))
            .unwrap();
        assert_eq!(get(a, "status"), &Json::str("undetermined"));
        assert!(!obj(get(a, "outputs")).contains_key("value"));
        let missing = arr(get(a, "reasons"))
            .iter()
            .flat_map(|reason| arr(get(reason, "missing")));
        assert!(
            missing
                .into_iter()
                .any(|m| get(m, "subject") == &Json::str("s")
                    && get(m, "field") == &Json::str(field))
        );
    }
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
    assert_eq!(
        format!("{:?}", before.sources()),
        format!("{:?}", r.prepared().inputs().sources())
    );
    audit_inputs(&r, "r1");
}
#[test]
fn closed_term_provenance_pair_preserves_results_and_the_current_source() {
    let asks = [
        "a=evaluate(Terms.applied,s=@v/s)",
        "f=evaluate(Terms.read,s=@v/s)",
        "m=evaluate(Terms.matched,s=@v/s)",
    ];
    let a = evaluate_observed_bytes(sources("r1"), &asks, &mut quiet()).unwrap();
    let b = evaluate_observed_bytes(sources("r2"), &asks, &mut quiet()).unwrap();
    let (aw, bw) = (a.wire(), b.wire());
    assert_eq!(get(&aw, "answers"), get(&bw, "answers"));
    assert_ne!(
        a.prepared().inputs().metadata_wire(),
        b.prepared().inputs().metadata_wire()
    );
    audit_inputs(&a, "r1");
    audit_inputs(&b, "r2");
}
#[test]
fn unselected_term_captures_and_invalid_observed_bodies_are_rejected_before_evaluation() {
    let good = sources("r1");
    let d = check_definitions(&[("definition0", terms::DEFINITIONS.as_bytes())]).unwrap();
    let digest = &d.vocabularies["Terms"].digest;
    for body in ["s.h", "seed()"] {
        let script = format!(
            "{} view bad(s:Sample):Term<(Z)->Z> = fn(x:Z)=>{body};",
            terms::SCRIPT
        );
        let law = format!(
            "law \"archsig.law/2\" semantics \"archsig/0.6.0\"; reading Terms {{ use vocabulary Terms version \"1\" digest \"{digest}\"; {script} }}"
        );
        let bad = InputSources::from_bytes(
            vec![terms::DEFINITIONS.as_bytes().to_vec()],
            law.into_bytes(),
            terms::archmap(digest, "r1").into_bytes(),
        );
        let e =
            evaluate_observed_bytes(bad, &["a=evaluate(Terms.seed)"], &mut quiet()).unwrap_err();
        let w = e.wire().unwrap();
        assert_eq!(get(&w, "status"), &Json::str("invalid"));
        assert!(
            arr(get(&w, "issues"))
                .iter()
                .any(|issue| get(issue, "code") == &Json::str("reference")
                    && get(get(issue, "location"), "input") == &Json::str("law"))
        );
        for table in ["requests", "answers", "nodes"] {
            assert!(arr(get(&w, table)).is_empty());
        }
    }
    let invalid = terms::archmap(digest, "r1").replace("let twice=2*x in twice-y", "unbound+1");
    let bad = InputSources::from_bytes(
        vec![terms::DEFINITIONS.as_bytes().to_vec()],
        terms::law(digest).into_bytes(),
        invalid.into_bytes(),
    );
    assert!(
        evaluate_observed_bytes(bad, &["a=evaluate(Terms.seed)"], &mut quiet())
            .unwrap_err()
            .wire()
            .is_some()
    );
    assert_eq!(
        result_value(
            &evaluate_observed_bytes(good, &["a=evaluate(Terms.seed)"], &mut quiet())
                .unwrap()
                .wire(),
            "a"
        ),
        &Json::str("1")
    );
}

#[test]
fn closed_terms_return_closed_functions_and_preserve_typed_term_arguments() {
    let r = evaluate_observed_bytes(
        sources("r1"),
        &[
            "n=evaluate(Terms.nestedFunction)",
            "f=evaluate(Terms.termArgument,s=@v/s)",
            "r=evaluate(Terms.read,s=@v/s)",
        ],
        &mut quiet(),
    )
    .unwrap();
    let w = r.wire();
    assert_eq!(result_value(&w, "n"), &Json::str("5"));
    assert_eq!(result_value(&w, "f"), result_value(&w, "r"));
    audit_inputs(&r, "r1");
}
