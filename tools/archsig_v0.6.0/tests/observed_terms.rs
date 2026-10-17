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
    for id in ["a", "f", "m"] {
        assert_eq!(result_value(&aw, id), result_value(&bw, id));
        let node_type = |w: &Json| {
            let answer = arr(get(w, "answers"))
                .iter()
                .find(|a| get(a, "id") == &Json::str(id))
                .unwrap();
            let reference = get(get(get(answer, "outputs"), "value"), "node");
            get(
                arr(get(w, "nodes"))
                    .iter()
                    .find(|n| get(n, "id") == reference)
                    .unwrap(),
                "type",
            )
            .clone()
        };
        assert_eq!(node_type(&aw), node_type(&bw));
        let expected_type = if id == "f" {
            Json::Arr(vec![
                Json::str("Term"),
                Json::Arr(vec![Json::str("Z"), Json::str("Z")]),
                Json::str("Z"),
            ])
        } else {
            Json::str("Z")
        };
        assert_eq!(node_type(&aw), expected_type);
    }
    assert_eq!(result_value(&aw, "a"), &Json::str("11"));
    assert_eq!(result_value(&aw, "m"), &Json::str("6"));
    assert_eq!(
        result_value(&aw, "f"),
        &Json::obj([
            ("params", Json::Arr(vec![Json::str("x"), Json::str("y")])),
            ("body", Json::str("let twice=2*x in twice-y")),
        ])
    );
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

fn term_branch_sources(script: &str, boxed: bool) -> InputSources {
    let mut definitions = terms::DEFINITIONS.replace(
        r#"{"name":"h","type":"Z","meaning":"h"}"#,
        r#"{"name":"p","type":"Bool","meaning":"p"}"#,
    );
    if boxed {
        definitions = definitions.replace(
            r#"{"kind":"data","name":"Terms.Choice""#,
            r#"{"kind":"data","name":"Terms.Box","meaning":"box","constructors":[{"name":"Wrap","arguments":[["Term",["Z","Z"],"Z"]],"meaning":"wrap"}]},{"kind":"data","name":"Terms.Choice""#,
        );
    }
    let checked = check_definitions(&[("definition0", definitions.as_bytes())]).unwrap();
    let digest = &checked.vocabularies["Terms"].digest;
    let law = format!(
        "law \"archsig.law/2\" semantics \"archsig/0.6.0\"; reading Terms {{ use vocabulary Terms version \"1\" digest \"{digest}\"; {script} }}"
    );
    InputSources::from_bytes(
        vec![definitions.into_bytes()],
        law.into_bytes(),
        terms::archmap(digest, "r1").into_bytes(),
    )
}
#[test]
fn closed_term_unknown_condition_keeps_identical_callee_and_containers() {
    let script = r#"
    view pick(s:Sample):Term<(Z,Z)->Z> = if s.p then s.f else s.f;
    view applied(s:Sample):Z = pick(s)(7,3);
    view packed(s:Sample):(Term<(Z,Z)->Z>,List<Term<(Z,Z)->Z>>,Option<Term<(Z,Z)->Z>>,Box) =
      if s.p then (s.f,list<Term<(Z,Z)->Z>>[s.f],some(s.f),Box.Wrap(s.f))
      else (s.f,list<Term<(Z,Z)->Z>>[s.f],some(s.f),Box.Wrap(s.f));
    view differing(s:Sample):Z = (if s.p then s.f else fn(x:Z,y:Z)=>x+y)(7,3);
    "#;
    let r = evaluate_observed_bytes(
        term_branch_sources(script, true),
        &[
            "a=evaluate(Terms.applied,s=@v/s)",
            "p=evaluate(Terms.packed,s=@v/s)",
            "d=evaluate(Terms.differing,s=@v/s)",
        ],
        &mut quiet(),
    )
    .unwrap();
    assert_eq!(r.status(), "partial");
    let w = r.wire();
    assert_eq!(result_value(&w, "a"), &Json::str("11"));
    let f = Json::obj([
        ("params", Json::Arr(vec![Json::str("x"), Json::str("y")])),
        ("body", Json::str("let twice=2*x in twice-y")),
    ]);
    assert_eq!(
        result_value(&w, "p"),
        &Json::Arr(vec![
            f.clone(),
            Json::Arr(vec![f.clone()]),
            Json::obj([("some", f.clone())]),
            Json::obj([("tag", Json::str("Wrap")), ("args", Json::Arr(vec![f]))])
        ])
    );
    let d = arr(get(&w, "answers"))
        .iter()
        .find(|a| get(a, "id") == &Json::str("d"))
        .unwrap();
    assert_eq!(get(d, "status"), &Json::str("undetermined"));
    assert!(!obj(get(d, "outputs")).contains_key("value"));
    assert!(
        arr(get(d, "reasons"))
            .iter()
            .flat_map(|r| arr(get(r, "missing")))
            .any(|m| get(m, "field") == &Json::str("Terms.Sample.p"))
    );
    assert!(!format!("{:?}", get(&w, "issues")).contains("internal"));
    audit_inputs(&r, "r1");
}
#[test]
fn closed_term_boolean_short_circuit_skips_only_unneeded_comparisons() {
    let script = r#"
    view a():Bool=(fn(b:Bool)=>b and ((fn()=>0)=(fn()=>0)))(false);
    view o():Bool=(fn(b:Bool)=>b or ((fn()=>0)=(fn()=>0)))(true);
    view i():Bool=(fn(b:Bool)=>b implies ((fn()=>0)=(fn()=>0)))(false);
    view needed():Bool=(fn(b:Bool)=>b and ((fn()=>0)=(fn()=>0)))(true);
    "#;
    let r = evaluate_observed_bytes(
        term_branch_sources(script, false),
        &[
            "a=evaluate(Terms.a)",
            "o=evaluate(Terms.o)",
            "i=evaluate(Terms.i)",
        ],
        &mut quiet(),
    )
    .unwrap();
    assert_eq!(r.status(), "complete");
    let w = r.wire();
    for (id, b) in [("a", false), ("o", true), ("i", true)] {
        assert_eq!(result_value(&w, id), &Json::Bool(b));
    }
    assert!(matches!(
        evaluate_observed_bytes(
            term_branch_sources(script, false),
            &["n=evaluate(Terms.needed)"],
            &mut quiet()
        ),
        Err(archsig::observed::EvaluationFailure::NotImplemented { .. })
    ));
}

#[test]
fn closed_term_finite_quantifiers_keep_decisive_values_before_unsupported_later_member() {
    let script = r#"
    view allList():Bool=(fn()=>forall b in list<Bool>[false,true] . if b then ((fn()=>0)=(fn()=>0)) else false)();
    view anyList():Bool=(fn()=>exists b in list<Bool>[true,false] . if b then true else ((fn()=>0)=(fn()=>0)))();
    view allType():Bool=(fn()=>forall b:Bool . if b then ((fn()=>0)=(fn()=>0)) else false)();
    view anyType():Bool=(fn()=>exists b:Bool . if b then ((fn()=>0)=(fn()=>0)) else true)();
    view allEmpty():Bool=(fn()=>forall b in list<Bool>[] . b)();
    view anyEmpty():Bool=(fn()=>exists b in list<Bool>[] . b)();
    law required falseAll():(fn()=>forall b in list<Bool>[false,true] . if b then ((fn()=>0)=(fn()=>0)) else false)();
    view allNeeded():Bool=(fn()=>forall b in list<Bool>[false,true] . if b then ((fn()=>0)=(fn()=>0)) else true)();
    view anyNeeded():Bool=(fn()=>exists b in list<Bool>[false,true] . if b then ((fn()=>0)=(fn()=>0)) else false)();
    "#;
    let r = evaluate_observed_bytes(
        term_branch_sources(script, false),
        &[
            "al=evaluate(Terms.allList)",
            "an=evaluate(Terms.anyList)",
            "tl=evaluate(Terms.allType)",
            "tn=evaluate(Terms.anyType)",
            "el=evaluate(Terms.allEmpty)",
            "en=evaluate(Terms.anyEmpty)",
            "c=check(Terms.falseAll)",
        ],
        &mut quiet(),
    )
    .unwrap();
    assert_eq!(r.status(), "complete");
    let w = r.wire();
    for (id, b) in [
        ("al", false),
        ("an", true),
        ("tl", false),
        ("tn", true),
        ("el", true),
        ("en", false),
    ] {
        assert_eq!(result_value(&w, id), &Json::Bool(b));
    }
    let law = arr(get(&w, "answers"))
        .iter()
        .find(|a| get(a, "id") == &Json::str("c"))
        .unwrap();
    assert_eq!(get(law, "status"), &Json::str("refuted"));
    for declaration in ["allNeeded", "anyNeeded"] {
        let ask = format!("n=evaluate(Terms.{declaration})");
        assert!(matches!(
            evaluate_observed_bytes(term_branch_sources(script, false), &[&ask], &mut quiet()),
            Err(archsig::observed::EvaluationFailure::NotImplemented { .. })
        ));
    }
}
