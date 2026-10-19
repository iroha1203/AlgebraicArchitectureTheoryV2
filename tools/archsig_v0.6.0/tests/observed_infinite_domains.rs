//! 検査済み無限型量化を、元の型と域を持つ未決として返す。
#[allow(dead_code)]
#[path = "common/infinite_domains.rs"]
mod fixture;
use archsig::{
    canonical::Json,
    observed::{
        control::{Control, Limits, Usage},
        evaluate_observed_bytes,
    },
};
fn field<'a>(json: &'a Json, key: &str) -> &'a Json {
    let Json::Obj(fields) = json else {
        panic!("object")
    };
    fields.get(key).unwrap_or_else(|| panic!("{key}"))
}
fn array(json: &Json) -> &[Json] {
    let Json::Arr(xs) = json else { panic!("array") };
    xs
}
fn node<'a>(wire: &'a Json, reference: &Json) -> &'a Json {
    array(field(wire, "nodes"))
        .iter()
        .find(|n| field(n, "id") == field(reference, "node"))
        .unwrap()
}
fn refs(json: &Json, output: &mut Vec<String>) {
    match json {
        Json::Obj(o) if o.len() == 1 && o.contains_key("node") => {
            let Json::Str(id) = &o["node"] else { panic!() };
            output.push(id.clone());
        }
        Json::Obj(o) => {
            for v in o.values() {
                refs(v, output)
            }
        }
        Json::Arr(xs) => {
            for v in xs {
                refs(v, output)
            }
        }
        _ => {}
    }
}
fn audit(wire: &Json) {
    let mut earlier = std::collections::BTreeSet::new();
    for n in array(field(wire, "nodes")) {
        let mut used = vec![];
        refs(n, &mut used);
        assert!(used.iter().all(|id| earlier.contains(id)));
        let Json::Str(id) = field(n, "id") else {
            panic!()
        };
        assert!(earlier.insert(id.clone()));
    }
    for answer in array(field(wire, "answers")) {
        let Json::Obj(fields) = answer else { panic!() };
        if let Some(claim) = fields.get("claim") {
            let claim = node(wire, claim);
            assert_eq!(field(claim, "type"), &Json::str("Proposition"));
            assert_eq!(
                field(field(claim, "judgment"), "status"),
                field(answer, "status")
            );
            assert_eq!(
                field(field(claim, "judgment"), "evidence"),
                field(answer, "evidence")
            );
        }
    }
}
#[test]
fn infinite_text_quantifier_returns_typed_undetermined_through_actual_call() {
    let inputs = fixture::input(
        "view inner(n:Node):Bool=forall text:Text.text=text; view caller(n:Node):Bool=inner(n);",
        "Z",
        &[],
        "r1",
    );
    let result = evaluate_observed_bytes(
        inputs.clone(),
        &["v=evaluate(Walk.caller,n=@v/p)"],
        &mut Control::new(Limits::default(), |_| Usage::default()),
    )
    .expect("検査済み無限型の算法非対応は型付き未決へ接続する");
    assert_eq!(result.prepared().inputs().sources(), &inputs);
    let wire = result.wire();
    audit(&wire);
    assert_eq!(result.status(), "partial", "{:?}", field(&wire, "issues"));
    let Json::Arr(answers) = field(&wire, "answers") else {
        panic!()
    };
    assert_eq!(answers.len(), 1);
    assert_eq!(field(&answers[0], "status"), &Json::str("undetermined"));
    assert!(
        matches!(field(&answers[0], "outputs"), Json::Obj(o) if !o.contains_key("value") && o.contains_key("evaluation"))
    );
    let Json::Arr(reasons) = field(&answers[0], "reasons") else {
        panic!()
    };
    assert!(
        reasons
            .iter()
            .any(|r| field(r, "code") == &Json::str("unsupported_algorithm"))
    );
}

#[test]
fn infinite_explicit_types_preserve_original_domain_kind_and_binder() {
    for ty in [
        "Text",
        "List<Z>",
        "Tree",
        "Infinite",
        "Option<Text>",
        "Set<Text>",
        "(Text,Z)",
    ] {
        for kind in ["forall", "exists"] {
            let script = format!("view current():Bool={kind} item:{ty}.item=item;");
            let result = evaluate_observed_bytes(
                fixture::input(&script, "Z", &[], "r1"),
                &["v=evaluate(Walk.current)"],
                &mut Control::new(Limits::default(), |_| Usage::default()),
            )
            .unwrap();
            let wire = result.wire();
            audit(&wire);
            assert_eq!(
                result.status(),
                "partial",
                "{script}: {:?}",
                field(&wire, "issues")
            );
            let Json::Arr(answers) = field(&wire, "answers") else {
                panic!()
            };
            assert_eq!(field(&answers[0], "status"), &Json::str("undetermined"));
            let Json::Arr(qs) = field(field(&answers[0], "scope"), "quantifiers") else {
                panic!()
            };
            let q = qs
                .iter()
                .find(|q| field(q, "name") == &Json::str("item"))
                .unwrap();
            assert_eq!(field(q, "kind"), &Json::str(kind));
            let Json::Arr(nodes) = field(&wire, "nodes") else {
                panic!()
            };
            let domain = nodes
                .iter()
                .find(|n| field(n, "id") == field(field(q, "domain"), "node"))
                .unwrap();
            assert_eq!(field(domain, "type"), &Json::str("Domain"));
            assert_eq!(field(field(domain, "value"), "kind"), &Json::str("type"));
            assert_eq!(field(field(domain, "value"), "type"), field(q, "type"));
            let Json::Arr(reasons) = field(&answers[0], "reasons") else {
                panic!()
            };
            assert!(
                reasons
                    .iter()
                    .any(|r| field(r, "code") == &Json::str("unsupported_algorithm"))
            );
        }
    }
}
#[test]
fn infinite_free_law_parameters_and_mixed_finite_domains_return_claims() {
    for params in [
        "item:Text",
        "item:List<Z>",
        "item:Tree",
        "item:Infinite",
        "b:Bool,item:Text",
        "item:Text,b:Bool",
        "z:Q,item:Text",
        "item:Text,z:Z",
    ] {
        let script = format!("law required current({params}):item=item;");
        let result = evaluate_observed_bytes(
            fixture::input(&script, "Z", &[], "r1"),
            &["v=check(Walk.current)"],
            &mut Control::new(Limits::default(), |_| Usage::default()),
        )
        .unwrap();
        let wire = result.wire();
        audit(&wire);
        assert_eq!(
            result.status(),
            "partial",
            "{params}: {:?}",
            field(&wire, "issues")
        );
        let Json::Arr(answers) = field(&wire, "answers") else {
            panic!()
        };
        assert_eq!(field(&answers[0], "status"), &Json::str("undetermined"));
        assert!(matches!(&answers[0],Json::Obj(o) if o.contains_key("claim")));
    }
}

#[test]
fn infinite_nested_calls_keep_missing_reasons_prior_results_and_dependency() {
    let script = "view inner(n:Node):Bool=forall item:Text.(item=item) and n.mark=0; view middle(n:Node):Bool=let use_inner=true in if use_inner then inner(n) else false; view current(n:Node):Bool=forall z:Z.middle(n); view keep(x:Bool):Bool=x;";
    let inputs = fixture::input(script, "Z", &["p-mark"], "r1");
    let asks = [
        "seed=evaluate(Walk.seed)",
        "prior=check(Walk.prior)",
        "v=evaluate(Walk.current,n=@v/p)",
        "later=evaluate(Walk.keep,x=$v.value)",
    ];
    let result = evaluate_observed_bytes(
        inputs.clone(),
        &asks,
        &mut Control::new(Limits::default(), |_| Usage::default()),
    )
    .unwrap();
    let wire = result.wire();
    audit(&wire);
    assert_eq!(result.status(), "partial", "{:?}", field(&wire, "issues"));
    let Json::Arr(answers) = field(&wire, "answers") else {
        panic!()
    };
    assert_eq!(field(&answers[0], "status"), &Json::str("established"));
    assert_eq!(field(&answers[1], "status"), &Json::str("refuted"));
    assert!(matches!(&answers[1],Json::Obj(o) if o.contains_key("claim")));
    for i in [2, 3] {
        assert_eq!(field(&answers[i], "status"), &Json::str("undetermined"));
        let Json::Arr(reasons) = field(&answers[i], "reasons") else {
            panic!()
        };
        assert!(
            reasons
                .iter()
                .any(|r| field(r, "code") == &Json::str("missing_observation"))
        );
        assert!(reasons.iter().any(|r|field(r,"code")==&Json::str("unsupported_algorithm") && matches!(field(field(r,"details"),"operand_types"),Json::Arr(types) if types.contains(&Json::str("Text")))));
    }
    let Json::Arr(reasons) = field(&answers[3], "reasons") else {
        panic!()
    };
    assert!(
        reasons
            .iter()
            .any(|r| field(r, "code") == &Json::str("dependency_blocked"))
    );
    assert!(matches!(field(&answers[3],"outputs"),Json::Obj(o) if o.is_empty()));
    assert_eq!(result.prepared().inputs().sources(), &inputs);
}

#[test]
fn infinite_domains_preserve_current_provenance_without_changing_mathematical_answers() {
    let script = "view current(n:Node):Bool=forall item:Text.(item=item) and n.mark=2;";
    let mut pair = vec![];
    for revision in ["r1", "r2"] {
        let input = fixture::input(script, "Z", &[], revision);
        let result = evaluate_observed_bytes(
            input.clone(),
            &["v=evaluate(Walk.current,n=@v/p)"],
            &mut Control::new(Limits::default(), |_| Usage::default()),
        )
        .unwrap();
        assert_eq!(result.status(), "partial");
        let wire = result.wire();
        audit(&wire);
        let checked = result.prepared().inputs().archmap();
        let subject = checked
            .snapshots
            .iter()
            .find(|s| s.id == "v")
            .unwrap()
            .subjects
            .iter()
            .find(|s| s.id == "p")
            .unwrap();
        let slot = subject
            .fields
            .iter()
            .find(|f| f.name == "Paths.Node.mark")
            .unwrap();
        let archsig::archmap::Slot::Known { atom, origin, .. } = &slot.slot else {
            panic!()
        };
        assert!(array(field(&wire,"nodes")).iter().flat_map(|n|array(field(n,"support"))).any(|fact|matches!(fact,Json::Obj(o) if o.get("field")==Some(&Json::str("Paths.Node.mark"))&&o.get("subject")==Some(&Json::str("p"))&&o.get("atom")==Some(&Json::str(atom)))));
        let origin = checked.origins.iter().find(|o| &o.id == origin).unwrap();
        assert!(!origin.locations.is_empty());
        for at in &origin.locations {
            let source = checked.sources.iter().find(|s| s.id == at.source).unwrap();
            assert_eq!(source.revision, revision);
            assert_eq!(
                at.span,
                Some(if revision == "r1" { (0, 1) } else { (10, 11) })
            );
        }
        pair.push(wire);
    }
    assert_ne!(field(&pair[0], "inputs"), field(&pair[1], "inputs"));
    assert_eq!(field(&pair[0], "nodes"), field(&pair[1], "nodes"));
    assert_eq!(field(&pair[0], "answers"), field(&pair[1], "answers"));
}
#[test]
fn infinite_domains_keep_constant_short_circuit_and_finite_numeric_decisions() {
    for (body, expected) in [
        ("forall t:Text.false and t=t", false),
        ("exists t:Text.true or t=t", true),
        ("forall t:List<Z>.true", true),
        ("exists t:Tree.false", false),
        ("forall t:Tree.true", true),
        ("forall z:Z.z+count(set{x|x in list<Z>[1,2]})=z+2", true),
    ] {
        let script = format!("view current():Bool={body};law required required_value():{body};");
        let result = evaluate_observed_bytes(
            fixture::input(&script, "Z", &[], "r1"),
            &["v=evaluate(Walk.current)", "c=check(Walk.required_value)"],
            &mut Control::new(Limits::default(), |_| Usage::default()),
        )
        .unwrap();
        let wire = result.wire();
        audit(&wire);
        assert_eq!(
            result.status(),
            "complete",
            "{body}: {:?}",
            field(&wire, "issues")
        );
        let answers = array(field(&wire, "answers"));
        assert_eq!(field(&answers[0], "status"), &Json::str("established"));
        assert_eq!(
            field(
                node(&wire, field(field(&answers[0], "outputs"), "value")),
                "value"
            ),
            &Json::Bool(expected)
        );
        assert_eq!(
            field(&answers[1], "status"),
            &Json::str(if expected { "established" } else { "refuted" })
        );
        assert!(!array(field(&answers[1], "evidence")).is_empty());
    }
}

#[test]
fn infinite_typed_frontiers_keep_literal_collection_and_match_source_expressions() {
    for body in [
        r#"forall text:Text.text="seen""#,
        "exists xs:List<Z>.count(xs)=0",
        "forall value:Infinite.match value {Amount(n)=>n=0;}",
        "exists tree:Tree.match tree {End=>true;Next(rest)=>false;}",
    ] {
        let script = format!("view current():Bool={body};");
        let input = fixture::input(&script, "Z", &[], "r1");
        let result = evaluate_observed_bytes(
            input.clone(),
            &["v=evaluate(Walk.current)"],
            &mut Control::new(Limits::default(), |_| Usage::default()),
        )
        .unwrap();
        let wire = result.wire();
        audit(&wire);
        assert_eq!(
            result.status(),
            "partial",
            "{body}: {:?}",
            field(&wire, "issues")
        );
        let answer = &array(field(&wire, "answers"))[0];
        assert_eq!(field(answer, "status"), &Json::str("undetermined"));
        assert!(
            array(field(answer, "reasons"))
                .iter()
                .any(|r| field(r, "code") == &Json::str("unsupported_algorithm"))
        );
        let whole = node(&wire, field(field(answer, "outputs"), "evaluation"));
        let source = node(&wire, field(field(whole, "value"), "expression"));
        let span = array(field(field(field(source, "value"), "location"), "span"));
        let (Json::Nat(a), Json::Nat(b)) = (&span[0], &span[1]) else {
            panic!()
        };
        assert_eq!(
            &input.law().bytes()[*a as usize..*b as usize],
            body.as_bytes()
        );
        assert!(!array(field(field(answer, "scope"), "quantifiers")).is_empty());
    }
}
