//! 明示In量化を独立三入力から評価し、有限域・原出現・欠測・証拠と停止prefixを確認する。
mod common;
use archsig::{
    canonical::Json,
    definition::check_definitions_controlled,
    law::{
        ast::{ExprKind, QuantDomain, QuantSplit},
        model::Signature,
    },
    observed::{
        control::{Checkpoint, Control, Limits, Usage},
        evaluate_observed_bytes,
        input::{CheckedInputs, InputSources, check_inputs},
    },
    result::Signal,
};
use std::{
    cell::Cell,
    collections::{BTreeMap, BTreeSet},
    rc::Rc,
};
fn quiet() -> Control {
    Control::new(Limits::default(), |_| Usage::default())
}
fn obj(j: &Json) -> &BTreeMap<String, Json> {
    let Json::Obj(v) = j else {
        panic!("object: {j:?}")
    };
    v
}
fn arr(j: &Json) -> &[Json] {
    let Json::Arr(v) = j else {
        panic!("array: {j:?}")
    };
    v
}
fn text(j: &Json) -> &str {
    let Json::Str(v) = j else {
        panic!("string: {j:?}")
    };
    v
}
fn f<'a>(j: &'a Json, key: &str) -> &'a Json {
    &obj(j)[key]
}
fn val(j: &Json) -> &Json {
    assert_eq!(f(j, "state"), &Json::str("value"));
    f(j, "value")
}
fn index(j: &Json) -> BTreeMap<&str, &Json> {
    arr(f(j, "nodes"))
        .iter()
        .map(|n| (text(f(n, "id")), n))
        .collect()
}
fn target<'a>(ns: &BTreeMap<&str, &'a Json>, reference: &Json, ty: &Json) -> &'a Json {
    assert_eq!(obj(reference).len(), 1);
    let node = ns[text(f(reference, "node"))];
    assert_eq!(f(node, "type"), ty);
    node
}
fn answer<'a>(j: &'a Json, id: &str) -> &'a Json {
    arr(f(j, "answers"))
        .iter()
        .find(|a| text(f(a, "id")) == id)
        .unwrap()
}
fn refs(j: &Json, out: &mut Vec<String>) {
    match j {
        Json::Obj(m) if m.len() == 1 && m.contains_key("node") => out.push(text(&m["node"]).into()),
        Json::Obj(m) => {
            for value in m.values() {
                refs(value, out);
            }
        }
        Json::Arr(a) => {
            for value in a {
                refs(value, out);
            }
        }
        _ => {}
    }
}
fn reached(ns: &BTreeMap<&str, &Json>, roots: &[&Json]) -> BTreeSet<String> {
    let mut todo = vec![];
    for root in roots {
        refs(root, &mut todo);
    }
    let mut seen = BTreeSet::new();
    while let Some(id) = todo.pop() {
        if seen.insert(id.clone()) {
            refs(ns[id.as_str()], &mut todo);
        }
    }
    seen
}
fn span(location: &Json) -> (usize, usize) {
    assert_eq!(f(location, "input"), &Json::str("law"));
    let a = arr(f(location, "span"));
    let nat = |j: &Json| {
        let Json::Nat(n) = j else { panic!("Nat") };
        *n as usize
    };
    (nat(&a[0]), nat(&a[1]))
}
fn expression<'a>(ns: &BTreeMap<&str, &'a Json>, evaluation: &Json) -> &'a Json {
    target(
        ns,
        f(val(evaluation), "expression"),
        &Json::str("Expression"),
    )
}
fn evaluation_span(ns: &BTreeMap<&str, &Json>, evaluation: &Json) -> (usize, usize) {
    span(f(val(expression(ns, evaluation)), "location"))
}
// Law適用の集約は、通常の元式Evaluationと異なりLawInstanceを第一引数に持つ。
fn aggregate_instance<'a>(ns: &BTreeMap<&str, &'a Json>, evaluation: &Json) -> Option<&'a Json> {
    let first = arr(f(evaluation, "arguments")).first()?;
    let node = ns[text(f(first, "node"))];
    (f(node, "type") == &Json::str("LawInstance")).then_some(node)
}
fn part(evaluation: &Json) -> &Json {
    let parts = arr(f(val(evaluation), "parts"));
    assert_eq!(parts.len(), 1);
    &parts[0]
}

fn run(inputs: InputSources, asks: &[&str]) -> (Json, CheckedInputs) {
    let checked = check_inputs(inputs.clone(), &mut quiet())
        .unwrap_or_else(|e| panic!("入力: {:?}", e.issues()));
    let wire = evaluate_observed_bytes(inputs, asks, &mut quiet())
        .unwrap_or_else(|e| panic!("評価: {e:?}"))
        .wire();
    audit(&wire, &checked);
    (wire, checked)
}
fn output<'a>(wire: &'a Json, id: &str, ty: &Json, expected: Json) -> &'a Json {
    let a = answer(wire, id);
    assert_eq!(
        f(a, "status"),
        &Json::str("established"),
        "{id}; issues: {:?}",
        f(wire, "issues")
    );
    assert!(
        !obj(a).contains_key("claim"),
        "Boolも値の問いはclaimを持たない"
    );
    assert_eq!(
        val(target(&index(wire), f(f(a, "outputs"), "value"), ty)),
        &expected,
        "{id}"
    );
    a
}
fn audit(wire: &Json, checked: &CheckedInputs) {
    let ns = index(wire);
    let mut earlier = BTreeSet::new();
    for n in arr(f(wire, "nodes")) {
        let mut links = vec![];
        refs(n, &mut links);
        for id in links {
            assert!(earlier.contains(id.as_str()), "既出Ref: {id}");
        }
        assert!(earlier.insert(text(f(n, "id"))));
        if f(n, "type") != &Json::str("Proposition") {
            assert!(!obj(n).contains_key("judgment"));
        }
        if let Some(v) = obj(n).get("value") {
            let mut links = vec![];
            refs(v, &mut links);
            for id in links {
                assert_ne!(f(ns[id.as_str()], "state"), &Json::str("blocked"));
                assert!(!obj(ns[id.as_str()]).contains_key("partial"));
            }
        }
        for fact in arr(f(n, "support")) {
            assert_eq!(f(fact, "snapshot"), &Json::str("v"));
            let subject = checked.archmap().snapshots[0]
                .subjects
                .iter()
                .find(|s| s.id == text(f(fact, "subject")))
                .unwrap();
            let origin = if let Some(field) = obj(fact).get("field") {
                let slot = &subject
                    .fields
                    .iter()
                    .find(|s| s.name == text(field))
                    .unwrap()
                    .slot;
                let archsig::archmap::Slot::Known {
                    atom,
                    origin,
                    pointer,
                    ..
                } = slot
                else {
                    panic!("欠測は支持Atomでない")
                };
                assert_eq!(f(fact, "atom"), &Json::str(atom));
                assert!(pointer.starts_with("/snapshots/0/atoms/"));
                origin
            } else {
                &subject.origin
            };
            let origin = checked
                .archmap()
                .origins
                .iter()
                .find(|o| &o.id == origin)
                .unwrap();
            assert_eq!(origin.mode, archsig::archmap::Mode::Specification);
            let at = &origin.locations[0];
            let cited_source = checked
                .archmap()
                .sources
                .iter()
                .find(|s| s.id == at.source)
                .unwrap();
            assert_eq!(
                at.path,
                if obj(fact).contains_key("field") {
                    "values.model"
                } else {
                    "subjects.model"
                }
            );
            assert_eq!(
                at.span,
                Some(if obj(fact).contains_key("field") {
                    if cited_source.revision == "r2" {
                        (7, 9)
                    } else {
                        (2, 5)
                    }
                } else {
                    (0, 1)
                })
            );
            assert_eq!(
                checked
                    .archmap()
                    .sources
                    .iter()
                    .find(|s| s.id == at.source)
                    .unwrap()
                    .uri,
                "urn:fixture:quantification"
            );
        }
        if f(n, "type") == &Json::str("Expression") && f(val(n), "kind") == &Json::str("source") {
            assert!(arr(f(val(n), "parameters")).is_empty());
            let at = span(f(val(n), "location"));
            assert_eq!(span(f(f(n, "rule"), "location")), at);
            assert!(at.0 < at.1 && at.1 <= checked.sources().law().bytes().len());
        }
        if f(n, "type") == &Json::str("Evaluation") {
            if aggregate_instance(&ns, n).is_none() {
                assert_eq!(
                    f(val(expression(&ns, n)), "bindings"),
                    f(val(n), "bindings")
                );
                assert_eq!(span(f(part(n), "location")), evaluation_span(&ns, n));
            }
            for p in arr(f(val(n), "parts")) {
                for child in arr(f(p, "children")) {
                    for fact in arr(f(target(&ns, child, &Json::str("Evaluation")), "support")) {
                        assert!(arr(f(n, "support")).contains(fact));
                    }
                }
            }
        }
        if f(n, "type") == &Json::str("Domain") && f(val(n), "kind") == &Json::str("finite") {
            for element in arr(f(val(n), "elements")) {
                val(target(&ns, element, f(val(n), "type")));
            }
        }
        if f(n, "type") == &Json::str("Evidence")
            && f(val(n), "kind") == &Json::str("finite_exhaustion")
        {
            let data = f(val(n), "data");
            target(&ns, f(data, "domain"), &Json::str("Domain"));
            assert_eq!(
                f(data, "checked"),
                &Json::Nat(arr(f(data, "instances")).len() as u64)
            );
            for instance in arr(f(data, "instances")) {
                let evaluation = target(&ns, instance, &Json::str("Evaluation"));
                val(target(&ns, f(val(evaluation), "value"), &Json::str("Bool")));
            }
        }
    }
    for a in arr(f(wire, "answers")) {
        let mut links = vec![];
        refs(a, &mut links);
        for id in links {
            assert!(ns.contains_key(id.as_str()));
        }
        for q in arr(f(f(a, "scope"), "quantifiers")) {
            assert!(["forall", "exists"].contains(&text(f(q, "kind"))));
            if let Some(domain) = obj(q).get("domain") {
                let domain = target(&ns, domain, &Json::str("Domain"));
                assert_eq!(f(val(domain), "type"), f(q, "type"));
            }
        }
    }
}
fn root<'a>(wire: &'a Json, id: &str) -> &'a Json {
    target(
        &index(wire),
        f(f(answer(wire, id), "outputs"), "evaluation"),
        &Json::str("Evaluation"),
    )
}
fn source<'a>(checked: &'a CheckedInputs, at: (usize, usize)) -> &'a [u8] {
    &checked.sources().law().bytes()[at.0..at.1]
}
fn declared_body(checked: &CheckedInputs, name: &str) -> usize {
    let Signature::View { body, .. } = &checked.law().declarations[name].signature else {
        panic!("view")
    };
    *body
}

fn ty(kind: &str, item: Json) -> Json {
    Json::Arr(vec![Json::str(kind), item])
}
fn numbers(values: &[&str]) -> Json {
    Json::Arr(values.iter().map(|v| Json::str(*v)).collect())
}
fn reference(subject: &str) -> Json {
    Json::Arr(vec![Json::str("v"), Json::str(subject)])
}
fn fixture(script: &str, peer_flag: bool, reverse: bool) -> InputSources {
    use common::{
        constructor_json, data_json, definition_json, entity_json, field_json, vocabulary_json,
    };
    let fields = [
        ("nums", r#"["List","Z"]"#),
        ("setnums", r#"["Set","Z"]"#),
        ("refs", r#"["List",["Ref","Quantification.Sample"]]"#),
        ("zero", r#""Z""#),
        ("prime", r#"["Fp","5"]"#),
        ("missinglist", r#"["List","Z"]"#),
        ("flag", r#""Bool""#),
    ]
    .into_iter()
    .map(|(n, t)| field_json(n, t))
    .collect::<Vec<_>>()
    .join(",");
    let entity = entity_json("Quantification.Sample", "[]", &format!("[{fields}]"));
    let data = data_json(
        "Quantification.Tag",
        &format!(
            "[{},{}]",
            constructor_json("Low", "[]"),
            constructor_json("High", "[]")
        ),
    );
    let definitions = definition_json(&format!(
        "[{}]",
        vocabulary_json("Quantification", &format!("[{entity},{data}]"), "[]")
    ));
    let checked =
        check_definitions_controlled(&[("definition0", definitions.as_bytes())], &mut quiet())
            .unwrap();
    let digest = &checked.vocabularies["Quantification"].digest;
    let law = format!(
        r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Calc {{ use vocabulary Quantification version "1" digest "{digest}"; {script} }}"#
    );
    let subjects = if reverse {
        vec![reference("peer"), reference("sample")]
    } else {
        vec![reference("sample"), reference("peer")]
    };
    let values = [
        ("nums", numbers(&["1", "1", "2"])),
        ("setnums", numbers(&["2", "1"])),
        ("refs", Json::Arr(subjects)),
        ("zero", Json::str("0")),
        ("prime", Json::str("4")),
    ];
    let mut atoms=values.into_iter().map(|(name,value)|format!(r#"{{"id":"{name}","subject":"sample","field":"Quantification.Sample.{name}","value":{},"origin":"values"}}"#,value.canonical())).collect::<Vec<_>>();
    atoms.push(format!(r#"{{"id":"peerflag","subject":"peer","field":"Quantification.Sample.flag","value":{peer_flag},"origin":"values"}}"#));
    let atoms = atoms.join(",");
    let map = format!(
        r#"{{"format":"archsig.archmap/2","semantics":"archsig/0.6.0",
"vocabularies":[{{"namespace":"Quantification","version":"1","digest":"{digest}"}}],
"sources":[{{"id":"scan","uri":"urn:fixture:quantification","revision":"r1","digest":"sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"}}],
"origins":[{{"id":"base","mode":"specification","method":"対象を提示する。","locations":[{{"source":"scan","path":"subjects.model","span":[0,1]}}]}},
{{"id":"values","mode":"specification","method":"fieldの観測。","locations":[{{"source":"scan","path":"values.model","span":[2,5]}}]}}],
"snapshots":[{{"id":"v","origin":"base","subjects":[{{"id":"sample","type":"Quantification.Sample","origin":"base"}},{{"id":"peer","type":"Quantification.Sample","origin":"base"}}],"atoms":[{atoms}]}}]}}"#
    );
    InputSources::from_bytes(
        vec![definitions.into_bytes()],
        law.into_bytes(),
        map.into_bytes(),
    )
}
fn children<'a>(ns: &BTreeMap<&str, &'a Json>, evaluation: &Json) -> Vec<&'a Json> {
    arr(f(part(evaluation), "children"))
        .iter()
        .map(|r| target(ns, r, &Json::str("Evaluation")))
        .collect()
}
fn evaluations_at<'a>(wire: &'a Json, at: (usize, usize)) -> Vec<&'a Json> {
    let ns = index(wire);
    arr(f(wire, "nodes"))
        .iter()
        .filter(|n| {
            f(n, "type") == &Json::str("Evaluation")
                && aggregate_instance(&ns, n).is_none()
                && evaluation_span(&ns, n) == at
        })
        .collect()
}
fn evidence<'a>(ns: &BTreeMap<&str, &'a Json>, root: &Json, kind: &str) -> Vec<&'a Json> {
    reached(ns, &[root])
        .iter()
        .map(|id| ns[id.as_str()])
        .filter(|n| f(n, "type") == &Json::str("Evidence") && f(val(n), "kind") == &Json::str(kind))
        .collect()
}
fn quantifier_domain<'a>(
    wire: &'a Json,
    id: &str,
    name: &str,
    kind: &str,
    element_type: &Json,
) -> &'a Json {
    let scope = f(answer(wire, id), "scope");
    let q = arr(f(scope, "quantifiers"))
        .iter()
        .find(|q| f(q, "name") == &Json::str(name) && f(q, "kind") == &Json::str(kind))
        .unwrap();
    assert_eq!(f(q, "type"), element_type);
    let domain = target(&index(wire), f(q, "domain"), &Json::str("Domain"));
    assert_eq!(f(val(domain), "kind"), &Json::str("finite"));
    assert_eq!(f(val(domain), "type"), element_type);
    domain
}
fn domain_values(wire: &Json, domain: &Json) -> Vec<String> {
    let ns = index(wire);
    let item_type = f(val(domain), "type");
    let mut values = arr(f(val(domain), "elements"))
        .iter()
        .map(|r| val(target(&ns, r, item_type)).canonical())
        .collect::<Vec<_>>();
    values.sort();
    values
}
fn assert_missing(
    wire: &Json,
    id: &str,
    field: &str,
    expression_text: &[u8],
    checked: &CheckedInputs,
) {
    let ns = index(wire);
    let reasons = arr(f(answer(wire, id), "reasons"))
        .iter()
        .filter(|r| f(r, "code") == &Json::str("missing_observation"))
        .collect::<Vec<_>>();
    assert!(!reasons.is_empty(), "{id}の読取済missing");
    for reason in reasons {
        assert_eq!(
            arr(f(reason, "missing")),
            &[Json::obj([
                ("snapshot", Json::str("v")),
                ("subject", Json::str("sample")),
                ("field", Json::str(format!("Quantification.Sample.{field}")))
            ])]
        );
        let deps = arr(f(reason, "dependencies"));
        assert!(!deps.is_empty());
        for dep in deps {
            let e = target(&ns, dep, &Json::str("Expression"));
            assert_eq!(
                source(checked, span(f(val(e), "location"))),
                expression_text
            );
        }
    }
}
fn quant_parts(checked: &CheckedInputs, body: usize) -> (usize, usize) {
    let ExprKind::Quant {
        split:
            QuantSplit::Fixed {
                domain: QuantDomain::In(domain),
                body,
            },
        ..
    } = &checked.law().exprs[body].kind
    else {
        panic!("検査済In量化")
    };
    (*domain, *body)
}
fn check_claim(wire: &Json, id: &str, status: &str) {
    let a = answer(wire, id);
    assert_eq!(f(a, "status"), &Json::str(status));
    let ns = index(wire);
    let claim = target(&ns, f(a, "claim"), &Json::str("Proposition"));
    assert_eq!(f(f(claim, "judgment"), "status"), &Json::str(status));
    assert!(!arr(f(claim, "evidence")).is_empty());
}

#[test]
fn in_quantifiers_keep_distinct_domains_original_occurrences_and_evidence() {
    let script = r#"
view all_list(s: Sample): Bool = forall n in s.nums . n>0;
view all_set(s: Sample): Bool = forall n in s.setnums . n>0;
view no_witness(): Bool = exists n in list<Z>[1,1,2] . n>9;
view empty_all(): Bool = forall q in list<Q>[] . q>0;
view empty_exists(): Bool = exists t in set<Tag>{} . t=Low;
view rational(): Bool = forall q in list<Q>[rat(1,2),rat(2,3)] . q>0;
view residue(): Bool = forall p in list<Fp(5)>[0,4] . p=p;
view tagged(): Bool = exists t in list<Tag>[Low,High] . match t { Low => false; High => true; };
view all_true(): Bool = forall b in list<Bool>[true,true] . b;
view all_false(): Bool = exists b in list<Bool>[false,false] . b;
law required rejected(): forall b in list<Bool>[true,false] . b;
"#;
    let asks = [
        "a=evaluate(Calc.all_list,s=@v/sample)",
        "b=evaluate(Calc.all_set,s=@v/sample)",
        "c=evaluate(Calc.no_witness)",
        "d=evaluate(Calc.empty_all)",
        "e=evaluate(Calc.empty_exists)",
        "f=evaluate(Calc.rational)",
        "g=evaluate(Calc.residue)",
        "h=evaluate(Calc.tagged)",
        "j=check(Calc.rejected)",
        "k=evaluate(Calc.all_true)",
        "m=evaluate(Calc.all_false)",
    ];
    let (wire, checked) = run(fixture(script, false, false), &asks);
    assert_eq!(f(&wire, "status"), &Json::str("complete"));
    for (id, v) in [
        ("a", true),
        ("b", true),
        ("c", false),
        ("d", true),
        ("e", false),
        ("f", true),
        ("g", true),
        ("h", true),
        ("k", true),
        ("m", false),
    ] {
        output(&wire, id, &Json::str("Bool"), Json::Bool(v));
    }
    check_claim(&wire, "j", "refuted");
    let ns = index(&wire);
    let (domain, body) = quant_parts(&checked, declared_body(&checked, "Calc.all_list"));
    let original_children = children(&ns, root(&wire, "a"));
    assert_eq!(
        evaluation_span(&ns, original_children[0]),
        checked.law().exprs[domain].span
    );
    assert_eq!(
        val(target(
            &ns,
            f(val(original_children[0]), "value"),
            &ty("List", Json::str("Z"))
        )),
        &numbers(&["1", "1", "2"])
    );
    let bodies = original_children
        .iter()
        .filter(|e| evaluation_span(&ns, e) == checked.law().exprs[body].span)
        .collect::<Vec<_>>();
    assert_eq!(
        bodies.len(),
        2,
        "bodyはdistinct域、元List三出現はcollection値に保つ"
    );
    let domain = quantifier_domain(&wire, "a", "n", "forall", &Json::str("Z"));
    assert_eq!(
        domain_values(&wire, domain),
        vec![Json::str("1").canonical(), Json::str("2").canonical()]
    );
    assert!(
        reached(&ns, &[domain]).contains(text(f(original_children[0], "id"))),
        "Domainは元collectionに依存する"
    );
    for body in bodies {
        assert_eq!(
            val(target(&ns, f(val(body), "value"), &Json::str("Bool"))),
            &Json::Bool(true)
        );
        assert!(reached(&ns, &[body]).contains(text(f(original_children[0], "id"))));
        assert!(
            arr(f(val(body), "bindings"))
                .iter()
                .all(|b| f(b, "name") != &Json::str("n")),
            "量化binderは自由parameterでない"
        );
    }
    for (id, name, kind, t) in [
        ("d", "q", "forall", Json::str("Q")),
        (
            "e",
            "t",
            "exists",
            ty("Data", Json::str("Quantification.Tag")),
        ),
    ] {
        let domain = quantifier_domain(&wire, id, name, kind, &t);
        assert!(arr(f(val(domain), "elements")).is_empty());
        let proofs = evidence(&ns, answer(&wire, id), "finite_exhaustion");
        assert!(!proofs.is_empty());
        for proof in proofs {
            let data = f(val(proof), "data");
            assert_eq!(
                f(data, "domain"),
                &Json::obj([("node", f(domain, "id").clone())])
            );
            assert_eq!(f(data, "checked"), &Json::Nat(0));
            assert!(arr(f(data, "instances")).is_empty());
        }
    }
    let proofs = evidence(&ns, answer(&wire, "a"), "finite_exhaustion");
    assert!(!proofs.is_empty());
    for proof in proofs {
        let data = f(val(proof), "data");
        assert_eq!(
            f(data, "domain"),
            &Json::obj([("node", f(domain, "id").clone())])
        );
        let instances = arr(f(data, "instances"));
        assert_eq!(instances.len(), 2);
        assert_eq!(f(data, "checked"), &Json::Nat(2));
        for r in instances {
            let e = target(&ns, r, &Json::str("Evaluation"));
            assert_eq!(evaluation_span(&ns, e), checked.law().exprs[body].span);
            assert_eq!(
                val(target(&ns, f(val(e), "value"), &Json::str("Bool"))),
                &Json::Bool(true)
            );
        }
        let mut bound = instances
            .iter()
            .map(|r| {
                let body = target(&ns, r, &Json::str("Evaluation"));
                let binder = children(&ns, body)
                    .into_iter()
                    .find(|e| source(&checked, evaluation_span(&ns, e)) == b"n")
                    .unwrap();
                assert_eq!(
                    arr(f(part(binder), "children")),
                    &[Json::obj([("node", f(original_children[0], "id").clone())])]
                );
                let scalar = target(&ns, f(val(binder), "value"), &Json::str("Z"));
                assert_eq!(
                    arr(f(scalar, "arguments")),
                    &[Json::obj([("node", f(original_children[0], "id").clone())])]
                );
                val(scalar).canonical()
            })
            .collect::<Vec<_>>();
        bound.sort();
        assert_eq!(
            bound,
            vec![Json::str("1").canonical(), Json::str("2").canonical()],
            "全coverageは実binderを尽くす"
        );
    }
    // Setの表示順を変えても同じ元集合と数学判断を得る。
    let input = fixture(script, false, false);
    let map = String::from_utf8(input.archmap().bytes().to_vec())
        .unwrap()
        .replace(
            r#""field":"Quantification.Sample.setnums","value":["2","1"]"#,
            r#""field":"Quantification.Sample.setnums","value":["1","2"]"#,
        );
    let reordered = InputSources::from_bytes(
        input
            .definitions()
            .iter()
            .map(|d| d.bytes().to_vec())
            .collect(),
        input.law().bytes().to_vec(),
        map.into_bytes(),
    );
    let (other, _) = run(reordered, &[asks[1]]);
    output(&other, "b", &Json::str("Bool"), Json::Bool(true));
    assert_eq!(
        domain_values(
            &wire,
            quantifier_domain(&wire, "b", "n", "forall", &Json::str("Z"))
        ),
        domain_values(
            &other,
            quantifier_domain(&other, "b", "n", "forall", &Json::str("Z"))
        )
    );
    let input = fixture(script, false, false);
    let map = String::from_utf8(input.archmap().bytes().to_vec())
        .unwrap()
        .replace(r#""revision":"r1""#, r#""revision":"r2""#)
        .replace(r#""span":[2,5]"#, r#""span":[7,9]"#);
    let moved = InputSources::from_bytes(
        input
            .definitions()
            .iter()
            .map(|d| d.bytes().to_vec())
            .collect(),
        input.law().bytes().to_vec(),
        map.into_bytes(),
    );
    let (moved, moved_checked) = run(moved, &[asks[0]]);
    output(&moved, "a", &Json::str("Bool"), Json::Bool(true));
    assert_eq!(
        domain_values(
            &wire,
            quantifier_domain(&wire, "a", "n", "forall", &Json::str("Z"))
        ),
        domain_values(
            &moved,
            quantifier_domain(&moved, "a", "n", "forall", &Json::str("Z"))
        )
    );
    assert_eq!(moved_checked.archmap().sources[0].revision, "r2");
    assert_eq!(
        moved_checked
            .archmap()
            .origins
            .iter()
            .find(|o| o.id == "values")
            .unwrap()
            .locations[0]
            .span,
        Some((7, 9)),
        "同じ判断から変更後の由来へ戻る"
    );
}

#[test]
fn in_quantifier_fixed_expression_stops_keep_prefixes() {
    let input = fixture(
        r#"
view seed(s: Sample): Z = s.zero;
view absent(s: Sample): Bool = s.flag;
law required rejected(): forall b in list<Bool>[true,false] . b;
view current(): Bool = forall n in list<Z>[1,2] . n>0;
view later(s: Sample): Z = s.zero+9;
"#,
        false,
        false,
    );
    let checked = check_inputs(input.clone(), &mut quiet()).unwrap();
    let asks = [
        "seed=evaluate(Calc.seed,s=@v/sample)",
        "absent=evaluate(Calc.absent,s=@v/sample)",
        "rejected=check(Calc.rejected)",
        "current=evaluate(Calc.current)",
        "later=evaluate(Calc.later,s=@v/sample)",
    ];
    let count = Rc::new(Cell::new(0));
    let c = count.clone();
    let mut prior_control = Control::new(Limits::default(), move |point| {
        if point == Checkpoint::Expression {
            c.set(c.get() + 1);
        }
        Usage::default()
    });
    let prior = evaluate_observed_bytes(input.clone(), &asks[..3], &mut prior_control)
        .unwrap()
        .wire();
    audit(&prior, &checked);
    output(&prior, "seed", &Json::str("Z"), Json::str("0"));
    assert_missing(&prior, "absent", "flag", b"s.flag", &checked);
    check_claim(&prior, "rejected", "refuted");
    let total = Rc::new(Cell::new(0));
    let c = total.clone();
    let mut baseline_control = Control::new(Limits::default(), move |point| {
        if point == Checkpoint::Expression {
            c.set(c.get() + 1);
        }
        Usage::default()
    });
    let baseline = evaluate_observed_bytes(input.clone(), &asks[..4], &mut baseline_control)
        .unwrap()
        .wire();
    audit(&baseline, &checked);
    output(&baseline, "current", &Json::str("Bool"), Json::Bool(true));
    assert_eq!(
        total.get() - count.get(),
        20,
        "固定量化ASTのExpression pre/post"
    );
    let original = declared_body(&checked, "Calc.current");
    let (collection, body) = quant_parts(&checked, original);
    let collection_span = checked.law().exprs[collection].span;
    let body_span = checked.law().exprs[body].span;
    let ns = index(&baseline);
    let full = children(&ns, root(&baseline, "current"));
    assert_eq!(
        full.iter()
            .map(|e| evaluation_span(&ns, e))
            .collect::<Vec<_>>(),
        vec![collection_span, body_span, body_span]
    );
    assert_eq!(source(&checked, collection_span), b"list<Z>[1,2]");
    assert_eq!(source(&checked, body_span), b"n>0");
    assert!(!evidence(&ns, answer(&baseline, "current"), "finite_exhaustion").is_empty());
    // domain post後/第2body pre/最終body postの固定点。実証拠構成loop内部はprivate試験が担う。
    for (offset, kind, done) in [(8, 0, 0), (14, 1, 1), (19, 2, 2)] {
        let at = count.get() + offset;
        let expressions = Rc::new(Cell::new(0));
        let probes = Rc::new(Cell::new(0));
        let frozen = Rc::new(Cell::new(None));
        let (e, p, s) = (expressions.clone(), probes.clone(), frozen.clone());
        let mut control = Control::new(
            Limits {
                time_ms: (kind == 1).then_some(1),
                memory_mib: (kind == 2).then_some(1),
            },
            move |point| {
                p.set(p.get() + 1);
                if point == Checkpoint::Expression {
                    e.set(e.get() + 1);
                    if e.get() == at {
                        s.set(Some(p.get()));
                        return Usage {
                            signal: (kind == 0).then_some(Signal::Term),
                            elapsed_ms: u128::from(kind == 1),
                            memory_mib: u128::from(kind == 2),
                        };
                    }
                }
                Usage::default()
            },
        );
        let wire = evaluate_observed_bytes(input.clone(), &asks, &mut control)
            .unwrap()
            .wire();
        assert_eq!(f(&wire, "status"), &Json::str("interrupted"));
        audit(&wire, &checked);
        output(&wire, "seed", &Json::str("Z"), Json::str("0"));
        check_claim(&wire, "rejected", "refuted");
        for id in ["absent", "rejected"] {
            for key in ["status", "outputs", "scope", "reasons", "evidence"] {
                assert_eq!(f(answer(&wire, id), key), f(answer(&prior, id), key));
            }
        }
        let ns = index(&wire);
        let original_examples =
            evidence(&index(&prior), answer(&prior, "rejected"), "counterexample");
        let kept_examples = evidence(&ns, answer(&wire, "rejected"), "counterexample");
        assert_eq!(
            kept_examples, original_examples,
            "既生成反例を保持し停止後に再導出しない"
        );
        for id in ["current", "later"] {
            let a = answer(&wire, id);
            assert_eq!(f(a, "status"), &Json::str("undetermined"));
            assert!(obj(f(a, "outputs")).is_empty());
            let code = if kind == 0 {
                "cancelled"
            } else {
                "budget_exhausted"
            };
            let reason = arr(f(a, "reasons"))
                .iter()
                .find(|r| f(r, "code") == &Json::str(code))
                .unwrap();
            let details = if kind == 0 {
                Json::obj([("signal", Json::str("SIGTERM"))])
            } else {
                Json::obj([
                    (
                        "resource",
                        Json::str(if kind == 1 { "time_ms" } else { "memory_mib" }),
                    ),
                    ("limit", Json::str("1")),
                    ("observed", Json::str("1")),
                ])
            };
            assert_eq!(f(reason, "details"), &details);
        }
        assert!(
            evaluations_at(&wire, checked.law().exprs[original].span).is_empty(),
            "親量化未完成"
        );
        let collections = evaluations_at(&wire, collection_span);
        assert_eq!(collections.len(), 1);
        assert_eq!(
            val(target(
                &ns,
                f(val(collections[0]), "value"),
                &ty("List", Json::str("Z"))
            )),
            &numbers(&["1", "2"])
        );
        let bodies = evaluations_at(&wire, body_span);
        assert_eq!(bodies.len(), done);
        for body in bodies {
            assert_eq!(
                val(target(&ns, f(val(body), "value"), &Json::str("Bool"))),
                &Json::Bool(true)
            );
        }
        let collection_ref = Json::obj([("node", f(collections[0], "id").clone())]);
        let domains = arr(f(&wire, "nodes"))
            .iter()
            .filter(|n| {
                f(n, "type") == &Json::str("Domain")
                    && arr(f(n, "arguments")).contains(&collection_ref)
            })
            .collect::<Vec<_>>();
        for domain in domains {
            let domain_ref = Json::obj([("node", f(domain, "id").clone())]);
            assert!(
                !arr(f(&wire, "nodes"))
                    .iter()
                    .any(|n| f(n, "type") == &Json::str("Evidence")
                        && f(val(n), "kind") == &Json::str("finite_exhaustion")
                        && f(f(val(n), "data"), "domain") == &domain_ref),
                "最終body post停止でも未完成全検査証拠を生成しない"
            );
        }
        assert!(
            evaluations_at(
                &wire,
                checked.law().exprs[declared_body(&checked, "Calc.later")].span
            )
            .is_empty()
        );
        assert_eq!(expressions.get(), at);
        assert_eq!(Some(probes.get()), frozen.get());
        let before = probes.get();
        assert!(control.checkpoint(Checkpoint::Expression).is_err());
        assert_eq!(probes.get(), before, "停止後probe非再開");
    }
}

#[test]
fn in_quantifiers_keep_known_decisions_with_missing_instances() {
    let script = r#"
view all_refs(s: Sample): Bool = forall r in s.refs . r.flag;
view any_refs(s: Sample): Bool = exists r in s.refs . r.flag;
view missing_only(s: Sample): Bool = forall r in list<Sample>[s] . r.flag;
view missing_exists(s: Sample): Bool = exists r in list<Sample>[s] . r.flag;
view unknown_domain(s: Sample): Bool = forall n in s.missinglist . n>0;
view known_empty(): Bool = forall n in list<Z>[] . n>0;
law required all_law(s: Sample): forall r in s.refs . r.flag;
"#;
    let asks = [
        "a=evaluate(Calc.all_refs,s=@v/sample)",
        "b=check(Calc.all_law,s=@v/sample)",
        "c=evaluate(Calc.missing_only,s=@v/sample)",
        "d=evaluate(Calc.unknown_domain,s=@v/sample)",
        "e=evaluate(Calc.known_empty)",
    ];
    for reverse in [false, true] {
        let (wire, checked) = run(fixture(script, false, reverse), &asks);
        assert_eq!(f(&wire, "status"), &Json::str("partial"));
        output(&wire, "a", &Json::str("Bool"), Json::Bool(false));
        check_claim(&wire, "b", "refuted");
        output(&wire, "e", &Json::str("Bool"), Json::Bool(true));
        let ns = index(&wire);
        let domain = quantifier_domain(
            &wire,
            "a",
            "r",
            "forall",
            &ty("Ref", Json::str("Quantification.Sample")),
        );
        let mut expected = vec![
            reference("sample").canonical(),
            reference("peer").canonical(),
        ];
        expected.sort();
        assert_eq!(
            domain_values(&wire, domain),
            expected,
            "欠測subjectも域に残す"
        );
        if !reverse {
            for id in ["a", "b"] {
                assert_missing(&wire, id, "flag", b"r.flag", &checked);
            }
        }
        for id in ["a", "b"] {
            let examples = evidence(&ns, answer(&wire, id), "counterexample");
            assert!(!examples.is_empty());
            let matching = examples
                .iter()
                .find(|example| {
                    arr(f(f(val(example), "data"), "bindings"))
                        .iter()
                        .any(|b| f(b, "name") == &Json::str("r"))
                })
                .expect("実量化binderを持つ反例");
            let data = f(val(matching), "data");
            let binder = arr(f(data, "bindings"))
                .iter()
                .find(|b| f(b, "name") == &Json::str("r"))
                .unwrap();
            assert_eq!(
                val(target(
                    &ns,
                    f(binder, "value"),
                    &ty("Ref", Json::str("Quantification.Sample"))
                )),
                &reference("peer")
            );
            assert_eq!(
                val(target(&ns, f(data, "left"), &Json::str("Bool"))),
                &Json::Bool(false)
            );
            assert_eq!(
                val(target(&ns, f(data, "right"), &Json::str("Bool"))),
                &Json::Bool(true)
            );
            assert!(arr(f(data, "paths")).is_empty());
            assert!(
                arr(f(data, "facts"))
                    .iter()
                    .any(|fact| obj(fact).get("field")
                        == Some(&Json::str("Quantification.Sample.flag"))
                        && f(fact, "subject") == &Json::str("peer")
                        && f(fact, "atom") == &Json::str("peerflag"))
            );
            let body = arr(f(matching, "arguments"))
                .iter()
                .map(|r| ns[text(f(r, "node"))])
                .find(|n| f(n, "type") == &Json::str("Evaluation"))
                .unwrap();
            assert_eq!(source(&checked, evaluation_span(&ns, body)), b"r.flag");
            assert_eq!(f(val(body), "value"), f(data, "left"));
            assert_eq!(f(body, "support"), f(matching, "support"));
        }
        for (id, field, expression_text) in [
            ("c", "flag", b"r.flag".as_slice()),
            ("d", "missinglist", b"s.missinglist".as_slice()),
        ] {
            let a = answer(&wire, id);
            assert_eq!(f(a, "status"), &Json::str("undetermined"));
            assert!(!obj(f(a, "outputs")).contains_key("value"));
            assert_missing(&wire, id, field, expression_text, &checked);
            assert!(
                evidence(&ns, a, "finite_exhaustion").is_empty(),
                "未知を全検査済みにしない"
            );
        }
        let (domain, body) = quant_parts(&checked, declared_body(&checked, "Calc.unknown_domain"));
        assert_eq!(children(&ns, root(&wire, "d")).len(), 1);
        assert!(evaluations_at(&wire, checked.law().exprs[body].span).is_empty());
        assert!(
            !obj(val(
                evaluations_at(&wire, checked.law().exprs[domain].span)[0]
            ))
            .contains_key("value")
        );
    }
    let (wire, checked) = run(
        fixture(script, true, false),
        &["a=evaluate(Calc.any_refs,s=@v/sample)"],
    );
    output(&wire, "a", &Json::str("Bool"), Json::Bool(true));
    assert_missing(&wire, "a", "flag", b"r.flag", &checked);
    let ns = index(&wire);
    assert_eq!(
        domain_values(
            &wire,
            quantifier_domain(
                &wire,
                "a",
                "r",
                "exists",
                &ty("Ref", Json::str("Quantification.Sample"))
            )
        )
        .len(),
        2
    );
    assert!(
        evidence(&ns, answer(&wire, "a"), "finite_exhaustion").is_empty(),
        "存在証人を全域全検査へ置き換えない"
    );
    let (wire, checked) = run(
        fixture(script, true, false),
        &["a=evaluate(Calc.missing_exists,s=@v/sample)"],
    );
    assert_eq!(f(answer(&wire, "a"), "status"), &Json::str("undetermined"));
    assert_missing(&wire, "a", "flag", b"r.flag", &checked);
}

#[test]
fn in_quantifiers_nested_calls_and_static_rejection() {
    let script = r#"
view compare(x: Z,y: Z): Bool = let shifted=x+1 in match Tag.High { Low => false; High => shifted=y; };
view nested(): Bool = forall x in list<Z>[1,2] . exists y in set { z+1 | z in list<Z>[1,2] } . compare(x,y);
view restore(x: Sample): (Bool,Sample) = (forall y in list<Z>[1,2] . y>0,x);
view by_call(s: Sample): Bool = nested() and (s.zero=0);
"#;
    let asks = [
        "a=evaluate(Calc.nested)",
        "b=evaluate(Calc.restore,x=@v/sample)",
        "c=evaluate(Calc.restore,x=@v/peer)",
        "d=evaluate(Calc.by_call,s=@v/sample)",
    ];
    let (wire, checked) = run(fixture(script, false, false), &asks);
    output(&wire, "a", &Json::str("Bool"), Json::Bool(true));
    output(&wire, "d", &Json::str("Bool"), Json::Bool(true));
    let ns = index(&wire);
    let tuple_type = Json::Arr(vec![
        Json::str("Tuple"),
        Json::str("Bool"),
        ty("Ref", Json::str("Quantification.Sample")),
    ]);
    for (id, subject) in [("b", "sample"), ("c", "peer")] {
        output(
            &wire,
            id,
            &tuple_type,
            Json::Arr(vec![Json::Bool(true), reference(subject)]),
        );
        let bindings = arr(f(val(root(&wire, id)), "bindings"));
        assert_eq!(bindings.len(), 1);
        assert_eq!(f(&bindings[0], "name"), &Json::str("x"));
        assert_eq!(
            val(target(
                &ns,
                f(&bindings[0], "value"),
                &ty("Ref", Json::str("Quantification.Sample"))
            )),
            &reference(subject)
        );
    }
    let qs = arr(f(f(answer(&wire, "a"), "scope"), "quantifiers"));
    assert!(qs.len() >= 2);
    assert_eq!(
        (text(f(&qs[0], "kind")), text(f(&qs[0], "name"))),
        ("forall", "x"),
        "元量化順序を保持"
    );
    let (_, inner) = quant_parts(&checked, declared_body(&checked, "Calc.nested"));
    let (inner_domain, _) = quant_parts(&checked, inner);
    for q in &qs[1..] {
        assert_eq!((text(f(q, "kind")), text(f(q, "name"))), ("exists", "y"));
        let domain = target(&ns, f(q, "domain"), &Json::str("Domain"));
        assert_eq!(
            domain_values(&wire, domain),
            vec![Json::str("2").canonical(), Json::str("3").canonical()]
        );
        let collection = arr(f(domain, "arguments"))
            .iter()
            .map(|r| ns[text(f(r, "node"))])
            .find(|n| f(n, "type") == &Json::str("Evaluation"))
            .unwrap();
        assert_eq!(
            evaluation_span(&ns, collection),
            checked.law().exprs[inner_domain].span,
            "各実inner域を元内包へ戻す"
        );
    }
    let (outer_domain, outer_body) = quant_parts(&checked, declared_body(&checked, "Calc.nested"));
    let outer = children(&ns, root(&wire, "a"));
    assert_eq!(
        evaluation_span(&ns, outer[0]),
        checked.law().exprs[outer_domain].span
    );
    assert_eq!(outer.len(), 3);
    for e in &outer[1..] {
        assert_eq!(
            evaluation_span(&ns, e),
            checked.law().exprs[outer_body].span
        );
        assert!(
            reached(&ns, &[e]).contains(text(f(outer[0], "id"))),
            "外側binderのproducerを保持"
        );
    }
    for bad in [
        "view bad(): Bool = forall n in list<Z>[] . 7;",
        "view bad(): Bool = exists n in list<Z>[] . n.unknownfield=true;",
        "view bad(): Bool = forall n in list<Z>[] . forall n in list<Z>[] . true;",
        "view bad(): Bool = if true then true else exists n in false . true;",
    ] {
        let input = fixture(
            &format!("view selected(): Bool = true; {bad}"),
            false,
            false,
        );
        let law = input.law().bytes().to_vec();
        let error = evaluate_observed_bytes(input, &["a=evaluate(Calc.selected)"], &mut quiet())
            .unwrap_err();
        let invalid = error.wire().unwrap();
        assert_eq!(f(&invalid, "status"), &Json::str("invalid"), "{bad}");
        let issue = &arr(f(&invalid, "issues"))[0];
        let at = span(f(issue, "location"));
        assert!(at.0 < at.1 && at.1 <= law.len());
        assert!(
            bad.contains(std::str::from_utf8(&law[at.0..at.1]).unwrap()),
            "{bad}: {issue:?}"
        );
        for key in ["requests", "nodes", "answers"] {
            assert!(arr(f(&invalid, key)).is_empty());
        }
    }
}

#[test]
fn quantifier_scopes_follow_ast_order_through_domains_and_view_calls() {
    let script = r#"
view earlier_domain(s: Sample): List<Z> = if (exists earlier in list<Z>[s.zero] . earlier=0) then list<Z>[1] else list<Z>[];
view call_earlier(s: Sample): Bool = forall outerearly in earlier_domain(s) . outerearly>0;
view call_later(s: Sample): Bool = forall outerlate in later_domain(s) . outerlate>0;
view later_domain(s: Sample): List<Z> = if (exists later in list<Z>[s.zero] . later=0) then list<Z>[1] else list<Z>[];
view literal_domain(): Bool = forall x in list<Bool>[(exists y in list<Z>[1] . y=1)] . x;
view conditional_domain(): Bool = forall n in (if (forall b in list<Bool>[true] . b) then list<Z>[1] else list<Z>[]) . n>0;
law required ordered(s: Sample): forall outerlaw in later_domain(s) . outerlaw>0;
"#;
    let asks = [
        "a=evaluate(Calc.literal_domain)",
        "b=evaluate(Calc.conditional_domain)",
        "c=evaluate(Calc.call_earlier,s=@v/sample)",
        "d=evaluate(Calc.call_later,s=@v/sample)",
        "e=check(Calc.ordered,s=@v/sample)",
    ];
    let (wire, checked) = run(fixture(script, false, false), &asks);
    assert_eq!(f(&wire, "status"), &Json::str("complete"));
    let ns = index(&wire);
    for id in ["a", "b", "c", "d"] {
        output(&wire, id, &Json::str("Bool"), Json::Bool(true));
    }
    check_claim(&wire, "e", "established");
    // 順序は量化を根とする元ASTの順。callee宣言のbyte位置やdomainの評価順には依存しない。
    for (id, names, kinds, types, values, collection_sources) in [
        (
            "a",
            ["x", "y"],
            ["forall", "exists"],
            ["Bool", "Z"],
            [Json::Bool(true), Json::str("1")],
            ["list<Bool>[(exists y in list<Z>[1] . y=1)]", "list<Z>[1]"],
        ),
        (
            "b",
            ["n", "b"],
            ["forall", "forall"],
            ["Z", "Bool"],
            [Json::str("1"), Json::Bool(true)],
            [
                "(if (forall b in list<Bool>[true] . b) then list<Z>[1] else list<Z>[])",
                "list<Bool>[true]",
            ],
        ),
        (
            "c",
            ["outerearly", "earlier"],
            ["forall", "exists"],
            ["Z", "Z"],
            [Json::str("1"), Json::str("0")],
            ["earlier_domain(s)", "list<Z>[s.zero]"],
        ),
        (
            "d",
            ["outerlate", "later"],
            ["forall", "exists"],
            ["Z", "Z"],
            [Json::str("1"), Json::str("0")],
            ["later_domain(s)", "list<Z>[s.zero]"],
        ),
        (
            "e",
            ["outerlaw", "later"],
            ["forall", "exists"],
            ["Z", "Z"],
            [Json::str("1"), Json::str("0")],
            ["later_domain(s)", "list<Z>[s.zero]"],
        ),
    ] {
        let a = answer(&wire, id);
        let qs = f(f(a, "scope"), "quantifiers");
        assert_eq!(arr(qs).len(), 2, "{id}");
        for (position, q) in arr(qs).iter().enumerate() {
            assert_eq!(f(q, "name"), &Json::str(names[position]), "{id}");
            assert_eq!(f(q, "kind"), &Json::str(kinds[position]), "{id}");
            assert_eq!(f(q, "type"), &Json::str(types[position]), "{id}");
            let domain = target(&ns, f(q, "domain"), &Json::str("Domain"));
            assert_eq!(f(val(domain), "kind"), &Json::str("finite"));
            assert_eq!(f(val(domain), "type"), f(q, "type"));
            assert_eq!(
                domain_values(&wire, domain),
                vec![values[position].canonical()]
            );
            let collection = arr(f(domain, "arguments"))
                .iter()
                .map(|r| ns[text(f(r, "node"))])
                .find(|n| f(n, "type") == &Json::str("Evaluation"))
                .unwrap();
            assert_eq!(
                source(&checked, evaluation_span(&ns, collection)),
                collection_sources[position].as_bytes(),
                "{id}の元domain AST位置"
            );
            assert_eq!(
                val(target(
                    &ns,
                    f(val(collection), "value"),
                    &ty("List", Json::str(types[position]))
                )),
                &Json::Arr(vec![values[position].clone()])
            );
        }
        let evaluation = root(&wire, id);
        assert_eq!(f(f(evaluation, "scope"), "quantifiers"), qs);
        let value = target(&ns, f(val(evaluation), "value"), &Json::str("Bool"));
        assert_eq!(val(value), &Json::Bool(true));
        assert_eq!(f(f(value, "scope"), "quantifiers"), qs);
        if id == "e" {
            let claim = target(&ns, f(a, "claim"), &Json::str("Proposition"));
            assert_eq!(f(f(claim, "scope"), "quantifiers"), qs);
        }
        // 中間Domainは自身へのRefを持てない。保持している量化の部分列を元順と照合する。
        for node in reached(&ns, &[a]).iter().map(|id| ns[id.as_str()]) {
            let ordered = arr(f(f(node, "scope"), "quantifiers"))
                .iter()
                .filter_map(|q| {
                    names
                        .iter()
                        .position(|name| f(q, "name") == &Json::str(*name))
                })
                .collect::<Vec<_>>();
            assert!(
                ordered.windows(2).all(|p| p[0] <= p[1]),
                "{id}: {:?}",
                f(node, "id")
            );
            for q in arr(f(f(node, "scope"), "quantifiers")) {
                if let Some(domain) = obj(q).get("domain") {
                    let domain = target(&ns, domain, &Json::str("Domain"));
                    assert_eq!(f(val(domain), "type"), f(q, "type"));
                }
            }
        }
        if ["c", "d", "e"].contains(&id) {
            assert!(
                arr(f(evaluation, "support")).iter().any(|fact| {
                    obj(fact).get("field") == Some(&Json::str("Quantification.Sample.zero"))
                        && f(fact, "subject") == &Json::str("sample")
                }),
                "domainの呼出しから原始支持を保持"
            );
        }
    }
    let earlier = declared_body(&checked, "Calc.earlier_domain");
    let call_earlier = declared_body(&checked, "Calc.call_earlier");
    let later = declared_body(&checked, "Calc.later_domain");
    let call_later = declared_body(&checked, "Calc.call_later");
    assert!(checked.law().exprs[earlier].span.0 < checked.law().exprs[call_earlier].span.0);
    assert!(checked.law().exprs[later].span.0 > checked.law().exprs[call_later].span.0);
}
