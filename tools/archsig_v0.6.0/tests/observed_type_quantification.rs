//! 有限値型の全域量化を独立三入力から評価し、元型・全coverage・支持と停止prefixを確認する。
mod common;
use archsig::{
    canonical::Json,
    definition::check_definitions_controlled,
    law::{
        ast::{ExprKind, QuantDomain, QuantSplit},
        model::Signature,
    },
    observed::{
        EvaluationFailure,
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
                "urn:fixture:finite-types"
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
                ("field", Json::str(format!("FiniteTypes.Sample.{field}")))
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
fn check_claim(wire: &Json, id: &str, status: &str) {
    let a = answer(wire, id);
    assert_eq!(f(a, "status"), &Json::str(status));
    let ns = index(wire);
    let claim = target(&ns, f(a, "claim"), &Json::str("Proposition"));
    assert_eq!(f(f(claim, "judgment"), "status"), &Json::str(status));
    assert!(!arr(f(claim, "evidence")).is_empty());
}

fn fixture(script: &str) -> InputSources {
    use common::{
        constructor_json, data_json, definition_json, entity_json, field_json, vocabulary_json,
    };
    let fields = format!(
        "[{},{}]",
        field_json("zero", r#""Z""#),
        field_json("flag", r#""Bool""#)
    );
    let entity = entity_json("FiniteTypes.Sample", "[]", &fields);
    let constructors = format!(
        "[{},{}]",
        constructor_json("Empty", "[]"),
        constructor_json("Flag", r#"["Bool"]"#)
    );
    let flagged = data_json("FiniteTypes.Flagged", &constructors);
    let twin = data_json("FiniteTypes.Twin", &constructors);
    let infinite = data_json(
        "FiniteTypes.Infinite",
        &format!("[{}]", constructor_json("Amount", r#"["Z"]"#)),
    );
    let tree = data_json(
        "FiniteTypes.Tree",
        &format!(
            "[{},{}]",
            constructor_json("End", "[]"),
            constructor_json("Next", r#"[["Data","FiniteTypes.Tree"]]"#)
        ),
    );
    let definitions = definition_json(&format!(
        "[{}]",
        vocabulary_json(
            "FiniteTypes",
            &format!("[{entity},{flagged},{twin},{infinite},{tree}]"),
            "[]"
        )
    ));
    let checked =
        check_definitions_controlled(&[("definition0", definitions.as_bytes())], &mut quiet())
            .unwrap();
    let digest = &checked.vocabularies["FiniteTypes"].digest;
    let law = format!(
        r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading FiniteTypes {{ use vocabulary FiniteTypes version "1" digest "{digest}"; }}
reading Calc {{ use vocabulary FiniteTypes version "1" digest "{digest}"; use FiniteTypes as F; {script} }}"#
    );
    let map = format!(
        r#"{{"format":"archsig.archmap/2","semantics":"archsig/0.6.0",
"vocabularies":[{{"namespace":"FiniteTypes","version":"1","digest":"{digest}"}}],
"sources":[{{"id":"scan","uri":"urn:fixture:finite-types","revision":"r1","digest":"sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"}}],
"origins":[{{"id":"base","mode":"specification","method":"対象を提示する。","locations":[{{"source":"scan","path":"subjects.model","span":[0,1]}}]}},
{{"id":"values","mode":"specification","method":"fieldの観測。","locations":[{{"source":"scan","path":"values.model","span":[2,5]}}]}}],
"snapshots":[{{"id":"v","origin":"base","subjects":[{{"id":"sample","type":"FiniteTypes.Sample","origin":"base"}},{{"id":"peer","type":"FiniteTypes.Sample","origin":"base"}}],"atoms":[{{"id":"zero","subject":"sample","field":"FiniteTypes.Sample.zero","value":"0","origin":"values"}},{{"id":"peerzero","subject":"peer","field":"FiniteTypes.Sample.zero","value":"4","origin":"values"}}]}}]}}"#
    );
    InputSources::from_bytes(
        vec![definitions.into_bytes()],
        law.into_bytes(),
        map.into_bytes(),
    )
}
fn data(tag: &str, args: Vec<Json>) -> Json {
    Json::obj([("tag", Json::str(tag)), ("args", Json::Arr(args))])
}
fn type_body(checked: &CheckedInputs, name: &str) -> usize {
    let id = declared_body(checked, name);
    let ExprKind::Quant {
        split:
            QuantSplit::Fixed {
                domain: QuantDomain::Type(_),
                body,
            },
        ..
    } = &checked.law().exprs[id].kind
    else {
        panic!("型量化")
    };
    *body
}

#[test]
fn finite_type_quantifiers_enumerate_exact_domains_and_coverage() {
    let script = r#"
view one(): Bool = forall u:Unit . true;
view boolean(): Bool = forall b:Bool . b or not b;
view residue(): Bool = forall p:Fp(3) . p=p;
view flagged(): Bool = forall d:Flagged . d=d;
view product(): Bool = forall p:(Bool,Fp(2)) . p=p;
view option_values(): Bool = forall o:Option<Bool> . o=o;
view powerset(): Bool = forall a:Set<Bool> . a=a;
view alias_unused(): Bool = forall d:F.Flagged . true;
view twin_unused(): Bool = forall d:Twin . true;
view no_witness(): Bool = exists b:Bool . false;
view false_value(): Bool = forall b:Bool . b;
view witness(): Bool = exists b:Bool . b;
law required false_law(): forall b:Bool . b;
"#;
    let names = [
        "one",
        "boolean",
        "residue",
        "flagged",
        "product",
        "option_values",
        "powerset",
        "alias_unused",
        "twin_unused",
        "no_witness",
        "false_value",
        "witness",
    ];
    let mut asks = names
        .iter()
        .map(|name| format!("{name}=evaluate(Calc.{name})"))
        .collect::<Vec<_>>();
    asks.push("checked=check(Calc.false_law)".into());
    let (wire, checked) = run(
        fixture(script),
        &asks.iter().map(String::as_str).collect::<Vec<_>>(),
    );
    assert_eq!(f(&wire, "status"), &Json::str("complete"));
    for name in names {
        output(
            &wire,
            name,
            &Json::str("Bool"),
            Json::Bool(!["no_witness", "false_value"].contains(&name)),
        );
    }
    check_claim(&wire, "checked", "refuted");
    let flagged = vec![
        data("Empty", vec![]),
        data("Flag", vec![Json::Bool(false)]),
        data("Flag", vec![Json::Bool(true)]),
    ];
    let booleans = vec![Json::Bool(false), Json::Bool(true)];
    let products = vec![
        Json::Arr(vec![Json::Bool(false), Json::str("0")]),
        Json::Arr(vec![Json::Bool(false), Json::str("1")]),
        Json::Arr(vec![Json::Bool(true), Json::str("0")]),
        Json::Arr(vec![Json::Bool(true), Json::str("1")]),
    ];
    let options = vec![
        Json::obj([("none", Json::Bool(true))]),
        Json::obj([("some", Json::Bool(false))]),
        Json::obj([("some", Json::Bool(true))]),
    ];
    let sets = vec![
        Json::Arr(vec![]),
        Json::Arr(vec![Json::Bool(false)]),
        Json::Arr(vec![Json::Bool(true)]),
        Json::Arr(booleans.clone()),
    ];
    let ns = index(&wire);
    for (name, binder, t, wanted, truth) in [
        ("one", "u", Json::str("Unit"), vec![Json::Arr(vec![])], true),
        ("boolean", "b", Json::str("Bool"), booleans.clone(), true),
        (
            "residue",
            "p",
            ty("Fp", Json::str("3")),
            arr(&numbers(&["0", "1", "2"])).to_vec(),
            true,
        ),
        (
            "flagged",
            "d",
            ty("Data", Json::str("FiniteTypes.Flagged")),
            flagged.clone(),
            true,
        ),
        (
            "product",
            "p",
            Json::Arr(vec![
                Json::str("Tuple"),
                Json::str("Bool"),
                ty("Fp", Json::str("2")),
            ]),
            products,
            true,
        ),
        (
            "option_values",
            "o",
            ty("Option", Json::str("Bool")),
            options,
            true,
        ),
        ("powerset", "a", ty("Set", Json::str("Bool")), sets, true),
        (
            "alias_unused",
            "d",
            ty("Data", Json::str("FiniteTypes.Flagged")),
            flagged.clone(),
            true,
        ),
        (
            "twin_unused",
            "d",
            ty("Data", Json::str("FiniteTypes.Twin")),
            flagged,
            true,
        ),
        ("no_witness", "b", Json::str("Bool"), booleans, false),
    ] {
        let kind = if name == "no_witness" {
            "exists"
        } else {
            "forall"
        };
        let domain = quantifier_domain(&wire, name, binder, kind, &t);
        let normalize = |value: &Json| {
            if let Json::Arr(tp) = &t
                && tp.first() == Some(&Json::str("Set"))
            {
                let mut elements = arr(value).iter().map(Json::canonical).collect::<Vec<_>>();
                elements.sort();
                format!("{elements:?}")
            } else {
                value.canonical()
            }
        };
        let mut actual = arr(f(val(domain), "elements"))
            .iter()
            .map(|r| normalize(val(target(&ns, r, &t))))
            .collect::<Vec<_>>();
        actual.sort();
        let mut expected = wanted.iter().map(normalize).collect::<Vec<_>>();
        expected.sort();
        assert_eq!(actual, expected, "{name}:元型の意味上の全域");
        let original = declared_body(&checked, &format!("Calc.{name}"));
        let source_node = arr(f(domain, "arguments"))
            .iter()
            .map(|r| ns[text(f(r, "node"))])
            .find(|n| f(n, "type") == &Json::str("Expression"))
            .unwrap();
        assert_eq!(
            span(f(val(source_node), "location")),
            checked.law().exprs[original].span
        );
        for member in arr(f(val(domain), "elements")) {
            let member = target(&ns, member, &t);
            assert_eq!(
                arr(f(member, "arguments")),
                &[Json::obj([("node", f(source_node, "id").clone())])],
                "元解決済型を持つ量化Sourceから列挙する"
            );
        }
        assert!(
            arr(f(domain, "arguments"))
                .iter()
                .all(|r| f(ns[text(f(r, "node"))], "type") != &Json::str("Evaluation")),
            "型域に架空のcollection Evaluationを作らない"
        );
        let body_span = checked.law().exprs[type_body(&checked, &format!("Calc.{name}"))].span;
        let body_evals = children(&ns, root(&wire, name));
        assert_eq!(body_evals.len(), wanted.len(), "{name}:全body coverage");
        let mut covered = vec![];
        for body in body_evals {
            assert_eq!(evaluation_span(&ns, body), body_span);
            assert_eq!(
                val(target(&ns, f(val(body), "value"), &Json::str("Bool"))),
                &Json::Bool(truth)
            );
            assert!(
                arr(f(val(body), "bindings"))
                    .iter()
                    .all(|b| f(b, "name") != &Json::str(binder)),
                "型binderを自由parameterへ変えない"
            );
            assert!(
                reached(&ns, &[body]).contains(text(f(domain, "id"))),
                "未使用binder bodyも元型域へ戻る"
            );
            let member_refs = arr(f(expression(&ns, body), "arguments"))
                .iter()
                .filter(|r| arr(f(val(domain), "elements")).contains(r))
                .collect::<Vec<_>>();
            assert_eq!(member_refs.len(), 1, "{name}:実bodyの選択member");
            covered.push(normalize(val(target(&ns, member_refs[0], &t))));
            for name_eval in reached(&ns, &[body])
                .iter()
                .map(|id| ns[id.as_str()])
                .filter(|n| {
                    f(n, "type") == &Json::str("Evaluation")
                        && aggregate_instance(&ns, n).is_none()
                        && source(&checked, evaluation_span(&ns, n)) == binder.as_bytes()
                })
            {
                assert!(
                    arr(f(part(name_eval), "children")).is_empty(),
                    "型binderへcollection評価を捏造しない"
                );
                let scalar = target(&ns, f(val(name_eval), "value"), &t);
                assert_eq!(
                    arr(f(scalar, "arguments")),
                    &[Json::obj([("node", f(domain, "id").clone())])]
                );
                assert_eq!(
                    normalize(val(scalar)),
                    normalize(val(target(&ns, member_refs[0], &t)))
                );
            }
        }
        covered.sort();
        assert_eq!(
            covered, expected,
            "{name}:未使用binderを含め全memberを尽くす"
        );
        let proofs = evidence(&ns, answer(&wire, name), "finite_exhaustion");
        assert_eq!(proofs.len(), 1);
        let proof = f(val(proofs[0]), "data");
        assert_eq!(
            f(proof, "domain"),
            &Json::obj([("node", f(domain, "id").clone())])
        );
        assert_eq!(f(proof, "checked"), &Json::Nat(wanted.len() as u64));
        assert_eq!(arr(f(proof, "instances")).len(), wanted.len());
        for instance in arr(f(proof, "instances")) {
            assert_eq!(
                evaluation_span(&ns, target(&ns, instance, &Json::str("Evaluation"))),
                body_span
            );
        }
    }
    for id in ["false_value", "checked"] {
        let examples = evidence(&ns, answer(&wire, id), "counterexample");
        let example = examples
            .iter()
            .find(|e| {
                arr(f(f(val(e), "data"), "bindings"))
                    .iter()
                    .any(|b| f(b, "name") == &Json::str("b"))
            })
            .unwrap();
        let data = f(val(example), "data");
        let binder = arr(f(data, "bindings"))
            .iter()
            .find(|b| f(b, "name") == &Json::str("b"))
            .unwrap();
        assert_eq!(
            val(target(&ns, f(binder, "value"), &Json::str("Bool"))),
            &Json::Bool(false)
        );
        assert_eq!(
            val(target(&ns, f(data, "left"), &Json::str("Bool"))),
            &Json::Bool(false)
        );
        assert_eq!(
            val(target(&ns, f(data, "right"), &Json::str("Bool"))),
            &Json::Bool(true)
        );
    }
}

#[test]
fn finite_type_quantifiers_nested_calls_preserve_bindings_and_missing() {
    let script = r#"
view assess(b: Bool,s: Sample): Bool = let kept=b in match Flagged.Flag(kept) { Empty => s.zero>=0; Flag(p) => (p or not p) and s.zero>=0; };
view mixed(s: Sample): Bool = forall x:Bool . exists n in list<Z>[s.zero] . assess(x,s);
view domain_nested(): Bool = forall u in list<Bool>[(exists q:Bool . q)] . u;
view restore(x: Sample): (Bool,Sample) = (forall b:Bool . assess(b,x),x);
view missing(s: Sample): Bool = forall b:Bool . s.flag;
view decisive(s: Sample): Bool = forall b:Bool . if b then false else s.flag;
law required decisive_law(s: Sample): forall b:Bool . if b then false else s.flag;
"#;
    let asks = [
        "a=evaluate(Calc.mixed,s=@v/sample)",
        "b=evaluate(Calc.domain_nested)",
        "c=evaluate(Calc.restore,x=@v/sample)",
        "d=evaluate(Calc.restore,x=@v/peer)",
        "e=evaluate(Calc.missing,s=@v/sample)",
        "f=evaluate(Calc.decisive,s=@v/sample)",
        "g=check(Calc.decisive_law,s=@v/sample)",
    ];
    let (wire, checked) = run(fixture(script), &asks);
    assert_eq!(
        f(&wire, "status"),
        &Json::str("partial"),
        "{:?}",
        f(&wire, "issues")
    );
    for id in ["a", "b"] {
        output(&wire, id, &Json::str("Bool"), Json::Bool(true));
    }
    output(&wire, "f", &Json::str("Bool"), Json::Bool(false));
    check_claim(&wire, "g", "refuted");
    let tuple_type = Json::Arr(vec![
        Json::str("Tuple"),
        Json::str("Bool"),
        ty("Ref", Json::str("FiniteTypes.Sample")),
    ]);
    let ns = index(&wire);
    for (id, subject) in [("c", "sample"), ("d", "peer")] {
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
                &ty("Ref", Json::str("FiniteTypes.Sample"))
            )),
            &reference(subject)
        );
    }
    let mixed_scope = arr(f(f(answer(&wire, "a"), "scope"), "quantifiers"));
    assert!(mixed_scope.len() >= 2);
    assert_eq!(
        (
            text(f(&mixed_scope[0], "kind")),
            text(f(&mixed_scope[0], "name"))
        ),
        ("forall", "x")
    );
    for q in &mixed_scope[1..] {
        assert_eq!((text(f(q, "kind")), text(f(q, "name"))), ("exists", "n"));
    }
    let outer_domain = quantifier_domain(&wire, "a", "x", "forall", &Json::str("Bool"));
    let inner_quant = type_body(&checked, "Calc.mixed");
    let outer_children = children(&ns, root(&wire, "a"));
    assert_eq!(outer_children.len(), 2);
    for inner in outer_children {
        assert_eq!(
            evaluation_span(&ns, inner),
            checked.law().exprs[inner_quant].span
        );
        assert!(
            reached(&ns, &[inner]).contains(text(f(outer_domain, "id"))),
            "In量化から元型binderへ戻る"
        );
        assert_eq!(children(&ns, inner).len(), 2, "In域Evaluationと一body");
    }
    let domain_scope = arr(f(f(answer(&wire, "b"), "scope"), "quantifiers"));
    assert_eq!(
        domain_scope
            .iter()
            .map(|q| (text(f(q, "kind")), text(f(q, "name"))))
            .collect::<Vec<_>>(),
        vec![("forall", "u"), ("exists", "q")],
        "domain内型量化も元AST順"
    );
    assert_eq!(f(answer(&wire, "e"), "status"), &Json::str("undetermined"));
    assert!(!obj(f(answer(&wire, "e"), "outputs")).contains_key("value"));
    let original_root = |id: &str, name: &str| {
        let aggregate = root(&wire, id);
        let seed = expression(&ns, aggregate);
        assert_eq!(
            arr(f(aggregate, "arguments")).first(),
            Some(f(val(aggregate), "expression"))
        );
        let (Signature::View { body, .. } | Signature::Law { body, .. }) =
            &checked.law().declarations[name].signature
        else {
            panic!("元view/Law")
        };
        let at = checked.law().exprs[*body].span;
        let originals = arr(f(seed, "arguments"))
            .iter()
            .map(|r| ns[text(f(r, "node"))])
            .filter(|n| {
                f(n, "type") == &Json::str("Evaluation")
                    && evaluation_span(&ns, n) == at
                    && f(val(expression(&ns, n)), "kind") == &Json::str("source")
                    && f(val(expression(&ns, n)), "bindings") == f(val(seed), "bindings")
                    && f(val(n), "bindings") == f(val(seed), "bindings")
                    && arr(f(val(expression(&ns, n)), "parameters")).is_empty()
                    && arr(f(n, "arguments")).first() == Some(f(val(n), "expression"))
            })
            .collect::<Vec<_>>();
        assert_eq!(
            originals.len(),
            1,
            "元seed直接rootsから元AST/明示bindingsの評価を一意選択"
        );
        originals[0]
    };
    let original_e = original_root("e", "Calc.missing");
    let original_f = original_root("f", "Calc.decisive");
    let original_g = original_root("g", "Calc.decisive_law");
    assert!(!obj(val(original_e)).contains_key("value"));
    assert!(evidence(&ns, original_e, "finite_exhaustion").is_empty());
    for id in ["e", "f", "g"] {
        assert_missing(&wire, id, "flag", b"s.flag", &checked);
    }
    for id in ["f", "g"] {
        let original = if id == "f" { original_f } else { original_g };
        assert_eq!(
            val(target(&ns, f(val(original), "value"), &Json::str("Bool"))),
            &Json::Bool(false)
        );
        let examples = evidence(&ns, original, "counterexample");
        let example = examples
            .iter()
            .find(|e| {
                arr(f(f(val(e), "data"), "bindings"))
                    .iter()
                    .any(|b| f(b, "name") == &Json::str("b"))
            })
            .unwrap();
        let data = f(val(example), "data");
        assert!(
            reached(&ns, &[answer(&wire, id)]).contains(text(f(example, "id"))),
            "元の既知反例を最終集約から保持"
        );
        let binder = arr(f(data, "bindings"))
            .iter()
            .find(|b| f(b, "name") == &Json::str("b"))
            .unwrap();
        assert_eq!(
            val(target(&ns, f(binder, "value"), &Json::str("Bool"))),
            &Json::Bool(true)
        );
        assert_eq!(
            val(target(&ns, f(data, "left"), &Json::str("Bool"))),
            &Json::Bool(false)
        );
        assert_eq!(
            val(target(&ns, f(data, "right"), &Json::str("Bool"))),
            &Json::Bool(true)
        );
    }
    for (id, original) in [("e", original_e), ("f", original_f), ("g", original_g)] {
        let aggregate = root(&wire, id);
        let domain_ref = &arr(f(aggregate, "arguments"))[1];
        let domain = target(&ns, domain_ref, &Json::str("Domain"));
        assert_eq!(f(val(domain), "kind"), &Json::str("finite"));
        assert_eq!(f(val(domain), "type"), &Json::str("Bool"));
        let members = arr(f(val(domain), "elements"));
        assert_eq!(members.len(), 2);
        let case_refs = arr(f(part(aggregate), "children"));
        assert_eq!(case_refs.len(), 2);
        let mut seen = BTreeSet::new();
        for case_ref in case_refs {
            let case = target(&ns, case_ref, &Json::str("Evaluation"));
            assert_eq!(evaluation_span(&ns, case), evaluation_span(&ns, original));
            let case_bindings = arr(f(val(case), "bindings"));
            let original_bindings = arr(f(val(original), "bindings"));
            assert_eq!(case_bindings.len(), original_bindings.len());
            for (actual, original) in case_bindings.iter().zip(original_bindings) {
                assert_eq!(f(actual, "name"), f(original, "name"));
                let t = ty("Ref", Json::str("FiniteTypes.Sample"));
                assert_eq!(
                    val(target(&ns, f(actual, "value"), &t)),
                    val(target(&ns, f(original, "value"), &t))
                );
            }
            let source = expression(&ns, case);
            let selected = arr(f(source, "arguments"))
                .iter()
                .filter(|r| members.contains(r))
                .collect::<Vec<_>>();
            assert_eq!(selected.len(), 1);
            let Json::Bool(flag) = val(target(&ns, selected[0], &Json::str("Bool"))) else {
                panic!("Bool")
            };
            assert!(seen.insert(*flag));
            assert_eq!(
                val(target(&ns, f(val(case), "value"), &Json::str("Bool"))),
                &Json::Bool(id == "e" && *flag)
            );
        }
        assert_eq!(seen, BTreeSet::from([false, true]));
        let proofs = arr(f(aggregate, "evidence"))
            .iter()
            .map(|r| target(&ns, r, &Json::str("Evidence")))
            .collect::<Vec<_>>();
        assert_eq!(proofs.len(), 1);
        let proof = proofs[0];
        let data = f(val(proof), "data");
        if id == "e" {
            assert_eq!(f(val(proof), "kind"), &Json::str("completion_pair"));
            assert_eq!(
                f(data, "fields"),
                &Json::Arr(vec![Json::obj([
                    ("snapshot", Json::str("v")),
                    ("subject", Json::str("sample")),
                    ("field", Json::str("FiniteTypes.Sample.flag"))
                ])])
            );
            let mut flags = BTreeSet::new();
            for (bindings, result) in [("first", "first_result"), ("second", "second_result")] {
                let assignment = arr(f(data, bindings));
                assert_eq!(assignment.len(), 1);
                let Json::Bool(flag) = val(target(&ns, &assignment[0], &Json::str("Bool"))) else {
                    panic!("Bool")
                };
                assert!(flags.insert(*flag));
                assert!(case_refs.contains(f(data, result)));
                let case = target(&ns, f(data, result), &Json::str("Evaluation"));
                assert!(arr(f(expression(&ns, case), "arguments")).contains(&assignment[0]));
                assert_eq!(
                    val(target(&ns, f(val(case), "value"), &Json::str("Bool"))),
                    &Json::Bool(*flag)
                );
            }
            assert_eq!(flags, BTreeSet::from([false, true]));
        } else {
            assert_eq!(f(val(proof), "kind"), &Json::str("finite_exhaustion"));
            assert_eq!(f(data, "domain"), domain_ref);
            assert_eq!(f(data, "checked"), &Json::Nat(2));
            assert_eq!(f(data, "instances"), &Json::Arr(case_refs.to_vec()));
        }
    }
    assert!(
        arr(f(root(&wire, "a"), "support"))
            .iter()
            .any(|p| obj(p).get("field") == Some(&Json::str("FiniteTypes.Sample.zero"))),
        "呼出しから原始支持と由来を保持"
    );
}

#[test]
fn infinite_type_quantifiers_remain_not_implemented() {
    let script = r#"
view integers(s: Sample): Bool = forall unused:Z . s.zero=0;
view rationals(): Bool = forall unused:Q . true;
view texts(): Bool = exists unused:Text . false;
view lists(): Bool = forall unused:List<Bool> . true;
view recursive(): Bool = forall unused:Tree . true;
view infinite_payload(): Bool = forall unused:Infinite . true;
"#;
    let input = fixture(script);
    let checked = check_inputs(input.clone(), &mut quiet()).unwrap();
    for name in [
        "integers",
        "rationals",
        "texts",
        "lists",
        "recursive",
        "infinite_payload",
    ] {
        let ask = format!(
            "a=evaluate(Calc.{name}{})",
            if name == "integers" {
                ",s=@v/sample"
            } else {
                ""
            }
        );
        if let Some(ty) = match name {
            "integers" => Some("Z"),
            "rationals" => Some("Q"),
            _ => None,
        } {
            let wire = evaluate_observed_bytes(input.clone(), &[&ask], &mut quiet())
                .unwrap()
                .wire();
            output(&wire, "a", &Json::str("Bool"), Json::Bool(true));
            assert_eq!(f(&wire, "status"), &Json::str("complete"));
            assert!(arr(f(&wire, "issues")).is_empty());
            let ns = index(&wire);
            let evaluation = root(&wire, "a");
            let original = expression(&ns, evaluation);
            let declaration = format!("Calc.{name}");
            let original_span = checked.law().exprs[declared_body(&checked, &declaration)].span;
            let body_span = checked.law().exprs[type_body(&checked, &declaration)].span;
            assert_eq!(span(f(val(original), "location")), original_span);
            assert_eq!(f(val(original), "kind"), &Json::str("source"));
            assert!(arr(f(val(original), "parameters")).is_empty());
            assert_eq!(
                f(f(evaluation, "scope"), "domain"),
                &Json::str("all_assignments")
            );
            assert_eq!(f(evaluation, "scope"), f(answer(&wire, "a"), "scope"));
            let quantifiers = arr(f(f(evaluation, "scope"), "quantifiers"));
            assert_eq!(quantifiers.len(), 1);
            assert_eq!(f(&quantifiers[0], "kind"), &Json::str("forall"));
            assert_eq!(f(&quantifiers[0], "name"), &Json::str("unused"));
            assert_eq!(f(&quantifiers[0], "type"), &Json::str(ty));
            let domain = target(&ns, f(&quantifiers[0], "domain"), &Json::str("Domain"));
            assert_eq!(f(val(domain), "kind"), &Json::str("type"));
            assert_eq!(f(val(domain), "type"), &Json::str(ty));
            assert!(!obj(val(domain)).contains_key("elements"));
            assert_eq!(
                arr(f(domain, "arguments")),
                &[f(val(evaluation), "expression").clone()]
            );
            let quantifier_id = declared_body(&checked, &declaration);
            let ExprKind::Quant {
                kind: archsig::law::ast::QuantKind::Forall,
                var,
                split:
                    QuantSplit::Fixed {
                        domain: QuantDomain::Type(archsig::law::ast::TypeAst::Builtin(builtin, _)),
                        body: body_id,
                    },
            } = &checked.law().exprs[quantifier_id].kind
            else {
                panic!("元のZ/Q forall AST")
            };
            assert_eq!(var.name, "unused");
            assert_eq!(*body_id, type_body(&checked, &declaration));
            assert_eq!(
                builtin,
                &if ty == "Z" {
                    archsig::law::ast::Builtin::Z
                } else {
                    archsig::law::ast::Builtin::Q
                }
            );
            for id in [quantifier_id, *body_id] {
                assert_eq!(
                    checked.law().expr_type(id).unwrap().wire(),
                    Json::str("Bool")
                );
            }
            let whole_children = children(&ns, evaluation);
            assert_eq!(whole_children.len(), 1);
            let quantifier = whole_children[0];
            let quantifier_source = expression(&ns, quantifier);
            assert_eq!(f(val(quantifier_source), "kind"), &Json::str("source"));
            assert_eq!(evaluation_span(&ns, quantifier), original_span);
            assert_eq!(span(f(part(quantifier), "location")), original_span);
            assert_eq!(f(val(quantifier_source), "parameters"), &Json::Arr(vec![]));
            assert_eq!(
                arr(f(quantifier_source, "arguments")).first(),
                Some(f(val(evaluation), "expression"))
            );
            assert_eq!(
                f(val(quantifier), "bindings"),
                f(val(evaluation), "bindings")
            );
            let quantifier_children = children(&ns, quantifier);
            assert_eq!(quantifier_children.len(), 1);
            let body = quantifier_children[0];
            assert_eq!(evaluation_span(&ns, body), body_span);
            assert_eq!(span(f(part(body), "location")), body_span);
            for (parent, child) in [(evaluation, quantifier), (quantifier, body)] {
                assert_eq!(f(val(parent), "applicability"), &Json::str("applicable"));
                for fact in arr(f(child, "support")) {
                    assert!(arr(f(parent, "support")).contains(fact));
                }
            }
            let body_source = expression(&ns, body);
            assert_eq!(f(val(body_source), "kind"), &Json::str("source"));
            assert_eq!(span(f(f(body_source, "rule"), "location")), body_span);
            assert_eq!(
                f(val(body_source), "parameters"),
                &Json::Arr(vec![Json::obj([
                    ("name", Json::str("unused")),
                    ("type", Json::str(ty)),
                ])])
            );
            assert_eq!(
                val(target(&ns, f(val(body), "value"), &Json::str("Bool"))),
                &Json::Bool(true)
            );
            assert!(
                arr(f(val(evaluation), "bindings"))
                    .iter()
                    .all(|b| f(b, "name") != &Json::str("unused"))
            );
            for node in [original, quantifier_source, body_source] {
                assert_eq!(
                    span(f(f(node, "rule"), "location")),
                    span(f(val(node), "location"))
                );
                assert_eq!(f(f(node, "rule"), "kind"), &Json::str("law"));
            }
            let proofs = arr(f(evaluation, "evidence"));
            assert_eq!(proofs.len(), 1);
            let proof = target(&ns, &proofs[0], &Json::str("Evidence"));
            assert_eq!(f(val(proof), "kind"), &Json::str("normalization"));
            let data = f(val(proof), "data");
            assert_eq!(f(data, "before"), f(val(evaluation), "expression"));
            assert_eq!(f(data, "after"), f(val(evaluation), "value"));
            assert_eq!(f(proof, "support"), f(evaluation, "support"));
            assert_eq!(f(proof, "scope"), f(evaluation, "scope"));
            if name == "rationals" {
                assert!(arr(f(data, "steps")).is_empty());
                assert!(!obj(part(evaluation)).contains_key("residual"));
            }
            let mut earlier = BTreeSet::new();
            for node in arr(f(&wire, "nodes")) {
                let mut references = vec![];
                refs(node, &mut references);
                assert!(references.iter().all(|id| earlier.contains(id)));
                assert!(earlier.insert(text(f(node, "id")).to_owned()));
                if f(node, "type") == &Json::str("Domain") {
                    assert_eq!(f(val(node), "kind"), &Json::str("type"));
                    assert_eq!(f(val(node), "type"), &Json::str(ty));
                }
            }
            let support = arr(f(evaluation, "support"));
            if name == "integers" {
                let fact = support
                    .iter()
                    .find(|fact| {
                        obj(fact).get("field") == Some(&Json::str("FiniteTypes.Sample.zero"))
                    })
                    .unwrap();
                assert_eq!(f(fact, "snapshot"), &Json::str("v"));
                assert_eq!(f(fact, "subject"), &Json::str("sample"));
                assert_eq!(f(fact, "atom"), &Json::str("zero"));
                assert!(arr(f(body, "support")).contains(fact));
            } else {
                assert!(support.is_empty());
            }
            continue;
        }
        let error = evaluate_observed_bytes(input.clone(), &[&ask], &mut quiet()).unwrap_err();
        assert!(
            error.wire().is_none(),
            "{name}:対象外型全域を公開unsupported/未決へ変えない"
        );
        let EvaluationFailure::NotImplemented {
            declaration,
            location: archsig::issue::Location::Law { span },
            feature,
        } = error
        else {
            panic!("{name}:専用NotImplemented")
        };
        assert_eq!(declaration, format!("Calc.{name}"));
        assert_eq!(
            span,
            checked.law().exprs[declared_body(&checked, &declaration)].span
        );
        assert!(!feature.is_empty());
    }
}

#[test]
fn finite_type_quantifier_expression_stops_keep_prefixes() {
    let input = fixture(
        r#"
view seed(s: Sample): Z = s.zero;
view absent(s: Sample): Bool = s.flag;
law required rejected(): forall b:Bool . b;
view current(): Bool = forall b:Bool . true;
view later(s: Sample): Z = s.zero+9;
"#,
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
        6,
        "元型量化と2bodyの通常Expression pre/post"
    );
    let original = declared_body(&checked, "Calc.current");
    let body = type_body(&checked, "Calc.current");
    let body_span = checked.law().exprs[body].span;
    let ns = index(&baseline);
    assert_eq!(children(&ns, root(&baseline, "current")).len(), 2);
    assert!(!evidence(&ns, answer(&baseline, "current"), "finite_exhaustion").is_empty());
    // 固定Expression: +2=型列挙後の第1body pre、+4=第2body pre、+5=最終body post。
    // 実列挙/全検査証拠構成のloop内部停止はprivate試験が担う。
    for (offset, kind, done) in [(2, 0, 0), (4, 1, 1), (5, 2, 2)] {
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
        assert_eq!(
            evidence(&ns, answer(&wire, "rejected"), "counterexample"),
            evidence(&index(&prior), answer(&prior, "rejected"), "counterexample")
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
        assert!(evaluations_at(&wire, checked.law().exprs[original].span).is_empty());
        let bodies = evaluations_at(&wire, body_span);
        assert_eq!(bodies.len(), done);
        for body in bodies {
            assert_eq!(
                val(target(&ns, f(val(body), "value"), &Json::str("Bool"))),
                &Json::Bool(true)
            );
        }
        let source_span = checked.law().exprs[original].span;
        let current_domains = arr(f(&wire, "nodes"))
            .iter()
            .filter(|n| {
                f(n, "type") == &Json::str("Domain")
                    && arr(f(n, "arguments")).iter().any(|r| {
                        let parent = ns[text(f(r, "node"))];
                        f(parent, "type") == &Json::str("Expression")
                            && span(f(val(parent), "location")) == source_span
                    })
            })
            .collect::<Vec<_>>();
        assert_eq!(current_domains.len(), 1, "型列挙後の実Domainを保持");
        let domain_ref = Json::obj([("node", f(current_domains[0], "id").clone())]);
        assert!(
            !arr(f(&wire, "nodes"))
                .iter()
                .any(|n| f(n, "type") == &Json::str("Evidence")
                    && f(val(n), "kind") == &Json::str("finite_exhaustion")
                    && f(f(val(n), "data"), "domain") == &domain_ref),
            "未完成全域証拠を生成しない"
        );
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
        assert_eq!(probes.get(), before);
    }
}
