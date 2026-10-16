//! 全snapshotのplain参照族を独立三入力から評価し、型・支持・由来・有限域と停止prefixを確認する。
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
fn reference(snapshot: &str, subject: &str) -> Json {
    Json::Arr(vec![Json::str(snapshot), Json::str(subject)])
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
fn check_claim(wire: &Json, id: &str, status: &str) {
    let a = answer(wire, id);
    assert_eq!(f(a, "status"), &Json::str(status));
    let ns = index(wire);
    let claim = target(&ns, f(a, "claim"), &Json::str("Proposition"));
    assert_eq!(f(f(claim, "judgment"), "status"), &Json::str(status));
    assert!(!arr(f(claim, "evidence")).is_empty());
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

fn fixture(script: &str, known_flag: Option<bool>, reverse: bool, moved: bool) -> InputSources {
    use common::{
        constructor_json, data_json, definition_json, entity_json, field_json, vocabulary_json,
    };
    let root = entity_json("Roster.Root", "[]", "[]");
    let e = entity_json(
        "Roster.E",
        &format!("[{}]", field_json("owner", r#"["Ref","Roster.Root"]"#)),
        &format!("[{}]", field_json("flag", r#""Bool""#)),
    );
    let other = entity_json("Roster.Other", "[]", "[]");
    let empty = entity_json("Roster.Empty", "[]", "[]");
    let maybe = data_json(
        "Roster.MaybeAt",
        &format!(
            "[{},{}]",
            constructor_json("NoRef", "[]"),
            constructor_json("At", r#"[["Ref","Roster.E"]]"#)
        ),
    );
    let definitions = definition_json(&format!(
        "[{}]",
        vocabulary_json(
            "Roster",
            &format!("[{root},{e},{other},{empty},{maybe}]"),
            "[]"
        )
    ));
    let checked =
        check_definitions_controlled(&[("definition0", definitions.as_bytes())], &mut quiet())
            .unwrap();
    let digest = &checked.vocabularies["Roster"].digest;
    let law = format!(
        r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Roster {{ use vocabulary Roster version "1" digest "{digest}"; }}
reading Calc {{ use vocabulary Roster version "1" digest "{digest}"; use Roster as R; {script} }}"#
    );
    let suffix = if moved { "_moved" } else { "" };
    let shift = if moved { 10 } else { 0 };
    let mut origins = vec![];
    for (snap, mode) in [("v", "specification"), ("w", "proposed"), ("z", "observed")] {
        for (kind, start) in [("snapshot", 0), ("subjects", 2), ("values", 4)] {
            origins.push(format!(r#"{{"id":"{snap}_{kind}{suffix}","mode":"{mode}","method":"小さい登録表を提示する。","locations":[{{"source":"scan","path":"{snap}.{kind}.model","span":[{},{}]}}]}}"#,start+shift,start+shift+1));
        }
    }
    let first = format!(
        r#"{{"id":"v","origin":"v_snapshot{suffix}","subjects":[{{"id":"root","type":"Roster.Root","origin":"v_subjects{suffix}"}},{{"id":"item","type":"Roster.E","origin":"v_subjects{suffix}"}},{{"id":"noise","type":"Roster.Other","origin":"v_subjects{suffix}"}}],"atoms":[]}}"#
    );
    let atom=known_flag.map(|flag|format!(r#"{{"id":"flag","subject":"item","field":"Roster.E.flag","value":{flag},"origin":"w_values{suffix}"}}"#)).unwrap_or_default();
    let second = format!(
        r#"{{"id":"w","origin":"w_snapshot{suffix}","subjects":[{{"id":"root","type":"Roster.Root","origin":"w_subjects{suffix}"}},{{"id":"item","type":"Roster.E","origin":"w_subjects{suffix}"}}],"atoms":[{atom}]}}"#
    );
    let empty = format!(r#"{{"id":"z","origin":"z_snapshot{suffix}","subjects":[],"atoms":[]}}"#);
    let snapshots = if reverse {
        vec![second, first, empty]
    } else {
        vec![first, second, empty]
    }
    .join(",");
    let origins = origins.join(",");
    let revision = if moved { "r2" } else { "r1" };
    let uri = if moved {
        "urn:fixture:plain-ref:relocated"
    } else {
        "urn:fixture:plain-ref"
    };
    let map = format!(
        r#"{{"format":"archsig.archmap/2","semantics":"archsig/0.6.0","vocabularies":[{{"namespace":"Roster","version":"1","digest":"{digest}"}}],"sources":[{{"id":"scan","uri":"{uri}","revision":"{revision}","digest":"sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"}}],"origins":[{origins}],"snapshots":[{snapshots}]}}"#
    );
    InputSources::from_bytes(
        vec![definitions.into_bytes()],
        law.into_bytes(),
        map.into_bytes(),
    )
}
fn audit(wire: &Json, checked: &CheckedInputs) {
    let ns = index(wire);
    let mut earlier = BTreeSet::new();
    for node in arr(f(wire, "nodes")) {
        let mut links = vec![];
        refs(node, &mut links);
        for link in links {
            assert!(earlier.contains(link.as_str()), "既出Ref: {link}");
        }
        assert!(earlier.insert(text(f(node, "id"))));
        if f(node, "type") != &Json::str("Proposition") {
            assert!(!obj(node).contains_key("judgment"));
        }
        if let Some(value) = obj(node).get("value") {
            let mut refs_in_value = vec![];
            refs(value, &mut refs_in_value);
            for link in refs_in_value {
                assert_ne!(f(ns[link.as_str()], "state"), &Json::str("blocked"));
                assert!(!obj(ns[link.as_str()]).contains_key("partial"));
            }
        }
        for fact in arr(f(node, "support")) {
            let snapshot = checked
                .archmap()
                .snapshots
                .iter()
                .find(|s| s.id == text(f(fact, "snapshot")))
                .unwrap();
            let subject = snapshot
                .subjects
                .iter()
                .find(|s| s.id == text(f(fact, "subject")))
                .unwrap();
            let snapshot_origin = checked
                .archmap()
                .origins
                .iter()
                .find(|o| o.id == snapshot.origin)
                .unwrap();
            let (origin_id, kind, start) = if let Some(field) = obj(fact).get("field") {
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
                    panic!("欠測を支持Atomにしない")
                };
                assert_eq!(f(fact, "atom"), &Json::str(atom));
                assert!(pointer.starts_with("/snapshots/"));
                (origin, "values", 4)
            } else {
                assert!(!obj(fact).contains_key("atom"));
                (&subject.origin, "subjects", 2)
            };
            let origin = checked
                .archmap()
                .origins
                .iter()
                .find(|o| &o.id == origin_id)
                .unwrap();
            assert_eq!(origin.mode, snapshot_origin.mode);
            assert_eq!(
                origin.mode,
                match snapshot.id.as_str() {
                    "v" => archsig::archmap::Mode::Specification,
                    "w" => archsig::archmap::Mode::Proposed,
                    _ => archsig::archmap::Mode::Observed,
                }
            );
            let source = checked
                .archmap()
                .sources
                .iter()
                .find(|s| s.id == origin.locations[0].source)
                .unwrap();
            let shift = if source.revision == "r2" { 10 } else { 0 };
            assert_eq!(
                origin.locations[0].path,
                format!("{}.{kind}.model", snapshot.id)
            );
            assert_eq!(
                origin.locations[0].span,
                Some((start + shift, start + shift + 1))
            );
            assert_eq!(
                source.uri,
                if shift == 0 {
                    "urn:fixture:plain-ref"
                } else {
                    "urn:fixture:plain-ref:relocated"
                }
            );
        }
        for q in arr(f(f(node, "scope"), "quantifiers")) {
            if let Some(domain) = obj(q).get("domain") {
                let domain = target(&ns, domain, &Json::str("Domain"));
                assert_eq!(f(val(domain), "type"), f(q, "type"));
            }
        }
        if f(node, "type") == &Json::str("Expression")
            && f(val(node), "kind") == &Json::str("source")
        {
            let at = span(f(val(node), "location"));
            assert!(at.0 < at.1 && at.1 <= checked.sources().law().bytes().len());
            assert_eq!(span(f(f(node, "rule"), "location")), at);
        }
        if f(node, "type") == &Json::str("Evaluation") {
            if aggregate_instance(&ns, node).is_none() {
                assert_eq!(
                    f(val(expression(&ns, node)), "bindings"),
                    f(val(node), "bindings")
                );
                assert_eq!(span(f(part(node), "location")), evaluation_span(&ns, node));
            }
            for part in arr(f(val(node), "parts")) {
                for child in arr(f(part, "children")) {
                    for fact in arr(f(target(&ns, child, &Json::str("Evaluation")), "support")) {
                        assert!(arr(f(node, "support")).contains(fact));
                    }
                }
            }
        }
        if f(node, "type") == &Json::str("Domain") && f(val(node), "kind") == &Json::str("finite") {
            for member in arr(f(val(node), "elements")) {
                val(target(&ns, member, f(val(node), "type")));
            }
        }
        if f(node, "type") == &Json::str("Evidence")
            && f(val(node), "kind") == &Json::str("finite_exhaustion")
        {
            let data = f(val(node), "data");
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
    for answer in arr(f(wire, "answers")) {
        let mut links = vec![];
        refs(answer, &mut links);
        for link in links {
            assert!(ns.contains_key(link.as_str()));
        }
    }
}
fn assert_roster_scope(node: &Json) {
    let scope = f(node, "scope");
    assert_eq!(
        f(scope, "snapshots"),
        &Json::Arr(vec![Json::str("v"), Json::str("w"), Json::str("z")])
    );
    assert_eq!(
        f(scope, "modes"),
        &Json::Arr(vec![
            Json::str("observed"),
            Json::str("proposed"),
            Json::str("specification")
        ])
    );
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
fn existence(snapshot: &str) -> Json {
    Json::obj([
        ("snapshot", Json::str(snapshot)),
        ("subject", Json::str("item")),
    ])
}
fn assert_roster_support(node: &Json) {
    let support = arr(f(node, "support"));
    assert!(support.contains(&existence("v")));
    assert!(support.contains(&existence("w")));
    assert!(
        support.iter().all(|p| text(f(p, "subject")) == "item"),
        "異型Root/Otherを混入しない"
    );
}
fn assert_missing(wire: &Json, id: &str, checked: &CheckedInputs) {
    let ns = index(wire);
    let reasons = arr(f(answer(wire, id), "reasons"))
        .iter()
        .filter(|r| f(r, "code") == &Json::str("missing_observation"))
        .collect::<Vec<_>>();
    assert!(!reasons.is_empty());
    for reason in reasons {
        assert!(
            arr(f(reason, "missing"))
                .iter()
                .all(|p| f(p, "field") == &Json::str("Roster.E.flag")
                    && f(p, "subject") == &Json::str("item")
                    && !obj(p).contains_key("atom"))
        );
        assert!(!arr(f(reason, "dependencies")).is_empty());
        for dep in arr(f(reason, "dependencies")) {
            let dep = target(&ns, dep, &Json::str("Expression"));
            let bytes = source(checked, span(f(val(dep), "location")));
            assert!(bytes == b"r.flag" || bytes == b"s.flag");
        }
    }
}
fn member_key(t: &Json, value: &Json) -> String {
    if let Json::Arr(parts) = t
        && parts.first() == Some(&Json::str("Set"))
    {
        let mut values = arr(value).iter().map(Json::canonical).collect::<Vec<_>>();
        values.sort();
        format!("{values:?}")
    } else {
        value.canonical()
    }
}
fn assert_full_domain(
    wire: &Json,
    checked: &CheckedInputs,
    id: &str,
    declaration: &str,
    binder: &str,
    t: Json,
    wanted: &[Json],
    truth: bool,
) {
    let ns = index(wire);
    let kind = if truth { "forall" } else { "exists" };
    let domain = quantifier_domain(wire, id, binder, kind, &t);
    assert_roster_scope(domain);
    let mut actual = arr(f(val(domain), "elements"))
        .iter()
        .map(|r| member_key(&t, val(target(&ns, r, &t))))
        .collect::<Vec<_>>();
    actual.sort();
    let mut expected = wanted.iter().map(|v| member_key(&t, v)).collect::<Vec<_>>();
    expected.sort();
    assert_eq!(actual, expected, "{id}:全域");
    let original = declared_body(checked, declaration);
    let body = type_body(checked, declaration);
    let body_span = checked.law().exprs[body].span;
    let source_node = arr(f(domain, "arguments"))
        .iter()
        .map(|r| ns[text(f(r, "node"))])
        .find(|n| f(n, "type") == &Json::str("Expression"))
        .unwrap();
    assert_eq!(
        span(f(val(source_node), "location")),
        checked.law().exprs[original].span
    );
    assert!(
        arr(f(domain, "arguments"))
            .iter()
            .all(|r| f(ns[text(f(r, "node"))], "type") != &Json::str("Evaluation"))
    );
    let body_evals = children(&ns, root(wire, id));
    assert_eq!(body_evals.len(), wanted.len());
    let mut covered = vec![];
    for body in body_evals {
        assert_eq!(evaluation_span(&ns, body), body_span);
        assert_eq!(
            val(target(&ns, f(val(body), "value"), &Json::str("Bool"))),
            &Json::Bool(truth)
        );
        let selected = arr(f(expression(&ns, body), "arguments"))
            .iter()
            .filter(|r| arr(f(val(domain), "elements")).contains(r))
            .collect::<Vec<_>>();
        assert_eq!(selected.len(), 1);
        covered.push(member_key(&t, val(target(&ns, selected[0], &t))));
        assert!(
            arr(f(val(body), "bindings"))
                .iter()
                .all(|b| f(b, "name") != &Json::str(binder))
        );
        assert!(reached(&ns, &[body]).contains(text(f(domain, "id"))));
    }
    covered.sort();
    assert_eq!(covered, expected, "{id}:実binder coverage");
    let proofs = evidence(&ns, answer(wire, id), "finite_exhaustion");
    assert_eq!(proofs.len(), 1);
    let data = f(val(proofs[0]), "data");
    assert_eq!(
        f(data, "domain"),
        &Json::obj([("node", f(domain, "id").clone())])
    );
    assert_eq!(f(data, "checked"), &Json::Nat(wanted.len() as u64));
    assert_eq!(arr(f(data, "instances")).len(), wanted.len());
    for instance in arr(f(data, "instances")) {
        assert_eq!(
            evaluation_span(&ns, target(&ns, instance, &Json::str("Evaluation"))),
            body_span
        );
    }
}

#[test]
fn plain_ref_quantifiers_keep_snapshot_identity_and_roster_scope() {
    let script = r#"
view all_refs(): Bool = forall r:E . r=r;
view unused_refs(): Bool = forall r:E . true;
view exists_ref(): Bool = exists r:R.E . true;
law required self_law(): forall r:E . r=r;
"#;
    let asks = [
        "a=evaluate(Calc.all_refs)",
        "b=evaluate(Calc.unused_refs)",
        "c=evaluate(Calc.exists_ref)",
        "d=check(Calc.self_law)",
    ];
    let (wire, checked) = run(fixture(script, Some(false), false, false), &asks);
    assert_eq!(f(&wire, "status"), &Json::str("complete"));
    for id in ["a", "b", "c"] {
        output(&wire, id, &Json::str("Bool"), Json::Bool(true));
    }
    check_claim(&wire, "d", "established");
    let t = ty("Ref", Json::str("Roster.E"));
    let wanted = vec![reference("v", "item"), reference("w", "item")];
    for (id, declaration) in [("a", "Calc.all_refs"), ("b", "Calc.unused_refs")] {
        assert_full_domain(
            &wire,
            &checked,
            id,
            declaration,
            "r",
            t.clone(),
            &wanted,
            true,
        );
    }
    let ns = index(&wire);
    let domain = quantifier_domain(&wire, "a", "r", "forall", &t);
    assert_eq!(
        domain_values(&wire, domain),
        wanted.iter().map(Json::canonical).collect::<Vec<_>>()
    );
    for node in std::iter::once(domain)
        .chain(
            arr(f(val(domain), "elements"))
                .iter()
                .map(|r| target(&ns, r, &t)),
        )
        .chain([
            root(&wire, "a"),
            target(&ns, f(val(root(&wire, "a")), "value"), &Json::str("Bool")),
        ])
    {
        assert_roster_scope(node);
        assert_roster_support(node);
    }
    for snapshot in &checked.archmap().snapshots {
        let origin = checked
            .archmap()
            .origins
            .iter()
            .find(|o| o.id == snapshot.origin)
            .unwrap();
        assert_eq!(
            origin.locations[0].path,
            format!("{}.snapshot.model", snapshot.id)
        );
        assert_eq!(origin.locations[0].span, Some((0, 1)));
        if snapshot.id == "z" {
            assert!(snapshot.subjects.is_empty());
            assert_eq!(origin.mode, archsig::archmap::Mode::Observed);
        }
        for subject in snapshot.subjects.iter().filter(|s| s.ty == "Roster.E") {
            assert_eq!(
                subject
                    .fields
                    .iter()
                    .find(|f| f.name == "Roster.E.owner")
                    .unwrap()
                    .slot,
                archsig::archmap::Slot::Missing
            );
        }
    }
    let body = type_body(&checked, "Calc.all_refs");
    let body_span = checked.law().exprs[body].span;
    for body in evaluations_at(&wire, body_span) {
        for name_eval in children(&ns, body) {
            let scalar = target(&ns, f(val(name_eval), "value"), &t);
            assert_eq!(
                arr(f(scalar, "arguments")),
                &[Json::obj([("node", f(domain, "id").clone())])]
            );
            assert_roster_support(scalar);
            assert_roster_scope(scalar);
        }
    }
    let (moved, moved_checked) = run(fixture(script, Some(false), false, true), &[asks[0]]);
    output(&moved, "a", &Json::str("Bool"), Json::Bool(true));
    assert_eq!(
        domain_values(&moved, quantifier_domain(&moved, "a", "r", "forall", &t)),
        domain_values(&wire, domain)
    );
    for key in ["readings", "snapshots", "modes", "domain"] {
        assert_eq!(
            f(f(answer(&moved, "a"), "scope"), key),
            f(f(answer(&wire, "a"), "scope"), key)
        );
    }
    assert!(
        moved_checked
            .archmap()
            .origins
            .iter()
            .all(|o| o.id.ends_with("_moved"))
    );
    assert_eq!(moved_checked.archmap().sources[0].revision, "r2");
    assert_eq!(
        moved_checked.archmap().sources[0].uri,
        "urn:fixture:plain-ref:relocated"
    );
}

#[test]
fn ref_container_domains_keep_exact_values_and_empty_families() {
    let script = r#"
view product(): Bool = forall p:(E,Bool) . p=p;
view optional_refs(): Bool = forall o:Option<E> . o=o;
view set_refs(): Bool = forall a:Set<E> . a=a;
view data_refs(): Bool = forall d:MaybeAt . d=d;
view empty_all(): Bool = forall r:Empty . true;
view empty_exists(): Bool = exists r:Empty . true;
view empty_option(): Bool = forall o:Option<Empty> . o=none<Empty>;
view empty_set(): Bool = forall a:Set<Empty> . a=set<Empty>{};
"#;
    let names = [
        "product",
        "optional_refs",
        "set_refs",
        "data_refs",
        "empty_all",
        "empty_exists",
        "empty_option",
        "empty_set",
    ];
    let asks = names
        .iter()
        .map(|n| format!("{n}=evaluate(Calc.{n})"))
        .collect::<Vec<_>>();
    let (wire, checked) = run(
        fixture(script, Some(false), false, false),
        &asks.iter().map(String::as_str).collect::<Vec<_>>(),
    );
    assert_eq!(f(&wire, "status"), &Json::str("complete"));
    for name in names {
        output(
            &wire,
            name,
            &Json::str("Bool"),
            Json::Bool(name != "empty_exists"),
        );
    }
    let e = ty("Ref", Json::str("Roster.E"));
    let empty = ty("Ref", Json::str("Roster.Empty"));
    let v = reference("v", "item");
    let w = reference("w", "item");
    let product = vec![
        Json::Arr(vec![v.clone(), Json::Bool(false)]),
        Json::Arr(vec![v.clone(), Json::Bool(true)]),
        Json::Arr(vec![w.clone(), Json::Bool(false)]),
        Json::Arr(vec![w.clone(), Json::Bool(true)]),
    ];
    let options = vec![
        Json::obj([("none", Json::Bool(true))]),
        Json::obj([("some", v.clone())]),
        Json::obj([("some", w.clone())]),
    ];
    let sets = vec![
        Json::Arr(vec![]),
        Json::Arr(vec![v.clone()]),
        Json::Arr(vec![w.clone()]),
        Json::Arr(vec![v.clone(), w.clone()]),
    ];
    let data_values = vec![
        data("NoRef", vec![]),
        data("At", vec![v]),
        data("At", vec![w]),
    ];
    for (name, binder, t, wanted, truth) in [
        (
            "product",
            "p",
            Json::Arr(vec![Json::str("Tuple"), e.clone(), Json::str("Bool")]),
            product,
            true,
        ),
        ("optional_refs", "o", ty("Option", e.clone()), options, true),
        ("set_refs", "a", ty("Set", e), sets, true),
        (
            "data_refs",
            "d",
            ty("Data", Json::str("Roster.MaybeAt")),
            data_values,
            true,
        ),
        ("empty_all", "r", empty.clone(), vec![], true),
        ("empty_exists", "r", empty.clone(), vec![], false),
        (
            "empty_option",
            "o",
            ty("Option", empty.clone()),
            vec![Json::obj([("none", Json::Bool(true))])],
            true,
        ),
        (
            "empty_set",
            "a",
            ty("Set", empty),
            vec![Json::Arr(vec![])],
            true,
        ),
    ] {
        // 空existsも全域の全false判断。body未実行、checked=0を確認する。
        assert_full_domain(
            &wire,
            &checked,
            name,
            &format!("Calc.{name}"),
            binder,
            t.clone(),
            &wanted,
            truth,
        );
        let ns = index(&wire);
        let domain = quantifier_domain(
            &wire,
            name,
            binder,
            if truth { "forall" } else { "exists" },
            &t,
        );
        if name.starts_with("empty_") {
            assert!(arr(f(domain, "support")).is_empty());
        } else {
            assert_roster_support(domain);
            for member in arr(f(val(domain), "elements")) {
                let member = target(&ns, member, &t);
                assert_roster_scope(member);
                assert_roster_support(member);
            }
        }
    }
}

#[test]
fn plain_ref_quantifiers_keep_missing_and_actual_counterexamples() {
    let script = r#"
view all_flags(): Bool = forall r:E . r.flag;
view any_flag(): Bool = exists r:E . r.flag;
law required flags_law(): forall r:E . r.flag;
"#;
    let asks = ["a=evaluate(Calc.all_flags)", "b=check(Calc.flags_law)"];
    for reverse in [false, true] {
        let (wire, checked) = run(fixture(script, Some(false), reverse, false), &asks);
        output(&wire, "a", &Json::str("Bool"), Json::Bool(false));
        check_claim(&wire, "b", "refuted");
        assert_eq!(f(&wire, "status"), &Json::str("complete"));
        let ns = index(&wire);
        let t = ty("Ref", Json::str("Roster.E"));
        let domain = quantifier_domain(&wire, "a", "r", "forall", &t);
        assert_eq!(
            domain_values(&wire, domain),
            vec![
                reference("v", "item").canonical(),
                reference("w", "item").canonical()
            ]
        );
        for id in ["a", "b"] {
            assert_missing(&wire, id, &checked);
            assert_roster_scope(answer(&wire, id));
            assert_roster_support(root(&wire, id));
            let reasons = arr(f(answer(&wire, id), "reasons"));
            assert!(
                reasons
                    .iter()
                    .filter(|r| f(r, "code") == &Json::str("missing_observation"))
                    .flat_map(|r| arr(f(r, "missing")))
                    .any(|p| f(p, "snapshot") == &Json::str("v"))
            );
            let examples = evidence(&ns, answer(&wire, id), "counterexample");
            let example = examples
                .iter()
                .find(|e| {
                    arr(f(f(val(e), "data"), "facts")).contains(&Json::obj([
                        ("snapshot", Json::str("w")),
                        ("subject", Json::str("item")),
                        ("field", Json::str("Roster.E.flag")),
                        ("atom", Json::str("flag")),
                    ]))
                })
                .unwrap();
            let data = f(val(example), "data");
            let binder = arr(f(data, "bindings"))
                .iter()
                .find(|b| f(b, "name") == &Json::str("r"))
                .unwrap();
            assert_eq!(
                val(target(&ns, f(binder, "value"), &t)),
                &reference("w", "item")
            );
            assert_eq!(
                val(target(&ns, f(data, "left"), &Json::str("Bool"))),
                &Json::Bool(false)
            );
            assert_eq!(
                val(target(&ns, f(data, "right"), &Json::str("Bool"))),
                &Json::Bool(true)
            );
            assert!(arr(f(data, "facts")).contains(&Json::obj([
                ("snapshot", Json::str("w")),
                ("subject", Json::str("item")),
                ("field", Json::str("Roster.E.flag")),
                ("atom", Json::str("flag"))
            ])));
            let body = arr(f(example, "arguments"))
                .iter()
                .map(|r| ns[text(f(r, "node"))])
                .find(|n| f(n, "type") == &Json::str("Evaluation"))
                .unwrap();
            assert_eq!(source(&checked, evaluation_span(&ns, body)), b"r.flag");
            assert_eq!(f(val(body), "value"), f(data, "left"));
            assert_roster_support(body);
            assert_roster_scope(body);
        }
    }
    let (all_missing, checked) = run(
        fixture(script, None, false, false),
        &["a=evaluate(Calc.all_flags)", "b=evaluate(Calc.any_flag)"],
    );
    assert_eq!(f(&all_missing, "status"), &Json::str("partial"));
    let ns = index(&all_missing);
    for (id, kind) in [("a", "forall"), ("b", "exists")] {
        let a = answer(&all_missing, id);
        assert_eq!(f(a, "status"), &Json::str("undetermined"));
        assert!(!obj(f(a, "outputs")).contains_key("value"));
        assert_missing(&all_missing, id, &checked);
        let aggregate = root(&all_missing, id);
        let seed = expression(&ns, aggregate);
        assert_eq!(
            arr(f(aggregate, "arguments")).first(),
            Some(f(val(aggregate), "expression"))
        );
        let name = if id == "a" {
            "Calc.all_flags"
        } else {
            "Calc.any_flag"
        };
        let expected_span = checked.law().exprs[declared_body(&checked, name)].span;
        let originals = arr(f(seed, "arguments"))
            .iter()
            .map(|r| ns[text(f(r, "node"))])
            .filter(|n| {
                f(n, "type") == &Json::str("Evaluation")
                    && evaluation_span(&ns, n) == expected_span
                    && f(val(expression(&ns, n)), "kind") == &Json::str("source")
                    && arr(f(val(expression(&ns, n)), "parameters")).is_empty()
                    && arr(f(val(expression(&ns, n)), "bindings")).is_empty()
                    && arr(f(val(n), "bindings")).is_empty()
                    && arr(f(n, "arguments")).first() == Some(f(val(n), "expression"))
            })
            .collect::<Vec<_>>();
        assert_eq!(
            originals.len(),
            1,
            "元補完seedの直接rootsから元AST/束縛/型付き辺の評価を一意選択"
        );
        let original = originals[0];
        assert!(!obj(val(original)).contains_key("value"));
        assert_eq!(
            f(f(original, "scope"), "domain"),
            &Json::str("all_completions")
        );
        assert_roster_scope(original);
        assert_roster_support(original);
        let q = arr(f(f(original, "scope"), "quantifiers"))
            .iter()
            .find(|q| f(q, "name") == &Json::str("r") && f(q, "kind") == &Json::str(kind))
            .unwrap();
        let original_domain = target(&ns, f(q, "domain"), &Json::str("Domain"));
        assert_eq!(f(val(original_domain), "kind"), &Json::str("finite"));
        assert_eq!(
            f(val(original_domain), "type"),
            &ty("Ref", Json::str("Roster.E"))
        );
        assert_eq!(
            domain_values(&all_missing, original_domain),
            vec![
                reference("v", "item").canonical(),
                reference("w", "item").canonical()
            ]
        );
        assert_eq!(
            domain_values(
                &all_missing,
                quantifier_domain(
                    &all_missing,
                    id,
                    "r",
                    kind,
                    &ty("Ref", Json::str("Roster.E"))
                )
            )
            .len(),
            2
        );
        let missing = arr(f(a, "reasons"))
            .iter()
            .filter(|r| f(r, "code") == &Json::str("missing_observation"))
            .flat_map(|r| arr(f(r, "missing")))
            .map(|m| text(f(m, "snapshot")))
            .collect::<BTreeSet<_>>();
        assert_eq!(missing, BTreeSet::from(["v", "w"]));
        let original_missing = arr(f(original, "reasons"))
            .iter()
            .filter(|r| f(r, "code") == &Json::str("missing_observation"))
            .flat_map(|r| arr(f(r, "missing")))
            .map(|m| text(f(m, "snapshot")))
            .collect::<BTreeSet<_>>();
        assert_eq!(original_missing, BTreeSet::from(["v", "w"]));
        assert!(evidence(&ns, original, "finite_exhaustion").is_empty());
        assert!(evidence(&ns, original, "counterexample").is_empty());
        let original_bodies = children(&ns, original);
        assert_eq!(original_bodies.len(), 2);
        assert!(
            original_bodies
                .iter()
                .all(|body| !obj(val(body)).contains_key("value"))
        );
        assert_eq!(
            f(f(aggregate, "scope"), "domain"),
            &Json::str("all_completions")
        );
        let assignment_domain_ref = &arr(f(aggregate, "arguments"))[1];
        let assignment_domain = target(&ns, assignment_domain_ref, &Json::str("Domain"));
        let assignment_type = Json::Arr(vec![
            Json::str("Tuple"),
            Json::str("Bool"),
            Json::str("Bool"),
        ]);
        assert_eq!(f(val(assignment_domain), "kind"), &Json::str("finite"));
        assert_eq!(f(val(assignment_domain), "type"), &assignment_type);
        assert_eq!(
            arr(f(assignment_domain, "arguments")).first(),
            Some(f(val(aggregate), "expression"))
        );
        let members = arr(f(val(assignment_domain), "elements"));
        assert_eq!(members.len(), 4);
        let cases = children(&ns, aggregate);
        assert_eq!(cases.len(), 4);
        let mut assignments = BTreeSet::new();
        let mut case_assignments = BTreeMap::new();
        for case in cases {
            assert_eq!(evaluation_span(&ns, case), expected_span);
            assert!(arr(f(val(case), "bindings")).is_empty());
            let case_source = expression(&ns, case);
            let selected = arr(f(case_source, "arguments"))
                .iter()
                .filter(|r| members.contains(r))
                .collect::<Vec<_>>();
            assert_eq!(selected.len(), 1);
            let assignment = arr(val(target(&ns, selected[0], &assignment_type)))
                .iter()
                .map(|b| {
                    let Json::Bool(b) = b else {
                        panic!("Bool slot")
                    };
                    *b
                })
                .collect::<Vec<_>>();
            assert_eq!(assignment.len(), 2);
            assert!(assignments.insert(assignment.clone()));
            case_assignments.insert(text(f(case, "id")), assignment.clone());
            let expected = if kind == "forall" {
                assignment[0] && assignment[1]
            } else {
                assignment[0] || assignment[1]
            };
            assert_eq!(
                val(target(&ns, f(val(case), "value"), &Json::str("Bool"))),
                &Json::Bool(expected)
            );
            assert_eq!(f(f(case, "scope"), "domain"), &Json::str("all_completions"));
            let case_q = arr(f(f(case, "scope"), "quantifiers"))
                .iter()
                .find(|q| f(q, "name") == &Json::str("r") && f(q, "kind") == &Json::str(kind))
                .unwrap();
            let domain = target(&ns, f(case_q, "domain"), &Json::str("Domain"));
            assert_eq!(
                domain_values(&all_missing, domain),
                domain_values(&all_missing, original_domain)
            );
            let bodies = children(&ns, case);
            assert_eq!(bodies.len(), 2);
            let mut owners = BTreeSet::new();
            for body in bodies {
                assert_eq!(source(&checked, evaluation_span(&ns, body)), b"r.flag");
                let value = target(&ns, f(val(body), "value"), &Json::str("Bool"));
                assert_eq!(f(f(value, "rule"), "kind"), &Json::str("law"));
                let inputs = arr(f(value, "arguments"));
                assert_eq!(inputs.len(), 3);
                assert_eq!(&inputs[0], f(val(body), "expression"));
                let owner = val(target(&ns, &inputs[1], &ty("Ref", Json::str("Roster.E"))));
                let at = if owner == &reference("v", "item") {
                    0
                } else {
                    assert_eq!(owner, &reference("w", "item"));
                    1
                };
                assert!(owners.insert(at));
                assert_eq!(val(value), &Json::Bool(assignment[at]));
                let projection = target(&ns, &inputs[2], &Json::str("Bool"));
                assert_eq!(f(f(projection, "rule"), "kind"), &Json::str("construction"));
                assert_eq!(val(projection), val(value));
                assert_eq!(&arr(f(projection, "arguments"))[1], assignment_domain_ref);
                assert_eq!(&arr(f(projection, "arguments"))[2], selected[0]);
                assert_roster_scope(body);
                assert_roster_support(body);
            }
            assert_eq!(owners, BTreeSet::from([0, 1]));
            let proofs = arr(f(case, "evidence"))
                .iter()
                .map(|r| target(&ns, r, &Json::str("Evidence")))
                .collect::<Vec<_>>();
            if (kind == "forall" && expected) || (kind == "exists" && !expected) {
                let full = proofs
                    .iter()
                    .filter(|p| f(val(p), "kind") == &Json::str("finite_exhaustion"))
                    .collect::<Vec<_>>();
                assert_eq!(full.len(), 1);
                let data = f(val(full[0]), "data");
                assert_eq!(f(data, "domain"), f(case_q, "domain"));
                assert_eq!(f(data, "checked"), &Json::Nat(2));
                assert_eq!(f(data, "instances"), f(part(case), "children"));
            } else if kind == "forall" {
                let counterexamples = proofs
                    .iter()
                    .filter(|p| f(val(p), "kind") == &Json::str("counterexample"))
                    .collect::<Vec<_>>();
                assert_eq!(
                    counterexamples.len(),
                    assignment.iter().filter(|b| !**b).count()
                );
                for counterexample in counterexamples {
                    let data = f(val(counterexample), "data");
                    let bindings = arr(f(data, "bindings"));
                    assert_eq!(bindings.len(), 1);
                    assert_eq!(f(&bindings[0], "name"), &Json::str("r"));
                    let owner = val(target(
                        &ns,
                        f(&bindings[0], "value"),
                        &ty("Ref", Json::str("Roster.E")),
                    ));
                    let at = if owner == &reference("v", "item") {
                        0
                    } else {
                        assert_eq!(owner, &reference("w", "item"));
                        1
                    };
                    assert!(!assignment[at]);
                    assert_eq!(
                        val(target(&ns, f(data, "left"), &Json::str("Bool"))),
                        &Json::Bool(false)
                    );
                    assert_eq!(
                        val(target(&ns, f(data, "right"), &Json::str("Bool"))),
                        &Json::Bool(true)
                    );
                    let edges = arr(f(counterexample, "arguments"));
                    assert_eq!(edges.len(), 3);
                    assert_eq!(&edges[0], f(val(case), "expression"));
                    assert_eq!(&edges[1], f(case_q, "domain"));
                    assert!(arr(f(part(case), "children")).contains(&edges[2]));
                    assert_eq!(
                        f(
                            val(target(&ns, &edges[2], &Json::str("Evaluation"))),
                            "value"
                        ),
                        f(data, "left")
                    );
                    assert_roster_scope(counterexample);
                    assert_roster_support(counterexample);
                }
            }
        }
        assert_eq!(
            assignments,
            BTreeSet::from([
                vec![false, false],
                vec![false, true],
                vec![true, false],
                vec![true, true]
            ])
        );
        assert!(
            arr(f(aggregate, "evidence"))
                .iter()
                .all(|r| f(val(target(&ns, r, &Json::str("Evidence"))), "kind")
                    != &Json::str("finite_exhaustion")),
            "異なるwhole値に全case同値の完成証拠を付けない"
        );
        let pairs = arr(f(aggregate, "evidence"))
            .iter()
            .map(|r| target(&ns, r, &Json::str("Evidence")))
            .filter(|e| f(val(e), "kind") == &Json::str("completion_pair"))
            .collect::<Vec<_>>();
        assert_eq!(pairs.len(), 1);
        let pair = f(val(pairs[0]), "data");
        assert_eq!(
            f(pair, "fields"),
            &Json::Arr(
                ["v", "w"]
                    .iter()
                    .map(|snap| Json::obj([
                        ("snapshot", Json::str(*snap)),
                        ("subject", Json::str("item")),
                        ("field", Json::str("Roster.E.flag"))
                    ]))
                    .collect()
            )
        );
        let mut results = BTreeSet::new();
        for (binding_key, result_key) in [("first", "first_result"), ("second", "second_result")] {
            let values = arr(f(pair, binding_key));
            assert_eq!(values.len(), 2);
            let assignment = values
                .iter()
                .map(|r| {
                    let Json::Bool(b) = val(target(&ns, r, &Json::str("Bool"))) else {
                        panic!("Bool")
                    };
                    *b
                })
                .collect::<Vec<_>>();
            let case = target(&ns, f(pair, result_key), &Json::str("Evaluation"));
            assert_eq!(case_assignments[text(f(case, "id"))], assignment);
            assert!(
                values
                    .iter()
                    .all(|r| arr(f(expression(&ns, case), "arguments")).contains(r))
            );
            let value = val(target(&ns, f(val(case), "value"), &Json::str("Bool")));
            results.insert(value.canonical());
        }
        assert_eq!(
            results,
            BTreeSet::from([Json::Bool(false).canonical(), Json::Bool(true).canonical()])
        );
    }
    let (wire, checked) = run(
        fixture(script, Some(true), false, false),
        &["a=evaluate(Calc.any_flag)"],
    );
    output(&wire, "a", &Json::str("Bool"), Json::Bool(true));
    assert_missing(&wire, "a", &checked);
}

#[test]
fn plain_ref_nested_quantifiers_preserve_parent_bindings() {
    let script = r#"
view echo(s: E): E = let held=s in match MaybeAt.At(held) { NoRef => s; At(x) => x; };
view nested(): Bool = forall r:E . exists x in list<E>[r] . echo(x)=r;
view restore(s: E): (Bool,E) = (forall r:E . echo(r)=r,s);
view owned(root: Root): Bool = forall r:E[root] . true;
view owned_option(root: Root): Bool = forall r:Option<E[root]> . true;
view owned_tuple(root: Root): Bool = forall r:(E[root],Bool) . true;
view unbounded_list(): Bool = forall unused:List<E> . true;
"#;
    let asks = [
        "a=evaluate(Calc.nested)",
        "b=evaluate(Calc.restore,s=@v/item)",
        "c=evaluate(Calc.restore,s=@w/item)",
    ];
    let (wire, checked) = run(fixture(script, Some(false), false, false), &asks);
    assert_eq!(f(&wire, "status"), &Json::str("complete"));
    output(&wire, "a", &Json::str("Bool"), Json::Bool(true));
    let ns = index(&wire);
    let t = ty("Ref", Json::str("Roster.E"));
    let tuple = Json::Arr(vec![Json::str("Tuple"), Json::str("Bool"), t.clone()]);
    for (id, snapshot) in [("b", "v"), ("c", "w")] {
        output(
            &wire,
            id,
            &tuple,
            Json::Arr(vec![Json::Bool(true), reference(snapshot, "item")]),
        );
        let bs = arr(f(val(root(&wire, id)), "bindings"));
        assert_eq!(bs.len(), 1);
        assert_eq!(f(&bs[0], "name"), &Json::str("s"));
        assert_eq!(
            val(target(&ns, f(&bs[0], "value"), &t)),
            &reference(snapshot, "item")
        );
    }
    let qs = arr(f(f(answer(&wire, "a"), "scope"), "quantifiers"));
    assert!(qs.len() >= 2);
    assert_eq!(
        (text(f(&qs[0], "kind")), text(f(&qs[0], "name"))),
        ("forall", "r")
    );
    for q in &qs[1..] {
        assert_eq!((text(f(q, "kind")), text(f(q, "name"))), ("exists", "x"));
    }
    let outer = quantifier_domain(&wire, "a", "r", "forall", &t);
    let inner_span = checked.law().exprs[type_body(&checked, "Calc.nested")].span;
    let inners = children(&ns, root(&wire, "a"));
    assert_eq!(inners.len(), 2);
    let mut selected = vec![];
    for inner in inners {
        assert_eq!(evaluation_span(&ns, inner), inner_span);
        assert!(reached(&ns, &[inner]).contains(text(f(outer, "id"))));
        let children = children(&ns, inner);
        assert_eq!(children.len(), 2);
        assert_eq!(
            source(&checked, evaluation_span(&ns, children[0])),
            b"list<E>[r]"
        );
        let value = val(target(
            &ns,
            f(val(children[0]), "value"),
            &ty("List", t.clone()),
        ));
        assert_eq!(arr(value).len(), 1);
        selected.push(arr(value)[0].canonical());
        assert_eq!(
            val(target(
                &ns,
                f(val(children[1]), "value"),
                &Json::str("Bool")
            )),
            &Json::Bool(true)
        );
    }
    selected.sort();
    assert_eq!(
        selected,
        vec![
            reference("v", "item").canonical(),
            reference("w", "item").canonical()
        ]
    );
    let input = fixture(script, Some(false), false, false);
    let checked = check_inputs(input.clone(), &mut quiet()).unwrap();
    for (declaration, ask) in [
        ("Calc.owned", "d=evaluate(Calc.owned,root=@v/root)"),
        (
            "Calc.owned_option",
            "d=evaluate(Calc.owned_option,root=@v/root)",
        ),
        (
            "Calc.owned_tuple",
            "d=evaluate(Calc.owned_tuple,root=@v/root)",
        ),
        ("Calc.unbounded_list", "d=evaluate(Calc.unbounded_list)"),
    ] {
        let error = match evaluate_observed_bytes(input.clone(), &[ask], &mut quiet()) {
            Err(error) => error,
            Ok(result) => panic!(
                "{declaration}: 専用NotImplementedの代わりにstatus={}",
                result.status()
            ),
        };
        assert!(
            error.wire().is_none(),
            "{declaration}: 公開wireへ変換しない"
        );
        let EvaluationFailure::NotImplemented {
            declaration: found,
            location: archsig::issue::Location::Law { span },
            feature,
        } = error
        else {
            panic!("{declaration}: 対象外専用NotImplemented")
        };
        assert_eq!(found, declaration);
        assert_eq!(
            span,
            checked.law().exprs[declared_body(&checked, declaration)].span
        );
        assert!(!feature.is_empty());
    }
}

#[test]
fn plain_ref_fixed_expression_stops_keep_prefixes() {
    let input = fixture(
        r#"
view seed(s: E): Unit = unit;
view absent(s: E): Bool = s.flag;
law required rejected(): forall r:E . r.flag;
view current(): Bool = forall r:E . true;
view later(s: E): Unit = unit;
"#,
        Some(false),
        false,
        false,
    );
    let checked = check_inputs(input.clone(), &mut quiet()).unwrap();
    let asks = [
        "seed=evaluate(Calc.seed,s=@v/item)",
        "absent=evaluate(Calc.absent,s=@v/item)",
        "rejected=check(Calc.rejected)",
        "current=evaluate(Calc.current)",
        "later=evaluate(Calc.later,s=@v/item)",
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
    output(&prior, "seed", &Json::str("Unit"), Json::Arr(vec![]));
    assert_missing(&prior, "absent", &checked);
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
    assert_eq!(total.get() - count.get(), 6);
    let original = declared_body(&checked, "Calc.current");
    let original_span = checked.law().exprs[original].span;
    let body_span = checked.law().exprs[type_body(&checked, "Calc.current")].span;
    let ns = index(&baseline);
    assert_eq!(children(&ns, root(&baseline, "current")).len(), 2);
    assert_roster_support(root(&baseline, "current"));
    assert_roster_support(target(
        &ns,
        f(val(root(&baseline, "current")), "value"),
        &Json::str("Bool"),
    ));
    assert!(!evidence(&ns, answer(&baseline, "current"), "finite_exhaustion").is_empty());
    // roster列挙後のbody pre、次body pre、最後body postの3固定点。実roster/構成/再検査内はprivate試験で確認する。
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
        output(&wire, "seed", &Json::str("Unit"), Json::Arr(vec![]));
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
        assert!(evaluations_at(&wire, original_span).is_empty());
        let bodies = evaluations_at(&wire, body_span);
        assert_eq!(bodies.len(), done);
        let domains = arr(f(&wire, "nodes"))
            .iter()
            .filter(|n| {
                f(n, "type") == &Json::str("Domain")
                    && arr(f(n, "arguments")).iter().any(|r| {
                        let source = ns[text(f(r, "node"))];
                        f(source, "type") == &Json::str("Expression")
                            && span(f(val(source), "location")) == original_span
                    })
            })
            .collect::<Vec<_>>();
        assert_eq!(domains.len(), 1);
        assert_roster_scope(domains[0]);
        assert_roster_support(domains[0]);
        let domain_ref = Json::obj([("node", f(domains[0], "id").clone())]);
        let quant_source = arr(f(domains[0], "arguments"))
            .iter()
            .find(|r| {
                let node = ns[text(f(r, "node"))];
                f(node, "type") == &Json::str("Expression")
                    && span(f(val(node), "location")) == original_span
            })
            .unwrap();
        let member_type = ty("Ref", Json::str("Roster.E"));
        assert_eq!(f(val(domains[0]), "type"), &member_type);
        assert_eq!(
            domain_values(&wire, domains[0]),
            vec![
                reference("v", "item").canonical(),
                reference("w", "item").canonical()
            ]
        );
        let mut selected_values = BTreeSet::new();
        for body in bodies {
            let scalar = target(&ns, f(val(body), "value"), &Json::str("Bool"));
            assert_eq!(val(scalar), &Json::Bool(true));
            assert_roster_scope(body);
            assert!(
                arr(f(body, "support")).is_empty(),
                "定数true bodyへ存在事実を直接追加しない"
            );
            assert!(
                arr(f(scalar, "support")).is_empty(),
                "定数値へ存在事実を直接追加しない"
            );
            let source_node = expression(&ns, body);
            assert_eq!(
                source(&checked, span(f(val(source_node), "location"))),
                b"true"
            );
            let arguments = arr(f(source_node, "arguments"));
            assert!(
                arguments.contains(&domain_ref),
                "元定数出現から今回のDomainへ戻る"
            );
            assert!(
                arguments.contains(quant_source),
                "元定数出現から今回の量化ASTへ戻る"
            );
            let selected = arguments
                .iter()
                .filter(|r| arr(f(val(domains[0]), "elements")).contains(r))
                .collect::<Vec<_>>();
            assert_eq!(selected.len(), 1, "未使用binderも実memberを保持");
            let member = target(&ns, selected[0], &member_type);
            assert!(
                selected_values.insert(val(member).canonical()),
                "完成body間で同じmemberを重複しない"
            );
            assert_roster_scope(member);
            assert_roster_support(member);
            assert!(
                reached(&ns, &[body]).contains(text(f(domains[0], "id"))),
                "原出現からDomainの存在支持へ到達する"
            );
        }
        assert_eq!(selected_values.len(), done);
        if done == 2 {
            assert_eq!(
                selected_values,
                BTreeSet::from([
                    reference("v", "item").canonical(),
                    reference("w", "item").canonical()
                ])
            );
        }
        assert!(
            !arr(f(&wire, "nodes"))
                .iter()
                .any(|n| f(n, "type") == &Json::str("Evidence")
                    && f(val(n), "kind") == &Json::str("finite_exhaustion")
                    && f(f(val(n), "data"), "domain") == &domain_ref)
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
