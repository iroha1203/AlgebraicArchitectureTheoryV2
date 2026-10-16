//! 有限な未束縛Law parameterの実直積と適用族を独立三入力から検査する。
mod common;
use archsig::{
    canonical::Json,
    definition::check_definitions_controlled,
    law::model::Signature,
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
    let (Signature::View { body, .. } | Signature::Law { body, .. }) =
        &checked.law().declarations[name].signature
    else {
        panic!("view/law")
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
    let flagged = data_json(
        "Roster.Flagged",
        &format!(
            "[{},{}]",
            constructor_json("EmptyFlag", "[]"),
            constructor_json("Flag", r#"["Bool"]"#)
        ),
    );
    let definitions = definition_json(&format!(
        "[{}]",
        vocabulary_json(
            "Roster",
            &format!("[{root},{e},{other},{empty},{maybe},{flagged}]"),
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
            if aggregate_instance(&ns, node).is_none()
                && arr(f(val(expression(&ns, node)), "parameters")).is_empty()
                && arr(f(val(node), "parts")).len() == 1
            {
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

fn law_parts(checked: &CheckedInputs, name: &str) -> (usize, Option<usize>) {
    let Signature::Law { body, guard, .. } = &checked.law().declarations[name].signature else {
        panic!("Law")
    };
    (*body, *guard)
}
fn binding_values(wire: &Json, bindings: &Json, types: &[(&str, Json)]) -> Vec<Json> {
    let ns = index(wire);
    let bindings = arr(bindings);
    assert_eq!(bindings.len(), types.len());
    bindings
        .iter()
        .zip(types)
        .map(|(binding, (name, t))| {
            assert_eq!(f(binding, "name"), &Json::str(*name));
            val(target(&ns, f(binding, "value"), t)).clone()
        })
        .collect()
}
fn instance_for_eval<'a>(wire: &'a Json, id: &str, name: &str, evaluation: &Json) -> &'a Json {
    let ns = index(wire);
    if let Some(instance) = aggregate_instance(&ns, evaluation) {
        assert_eq!(f(val(instance), "name"), &Json::str(name));
        return instance;
    }
    let reference = Json::obj([("node", f(evaluation, "id").clone())]);
    let instances = reached(&ns, &[answer(wire, id)])
        .iter()
        .map(|id| ns[id.as_str()])
        .filter(|n| {
            f(n, "type") == &Json::str("LawInstance")
                && f(val(n), "name") == &Json::str(name)
                && arr(f(n, "arguments")).first() == Some(&reference)
                && f(val(n), "bindings") == f(val(evaluation), "bindings")
                && f(val(n), "body") == f(val(evaluation), "expression")
        })
        .collect::<Vec<_>>();
    assert_eq!(
        instances.len(),
        1,
        "省略guardのraw body Evaluationを実LawInstanceの辺から照合"
    );
    instances[0]
}
fn row_instances<'a>(wire: &'a Json, id: &str, name: &str) -> Vec<(&'a Json, &'a Json)> {
    row_instances_selected(wire, root(wire, id), name)
}
fn row_instances_selected<'a>(
    wire: &'a Json,
    whole_eval: &Json,
    name: &str,
) -> Vec<(&'a Json, &'a Json)> {
    let ns = index(wire);
    let whole = aggregate_instance(&ns, whole_eval).expect("選択した実Law族whole");
    children(&ns, whole_eval)
        .into_iter()
        .map(|evaluation| {
            let reference = Json::obj([("node", f(evaluation, "id").clone())]);
            let instances = arr(f(whole, "arguments"))
                .iter()
                .map(|r| ns[text(f(r, "node"))])
                .filter(|n| {
                    f(n, "type") == &Json::str("LawInstance")
                        && f(val(n), "name") == &Json::str(name)
                        && (aggregate_instance(&ns, evaluation)
                            .is_some_and(|instance| f(instance, "id") == f(n, "id"))
                            || (arr(f(n, "arguments")).first() == Some(&reference)
                                && f(val(n), "bindings") == f(val(evaluation), "bindings")
                                && f(val(n), "body") == f(val(evaluation), "expression")))
                })
                .collect::<Vec<_>>();
            assert_eq!(
                instances.len(),
                1,
                "選択したwholeの直接辺から実row instanceを一意照合"
            );
            let instance = instances[0];
            (instance, evaluation)
        })
        .collect()
}
fn row_keys(rows: &[Vec<Json>], types: &[(&str, Json)]) -> BTreeSet<String> {
    rows.iter()
        .map(|row| {
            Json::Arr(
                row.iter()
                    .zip(types)
                    .map(|(value, (_, t))| Json::str(member_key(t, value)))
                    .collect(),
            )
            .canonical()
        })
        .collect()
}
fn retained_observed_family<'a>(wire: &'a Json, id: &str, name: &str) -> (&'a Json, &'a Json) {
    let ns = index(wire);
    let aggregate = root(wire, id);
    let seed = expression(&ns, aggregate);
    assert_eq!(
        arr(f(aggregate, "arguments")).first(),
        Some(f(val(aggregate), "expression"))
    );
    let direct = arr(f(seed, "arguments"))
        .iter()
        .map(|r| ns[text(f(r, "node"))])
        .collect::<Vec<_>>();
    let claims = direct
        .iter()
        .copied()
        .filter(|n| {
            f(n, "type") == &Json::str("Proposition")
                && f(val(n), "predicate") == &Json::str("law_holds")
                && arr(f(val(n), "operands")).len() == 1
                && f(
                    val(target(
                        &ns,
                        &arr(f(val(n), "operands"))[0],
                        &Json::str("LawInstance"),
                    )),
                    "name",
                ) == &Json::str(name)
        })
        .collect::<Vec<_>>();
    assert_eq!(
        claims.len(),
        1,
        "元補完seedの直接辺から元Law族命題を一意選択"
    );
    let claim = claims[0];
    let args = arr(f(claim, "arguments"));
    assert_eq!(args.len(), 2);
    assert_eq!(&args[0], &arr(f(val(claim), "operands"))[0]);
    let whole_eval = target(&ns, &args[1], &Json::str("Evaluation"));
    assert!(
        direct.iter().any(|n| f(n, "id") == f(whole_eval, "id")),
        "元whole評価もseedの直接root"
    );
    assert_eq!(arr(f(whole_eval, "arguments")).first(), Some(&args[0]));
    (whole_eval, claim)
}
fn assert_universal_request(wire: &Json, id: &str, name: &str, parameters: &[&str]) {
    let request = arr(f(wire, "requests"))
        .iter()
        .find(|r| f(r, "id") == &Json::str(id))
        .unwrap();
    let default = arr(f(request, "defaults"))
        .iter()
        .find(|d| f(d, "rule") == &Json::str("universal_parameters"))
        .unwrap();
    assert_eq!(f(default, "declaration"), &Json::str(name));
    assert_eq!(
        f(default, "parameters"),
        &Json::Arr(parameters.iter().map(|p| Json::str(*p)).collect())
    );
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
fn assert_family(
    wire: &Json,
    checked: &CheckedInputs,
    id: &str,
    name: &str,
    remaining: &[(&str, Json, Vec<Json>)],
    fixed: &[(&str, Json, Json)],
    all_types: &[(&str, Json)],
    expected_rows: &[Vec<Json>],
    decision: &str,
    exhausted: bool,
) {
    let ns = index(wire);
    let a = answer(wire, id);
    assert_eq!(f(a, "status"), &Json::str(decision));
    let claim = target(&ns, f(a, "claim"), &Json::str("Proposition"));
    assert_eq!(f(claim, "scope"), f(a, "scope"));
    assert_family_selected(
        wire,
        checked,
        id,
        name,
        remaining,
        fixed,
        all_types,
        expected_rows,
        decision,
        exhausted,
        root(wire, id),
        claim,
    );
}
fn assert_family_selected(
    wire: &Json,
    checked: &CheckedInputs,
    id: &str,
    name: &str,
    remaining: &[(&str, Json, Vec<Json>)],
    fixed: &[(&str, Json, Json)],
    all_types: &[(&str, Json)],
    expected_rows: &[Vec<Json>],
    decision: &str,
    exhausted: bool,
    whole_eval: &Json,
    claim: &Json,
) {
    let ns = index(wire);
    assert_eq!(f(f(claim, "judgment"), "status"), &Json::str(decision));
    assert_eq!(f(val(claim), "predicate"), &Json::str("law_holds"));
    let operands = arr(f(val(claim), "operands"));
    assert_eq!(operands.len(), 1);
    let whole = target(&ns, &operands[0], &Json::str("LawInstance"));
    assert_eq!(f(val(whole), "name"), &Json::str(name));
    assert_eq!(f(val(whole), "role"), &Json::str("required"));
    let fixed_types = fixed
        .iter()
        .map(|(n, t, _)| (*n, t.clone()))
        .collect::<Vec<_>>();
    let fixed_values = fixed.iter().map(|(_, _, v)| v.clone()).collect::<Vec<_>>();
    assert_eq!(
        binding_values(wire, f(val(whole), "bindings"), &fixed_types),
        fixed_values
    );
    let source_node = target(&ns, f(val(whole), "body"), &Json::str("Expression"));
    assert_eq!(
        f(val(source_node), "parameters"),
        &Json::Arr(
            remaining
                .iter()
                .map(|(n, t, _)| Json::obj([("name", Json::str(*n)), ("type", t.clone())]))
                .collect()
        )
    );
    assert_eq!(f(val(source_node), "bindings"), f(val(whole), "bindings"));
    let (body, guard) = law_parts(checked, name);
    let body_span = checked.law().exprs[body].span;
    assert_eq!(span(f(val(source_node), "location")), body_span);
    assert_eq!(
        span(f(val(whole), "occurrence")),
        checked.law().declarations[name].span
    );
    if let Some(guard) = guard {
        let expr = target(&ns, f(val(whole), "guard"), &Json::str("Expression"));
        assert_eq!(
            span(f(val(expr), "location")),
            checked.law().exprs[guard].span
        );
        assert_eq!(
            f(val(expr), "parameters"),
            f(val(source_node), "parameters")
        );
    }
    assert_eq!(
        f(claim, "arguments"),
        &Json::Arr(vec![
            operands[0].clone(),
            Json::obj([("node", f(whole_eval, "id").clone())])
        ])
    );
    assert_eq!(f(val(whole_eval), "expression"), f(val(whole), "body"));
    assert_eq!(f(val(whole_eval), "bindings"), f(val(whole), "bindings"));
    assert_eq!(
        f(val(whole_eval), "applicability"),
        &Json::str("applicable")
    );
    assert_eq!(span(f(part(whole_eval), "location")), body_span);
    if decision == "undetermined" {
        assert!(!obj(val(whole_eval)).contains_key("value"));
    } else {
        assert_eq!(
            val(target(&ns, f(val(whole_eval), "value"), &Json::str("Bool"))),
            &Json::Bool(decision == "established")
        );
    }
    let quantifiers = arr(f(val(claim), "quantifiers"));
    assert!(quantifiers.len() >= remaining.len());
    let scope_qs = arr(f(f(claim, "scope"), "quantifiers"));
    assert!(scope_qs.len() >= remaining.len());
    assert_eq!(quantifiers, scope_qs, "freeparameterと内部量化を全件保持");
    for (i, (parameter, t, wanted)) in remaining.iter().enumerate() {
        let q = &quantifiers[i];
        assert_eq!(f(q, "kind"), &Json::str("forall"));
        assert_eq!(f(q, "name"), &Json::str(*parameter));
        assert_eq!(f(q, "type"), t);
        assert_eq!(&scope_qs[i], q);
        let domain = target(&ns, f(q, "domain"), &Json::str("Domain"));
        assert_eq!(f(val(domain), "kind"), &Json::str("finite"));
        assert_eq!(f(val(domain), "type"), t);
        let mut actual = arr(f(val(domain), "elements"))
            .iter()
            .map(|r| member_key(t, val(target(&ns, r, t))))
            .collect::<Vec<_>>();
        actual.sort();
        let mut expected = wanted.iter().map(|v| member_key(t, v)).collect::<Vec<_>>();
        expected.sort();
        assert_eq!(actual, expected, "{name}.{parameter}:元型全域");
    }
    let row_pairs = row_instances_selected(wire, whole_eval, name);
    assert_eq!(row_pairs.len(), expected_rows.len());
    let mut actual_rows = vec![];
    for (instance, evaluation) in &row_pairs {
        assert_eq!(f(val(instance), "role"), &Json::str("required"));
        assert_eq!(
            span(f(val(instance), "occurrence")),
            checked.law().declarations[name].span
        );
        let bindings = f(val(instance), "bindings");
        actual_rows.push(binding_values(wire, bindings, all_types));
        assert_eq!(f(val(evaluation), "bindings"), bindings);
        let body_source = target(&ns, f(val(instance), "body"), &Json::str("Expression"));
        assert!(arr(f(val(body_source), "parameters")).is_empty());
        assert_eq!(f(val(body_source), "bindings"), bindings);
        assert_eq!(span(f(val(body_source), "location")), body_span);
    }
    assert_eq!(
        row_keys(&actual_rows, all_types),
        row_keys(expected_rows, all_types)
    );
    assert_eq!(
        row_keys(&actual_rows, all_types).len(),
        actual_rows.len(),
        "直積rowを欠落/重複しない"
    );
    let product = target(
        &ns,
        &arr(f(whole_eval, "arguments"))[1],
        &Json::str("Domain"),
    );
    let product_type = if remaining.len() == 1 {
        remaining[0].1.clone()
    } else {
        Json::Arr(
            std::iter::once(Json::str("Tuple"))
                .chain(remaining.iter().map(|(_, t, _)| t.clone()))
                .collect(),
        )
    };
    assert_eq!(f(val(product), "type"), &product_type);
    let mut product_values = arr(f(val(product), "elements"))
        .iter()
        .map(|r| member_key(&product_type, val(target(&ns, r, &product_type))))
        .collect::<Vec<_>>();
    product_values.sort();
    let mut expected_product = expected_rows
        .iter()
        .map(|row| {
            let selected = remaining
                .iter()
                .map(|(n, _, _)| {
                    row[all_types.iter().position(|(name, _)| name == n).unwrap()].clone()
                })
                .collect::<Vec<_>>();
            if selected.len() == 1 {
                member_key(&product_type, &selected[0])
            } else {
                Json::Arr(selected).canonical()
            }
        })
        .collect::<Vec<_>>();
    expected_product.sort();
    assert_eq!(product_values, expected_product, "元parameter順の実直積");
    let product_ref = Json::obj([("node", f(product, "id").clone())]);
    let proofs = evidence(&ns, claim, "finite_exhaustion")
        .into_iter()
        .filter(|e| f(f(val(e), "data"), "domain") == &product_ref)
        .collect::<Vec<_>>();
    if exhausted {
        assert_eq!(proofs.len(), 1);
        let proof = f(val(proofs[0]), "data");
        assert_eq!(f(proof, "checked"), &Json::Nat(expected_rows.len() as u64));
        assert_eq!(
            arr(f(proof, "instances"))
                .iter()
                .map(Json::canonical)
                .collect::<BTreeSet<_>>(),
            arr(f(part(whole_eval), "children"))
                .iter()
                .map(Json::canonical)
                .collect::<BTreeSet<_>>()
        );
    } else if decision == "undetermined" {
        assert!(proofs.is_empty());
    }
    assert_universal_request(
        wire,
        id,
        name,
        &remaining.iter().map(|(n, _, _)| *n).collect::<Vec<_>>(),
    );
}

#[test]
fn finite_law_parameters_keep_products_partial_bindings_and_counterexamples() {
    let script = r#"
law required cross(r:E,b:Bool): r=r and (b or not b);
law required equal_pair(p:E,q:E): p=q;
"#;
    let asks = [
        "a=check(Calc.cross)",
        "b=check(Calc.equal_pair)",
        "c=check(Calc.cross,r=@v/item)",
        "d=check(Calc.equal_pair,p=@v/item)",
    ];
    let (wire, checked) = run(fixture(script, Some(false), false, false), &asks);
    assert_eq!(f(&wire, "status"), &Json::str("complete"));
    let e = ty("Ref", Json::str("Roster.E"));
    let refs = vec![reference("v", "item"), reference("w", "item")];
    let bools = vec![Json::Bool(false), Json::Bool(true)];
    let cross = vec![
        vec![refs[0].clone(), bools[0].clone()],
        vec![refs[0].clone(), bools[1].clone()],
        vec![refs[1].clone(), bools[0].clone()],
        vec![refs[1].clone(), bools[1].clone()],
    ];
    let pairs = vec![
        vec![refs[0].clone(), refs[0].clone()],
        vec![refs[0].clone(), refs[1].clone()],
        vec![refs[1].clone(), refs[0].clone()],
        vec![refs[1].clone(), refs[1].clone()],
    ];
    assert_family(
        &wire,
        &checked,
        "a",
        "Calc.cross",
        &[
            ("r", e.clone(), refs.clone()),
            ("b", Json::str("Bool"), bools.clone()),
        ],
        &[],
        &[("r", e.clone()), ("b", Json::str("Bool"))],
        &cross,
        "established",
        true,
    );
    assert_family(
        &wire,
        &checked,
        "b",
        "Calc.equal_pair",
        &[
            ("p", e.clone(), refs.clone()),
            ("q", e.clone(), refs.clone()),
        ],
        &[],
        &[("p", e.clone()), ("q", e.clone())],
        &pairs,
        "refuted",
        false,
    );
    assert_family(
        &wire,
        &checked,
        "c",
        "Calc.cross",
        &[("b", Json::str("Bool"), bools)],
        &[("r", e.clone(), refs[0].clone())],
        &[("r", e.clone()), ("b", Json::str("Bool"))],
        &cross[..2],
        "established",
        true,
    );
    assert_family(
        &wire,
        &checked,
        "d",
        "Calc.equal_pair",
        &[("q", e.clone(), refs.clone())],
        &[("p", e.clone(), refs[0].clone())],
        &[("p", e.clone()), ("q", e.clone())],
        &pairs[..2],
        "refuted",
        false,
    );
    let ns = index(&wire);
    let roster = quantifier_domain(&wire, "a", "r", "forall", &e);
    for node in [
        roster,
        root(&wire, "a"),
        target(
            &ns,
            f(answer(&wire, "a"), "claim"),
            &Json::str("Proposition"),
        ),
    ] {
        assert_eq!(
            f(f(node, "scope"), "snapshots"),
            &Json::Arr(vec![Json::str("v"), Json::str("w"), Json::str("z")])
        );
        assert_eq!(
            f(f(node, "scope"), "modes"),
            &Json::Arr(vec![
                Json::str("observed"),
                Json::str("proposed"),
                Json::str("specification")
            ])
        );
        for snapshot in ["v", "w"] {
            assert!(arr(f(node, "support")).contains(&Json::obj([
                ("snapshot", Json::str(snapshot)),
                ("subject", Json::str("item"))
            ])));
        }
    }
    for id in ["b", "d"] {
        let examples = evidence(&ns, answer(&wire, id), "counterexample");
        assert!(!examples.is_empty());
        let pair = examples
            .iter()
            .find_map(|example| {
                let bindings = f(f(val(example), "data"), "bindings");
                (arr(bindings).len() == 2)
                    .then(|| binding_values(&wire, bindings, &[("p", e.clone()), ("q", e.clone())]))
            })
            .unwrap();
        assert_ne!(pair[0], pair[1]);
        assert!(refs.contains(&pair[0]) && refs.contains(&pair[1]));
        if id == "d" {
            assert_eq!(pair[0], refs[0]);
            assert_eq!(pair[1], refs[1]);
        }
    }
}

#[test]
fn finite_law_parameters_keep_typed_domains_and_empty_products() {
    let script = r#"
law required unit_case(u:Unit): true;
law required fp_case(p:Fp(3)): p=p;
law required tuple_case(p:(Bool,Fp(2))): p=p;
law required option_case(o:Option<Bool>): o=o;
law required set_case(a:Set<Bool>): a=a;
law required data_case(d:Flagged): d=d;
law required empty_case(r:Empty,b:Bool): false;
"#;
    let names = [
        "unit_case",
        "fp_case",
        "tuple_case",
        "option_case",
        "set_case",
        "data_case",
        "empty_case",
    ];
    let asks = names
        .iter()
        .map(|n| format!("{n}=check(Calc.{n})"))
        .collect::<Vec<_>>();
    let (wire, checked) = run(
        fixture(script, Some(false), false, false),
        &asks.iter().map(String::as_str).collect::<Vec<_>>(),
    );
    assert_eq!(f(&wire, "status"), &Json::str("complete"));
    let booleans = vec![Json::Bool(false), Json::Bool(true)];
    let tuple_values = vec![
        Json::Arr(vec![Json::Bool(false), Json::str("0")]),
        Json::Arr(vec![Json::Bool(false), Json::str("1")]),
        Json::Arr(vec![Json::Bool(true), Json::str("0")]),
        Json::Arr(vec![Json::Bool(true), Json::str("1")]),
    ];
    let option_values = vec![
        Json::obj([("none", Json::Bool(true))]),
        Json::obj([("some", Json::Bool(false))]),
        Json::obj([("some", Json::Bool(true))]),
    ];
    let set_values = vec![
        Json::Arr(vec![]),
        Json::Arr(vec![Json::Bool(false)]),
        Json::Arr(vec![Json::Bool(true)]),
        Json::Arr(booleans.clone()),
    ];
    let data_values = vec![
        data("EmptyFlag", vec![]),
        data("Flag", vec![Json::Bool(false)]),
        data("Flag", vec![Json::Bool(true)]),
    ];
    for (name, parameter, t, values) in [
        ("unit_case", "u", Json::str("Unit"), vec![Json::Arr(vec![])]),
        (
            "fp_case",
            "p",
            ty("Fp", Json::str("3")),
            vec![Json::str("0"), Json::str("1"), Json::str("2")],
        ),
        (
            "tuple_case",
            "p",
            Json::Arr(vec![
                Json::str("Tuple"),
                Json::str("Bool"),
                ty("Fp", Json::str("2")),
            ]),
            tuple_values,
        ),
        (
            "option_case",
            "o",
            ty("Option", Json::str("Bool")),
            option_values,
        ),
        ("set_case", "a", ty("Set", Json::str("Bool")), set_values),
        (
            "data_case",
            "d",
            ty("Data", Json::str("Roster.Flagged")),
            data_values,
        ),
    ] {
        let rows = values.iter().map(|v| vec![v.clone()]).collect::<Vec<_>>();
        assert_family(
            &wire,
            &checked,
            name,
            &format!("Calc.{name}"),
            &[(parameter, t.clone(), values)],
            &[],
            &[(parameter, t)],
            &rows,
            "established",
            true,
        );
    }
    let empty = ty("Ref", Json::str("Roster.Empty"));
    assert_family(
        &wire,
        &checked,
        "empty_case",
        "Calc.empty_case",
        &[
            ("r", empty.clone(), vec![]),
            ("b", Json::str("Bool"), booleans),
        ],
        &[],
        &[("r", empty), ("b", Json::str("Bool"))],
        &[],
        "established",
        true,
    );
    let body = declared_body(&checked, "Calc.empty_case");
    assert!(
        evaluations_at(&wire, checked.law().exprs[body].span).is_empty(),
        "空直積で架空body Evaluationを作らない"
    );
}

#[test]
fn finite_law_guards_keep_applicability_and_known_refutations() {
    let script = r#"
law required off(r:E,b:Bool) when false: r.flag and b;
law required mixed(r:E,b:Bool) when b: r=r;
law required fail_active(r:E,b:Bool) when b: not b;
law required unknown_guard(r:E) when r.flag: false;
law required observed(r:E): r.flag;
"#;
    let asks = [
        "a=check(Calc.off)",
        "b=check(Calc.mixed)",
        "c=check(Calc.fail_active)",
        "d=check(Calc.unknown_guard)",
        "e=check(Calc.observed)",
    ];
    let (wire, checked) = run(fixture(script, Some(false), false, false), &asks);
    assert_eq!(
        f(&wire, "status"),
        &Json::str("partial"),
        "{:?}",
        f(&wire, "issues")
    );
    let e = ty("Ref", Json::str("Roster.E"));
    let refs = vec![reference("v", "item"), reference("w", "item")];
    let bools = vec![Json::Bool(false), Json::Bool(true)];
    let cross = vec![
        vec![refs[0].clone(), bools[0].clone()],
        vec![refs[0].clone(), bools[1].clone()],
        vec![refs[1].clone(), bools[0].clone()],
        vec![refs[1].clone(), bools[1].clone()],
    ];
    for (id, name, decision, exhausted) in [
        ("a", "Calc.off", "established", true),
        ("b", "Calc.mixed", "established", true),
        ("c", "Calc.fail_active", "refuted", false),
    ] {
        assert_family(
            &wire,
            &checked,
            id,
            name,
            &[
                ("r", e.clone(), refs.clone()),
                ("b", Json::str("Bool"), bools.clone()),
            ],
            &[],
            &[("r", e.clone()), ("b", Json::str("Bool"))],
            &cross,
            decision,
            exhausted,
        );
    }
    let ns = index(&wire);
    for (instance, row) in row_instances(&wire, "a", "Calc.off") {
        assert_eq!(f(val(row), "applicability"), &Json::str("not_applicable"));
        assert_eq!(
            val(target(&ns, f(val(row), "value"), &Json::str("Bool"))),
            &Json::Bool(true)
        );
        let parts = arr(f(val(row), "parts"));
        assert_eq!(parts.len(), 2);
        assert_eq!(source(&checked, span(f(&parts[0], "location"))), b"false");
        assert_eq!(
            val(target(&ns, f(&parts[0], "value"), &Json::str("Bool"))),
            &Json::Bool(false)
        );
        assert_eq!(
            source(&checked, span(f(&parts[1], "location"))),
            b"r.flag and b"
        );
        assert!(!obj(&parts[1]).contains_key("value"));
        assert!(arr(f(&parts[1], "children")).is_empty());
        let body_ref = f(val(instance), "body");
        assert!(
            !reached(&ns, &[row])
                .iter()
                .map(|id| ns[id.as_str()])
                .any(|n| f(n, "type") == &Json::str("Evaluation")
                    && f(n, "id") != f(row, "id")
                    && f(val(n), "expression") == body_ref),
            "false guard bodyを評価済みにしない"
        );
    }
    for (instance, row) in row_instances(&wire, "b", "Calc.mixed") {
        let bindings = binding_values(
            &wire,
            f(val(instance), "bindings"),
            &[("r", e.clone()), ("b", Json::str("Bool"))],
        );
        assert_eq!(
            f(val(row), "applicability"),
            &Json::str(if bindings[1] == Json::Bool(true) {
                "applicable"
            } else {
                "not_applicable"
            })
        );
    }
    let rows = refs.iter().map(|r| vec![r.clone()]).collect::<Vec<_>>();
    let (original_d, original_d_claim) = retained_observed_family(&wire, "d", "Calc.unknown_guard");
    let (original_e, original_e_claim) = retained_observed_family(&wire, "e", "Calc.observed");
    assert_family_selected(
        &wire,
        &checked,
        "d",
        "Calc.unknown_guard",
        &[("r", e.clone(), refs.clone())],
        &[],
        &[("r", e.clone())],
        &rows,
        "undetermined",
        false,
        original_d,
        original_d_claim,
    );
    assert_family_selected(
        &wire,
        &checked,
        "e",
        "Calc.observed",
        &[("r", e.clone(), refs.clone())],
        &[],
        &[("r", e.clone())],
        &rows,
        "refuted",
        false,
        original_e,
        original_e_claim,
    );
    for id in ["d", "e"] {
        assert_missing(&wire, id, &checked);
        let missing = arr(f(answer(&wire, id), "reasons"))
            .iter()
            .filter(|r| f(r, "code") == &Json::str("missing_observation"))
            .flat_map(|r| arr(f(r, "missing")))
            .collect::<Vec<_>>();
        assert!(missing.iter().any(|m| f(m, "snapshot") == &Json::str("v")
            && f(m, "subject") == &Json::str("item")
            && f(m, "field") == &Json::str("Roster.E.flag")
            && !obj(m).contains_key("atom")));
    }
    let unknown = row_instances_selected(&wire, original_d, "Calc.unknown_guard");
    assert_eq!(unknown.len(), 2);
    for (instance, row) in unknown {
        let bound = binding_values(&wire, f(val(instance), "bindings"), &[("r", e.clone())]);
        assert_eq!(
            f(val(row), "applicability"),
            &Json::str(if bound[0] == refs[0] {
                "undetermined"
            } else {
                "not_applicable"
            })
        );
    }
    let examples = evidence(&ns, original_e_claim, "counterexample");
    assert!(examples.iter().any(|ce| {
        let bs = f(f(val(ce), "data"), "bindings");
        arr(bs).len() == 1
            && binding_values(&wire, bs, &[("r", e.clone())]) == vec![refs[1].clone()]
    }));
    for (id, name) in [("d", "Calc.unknown_guard"), ("e", "Calc.observed")] {
        let aggregate = root(&wire, id);
        assert_eq!(
            f(f(aggregate, "scope"), "domain"),
            &Json::str("all_completions")
        );
        let domain_ref = &arr(f(aggregate, "arguments"))[1];
        let domain = target(&ns, domain_ref, &Json::str("Domain"));
        assert_eq!(f(val(domain), "kind"), &Json::str("finite"));
        assert_eq!(f(val(domain), "type"), &Json::str("Bool"));
        let members = arr(f(val(domain), "elements"));
        assert_eq!(members.len(), 2);
        assert_eq!(
            members
                .iter()
                .map(|r| val(target(&ns, r, &Json::str("Bool"))).canonical())
                .collect::<BTreeSet<_>>(),
            BTreeSet::from([Json::Bool(false).canonical(), Json::Bool(true).canonical()])
        );
        let cases = children(&ns, aggregate);
        assert_eq!(cases.len(), 2);
        let propositions = arr(f(aggregate, "arguments"))
            .iter()
            .map(|r| ns[text(f(r, "node"))])
            .filter(|n| f(n, "type") == &Json::str("Proposition"))
            .collect::<Vec<_>>();
        assert_eq!(propositions.len(), 2);
        let mut used = BTreeSet::new();
        let mut matched = BTreeSet::new();
        for case in cases {
            let whole = aggregate_instance(&ns, case).expect("補完内の実Ref全域Law族");
            assert_eq!(f(val(whole), "name"), &Json::str(name));
            let body = target(&ns, f(val(whole), "body"), &Json::str("Expression"));
            let selected = arr(f(body, "arguments"))
                .iter()
                .filter(|r| members.contains(r))
                .collect::<Vec<_>>();
            assert_eq!(selected.len(), 1);
            assert!(used.insert(selected[0].canonical()));
            let Json::Bool(h) = val(target(&ns, selected[0], &Json::str("Bool"))) else {
                panic!("Bool代入")
            };
            let case_ref = Json::obj([("node", f(case, "id").clone())]);
            let claims = propositions
                .iter()
                .copied()
                .filter(|p| arr(f(p, "arguments")).get(1) == Some(&case_ref))
                .collect::<Vec<_>>();
            assert_eq!(claims.len(), 1);
            assert!(matched.insert(text(f(claims[0], "id"))));
            let decision = if id == "d" && !h {
                "established"
            } else {
                "refuted"
            };
            assert_family_selected(
                &wire,
                &checked,
                id,
                name,
                &[("r", e.clone(), refs.clone())],
                &[],
                &[("r", e.clone())],
                &rows,
                decision,
                decision == "established",
                case,
                claims[0],
            );
            if id == "e" {
                let examples = evidence(&ns, claims[0], "counterexample");
                assert!(
                    examples.iter().any(|ce| {
                        let data = f(val(ce), "data");
                        binding_values(&wire, f(data, "bindings"), &[("r", e.clone())])
                            == vec![refs[1].clone()]
                            && arr(f(data, "facts")).iter().any(|fact| {
                                f(fact, "snapshot") == &Json::str("w")
                                    && f(fact, "subject") == &Json::str("item")
                                    && obj(fact).get("atom") == Some(&Json::str("flag"))
                            })
                            && val(target(&ns, f(data, "left"), &Json::str("Bool")))
                                == &Json::Bool(false)
                            && val(target(&ns, f(data, "right"), &Json::str("Bool")))
                                == &Json::Bool(true)
                    }),
                    "各補完も元w.flag=falseの実反例を保持"
                );
            }
        }
        assert_eq!(used.len(), 2);
        assert_eq!(matched.len(), 2);
        if id == "d" {
            check_claim(&wire, id, "undetermined");
            assert!(!obj(val(aggregate)).contains_key("value"));
            let pairs = evidence(&ns, answer(&wire, id), "completion_pair");
            assert_eq!(pairs.len(), 1);
            let pair = f(val(pairs[0]), "data");
            assert_eq!(
                f(pair, "fields"),
                &Json::Arr(vec![Json::obj([
                    ("snapshot", Json::str("v")),
                    ("subject", Json::str("item")),
                    ("field", Json::str("Roster.E.flag"))
                ])])
            );
            let mut values = BTreeSet::new();
            for (assignment_key, result_key) in
                [("first", "first_result"), ("second", "second_result")]
            {
                let assignment = arr(f(pair, assignment_key));
                assert_eq!(assignment.len(), 1);
                let h = val(target(&ns, &assignment[0], &Json::str("Bool")));
                let Json::Bool(h) = h else { panic!("Bool") };
                assert!(values.insert(*h));
                assert!(arr(f(part(aggregate), "children")).contains(f(pair, result_key)));
                let case = target(&ns, f(pair, result_key), &Json::str("Evaluation"));
                let body = expression(&ns, case);
                assert!(
                    arr(f(body, "arguments")).contains(&assignment[0]),
                    "補完対代入はその実whole caseに属する"
                );
                assert_eq!(
                    val(target(&ns, f(val(case), "value"), &Json::str("Bool"))),
                    &Json::Bool(!h)
                );
            }
            assert_eq!(values, BTreeSet::from([false, true]));
        } else {
            check_claim(&wire, id, "refuted");
            assert_eq!(
                val(target(&ns, f(val(aggregate), "value"), &Json::str("Bool"))),
                &Json::Bool(false)
            );
            let claim = target(
                &ns,
                f(answer(&wire, id), "claim"),
                &Json::str("Proposition"),
            );
            let proofs = arr(f(claim, "evidence"))
                .iter()
                .map(|r| target(&ns, r, &Json::str("Evidence")))
                .collect::<Vec<_>>();
            assert_eq!(proofs.len(), 1);
            assert_eq!(f(val(proofs[0]), "kind"), &Json::str("finite_exhaustion"));
            let proof = f(val(proofs[0]), "data");
            assert_eq!(f(proof, "domain"), domain_ref);
            assert_eq!(f(proof, "checked"), &Json::Nat(2));
            assert_eq!(f(proof, "instances"), f(part(aggregate), "children"));
        }
    }
}

fn nested_sources_fixture(moved: bool) -> InputSources {
    let script = r#"
view helper(s:E,b:Bool): Bool = let held=s in match MaybeAt.At(held) { NoRef => false; At(x) => x=s and (b or not b); };
view echo(s:E): E = let held=s in match MaybeAt.At(held) { NoRef => s; At(x) => x; };
law required nested(s:E,b:Bool): (forall z in list<E>[s] . helper(z,b)) and (forall u:Unit . true);
law required bound(s:E): helper(s,true);
"#;
    fixture(script, Some(false), false, moved)
}

#[test]
fn finite_law_instances_preserve_nested_sources_and_parent_bindings() {
    let asks = ["a=check(Calc.nested)", "b=check(Calc.nested)"];
    let (wire, checked) = run(nested_sources_fixture(false), &asks);
    assert_eq!(f(&wire, "status"), &Json::str("complete"));
    let e = ty("Ref", Json::str("Roster.E"));
    let refs = vec![reference("v", "item"), reference("w", "item")];
    let bools = vec![Json::Bool(false), Json::Bool(true)];
    let rows = vec![
        vec![refs[0].clone(), bools[0].clone()],
        vec![refs[0].clone(), bools[1].clone()],
        vec![refs[1].clone(), bools[0].clone()],
        vec![refs[1].clone(), bools[1].clone()],
    ];
    for id in ["a", "b"] {
        assert_family(
            &wire,
            &checked,
            id,
            "Calc.nested",
            &[
                ("s", e.clone(), refs.clone()),
                ("b", Json::str("Bool"), bools.clone()),
            ],
            &[],
            &[("s", e.clone()), ("b", Json::str("Bool"))],
            &rows,
            "established",
            true,
        );
    }
    let ns = index(&wire);
    assert_ne!(
        f(root(&wire, "a"), "id"),
        f(root(&wire, "b"), "id"),
        "別Requestの元Law適用を保持"
    );
    let qs = arr(f(f(answer(&wire, "a"), "scope"), "quantifiers"));
    assert_eq!(text(f(&qs[0], "name")), "s");
    assert_eq!(text(f(&qs[1], "name")), "b");
    assert!(
        qs.iter()
            .skip(2)
            .all(|q| ["z", "u"].contains(&text(f(q, "name"))))
    );
    assert!(qs.iter().any(|q| f(q, "name") == &Json::str("z")));
    assert!(qs.iter().any(|q| f(q, "name") == &Json::str("u")));
    for (instance, row) in row_instances(&wire, "a", "Calc.nested") {
        let bindings = binding_values(
            &wire,
            f(val(instance), "bindings"),
            &[("s", e.clone()), ("b", Json::str("Bool"))],
        );
        let reachable = reached(&ns, &[row]);
        let collections = reachable
            .iter()
            .map(|id| ns[id.as_str()])
            .filter(|n| {
                f(n, "type") == &Json::str("Evaluation")
                    && aggregate_instance(&ns, n).is_none()
                    && source(&checked, evaluation_span(&ns, n)) == b"list<E>[s]"
            })
            .collect::<Vec<_>>();
        assert_eq!(collections.len(), 1);
        assert_eq!(
            val(target(
                &ns,
                f(val(collections[0]), "value"),
                &ty("List", e.clone())
            )),
            &Json::Arr(vec![bindings[0].clone()])
        );
        let calls = reachable
            .iter()
            .map(|id| ns[id.as_str()])
            .filter(|n| {
                f(n, "type") == &Json::str("Evaluation")
                    && aggregate_instance(&ns, n).is_none()
                    && source(&checked, evaluation_span(&ns, n)) == b"helper(z,b)"
            })
            .collect::<Vec<_>>();
        assert_eq!(calls.len(), 1);
        assert_eq!(
            val(target(&ns, f(val(calls[0]), "value"), &Json::str("Bool"))),
            &Json::Bool(true)
        );
        assert_eq!(
            binding_values(
                &wire,
                f(val(calls[0]), "bindings"),
                &[("s", e.clone()), ("b", Json::str("Bool"))]
            ),
            bindings
        );
    }
}

#[test]
fn finite_law_instances_preserve_nested_sources_with_explicit_subject_binding() {
    let (wire, checked) = run(
        nested_sources_fixture(false),
        &["c=check(Calc.nested,s=@v/item)"],
    );
    assert_eq!(f(&wire, "status"), &Json::str("complete"));
    let e = ty("Ref", Json::str("Roster.E"));
    let refs = vec![reference("v", "item"), reference("w", "item")];
    let bools = vec![Json::Bool(false), Json::Bool(true)];
    let rows = vec![
        vec![refs[0].clone(), bools[0].clone()],
        vec![refs[0].clone(), bools[1].clone()],
        vec![refs[1].clone(), bools[0].clone()],
        vec![refs[1].clone(), bools[1].clone()],
    ];
    assert_family(
        &wire,
        &checked,
        "c",
        "Calc.nested",
        &[("b", Json::str("Bool"), bools)],
        &[("s", e.clone(), refs[0].clone())],
        &[("s", e.clone()), ("b", Json::str("Bool"))],
        &rows[..2],
        "established",
        true,
    );
}

#[test]
fn finite_law_instances_preserve_bound_call_parent_binding() {
    let (wire, _) = run(
        nested_sources_fixture(false),
        &["d=check(Calc.bound,s=@v/item)"],
    );
    assert_eq!(f(&wire, "status"), &Json::str("complete"));
    let e = ty("Ref", Json::str("Roster.E"));
    let refs = vec![reference("v", "item"), reference("w", "item")];
    check_claim(&wire, "d", "established");
    let request = arr(f(&wire, "requests"))
        .iter()
        .find(|r| f(r, "id") == &Json::str("d"))
        .unwrap();
    assert!(
        arr(f(request, "defaults"))
            .iter()
            .all(|d| f(d, "rule") != &Json::str("universal_parameters"))
    );
    let explicit = instance_for_eval(&wire, "d", "Calc.bound", root(&wire, "d"));
    assert_eq!(
        binding_values(&wire, f(val(explicit), "bindings"), &[("s", e.clone())]),
        vec![refs[0].clone()]
    );
}

#[test]
fn finite_law_instances_preserve_nested_view_return() {
    let (wire, _) = run(
        nested_sources_fixture(false),
        &["e=evaluate(Calc.echo,s=@w/item)"],
    );
    assert_eq!(f(&wire, "status"), &Json::str("complete"));
    let e = ty("Ref", Json::str("Roster.E"));
    let refs = vec![reference("v", "item"), reference("w", "item")];
    output(&wire, "e", &e, refs[1].clone());
}

#[test]
fn finite_law_instances_preserve_nested_sources_after_provenance_relocation() {
    let (moved, moved_checked) = run(nested_sources_fixture(true), &["a=check(Calc.nested)"]);
    check_claim(&moved, "a", "established");
    assert_eq!(moved_checked.archmap().sources[0].revision, "r2");
    assert!(
        moved_checked
            .archmap()
            .origins
            .iter()
            .all(|o| o.id.ends_with("_moved"))
    );
}

fn assert_missing(wire: &Json, id: &str, checked: &CheckedInputs) {
    let ns = index(wire);
    let missing = arr(f(answer(wire, id), "reasons"))
        .iter()
        .filter(|r| f(r, "code") == &Json::str("missing_observation"))
        .collect::<Vec<_>>();
    assert!(!missing.is_empty());
    for reason in missing {
        assert!(
            arr(f(reason, "missing"))
                .iter()
                .any(|m| f(m, "snapshot") == &Json::str("v")
                    && f(m, "subject") == &Json::str("item")
                    && f(m, "field") == &Json::str("Roster.E.flag")
                    && !obj(m).contains_key("atom"))
        );
        let deps = arr(f(reason, "dependencies"));
        assert!(!deps.is_empty());
        for dep in deps {
            let expression = target(&ns, dep, &Json::str("Expression"));
            let bytes = source(checked, span(f(val(expression), "location")));
            assert!(bytes == b"r.flag" || bytes == b"s.flag");
        }
    }
}

#[test]
fn finite_law_parameter_stops_keep_completed_prefixes() {
    let input = fixture(
        r#"
view seed(s:E): Unit = unit;
view absent(s:E): Bool = s.flag;
law required observed(r:E): r.flag;
law required current(b:Bool): true;
view later(s:E): Unit = unit;
"#,
        Some(false),
        false,
        false,
    );
    let checked = check_inputs(input.clone(), &mut quiet()).unwrap();
    let asks = [
        "seed=evaluate(Calc.seed,s=@v/item)",
        "absent=evaluate(Calc.absent,s=@v/item)",
        "observed=check(Calc.observed)",
        "current=check(Calc.current)",
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
    check_claim(&prior, "observed", "refuted");
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
    check_claim(&baseline, "current", "established");
    assert_eq!(
        total.get() - count.get(),
        4,
        "2実instanceのbody Expression pre/post"
    );
    let ns = index(&baseline);
    let baseline_rows = row_instances(&baseline, "current", "Calc.current");
    assert_eq!(baseline_rows.len(), 2);
    let body_span = checked.law().exprs[declared_body(&checked, "Calc.current")].span;
    assert!(!evidence(&ns, answer(&baseline, "current"), "finite_exhaustion").is_empty());
    // 固定Expression pre/postだけを注入。実直積/適用/集約証拠/再検査内部はprivate試験が担う。
    for (offset, kind, done_bodies, done_rows) in [(1, 0, 0, 0), (3, 1, 1, 1), (4, 2, 2, 1)] {
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
        check_claim(&wire, "observed", "refuted");
        for id in ["absent", "observed"] {
            for key in ["status", "outputs", "scope", "reasons", "evidence"] {
                assert_eq!(f(answer(&wire, id), key), f(answer(&prior, id), key));
            }
        }
        let ns = index(&wire);
        assert_eq!(
            evidence(&ns, answer(&wire, "observed"), "counterexample"),
            evidence(&index(&prior), answer(&prior, "observed"), "counterexample")
        );
        for id in ["current", "later"] {
            let a = answer(&wire, id);
            assert_eq!(f(a, "status"), &Json::str("undetermined"));
            assert!(!obj(a).contains_key("claim"));
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
        let body_evals = evaluations_at(&wire, body_span);
        assert_eq!(body_evals.len(), done_bodies);
        for body in body_evals {
            assert_eq!(
                val(target(&ns, f(val(body), "value"), &Json::str("Bool"))),
                &Json::Bool(true)
            );
            assert!(arr(f(body, "support")).is_empty());
        }
        let instances = arr(f(&wire, "nodes"))
            .iter()
            .filter(|n| {
                f(n, "type") == &Json::str("LawInstance")
                    && f(val(n), "name") == &Json::str("Calc.current")
                    && arr(f(val(n), "bindings")).len() == 1
            })
            .collect::<Vec<_>>();
        // 完成したrow適用だけを数え、停止中のrowのSource/値は未完として保持できる。
        let row_evals = instances
            .iter()
            .map(|instance| {
                let row = target(
                    &ns,
                    &arr(f(instance, "arguments"))[0],
                    &Json::str("Evaluation"),
                );
                assert_eq!(f(val(instance), "body"), f(val(row), "expression"));
                assert_eq!(f(val(instance), "bindings"), f(val(row), "bindings"));
                row
            })
            .collect::<Vec<_>>();
        assert_eq!(row_evals.len(), done_rows);
        let whole = arr(f(&wire, "nodes"))
            .iter()
            .filter(|n| {
                f(n, "type") == &Json::str("LawInstance")
                    && f(val(n), "name") == &Json::str("Calc.current")
                    && arr(f(val(n), "bindings")).is_empty()
            })
            .collect::<Vec<_>>();
        assert!(
            !arr(f(&wire, "nodes"))
                .iter()
                .any(|n| f(n, "type") == &Json::str("Proposition")
                    && arr(f(val(n), "operands"))
                        .iter()
                        .any(|r| whole.iter().any(|w| f(w, "id") == f(r, "node")))),
            "未完成wholeを命題判断へ昇格しない"
        );
        let products = arr(f(&wire, "nodes"))
            .iter()
            .filter(|n| {
                f(n, "type") == &Json::str("Domain")
                    && arr(f(n, "arguments")).iter().any(|r| {
                        let source = ns[text(f(r, "node"))];
                        f(source, "type") == &Json::str("Expression")
                            && span(f(val(source), "location")) == body_span
                            && f(val(source), "parameters")
                                == &Json::Arr(vec![Json::obj([
                                    ("name", Json::str("b")),
                                    ("type", Json::str("Bool")),
                                ])])
                    })
            })
            .collect::<Vec<_>>();
        assert_eq!(
            products.len(),
            1,
            "型と元自由parameter Sourceから実Bool直積を特定"
        );
        for product in products {
            assert_eq!(f(val(product), "type"), &Json::str("Bool"));
            assert_eq!(
                arr(f(val(product), "elements"))
                    .iter()
                    .map(|r| val(target(&ns, r, &Json::str("Bool"))).canonical())
                    .collect::<BTreeSet<_>>(),
                BTreeSet::from([Json::Bool(false).canonical(), Json::Bool(true).canonical()])
            );
            let product_ref = Json::obj([("node", f(product, "id").clone())]);
            assert!(
                !arr(f(&wire, "nodes"))
                    .iter()
                    .any(|n| f(n, "type") == &Json::str("Evidence")
                        && f(val(n), "kind") == &Json::str("finite_exhaustion")
                        && f(f(val(n), "data"), "domain") == &product_ref)
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
        assert_eq!(probes.get(), before);
    }
}
