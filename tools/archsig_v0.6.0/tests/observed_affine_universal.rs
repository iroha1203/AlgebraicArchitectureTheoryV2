//! Z/Q 全域parameterと欠測Factの補完を区別し、元式への導出を三入力から検査する。
mod common;
use archsig::{
    archmap::Slot,
    canonical::Json,
    definition::check_definitions_controlled,
    law::{ast::ExprKind, model::Signature},
    observed::{
        control::{Control, Limits, Usage},
        evaluate_observed_bytes,
        input::{CheckedInputs, InputSources, check_inputs},
    },
};
use std::collections::{BTreeMap, BTreeSet};

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
fn index(wire: &Json) -> BTreeMap<&str, &Json> {
    arr(f(wire, "nodes"))
        .iter()
        .map(|n| (text(f(n, "id")), n))
        .collect()
}
fn target<'a>(ns: &BTreeMap<&str, &'a Json>, reference: &Json, ty: &str) -> &'a Json {
    assert_eq!(obj(reference).len(), 1);
    let n = ns[text(f(reference, "node"))];
    assert_eq!(f(n, "type"), &Json::str(ty));
    n
}
fn typed<'a>(ns: &BTreeMap<&str, &'a Json>, reference: &Json, ty: &Json) -> &'a Json {
    assert_eq!(obj(reference).len(), 1);
    let n = ns[text(f(reference, "node"))];
    assert_eq!(f(n, "type"), ty);
    n
}
fn reference(node: &Json) -> Json {
    Json::obj([("node", f(node, "id").clone())])
}
fn answer<'a>(wire: &'a Json, id: &str) -> &'a Json {
    arr(f(wire, "answers"))
        .iter()
        .find(|a| f(a, "id") == &Json::str(id))
        .unwrap()
}
fn root<'a>(wire: &'a Json, id: &str) -> &'a Json {
    target(
        &index(wire),
        f(f(answer(wire, id), "outputs"), "evaluation"),
        "Evaluation",
    )
}
fn refs(j: &Json, out: &mut Vec<String>) {
    match j {
        Json::Obj(m) if m.len() == 1 && m.contains_key("node") => out.push(text(&m["node"]).into()),
        Json::Obj(m) => {
            for v in m.values() {
                refs(v, out);
            }
        }
        Json::Arr(a) => {
            for v in a {
                refs(v, out);
            }
        }
        _ => {}
    }
}
fn reachable<'a>(wire: &'a Json, root: &Json) -> Vec<&'a Json> {
    let ns = index(wire);
    let mut pending = vec![];
    refs(root, &mut pending);
    let mut seen = BTreeSet::new();
    while let Some(id) = pending.pop() {
        if seen.insert(id.clone()) {
            refs(ns[id.as_str()], &mut pending);
        }
    }
    arr(f(wire, "nodes"))
        .iter()
        .filter(|n| seen.contains(text(f(n, "id"))))
        .collect()
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
fn source(checked: &CheckedInputs, position: (usize, usize)) -> &[u8] {
    &checked.sources().law().bytes()[position.0..position.1]
}
fn expression<'a>(ns: &BTreeMap<&str, &'a Json>, evaluation: &Json) -> &'a Json {
    target(ns, f(val(evaluation), "expression"), "Expression")
}
fn q(n: &str, d: &str) -> Json {
    Json::Arr(vec![Json::str(n), Json::str(d)])
}
fn numeric(ty: &str, value: &str) -> Json {
    if ty == "Q" {
        q(value, "1")
    } else {
        Json::str(value)
    }
}
fn fact(field: &str) -> Json {
    Json::obj([
        ("snapshot", Json::str("v")),
        ("subject", Json::str("item")),
        ("field", Json::str(format!("Universal.Sample.{field}"))),
    ])
}
fn parameter(name: &str, ty: &str) -> Json {
    Json::obj([("name", Json::str(name)), ("type", Json::str(ty))])
}

fn fixture(script: &str, missing_bool: bool, moved: bool) -> InputSources {
    use common::{definition_json, entity_json, field_json, vocabulary_json};
    let root = entity_json("Universal.Root", "[]", "[]");
    let fields = [
        ("z", "Z"),
        ("k", "Z"),
        ("q", "Q"),
        ("p", "Bool"),
        ("knownz", "Z"),
        ("knownq", "Q"),
    ]
    .iter()
    .map(|(name, ty)| field_json(name, &Json::str(*ty).canonical()))
    .collect::<Vec<_>>()
    .join(",");
    let sample = entity_json(
        "Universal.Sample",
        &format!("[{}]", field_json("owner", r#"["Ref","Universal.Root"]"#)),
        &format!("[{fields}]"),
    );
    let definition = definition_json(&format!(
        "[{}]",
        vocabulary_json("Universal", &format!("[{root},{sample}]"), "[]")
    ));
    let checked =
        check_definitions_controlled(&[("definition0", definition.as_bytes())], &mut quiet())
            .unwrap();
    let digest = &checked.vocabularies["Universal"].digest;
    let law = format!(
        r#"law "archsig.law/2" semantics "archsig/0.6.0"; reading Calc {{ use vocabulary Universal version "1" digest "{digest}"; {script} }}"#
    );
    let suffix = if moved { "_moved" } else { "" };
    let shift = if moved { 10 } else { 0 };
    let uri = if moved {
        "urn:fixture:affine-universal:relocated"
    } else {
        "urn:fixture:affine-universal"
    };
    let revision = if moved { "r2" } else { "r1" };
    let origins=[("snapshot",0),("subjects",2),("values",4)].iter().map(|(kind,start)|format!(r#"{{"id":"{kind}{suffix}","mode":"specification","method":"小さい全域式の入力。","locations":[{{"source":"scan{suffix}","path":"{kind}.model","span":[{},{}]}}]}}"#,start+shift,start+shift+1)).collect::<Vec<_>>().join(",");
    let mut atoms = vec![];
    for (name, value) in [
        ("owner", Json::Arr(vec![Json::str("v"), Json::str("root")])),
        ("p", Json::Bool(false)),
        ("knownz", Json::str("7")),
        ("knownq", q("1", "2")),
    ] {
        if name == "p" && missing_bool {
            continue;
        }
        atoms.push(format!(r#"{{"id":"{name}","subject":"item","field":"Universal.Sample.{name}","value":{},"origin":"values{suffix}"}}"#,value.canonical()));
    }
    let map = format!(
        r#"{{"format":"archsig.archmap/2","semantics":"archsig/0.6.0","vocabularies":[{{"namespace":"Universal","version":"1","digest":"{digest}"}}],"sources":[{{"id":"scan{suffix}","uri":"{uri}","revision":"{revision}","digest":"sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"}}],"origins":[{origins}],"snapshots":[{{"id":"v","origin":"snapshot{suffix}","subjects":[{{"id":"root","type":"Universal.Root","origin":"subjects{suffix}"}},{{"id":"item","type":"Universal.Sample","origin":"subjects{suffix}"}}],"atoms":[{}]}}]}}"#,
        atoms.join(",")
    );
    InputSources::from_bytes(
        vec![definition.into_bytes()],
        law.into_bytes(),
        map.into_bytes(),
    )
}
fn run(inputs: InputSources, asks: &[&str]) -> (Json, CheckedInputs) {
    let checked = check_inputs(inputs.clone(), &mut quiet())
        .unwrap_or_else(|e| panic!("入力: {:?}", e.issues()));
    let evaluated =
        evaluate_observed_bytes(inputs.clone(), asks, &mut quiet()).unwrap_or_else(|e| {
            if let Some(wire) = e.wire() {
                panic!("評価: {:?}", f(&wire, "issues"));
            }
            panic!("評価: {e:?}");
        });
    let after = evaluated.prepared().inputs();
    assert_eq!(after.sources(), &inputs);
    assert_eq!(
        after.archmap().snapshots,
        checked.archmap().snapshots,
        "代入値・補完値で観測、owner、既知値を変更しない"
    );
    assert_eq!(after.archmap().bytes_digest, checked.archmap().bytes_digest);
    assert_eq!(after.archmap().model_digest, checked.archmap().model_digest);
    assert_eq!(
        after.definitions().vocabularies,
        checked.definitions().vocabularies
    );
    assert_eq!(after.law().declarations, checked.law().declarations);
    let wire = evaluated.wire();
    assert_ne!(
        f(&wire, "status"),
        &Json::str("error"),
        "評価wireのエラー: {:?}",
        f(&wire, "issues")
    );
    audit(&wire, &checked);
    (wire, checked)
}
fn audit(wire: &Json, checked: &CheckedInputs) {
    let ns = index(wire);
    let mut earlier = BTreeSet::new();
    for n in arr(f(wire, "nodes")) {
        let mut edges = vec![];
        refs(n, &mut edges);
        for edge in edges {
            assert!(earlier.contains(edge.as_str()), "既出Ref: {edge}");
        }
        assert!(earlier.insert(text(f(n, "id"))));
        if f(n, "type") != &Json::str("Proposition") {
            assert!(!obj(n).contains_key("judgment"));
        }
        if let Some(payload) = obj(n).get("value") {
            let mut edges = vec![];
            refs(payload, &mut edges);
            for edge in edges {
                assert_ne!(f(ns[edge.as_str()], "state"), &Json::str("blocked"));
                assert!(!obj(ns[edge.as_str()]).contains_key("partial"));
            }
        }
        for support in arr(f(n, "support")) {
            audit_fact(support, n, checked);
        }
        if f(n, "type") == &Json::str("Domain") {
            let kind = f(val(n), "kind");
            if [Json::str("Z"), Json::str("Q")].contains(f(val(n), "type")) {
                assert_eq!(
                    kind,
                    &Json::str("type"),
                    "零/単位代入をZ/Q全域の有限列挙としない"
                );
                assert!(!obj(val(n)).contains_key("elements"));
            }
            if kind == &Json::str("finite") {
                for member in arr(f(val(n), "elements")) {
                    val(typed(&ns, member, f(val(n), "type")));
                }
            }
        }
        if f(n, "type") == &Json::str("Expression") && f(val(n), "kind") == &Json::str("source") {
            let position = span(f(val(n), "location"));
            assert!(position.0 < position.1 && position.1 <= checked.sources().law().bytes().len());
            assert_eq!(span(f(f(n, "rule"), "location")), position);
            let parameters = arr(f(val(n), "parameters"));
            let mut names = BTreeSet::new();
            for p in parameters {
                assert!(names.insert(text(f(p, "name"))));
                assert!([Json::str("Z"), Json::str("Q"), Json::str("Bool")].contains(f(p, "type")));
            }
            for b in arr(f(val(n), "bindings")) {
                assert!(
                    !parameters.iter().any(|p| f(p, "name") == f(b, "name")),
                    "自由parameterを通常Bindingへ入れない"
                );
            }
        }
        if f(n, "type") == &Json::str("Evaluation") {
            let expr = expression(&ns, n);
            for binding in arr(f(val(n), "bindings")) {
                let scalar = ns[text(f(f(binding, "value"), "node"))];
                val(scalar);
                let mut expected = checked
                    .law()
                    .declarations
                    .values()
                    .filter_map(|d| match &d.signature {
                        Signature::View { params, .. } | Signature::Law { params, .. } => {
                            Some(params)
                        }
                        _ => None,
                    })
                    .flatten()
                    .filter(|p| p.name == text(f(binding, "name")))
                    .map(|p| p.ty.wire())
                    .collect::<Vec<_>>();
                for ast in &checked.law().exprs {
                    use archsig::law::ast::{Builtin, QuantDomain, QuantSplit, TypeAst};
                    if let ExprKind::Quant {
                        var,
                        split:
                            QuantSplit::Fixed {
                                domain: QuantDomain::Type(TypeAst::Builtin(kind, _)),
                                ..
                            },
                        ..
                    } = &ast.kind
                    {
                        if var.name == text(f(binding, "name")) {
                            match kind {
                                Builtin::Z => expected.push(Json::str("Z")),
                                Builtin::Q => expected.push(Json::str("Q")),
                                _ => {}
                            }
                        }
                    }
                }
                assert!(
                    expected.contains(f(scalar, "type")),
                    "元binder型の通常値だけをBindingへ入れる"
                );
            }
            if f(val(expr), "kind") == &Json::str("source") {
                let position = span(f(val(expr), "location"));
                if let Some((id, _)) = checked
                    .law()
                    .exprs
                    .iter()
                    .enumerate()
                    .find(|(_, e)| e.span == position)
                {
                    if let Some(value) = obj(val(n)).get("value") {
                        typed(&ns, value, &checked.law().expr_type(id).unwrap().wire());
                    }
                }
            }
            for part in arr(f(val(n), "parts")) {
                for child in arr(f(part, "children")) {
                    let child = target(&ns, child, "Evaluation");
                    for support in arr(f(child, "support")) {
                        assert!(arr(f(n, "support")).contains(support));
                    }
                }
            }
        }
    }
    for a in arr(f(wire, "answers")) {
        if let Some(claim) = obj(a).get("claim") {
            let claim = target(&ns, claim, "Proposition");
            assert_eq!(f(f(claim, "judgment"), "status"), f(a, "status"));
            assert_eq!(f(claim, "scope"), f(a, "scope"));
        }
        for reason in arr(f(a, "reasons"))
            .iter()
            .filter(|r| f(r, "code") == &Json::str("missing_observation"))
        {
            assert!(!arr(f(reason, "dependencies")).is_empty());
            for dependency in arr(f(reason, "dependencies")) {
                target(&ns, dependency, "Expression");
            }
            for missing in arr(f(reason, "missing")) {
                assert!(!obj(missing).contains_key("atom"));
                assert_eq!(f(missing, "snapshot"), &Json::str("v"));
                assert_eq!(f(missing, "subject"), &Json::str("item"));
                let subject = checked.archmap().snapshots[0]
                    .subjects
                    .iter()
                    .find(|s| s.id == "item")
                    .unwrap();
                assert!(matches!(
                    subject
                        .fields
                        .iter()
                        .find(|s| s.name == text(f(missing, "field")))
                        .unwrap()
                        .slot,
                    Slot::Missing
                ));
            }
        }
    }
}
fn audit_fact(support: &Json, node: &Json, checked: &CheckedInputs) {
    assert_eq!(f(support, "snapshot"), &Json::str("v"));
    assert!(arr(f(f(node, "scope"), "snapshots")).contains(&Json::str("v")));
    assert!(arr(f(f(node, "scope"), "modes")).contains(&Json::str("specification")));
    let subject = checked.archmap().snapshots[0]
        .subjects
        .iter()
        .find(|s| s.id == text(f(support, "subject")))
        .unwrap();
    let (origin_id, kind, start) = if let Some(field) = obj(support).get("field") {
        let slot = &subject
            .fields
            .iter()
            .find(|s| s.name == text(field))
            .unwrap()
            .slot;
        let Slot::Known { atom, origin, .. } = slot else {
            panic!("欠測を支持Atomにしない")
        };
        assert_eq!(f(support, "atom"), &Json::str(atom));
        (origin, "values", 4)
    } else {
        assert!(!obj(support).contains_key("atom"));
        (&subject.origin, "subjects", 2)
    };
    let origin = checked
        .archmap()
        .origins
        .iter()
        .find(|o| &o.id == origin_id)
        .unwrap();
    assert_eq!(origin.mode, archsig::archmap::Mode::Specification);
    let location = &origin.locations[0];
    let source = checked
        .archmap()
        .sources
        .iter()
        .find(|s| s.id == location.source)
        .unwrap();
    let shift = if source.revision == "r2" { 10 } else { 0 };
    assert_eq!(location.path, format!("{kind}.model"));
    assert_eq!(location.span, Some((start + shift, start + shift + 1)));
    assert_eq!(
        source.uri,
        if shift == 0 {
            "urn:fixture:affine-universal"
        } else {
            "urn:fixture:affine-universal:relocated"
        }
    );
    assert_eq!(origin.id.ends_with("_moved"), shift == 10);
    assert_eq!(source.id, if shift == 0 { "scan" } else { "scan_moved" });
}
fn missing(wire: &Json, id: &str, fields: &[&str]) {
    let actual = arr(f(answer(wire, id), "reasons"))
        .iter()
        .filter(|r| f(r, "code") == &Json::str("missing_observation"))
        .flat_map(|r| arr(f(r, "missing")))
        .map(Json::canonical)
        .collect::<BTreeSet<_>>();
    assert_eq!(
        actual,
        fields.iter().map(|field| fact(field).canonical()).collect(),
        "parameterは欠測Factでない"
    );
}
fn missing_occurrences(wire: &Json, checked: &CheckedInputs, id: &str, field: &str, count: usize) {
    let ns = index(wire);
    let original = root(wire, id);
    let subject = Json::obj([("snapshot", Json::str("v")), ("subject", Json::str("item"))]);
    assert!(arr(f(original, "support")).contains(&subject));
    let sources = expression_at(wire, checked, &format!("s.{field}"));
    assert_eq!(sources.len(), count, "相殺後も元fieldの全出現を残す");
    let tree = evaluation_tree(wire, original);
    for source in sources {
        let evaluations = tree
            .iter()
            .copied()
            .filter(|evaluation| f(val(evaluation), "expression") == &reference(source))
            .collect::<Vec<_>>();
        assert_eq!(evaluations.len(), 1);
        let evaluation = evaluations[0];
        assert!(!obj(val(evaluation)).contains_key("value"));
        let reasons = arr(f(evaluation, "reasons"))
            .iter()
            .filter(|reason| f(reason, "code") == &Json::str("missing_observation"))
            .collect::<Vec<_>>();
        assert_eq!(reasons.len(), 1);
        assert_eq!(f(reasons[0], "missing"), &Json::Arr(vec![fact(field)]));
        assert_eq!(
            f(reasons[0], "dependencies"),
            &Json::Arr(vec![reference(source)])
        );
        assert_eq!(f(reasons[0], "location"), f(val(source), "location"));
        assert!(arr(f(evaluation, "support")).contains(&subject));
        for ancestor in tree
            .iter()
            .copied()
            .filter(|ancestor| evaluation_tree(wire, ancestor).contains(&evaluation))
        {
            for supported in arr(f(evaluation, "support")) {
                assert!(arr(f(ancestor, "support")).contains(supported));
            }
        }
        // 未観測slotはReason.missing、支持の原始事実はsubject存在や既知Atomとして保つ。
        for supported in arr(f(evaluation, "support")) {
            audit_fact(supported, evaluation, checked);
        }
        assert_eq!(expression(&ns, evaluation), source);
    }
}
fn decision(wire: &Json, id: &str, status: &str, view_value: Option<bool>) {
    let a = answer(wire, id);
    assert_eq!(f(a, "status"), &Json::str(status));
    let ns = index(wire);
    if let Some(value) = view_value {
        assert!(!obj(a).contains_key("claim"));
        assert_eq!(
            val(target(&ns, f(f(a, "outputs"), "value"), "Bool")),
            &Json::Bool(value)
        );
    } else {
        let claim = target(&ns, f(a, "claim"), "Proposition");
        assert_eq!(f(val(claim), "predicate"), &Json::str("law_holds"));
        assert_eq!(f(f(claim, "judgment"), "status"), &Json::str(status));
    }
}

fn expression_at<'a>(wire: &'a Json, checked: &CheckedInputs, bytes: &str) -> Vec<&'a Json> {
    arr(f(wire, "nodes"))
        .iter()
        .filter(|n| {
            f(n, "type") == &Json::str("Expression")
                && f(val(n), "kind") == &Json::str("source")
                && source(checked, span(f(val(n), "location"))) == bytes.as_bytes()
        })
        .collect()
}
fn evaluation_tree<'a>(wire: &'a Json, evaluation: &'a Json) -> Vec<&'a Json> {
    let ns = index(wire);
    let mut todo = vec![evaluation];
    let mut seen = BTreeSet::new();
    let mut all = vec![];
    while let Some(e) = todo.pop() {
        if seen.insert(text(f(e, "id"))) {
            all.push(e);
            for part in arr(f(val(e), "parts")) {
                for child in arr(f(part, "children")) {
                    todo.push(target(&ns, child, "Evaluation"));
                }
            }
        }
    }
    all
}
fn assert_ast(wire: &Json, checked: &CheckedInputs, evaluation: &Json) {
    let ns = index(wire);
    let template = expression(&ns, evaluation);
    let area = span(f(val(template), "location"));
    let evaluations = evaluation_tree(wire, evaluation);
    for (id, ast) in checked
        .law()
        .exprs
        .iter()
        .enumerate()
        .filter(|(_, e)| area.0 <= e.span.0 && e.span.1 <= area.1)
    {
        if checked.law().expr_type(id).is_none() {
            continue;
        }
        assert!(
            evaluations.iter().any(|e| {
                let source = expression(&ns, e);
                f(val(source), "kind") == &Json::str("source")
                    && span(f(val(source), "location")) == ast.span
            }),
            "元AST出現 {:?}: {:?}",
            ast.span,
            source(checked, ast.span)
        );
    }
}
fn substitutions<'a>(wire: &'a Json, proof: &Json) -> Vec<&'a Json> {
    let ns = index(wire);
    let mut all = vec![];
    for step in arr(f(f(val(proof), "data"), "steps")) {
        let step = target(&ns, step, "Expression");
        if f(val(step), "operation") != &Json::str("substitute") {
            continue;
        }
        let operands = arr(f(val(step), "operands"));
        assert_eq!(operands.len(), 1);
        let original = target(&ns, &operands[0], "Expression");
        let bindings = arr(f(val(step), "bindings"));
        let mut expected = vec![operands[0].clone()];
        expected.extend(bindings.iter().map(|b| f(b, "value").clone()));
        assert_eq!(f(step, "arguments"), &Json::Arr(expected));
        let remaining = arr(f(val(original), "parameters"))
            .iter()
            .filter(|p| !bindings.iter().any(|b| f(b, "name") == f(p, "name")))
            .cloned()
            .collect::<Vec<_>>();
        assert_eq!(f(val(step), "parameters"), &Json::Arr(remaining));
        for binding in arr(f(val(original), "bindings")) {
            assert!(bindings.contains(binding), "同時代入は元固定束縛を保つ");
        }
        for binding in bindings {
            if let Some(p) = arr(f(val(original), "parameters"))
                .iter()
                .find(|p| f(p, "name") == f(binding, "name"))
            {
                val(typed(&ns, f(binding, "value"), f(p, "type")));
            }
        }
        all.push(step);
    }
    all
}
fn whole<'a>(
    wire: &'a Json,
    checked: &CheckedInputs,
    evaluation: &'a Json,
    axes: &[(&str, &str)],
    implicit: bool,
    expected: Option<bool>,
    has_missing: bool,
    nonconstant: bool,
) -> Option<&'a Json> {
    let ns = index(wire);
    let args = arr(f(evaluation, "arguments"));
    let template = target(&ns, &args[0], "Expression");
    assert_eq!(f(val(evaluation), "expression"), &args[0]);
    assert_eq!(f(val(template), "kind"), &Json::str("source"));
    let expected_parameters = if implicit {
        axes.iter().map(|(n, t)| parameter(n, t)).collect()
    } else {
        vec![]
    };
    assert_eq!(
        f(val(template), "parameters"),
        &Json::Arr(expected_parameters)
    );
    for name in axes.iter().map(|(n, _)| *n) {
        assert!(
            !arr(f(val(evaluation), "bindings"))
                .iter()
                .any(|b| f(b, "name") == &Json::str(name)),
            "元全域記号を通常Bindingへ昇格しない"
        );
    }
    assert_eq!(
        f(f(evaluation, "scope"), "domain"),
        &Json::str(if has_missing {
            "all_completions"
        } else {
            "all_assignments"
        })
    );
    let quantifiers = arr(f(f(evaluation, "scope"), "quantifiers"));
    let mut domains = vec![];
    for (position, (name, ty)) in axes.iter().enumerate() {
        let domain = target(&ns, &args[1 + position], "Domain");
        assert_eq!(f(val(domain), "kind"), &Json::str("type"));
        assert_eq!(f(val(domain), "type"), &Json::str(*ty));
        assert!(!obj(val(domain)).contains_key("elements"));
        assert_eq!(f(domain, "arguments"), &Json::Arr(vec![args[0].clone()]));
        let descriptor = quantifiers
            .iter()
            .find(|q| {
                f(q, "name") == &Json::str(*name)
                    && f(q, "type") == &Json::str(*ty)
                    && obj(q).get("domain") == Some(&args[1 + position])
            })
            .unwrap();
        assert_eq!(f(descriptor, "kind"), &Json::str("forall"));
        assert_eq!(f(descriptor, "domain"), &args[1 + position]);
        domains.push(args[1 + position].clone());
    }
    assert_eq!(
        quantifiers
            .iter()
            .filter(|q| obj(q).get("domain").is_some_and(|r| domains.contains(r)))
            .map(|q| text(f(q, "name")))
            .collect::<Vec<_>>(),
        axes.iter().map(|(name, _)| *name).collect::<Vec<_>>(),
        "Scopeは元binder順で実全域軸を保持する"
    );
    let body = target(&ns, &args[1 + axes.len()], "Evaluation");
    let difference_evaluation = target(&ns, &args[2 + axes.len()], "Evaluation");
    let difference = expression(&ns, difference_evaluation);
    assert_eq!(f(val(difference), "kind"), &Json::str("transform"));
    assert_eq!(f(val(difference), "operation"), &Json::str("difference"));
    assert_eq!(
        f(val(difference), "parameters"),
        &Json::Arr(axes.iter().map(|(n, t)| parameter(n, t)).collect())
    );
    let diff_args = arr(f(difference, "arguments"));
    assert_eq!(&diff_args[..1 + axes.len()], &args[..1 + axes.len()]);
    assert_eq!(diff_args.len(), 3 + axes.len());
    let operands = arr(f(val(difference), "operands"));
    assert_eq!(operands.len(), 2);
    let difference_parts = arr(f(val(difference_evaluation), "parts"));
    assert_eq!(difference_parts.len(), 1);
    let comparison_span = span(f(&difference_parts[0], "location"));
    let (_, comparison_ast) = checked
        .law()
        .exprs
        .iter()
        .enumerate()
        .find(|(_, ast)| ast.span == comparison_span)
        .unwrap();
    let ExprKind::Binary {
        lhs,
        rhs,
        op: archsig::law::ast::BinOp::Eq,
    } = &comparison_ast.kind
    else {
        panic!("元アフィンEq")
    };
    let operand_spans = [
        checked.law().exprs[*lhs].span,
        checked.law().exprs[*rhs].span,
    ];
    assert_eq!(
        f(&difference_parts[0], "children"),
        &Json::Arr(diff_args[1 + axes.len()..].to_vec())
    );
    assert!(!obj(&difference_parts[0]).contains_key("residual"));
    let mut residual_arguments = vec![reference(difference)];
    residual_arguments.extend(diff_args[1 + axes.len()..].iter().cloned());
    if let Some(value) = obj(val(difference_evaluation)).get("value") {
        typed(&ns, value, &checked.law().expr_type(*lhs).unwrap().wire());
        residual_arguments.push(value.clone());
    }
    assert_eq!(
        f(difference_evaluation, "arguments"),
        &Json::Arr(residual_arguments)
    );
    for (operand, position) in operands.iter().zip(operand_spans) {
        assert_eq!(
            span(f(val(target(&ns, operand, "Expression")), "location")),
            position,
            "差は元左右の順序を保つ"
        );
    }
    for ((evaluation, source), id) in diff_args[1 + axes.len()..]
        .iter()
        .zip(operands)
        .zip([*lhs, *rhs])
    {
        let evaluation = target(&ns, evaluation, "Evaluation");
        assert_eq!(f(val(evaluation), "expression"), source);
        assert_eq!(
            arr(f(target(&ns, source, "Expression"), "arguments")).first(),
            Some(&args[0])
        );
        if let ExprKind::Int(integer) = &checked.law().exprs[id].kind {
            let ty = checked.law().expr_type(id).unwrap().wire();
            assert_eq!(
                val(typed(&ns, f(val(evaluation), "value"), &ty)),
                &if ty == Json::str("Q") {
                    q(integer, "1")
                } else {
                    Json::str(integer)
                },
                "元の数値literalは正確な通常値を保つ"
            );
        } else {
            assert!(
                !obj(val(evaluation)).contains_key("value"),
                "自由数値parameterを読む元左右は通常値でない"
            );
        }
    }
    let parts = arr(f(val(evaluation), "parts"));
    assert_eq!(parts.len(), 1);
    assert_eq!(f(&parts[0], "residual"), &reference(difference_evaluation));
    assert!(arr(f(&parts[0], "children")).contains(&reference(body)));
    if nonconstant {
        assert!(!obj(val(difference_evaluation)).contains_key("value"));
        assert!(
            !obj(val(body)).contains_key("value"),
            "全域wholeの偽をpointwise bodyの偽へ転記しない"
        );
    }
    assert_ast(wire, checked, evaluation);
    let normalizations = arr(f(evaluation, "evidence"))
        .iter()
        .map(|r| target(&ns, r, "Evidence"))
        .filter(|n| f(val(n), "kind") == &Json::str("normalization"))
        .collect::<Vec<_>>();
    if let Some(expected) = expected {
        let boolean = target(&ns, f(val(evaluation), "value"), "Bool");
        assert_eq!(val(boolean), &Json::Bool(expected));
        assert_eq!(normalizations.len(), 1);
        let proof = normalizations[0];
        let data = f(val(proof), "data");
        assert_eq!(f(data, "before"), &args[0]);
        assert_eq!(f(data, "after"), f(val(evaluation), "value"));
        let steps = arr(f(data, "steps"));
        assert_eq!(steps.first(), Some(&reference(difference)));
        let mut expected_arguments = vec![args[0].clone(), reference(boolean)];
        expected_arguments.extend(steps.iter().cloned());
        assert_eq!(f(proof, "arguments"), &Json::Arr(expected_arguments));
        assert_eq!(
            f(boolean, "arguments"),
            &Json::Arr(
                std::iter::once(args[0].clone())
                    .chain(steps.iter().cloned())
                    .collect()
            )
        );
        assert_eq!(f(proof, "scope"), f(evaluation, "scope"));
        assert_eq!(f(proof, "support"), f(evaluation, "support"));
        assert_eq!(f(boolean, "scope"), f(evaluation, "scope"));
        assert_eq!(f(boolean, "support"), f(evaluation, "support"));
        assert_eq!(f(f(boolean, "rule"), "kind"), &Json::str("construction"));
        assert_eq!(f(f(boolean, "rule"), "name"), &Json::str("evaluation"));
        assert!(arr(f(boolean, "evidence")).is_empty());
        substitutions(wire, proof);
        let mut expected_args = vec![args[0].clone()];
        expected_args.extend(domains);
        expected_args.extend([
            reference(body),
            reference(difference_evaluation),
            reference(boolean),
            reference(proof),
        ]);
        assert_eq!(f(evaluation, "arguments"), &Json::Arr(expected_args));
        Some(proof)
    } else {
        assert!(!obj(val(evaluation)).contains_key("value"));
        assert!(normalizations.is_empty());
        None
    }
}
fn counterexample<'a>(wire: &'a Json, id: &str) -> &'a Json {
    let examples = reachable(wire, answer(wire, id))
        .into_iter()
        .filter(|n| {
            f(n, "type") == &Json::str("Evidence")
                && f(val(n), "kind") == &Json::str("counterexample")
        })
        .collect::<Vec<_>>();
    assert_eq!(examples.len(), 1);
    examples[0]
}
fn concrete_counterexample(
    wire: &Json,
    checked: &CheckedInputs,
    id: &str,
    ty: &str,
    name: &str,
    assigned: Json,
    left: Json,
    right: Json,
) {
    let ns = index(wire);
    let example = counterexample(wire, id);
    let data = f(val(example), "data");
    let binding = arr(f(data, "bindings"))
        .iter()
        .find(|b| f(b, "name") == &Json::str(name))
        .unwrap();
    assert_eq!(val(target(&ns, f(binding, "value"), ty)), &assigned);
    let args = arr(f(example, "arguments"));
    assert_eq!(args.len(), 5);
    let template = target(&ns, &args[0], "Expression");
    let proof = target(&ns, &args[1], "Evidence");
    let substitution = target(&ns, &args[2], "Expression");
    assert_eq!(f(val(substitution), "operation"), &Json::str("substitute"));
    assert!(substitutions(wire, proof).contains(&substitution));
    for (key, wanted, argument) in [("left", left, &args[3]), ("right", right, &args[4])] {
        assert_eq!(f(data, key), argument);
        let evaluation = target(&ns, argument, "Evaluation");
        assert_eq!(val(target(&ns, f(val(evaluation), "value"), ty)), &wanted);
        let original = expression(&ns, evaluation);
        assert_eq!(f(val(original), "operation"), &Json::str("substitute"));
        assert!(arr(f(val(original), "bindings")).contains(binding));
        let before = target(&ns, &arr(f(val(original), "operands"))[0], "Expression");
        assert_eq!(
            arr(f(before, "arguments")).first(),
            Some(&reference(template))
        );
        assert!(!source(checked, span(f(val(before), "location"))).is_empty());
    }
    assert_ne!(f(data, "left"), f(data, "right"));
}
fn fallback_counterexample(wire: &Json, id: &str) {
    let ns = index(wire);
    let example = counterexample(wire, id);
    let data = f(val(example), "data");
    let args = arr(f(example, "arguments"));
    assert_eq!(args.len(), 3);
    target(&ns, &args[0], "Expression");
    let whole = target(&ns, &args[1], "Evaluation");
    let proof = target(&ns, &args[2], "Evidence");
    assert_eq!(f(data, "left"), f(val(whole), "value"));
    assert_eq!(f(f(val(proof), "data"), "after"), f(data, "left"));
    assert_eq!(
        val(target(&ns, f(data, "left"), "Bool")),
        &Json::Bool(false)
    );
    assert_eq!(
        val(target(&ns, f(data, "right"), "Bool")),
        &Json::Bool(true)
    );
    assert!(
        arr(f(data, "bindings"))
            .iter()
            .all(|b| f(b, "name") == &Json::str("s")),
        "補完依存反例へ固定p/hを捏造しない"
    );
}

fn basic(ty: &str, implicit: bool, same: bool) {
    let rhs = if same { "1" } else { "2" };
    let body = format!("z+1=z+{rhs}");
    let (script, request) = if implicit {
        (
            format!("law required requirement(z:{ty}): {body};"),
            "a=check(Calc.requirement)",
        )
    } else {
        (
            format!("view comparison(): Bool = forall z:{ty} . {body};"),
            "a=evaluate(Calc.comparison)",
        )
    };
    let (wire, checked) = run(fixture(&script, false, false), &[request]);
    let defaults = arr(f(&arr(f(&wire, "requests"))[0], "defaults"));
    if implicit {
        let universal = defaults
            .iter()
            .find(|d| f(d, "rule") == &Json::str("universal_parameters"))
            .unwrap();
        assert_eq!(f(universal, "declaration"), &Json::str("Calc.requirement"));
        assert_eq!(f(universal, "parameters"), &Json::Arr(vec![Json::str("z")]));
    } else {
        assert!(
            defaults
                .iter()
                .all(|d| f(d, "rule") != &Json::str("universal_parameters"))
        );
    }
    decision(
        &wire,
        "a",
        if implicit && !same {
            "refuted"
        } else {
            "established"
        },
        (!implicit).then_some(same),
    );
    assert_eq!(f(&wire, "status"), &Json::str("complete"));
    let proof = whole(
        &wire,
        &checked,
        root(&wire, "a"),
        &[("z", ty)],
        implicit,
        Some(same),
        false,
        false,
    )
    .unwrap();
    missing(&wire, "a", &[]);
    if implicit && !same {
        concrete_counterexample(
            &wire,
            &checked,
            "a",
            ty,
            "z",
            numeric(ty, "0"),
            numeric(ty, "1"),
            numeric(ty, "2"),
        );
        assert!(!substitutions(&wire, proof).is_empty());
    }
}
#[test]
fn unbound_z_parameter_identity_uses_its_full_type_domain() {
    basic("Z", true, true);
}
#[test]
fn unbound_z_constant_difference_refutes_with_original_zero_substitution() {
    basic("Z", true, false);
}
#[test]
fn explicit_z_forall_identity_returns_true_over_all_assignments() {
    basic("Z", false, true);
}
#[test]
fn explicit_z_forall_constant_difference_returns_false() {
    basic("Z", false, false);
}
#[test]
fn unbound_q_parameter_identity_uses_its_full_type_domain() {
    basic("Q", true, true);
}
#[test]
fn unbound_q_constant_difference_refutes_with_typed_zero_substitution() {
    basic("Q", true, false);
}
#[test]
fn explicit_q_forall_identity_returns_true_over_all_assignments() {
    basic("Q", false, true);
}
#[test]
fn explicit_q_forall_constant_difference_returns_false() {
    basic("Q", false, false);
}

fn law_formula(
    ty: &str,
    parameters: &str,
    formula: &str,
    axes: &[(&str, &str)],
    expected: bool,
) -> (Json, CheckedInputs) {
    let (wire, checked) = run(
        fixture(
            &format!("law required requirement({parameters}): {formula};"),
            false,
            false,
        ),
        &["a=check(Calc.requirement)"],
    );
    decision(
        &wire,
        "a",
        if expected { "established" } else { "refuted" },
        None,
    );
    whole(
        &wire,
        &checked,
        root(&wire, "a"),
        axes,
        true,
        Some(expected),
        false,
        false,
    );
    let ns = index(&wire);
    let whole_eval = root(&wire, "a");
    let args = arr(f(whole_eval, "arguments"));
    let residual = target(&ns, &args[2 + axes.len()], "Evaluation");
    if let Some(value) = obj(val(residual)).get("value") {
        target(&ns, value, ty);
    }
    missing(&wire, "a", &[]);
    (wire, checked)
}
#[test]
fn q_universal_half_offsets_reduce_to_identity() {
    law_formula("Q", "z:Q", "z+rat(1,2)+rat(1,2)=z+1", &[("z", "Q")], true);
}
#[test]
fn q_universal_half_offsets_refute_variant_by_original_reapplication() {
    let (wire, checked) = law_formula("Q", "z:Q", "z+rat(1,2)+rat(1,2)=z+2", &[("z", "Q")], false);
    concrete_counterexample(
        &wire,
        &checked,
        "a",
        "Q",
        "z",
        q("0", "1"),
        q("1", "1"),
        q("2", "1"),
    );
}
#[test]
fn multiple_z_parameters_keep_declared_order_and_independent_axes() {
    law_formula("Z", "y:Z,x:Z", "x+y=y+x", &[("y", "Z"), ("x", "Z")], true);
}
#[test]
fn multiple_q_parameters_keep_exact_fractional_coefficients() {
    law_formula(
        "Q",
        "x:Q,y:Q",
        "rat(1,2)*x+rat(2,3)*y=rat(2,3)*y+rat(1,2)*x",
        &[("x", "Q"), ("y", "Q")],
        true,
    );
}
#[test]
fn z_universal_coefficients_above_i64_are_exact() {
    law_formula(
        "Z",
        "z:Z",
        "9223372036854775808*z+9223372036854775809=9223372036854775808*z+9223372036854775809",
        &[("z", "Z")],
        true,
    );
}
#[test]
fn z_nonzero_parameter_coefficient_uses_unit_counterexample_not_finite_coverage() {
    let (wire, checked) = run(
        fixture("law required requirement(z:Z): z=0;", false, false),
        &["a=check(Calc.requirement)"],
    );
    decision(&wire, "a", "refuted", None);
    whole(
        &wire,
        &checked,
        root(&wire, "a"),
        &[("z", "Z")],
        true,
        Some(false),
        false,
        true,
    );
    concrete_counterexample(
        &wire,
        &checked,
        "a",
        "Z",
        "z",
        Json::str("1"),
        Json::str("1"),
        Json::str("0"),
    );
}
#[test]
fn q_nonzero_parameter_coefficient_keeps_exact_unit_reapplication() {
    let (wire, checked) = run(
        fixture("law required requirement(z:Q): rat(1,2)*z=0;", false, false),
        &["a=check(Calc.requirement)"],
    );
    decision(&wire, "a", "refuted", None);
    whole(
        &wire,
        &checked,
        root(&wire, "a"),
        &[("z", "Q")],
        true,
        Some(false),
        false,
        true,
    );
    concrete_counterexample(
        &wire,
        &checked,
        "a",
        "Q",
        "z",
        q("1", "1"),
        q("1", "2"),
        q("0", "1"),
    );
}

fn missing_universal(ty: &str, field: &str, implicit: bool) {
    let formula = format!("z+s.{field}=z");
    let (script, request) = if implicit {
        (
            format!("law required requirement(s:Sample,z:{ty}): {formula};"),
            "a=check(Calc.requirement,s=@v/item)",
        )
    } else {
        (
            format!("view comparison(s:Sample): Bool = forall z:{ty} . {formula};"),
            "a=evaluate(Calc.comparison,s=@v/item)",
        )
    };
    let (wire, checked) = run(fixture(&script, false, false), &[request]);
    assert_eq!(f(answer(&wire, "a"), "status"), &Json::str("undetermined"));
    if implicit {
        decision(&wire, "a", "undetermined", None);
    } else {
        assert!(!obj(answer(&wire, "a")).contains_key("claim"));
    }
    assert_eq!(f(&wire, "status"), &Json::str("partial"));
    missing(&wire, "a", &[field]);
    whole(
        &wire,
        &checked,
        root(&wire, "a"),
        &[("z", ty)],
        implicit,
        None,
        true,
        true,
    );
    numeric_completion_pair(
        &wire,
        &checked,
        "a",
        ty,
        &[field],
        &[numeric(ty, "0")],
        &[numeric(ty, "1")],
    );
}
#[test]
fn unbound_z_parameter_and_missing_same_named_field_remain_distinct() {
    missing_universal("Z", "z", true);
}
#[test]
fn explicit_z_forall_with_missing_offset_is_undetermined() {
    missing_universal("Z", "z", false);
}
#[test]
fn unbound_q_parameter_and_missing_fact_remain_distinct() {
    missing_universal("Q", "q", true);
}
#[test]
fn explicit_q_forall_with_missing_offset_is_undetermined() {
    missing_universal("Q", "q", false);
}

#[test]
fn nonzero_parameter_coefficient_refutes_every_completion_without_fixed_parameter_witness() {
    let (wire, checked) = run(
        fixture(
            "law required requirement(s:Sample,z:Z): 2*z+s.z=0;",
            false,
            false,
        ),
        &["a=check(Calc.requirement,s=@v/item)"],
    );
    decision(&wire, "a", "refuted", None);
    whole(
        &wire,
        &checked,
        root(&wire, "a"),
        &[("z", "Z")],
        true,
        Some(false),
        true,
        true,
    );
    missing(&wire, "a", &["z"]);
    fallback_counterexample(&wire, "a");
}
#[test]
fn z_missing_coefficients_gcd_prevents_zero_in_every_completion() {
    let (wire, checked) = run(
        fixture(
            "law required requirement(s:Sample,z:Z): z+2*s.z+4*s.k=z+1;",
            false,
            false,
        ),
        &["a=check(Calc.requirement,s=@v/item)"],
    );
    decision(&wire, "a", "refuted", None);
    whole(
        &wire,
        &checked,
        root(&wire, "a"),
        &[("z", "Z")],
        true,
        Some(false),
        true,
        true,
    );
    missing(&wire, "a", &["z", "k"]);
    common_missing_counterexample(&wire, "a");
}

fn numeric_completion_pair(
    wire: &Json,
    checked: &CheckedInputs,
    id: &str,
    ty: &str,
    fields: &[&str],
    solution: &[Json],
    false_values: &[Json],
) {
    let ns = index(wire);
    let pairs = reachable(wire, answer(wire, id))
        .into_iter()
        .filter(|n| {
            f(n, "type") == &Json::str("Evidence")
                && f(val(n), "kind") == &Json::str("completion_pair")
        })
        .collect::<Vec<_>>();
    assert_eq!(pairs.len(), 1);
    let data = f(val(pairs[0]), "data");
    assert_eq!(
        f(data, "fields"),
        &Json::Arr(fields.iter().map(|field| fact(field)).collect())
    );
    let original = root(wire, id);
    let original_arguments = arr(f(original, "arguments"));
    let template = target(&ns, &original_arguments[0], "Expression");
    let domains = &original_arguments[1..2];
    let body = target(&ns, &original_arguments[2], "Evaluation");
    let difference = target(&ns, &original_arguments[3], "Evaluation");
    assert!(!obj(val(difference)).contains_key("value"));
    let original_part = &arr(f(val(original), "parts"))[0];
    let mut anchors = vec![];
    let mut results = vec![];
    let mut all_values = vec![];
    let mut rows = BTreeSet::new();
    for (binding, result) in [("first", "first_result"), ("second", "second_result")] {
        let values = arr(f(data, binding));
        assert_eq!(values.len(), fields.len());
        let assigned = values
            .iter()
            .map(|value| val(target(&ns, value, ty)).clone())
            .collect::<Vec<_>>();
        let expected = if assigned == solution {
            true
        } else {
            assert_eq!(assigned, false_values);
            false
        };
        assert!(rows.insert((Json::Arr(assigned).canonical(), expected)));
        let evaluation = target(&ns, f(data, result), "Evaluation");
        let anchor = expression(&ns, evaluation);
        assert_eq!(f(val(anchor), "kind"), &Json::str("transform"));
        assert_eq!(f(val(anchor), "operation"), &Json::str("substitute"));
        assert_eq!(
            f(val(anchor), "operands"),
            &Json::Arr(vec![reference(template)])
        );
        assert_eq!(f(val(anchor), "parameters"), f(val(template), "parameters"));
        assert_eq!(f(val(anchor), "bindings"), f(val(template), "bindings"));
        let mut anchor_arguments = vec![reference(template)];
        anchor_arguments.extend(
            arr(f(val(template), "bindings"))
                .iter()
                .map(|b| f(b, "value").clone()),
        );
        assert_eq!(f(anchor, "arguments"), &Json::Arr(anchor_arguments));
        for (value, field) in values.iter().zip(fields) {
            let scalar = target(&ns, value, ty);
            let scalar_arguments = arr(f(scalar, "arguments"));
            assert_eq!(scalar_arguments.len(), 3);
            assert_eq!(
                &scalar_arguments[..2],
                &[reference(template), reference(anchor)]
            );
            let original_field = target(&ns, &scalar_arguments[2], "Expression");
            assert_eq!(f(val(original_field), "kind"), &Json::str("source"));
            assert_eq!(
                source(checked, span(f(val(original_field), "location"))),
                format!("s.{field}").as_bytes()
            );
            assert_eq!(
                arr(f(original_field, "arguments")).first(),
                Some(&reference(template))
            );
            assert!(arr(f(scalar, "evidence")).is_empty());
        }
        let case_value = target(&ns, f(val(evaluation), "value"), "Bool");
        assert_eq!(val(case_value), &Json::Bool(expected));
        let mut value_arguments = vec![reference(template), reference(anchor)];
        value_arguments.extend_from_slice(values);
        assert_eq!(f(case_value, "arguments"), &Json::Arr(value_arguments));
        let mut case_arguments = vec![reference(anchor)];
        case_arguments.extend_from_slice(domains);
        case_arguments.extend([reference(body), reference(difference)]);
        case_arguments.extend_from_slice(values);
        case_arguments.push(reference(case_value));
        assert_eq!(f(evaluation, "arguments"), &Json::Arr(case_arguments));
        assert_eq!(f(val(evaluation), "bindings"), f(val(template), "bindings"));
        assert_eq!(
            f(val(evaluation), "applicability"),
            &Json::str("applicable")
        );
        let parts = arr(f(val(evaluation), "parts"));
        assert_eq!(parts.len(), 1);
        assert_eq!(f(&parts[0], "location"), f(original_part, "location"));
        assert_eq!(f(&parts[0], "children"), &Json::Arr(vec![reference(body)]));
        assert_eq!(f(&parts[0], "residual"), &reference(difference));
        assert_eq!(f(&parts[0], "value"), &reference(case_value));
        assert!(arr(f(evaluation, "evidence")).is_empty());
        assert!(arr(f(case_value, "evidence")).is_empty());
        for node in [anchor, evaluation, case_value] {
            assert_eq!(f(node, "scope"), f(original, "scope"));
            assert_eq!(f(node, "support"), f(original, "support"));
        }
        assert!(
            !arr(f(val(evaluation), "bindings")).iter().any(|b| fields
                .iter()
                .any(|field| f(b, "name") == &Json::str(*field))),
            "補完値を通常の観測Bindingにしない"
        );
        assert_eq!(
            f(f(evaluation, "scope"), "domain"),
            &Json::str("all_completions")
        );
        scope_axis(wire, evaluation, "z", ty);
        anchors.push(reference(anchor));
        results.push(reference(evaluation));
        all_values.extend_from_slice(values);
    }
    assert_eq!(rows.len(), 2);
    assert_ne!(anchors[0], anchors[1]);
    assert_ne!(results[0], results[1]);
    let mut pair_arguments = vec![reference(template)];
    pair_arguments.extend(anchors);
    pair_arguments.extend(results);
    pair_arguments.extend(all_values);
    assert_eq!(f(pairs[0], "arguments"), &Json::Arr(pair_arguments));
    assert_eq!(
        f(original, "evidence"),
        &Json::Arr(vec![reference(pairs[0])])
    );
    assert_eq!(f(pairs[0], "scope"), f(original, "scope"));
    assert_eq!(f(pairs[0], "support"), f(original, "support"));
    assert!(!obj(val(root(wire, id))).contains_key("value"));
    assert!(
        arr(f(wire, "nodes"))
            .iter()
            .all(|n| f(n, "type") != &Json::str("Evidence")
                || f(val(n), "kind") != &Json::str("finite_exhaustion")),
        "二補完の証拠対を数値全補完のcoverageとしない"
    );
}
#[test]
fn q_missing_linear_equation_constructs_half_solution_and_distinct_completion() {
    let (wire, checked) = run(
        fixture(
            "law required requirement(s:Sample,z:Q): z+2*s.q=z+1;",
            false,
            false,
        ),
        &["a=check(Calc.requirement,s=@v/item)"],
    );
    decision(&wire, "a", "undetermined", None);
    missing(&wire, "a", &["q"]);
    whole(
        &wire,
        &checked,
        root(&wire, "a"),
        &[("z", "Q")],
        true,
        None,
        true,
        true,
    );
    numeric_completion_pair(
        &wire,
        &checked,
        "a",
        "Q",
        &["q"],
        &[q("1", "2")],
        &[q("3", "2")],
    );
}

#[test]
fn canceled_missing_slot_remains_supported_and_is_completed_in_both_numeric_cases() {
    let (wire, checked) = run(
        fixture(
            "view comparison(s:Sample): Bool = forall z:Z . z+(s.z-s.z)+s.k=z;",
            false,
            false,
        ),
        &["a=evaluate(Calc.comparison,s=@v/item)"],
    );
    assert_eq!(f(answer(&wire, "a"), "status"), &Json::str("undetermined"));
    assert_eq!(f(&wire, "status"), &Json::str("partial"));
    missing(&wire, "a", &["z", "k"]);
    whole(
        &wire,
        &checked,
        root(&wire, "a"),
        &[("z", "Z")],
        false,
        None,
        true,
        true,
    );
    missing_occurrences(&wire, &checked, "a", "z", 2);
    missing_occurrences(&wire, &checked, "a", "k", 1);
    // Factの元順はfield名順。相殺zも両補完で型付き0を持ち、kだけがwhole判断を変える。
    numeric_completion_pair(
        &wire,
        &checked,
        "a",
        "Z",
        &["k", "z"],
        &[Json::str("0"), Json::str("0")],
        &[Json::str("1"), Json::str("0")],
    );
}
fn common_missing_counterexample(wire: &Json, id: &str) {
    let ns = index(wire);
    let example = counterexample(wire, id);
    let data = f(val(example), "data");
    let args = arr(f(example, "arguments"));
    assert_eq!(args.len(), 5);
    let binding = arr(f(data, "bindings"))
        .iter()
        .find(|b| f(b, "name") == &Json::str("z"))
        .unwrap();
    assert_eq!(val(target(&ns, f(binding, "value"), "Z")), &Json::str("0"));
    let substituted = target(&ns, &args[2], "Expression");
    assert_eq!(f(val(substituted), "operation"), &Json::str("substitute"));
    assert!(arr(f(val(substituted), "bindings")).contains(binding));
    for (key, argument) in [("left", &args[3]), ("right", &args[4])] {
        assert_eq!(f(data, key), argument);
        target(&ns, argument, "Evaluation");
    }
    let left = target(&ns, f(data, "left"), "Evaluation");
    assert!(!obj(val(left)).contains_key("value"));
    let right = target(&ns, f(data, "right"), "Evaluation");
    assert_eq!(
        val(target(&ns, f(val(right), "value"), "Z")),
        &Json::str("1")
    );
    assert!(
        arr(f(data, "bindings"))
            .iter()
            .all(|b| ["s", "z"].contains(&text(f(b, "name"))))
    );
}
#[test]
fn explicit_nested_forall_preserves_each_original_binder_and_scope_axis() {
    let script = "view comparison(): Bool = forall y:Z . forall x:Z . x+y=y+x;";
    let (wire, checked) = run(
        fixture(script, false, false),
        &["a=evaluate(Calc.comparison)"],
    );
    decision(&wire, "a", "established", Some(true));
    whole(
        &wire,
        &checked,
        root(&wire, "a"),
        &[("y", "Z"), ("x", "Z")],
        false,
        Some(true),
        false,
        false,
    );
    let inner = expression_at(&wire, &checked, "forall x:Z . x+y=y+x");
    assert!(!inner.is_empty());
    assert!(
        inner
            .iter()
            .any(|s| f(val(s), "parameters") == &Json::Arr(vec![parameter("y", "Z")]))
    );
    let body = expression_at(&wire, &checked, "x+y=y+x");
    assert!(
        body.iter().any(|s| f(val(s), "parameters")
            == &Json::Arr(vec![parameter("y", "Z"), parameter("x", "Z")]))
    );
}
#[test]
fn let_and_view_argument_keep_the_callers_universal_parameter_identity() {
    let script = "view carry(hz:Z): Z = let saved=hz in saved; law required requirement(z:Z): let held=z in carry(held)+1=z+1;";
    let (wire, checked) = run(
        fixture(script, false, false),
        &["a=check(Calc.requirement)"],
    );
    decision(&wire, "a", "established", None);
    whole(
        &wire,
        &checked,
        root(&wire, "a"),
        &[("z", "Z")],
        true,
        Some(true),
        false,
        false,
    );
    let ns = index(&wire);
    let mut calls = vec![];
    for n in reachable(&wire, answer(&wire, "a")) {
        if f(n, "type") == &Json::str("Evaluation") {
            let source_node = expression(&ns, n);
            if f(val(source_node), "kind") == &Json::str("source")
                && source(&checked, span(f(val(source_node), "location"))) == b"carry(held)"
            {
                calls.push(n);
            }
        }
    }
    assert_eq!(calls.len(), 1);
    let parts = arr(f(val(calls[0]), "parts"));
    assert_eq!(parts.len(), 1);
    let children = arr(f(&parts[0], "children"));
    assert_eq!(children.len(), 2);
    let argument = target(&ns, &children[0], "Evaluation");
    assert!(!obj(val(argument)).contains_key("value"));
    let body = target(&ns, &children[1], "Evaluation");
    assert!(!obj(val(body)).contains_key("value"));
    for n in evaluation_tree(&wire, body) {
        assert!(
            !arr(f(val(n), "bindings"))
                .iter()
                .any(|b| f(b, "name") == &Json::str("hz"))
        );
    }
    let parameter_sources = expression_at(&wire, &checked, "hz");
    assert!(!parameter_sources.is_empty());
    for parameter_source in parameter_sources {
        let uses = reachable(&wire, body)
            .into_iter()
            .filter(|n| {
                f(n, "type") == &Json::str("Evaluation")
                    && f(val(n), "expression") == &reference(parameter_source)
            })
            .collect::<Vec<_>>();
        for use_site in uses {
            assert!(arr(f(&arr(f(val(use_site), "parts"))[0], "children")).contains(&children[0]));
        }
    }
}
#[test]
fn repeated_requests_keep_distinct_original_domains_normalizations_and_binders() {
    let (wire, checked) = run(
        fixture("law required requirement(z:Z): z+1=z+1;", false, false),
        &["a=check(Calc.requirement)", "b=check(Calc.requirement)"],
    );
    let mut templates = BTreeSet::new();
    let mut domains = BTreeSet::new();
    let mut proofs = BTreeSet::new();
    for id in ["a", "b"] {
        decision(&wire, id, "established", None);
        let evaluation = root(&wire, id);
        let proof = whole(
            &wire,
            &checked,
            evaluation,
            &[("z", "Z")],
            true,
            Some(true),
            false,
            false,
        )
        .unwrap();
        let args = arr(f(evaluation, "arguments"));
        assert!(templates.insert(args[0].canonical()));
        assert!(domains.insert(args[1].canonical()));
        assert!(proofs.insert(text(f(proof, "id"))));
    }
}
fn scope_axis(wire: &Json, node: &Json, name: &str, ty: &str) {
    let ns = index(wire);
    let descriptors = arr(f(f(node, "scope"), "quantifiers"))
        .iter()
        .filter(|q| f(q, "name") == &Json::str(name) && f(q, "type") == &Json::str(ty))
        .collect::<Vec<_>>();
    assert!(!descriptors.is_empty());
    for descriptor in descriptors {
        assert_eq!(f(descriptor, "kind"), &Json::str("forall"));
        let domain = target(&ns, f(descriptor, "domain"), "Domain");
        assert_eq!(f(val(domain), "kind"), &Json::str("type"));
        assert_eq!(f(val(domain), "type"), &Json::str(ty));
        assert!(!obj(val(domain)).contains_key("elements"));
    }
}
fn unsupported_nonlinear(ty: &str, missing_field: Option<&str>) {
    let expression = if let Some(field) = missing_field {
        format!("z*s.{field}=z")
    } else {
        "z*z=z".into()
    };
    let (script, request) = if missing_field.is_some() {
        (
            format!("law required requirement(s:Sample,z:{ty}): {expression};"),
            "a=check(Calc.requirement,s=@v/item)",
        )
    } else {
        (
            format!("law required requirement(z:{ty}): {expression};"),
            "a=check(Calc.requirement)",
        )
    };
    let (wire, checked) = run(fixture(&script, false, false), &[request]);
    decision(&wire, "a", "undetermined", None);
    scope_axis(&wire, answer(&wire, "a"), "z", ty);
    missing(&wire, "a", &missing_field.into_iter().collect::<Vec<_>>());
    let reasons = arr(f(answer(&wire, "a"), "reasons"))
        .iter()
        .filter(|r| f(r, "code") == &Json::str("unsupported_algorithm"))
        .collect::<Vec<_>>();
    assert!(!reasons.is_empty());
    let ns = index(&wire);
    for reason in reasons {
        let details = f(reason, "details");
        assert_eq!(f(details, "question"), &Json::str("check"));
        assert!(arr(f(details, "operand_types")).contains(&Json::str(ty)));
        assert!(!text(f(details, "method")).is_empty());
        let location = span(f(reason, "location"));
        assert_eq!(source(&checked, location), expression.as_bytes());
        assert!(!arr(f(reason, "dependencies")).is_empty());
        for dependency in arr(f(reason, "dependencies")) {
            target(&ns, dependency, "Expression");
        }
    }
    assert!(!obj(val(root(&wire, "a"))).contains_key("value"));
    assert_ast(&wire, &checked, root(&wire, "a"));
    assert!(
        !reachable(&wire, answer(&wire, "a"))
            .iter()
            .any(|n| f(n, "type") == &Json::str("Evidence")
                && f(val(n), "kind") == &Json::str("counterexample"))
    );
}
#[test]
fn general_integer_nonlinear_universal_retains_original_type_domain_and_needed_algorithm() {
    unsupported_nonlinear("Z", None);
}
#[test]
fn missing_rational_coefficient_retains_unsupported_and_exact_missing() {
    unsupported_nonlinear("Q", Some("q"));
}

fn finite_wholes(wire: &Json, checked: &CheckedInputs, ty: &str, expected: &[(bool, bool)]) {
    let ns = index(wire);
    let aggregate = root(wire, "a");
    let args = arr(f(aggregate, "arguments"));
    assert_eq!(&args[0], f(val(aggregate), "expression"));
    let domain = target(&ns, &args[1], "Domain");
    assert_eq!(f(val(domain), "kind"), &Json::str("finite"));
    assert_eq!(f(val(domain), "type"), &Json::str("Bool"));
    let members = arr(f(val(domain), "elements"));
    assert_eq!(members.len(), 2);
    assert_eq!(
        members
            .iter()
            .map(|m| val(target(&ns, m, "Bool")).canonical())
            .collect::<BTreeSet<_>>(),
        BTreeSet::from([Json::Bool(false).canonical(), Json::Bool(true).canonical()])
    );
    let parts = arr(f(val(aggregate), "parts"));
    assert_eq!(parts.len(), 1);
    let cases = arr(f(&parts[0], "children"));
    assert_eq!(cases.len(), 2);
    let mut selected = BTreeSet::new();
    for case in cases {
        let case = target(&ns, case, "Evaluation");
        let template = target(&ns, &arr(f(case, "arguments"))[0], "Expression");
        let assignments = arr(f(template, "arguments"))
            .iter()
            .filter(|r| members.contains(r))
            .collect::<Vec<_>>();
        assert_eq!(assignments.len(), 1);
        let Json::Bool(flag) = val(target(&ns, assignments[0], "Bool")) else {
            panic!("Bool")
        };
        assert!(selected.insert(*flag));
        let wanted = expected.iter().find(|(b, _)| b == flag).unwrap().1;
        whole(
            wire,
            checked,
            case,
            &[("z", ty)],
            true,
            Some(wanted),
            true,
            false,
        );
        scope_axis(wire, case, "z", ty);
        assert_eq!(
            val(target(&ns, f(val(case), "value"), "Bool")),
            &Json::Bool(wanted)
        );
    }
    assert_eq!(selected, BTreeSet::from([false, true]));
    let evidence = arr(f(aggregate, "evidence"))
        .iter()
        .map(|r| target(&ns, r, "Evidence"))
        .collect::<Vec<_>>();
    assert_eq!(evidence.len(), 1);
    if expected[0].1 == expected[1].1 {
        assert_eq!(f(val(evidence[0]), "kind"), &Json::str("finite_exhaustion"));
        let data = f(val(evidence[0]), "data");
        assert_eq!(f(data, "domain"), &args[1]);
        assert_eq!(f(data, "checked"), &Json::Nat(2));
        assert_eq!(f(data, "instances"), f(&parts[0], "children"));
    } else {
        assert_eq!(f(val(evidence[0]), "kind"), &Json::str("completion_pair"));
        let data = f(val(evidence[0]), "data");
        assert_eq!(f(data, "fields"), &Json::Arr(vec![fact("p")]));
        let mut values = BTreeSet::new();
        let mut results = BTreeSet::new();
        for (assignment, result) in [("first", "first_result"), ("second", "second_result")] {
            let values_row = arr(f(data, assignment));
            assert_eq!(values_row.len(), 1);
            let value = val(target(&ns, &values_row[0], "Bool"));
            assert!(values.insert(value.canonical()));
            assert!(cases.contains(f(data, result)));
            let case = target(&ns, f(data, result), "Evaluation");
            assert!(results.insert(val(target(&ns, f(val(case), "value"), "Bool")).canonical()));
        }
        assert_eq!(values.len(), 2);
        assert_eq!(results.len(), 2);
    }
    missing(wire, "a", &["p"]);
}
#[test]
fn bool_completion_cases_quantify_z_wholes_before_constant_aggregation() {
    let script = "law required requirement(s:Sample,z:Z): if s.p then (if s.p then z=z else z+1=z+2) else z=z;";
    let (wire, checked) = run(
        fixture(script, true, false),
        &["a=check(Calc.requirement,s=@v/item)"],
    );
    decision(&wire, "a", "established", None);
    finite_wholes(&wire, &checked, "Z", &[(false, true), (true, true)]);
}
#[test]
fn bool_completion_cases_keep_q_whole_decisions_and_typed_pair() {
    let script = "law required requirement(s:Sample,z:Q): if s.p then z+rat(1,2)+rat(1,2)=z+1 else z+rat(1,2)+rat(1,2)=z+2;";
    let (wire, checked) = run(
        fixture(script, true, false),
        &["a=check(Calc.requirement,s=@v/item)"],
    );
    decision(&wire, "a", "undetermined", None);
    finite_wholes(&wire, &checked, "Q", &[(false, false), (true, true)]);
    assert!(
        !arr(f(answer(&wire, "a"), "evidence"))
            .iter()
            .any(|r| f(val(target(&index(&wire), r, "Evidence")), "kind")
                == &Json::str("counterexample")),
        "case反例を補完外の単一観測反例へ昇格しない"
    );
}
#[test]
fn false_universal_guard_retains_unobserved_body_and_original_type_domain() {
    let script = "law required requirement(z:Z) when false: z+1=z+2;";
    let (wire, checked) = run(
        fixture(script, false, false),
        &["a=check(Calc.requirement)"],
    );
    decision(&wire, "a", "established", None);
    scope_axis(&wire, answer(&wire, "a"), "z", "Z");
    let evaluation = root(&wire, "a");
    assert_eq!(
        f(val(evaluation), "applicability"),
        &Json::str("not_applicable")
    );
    let Signature::Law { body, .. } = &checked.law().declarations["Calc.requirement"].signature
    else {
        panic!("Law")
    };
    let body_span = checked.law().exprs[*body].span;
    let body_part = arr(f(val(evaluation), "parts"))
        .iter()
        .find(|p| span(f(p, "location")) == body_span)
        .unwrap();
    assert!(!obj(body_part).contains_key("value"));
    assert!(arr(f(body_part, "children")).is_empty());
    let ns = index(&wire);
    assert!(
        !reachable(&wire, evaluation)
            .into_iter()
            .any(|n| f(n, "type") == &Json::str("Evaluation") && {
                let source = expression(&ns, n);
                f(val(source), "kind") == &Json::str("source")
                    && span(f(val(source), "location")) == body_span
                    && f(n, "id") != f(evaluation, "id")
            })
    );
}
#[test]
fn unknown_bool_guard_preserves_all_completions_and_universal_axis() {
    let script = "law required requirement(s:Sample,z:Z) when s.p: z+1=z+2;";
    let (wire, _) = run(
        fixture(script, true, false),
        &["a=check(Calc.requirement,s=@v/item)"],
    );
    decision(&wire, "a", "undetermined", None);
    missing(&wire, "a", &["p"]);
    scope_axis(&wire, answer(&wire, "a"), "z", "Z");
    assert_eq!(
        f(f(answer(&wire, "a"), "scope"), "domain"),
        &Json::str("all_completions")
    );
    let ns = index(&wire);
    let pair = reachable(&wire, answer(&wire, "a"))
        .into_iter()
        .filter(|n| {
            f(n, "type") == &Json::str("Evidence")
                && f(val(n), "kind") == &Json::str("completion_pair")
        })
        .collect::<Vec<_>>();
    assert_eq!(pair.len(), 1);
    let data = f(val(pair[0]), "data");
    assert_eq!(f(data, "fields"), &Json::Arr(vec![fact("p")]));
    let mut decisions = BTreeSet::new();
    for (binding, result) in [("first", "first_result"), ("second", "second_result")] {
        let Json::Bool(flag) = val(target(&ns, &arr(f(data, binding))[0], "Bool")) else {
            panic!("Bool")
        };
        let evaluation = target(&ns, f(data, result), "Evaluation");
        assert_eq!(
            val(target(&ns, f(val(evaluation), "value"), "Bool")),
            &Json::Bool(!flag)
        );
        assert!(decisions.insert(*flag));
        scope_axis(&wire, evaluation, "z", "Z");
    }
    assert_eq!(decisions.len(), 2);
}
#[test]
fn known_coefficients_and_provenance_relocation_preserve_universal_refutation() {
    let script = "law required requirement(s:Sample,z:Z): z+s.knownz=z+8;";
    let request = ["a=check(Calc.requirement,s=@v/item)"];
    let (wire, checked) = run(fixture(script, false, false), &request);
    let (moved, moved_checked) = run(fixture(script, false, true), &request);
    for (result, inputs) in [(&wire, &checked), (&moved, &moved_checked)] {
        decision(result, "a", "refuted", None);
        whole(
            result,
            inputs,
            root(result, "a"),
            &[("z", "Z")],
            true,
            Some(false),
            false,
            false,
        );
        concrete_counterexample(
            result,
            inputs,
            "a",
            "Z",
            "z",
            Json::str("0"),
            Json::str("7"),
            Json::str("8"),
        );
        missing(result, "a", &[]);
        assert!(
            arr(f(root(result, "a"), "support"))
                .iter()
                .any(|support| obj(support).get("field")
                    == Some(&Json::str("Universal.Sample.knownz"))
                    && obj(support).get("atom") == Some(&Json::str("knownz")))
        );
        let subject = inputs.archmap().snapshots[0]
            .subjects
            .iter()
            .find(|s| s.id == "item")
            .unwrap();
        assert!(
            matches!(&subject.fields.iter().find(|f|f.name=="Universal.Sample.owner").unwrap().slot,Slot::Known {value:archsig::archmap::Value::Ref {snapshot,subject},..} if snapshot=="v" && subject=="root")
        );
        assert!(
            matches!(&subject.fields.iter().find(|f|f.name=="Universal.Sample.knownz").unwrap().slot,Slot::Known {value:archsig::archmap::Value::Z(value),..} if value.to_string()=="7")
        );
    }
    for key in ["status", "outputs", "evidence", "claim", "scope", "reasons"] {
        assert_eq!(
            obj(answer(&wire, "a")).get(key),
            obj(answer(&moved, "a")).get(key)
        );
    }
    assert_ne!(
        checked.sources().archmap().bytes(),
        moved_checked.sources().archmap().bytes()
    );
    assert!(
        moved_checked
            .archmap()
            .origins
            .iter()
            .all(|o| o.id.ends_with("_moved"))
    );
    assert_eq!(
        moved_checked.archmap().sources[0].uri,
        "urn:fixture:affine-universal:relocated"
    );
    assert_eq!(moved_checked.archmap().sources[0].revision, "r2");
}

#[test]
fn rational_view_return_preserves_the_universal_argument_and_half_offsets() {
    let script = "view carry(hq:Q): Q = let saved=hq in saved; law required requirement(z:Q): carry(z)+rat(1,2)+rat(1,2)=z+1;";
    let (wire, checked) = run(
        fixture(script, false, false),
        &["a=check(Calc.requirement)"],
    );
    decision(&wire, "a", "established", None);
    whole(
        &wire,
        &checked,
        root(&wire, "a"),
        &[("z", "Q")],
        true,
        Some(true),
        false,
        false,
    );
    let ns = index(&wire);
    let calls = reachable(&wire, answer(&wire, "a"))
        .into_iter()
        .filter(|n| {
            f(n, "type") == &Json::str("Evaluation") && {
                let s = expression(&ns, n);
                f(val(s), "kind") == &Json::str("source")
                    && source(&checked, span(f(val(s), "location"))) == b"carry(z)"
            }
        })
        .collect::<Vec<_>>();
    assert_eq!(calls.len(), 1);
    assert!(!obj(val(calls[0])).contains_key("value"));
    let children = arr(f(&arr(f(val(calls[0]), "parts"))[0], "children"));
    assert_eq!(children.len(), 2);
    let formal = expression_at(&wire, &checked, "hq");
    assert!(!formal.is_empty());
    for source in formal {
        assert_eq!(
            f(val(source), "parameters"),
            &Json::Arr(vec![parameter("hq", "Q")])
        );
        for n in reachable(&wire, answer(&wire, "a"))
            .into_iter()
            .filter(|n| {
                f(n, "type") == &Json::str("Evaluation")
                    && f(val(n), "expression") == &reference(source)
            })
        {
            assert!(!obj(val(n)).contains_key("value"));
            assert!(arr(f(&arr(f(val(n), "parts"))[0], "children")).contains(&children[0]));
            assert!(
                !arr(f(val(n), "bindings"))
                    .iter()
                    .any(|b| f(b, "name") == &Json::str("hq"))
            );
        }
    }
}

#[test]
fn bool_view_counterexample_substitutes_caller_and_preserves_missing_callee_argument() {
    let script = "view eq(a:Z): Bool = a=a+1; law required example(s:Sample,z:Z): eq(z+s.z);";
    let (wire, checked) = run(
        fixture(script, false, false),
        &["a=check(Calc.example,s=@v/item)"],
    );
    decision(&wire, "a", "refuted", None);
    assert_eq!(f(&wire, "status"), &Json::str("complete"));
    missing(&wire, "a", &["z"]);
    let ns = index(&wire);
    let evaluation = root(&wire, "a");
    scope_axis(&wire, evaluation, "z", "Z");
    assert_eq!(
        f(f(evaluation, "scope"), "domain"),
        &Json::str("all_completions")
    );
    missing_occurrences(&wire, &checked, "a", "z", 1);
    assert_eq!(
        val(target(&ns, f(val(evaluation), "value"), "Bool")),
        &Json::Bool(false)
    );
    assert!(
        arr(f(val(evaluation), "bindings"))
            .iter()
            .all(|b| f(b, "name") == &Json::str("s"))
    );
    let args = arr(f(evaluation, "arguments"));
    let template = target(&ns, &args[0], "Expression");
    assert_eq!(
        f(val(template), "parameters"),
        &Json::Arr(vec![parameter("z", "Z")])
    );
    assert_eq!(
        source(&checked, span(f(val(template), "location"))),
        b"eq(z+s.z)"
    );
    let call = target(&ns, &args[2], "Evaluation");
    let call_source = expression(&ns, call);
    assert_eq!(
        source(&checked, span(f(val(call_source), "location"))),
        b"eq(z+s.z)"
    );
    assert_eq!(
        arr(f(call_source, "arguments")).first(),
        Some(&reference(template))
    );
    let call_children = arr(f(&arr(f(val(call), "parts"))[0], "children"));
    assert_eq!(call_children.len(), 2);
    let callee = target(&ns, &call_children[1], "Evaluation");
    assert_eq!(
        source(&checked, span(f(val(expression(&ns, callee)), "location"))),
        b"a=a+1"
    );
    assert_ast(&wire, &checked, callee);
    let actual = target(&ns, &call_children[0], "Evaluation");
    assert_eq!(
        source(&checked, span(f(val(expression(&ns, actual)), "location"))),
        b"z+s.z"
    );
    assert!(!obj(val(actual)).contains_key("value"));
    assert_ast(&wire, &checked, evaluation);

    let example = counterexample(&wire, "a");
    let data = f(val(example), "data");
    let ce_args = arr(f(example, "arguments"));
    assert_eq!(ce_args.len(), 5);
    assert_eq!(&ce_args[0], &reference(template));
    let proof = target(&ns, &ce_args[1], "Evidence");
    assert_eq!(
        f(evaluation, "evidence"),
        &Json::Arr(vec![reference(proof)])
    );
    let normalization = f(val(proof), "data");
    assert_eq!(f(val(proof), "kind"), &Json::str("normalization"));
    assert_eq!(f(normalization, "before"), &reference(template));
    assert_eq!(f(normalization, "after"), f(val(evaluation), "value"));
    let difference_evaluation = target(&ns, &args[3], "Evaluation");
    let difference = expression(&ns, difference_evaluation);
    assert_eq!(f(val(difference), "operation"), &Json::str("difference"));
    assert_eq!(
        val(target(&ns, f(val(difference_evaluation), "value"), "Z")),
        &Json::str("-1")
    );
    let body_substitute = target(&ns, &ce_args[2], "Expression");
    assert_eq!(
        f(val(body_substitute), "operation"),
        &Json::str("substitute")
    );
    assert_eq!(
        f(val(body_substitute), "operands"),
        &Json::Arr(vec![reference(call_source)])
    );
    assert!(arr(f(val(body_substitute), "parameters")).is_empty());
    assert_eq!(
        f(normalization, "steps"),
        &Json::Arr(vec![reference(difference), reference(body_substitute)])
    );
    assert_eq!(
        f(proof, "arguments"),
        &Json::Arr(vec![
            reference(template),
            f(val(evaluation), "value").clone(),
            reference(difference),
            reference(body_substitute)
        ])
    );
    assert_eq!(f(val(body_substitute), "bindings"), f(data, "bindings"));
    let bindings = arr(f(data, "bindings"));
    assert_eq!(
        bindings
            .iter()
            .map(|b| text(f(b, "name")))
            .collect::<Vec<_>>(),
        ["s", "z"]
    );
    let zero = target(&ns, f(&bindings[1], "value"), "Z");
    assert_eq!(val(zero), &Json::str("0"));
    let mut substitute_arguments = vec![reference(call_source)];
    substitute_arguments.extend(bindings.iter().map(|b| f(b, "value").clone()));
    assert_eq!(
        f(body_substitute, "arguments"),
        &Json::Arr(substitute_arguments)
    );
    substitutions(&wire, proof);

    let operands = arr(f(val(difference), "operands"));
    assert_eq!(operands.len(), 2);
    for (position, ((key, side_ref), original_text)) in
        [("left", &ce_args[3]), ("right", &ce_args[4])]
            .into_iter()
            .zip([b"a".as_slice(), b"a+1".as_slice()])
            .enumerate()
    {
        assert_eq!(f(data, key), side_ref);
        let side = target(&ns, side_ref, "Evaluation");
        assert!(!obj(val(side)).contains_key("value"));
        assert!(arr(f(val(side), "bindings")).is_empty());
        let substitute = expression(&ns, side);
        assert_eq!(f(val(substitute), "operation"), &Json::str("substitute"));
        assert_eq!(
            f(val(substitute), "parameters"),
            &Json::Arr(vec![parameter("a", "Z")])
        );
        assert!(arr(f(val(substitute), "bindings")).is_empty());
        let original_ref = &arr(f(val(substitute), "operands"))[0];
        assert_eq!(&operands[position], original_ref);
        let original = target(&ns, original_ref, "Expression");
        assert_eq!(
            source(&checked, span(f(val(original), "location"))),
            original_text
        );
        assert_eq!(
            f(val(original), "parameters"),
            &Json::Arr(vec![parameter("a", "Z")])
        );
        assert_eq!(arr(f(substitute, "arguments")), &[original_ref.clone()]);
        let producers = arr(f(original, "arguments"));
        assert!(producers.contains(&reference(call_source)));
        assert!(
            producers.contains(&call_children[0]),
            "calleeは元実引数のproducerを保持する"
        );
        let side_args = arr(f(side, "arguments"));
        assert_eq!(side_args.len(), 2);
        assert_eq!(&side_args[0], &reference(substitute));
        let original_evaluation = target(&ns, &side_args[1], "Evaluation");
        assert_eq!(f(val(original_evaluation), "expression"), original_ref);
        assert!(!obj(val(original_evaluation)).contains_key("value"));
        let parts = arr(f(val(side), "parts"));
        assert_eq!(parts.len(), 1);
        assert_eq!(
            f(&parts[0], "children"),
            &Json::Arr(vec![side_args[1].clone()])
        );
        assert_eq!(
            span(f(&parts[0], "location")),
            span(f(val(original), "location"))
        );
        assert!(!obj(&parts[0]).contains_key("value"));
        for supported in arr(f(actual, "support")) {
            assert!(arr(f(side, "support")).contains(supported));
            assert!(arr(f(evaluation, "support")).contains(supported));
        }
        let side_missing = arr(f(side, "reasons"))
            .iter()
            .filter(|reason| f(reason, "code") == &Json::str("missing_observation"))
            .flat_map(|reason| arr(f(reason, "missing")))
            .map(Json::canonical)
            .collect::<BTreeSet<_>>();
        assert_eq!(side_missing, BTreeSet::from([fact("z").canonical()]));
    }
    assert_eq!(f(example, "support"), f(evaluation, "support"));
    assert_eq!(f(example, "scope"), f(evaluation, "scope"));
}
