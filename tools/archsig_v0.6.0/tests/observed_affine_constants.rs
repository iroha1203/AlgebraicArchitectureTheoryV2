//! 欠測 Z/Q の共有アフィン算術を三入力 byte から検査する。
mod common;

use archsig::{
    archmap::Slot,
    canonical::Json,
    definition::check_definitions_controlled,
    law::{ast::ExprKind, model::Signature},
    observed::{
        control::{Checkpoint, Control, Limits, Usage},
        evaluate_observed_bytes,
        input::{CheckedInputs, InputSources, InputStatus, check_inputs},
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
fn index(wire: &Json) -> BTreeMap<&str, &Json> {
    arr(f(wire, "nodes"))
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
        &Json::str("Evaluation"),
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
        Json::Arr(v) => {
            for v in v {
                refs(v, out);
            }
        }
        _ => {}
    }
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
fn at(ns: &BTreeMap<&str, &Json>, evaluation: &Json) -> (usize, usize) {
    span(f(val(expression(ns, evaluation)), "location"))
}
fn source(checked: &CheckedInputs, at: (usize, usize)) -> &[u8] {
    &checked.sources().law().bytes()[at.0..at.1]
}
fn live<'a>(ns: &BTreeMap<&str, &'a Json>, root: &'a Json) -> Vec<&'a Json> {
    let mut todo = vec![root];
    let mut seen = BTreeSet::new();
    let mut result = vec![];
    while let Some(e) = todo.pop() {
        assert_eq!(f(e, "type"), &Json::str("Evaluation"));
        if seen.insert(text(f(e, "id"))) {
            result.push(e);
            for p in arr(f(val(e), "parts")) {
                for child in arr(f(p, "children")) {
                    todo.push(target(ns, child, &Json::str("Evaluation")));
                }
            }
        }
    }
    result
}
fn evaluations_at<'a>(wire: &'a Json, at_span: (usize, usize)) -> Vec<&'a Json> {
    let ns = index(wire);
    arr(f(wire, "nodes"))
        .iter()
        .filter(|n| f(n, "type") == &Json::str("Evaluation") && at(&ns, n) == at_span)
        .collect()
}
fn body(checked: &CheckedInputs, name: &str) -> usize {
    let (Signature::View { body, .. } | Signature::Law { body, .. }) =
        &checked.law().declarations[name].signature
    else {
        panic!("view/law")
    };
    *body
}
fn q(n: &str, d: &str) -> Json {
    Json::Arr(vec![Json::str(n), Json::str(d)])
}
fn fact(snapshot: &str, subject: &str, field: &str) -> Json {
    Json::obj([
        ("snapshot", Json::str(snapshot)),
        ("subject", Json::str(subject)),
        ("field", Json::str(format!("Affine.Sample.{field}"))),
    ])
}

// Z/Q は常に欠測。Bool だけを必要な試験で二つの全補完へ分ける。
fn fixture(
    script: &str,
    missing_bool: bool,
    peer: bool,
    second_snapshot: bool,
    moved: bool,
) -> InputSources {
    use common::{definition_json, entity_json, field_json, vocabulary_json};
    let root = entity_json("Affine.Root", "[]", "[]");
    let fields = [
        ("z", "Z"),
        ("k", "Z"),
        ("q", "Q"),
        ("r", "Q"),
        ("p", "Bool"),
        ("known", "Bool"),
        ("knownz", "Z"),
        ("knownq", "Q"),
    ]
    .iter()
    .map(|(n, t)| field_json(n, &Json::str(*t).canonical()))
    .collect::<Vec<_>>()
    .join(",");
    let sample = entity_json(
        "Affine.Sample",
        &format!("[{}]", field_json("owner", r#"["Ref","Affine.Root"]"#)),
        &format!("[{fields}]"),
    );
    let definitions = definition_json(&format!(
        "[{}]",
        vocabulary_json("Affine", &format!("[{root},{sample}]"), "[]")
    ));
    let checked =
        check_definitions_controlled(&[("definition0", definitions.as_bytes())], &mut quiet())
            .unwrap();
    let digest = &checked.vocabularies["Affine"].digest;
    let law = format!(
        r#"law "archsig.law/2" semantics "archsig/0.6.0"; reading Calc {{ use vocabulary Affine version "1" digest "{digest}"; {script} }}"#
    );
    let suffix = if moved { "_moved" } else { "" };
    let shift = if moved { 10 } else { 0 };
    let mut origins = vec![];
    let mut snapshots = vec![];
    for (snapshot, mode) in [("v", "specification"), ("w", "proposed")] {
        if snapshot == "w" && !second_snapshot {
            continue;
        }
        for (kind, start) in [("snapshot", 0), ("subjects", 2), ("values", 4)] {
            origins.push(format!(r#"{{"id":"{snapshot}_{kind}{suffix}","mode":"{mode}","method":"小さい算術例の入力。","locations":[{{"source":"scan{suffix}","path":"{snapshot}.{kind}.model","span":[{},{}]}}]}}"#, start+shift, start+shift+1));
        }
        let mut subjects = vec![format!(
            r#"{{"id":"root","type":"Affine.Root","origin":"{snapshot}_subjects{suffix}"}}"#
        )];
        let mut atoms = vec![];
        for subject in if peer {
            vec!["item", "peer"]
        } else {
            vec!["item"]
        } {
            subjects.push(format!(r#"{{"id":"{subject}","type":"Affine.Sample","origin":"{snapshot}_subjects{suffix}"}}"#));
            for (name, value) in [
                (
                    "owner",
                    Json::Arr(vec![Json::str(snapshot), Json::str("root")]),
                ),
                ("p", Json::Bool(false)),
                ("known", Json::Bool(false)),
                ("knownz", Json::str("7")),
                ("knownq", q("1", "2")),
            ] {
                if name == "p" && missing_bool {
                    continue;
                }
                atoms.push(format!(r#"{{"id":"{subject}_{name}","subject":"{subject}","field":"Affine.Sample.{name}","value":{},"origin":"{snapshot}_values{suffix}"}}"#,value.canonical()));
            }
        }
        snapshots.push(format!(r#"{{"id":"{snapshot}","origin":"{snapshot}_snapshot{suffix}","subjects":[{}],"atoms":[{}]}}"#,subjects.join(","),atoms.join(",")));
    }
    let uri = if moved {
        "urn:fixture:affine-constants:relocated"
    } else {
        "urn:fixture:affine-constants"
    };
    let revision = if moved { "r2" } else { "r1" };
    let map = format!(
        r#"{{"format":"archsig.archmap/2","semantics":"archsig/0.6.0","vocabularies":[{{"namespace":"Affine","version":"1","digest":"{digest}"}}],"sources":[{{"id":"scan{suffix}","uri":"{uri}","revision":"{revision}","digest":"sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"}}],"origins":[{}],"snapshots":[{}]}}"#,
        origins.join(","),
        snapshots.join(",")
    );
    InputSources::from_bytes(
        vec![definitions.into_bytes()],
        law.into_bytes(),
        map.into_bytes(),
    )
}
fn simple(script: &str) -> InputSources {
    fixture(script, false, false, false, false)
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
    assert_eq!(evaluated.prepared().inputs().sources(), &inputs);
    assert_eq!(
        evaluated.prepared().inputs().sources().archmap().bytes(),
        inputs.archmap().bytes()
    );
    assert_eq!(
        evaluated.prepared().inputs().archmap().snapshots,
        checked.archmap().snapshots,
        "記号や補完値を観測Atom、owner、既知slotへ追加しない"
    );
    let wire = evaluated.wire();
    audit(&wire, &checked);
    (wire, checked)
}
fn output(wire: &Json, id: &str, ty: &str, expected: Json) {
    let a = answer(wire, id);
    assert_eq!(
        f(a, "status"),
        &Json::str("established"),
        "{id}: {:?}",
        f(wire, "issues")
    );
    assert!(!obj(a).contains_key("claim"), "値の問いはLaw判断を作らない");
    assert_eq!(
        val(target(
            &index(wire),
            f(f(a, "outputs"), "value"),
            &Json::str(ty)
        )),
        &expected
    );
}
fn missing(wire: &Json, id: &str, wanted: &[Json]) {
    let actual = arr(f(answer(wire, id), "reasons"))
        .iter()
        .filter(|r| f(r, "code") == &Json::str("missing_observation"))
        .flat_map(|r| {
            assert!(!arr(f(r, "dependencies")).is_empty());
            arr(f(r, "missing"))
        })
        .map(Json::canonical)
        .collect::<BTreeSet<_>>();
    assert_eq!(
        actual,
        wanted.iter().map(Json::canonical).collect(),
        "{id}の元missing identity"
    );
}
fn undetermined(wire: &Json, id: &str, wanted: &[Json]) {
    let a = answer(wire, id);
    assert_eq!(f(a, "status"), &Json::str("undetermined"));
    assert!(!obj(f(a, "outputs")).contains_key("value"));
    assert!(!obj(a).contains_key("claim"));
    missing(wire, id, wanted);
    for n in arr(f(wire, "nodes")) {
        if f(n, "type") == &Json::str("Evidence") {
            assert_ne!(
                f(val(n), "kind"),
                &Json::str("counterexample"),
                "未確定hへ仮の値を代入しない"
            );
        }
    }
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
        if f(n, "type") == &Json::str("Expression") && f(val(n), "kind") == &Json::str("source") {
            let position = span(f(val(n), "location"));
            assert!(position.0 < position.1 && position.1 <= checked.sources().law().bytes().len());
            assert_eq!(span(f(f(n, "rule"), "location")), position);
        }
        if f(n, "type") == &Json::str("Domain") && f(val(n), "kind") == &Json::str("finite") {
            assert_ne!(
                f(val(n), "type"),
                &Json::str("Z"),
                "Zを有限補完域へ入れない"
            );
            assert_ne!(
                f(val(n), "type"),
                &Json::str("Q"),
                "Qを有限補完域へ入れない"
            );
            for member in arr(f(val(n), "elements")) {
                val(target(&ns, member, f(val(n), "type")));
            }
        }
        if f(n, "type") != &Json::str("Evaluation") {
            continue;
        }
        for binding in arr(f(val(n), "bindings")) {
            let scalar = ns[text(f(f(binding, "value"), "node"))];
            let declared_types = checked
                .law()
                .declarations
                .values()
                .filter_map(|d| match &d.signature {
                    Signature::View { params, .. } | Signature::Law { params, .. } => Some(params),
                    _ => None,
                })
                .flatten()
                .filter(|p| p.name == text(f(binding, "name")))
                .map(|p| p.ty.wire())
                .collect::<Vec<_>>();
            assert!(
                declared_types.contains(f(scalar, "type")),
                "通常Bindingは元parameterの型を持つ"
            );
            val(scalar); // 欠測formを通常Bindingへ入れない。
        }
        let expression = expression(&ns, n);
        let completion_aggregate = arr(f(n, "arguments"))
            .get(1)
            .is_some_and(|r| f(ns[text(f(r, "node"))], "type") == &Json::str("Domain"));
        if !completion_aggregate && f(val(expression), "kind") == &Json::str("source") {
            let position = at(&ns, n);
            if let Some((id, expr)) = checked
                .law()
                .exprs
                .iter()
                .enumerate()
                .find(|(_, e)| e.span == position)
            {
                if let Some(value) = obj(val(n)).get("value") {
                    target(&ns, value, &checked.law().expr_type(id).unwrap().wire());
                }
                for part in arr(f(val(n), "parts"))
                    .iter()
                    .filter(|p| span(f(p, "location")) == position)
                {
                    if let Some(value) = obj(part).get("value") {
                        target(&ns, value, &checked.law().expr_type(id).unwrap().wire());
                    }
                    let expected = match &expr.kind {
                        ExprKind::Binary { lhs, rhs, .. } => vec![
                            checked.law().exprs[*lhs].span,
                            checked.law().exprs[*rhs].span,
                        ],
                        ExprKind::Unary { operand, .. }
                        | ExprKind::Group(operand)
                        | ExprKind::Field { base: operand, .. } => {
                            vec![checked.law().exprs[*operand].span]
                        }
                        ExprKind::Let { value, body, .. } => vec![
                            checked.law().exprs[*value].span,
                            checked.law().exprs[*body].span,
                        ],
                        ExprKind::If {
                            cond,
                            then_branch,
                            else_branch,
                        } => vec![
                            checked.law().exprs[*cond].span,
                            checked.law().exprs[*then_branch].span,
                            checked.law().exprs[*else_branch].span,
                        ],
                        _ => vec![],
                    };
                    if !expected.is_empty() {
                        let actual = arr(f(part, "children"))
                            .iter()
                            .map(|r| at(&ns, target(&ns, r, &Json::str("Evaluation"))))
                            .collect::<Vec<_>>();
                        assert_eq!(actual, expected, "元ASTの子を左右・単項・let・ifの順で保持");
                    }
                }
            }
        }
        for part in arr(f(val(n), "parts")) {
            for child in arr(f(part, "children")) {
                let child = target(&ns, child, &Json::str("Evaluation"));
                for support in arr(f(child, "support")) {
                    assert!(arr(f(n, "support")).contains(support));
                }
            }
        }
    }
    for a in arr(f(wire, "answers")) {
        let mut edges = vec![];
        refs(a, &mut edges);
        for edge in edges {
            assert!(ns.contains_key(edge.as_str()));
        }
        if let Some(claim) = obj(a).get("claim") {
            let claim = target(&ns, claim, &Json::str("Proposition"));
            assert_eq!(f(f(claim, "judgment"), "status"), f(a, "status"));
            assert_eq!(f(claim, "scope"), f(a, "scope"));
        }
        for reason in arr(f(a, "reasons"))
            .iter()
            .filter(|r| f(r, "code") == &Json::str("missing_observation"))
        {
            for dependency in arr(f(reason, "dependencies")) {
                let source = target(&ns, dependency, &Json::str("Expression"));
                assert_eq!(f(val(source), "kind"), &Json::str("source"));
                assert_eq!(f(val(source), "location"), f(reason, "location"));
            }
            for missing in arr(f(reason, "missing")) {
                assert!(!obj(missing).contains_key("atom"));
                let snapshot = checked
                    .archmap()
                    .snapshots
                    .iter()
                    .find(|s| s.id == text(f(missing, "snapshot")))
                    .unwrap();
                let subject = snapshot
                    .subjects
                    .iter()
                    .find(|s| s.id == text(f(missing, "subject")))
                    .unwrap();
                let field = subject
                    .fields
                    .iter()
                    .find(|s| s.name == text(f(missing, "field")))
                    .unwrap();
                assert!(matches!(field.slot, Slot::Missing));
            }
        }
    }
}
fn audit_fact(support: &Json, node: &Json, checked: &CheckedInputs) {
    let snapshot = checked
        .archmap()
        .snapshots
        .iter()
        .find(|s| s.id == text(f(support, "snapshot")))
        .unwrap();
    let subject = snapshot
        .subjects
        .iter()
        .find(|s| s.id == text(f(support, "subject")))
        .unwrap();
    assert!(arr(f(f(node, "scope"), "snapshots")).contains(f(support, "snapshot")));
    let (origin_id, kind, start) = if let Some(field) = obj(support).get("field") {
        let field = subject
            .fields
            .iter()
            .find(|s| s.name == text(field))
            .unwrap();
        match &field.slot {
            Slot::Known { atom, origin, .. } => {
                assert_eq!(f(support, "atom"), &Json::str(atom));
                (origin, "values", 4)
            }
            Slot::Missing => {
                assert!(!obj(support).contains_key("atom"));
                (&subject.origin, "subjects", 2)
            }
        }
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
    let snapshot_origin = checked
        .archmap()
        .origins
        .iter()
        .find(|o| o.id == snapshot.origin)
        .unwrap();
    assert_eq!(origin.mode, snapshot_origin.mode);
    assert!(
        arr(f(f(node, "scope"), "modes")).contains(&Json::str(if snapshot.id == "v" {
            "specification"
        } else {
            "proposed"
        }))
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
            "urn:fixture:affine-constants"
        } else {
            "urn:fixture:affine-constants:relocated"
        }
    );
    assert_eq!(origin.id.ends_with("_moved"), shift == 10);
    assert_eq!(source.id, if shift == 0 { "scan" } else { "scan_moved" });
}
fn complete_ast(wire: &Json, checked: &CheckedInputs, id: &str, declaration: &str) {
    let ns = index(wire);
    let reached = live(&ns, root(wire, id));
    let declaration = &checked.law().declarations[declaration];
    for (expr_id, expr) in checked
        .law()
        .exprs
        .iter()
        .enumerate()
        .filter(|(_, e)| declaration.span.0 <= e.span.0 && e.span.1 <= declaration.span.1)
    {
        if checked.law().expr_type(expr_id).is_none() {
            continue;
        }
        assert!(
            reached.iter().any(|e| at(&ns, e) == expr.span),
            "元AST出現 {:?}: {:?}",
            expr.span,
            source(checked, expr.span)
        );
    }
}
fn missing_field_evaluations(wire: &Json, checked: &CheckedInputs, field: &str) -> usize {
    let ns = index(wire);
    let mut count = 0;
    for n in arr(f(wire, "nodes"))
        .iter()
        .filter(|n| f(n, "type") == &Json::str("Evaluation"))
    {
        let expr = expression(&ns, n);
        if f(val(expr), "kind") != &Json::str("source")
            || source(checked, at(&ns, n)) != format!("s.{field}").as_bytes()
        {
            continue;
        }
        if arr(f(n, "reasons"))
            .iter()
            .any(|r| f(r, "code") == &Json::str("missing_observation"))
            && !obj(val(n)).contains_key("value")
        {
            assert_eq!(f(f(n, "scope"), "domain"), &Json::str("all_completions"));
            assert!(
                arr(f(n, "support")).iter().any(|support| {
                    f(support, "snapshot") == &Json::str("v")
                        && f(support, "subject") == &Json::str("item")
                        && !obj(support).contains_key("field")
                        && !obj(support).contains_key("atom")
                }),
                "欠測fieldの元subject支持を保つ"
            );
            assert!(arr(f(n, "reasons")).iter().any(|r| {
                f(r, "code") == &Json::str("missing_observation")
                    && arr(f(r, "missing"))
                        .iter()
                        .any(|m| f(m, "field") == &Json::str(format!("Affine.Sample.{field}")))
            }));
            count += 1;
        }
    }
    count
}
fn affine_scalar(
    wire: &Json,
    checked: &CheckedInputs,
    expression_text: &str,
    ty: &str,
    expected: Json,
) {
    let ns = index(wire);
    let nodes = arr(f(wire, "nodes"))
        .iter()
        .filter(|n| {
            f(n, "type") == &Json::str("Evaluation")
                && source(checked, at(&ns, n)) == expression_text.as_bytes()
        })
        .collect::<Vec<_>>();
    assert!(!nodes.is_empty(), "定数導出の元式: {expression_text}");
    for n in nodes {
        let scalar = target(&ns, f(val(n), "value"), &Json::str(ty));
        assert_eq!(val(scalar), &expected);
        assert_eq!(f(f(scalar, "rule"), "kind"), &Json::str("law"));
        assert_eq!(span(f(f(scalar, "rule"), "location")), at(&ns, n));
        let part = arr(f(val(n), "parts"))
            .iter()
            .find(|p| span(f(p, "location")) == at(&ns, n))
            .unwrap();
        let mut expected_args = vec![f(val(n), "expression").clone()];
        expected_args.extend(arr(f(part, "children")).iter().cloned());
        assert_eq!(
            f(scalar, "arguments"),
            &Json::Arr(expected_args),
            "新Scalarはown元Sourceと実子Evaluationを消費"
        );
        assert_eq!(f(scalar, "support"), f(n, "support"));
        assert_eq!(f(scalar, "scope"), f(n, "scope"));
    }
}

#[test]
fn missing_z_subtraction_derives_zero_without_observing_the_field() {
    let (wire, checked) = run(
        simple("view delta(s:Sample): Z = s.z-s.z;"),
        &["a=evaluate(Calc.delta,s=@v/item)"],
    );
    output(&wire, "a", "Z", Json::str("0"));
    missing(&wire, "a", &[fact("v", "item", "z")]);
    assert_eq!(missing_field_evaluations(&wire, &checked, "z"), 2);
    affine_scalar(&wire, &checked, "s.z-s.z", "Z", Json::str("0"));
    complete_ast(&wire, &checked, "a", "Calc.delta");
}

#[test]
fn missing_q_subtraction_derives_reduced_typed_zero() {
    let (wire, checked) = run(
        simple("view delta(s:Sample): Q = s.q-s.q;"),
        &["a=evaluate(Calc.delta,s=@v/item)"],
    );
    output(&wire, "a", "Q", q("0", "1"));
    missing(&wire, "a", &[fact("v", "item", "q")]);
    assert_eq!(missing_field_evaluations(&wire, &checked, "q"), 2);
    affine_scalar(&wire, &checked, "s.q-s.q", "Q", q("0", "1"));
    complete_ast(&wire, &checked, "a", "Calc.delta");
}

#[test]
fn missing_z_collects_nontrivial_coefficients_before_constant_extraction() {
    let (wire, checked) = run(
        simple("view delta(s:Sample): Z = (2*s.z+3)-s.z-s.z;"),
        &["a=evaluate(Calc.delta,s=@v/item)"],
    );
    output(&wire, "a", "Z", Json::str("3"));
    missing(&wire, "a", &[fact("v", "item", "z")]);
    assert_eq!(missing_field_evaluations(&wire, &checked, "z"), 3);
    affine_scalar(&wire, &checked, "(2*s.z+3)-s.z-s.z", "Z", Json::str("3"));
    complete_ast(&wire, &checked, "a", "Calc.delta");
}

#[test]
fn missing_q_collects_nonzero_fractional_coefficients() {
    let (wire, checked) = run(
        simple("view delta(s:Sample): Q = (rat(1,2)*s.q+rat(3,4))-rat(1,2)*s.q;"),
        &["a=evaluate(Calc.delta,s=@v/item)"],
    );
    output(&wire, "a", "Q", q("3", "4"));
    missing(&wire, "a", &[fact("v", "item", "q")]);
    affine_scalar(
        &wire,
        &checked,
        "(rat(1,2)*s.q+rat(3,4))-rat(1,2)*s.q",
        "Q",
        q("3", "4"),
    );
    complete_ast(&wire, &checked, "a", "Calc.delta");
}

#[test]
fn missing_q_half_offsets_reduce_to_one_with_positive_denominator() {
    let (wire, checked) = run(
        simple("view delta(s:Sample): Q = ((s.q+rat(1,2))+rat(1,2))-s.q;"),
        &["a=evaluate(Calc.delta,s=@v/item)"],
    );
    output(&wire, "a", "Q", q("1", "1"));
    missing(&wire, "a", &[fact("v", "item", "q")]);
    affine_scalar(
        &wire,
        &checked,
        "((s.q+rat(1,2))+rat(1,2))-s.q",
        "Q",
        q("1", "1"),
    );
    complete_ast(&wire, &checked, "a", "Calc.delta");
}

#[test]
fn missing_z_zero_multiplication_and_negation_keep_original_children() {
    let script = "view zero(s:Sample): Z = 0*s.z; view negate(s:Sample): Z = -s.z+s.z;";
    let (wire, checked) = run(
        simple(script),
        &[
            "zero=evaluate(Calc.zero,s=@v/item)",
            "neg=evaluate(Calc.negate,s=@v/item)",
        ],
    );
    for id in ["zero", "neg"] {
        output(&wire, id, "Z", Json::str("0"));
        missing(&wire, id, &[fact("v", "item", "z")]);
    }
    affine_scalar(&wire, &checked, "0*s.z", "Z", Json::str("0"));
    affine_scalar(&wire, &checked, "-s.z+s.z", "Z", Json::str("0"));
    for (id, name) in [("zero", "Calc.zero"), ("neg", "Calc.negate")] {
        complete_ast(&wire, &checked, id, name);
    }
}

#[test]
fn missing_q_zero_multiplication_and_negation_keep_q_type() {
    let script = "view zero(s:Sample): Q = s.q*0; view negate(s:Sample): Q = -s.q+s.q;";
    let (wire, checked) = run(
        simple(script),
        &[
            "zero=evaluate(Calc.zero,s=@v/item)",
            "neg=evaluate(Calc.negate,s=@v/item)",
        ],
    );
    for id in ["zero", "neg"] {
        output(&wire, id, "Q", q("0", "1"));
        missing(&wire, id, &[fact("v", "item", "q")]);
    }
    affine_scalar(&wire, &checked, "s.q*0", "Q", q("0", "1"));
    affine_scalar(&wire, &checked, "-s.q+s.q", "Q", q("0", "1"));
    for (id, name) in [("zero", "Calc.zero"), ("neg", "Calc.negate")] {
        complete_ast(&wire, &checked, id, name);
    }
}

#[test]
fn missing_z_uses_exact_coefficients_and_constants_above_i64() {
    // 固定した短い整数。係数と定数の双方を i64 の外で手計算する。
    let (wire, checked) = run(
        simple(
            "view delta(s:Sample): Z = (9223372036854775808*s.z+9223372036854775809)-9223372036854775808*s.z;",
        ),
        &["a=evaluate(Calc.delta,s=@v/item)"],
    );
    output(&wire, "a", "Z", Json::str("9223372036854775809"));
    affine_scalar(
        &wire,
        &checked,
        "(9223372036854775808*s.z+9223372036854775809)-9223372036854775808*s.z",
        "Z",
        Json::str("9223372036854775809"),
    );
    complete_ast(&wire, &checked, "a", "Calc.delta");
}

fn comparison_case(ty: &str, field: &str, expected: bool) {
    let rhs = if expected { "0" } else { "1" };
    let script = format!(
        "view comparison(s:Sample): Bool = s.{field}-s.{field}={rhs}; law required requirement(s:Sample): s.{field}-s.{field}={rhs};"
    );
    let (wire, checked) = run(
        simple(&script),
        &[
            "value=evaluate(Calc.comparison,s=@v/item)",
            "requirement=check(Calc.requirement,s=@v/item)",
        ],
    );
    output(&wire, "value", "Bool", Json::Bool(expected));
    let a = answer(&wire, "requirement");
    assert_eq!(
        f(a, "status"),
        &Json::str(if expected { "established" } else { "refuted" })
    );
    assert_eq!(f(&wire, "status"), &Json::str("complete"));
    let ns = index(&wire);
    let claim = target(&ns, f(a, "claim"), &Json::str("Proposition"));
    assert_eq!(f(val(claim), "predicate"), &Json::str("law_holds"));
    assert_eq!(f(f(claim, "judgment"), "status"), f(a, "status"));
    let encode = |z: &str| if ty == "Q" { q(z, "1") } else { Json::str(z) };
    let evidence = arr(f(a, "evidence"))
        .iter()
        .map(|r| val(target(&ns, r, &Json::str("Evidence"))))
        .collect::<Vec<_>>();
    let checked_equality = evidence
        .iter()
        .find(|e| f(e, "kind") == &Json::str("evaluation"))
        .unwrap();
    let data = f(checked_equality, "data");
    assert_ne!(
        f(data, "lhs"),
        f(data, "rhs"),
        "元左右の実Scalarを交換しない"
    );
    for (key, wanted) in [
        ("lhs", encode("0")),
        ("rhs", encode(rhs)),
        ("residual", encode(if expected { "0" } else { "-1" })),
    ] {
        assert_eq!(val(target(&ns, f(data, key), &Json::str(ty))), &wanted);
    }
    let counter = evidence
        .iter()
        .filter(|e| f(e, "kind") == &Json::str("counterexample"))
        .collect::<Vec<_>>();
    assert_eq!(counter.len(), usize::from(!expected));
    if !expected {
        let counter = f(counter[0], "data");
        assert_eq!(f(counter, "left"), f(data, "lhs"));
        assert_eq!(f(counter, "right"), f(data, "rhs"));
        assert_eq!(
            val(target(&ns, f(counter, "left"), &Json::str(ty))),
            &encode("0")
        );
        assert_eq!(
            val(target(&ns, f(counter, "right"), &Json::str(ty))),
            &encode("1")
        );
    }
    for id in ["value", "requirement"] {
        missing(&wire, id, &[fact("v", "item", field)]);
    }
    assert_eq!(missing_field_evaluations(&wire, &checked, field), 4);
    complete_ast(&wire, &checked, "value", "Calc.comparison");
}

#[test]
fn missing_z_zero_comparison_is_true_and_required_law_is_established() {
    comparison_case("Z", "z", true);
}
#[test]
fn missing_z_one_comparison_is_false_with_typed_residual_and_counterexample() {
    comparison_case("Z", "z", false);
}
#[test]
fn missing_q_zero_comparison_is_true_and_required_law_is_established() {
    comparison_case("Q", "q", true);
}
#[test]
fn missing_q_one_comparison_is_false_with_typed_residual_and_counterexample() {
    comparison_case("Q", "q", false);
}

#[test]
fn missing_z_nonconstants_and_separate_fields_remain_undetermined() {
    let script = "view subtract(s:Sample): Z = 2-s.z; view equality(s:Sample): Bool = s.z=0; view separate(s:Sample): Z = s.z-s.k;";
    let (wire, checked) = run(
        simple(script),
        &[
            "sub=evaluate(Calc.subtract,s=@v/item)",
            "eq=evaluate(Calc.equality,s=@v/item)",
            "separate=evaluate(Calc.separate,s=@v/item)",
        ],
    );
    undetermined(&wire, "sub", &[fact("v", "item", "z")]);
    undetermined(&wire, "eq", &[fact("v", "item", "z")]);
    undetermined(
        &wire,
        "separate",
        &[fact("v", "item", "z"), fact("v", "item", "k")],
    );
    for (id, name) in [
        ("sub", "Calc.subtract"),
        ("eq", "Calc.equality"),
        ("separate", "Calc.separate"),
    ] {
        complete_ast(&wire, &checked, id, name);
    }
}

#[test]
fn missing_q_nonconstants_and_separate_fields_remain_undetermined() {
    let script = "view subtract(s:Sample): Q = 2-s.q; view equality(s:Sample): Bool = s.q=0; view separate(s:Sample): Q = s.q-s.r;";
    let (wire, checked) = run(
        simple(script),
        &[
            "sub=evaluate(Calc.subtract,s=@v/item)",
            "eq=evaluate(Calc.equality,s=@v/item)",
            "separate=evaluate(Calc.separate,s=@v/item)",
        ],
    );
    undetermined(&wire, "sub", &[fact("v", "item", "q")]);
    undetermined(&wire, "eq", &[fact("v", "item", "q")]);
    undetermined(
        &wire,
        "separate",
        &[fact("v", "item", "q"), fact("v", "item", "r")],
    );
    for (id, name) in [
        ("sub", "Calc.subtract"),
        ("eq", "Calc.equality"),
        ("separate", "Calc.separate"),
    ] {
        complete_ast(&wire, &checked, id, name);
    }
}

#[test]
fn unknown_nonlinear_products_are_not_affine_constants() {
    let script = "view integer(s:Sample): Z = s.z*s.z-s.z*s.z; view rational(s:Sample): Q = s.q*s.q-s.q*s.q;";
    let (wire, checked) = run(
        simple(script),
        &[
            "z=evaluate(Calc.integer,s=@v/item)",
            "q=evaluate(Calc.rational,s=@v/item)",
        ],
    );
    undetermined(&wire, "z", &[fact("v", "item", "z")]);
    undetermined(&wire, "q", &[fact("v", "item", "q")]);
    complete_ast(&wire, &checked, "z", "Calc.integer");
    complete_ast(&wire, &checked, "q", "Calc.rational");
}

#[test]
fn known_nonlinear_values_and_bool_short_circuits_keep_original_support() {
    let script = "view integer(s:Sample): Z = s.knownz*s.knownz; view rational(s:Sample): Q = s.knownq*s.knownq; view flag(s:Sample): Bool = false and (s.z=0);";
    let (wire, checked) = run(
        simple(script),
        &[
            "z=evaluate(Calc.integer,s=@v/item)",
            "q=evaluate(Calc.rational,s=@v/item)",
            "flag=evaluate(Calc.flag,s=@v/item)",
        ],
    );
    output(&wire, "z", "Z", Json::str("49"));
    output(&wire, "q", "Q", q("1", "4"));
    output(&wire, "flag", "Bool", Json::Bool(false));
    missing(&wire, "flag", &[fact("v", "item", "z")]);
    let ns = index(&wire);
    for (id, field) in [("z", "knownz"), ("q", "knownq")] {
        assert!(
            arr(f(root(&wire, id), "support"))
                .iter()
                .any(
                    |s| obj(s).get("field") == Some(&Json::str(format!("Affine.Sample.{field}")))
                        && obj(s).get("atom") == Some(&Json::str(format!("item_{field}")))
                )
        );
        assert_eq!(
            f(f(root(&wire, id), "scope"), "domain"),
            &Json::str("finite_model")
        );
    }
    assert!(
        live(&ns, root(&wire, "flag"))
            .iter()
            .any(|e| source(&checked, at(&ns, e)) == b"s.z" && !obj(val(e)).contains_key("value"))
    );
    for (id, name) in [
        ("z", "Calc.integer"),
        ("q", "Calc.rational"),
        ("flag", "Calc.flag"),
    ] {
        complete_ast(&wire, &checked, id, name);
    }
}

#[test]
fn affine_z_and_q_are_not_implicitly_coerced() {
    let inputs = simple("view wrong(s:Sample): Q = s.z-s.z;");
    let failure = check_inputs(inputs, &mut quiet()).unwrap_err();
    assert_eq!(failure.status(), InputStatus::Invalid);
    assert!(
        failure
            .issues()
            .iter()
            .any(|issue| f(issue, "code") == &Json::str("type"))
    );
}

#[test]
fn uncancelled_missing_laws_keep_undetermined_claims_without_fictitious_counterexamples() {
    let script = "law required integer(s:Sample): s.z=0; law required rational(s:Sample): s.q=0;";
    let (wire, _) = run(
        simple(script),
        &[
            "z=check(Calc.integer,s=@v/item)",
            "q=check(Calc.rational,s=@v/item)",
        ],
    );
    let ns = index(&wire);
    for (id, field) in [("z", "z"), ("q", "q")] {
        let a = answer(&wire, id);
        assert_eq!(f(a, "status"), &Json::str("undetermined"));
        let claim = target(&ns, f(a, "claim"), &Json::str("Proposition"));
        assert_eq!(
            f(f(claim, "judgment"), "status"),
            &Json::str("undetermined")
        );
        assert!(arr(f(a, "evidence")).is_empty());
        assert!(arr(f(claim, "evidence")).is_empty());
        assert!(!obj(val(root(&wire, id))).contains_key("value"));
        missing(&wire, id, &[fact("v", "item", field)]);
    }
    assert!(arr(f(&wire, "nodes")).iter().all(|n| {
        f(n, "type") != &Json::str("Evidence") || f(val(n), "kind") != &Json::str("counterexample")
    }));
}

fn call_children<'a>(ns: &BTreeMap<&str, &'a Json>, evaluation: &Json) -> Vec<&'a Json> {
    let position = at(ns, evaluation);
    let part = arr(f(val(evaluation), "parts"))
        .iter()
        .find(|p| span(f(p, "location")) == position)
        .unwrap();
    arr(f(part, "children"))
        .iter()
        .map(|r| target(ns, r, &Json::str("Evaluation")))
        .collect()
}
fn shared_through_call(ty: &str, field: &str, parameter: &str) {
    let script = format!(
        "view carry({parameter}:{ty}): {ty} = let held={parameter} in held; view delta(s:Sample): {ty} = let saved=s.{field} in carry(saved)-carry(s.{field});"
    );
    let (wire, checked) = run(simple(&script), &["a=evaluate(Calc.delta,s=@v/item)"]);
    let zero = if ty == "Q" {
        q("0", "1")
    } else {
        Json::str("0")
    };
    output(&wire, "a", ty, zero.clone());
    missing(&wire, "a", &[fact("v", "item", field)]);
    complete_ast(&wire, &checked, "a", "Calc.delta");
    affine_scalar(
        &wire,
        &checked,
        &format!("carry(saved)-carry(s.{field})"),
        ty,
        zero,
    );
    let ns = index(&wire);
    let calls = live(&ns, root(&wire, "a"))
        .into_iter()
        .filter(|e| {
            let bytes = source(&checked, at(&ns, e));
            bytes == b"carry(saved)" || bytes == format!("carry(s.{field})").as_bytes()
        })
        .collect::<Vec<_>>();
    assert_eq!(calls.len(), 2);
    assert_ne!(f(calls[0], "id"), f(calls[1], "id"));
    let mut producer_ids = BTreeSet::new();
    for call in calls {
        assert!(
            !obj(val(call)).contains_key("value"),
            "未知返り値を通常Scalarへ入れない"
        );
        let children = call_children(&ns, call);
        assert_eq!(children.len(), 2, "実引数Evaluationの後に元view body");
        assert!(producer_ids.insert(text(f(children[0], "id"))));
        assert_eq!(
            source(&checked, at(&ns, children[1])),
            format!("let held={parameter} in held").as_bytes()
        );
        let formal_uses = live(&ns, children[1])
            .into_iter()
            .filter(|e| source(&checked, at(&ns, e)) == parameter.as_bytes())
            .collect::<Vec<_>>();
        assert_eq!(formal_uses.len(), 1);
        assert_eq!(
            call_children(&ns, formal_uses[0]),
            vec![children[0]],
            "形式引数はそのcallの実引数producerを使う"
        );
        for child in live(&ns, children[1]) {
            assert!(
                !arr(f(val(child), "bindings"))
                    .iter()
                    .any(|b| [parameter, "held"].contains(&text(f(b, "name")))),
                "未知実引数とletを通常Bindingへ生成しない"
            );
        }
    }
}
#[test]
fn missing_z_identity_survives_unknown_let_argument_and_view_return() {
    shared_through_call("Z", "z", "hz");
}
#[test]
fn missing_q_identity_survives_unknown_let_argument_and_view_return() {
    shared_through_call("Q", "q", "hq");
}

#[test]
fn unknown_view_argument_can_cancel_inside_the_called_body() {
    let script = "view cancel(hz:Z): Z = hz-hz; view delta(s:Sample): Z = cancel(s.z);";
    let (wire, checked) = run(simple(script), &["a=evaluate(Calc.delta,s=@v/item)"]);
    output(&wire, "a", "Z", Json::str("0"));
    affine_scalar(&wire, &checked, "hz-hz", "Z", Json::str("0"));
    missing(&wire, "a", &[fact("v", "item", "z")]);
    complete_ast(&wire, &checked, "a", "Calc.delta");
    let ns = index(&wire);
    let children = call_children(&ns, root(&wire, "a"));
    assert_eq!(children.len(), 2);
    assert!(!obj(val(children[0])).contains_key("value"));
    assert_eq!(source(&checked, at(&ns, children[0])), b"s.z");
    assert_eq!(source(&checked, at(&ns, children[1])), b"hz-hz");
    for name_use in call_children(&ns, children[1]) {
        assert_eq!(call_children(&ns, name_use), vec![children[0]]);
        assert!(
            !arr(f(val(name_use), "bindings"))
                .iter()
                .any(|b| f(b, "name") == &Json::str("hz"))
        );
    }
}

#[test]
fn same_named_slots_of_distinct_subjects_and_snapshots_are_independent() {
    let script = "view delta(s:Sample,t:Sample): Z = s.z-t.z;";
    let (wire, checked) = run(
        fixture(script, false, true, true, false),
        &[
            "subject=evaluate(Calc.delta,s=@v/item,t=@v/peer)",
            "snapshot=evaluate(Calc.delta,s=@v/item,t=@w/item)",
        ],
    );
    undetermined(
        &wire,
        "subject",
        &[fact("v", "item", "z"), fact("v", "peer", "z")],
    );
    undetermined(
        &wire,
        "snapshot",
        &[fact("v", "item", "z"), fact("w", "item", "z")],
    );
    for id in ["subject", "snapshot"] {
        complete_ast(&wire, &checked, id, "Calc.delta");
    }
    assert_eq!(
        f(f(answer(&wire, "snapshot"), "scope"), "snapshots"),
        &Json::Arr(vec![Json::str("v"), Json::str("w")])
    );
    assert_eq!(
        f(f(answer(&wire, "snapshot"), "scope"), "modes"),
        &Json::Arr(vec![Json::str("proposed"), Json::str("specification")])
    );
}

fn finite_cases(
    wire: &Json,
    checked: &CheckedInputs,
    id: &str,
    expected: &[(bool, Json)],
    result_type: &str,
) {
    let ns = index(wire);
    let aggregate = root(wire, id);
    let args = arr(f(aggregate, "arguments"));
    assert_eq!(&args[0], f(val(aggregate), "expression"));
    let domain = target(&ns, &args[1], &Json::str("Domain"));
    assert_eq!(f(val(domain), "kind"), &Json::str("finite"));
    assert_eq!(
        f(val(domain), "type"),
        &Json::str("Bool"),
        "有限化するslotはBoolだけ"
    );
    let members = arr(f(val(domain), "elements"));
    assert_eq!(members.len(), 2);
    assert_eq!(
        members
            .iter()
            .map(|r| val(target(&ns, r, &Json::str("Bool"))).canonical())
            .collect::<BTreeSet<_>>(),
        [Json::Bool(false).canonical(), Json::Bool(true).canonical()]
            .into_iter()
            .collect()
    );
    let cases = call_children(&ns, aggregate);
    assert_eq!(cases.len(), 2);
    let mut seen = BTreeSet::new();
    for case in &cases {
        let source = expression(&ns, case);
        let selected = arr(f(source, "arguments"))
            .iter()
            .filter(|r| members.contains(r))
            .collect::<Vec<_>>();
        assert_eq!(selected.len(), 1);
        let value = val(target(&ns, selected[0], &Json::str("Bool")));
        let Json::Bool(flag) = value else {
            panic!("Bool case")
        };
        assert!(seen.insert(*flag));
        let wanted = &expected.iter().find(|(f, _)| f == flag).unwrap().1;
        assert_eq!(
            val(target(&ns, f(val(case), "value"), &Json::str(result_type))),
            wanted,
            "wholeを先にcase内評価する"
        );
        assert_eq!(f(f(case, "scope"), "domain"), &Json::str("all_completions"));
        let field_text = if result_type == "Q" { "s.q" } else { "s.z" };
        assert!(
            live(&ns, case)
                .iter()
                .any(|e| source_text_is(&ns, checked, e, field_text)
                    && !obj(val(e)).contains_key("value")),
            "Z/Qはcase内でも観測値にしない"
        );
    }
    assert_eq!(seen, [false, true].into_iter().collect());
    let direct = arr(f(aggregate, "evidence"))
        .iter()
        .map(|r| target(&ns, r, &Json::str("Evidence")))
        .collect::<Vec<_>>();
    assert_eq!(direct.len(), 1);
    if expected[0].1 == expected[1].1 {
        assert_eq!(f(val(direct[0]), "kind"), &Json::str("finite_exhaustion"));
        let data = f(val(direct[0]), "data");
        assert_eq!(f(data, "domain"), &args[1]);
        assert_eq!(f(data, "checked"), &Json::Nat(2));
        assert_eq!(
            f(data, "instances"),
            &Json::Arr(cases.iter().map(|c| reference(c)).collect())
        );
    } else {
        assert_eq!(f(val(direct[0]), "kind"), &Json::str("completion_pair"));
        let data = f(val(direct[0]), "data");
        assert_eq!(f(data, "fields"), &Json::Arr(vec![fact("v", "item", "p")]));
        let mut assignments = vec![];
        let mut results = vec![];
        for (binding, result) in [("first", "first_result"), ("second", "second_result")] {
            let values = arr(f(data, binding));
            assert_eq!(values.len(), 1);
            let scalar = target(&ns, &values[0], &Json::str("Bool"));
            assignments.push(val(scalar).clone());
            let evaluation = target(&ns, f(data, result), &Json::str("Evaluation"));
            assert!(cases.contains(&evaluation));
            results.push(
                val(target(
                    &ns,
                    f(val(evaluation), "value"),
                    &Json::str(result_type),
                ))
                .clone(),
            );
            assert!(arr(f(expression(&ns, evaluation), "arguments")).contains(&values[0]));
            assert_eq!(f(f(scalar, "rule"), "kind"), &Json::str("construction"));
        }
        assert_ne!(assignments[0], assignments[1]);
        assert_ne!(results[0], results[1]);
    }
}
fn source_text_is(
    ns: &BTreeMap<&str, &Json>,
    checked: &CheckedInputs,
    evaluation: &Json,
    text: &str,
) -> bool {
    source(checked, at(ns, evaluation)) == text.as_bytes()
}

#[test]
fn bool_cases_normalize_affine_wholes_before_equal_result_aggregation() {
    // p=false と p=true のどちらも、case wholeは Z の0になる。
    let script = "view delta(s:Sample): Z = if s.p then (if s.p then s.z-s.z else 1) else 0;";
    let (wire, checked) = run(
        fixture(script, true, false, false, false),
        &["a=evaluate(Calc.delta,s=@v/item)"],
    );
    output(&wire, "a", "Z", Json::str("0"));
    missing(
        &wire,
        "a",
        &[fact("v", "item", "p"), fact("v", "item", "z")],
    );
    finite_cases(
        &wire,
        &checked,
        "a",
        &[(false, Json::str("0")), (true, Json::str("0"))],
        "Z",
    );
}

#[test]
fn bool_cases_keep_a_typed_pair_for_varying_affine_wholes() {
    // p=false のwholeは1、p=true のwholeは0。hの代入例は作らない。
    let script = "view delta(s:Sample): Z = if s.p then s.z-s.z else s.z-s.z+1;";
    let (wire, checked) = run(
        fixture(script, true, false, false, false),
        &["a=evaluate(Calc.delta,s=@v/item)"],
    );
    undetermined(
        &wire,
        "a",
        &[fact("v", "item", "p"), fact("v", "item", "z")],
    );
    finite_cases(
        &wire,
        &checked,
        "a",
        &[(false, Json::str("1")), (true, Json::str("0"))],
        "Z",
    );
}

#[test]
fn bool_cases_keep_q_affine_results_and_reduced_typed_pair() {
    let script = "view delta(s:Sample): Q = if s.p then s.q-s.q else s.q-s.q+rat(1,2);";
    let (wire, checked) = run(
        fixture(script, true, false, false, false),
        &["a=evaluate(Calc.delta,s=@v/item)"],
    );
    undetermined(
        &wire,
        "a",
        &[fact("v", "item", "p"), fact("v", "item", "q")],
    );
    finite_cases(
        &wire,
        &checked,
        "a",
        &[(false, q("1", "2")), (true, q("0", "1"))],
        "Q",
    );
}

#[test]
fn provenance_relocation_preserves_affine_judgments_and_returns_new_origins() {
    let script = "law required equal(s:Sample): (s.z-s.z)+s.knownz=7; law required unequal(s:Sample): s.q-s.q=1;";
    let asks = [
        "equal=check(Calc.equal,s=@v/item)",
        "unequal=check(Calc.unequal,s=@v/item)",
    ];
    let (original, original_checked) = run(fixture(script, false, false, false, false), &asks);
    let (relocated, relocated_checked) = run(fixture(script, false, false, false, true), &asks);
    for (id, status) in [("equal", "established"), ("unequal", "refuted")] {
        assert_eq!(f(answer(&original, id), "status"), &Json::str(status));
        assert_eq!(f(answer(&relocated, id), "status"), &Json::str(status));
        for key in ["outputs", "scope", "reasons", "evidence", "claim"] {
            assert_eq!(
                obj(answer(&original, id)).get(key),
                obj(answer(&relocated, id)).get(key),
                "由来変更は判断と元式導出を変えない"
            );
        }
    }
    assert_ne!(
        original_checked.sources().archmap().bytes(),
        relocated_checked.sources().archmap().bytes()
    );
    for checked in [&original_checked, &relocated_checked] {
        let sample = checked.archmap().snapshots[0]
            .subjects
            .iter()
            .find(|s| s.id == "item")
            .unwrap();
        assert!(matches!(
            sample
                .fields
                .iter()
                .find(|f| f.name == "Affine.Sample.z")
                .unwrap()
                .slot,
            Slot::Missing
        ));
        let owner = sample
            .fields
            .iter()
            .find(|f| f.name == "Affine.Sample.owner")
            .unwrap();
        assert!(
            matches!(&owner.slot,Slot::Known {value:archsig::archmap::Value::Ref {snapshot,subject},..} if snapshot == "v" && subject == "root")
        );
    }
    assert!(
        relocated_checked
            .archmap()
            .origins
            .iter()
            .all(|o| o.id.ends_with("_moved"))
    );
    assert_eq!(
        relocated_checked.archmap().sources[0].uri,
        "urn:fixture:affine-constants:relocated"
    );
}

fn counted(inputs: &InputSources, asks: &[&str]) -> (Json, usize) {
    let count = Rc::new(Cell::new(0));
    let seen = count.clone();
    let mut control = Control::new(Limits::default(), move |p| {
        if p == Checkpoint::Expression {
            seen.set(seen.get() + 1);
        }
        Usage::default()
    });
    let wire = evaluate_observed_bytes(inputs.clone(), asks, &mut control)
        .unwrap()
        .wire();
    (wire, count.get())
}

#[test]
fn affine_expression_stops_keep_verified_prefix_values_reasons_and_frozen_probes() {
    let inputs = simple(
        r#"
view seed(s:Sample): Unit = unit;
law required known_false(s:Sample): s.known;
view other_missing(s:Sample): Q = s.q;
view current(s:Sample): Z = s.z-s.z;
view later(s:Sample): Unit = unit;
"#,
    );
    let asks = [
        "seed=evaluate(Calc.seed,s=@v/item)",
        "known_false=check(Calc.known_false,s=@v/item)",
        "other_missing=evaluate(Calc.other_missing,s=@v/item)",
        "current=evaluate(Calc.current,s=@v/item)",
        "later=evaluate(Calc.later,s=@v/item)",
    ];
    let checked = check_inputs(inputs.clone(), &mut quiet()).unwrap();
    let (prior, prior_count) = counted(&inputs, &asks[..3]);
    let (baseline, baseline_count) = counted(&inputs, &asks[..4]);
    audit(&prior, &checked);
    audit(&baseline, &checked);
    output(&baseline, "current", "Z", Json::str("0"));
    affine_scalar(&baseline, &checked, "s.z-s.z", "Z", Json::str("0"));
    assert_eq!(
        baseline_count - prior_count,
        6,
        "二つの元fieldと元減算のExpression pre/postだけ"
    );
    let current_span = checked.law().exprs[body(&checked, "Calc.current")].span;
    let later_span = checked.law().exprs[body(&checked, "Calc.later")].span;
    // 元Expressionの固定3点だけ。係数走査と再検査の内部はprivate試験が扱う。
    for (offset, kind, field_prefix, complete_current) in
        [(3, 0, 1, false), (5, 1, 2, false), (6, 2, 2, true)]
    {
        let at_stop = prior_count + offset;
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
                    if e.get() == at_stop {
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
        let wire = evaluate_observed_bytes(inputs.clone(), &asks, &mut control)
            .unwrap()
            .wire();
        assert_eq!(f(&wire, "status"), &Json::str("interrupted"));
        audit(&wire, &checked);
        output(&wire, "seed", "Unit", Json::Arr(vec![]));
        assert_eq!(
            f(answer(&wire, "known_false"), "status"),
            &Json::str("refuted")
        );
        for id in ["seed", "known_false", "other_missing"] {
            for key in ["status", "outputs", "scope", "reasons", "evidence", "claim"] {
                assert_eq!(
                    obj(answer(&wire, id)).get(key),
                    obj(answer(&prior, id)).get(key),
                    "停止前の値・実反例・元理由を保持"
                );
            }
        }
        missing(&wire, "other_missing", &[fact("v", "item", "q")]);
        missing(&wire, "current", &[fact("v", "item", "z")]);
        for id in ["current", "later"] {
            let a = answer(&wire, id);
            assert_eq!(f(a, "status"), &Json::str("undetermined"));
            assert!(!obj(a).contains_key("claim"));
            assert!(arr(f(a, "evidence")).is_empty());
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
        assert!(obj(f(answer(&wire, "later"), "outputs")).is_empty());
        assert!(
            evaluations_at(&wire, later_span).is_empty(),
            "未着手の式を評価しない"
        );
        let current = evaluations_at(&wire, current_span);
        assert_eq!(current.len(), usize::from(complete_current));
        if complete_current {
            let outputs = f(answer(&wire, "current"), "outputs");
            assert_eq!(
                val(target(&index(&wire), f(outputs, "value"), &Json::str("Z"))),
                &Json::str("0"),
                "post停止前に検査済みの現在値を保持"
            );
            assert_eq!(f(outputs, "evaluation"), &reference(current[0]));
            affine_scalar(&wire, &checked, "s.z-s.z", "Z", Json::str("0"));
        } else {
            assert!(obj(f(answer(&wire, "current"), "outputs")).is_empty());
        }
        assert_eq!(
            missing_field_evaluations(&wire, &checked, "z"),
            field_prefix
        );
        let prefix = arr(f(&wire, "nodes"));
        assert_eq!(
            prefix,
            &arr(f(&baseline, "nodes"))[..prefix.len()],
            "完成した元DAG prefixをそのまま保持"
        );
        assert_eq!(expressions.get(), at_stop);
        assert_eq!(Some(probes.get()), frozen.get());
        let before = probes.get();
        assert!(control.checkpoint(Checkpoint::Expression).is_err());
        assert_eq!(probes.get(), before, "停止後の再検査でもprobeを再開しない");
    }
}
