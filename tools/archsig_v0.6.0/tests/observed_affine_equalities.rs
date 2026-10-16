//! 欠測 Z/Q を残す元左右と、定数差による Eq/Ne の導出を三入力 byte から検査する。
mod common;

use archsig::{
    archmap::Slot,
    canonical::Json,
    definition::check_definitions_controlled,
    law::{ast::ExprKind, model::Signature},
    observed::{
        control::{Control, Limits, Usage},
        evaluate_observed_bytes,
        input::{CheckedInputs, InputSources, InputStatus, check_inputs},
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
    assert_eq!(
        evaluated.prepared().inputs().archmap().bytes_digest,
        checked.archmap().bytes_digest
    );
    assert_eq!(
        evaluated.prepared().inputs().archmap().model_digest,
        checked.archmap().model_digest
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
fn own_part<'a>(ns: &BTreeMap<&str, &'a Json>, evaluation: &'a Json) -> &'a Json {
    arr(f(val(evaluation), "parts"))
        .iter()
        .find(|p| span(f(p, "location")) == at(ns, evaluation))
        .unwrap()
}
fn children<'a>(ns: &BTreeMap<&str, &'a Json>, evaluation: &'a Json) -> Vec<&'a Json> {
    arr(f(own_part(ns, evaluation), "children"))
        .iter()
        .map(|r| target(ns, r, &Json::str("Evaluation")))
        .collect()
}
fn normalization<'a>(
    wire: &'a Json,
    checked: &CheckedInputs,
    comparison: &'a Json,
    numeric_type: &str,
    residual_value: Json,
    boolean: bool,
) -> (&'a Json, &'a Json, &'a Json) {
    let ns = index(wire);
    let operands = children(&ns, comparison);
    assert_eq!(operands.len(), 2);
    let original = expression(&ns, comparison);
    assert_eq!(f(val(original), "kind"), &Json::str("source"));
    let comparison_span = at(&ns, comparison);
    let (id, ast) = checked
        .law()
        .exprs
        .iter()
        .enumerate()
        .find(|(_, e)| e.span == comparison_span)
        .unwrap();
    let ExprKind::Binary { op, lhs, rhs } = &ast.kind else {
        panic!("元Eq/Ne")
    };
    assert!(matches!(
        op,
        archsig::law::ast::BinOp::Eq | archsig::law::ast::BinOp::Ne
    ));
    assert_eq!(
        checked.law().expr_type(id).unwrap().wire(),
        Json::str("Bool")
    );
    assert_eq!(
        checked.law().expr_type(*lhs).unwrap().wire(),
        Json::str(numeric_type)
    );
    assert_eq!(
        checked.law().expr_type(*rhs).unwrap().wire(),
        Json::str(numeric_type)
    );
    for (operand, expr) in operands.iter().zip([*lhs, *rhs]) {
        assert_eq!(at(&ns, operand), checked.law().exprs[expr].span);
        assert!(
            !obj(val(operand)).contains_key("value"),
            "元左右の未知値をScalarへ捏造しない"
        );
        assert!(!obj(own_part(&ns, operand)).contains_key("value"));
        assert_eq!(
            f(f(operand, "scope"), "domain"),
            &Json::str("all_completions")
        );
    }
    assert_ne!(
        f(operands[0], "id"),
        f(operands[1], "id"),
        "元左右のAST出現を潰さない"
    );
    let own_source = f(val(comparison), "expression");
    let left = reference(operands[0]);
    let right = reference(operands[1]);
    let residual_ref = f(own_part(&ns, comparison), "residual");
    let residual = target(&ns, residual_ref, &Json::str(numeric_type));
    assert_eq!(val(residual), &residual_value);
    assert_eq!(f(f(residual, "rule"), "kind"), &Json::str("construction"));
    assert_eq!(f(f(residual, "rule"), "name"), &Json::str("evaluation"));
    let scalar_args = arr(f(residual, "arguments"));
    assert_eq!(scalar_args.len(), 4);
    let difference = target(&ns, &scalar_args[0], &Json::str("Expression"));
    let difference_ref = reference(difference);
    assert_eq!(f(val(difference), "kind"), &Json::str("transform"));
    assert_eq!(f(val(difference), "operation"), &Json::str("difference"));
    assert_eq!(
        f(val(difference), "operands"),
        &Json::Arr(vec![
            f(val(operands[0]), "expression").clone(),
            f(val(operands[1]), "expression").clone()
        ])
    );
    assert_eq!(
        f(val(difference), "bindings"),
        f(val(comparison), "bindings")
    );
    assert!(arr(f(val(difference), "parameters")).is_empty());
    assert_eq!(
        f(difference, "arguments"),
        &Json::Arr(vec![own_source.clone(), left.clone(), right.clone()])
    );
    assert_eq!(
        scalar_args,
        &[
            difference_ref.clone(),
            own_source.clone(),
            left.clone(),
            right.clone()
        ]
    );
    let result = target(&ns, f(val(comparison), "value"), &Json::str("Bool"));
    assert_eq!(val(result), &Json::Bool(boolean));
    assert_eq!(f(f(result, "rule"), "kind"), &Json::str("law"));
    assert_eq!(span(f(f(result, "rule"), "location")), comparison_span);
    let proofs = arr(f(result, "evidence"));
    assert_eq!(proofs.len(), 1);
    let proof = target(&ns, &proofs[0], &Json::str("Evidence"));
    assert_eq!(f(val(proof), "kind"), &Json::str("normalization"));
    assert_eq!(f(f(proof, "rule"), "kind"), &Json::str("construction"));
    assert_eq!(f(f(proof, "rule"), "name"), &Json::str("evidence"));
    let data = f(val(proof), "data");
    assert_eq!(f(data, "before"), &difference_ref);
    assert_eq!(f(data, "after"), residual_ref);
    assert_eq!(
        f(data, "steps"),
        &Json::Arr(vec![
            f(val(operands[0]), "expression").clone(),
            f(val(operands[1]), "expression").clone(),
            difference_ref.clone()
        ])
    );
    for step in arr(f(data, "steps")) {
        target(&ns, step, &Json::str("Expression"));
    }
    assert_eq!(
        f(proof, "arguments"),
        &Json::Arr(vec![
            own_source.clone(),
            left.clone(),
            right.clone(),
            difference_ref.clone(),
            residual_ref.clone()
        ])
    );
    assert_eq!(
        f(result, "arguments"),
        &Json::Arr(vec![
            own_source.clone(),
            left,
            right,
            difference_ref,
            residual_ref.clone(),
            reference(proof)
        ])
    );
    for node in [difference, residual, proof, result] {
        assert!(
            arr(f(node, "reasons")).is_empty(),
            "normalizationはmissingの代わりになる入力ではない"
        );
        assert_eq!(f(node, "support"), f(comparison, "support"));
        assert_eq!(f(node, "scope"), f(comparison, "scope"));
    }
    (difference, residual, proof)
}
fn law_comparison(wire: &Json, id: &str, expected: bool, comparison: &Json, proof: &Json) {
    let ns = index(wire);
    let a = answer(wire, id);
    let status = if expected { "established" } else { "refuted" };
    assert_eq!(f(a, "status"), &Json::str(status));
    let claim = target(&ns, f(a, "claim"), &Json::str("Proposition"));
    assert_eq!(f(f(claim, "judgment"), "status"), &Json::str(status));
    assert_eq!(f(val(claim), "predicate"), &Json::str("law_holds"));
    let proofs = arr(f(a, "evidence"))
        .iter()
        .map(|r| target(&ns, r, &Json::str("Evidence")))
        .collect::<Vec<_>>();
    let evaluated = proofs
        .iter()
        .filter(|e| f(val(e), "kind") == &Json::str("evaluation"))
        .copied()
        .collect::<Vec<_>>();
    assert_eq!(evaluated.len(), 1);
    let data = f(val(evaluated[0]), "data");
    let operands = children(&ns, comparison);
    assert_eq!(f(data, "lhs"), &reference(operands[0]));
    assert_eq!(f(data, "rhs"), &reference(operands[1]));
    assert_eq!(
        f(data, "residual"),
        f(own_part(&ns, comparison), "residual")
    );
    let examples = proofs
        .iter()
        .filter(|e| f(val(e), "kind") == &Json::str("counterexample"))
        .copied()
        .collect::<Vec<_>>();
    assert_eq!(examples.len(), usize::from(!expected));
    if !expected {
        let example = f(val(examples[0]), "data");
        assert_eq!(f(example, "left"), f(data, "lhs"));
        assert_eq!(f(example, "right"), f(data, "rhs"));
        for key in ["left", "right"] {
            let operand = target(&ns, f(example, key), &Json::str("Evaluation"));
            assert!(
                !obj(val(operand)).contains_key("value"),
                "反例に具体的なhを割当てない"
            );
        }
        assert_eq!(f(examples[0], "support"), f(comparison, "support"));
    }
    // 評価証拠の親EvaluationからBoolのnormalizationへ戻れる。
    let mut todo = vec![];
    refs(evaluated[0], &mut todo);
    let mut reachable = BTreeSet::new();
    while let Some(id) = todo.pop() {
        if reachable.insert(id.clone()) {
            refs(ns[id.as_str()], &mut todo);
        }
    }
    assert!(reachable.contains(text(f(proof, "id"))));
}
fn compare_case(numeric_type: &str, field: &str, op: &str, same: bool, required: bool) {
    let offset = if same { "1" } else { "2" };
    let expression = format!("s.{field}+1{op}s.{field}+{offset}");
    let (decl, request) = if required {
        (
            format!("law required requirement(s:Sample): {expression};"),
            "a=check(Calc.requirement,s=@v/item)",
        )
    } else {
        (
            format!("view comparison(s:Sample): Bool = {expression};"),
            "a=evaluate(Calc.comparison,s=@v/item)",
        )
    };
    let (wire, checked) = run(simple(&decl), &[request]);
    assert_eq!(f(&wire, "status"), &Json::str("complete"));
    let declaration = if required {
        "Calc.requirement"
    } else {
        "Calc.comparison"
    };
    let comparison_span = checked.law().exprs[body(&checked, declaration)].span;
    assert_eq!(
        evaluations_at(&wire, comparison_span),
        vec![root(&wire, "a")]
    );
    let expected = if op == "=" { same } else { !same };
    if !required {
        output(&wire, "a", "Bool", Json::Bool(expected));
    }
    missing(&wire, "a", &[fact("v", "item", field)]);
    let residual = if numeric_type == "Q" {
        q(if same { "0" } else { "-1" }, "1")
    } else {
        Json::str(if same { "0" } else { "-1" })
    };
    let (_, _, proof) = normalization(
        &wire,
        &checked,
        root(&wire, "a"),
        numeric_type,
        residual,
        expected,
    );
    if required {
        law_comparison(&wire, "a", expected, root(&wire, "a"), proof);
    }
    complete_ast(
        &wire,
        &checked,
        "a",
        if required {
            "Calc.requirement"
        } else {
            "Calc.comparison"
        },
    );
    assert_eq!(missing_field_evaluations(&wire, &checked, field), 2);
}

#[test]
fn z_equal_same_affine_sides_returns_true() {
    compare_case("Z", "z", "=", true, false);
}
#[test]
fn z_equal_distinct_affine_sides_returns_false() {
    compare_case("Z", "z", "=", false, false);
}
#[test]
fn z_unequal_same_affine_sides_returns_false() {
    compare_case("Z", "z", "!=", true, false);
}
#[test]
fn z_unequal_distinct_affine_sides_returns_true() {
    compare_case("Z", "z", "!=", false, false);
}
#[test]
fn q_equal_same_affine_sides_returns_true() {
    compare_case("Q", "q", "=", true, false);
}
#[test]
fn q_equal_distinct_affine_sides_returns_false() {
    compare_case("Q", "q", "=", false, false);
}
#[test]
fn q_unequal_same_affine_sides_returns_false() {
    compare_case("Q", "q", "!=", true, false);
}
#[test]
fn q_unequal_distinct_affine_sides_returns_true() {
    compare_case("Q", "q", "!=", false, false);
}
#[test]
fn z_equal_same_affine_sides_establishes_required_law() {
    compare_case("Z", "z", "=", true, true);
}
#[test]
fn z_equal_distinct_affine_sides_refutes_required_law() {
    compare_case("Z", "z", "=", false, true);
}
#[test]
fn z_unequal_same_affine_sides_refutes_required_law() {
    compare_case("Z", "z", "!=", true, true);
}
#[test]
fn z_unequal_distinct_affine_sides_establishes_required_law() {
    compare_case("Z", "z", "!=", false, true);
}
#[test]
fn q_equal_same_affine_sides_establishes_required_law() {
    compare_case("Q", "q", "=", true, true);
}
#[test]
fn q_equal_distinct_affine_sides_refutes_required_law() {
    compare_case("Q", "q", "=", false, true);
}
#[test]
fn q_unequal_same_affine_sides_refutes_required_law() {
    compare_case("Q", "q", "!=", true, true);
}
#[test]
fn q_unequal_distinct_affine_sides_establishes_required_law() {
    compare_case("Q", "q", "!=", false, true);
}

fn expression_case(
    expression: &str,
    numeric_type: &str,
    residual: Json,
    expected: bool,
    fields: &[&str],
) {
    let (wire, checked) = run(
        simple(&format!("view comparison(s:Sample): Bool = {expression};")),
        &["a=evaluate(Calc.comparison,s=@v/item)"],
    );
    output(&wire, "a", "Bool", Json::Bool(expected));
    normalization(
        &wire,
        &checked,
        root(&wire, "a"),
        numeric_type,
        residual,
        expected,
    );
    missing(
        &wire,
        "a",
        &fields
            .iter()
            .map(|field| fact("v", "item", field))
            .collect::<Vec<_>>(),
    );
    complete_ast(&wire, &checked, "a", "Calc.comparison");
}
#[test]
fn z_nontrivial_coefficients_cancel_between_unknown_sides() {
    expression_case("(2*s.z+3)-s.z=s.z+3", "Z", Json::str("0"), true, &["z"]);
}
#[test]
fn original_left_minus_right_order_keeps_positive_residual() {
    expression_case("s.z+2=s.z+1", "Z", Json::str("1"), false, &["z"]);
}
#[test]
fn z_multiple_missing_slots_cancel_without_becoming_observations() {
    expression_case(
        "s.z+s.k+3=s.k+s.z+4",
        "Z",
        Json::str("-1"),
        false,
        &["z", "k"],
    );
}
#[test]
fn q_fractional_coefficients_produce_reduced_negative_residual() {
    expression_case(
        "rat(1,2)*s.q+rat(6,8)=rat(1,2)*s.q+rat(10,8)",
        "Q",
        q("-1", "2"),
        false,
        &["q"],
    );
}
#[test]
fn q_multiple_slots_and_half_offsets_cancel_exactly() {
    expression_case(
        "(s.q+rat(1,2))+s.r+rat(1,2)=s.r+s.q+1",
        "Q",
        q("0", "1"),
        true,
        &["q", "r"],
    );
}
#[test]
fn z_coefficients_and_constants_above_i64_keep_exact_difference() {
    expression_case(
        "9223372036854775808*s.z+9223372036854775809=9223372036854775808*s.z+9223372036854775810",
        "Z",
        Json::str("-1"),
        false,
        &["z"],
    );
}
#[test]
fn q_comparison_with_z_is_rejected_without_implicit_coercion() {
    let failure = check_inputs(
        simple("view comparison(s:Sample): Bool = s.z+1=s.q+1;"),
        &mut quiet(),
    )
    .unwrap_err();
    assert_eq!(failure.status(), InputStatus::Invalid);
    assert!(
        failure
            .issues()
            .iter()
            .any(|issue| f(issue, "code") == &Json::str("type"))
    );
}
fn unknown_comparison(expression: &str, fields: &[Json], required: bool) {
    let (decl, request) = if required {
        (
            format!("law required requirement(s:Sample): {expression};"),
            "a=check(Calc.requirement,s=@v/item)",
        )
    } else {
        (
            format!("view comparison(s:Sample): Bool = {expression};"),
            "a=evaluate(Calc.comparison,s=@v/item)",
        )
    };
    let (wire, checked) = run(simple(&decl), &[request]);
    if !required {
        undetermined(&wire, "a", fields);
    } else {
        let a = answer(&wire, "a");
        assert_eq!(f(a, "status"), &Json::str("undetermined"));
        let claim = target(&index(&wire), f(a, "claim"), &Json::str("Proposition"));
        assert_eq!(
            f(f(claim, "judgment"), "status"),
            &Json::str("undetermined")
        );
        assert!(arr(f(a, "evidence")).is_empty());
        assert!(arr(f(claim, "evidence")).is_empty());
        missing(&wire, "a", fields);
    }
    let ns = index(&wire);
    let evaluation = root(&wire, "a");
    assert!(!obj(val(evaluation)).contains_key("value"));
    assert!(!obj(own_part(&ns, evaluation)).contains_key("residual"));
    assert!(
        arr(f(&wire, "nodes"))
            .iter()
            .all(|n| f(n, "type") != &Json::str("Evidence")
                || !["normalization", "counterexample"].contains(&text(f(val(n), "kind"))))
    );
    complete_ast(
        &wire,
        &checked,
        "a",
        if required {
            "Calc.requirement"
        } else {
            "Calc.comparison"
        },
    );
}
#[test]
fn z_nonconstant_difference_keeps_required_law_undetermined() {
    unknown_comparison("s.z=0", &[fact("v", "item", "z")], true);
}
#[test]
fn q_nonconstant_difference_keeps_required_law_undetermined() {
    unknown_comparison("s.q=0", &[fact("v", "item", "q")], true);
}
#[test]
fn z_distinct_missing_fields_are_not_correlated_by_equality() {
    unknown_comparison(
        "s.z+1=s.k+1",
        &[fact("v", "item", "z"), fact("v", "item", "k")],
        false,
    );
}
#[test]
fn q_distinct_missing_fields_are_not_correlated_by_inequality() {
    unknown_comparison(
        "s.q+1!=s.r+1",
        &[fact("v", "item", "q"), fact("v", "item", "r")],
        false,
    );
}
#[test]
fn unknown_nonlinear_sides_are_not_affine_normalization() {
    unknown_comparison("s.z*s.z=s.z*s.z", &[fact("v", "item", "z")], false);
}
fn independent_subjects(other: &str, expected_missing: Json) {
    let script = "view comparison(s:Sample,t:Sample): Bool = s.z+1=t.z+1;";
    let request = format!("a=evaluate(Calc.comparison,s=@v/item,t={other})");
    let (wire, checked) = run(fixture(script, false, true, true, false), &[&request]);
    undetermined(&wire, "a", &[fact("v", "item", "z"), expected_missing]);
    complete_ast(&wire, &checked, "a", "Calc.comparison");
    let ns = index(&wire);
    assert!(!obj(own_part(&ns, root(&wire, "a"))).contains_key("residual"));
}
#[test]
fn equally_named_slots_of_distinct_subjects_remain_independent() {
    independent_subjects("@v/peer", fact("v", "peer", "z"));
}
#[test]
fn equally_named_slots_of_distinct_snapshots_remain_independent() {
    independent_subjects("@w/item", fact("w", "item", "z"));
}
fn matching_evaluations<'a>(
    wire: &'a Json,
    checked: &CheckedInputs,
    expression_text: &str,
) -> Vec<&'a Json> {
    let ns = index(wire);
    arr(f(wire, "nodes"))
        .iter()
        .filter(|n| {
            f(n, "type") == &Json::str("Evaluation")
                && source(checked, at(&ns, n)) == expression_text.as_bytes()
        })
        .collect()
}
fn through_call(numeric_type: &str, field: &str, parameter: &str) {
    let comparison_text = format!("carry(saved)+1=carry(s.{field})+2");
    let script = format!(
        "view carry({parameter}:{numeric_type}): {numeric_type} = let held={parameter} in held; view comparison(s:Sample): Bool = let saved=s.{field} in {comparison_text};"
    );
    let (wire, checked) = run(simple(&script), &["a=evaluate(Calc.comparison,s=@v/item)"]);
    output(&wire, "a", "Bool", Json::Bool(false));
    missing(&wire, "a", &[fact("v", "item", field)]);
    complete_ast(&wire, &checked, "a", "Calc.comparison");
    let equalities = matching_evaluations(&wire, &checked, &comparison_text);
    assert_eq!(equalities.len(), 1);
    normalization(
        &wire,
        &checked,
        equalities[0],
        numeric_type,
        if numeric_type == "Q" {
            q("-1", "1")
        } else {
            Json::str("-1")
        },
        false,
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
    let mut producers = BTreeSet::new();
    for call in calls {
        assert!(!obj(val(call)).contains_key("value"));
        let actual = children(&ns, call);
        assert_eq!(actual.len(), 2);
        assert!(producers.insert(text(f(actual[0], "id"))));
        assert_eq!(
            source(&checked, at(&ns, actual[1])),
            format!("let held={parameter} in held").as_bytes()
        );
        let formal = live(&ns, actual[1])
            .into_iter()
            .filter(|e| source(&checked, at(&ns, e)) == parameter.as_bytes())
            .collect::<Vec<_>>();
        assert_eq!(formal.len(), 1);
        assert_eq!(
            children(&ns, formal[0]),
            vec![actual[0]],
            "そのcallの実引数producerへ戻る"
        );
        for use_site in live(&ns, actual[1]) {
            assert!(
                !arr(f(val(use_site), "bindings"))
                    .iter()
                    .any(|b| [parameter, "held"].contains(&text(f(b, "name"))))
            );
        }
    }
}
#[test]
fn z_equality_shares_missing_slot_through_unknown_let_and_view_return() {
    through_call("Z", "z", "hz");
}
#[test]
fn q_equality_shares_missing_slot_through_unknown_let_and_view_return() {
    through_call("Q", "q", "hq");
}
#[test]
fn comparison_inside_view_preserves_unknown_actual_argument_producer() {
    let script = "view compareoffset(hz:Z): Bool = hz+1=hz+2; view comparison(s:Sample): Bool = compareoffset(s.z);";
    let (wire, checked) = run(simple(script), &["a=evaluate(Calc.comparison,s=@v/item)"]);
    output(&wire, "a", "Bool", Json::Bool(false));
    let equality = matching_evaluations(&wire, &checked, "hz+1=hz+2");
    assert_eq!(equality.len(), 1);
    normalization(&wire, &checked, equality[0], "Z", Json::str("-1"), false);
    let ns = index(&wire);
    let call = children(&ns, root(&wire, "a"));
    assert_eq!(call.len(), 2);
    assert_eq!(equality[0], call[1]);
    assert!(!obj(val(call[0])).contains_key("value"));
    for parameter_use in matching_evaluations(&wire, &checked, "hz") {
        assert_eq!(children(&ns, parameter_use), vec![call[0]]);
        assert!(
            !arr(f(val(parameter_use), "bindings"))
                .iter()
                .any(|b| f(b, "name") == &Json::str("hz"))
        );
    }
    missing(&wire, "a", &[fact("v", "item", "z")]);
}
#[test]
fn identical_requests_retain_distinct_normalization_producers() {
    let (wire, checked) = run(
        simple("view comparison(s:Sample): Bool = s.z+1=s.z+2;"),
        &[
            "a=evaluate(Calc.comparison,s=@v/item)",
            "b=evaluate(Calc.comparison,s=@v/item)",
        ],
    );
    let mut sources = BTreeSet::new();
    let mut differences = BTreeSet::new();
    let mut proofs = BTreeSet::new();
    for id in ["a", "b"] {
        output(&wire, id, "Bool", Json::Bool(false));
        let evaluation = root(&wire, id);
        assert!(sources.insert(f(val(evaluation), "expression").canonical()));
        let (difference, _, proof) =
            normalization(&wire, &checked, evaluation, "Z", Json::str("-1"), false);
        assert!(differences.insert(text(f(difference, "id"))));
        assert!(proofs.insert(text(f(proof, "id"))));
        missing(&wire, id, &[fact("v", "item", "z")]);
    }
}

fn finite_wholes(wire: &Json, checked: &CheckedInputs, field: &str, expected: &[(bool, bool)]) {
    let ns = index(wire);
    let aggregate = root(wire, "a");
    assert_eq!(
        f(f(aggregate, "scope"), "domain"),
        &Json::str("all_completions")
    );
    let args = arr(f(aggregate, "arguments"));
    assert_eq!(&args[0], f(val(aggregate), "expression"));
    let domain = target(&ns, &args[1], &Json::str("Domain"));
    assert_eq!(f(val(domain), "kind"), &Json::str("finite"));
    assert_eq!(
        f(val(domain), "type"),
        &Json::str("Bool"),
        "Z/Qを有限補完域に入れない"
    );
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
    let mut selected_members = BTreeSet::new();
    for case in &cases {
        let selected = arr(f(expression(&ns, case), "arguments"))
            .iter()
            .filter(|r| members.contains(r))
            .collect::<Vec<_>>();
        assert_eq!(selected.len(), 1);
        let Json::Bool(assignment) = val(target(&ns, selected[0], &Json::str("Bool"))) else {
            panic!("Bool case")
        };
        assert!(selected_members.insert(*assignment));
        let result = expected.iter().find(|(a, _)| a == assignment).unwrap().1;
        assert_eq!(
            val(target(&ns, f(val(case), "value"), &Json::str("Bool"))),
            &Json::Bool(result),
            "各caseでwholeを先に判断する"
        );
        let case_nodes = live(&ns, case);
        assert!(case_nodes.iter().any(|e| source(checked, at(&ns, e))
            == format!("s.{field}").as_bytes()
            && !obj(val(e)).contains_key("value")));
        let mut normalized = 0;
        for equality in case_nodes {
            let bytes = source(checked, at(&ns, equality));
            let same = bytes == format!("s.{field}+1=s.{field}+1").as_bytes();
            if !same && bytes != format!("s.{field}+1=s.{field}+2").as_bytes() {
                continue;
            }
            let numeric_type = if field == "q" { "Q" } else { "Z" };
            let constant = if same { "0" } else { "-1" };
            normalization(
                wire,
                checked,
                equality,
                numeric_type,
                if field == "q" {
                    q(constant, "1")
                } else {
                    Json::str(constant)
                },
                same,
            );
            normalized += 1;
        }
        assert_eq!(normalized, 2, "caseの元左右比較を両方保持する");
    }
    assert_eq!(selected_members, BTreeSet::from([false, true]));
    let proofs = arr(f(aggregate, "evidence"))
        .iter()
        .map(|r| target(&ns, r, &Json::str("Evidence")))
        .collect::<Vec<_>>();
    assert_eq!(proofs.len(), 1);
    if expected[0].1 == expected[1].1 {
        assert_eq!(f(val(proofs[0]), "kind"), &Json::str("finite_exhaustion"));
        let data = f(val(proofs[0]), "data");
        assert_eq!(f(data, "domain"), &args[1]);
        assert_eq!(f(data, "checked"), &Json::Nat(2));
        assert_eq!(
            f(data, "instances"),
            &Json::Arr(cases.iter().map(|c| reference(c)).collect())
        );
    } else {
        assert_eq!(f(val(proofs[0]), "kind"), &Json::str("completion_pair"));
        let pair = f(val(proofs[0]), "data");
        assert_eq!(f(pair, "fields"), &Json::Arr(vec![fact("v", "item", "p")]));
        let mut assignments = vec![];
        let mut results = vec![];
        for (binding, result) in [("first", "first_result"), ("second", "second_result")] {
            let values = arr(f(pair, binding));
            assert_eq!(values.len(), 1);
            let value = target(&ns, &values[0], &Json::str("Bool"));
            assert_eq!(f(f(value, "rule"), "kind"), &Json::str("construction"));
            assignments.push(val(value).clone());
            let evaluation = target(&ns, f(pair, result), &Json::str("Evaluation"));
            assert!(cases.contains(&evaluation));
            assert!(arr(f(expression(&ns, evaluation), "arguments")).contains(&values[0]));
            results.push(val(target(&ns, f(val(evaluation), "value"), &Json::str("Bool"))).clone());
        }
        assert_ne!(assignments[0], assignments[1]);
        assert_ne!(results[0], results[1]);
    }
    missing(
        wire,
        "a",
        &[fact("v", "item", "p"), fact("v", "item", field)],
    );
}
#[test]
fn bool_cases_compare_z_wholes_before_constant_result_aggregation() {
    let script = "view comparison(s:Sample): Bool = if s.p then ((s.z+1=s.z+1) and s.p) else ((s.z+1=s.z+2) or not s.p);";
    let (wire, checked) = run(
        fixture(script, true, false, false, false),
        &["a=evaluate(Calc.comparison,s=@v/item)"],
    );
    output(&wire, "a", "Bool", Json::Bool(true));
    finite_wholes(&wire, &checked, "z", &[(false, true), (true, true)]);
}
#[test]
fn bool_cases_keep_typed_pair_for_varying_z_equalities() {
    let script = "view comparison(s:Sample): Bool = if s.p then (s.z+1=s.z+1) else (s.z+1=s.z+2);";
    let (wire, checked) = run(
        fixture(script, true, false, false, false),
        &["a=evaluate(Calc.comparison,s=@v/item)"],
    );
    undetermined(
        &wire,
        "a",
        &[fact("v", "item", "p"), fact("v", "item", "z")],
    );
    finite_wholes(&wire, &checked, "z", &[(false, false), (true, true)]);
}
#[test]
fn bool_cases_keep_typed_pair_for_varying_q_equalities() {
    let script = "view comparison(s:Sample): Bool = if s.p then (s.q+1=s.q+1) else (s.q+1=s.q+2);";
    let (wire, checked) = run(
        fixture(script, true, false, false, false),
        &["a=evaluate(Calc.comparison,s=@v/item)"],
    );
    undetermined(
        &wire,
        "a",
        &[fact("v", "item", "p"), fact("v", "item", "q")],
    );
    finite_wholes(&wire, &checked, "q", &[(false, false), (true, true)]);
}

#[test]
fn bool_cases_compare_each_law_whole_before_undetermined_claim() {
    let script =
        "law required requirement(s:Sample): if s.p then (s.z+1=s.z+1) else (s.z+1=s.z+2);";
    let (wire, checked) = run(
        fixture(script, true, false, false, false),
        &["a=check(Calc.requirement,s=@v/item)"],
    );
    let a = answer(&wire, "a");
    assert_eq!(f(a, "status"), &Json::str("undetermined"));
    let claim = target(&index(&wire), f(a, "claim"), &Json::str("Proposition"));
    assert_eq!(
        f(f(claim, "judgment"), "status"),
        &Json::str("undetermined")
    );
    finite_wholes(&wire, &checked, "z", &[(false, false), (true, true)]);
}
#[test]
fn provenance_relocation_keeps_false_affine_law_and_new_fact_origins() {
    let script = "law required requirement(s:Sample): s.z+s.knownz=s.z+8;";
    let request = ["a=check(Calc.requirement,s=@v/item)"];
    let (wire, checked) = run(fixture(script, false, false, false, false), &request);
    let (moved, moved_checked) = run(fixture(script, false, false, false, true), &request);
    for (result, inputs) in [(&wire, &checked), (&moved, &moved_checked)] {
        assert_eq!(f(result, "status"), &Json::str("complete"));
        let evaluation = root(result, "a");
        let (_, _, proof) = normalization(result, inputs, evaluation, "Z", Json::str("-1"), false);
        law_comparison(result, "a", false, evaluation, proof);
        missing(result, "a", &[fact("v", "item", "z")]);
        assert!(
            arr(f(evaluation, "support"))
                .iter()
                .any(|support| obj(support).get("field")
                    == Some(&Json::str("Affine.Sample.knownz"))
                    && obj(support).get("atom") == Some(&Json::str("item_knownz")))
        );
        let subject = inputs.archmap().snapshots[0]
            .subjects
            .iter()
            .find(|s| s.id == "item")
            .unwrap();
        assert!(
            matches!(&subject.fields.iter().find(|f|f.name == "Affine.Sample.owner").unwrap().slot,Slot::Known {value:archsig::archmap::Value::Ref {snapshot,subject},..} if snapshot == "v" && subject == "root")
        );
        assert!(
            matches!(&subject.fields.iter().find(|f|f.name == "Affine.Sample.knownz").unwrap().slot,Slot::Known {value:archsig::archmap::Value::Z(value),..} if value.to_string() == "7")
        );
        assert!(matches!(
            subject
                .fields
                .iter()
                .find(|f| f.name == "Affine.Sample.z")
                .unwrap()
                .slot,
            Slot::Missing
        ));
    }
    for key in ["status", "outputs", "scope", "reasons", "evidence", "claim"] {
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
    assert_eq!(moved_checked.archmap().sources[0].id, "scan_moved");
    assert_eq!(moved_checked.archmap().sources[0].revision, "r2");
    assert_eq!(
        moved_checked.archmap().sources[0].uri,
        "urn:fixture:affine-constants:relocated"
    );
}
#[test]
fn known_nonlinear_comparison_keeps_original_scalar_operands() {
    let (wire, checked) = run(
        simple("view comparison(s:Sample): Bool = s.knownz*s.knownz=49;"),
        &["a=evaluate(Calc.comparison,s=@v/item)"],
    );
    output(&wire, "a", "Bool", Json::Bool(true));
    let ns = index(&wire);
    let comparison = root(&wire, "a");
    assert_eq!(
        val(target(
            &ns,
            f(own_part(&ns, comparison), "residual"),
            &Json::str("Z")
        )),
        &Json::str("0")
    );
    for child in children(&ns, comparison) {
        assert_eq!(
            val(target(&ns, f(val(child), "value"), &Json::str("Z"))),
            &Json::str("49")
        );
    }
    assert!(
        arr(f(&wire, "nodes"))
            .iter()
            .all(|n| f(n, "type") != &Json::str("Evidence")
                || f(val(n), "kind") != &Json::str("normalization"))
    );
    complete_ast(&wire, &checked, "a", "Calc.comparison");
}
#[test]
fn bool_short_circuit_preserves_uncertain_numeric_comparison_source() {
    let (wire, checked) = run(
        simple("view comparison(s:Sample): Bool = true or (s.z=0);"),
        &["a=evaluate(Calc.comparison,s=@v/item)"],
    );
    output(&wire, "a", "Bool", Json::Bool(true));
    missing(&wire, "a", &[fact("v", "item", "z")]);
    let uncertain = matching_evaluations(&wire, &checked, "s.z=0");
    assert_eq!(uncertain.len(), 1);
    assert!(!obj(val(uncertain[0])).contains_key("value"));
    assert!(!obj(own_part(&index(&wire), uncertain[0])).contains_key("residual"));
    complete_ast(&wire, &checked, "a", "Calc.comparison");
}
