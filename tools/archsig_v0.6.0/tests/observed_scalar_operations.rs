//! AC4段階1: 小さいZ/Bool演算の値・判断・元式・欠測・由来をbyte入口から検査する。
use archsig::{
    canonical::Json,
    definition::check_definitions,
    law::ast::ExprKind,
    observed::{
        control::{Checkpoint, Control, Limits, Usage},
        evaluate_observed_bytes,
        input::{CheckedInputs, InputSources, check_inputs},
    },
};
use std::{
    cell::Cell,
    collections::{BTreeMap, BTreeSet},
    rc::Rc,
};

fn control() -> Control {
    Control::new(Limits::default(), |_| Usage::default())
}
fn obj(j: &Json) -> &BTreeMap<String, Json> {
    let Json::Obj(v) = j else {
        panic!("object {j:?}")
    };
    v
}
fn arr(j: &Json) -> &[Json] {
    let Json::Arr(v) = j else {
        panic!("array {j:?}")
    };
    v
}
fn txt(j: &Json) -> &str {
    let Json::Str(v) = j else {
        panic!("string {j:?}")
    };
    v
}
fn f<'a>(j: &'a Json, k: &str) -> &'a Json {
    &obj(j)[k]
}
fn val(j: &Json) -> &Json {
    assert_eq!(f(j, "state"), &Json::str("value"));
    f(j, "value")
}
fn nodes(j: &Json) -> BTreeMap<&str, &Json> {
    arr(f(j, "nodes"))
        .iter()
        .map(|n| (txt(f(n, "id")), n))
        .collect()
}
fn target<'a>(ns: &BTreeMap<&str, &'a Json>, r: &Json, ty: &str) -> &'a Json {
    assert_eq!(obj(r).len(), 1);
    let n = ns[txt(f(r, "node"))];
    assert_eq!(f(n, "type"), &Json::str(ty));
    n
}
fn answer<'a>(j: &'a Json, id: &str) -> &'a Json {
    arr(f(j, "answers"))
        .iter()
        .find(|a| txt(f(a, "id")) == id)
        .unwrap()
}
fn links(j: &Json, rs: &mut Vec<String>) {
    match j {
        Json::Obj(m) if m.len() == 1 && m.contains_key("node") => rs.push(txt(&m["node"]).into()),
        Json::Obj(m) => {
            for v in m.values() {
                links(v, rs);
            }
        }
        Json::Arr(v) => {
            for j in v {
                links(j, rs);
            }
        }
        _ => {}
    }
}
fn evaluation_tree<'a>(ns: &BTreeMap<&str, &'a Json>, root: &'a Json) -> Vec<&'a Json> {
    let mut todo = vec![root];
    let mut seen = BTreeSet::new();
    let mut evaluations = vec![];
    while let Some(evaluation) = todo.pop() {
        if seen.insert(txt(f(evaluation, "id"))) {
            evaluations.push(evaluation);
            for part in arr(f(val(evaluation), "parts")) {
                for child in arr(f(part, "children")) {
                    todo.push(target(ns, child, "Evaluation"));
                }
            }
        }
    }
    evaluations
}
fn original_root<'a>(ns: &BTreeMap<&str, &'a Json>, result: &Json, id: &str) -> &'a Json {
    let root = target(
        ns,
        f(f(answer(result, id), "outputs"), "evaluation"),
        "Evaluation",
    );
    let expression = target(ns, f(val(root), "expression"), "Expression");
    let arguments = arr(f(root, "arguments"));
    let completion = arguments.get(1).is_some_and(|r| {
        let n = ns[txt(f(r, "node"))];
        f(n, "type") == &Json::str("Domain")
            && arr(f(n, "arguments")).first() == Some(f(val(root), "expression"))
    });
    if !completion {
        return root;
    }
    let originals = arr(f(expression, "arguments"))
        .iter()
        .map(|r| ns[txt(f(r, "node"))])
        .filter(|n| f(n, "type") == &Json::str("Evaluation"))
        .collect::<Vec<_>>();
    assert_eq!(originals.len(), 1, "補完seedの直接の元式rootを一意に辿る");
    assert_ne!(f(originals[0], "id"), f(root, "id"));
    originals[0]
}
fn span(location: &Json) -> (usize, usize) {
    assert_eq!(f(location, "input"), &Json::str("law"));
    let a = arr(f(location, "span"));
    let nat = |n: &Json| {
        let Json::Nat(v) = n else { panic!("Nat") };
        *v as usize
    };
    (nat(&a[0]), nat(&a[1]))
}

fn fixture(x: Option<&str>, y: Option<&str>, p: Option<bool>, q: Option<bool>) -> InputSources {
    let definitions = r#"{"format":"archsig.atom-definition/1","semantics":"archsig/0.6.0",
      "vocabularies":[{"semantics":"archsig/0.6.0","namespace":"Measure","version":"1","dependencies":[],
      "declarations":[{"kind":"entity","name":"Measure.Point","meaning":"整数とBoolの観測対象。","parameters":[],
      "fields":[{"name":"x","type":"Z","meaning":"第一整数。"},{"name":"y","type":"Z","meaning":"第二整数。"},
      {"name":"p","type":"Bool","meaning":"第一条件。"},{"name":"q","type":"Bool","meaning":"第二条件。"}],"alignments":[]}]}]}"#;
    let checked = check_definitions(&[("definition0", definitions.as_bytes())]).unwrap();
    let digest = &checked.vocabularies["Measure"].digest;
    let law = format!(
        r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Calc {{
 use vocabulary Measure version "1" digest "{digest}";
 view add(s: Point): Z = s.x + s.y;
 view subtract(s: Point): Z = s.x - s.y;
 view multiply(s: Point): Z = s.x * s.y;
 view nested(s: Point): Z = ((s.x + 3) * (s.y - 2)) - (-s.x);
 view zero(s: Point): Z = s.x - s.x;
 law required equal(s: Point): s.x + s.y = 1;
 law required product_zero(s: Point): s.x * s.y = 0;
 law required ordered(s: Point): s.x < s.y;
 view negate(s: Point): Bool = not s.p;
 view both(s: Point): Bool = s.p and s.q;
 view either(s: Point): Bool = s.p or s.q;
 view implication(s: Point): Bool = s.p implies s.q;
 view same(s: Point): Bool = s.p = s.q;
 view forced(s: Point): Bool = false and s.p;
 view open(s: Point): Bool = true or s.p;
 view vacuous(s: Point): Bool = false implies s.p;
 law required not_law(s: Point): not s.p;
 law required both_law(s: Point): s.p and s.q;
 law required either_law(s: Point): s.p or s.q;
 law required implies_law(s: Point): s.p implies s.q;
 law required guarded_or(s: Point) when true: false or false;
 law required guarded_and(s: Point) when true: true and false;
}}
"#
    );
    let mut atoms = vec![];
    for (name, value) in [("x", x), ("y", y)] {
        if let Some(v) = value {
            atoms.push(format!(r#"{{"id":"{name}","subject":"sample","field":"Measure.Point.{name}","value":"{v}","origin":"numbers"}}"#));
        }
    }
    for (name, value) in [("p", p), ("q", q)] {
        if let Some(v) = value {
            atoms.push(format!(r#"{{"id":"{name}","subject":"sample","field":"Measure.Point.{name}","value":{v},"origin":"logic"}}"#));
        }
    }
    let atoms = atoms.join(",");
    let map = format!(
        r#"{{"format":"archsig.archmap/2","semantics":"archsig/0.6.0",
      "vocabularies":[{{"namespace":"Measure","version":"1","digest":"{digest}"}}],
      "sources":[{{"id":"scan","uri":"urn:fixture:scalar-ops","revision":"r1","digest":"sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"}}],
      "origins":[{{"id":"base","mode":"observed","method":"対象を観測する。","locations":[{{"source":"scan","path":"state.model","span":[0,1]}}]}},
      {{"id":"numbers","mode":"observed","method":"整数を観測する。","locations":[{{"source":"scan","path":"numbers.model","span":[2,5]}}]}},
      {{"id":"logic","mode":"observed","method":"Boolを観測する。","locations":[{{"source":"scan","path":"logic.model","span":[6,9]}}]}}],
      "snapshots":[{{"id":"v","origin":"base","subjects":[{{"id":"sample","type":"Measure.Point","origin":"base"}}],"atoms":[{atoms}]}}]}}"#
    );
    InputSources::from_bytes(
        vec![definitions.as_bytes().to_vec()],
        law.into_bytes(),
        map.into_bytes(),
    )
}
fn run(inputs: InputSources, asks: &[&str]) -> (Json, CheckedInputs) {
    let checked = check_inputs(inputs.clone(), &mut control()).unwrap();
    (
        evaluate_observed_bytes(inputs, asks, &mut control())
            .unwrap()
            .wire(),
        checked,
    )
}
fn output<'a>(result: &'a Json, id: &str, ty: &str) -> Option<&'a Json> {
    let ns = nodes(result);
    let a = answer(result, id);
    obj(f(a, "outputs"))
        .get("value")
        .map(|r| val(target(&ns, r, ty)))
}

fn original_source<'a>(ns: &BTreeMap<&str, &'a Json>, evaluation: &Json) -> &'a Json {
    if let Some(first) = arr(f(evaluation, "arguments")).first() {
        let node = ns[txt(f(first, "node"))];
        if f(node, "type") == &Json::str("LawInstance") {
            return target(ns, f(val(node), "body"), "Expression");
        }
    }
    target(ns, f(val(evaluation), "expression"), "Expression")
}

// The finite Bool oracle is independent of the evaluator's expression traversal.
fn bool_oracle(name: &str, p: bool, q: bool) -> bool {
    match name.rsplit('.').next().unwrap() {
        "negate" | "not_law" => !p,
        "both" | "both_law" => p && q,
        "either" | "either_law" => p || q,
        "implication" | "implies_law" => !p || q,
        "same" => p == q,
        "forced" => false,
        "open" | "vacuous" => true,
        other => panic!("Bool completion oracle has no fixture {other}"),
    }
}
fn audit_completion(result: &Json, checked: &CheckedInputs, request: &Json, original: &Json) {
    let ns = nodes(result);
    let answer = answer(result, txt(f(request, "id")));
    let root = target(&ns, f(f(answer, "outputs"), "evaluation"), "Evaluation");
    if f(root, "id") == f(original, "id") {
        return;
    }
    let seed = target(&ns, f(val(root), "expression"), "Expression");
    let source = original_source(&ns, original);
    assert_eq!(f(val(seed), "location"), f(val(source), "location"));
    let (start, end) = span(f(val(seed), "location"));
    let text = std::str::from_utf8(&checked.sources().law().bytes()[start..end]).unwrap();
    let sample = &checked.archmap().snapshots[0].subjects[0];
    let mut fixed = BTreeMap::new();
    let mut fields = vec![];
    for name in ["p", "q"] {
        let field = sample
            .fields
            .iter()
            .find(|f| f.name == format!("Measure.Point.{name}"))
            .unwrap();
        match &field.slot {
            archsig::archmap::Slot::Known {
                value: archsig::archmap::Value::Bool(v),
                ..
            } => {
                fixed.insert(name, *v);
            }
            archsig::archmap::Slot::Missing if text.contains(&format!("s.{name}")) => {
                fields.push(name)
            }
            archsig::archmap::Slot::Missing => {}
            _ => panic!("fixture Bool field"),
        }
    }
    assert!(!fields.is_empty());
    let arguments = arr(f(root, "arguments"));
    assert_eq!(&arguments[0], f(val(root), "expression"));
    let domain = target(&ns, &arguments[1], "Domain");
    assert_eq!(f(val(domain), "kind"), &Json::str("finite"));
    assert_eq!(arr(f(domain, "arguments")).first(), Some(&arguments[0]));
    let domain_type = if fields.len() == 1 {
        Json::str("Bool")
    } else {
        Json::Arr(vec![
            Json::str("Tuple"),
            Json::str("Bool"),
            Json::str("Bool"),
        ])
    };
    assert_eq!(f(val(domain), "type"), &domain_type);
    let decode = |value: &Json| {
        let scalar = |v: &Json| {
            let Json::Bool(b) = v else {
                panic!("Bool assignment")
            };
            *b
        };
        if fields.len() == 1 {
            vec![scalar(value)]
        } else {
            arr(value).iter().map(scalar).collect::<Vec<_>>()
        }
    };
    let expected_rows = (0..(1 << fields.len()))
        .map(|mask| {
            (0..fields.len())
                .map(|bit| mask & (1 << bit) != 0)
                .collect::<Vec<_>>()
        })
        .collect::<BTreeSet<_>>();
    let members = arr(f(val(domain), "elements"));
    let mut member_rows = BTreeMap::new();
    for r in members {
        let member = ns[txt(f(r, "node"))];
        assert_eq!(f(member, "type"), &domain_type);
        assert_eq!(f(f(member, "rule"), "kind"), &Json::str("construction"));
        assert!(
            member_rows
                .insert(r.canonical(), decode(val(member)))
                .is_none()
        );
    }
    assert_eq!(
        member_rows.values().cloned().collect::<BTreeSet<_>>(),
        expected_rows
    );
    assert_eq!(members.len(), 1 << fields.len());
    let parts = arr(f(val(root), "parts"));
    assert_eq!(parts.len(), 1);
    assert!(!obj(&parts[0]).contains_key("residual"));
    let cases = arr(f(&parts[0], "children"));
    assert_eq!(cases.len(), members.len());
    let mut case_rows = BTreeMap::new();
    let mut case_values = BTreeMap::new();
    for r in cases {
        let case = target(&ns, r, "Evaluation");
        let case_source = original_source(&ns, case);
        assert_eq!(f(val(case_source), "location"), f(val(seed), "location"));
        let expression = target(&ns, f(val(case), "expression"), "Expression");
        let selected = [expression, case_source]
            .iter()
            .flat_map(|n| arr(f(n, "arguments")))
            .filter(|r| member_rows.contains_key(&r.canonical()))
            .map(Json::canonical)
            .collect::<BTreeSet<_>>();
        assert_eq!(
            selected.len(),
            1,
            "each actual case selects one real assignment member"
        );
        let row = member_rows[selected.first().unwrap()].clone();
        let mut assignment = fixed.clone();
        for (&field, &value) in fields.iter().zip(&row) {
            assignment.insert(field, value);
        }
        let expected = bool_oracle(
            txt(f(f(request, "head"), "name")),
            *assignment.get("p").unwrap_or(&false),
            *assignment.get("q").unwrap_or(&false),
        );
        let actual = target(&ns, f(val(case), "value"), "Bool");
        assert_eq!(val(actual), &Json::Bool(expected));
        assert_eq!(f(f(case, "scope"), "domain"), &Json::str("all_completions"));
        assert!(case_rows.insert(r.canonical(), row).is_none());
        case_values.insert(r.canonical(), expected);
    }
    assert_eq!(
        case_rows.values().cloned().collect::<BTreeSet<_>>(),
        expected_rows
    );
    let proofs = arr(f(answer, "evidence"))
        .iter()
        .map(|r| val(target(&ns, r, "Evidence")))
        .collect::<Vec<_>>();
    let covers = proofs
        .iter()
        .filter(|p| {
            f(p, "kind") == &Json::str("finite_exhaustion")
                && f(f(p, "data"), "domain") == &arguments[1]
        })
        .collect::<Vec<_>>();
    let pairs = proofs
        .iter()
        .filter(|p| f(p, "kind") == &Json::str("completion_pair"))
        .collect::<Vec<_>>();
    let unanimous = case_values
        .values()
        .all(|v| v == case_values.values().next().unwrap());
    if unanimous {
        assert_eq!(covers.len(), 1);
        assert!(pairs.is_empty());
        let data = f(covers[0], "data");
        assert_eq!(f(data, "checked"), &Json::Nat(cases.len() as u64));
        assert_eq!(
            arr(f(data, "instances"))
                .iter()
                .map(Json::canonical)
                .collect::<BTreeSet<_>>(),
            case_rows.keys().cloned().collect()
        );
        assert_eq!(
            val(target(&ns, f(val(root), "value"), "Bool")),
            &Json::Bool(*case_values.values().next().unwrap())
        );
    } else {
        assert!(covers.is_empty());
        assert_eq!(pairs.len(), 1);
        assert!(!obj(val(root)).contains_key("value"));
        let data = f(pairs[0], "data");
        assert_eq!(
            f(data, "fields"),
            &Json::Arr(
                fields
                    .iter()
                    .map(|field| Json::obj([
                        ("snapshot", Json::str("v")),
                        ("subject", Json::str("sample")),
                        ("field", Json::str(format!("Measure.Point.{field}")))
                    ]))
                    .collect()
            )
        );
        let mut result_values = vec![];
        let mut rows = vec![];
        for (binding, result) in [("first", "first_result"), ("second", "second_result")] {
            let r = f(data, result).canonical();
            let row = arr(f(data, binding))
                .iter()
                .map(|r| {
                    let value = target(&ns, r, "Bool");
                    assert_eq!(f(f(value, "rule"), "kind"), &Json::str("construction"));
                    let Json::Bool(b) = val(value) else {
                        panic!("Bool")
                    };
                    *b
                })
                .collect::<Vec<_>>();
            assert_eq!(case_rows[&r], row);
            rows.push(row);
            result_values.push(case_values[&r]);
        }
        assert_ne!(rows[0], rows[1]);
        assert_ne!(result_values[0], result_values[1]);
    }
}

fn audit(result: &Json, checked: &CheckedInputs) {
    let ns = nodes(result);
    let mut earlier = BTreeSet::new();
    for n in arr(f(result, "nodes")) {
        let mut rs = vec![];
        links(n, &mut rs);
        for r in rs {
            assert!(earlier.contains(r.as_str()), "Refは既出nodeだけへ向く");
        }
        assert!(earlier.insert(txt(f(n, "id"))));
        if f(n, "type") != &Json::str("Proposition") {
            assert!(!obj(n).contains_key("judgment"));
        }
        if let Some(v) = obj(n).get("value") {
            let mut rs = vec![];
            links(v, &mut rs);
            for r in rs {
                assert_ne!(f(ns[r.as_str()], "state"), &Json::str("blocked"));
            }
        }
        for support in arr(f(n, "support")) {
            if let Some(field) = obj(support).get("field") {
                let sample = &checked.archmap().snapshots[0].subjects[0];
                let slot = &sample
                    .fields
                    .iter()
                    .find(|item| item.name == txt(field))
                    .unwrap()
                    .slot;
                let archsig::archmap::Slot::Known { atom, origin, .. } = slot else {
                    panic!("欠測slotを支持Atomへ昇格しない")
                };
                assert_eq!(atom, txt(f(support, "atom")));
                let origin = checked
                    .archmap()
                    .origins
                    .iter()
                    .find(|o| &o.id == origin)
                    .unwrap();
                assert_eq!(origin.mode, archsig::archmap::Mode::Observed);
                let source = checked
                    .archmap()
                    .sources
                    .iter()
                    .find(|s| s.id == origin.locations[0].source)
                    .unwrap();
                assert_eq!(source.uri, "urn:fixture:scalar-ops");
                assert_eq!(
                    origin.locations[0].path,
                    if atom == "x" || atom == "y" {
                        "numbers.model"
                    } else {
                        "logic.model"
                    }
                );
            }
        }
    }
    for (request, a) in arr(f(result, "requests"))
        .iter()
        .zip(arr(f(result, "answers")))
    {
        assert_eq!(f(request, "id"), f(a, "id"));
        let scope = f(a, "scope");
        assert_eq!(f(scope, "modes"), &Json::Arr(vec![Json::str("observed")]));
        assert_eq!(f(scope, "readings"), &Json::Arr(vec![Json::str("Calc")]));
        assert_eq!(f(scope, "snapshots"), &Json::Arr(vec![Json::str("v")]));
        if let Some(claim) = obj(a).get("claim") {
            let prop = target(&ns, claim, "Proposition");
            assert_eq!(f(f(prop, "judgment"), "status"), f(a, "status"));
            assert_eq!(f(f(a, "outputs"), "proposition"), claim);
        }
        for reason in arr(f(a, "reasons"))
            .iter()
            .filter(|r| f(r, "code") == &Json::str("missing_observation"))
        {
            assert!(!arr(f(reason, "dependencies")).is_empty());
            for missing in arr(f(reason, "missing")) {
                assert_eq!(f(missing, "snapshot"), &Json::str("v"));
                assert_eq!(f(missing, "subject"), &Json::str("sample"));
                assert!(!obj(missing).contains_key("atom"));
            }
            for dep in arr(f(reason, "dependencies")) {
                let source = val(target(&ns, dep, "Expression"));
                let (s, e) = span(f(source, "location"));
                assert!(matches!(
                    &checked.sources().law().bytes()[s..e],
                    b"s.x" | b"s.y" | b"s.p" | b"s.q"
                ));
            }
        }
        let name = txt(f(f(request, "head"), "name"));
        let decl = &checked.law().declarations[name];
        let original = original_root(&ns, result, txt(f(a, "id")));
        let evaluations = evaluation_tree(&ns, original);
        audit_completion(result, checked, request, original);
        for (id, expr) in checked
            .law()
            .exprs
            .iter()
            .enumerate()
            .filter(|(_, e)| decl.span.0 <= e.span.0 && e.span.1 <= decl.span.1)
        {
            if checked.law().expr_type(id).is_none() {
                continue;
            }
            let evaluation = evaluations
                .iter()
                .copied()
                .find(|n| {
                    let expression = target(&ns, f(val(n), "expression"), "Expression");
                    f(val(expression), "kind") == &Json::str("source")
                        && span(f(val(expression), "location")) == expr.span
                        && arr(f(val(n), "parts"))
                            .iter()
                            .filter(|p| span(f(p, "location")) == expr.span)
                            .all(|p| {
                                arr(f(p, "children")).iter().all(|r| {
                                    let child = val(target(&ns, r, "Evaluation"));
                                    let source =
                                        val(target(&ns, f(child, "expression"), "Expression"));
                                    obj(source)
                                        .get("location")
                                        .is_none_or(|l| span(l) != expr.span)
                                })
                            })
                })
                .expect("元rootのAST各出現の実Evaluationを保持する");
            let source = target(&ns, f(val(evaluation), "expression"), "Expression");
            assert_eq!(span(f(val(source), "location")), expr.span);
            let bindings = arr(f(val(evaluation), "bindings"));
            assert_eq!(f(&bindings[0], "name"), &Json::str("s"));
            let binding = ns[txt(f(f(&bindings[0], "value"), "node"))];
            assert_eq!(
                val(binding),
                &Json::Arr(vec![Json::str("v"), Json::str("sample")])
            );
            let part = arr(f(val(evaluation), "parts"))
                .iter()
                .find(|p| span(f(p, "location")) == expr.span)
                .unwrap();
            let source_text =
                std::str::from_utf8(&checked.sources().law().bytes()[expr.span.0..expr.span.1])
                    .unwrap();
            let mut has_missing = false;
            for name in ["x", "y", "p", "q"] {
                if !source_text.contains(&format!("s.{name}")) {
                    continue;
                }
                let field = checked.archmap().snapshots[0].subjects[0]
                    .fields
                    .iter()
                    .find(|field| field.name == format!("Measure.Point.{name}"))
                    .unwrap();
                match &field.slot {
                    archsig::archmap::Slot::Known { atom, .. } => {
                        assert!(
                            arr(f(evaluation, "support"))
                                .iter()
                                .any(|fact| obj(fact).get("field")
                                    == Some(&Json::str(&field.name))
                                    && obj(fact).get("atom") == Some(&Json::str(atom))),
                            "演算の各既知operandの支持を失わない"
                        );
                    }
                    archsig::archmap::Slot::Missing => has_missing = true,
                }
            }
            assert_eq!(
                f(f(evaluation, "scope"), "domain"),
                &Json::str(if has_missing {
                    "all_completions"
                } else {
                    "finite_model"
                })
            );
            if let Some(value) = obj(part).get("value") {
                assert_eq!(
                    f(ns[txt(f(value, "node"))], "type"),
                    &checked.law().expr_type(id).unwrap().wire()
                );
            }
            let expected: Vec<_> = match &expr.kind {
                ExprKind::Binary { lhs, rhs, .. } => vec![
                    checked.law().exprs[*lhs].span,
                    checked.law().exprs[*rhs].span,
                ],
                ExprKind::Unary { operand, .. } | ExprKind::Group(operand) => {
                    vec![checked.law().exprs[*operand].span]
                }
                _ => vec![],
            };
            if !expected.is_empty() {
                let actual = arr(f(part, "children"))
                    .iter()
                    .map(|r| {
                        let ev = val(target(&ns, r, "Evaluation"));
                        let ex = val(target(&ns, f(ev, "expression"), "Expression"));
                        span(f(ex, "location"))
                    })
                    .collect::<Vec<_>>();
                assert_eq!(actual, expected, "両子評価を元AST順に残す");
            }
            if checked.law().expr_type(id) == Some(&archsig::types::Type::Bool) {
                let z_equality = matches!(&expr.kind,ExprKind::Binary{op:archsig::law::ast::BinOp::Eq,lhs,..} if checked.law().expr_type(*lhs)==Some(&archsig::types::Type::Z));
                if !z_equality {
                    assert!(
                        !obj(part).contains_key("residual"),
                        "一般Boolや不等式に整数残差を作らない"
                    );
                }
            }
        }
    }
}

#[test]
fn integer_operations_preserve_nested_values_equation_evidence_and_zero() {
    let asks = [
        "a=evaluate(Calc.add,s=@v/sample)",
        "s=evaluate(Calc.subtract,s=@v/sample)",
        "m=evaluate(Calc.multiply,s=@v/sample)",
        "n=evaluate(Calc.nested,s=@v/sample)",
        "z=evaluate(Calc.zero,s=@v/sample)",
        "eq=check(Calc.equal,s=@v/sample)",
        "bad=check(Calc.product_zero,s=@v/sample)",
        "order=check(Calc.ordered,s=@v/sample)",
    ];
    let (result, checked) = run(
        fixture(Some("-4"), Some("5"), Some(true), Some(false)),
        &asks,
    );
    assert_eq!(f(&result, "status"), &Json::str("complete"));
    for (id, expected) in [
        ("a", "1"),
        ("s", "-9"),
        ("m", "-20"),
        ("n", "-7"),
        ("z", "0"),
    ] {
        assert_eq!(output(&result, id, "Z"), Some(&Json::str(expected)));
        assert_eq!(f(answer(&result, id), "status"), &Json::str("established"));
    }
    assert_eq!(
        f(answer(&result, "eq"), "status"),
        &Json::str("established")
    );
    assert_eq!(f(answer(&result, "bad"), "status"), &Json::str("refuted"));
    assert_eq!(
        f(answer(&result, "order"), "status"),
        &Json::str("established")
    );
    let ns = nodes(&result);
    for (id, lhs, rhs, residual) in [("eq", "1", "1", "0"), ("bad", "-20", "0", "-20")] {
        let a = answer(&result, id);
        let evidence = arr(f(a, "evidence"))
            .iter()
            .map(|r| val(target(&ns, r, "Evidence")))
            .find(|e| f(e, "kind") == &Json::str("evaluation"))
            .unwrap();
        let d = f(evidence, "data");
        for (key, v) in [("lhs", lhs), ("rhs", rhs), ("residual", residual)] {
            assert_eq!(val(target(&ns, f(d, key), "Z")), &Json::str(v));
        }
    }
    audit(&result, &checked);
}

#[test]
fn integer_operations_keep_arbitrary_precision_beyond_i64() {
    let (result, checked) = run(
        fixture(Some("9223372036854775809"), Some("-2"), None, None),
        &[
            "a=evaluate(Calc.add,s=@v/sample)",
            "s=evaluate(Calc.subtract,s=@v/sample)",
            "m=evaluate(Calc.multiply,s=@v/sample)",
        ],
    );
    for (id, expected) in [
        ("a", "9223372036854775807"),
        ("s", "9223372036854775811"),
        ("m", "-18446744073709551618"),
    ] {
        assert_eq!(output(&result, id, "Z"), Some(&Json::str(expected)));
    }
    audit(&result, &checked);
}

#[test]
fn missing_integer_operands_stay_missing_without_fabricated_scalar_values() {
    let (result, checked) = run(
        fixture(None, Some("2"), Some(true), Some(false)),
        &[
            "a=evaluate(Calc.add,s=@v/sample)",
            "s=evaluate(Calc.subtract,s=@v/sample)",
            "m=evaluate(Calc.multiply,s=@v/sample)",
        ],
    );
    assert_eq!(f(&result, "status"), &Json::str("partial"));
    for id in ["a", "s", "m"] {
        let a = answer(&result, id);
        assert_eq!(f(a, "status"), &Json::str("undetermined"));
        assert!(output(&result, id, "Z").is_none());
        assert_eq!(f(f(a, "scope"), "domain"), &Json::str("all_completions"));
        let r = arr(f(a, "reasons"))
            .iter()
            .find(|r| f(r, "code") == &Json::str("missing_observation"))
            .unwrap();
        assert_eq!(
            f(&arr(f(r, "missing"))[0], "field"),
            &Json::str("Measure.Point.x")
        );
    }
    audit(&result, &checked);
}

fn boolean_truth_tables(cases: &[(usize, usize)]) {
    const F: Option<bool> = Some(false);
    const T: Option<bool> = Some(true);
    const U: Option<bool> = None;
    let both = [[F, F, F], [F, T, U], [F, U, U]];
    let either = [[F, T, U], [T, T, T], [U, T, U]];
    let implies = [[T, T, T], [F, T, U], [U, T, U]];
    let equal = [[T, F, U], [F, T, U], [U, U, U]];
    let not = [T, F, U];
    let asks = [
        "v_not=evaluate(Calc.negate,s=@v/sample)",
        "v_and=evaluate(Calc.both,s=@v/sample)",
        "v_or=evaluate(Calc.either,s=@v/sample)",
        "imp=evaluate(Calc.implication,s=@v/sample)",
        "eq=evaluate(Calc.same,s=@v/sample)",
        "nl=check(Calc.not_law,s=@v/sample)",
        "al=check(Calc.both_law,s=@v/sample)",
        "ol=check(Calc.either_law,s=@v/sample)",
        "il=check(Calc.implies_law,s=@v/sample)",
    ];
    for &(i, j) in cases {
        let p = [F, T, U][i];
        let q = [F, T, U][j];
        let (result, checked) = run(fixture(Some("1"), Some("2"), p, q), &asks);
        for (id, expected) in [
            ("v_not", not[i]),
            ("v_and", both[i][j]),
            ("v_or", either[i][j]),
            ("imp", implies[i][j]),
            ("eq", equal[i][j]),
        ] {
            let a = answer(&result, id);
            assert!(!obj(a).contains_key("claim"));
            assert_eq!(
                f(a, "status"),
                &Json::str(if expected.is_some() {
                    "established"
                } else {
                    "undetermined"
                })
            );
            assert_eq!(
                output(&result, id, "Bool"),
                expected.map(Json::Bool).as_ref()
            );
        }
        for (id, expected) in [
            ("nl", not[i]),
            ("al", both[i][j]),
            ("ol", either[i][j]),
            ("il", implies[i][j]),
        ] {
            assert_eq!(
                f(answer(&result, id), "status"),
                &Json::str(match expected {
                    Some(true) => "established",
                    Some(false) => "refuted",
                    None => "undetermined",
                })
            );
        }
        for id in ["v_and", "v_or", "imp", "al", "ol", "il"] {
            let a = answer(&result, id);
            assert_eq!(
                f(f(a, "scope"), "domain"),
                &Json::str(if p.is_none() || q.is_none() {
                    "all_completions"
                } else {
                    "finite_model"
                })
            );
            let missing: BTreeSet<_> = arr(f(a, "reasons"))
                .iter()
                .filter(|r| f(r, "code") == &Json::str("missing_observation"))
                .flat_map(|r| arr(f(r, "missing")))
                .map(|m| txt(f(m, "field")).to_owned())
                .collect();
            let expected: BTreeSet<_> = [("Measure.Point.p", p), ("Measure.Point.q", q)]
                .into_iter()
                .filter(|(_, v)| v.is_none())
                .map(|(n, _)| n.to_owned())
                .collect();
            assert_eq!(
                missing, expected,
                "短絡で確定しても両raw operandの欠測identityを残す"
            );
        }
        audit(&result, &checked);
    }
}

#[test]
fn boolean_truth_tables_distinguish_values_law_judgments_and_unknown_slots() {
    boolean_truth_tables(&[(0, 0), (0, 1), (1, 0), (1, 1)]);
}

#[test]
fn boolean_truth_tables_with_exactly_one_unknown_slot() {
    boolean_truth_tables(&[(0, 2), (1, 2), (2, 0), (2, 1)]);
}

#[test]
fn boolean_truth_tables_with_both_slots_unknown() {
    boolean_truth_tables(&[(2, 2)]);
}

#[test]
fn literal_boolean_constants_determine_results_without_filling_missing_fields() {
    let (result, checked) = run(
        fixture(None, None, None, None),
        &[
            "f=evaluate(Calc.forced,s=@v/sample)",
            "t=evaluate(Calc.open,s=@v/sample)",
            "i=evaluate(Calc.vacuous,s=@v/sample)",
        ],
    );
    assert_eq!(f(&result, "status"), &Json::str("complete"));
    for (id, expected) in [("f", false), ("t", true), ("i", true)] {
        assert_eq!(output(&result, id, "Bool"), Some(&Json::Bool(expected)));
        assert_eq!(f(answer(&result, id), "status"), &Json::str("established"));
        assert_eq!(
            f(f(answer(&result, id), "scope"), "domain"),
            &Json::str("all_completions")
        );
    }
    audit(&result, &checked);
}

#[test]
fn guarded_boolean_binary_laws_use_result_versus_true_as_refutation_evidence() {
    let (result, checked) = run(
        fixture(Some("1"), Some("2"), Some(true), Some(false)),
        &[
            "v_or=check(Calc.guarded_or,s=@v/sample)",
            "v_and=check(Calc.guarded_and,s=@v/sample)",
        ],
    );
    assert_eq!(f(&result, "status"), &Json::str("complete"));
    let ns = nodes(&result);
    for id in ["v_or", "v_and"] {
        let a = answer(&result, id);
        assert_eq!(f(a, "status"), &Json::str("refuted"));
        let evaluation = target(&ns, f(f(a, "outputs"), "evaluation"), "Evaluation");
        assert_eq!(
            f(val(evaluation), "applicability"),
            &Json::str("applicable")
        );
        for evidence in arr(f(a, "evidence")) {
            let e = val(target(&ns, evidence, "Evidence"));
            let d = f(e, "data");
            assert!(!obj(d).contains_key("residual"));
            let (left, right) = if f(e, "kind") == &Json::str("counterexample") {
                ("left", "right")
            } else {
                ("lhs", "rhs")
            };
            assert_eq!(val(target(&ns, f(d, left), "Bool")), &Json::Bool(false));
            assert_eq!(
                val(target(&ns, f(d, right), "Bool")),
                &Json::Bool(true),
                "一般Bool二項を左右比較の反証へ読み替えない"
            );
        }
    }
    audit(&result, &checked);
}

#[test]
fn memory_stop_inside_boolean_operator_keeps_prior_integer_and_original_reason() {
    let seed = "seed=evaluate(Calc.add,s=@v/sample)";
    let count = Rc::new(Cell::new(0));
    let seen = count.clone();
    let mut baseline = Control::new(Limits::default(), move |point| {
        if point == Checkpoint::Expression {
            seen.set(seen.get() + 1);
        }
        Usage::default()
    });
    evaluate_observed_bytes(
        fixture(Some("2"), Some("3"), None, Some(false)),
        &[seed],
        &mut baseline,
    )
    .unwrap();
    let target = count.get() + 3;
    let expressions = Rc::new(Cell::new(0));
    let probes = Rc::new(Cell::new(0));
    let frozen = Rc::new(Cell::new(None));
    let (seen, calls, stopped) = (expressions.clone(), probes.clone(), frozen.clone());
    let mut c = Control::new(
        Limits {
            time_ms: None,
            memory_mib: Some(1),
        },
        move |point| {
            calls.set(calls.get() + 1);
            if point == Checkpoint::Expression {
                seen.set(seen.get() + 1);
                if seen.get() == target {
                    stopped.set(Some(calls.get()));
                    return Usage {
                        memory_mib: 1,
                        ..Usage::default()
                    };
                }
            }
            Usage::default()
        },
    );
    let result = evaluate_observed_bytes(
        fixture(Some("2"), Some("3"), None, Some(false)),
        &[
            seed,
            "current=check(Calc.both_law,s=@v/sample)",
            "later=check(Calc.equal,s=@v/sample)",
        ],
        &mut c,
    )
    .unwrap()
    .wire();
    assert_eq!(f(&result, "status"), &Json::str("interrupted"));
    assert_eq!(output(&result, "seed", "Z"), Some(&Json::str("5")));
    assert_eq!(
        f(answer(&result, "seed"), "status"),
        &Json::str("established")
    );
    for id in ["current", "later"] {
        let a = answer(&result, id);
        assert_eq!(f(a, "status"), &Json::str("undetermined"));
        assert!(obj(f(a, "outputs")).is_empty());
        let reason = arr(f(a, "reasons"))
            .iter()
            .find(|r| f(r, "code") == &Json::str("budget_exhausted"))
            .unwrap();
        assert_eq!(
            f(reason, "details"),
            &Json::obj([
                ("resource", Json::str("memory_mib")),
                ("limit", Json::str("1")),
                ("observed", Json::str("1"))
            ])
        );
    }
    assert_eq!(expressions.get(), target);
    assert_eq!(Some(probes.get()), frozen.get());
    let before = probes.get();
    assert!(c.checkpoint(Checkpoint::Expression).is_err());
    assert_eq!(probes.get(), before);
}
