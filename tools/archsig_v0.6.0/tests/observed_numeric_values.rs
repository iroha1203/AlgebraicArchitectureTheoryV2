//! AC4数値型段階: Q/Fp/数値Tupleの値・残差・各出現と由来を三入力byteから検査する。
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
fn target<'a>(ns: &BTreeMap<&str, &'a Json>, r: &Json, ty: &Json) -> &'a Json {
    assert_eq!(obj(r).len(), 1);
    let n = ns[txt(f(r, "node"))];
    assert_eq!(f(n, "type"), ty);
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

fn span(location: &Json) -> (usize, usize) {
    assert_eq!(f(location, "input"), &Json::str("law"));
    let a = arr(f(location, "span"));
    let nat = |n: &Json| {
        let Json::Nat(v) = n else { panic!("Nat") };
        *v as usize
    };
    (nat(&a[0]), nat(&a[1]))
}

fn fixture(omitted: &[&str], body: &str) -> InputSources {
    let definitions = r#"{"format":"archsig.atom-definition/1","semantics":"archsig/0.6.0",
      "vocabularies":[{"semantics":"archsig/0.6.0","namespace":"Numeric","version":"1","dependencies":[],
      "declarations":[{"kind":"entity","name":"Numeric.Sample","meaning":"小さい数値を観測する対象。","parameters":[],
      "fields":[{"name":"q","type":"Q","meaning":"有理数。"},
      {"name":"f","type":["Fp","5"],"meaning":"五元体の値。"},
      {"name":"g","type":["Fp","7"],"meaning":"七元体の値。"},
      {"name":"t","type":["Tuple","Z","Q",["Tuple",["Fp","5"],"Z"]],"meaning":"混合した数値Tuple。"},
      {"name":"p","type":"Bool","meaning":"条件。"}],"alignments":[]}]}]}"#;
    let checked = check_definitions(&[("definition0", definitions.as_bytes())]).unwrap();
    let digest = &checked.vocabularies["Numeric"].digest;
    let law = format!(
        r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Calc {{
 use vocabulary Numeric version "1" digest "{digest}";
 {body}
}}
"#
    );
    let atoms = [
        ("q", r#"["-2","3"]"#),
        ("f", r#""4""#),
        ("g", r#""4""#),
        ("t", r#"["-2",["1","2"],["4","3"]]"#),
        ("p", "false"),
    ].into_iter().filter(|(name, _)| !omitted.contains(name)).map(|(name, value)| {
        format!(r#"{{"id":"{name}","subject":"sample","field":"Numeric.Sample.{name}","value":{value},"origin":"values"}}"#)
    }).collect::<Vec<_>>().join(",");
    let map = format!(
        r#"{{"format":"archsig.archmap/2","semantics":"archsig/0.6.0",
      "vocabularies":[{{"namespace":"Numeric","version":"1","digest":"{digest}"}}],
      "sources":[{{"id":"scan","uri":"urn:fixture:numeric-values","revision":"r1","digest":"sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"}}],
      "origins":[{{"id":"base","mode":"observed","method":"対象を観測する。","locations":[{{"source":"scan","path":"state.model","span":[0,1]}}]}},
      {{"id":"values","mode":"observed","method":"数値と条件を観測する。","locations":[{{"source":"scan","path":"values.model","span":[2,5]}}]}}],
      "snapshots":[{{"id":"v","origin":"base","subjects":[{{"id":"sample","type":"Numeric.Sample","origin":"base"}}],"atoms":[{atoms}]}}]}}"#
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
fn fp(modulus: &str) -> Json {
    Json::Arr(vec![Json::str("Fp"), Json::str(modulus)])
}
fn tuple_type() -> Json {
    Json::Arr(vec![
        Json::str("Tuple"),
        Json::str("Z"),
        Json::str("Q"),
        Json::Arr(vec![Json::str("Tuple"), fp("5"), Json::str("Z")]),
    ])
}
fn q(n: &str, d: &str) -> Json {
    Json::Arr(vec![Json::str(n), Json::str(d)])
}
fn tuple(z: &str, n: &str, d: &str, f: &str, inner_z: &str) -> Json {
    Json::Arr(vec![
        Json::str(z),
        q(n, d),
        Json::Arr(vec![Json::str(f), Json::str(inner_z)]),
    ])
}
fn output<'a>(result: &'a Json, id: &str, ty: &Json) -> Option<&'a Json> {
    let ns = nodes(result);
    obj(f(answer(result, id), "outputs"))
        .get("value")
        .map(|r| val(target(&ns, r, ty)))
}
fn assert_output(result: &Json, id: &str, ty: &Json, expected: Json) {
    assert_eq!(
        f(answer(result, id), "status"),
        &Json::str("established"),
        "{id}"
    );
    assert!(
        !obj(answer(result, id)).contains_key("claim"),
        "viewの値はLaw判断へ昇格しない"
    );
    assert_eq!(output(result, id, ty), Some(&expected), "{id}");
}

fn evaluation_tree<'a>(ns: &BTreeMap<&str, &'a Json>, root: &'a Json) -> Vec<&'a Json> {
    let mut pending = vec![root];
    let mut seen = BTreeSet::new();
    let mut evaluations = Vec::new();
    while let Some(evaluation) = pending.pop() {
        assert_eq!(f(evaluation, "type"), &Json::str("Evaluation"));
        if !seen.insert(txt(f(evaluation, "id"))) {
            continue;
        }
        evaluations.push(evaluation);
        for part in arr(f(val(evaluation), "parts")) {
            for child in arr(f(part, "children")) {
                pending.push(target(ns, child, &Json::str("Evaluation")));
            }
        }
    }
    evaluations
}
fn original_evaluation<'a>(ns: &BTreeMap<&str, &'a Json>, root: &'a Json) -> &'a Json {
    let source = target(ns, f(val(root), "expression"), &Json::str("Expression"));
    let original = arr(f(source, "arguments"))
        .iter()
        .filter_map(|reference| {
            let node = ns[txt(f(reference, "node"))];
            (f(node, "type") == &Json::str("Evaluation")).then_some(node)
        })
        .collect::<Vec<_>>();
    if original.is_empty() {
        return root;
    }
    assert_eq!(
        original.len(),
        1,
        "CompletionSeedから元Evaluationへ直接戻る"
    );
    let arguments = arr(f(root, "arguments"));
    assert_eq!(&arguments[0], f(val(root), "expression"));
    let domain = target(ns, &arguments[1], &Json::str("Domain"));
    assert_eq!(
        arr(f(domain, "arguments")).first(),
        Some(f(val(root), "expression"))
    );
    let original_source = target(
        ns,
        f(val(original[0]), "expression"),
        &Json::str("Expression"),
    );
    assert_eq!(
        f(val(source), "location"),
        f(val(original_source), "location")
    );
    original[0]
}

fn numeric(ty: &archsig::types::Type) -> bool {
    use archsig::types::Type;
    match ty {
        Type::Z | Type::Q | Type::Fp(_) => true,
        Type::Tuple(items) => items.iter().all(numeric),
        _ => false,
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
                assert_ne!(f(ns[r.as_str()], "state"), &Json::str("partial"));
            }
        }
        for support in arr(f(n, "support")) {
            assert_eq!(f(support, "snapshot"), &Json::str("v"));
            assert_eq!(f(support, "subject"), &Json::str("sample"));
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
                assert_eq!(source.uri, "urn:fixture:numeric-values");
                assert_eq!(origin.locations[0].path, "values.model");
                assert_eq!(origin.locations[0].span, Some((2, 5)));
            } else {
                assert!(!obj(support).contains_key("atom"));
                let sample = &checked.archmap().snapshots[0].subjects[0];
                let origin = checked
                    .archmap()
                    .origins
                    .iter()
                    .find(|o| o.id == sample.origin)
                    .unwrap();
                assert_eq!(origin.mode, archsig::archmap::Mode::Observed);
                let source = checked
                    .archmap()
                    .sources
                    .iter()
                    .find(|s| s.id == origin.locations[0].source)
                    .unwrap();
                assert_eq!(source.uri, "urn:fixture:numeric-values");
                assert_eq!(origin.locations[0].path, "state.model");
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
            let prop = target(&ns, claim, &Json::str("Proposition"));
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
                let source = val(target(&ns, dep, &Json::str("Expression")));
                let (s, e) = span(f(source, "location"));
                assert!(matches!(
                    &checked.sources().law().bytes()[s..e],
                    b"s.q" | b"s.f" | b"s.g" | b"s.t" | b"s.p"
                ));
            }
        }
        let name = txt(f(f(request, "head"), "name"));
        let decl = &checked.law().declarations[name];
        let root = target(
            &ns,
            f(f(a, "outputs"), "evaluation"),
            &Json::str("Evaluation"),
        );
        let original = original_evaluation(&ns, root);
        let mut runs = vec![(evaluation_tree(&ns, original), false)];
        if f(root, "id") != f(original, "id") {
            for part in arr(f(val(root), "parts")) {
                for child in arr(f(part, "children")) {
                    runs.push((
                        evaluation_tree(&ns, target(&ns, child, &Json::str("Evaluation"))),
                        true,
                    ));
                }
            }
        }
        for (evaluations, completion_case) in runs {
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
                let matching = evaluations
                    .iter()
                    .copied()
                    .filter(|evaluation| {
                        let source = target(
                            &ns,
                            f(val(evaluation), "expression"),
                            &Json::str("Expression"),
                        );
                        f(val(source), "kind") == &Json::str("source")
                            && span(f(val(source), "location")) == expr.span
                            && arr(f(val(evaluation), "parts"))
                                .iter()
                                .filter(|p| span(f(p, "location")) == expr.span)
                                .all(|p| {
                                    arr(f(p, "children")).iter().all(|r| {
                                        let child = val(target(&ns, r, &Json::str("Evaluation")));
                                        let expression = val(target(
                                            &ns,
                                            f(child, "expression"),
                                            &Json::str("Expression"),
                                        ));
                                        obj(expression)
                                            .get("location")
                                            .is_none_or(|location| span(location) != expr.span)
                                    })
                                })
                    })
                    .collect::<Vec<_>>();
                assert_eq!(
                    matching.len(),
                    1,
                    "各元AST出現に一つの実Evaluationを保持する"
                );
                let evaluation = matching[0];
                let source = target(
                    &ns,
                    f(val(evaluation), "expression"),
                    &Json::str("Expression"),
                );
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
                for name in ["q", "f", "g", "t", "p"] {
                    if !source_text.contains(&format!("s.{name}")) {
                        continue;
                    }
                    let field = checked.archmap().snapshots[0].subjects[0]
                        .fields
                        .iter()
                        .find(|field| field.name == format!("Numeric.Sample.{name}"))
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
                    &Json::str(if has_missing || completion_case {
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
                    ExprKind::Unary { operand, .. }
                    | ExprKind::Group(operand)
                    | ExprKind::Index { base: operand, .. }
                    | ExprKind::Field { base: operand, .. } => {
                        vec![checked.law().exprs[*operand].span]
                    }
                    ExprKind::Tuple(items) | ExprKind::Call { args: items, .. } => items
                        .iter()
                        .map(|id| checked.law().exprs[*id].span)
                        .collect(),
                    _ => vec![],
                };
                if !expected.is_empty() {
                    let actual = arr(f(part, "children"))
                        .iter()
                        .map(|r| {
                            let ev = val(target(&ns, r, &Json::str("Evaluation")));
                            let ex =
                                val(target(&ns, f(ev, "expression"), &Json::str("Expression")));
                            span(f(ex, "location"))
                        })
                        .collect::<Vec<_>>();
                    assert_eq!(actual, expected, "両子評価を元AST順に残す");
                }
                if let Some(residual) = obj(part).get("residual") {
                    let ExprKind::Binary {
                        op: archsig::law::ast::BinOp::Eq,
                        lhs,
                        ..
                    } = &expr.kind
                    else {
                        panic!("数値等号だけが残差を持つ")
                    };
                    assert_eq!(
                        f(ns[txt(f(residual, "node"))], "type"),
                        &checked.law().expr_type(*lhs).unwrap().wire()
                    );
                }
                if checked.law().expr_type(id) == Some(&archsig::types::Type::Bool) {
                    let numeric_equality = matches!(&expr.kind,ExprKind::Binary{op:archsig::law::ast::BinOp::Eq,lhs,..} if checked.law().expr_type(*lhs).is_some_and(numeric));
                    if !numeric_equality {
                        assert!(
                            !obj(part).contains_key("residual"),
                            "一般Boolや不等式に数値残差を作らない"
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn rational_values_reduce_keep_positive_denominators_and_exact_order() {
    let (result, checked) = run(
        fixture(
            &[],
            r#"
 view field(s: Sample): Q = s.q;
 view literal(s: Sample): Q = -3;
 view reduced(s: Sample): Q = rat(2,4);
 view add(s: Sample): Q = s.q + rat(5,6);
 view subtract(s: Sample): Q = s.q - rat(5,6);
 view multiply(s: Sample): Q = s.q * rat(5,6);
 view negate(s: Sample): Q = -s.q;
 view zero(s: Sample): Q = s.q - s.q;
 view lt(s: Sample): Bool = s.q < -rat(1,2);
 view le(s: Sample): Bool = s.q <= -rat(2,3);
 view gt(s: Sample): Bool = s.q > -1;
 view ge(s: Sample): Bool = s.q >= -rat(2,3);
 view ne(s: Sample): Bool = s.q != 0;
"#,
        ),
        &[
            "field=evaluate(Calc.field,s=@v/sample)",
            "literal=evaluate(Calc.literal,s=@v/sample)",
            "reduced=evaluate(Calc.reduced,s=@v/sample)",
            "add=evaluate(Calc.add,s=@v/sample)",
            "sub=evaluate(Calc.subtract,s=@v/sample)",
            "mul=evaluate(Calc.multiply,s=@v/sample)",
            "neg=evaluate(Calc.negate,s=@v/sample)",
            "zero=evaluate(Calc.zero,s=@v/sample)",
            "lt=evaluate(Calc.lt,s=@v/sample)",
            "le=evaluate(Calc.le,s=@v/sample)",
            "gt=evaluate(Calc.gt,s=@v/sample)",
            "ge=evaluate(Calc.ge,s=@v/sample)",
            "ne=evaluate(Calc.ne,s=@v/sample)",
        ],
    );
    assert_eq!(f(&result, "status"), &Json::str("complete"));
    // -2/3 + 5/6 = 1/6; -2/3 - 5/6 = -3/2; (-2/3)(5/6) = -5/9.
    for (id, n, d) in [
        ("field", "-2", "3"),
        ("literal", "-3", "1"),
        ("reduced", "1", "2"),
        ("add", "1", "6"),
        ("sub", "-3", "2"),
        ("mul", "-5", "9"),
        ("neg", "2", "3"),
        ("zero", "0", "1"),
    ] {
        assert_output(&result, id, &Json::str("Q"), q(n, d));
    }
    for id in ["lt", "le", "gt", "ge", "ne"] {
        assert_output(&result, id, &Json::str("Bool"), Json::Bool(true));
    }
    audit(&result, &checked);
}

#[test]
fn finite_field_values_reduce_modulo_and_keep_distinct_declared_fields() {
    let (result, checked) = run(
        fixture(
            &[],
            r#"
 view field(s: Sample): Fp(5) = s.f;
 view other(s: Sample): Fp(7) = s.g;
 view add(s: Sample): Fp(5) = s.f + 3;
 view subtract(s: Sample): Fp(5) = s.f - 1;
 view multiply(s: Sample): Fp(5) = s.f * 3;
 view negate(s: Sample): Fp(5) = -s.f;
 view literal(s: Sample): Fp(5) = -2;
 view zero(s: Sample): Fp(5) = s.f - s.f;
 view equal(s: Sample): Bool = s.f = -1;
 view different(s: Sample): Bool = s.f != 3;
"#,
        ),
        &[
            "field=evaluate(Calc.field,s=@v/sample)",
            "other=evaluate(Calc.other,s=@v/sample)",
            "add=evaluate(Calc.add,s=@v/sample)",
            "sub=evaluate(Calc.subtract,s=@v/sample)",
            "mul=evaluate(Calc.multiply,s=@v/sample)",
            "neg=evaluate(Calc.negate,s=@v/sample)",
            "literal=evaluate(Calc.literal,s=@v/sample)",
            "zero=evaluate(Calc.zero,s=@v/sample)",
            "eq=evaluate(Calc.equal,s=@v/sample)",
            "ne=evaluate(Calc.different,s=@v/sample)",
        ],
    );
    assert_eq!(f(&result, "status"), &Json::str("complete"));
    // 4+3=7≡2, 4*3=12≡2, -4≡1, -2≡3 (mod 5).
    for (id, value) in [
        ("field", "4"),
        ("add", "2"),
        ("sub", "3"),
        ("mul", "2"),
        ("neg", "1"),
        ("literal", "3"),
        ("zero", "0"),
    ] {
        assert_output(&result, id, &fp("5"), Json::str(value));
    }
    assert_output(&result, "other", &fp("7"), Json::str("4"));
    for id in ["eq", "ne"] {
        assert_output(&result, id, &Json::str("Bool"), Json::Bool(true));
    }
    audit(&result, &checked);
}

#[test]
fn nested_numeric_tuple_values_preserve_components_operations_and_projection() {
    let (result, checked) = run(
        fixture(
            &[],
            r#"
 view field(s: Sample): (Z,Q,(Fp(5),Z)) = s.t;
 view constructed(s: Sample): (Z,Q,(Fp(5),Z)) = (-2,s.q,(s.f,3));
 view literal(s: Sample): (Z,Q,(Fp(5),Z)) = (-2,rat(2,4),(-1,3));
 view add(s: Sample): (Z,Q,(Fp(5),Z)) = s.t + (3,rat(1,2),(2,-4));
 view subtract(s: Sample): (Z,Q,(Fp(5),Z)) = s.t - (3,rat(1,2),(2,-4));
 view multiply(s: Sample): (Z,Q,(Fp(5),Z)) = s.t * (3,rat(1,2),(2,-4));
 view negate(s: Sample): (Z,Q,(Fp(5),Z)) = -s.t;
 view zero(s: Sample): (Z,Q,(Fp(5),Z)) = s.t - s.t;
 view project(s: Sample): Fp(5) = (s.t).2.0;
 view fraction(s: Sample): Q = s.t.1;
 view different(s: Sample): Bool = s.t != (0,rat(1,2),(1,3));
"#,
        ),
        &[
            "field=evaluate(Calc.field,s=@v/sample)",
            "construct=evaluate(Calc.constructed,s=@v/sample)",
            "literal=evaluate(Calc.literal,s=@v/sample)",
            "add=evaluate(Calc.add,s=@v/sample)",
            "sub=evaluate(Calc.subtract,s=@v/sample)",
            "mul=evaluate(Calc.multiply,s=@v/sample)",
            "neg=evaluate(Calc.negate,s=@v/sample)",
            "zero=evaluate(Calc.zero,s=@v/sample)",
            "project=evaluate(Calc.project,s=@v/sample)",
            "fraction=evaluate(Calc.fraction,s=@v/sample)",
            "different=evaluate(Calc.different,s=@v/sample)",
        ],
    );
    assert_eq!(f(&result, "status"), &Json::str("complete"));
    // t=(-2,1/2,(4,3)); the final pair uses Fp(5) and Z respectively.
    for (id, value) in [
        ("field", tuple("-2", "1", "2", "4", "3")),
        ("construct", tuple("-2", "-2", "3", "4", "3")),
        ("literal", tuple("-2", "1", "2", "4", "3")),
        ("add", tuple("1", "1", "1", "1", "-1")),
        ("sub", tuple("-5", "0", "1", "2", "7")),
        ("mul", tuple("-6", "1", "4", "3", "-12")),
        ("neg", tuple("2", "-1", "2", "1", "-3")),
        ("zero", tuple("0", "0", "1", "0", "0")),
    ] {
        assert_output(&result, id, &tuple_type(), value);
    }
    assert_output(&result, "project", &fp("5"), Json::str("4"));
    assert_output(&result, "fraction", &Json::str("Q"), q("1", "2"));
    assert_output(&result, "different", &Json::str("Bool"), Json::Bool(true));
    audit(&result, &checked);
}

#[test]
fn numeric_equalities_keep_typed_original_sides_and_residuals_but_bool_has_none() {
    let (result, checked) = run(
        fixture(
            &[],
            r#"
 view same(s: Sample): Bool = s.q = rat(1,3);
 view flag(s: Sample): Bool = s.p;
 law required rational(s: Sample): s.q = rat(1,3);
 law required field(s: Sample): s.f = 1;
 law required tuple(s: Sample): s.t = (0,rat(1,2),(1,3));
 law required exact(s: Sample): s.q + rat(2,3) = 0;
 law required flag_law(s: Sample): s.p;
 law required flag_equal(s: Sample): s.p = true;
"#,
        ),
        &[
            "same=evaluate(Calc.same,s=@v/sample)",
            "flag=evaluate(Calc.flag,s=@v/sample)",
            "q=check(Calc.rational,s=@v/sample)",
            "f=check(Calc.field,s=@v/sample)",
            "t=check(Calc.tuple,s=@v/sample)",
            "zero=check(Calc.exact,s=@v/sample)",
            "bool=check(Calc.flag_law,s=@v/sample)",
            "bool_eq=check(Calc.flag_equal,s=@v/sample)",
        ],
    );
    assert_eq!(f(&result, "status"), &Json::str("complete"));
    assert_output(&result, "same", &Json::str("Bool"), Json::Bool(false));
    assert_output(&result, "flag", &Json::str("Bool"), Json::Bool(false));
    let ns = nodes(&result);
    for (id, ty, left, right, residual, status) in [
        (
            "q",
            Json::str("Q"),
            q("-2", "3"),
            q("1", "3"),
            q("-1", "1"),
            "refuted",
        ),
        (
            "f",
            fp("5"),
            Json::str("4"),
            Json::str("1"),
            Json::str("3"),
            "refuted",
        ),
        (
            "t",
            tuple_type(),
            tuple("-2", "1", "2", "4", "3"),
            tuple("0", "1", "2", "1", "3"),
            tuple("-2", "0", "1", "3", "0"),
            "refuted",
        ),
        (
            "zero",
            Json::str("Q"),
            q("0", "1"),
            q("0", "1"),
            q("0", "1"),
            "established",
        ),
    ] {
        let a = answer(&result, id);
        assert_eq!(f(a, "status"), &Json::str(status));
        let evaluation = arr(f(a, "evidence"))
            .iter()
            .map(|r| val(target(&ns, r, &Json::str("Evidence"))))
            .find(|e| f(e, "kind") == &Json::str("evaluation"))
            .unwrap();
        let data = f(evaluation, "data");
        assert_ne!(
            f(data, "lhs"),
            f(data, "rhs"),
            "同じ値でも元左右の参照を区別する"
        );
        for (key, expected) in [
            ("lhs", left.clone()),
            ("rhs", right.clone()),
            ("residual", residual),
        ] {
            assert_eq!(val(target(&ns, f(data, key), &ty)), &expected, "{id}.{key}");
        }
        if status == "refuted" {
            let counterexample = arr(f(a, "evidence"))
                .iter()
                .map(|r| val(target(&ns, r, &Json::str("Evidence"))))
                .find(|e| f(e, "kind") == &Json::str("counterexample"))
                .unwrap();
            assert_eq!(
                val(target(&ns, f(f(counterexample, "data"), "left"), &ty)),
                &left
            );
            assert_eq!(
                val(target(&ns, f(f(counterexample, "data"), "right"), &ty)),
                &right
            );
        }
    }
    for id in ["bool", "bool_eq"] {
        let a = answer(&result, id);
        assert_eq!(f(a, "status"), &Json::str("refuted"));
        for evidence in arr(f(a, "evidence")) {
            assert!(
                !obj(f(
                    val(target(&ns, evidence, &Json::str("Evidence"))),
                    "data"
                ))
                .contains_key("residual")
            );
        }
    }
    audit(&result, &checked);
}

#[test]
fn missing_numeric_slots_keep_identity_children_and_scope_without_filling_components() {
    let (result, checked) = run(
        fixture(
            &["q", "f", "t"],
            r#"
 view rational(s: Sample): Q = s.q * 0;
 view field(s: Sample): Fp(5) = s.f - s.f;
 view tuple(s: Sample): (Z,Q,(Fp(5),Z)) = s.t + (1,rat(1,2),(0,0));
 view constructed(s: Sample): (Q,Fp(7)) = (s.q,s.g);
 view project(s: Sample): Z = s.t.0;
 view pair(s: Sample): (Q,Fp(5)) = (s.q,s.f);
"#,
        ),
        &[
            "q=evaluate(Calc.rational,s=@v/sample)",
            "f=evaluate(Calc.field,s=@v/sample)",
            "t=evaluate(Calc.tuple,s=@v/sample)",
            "construct=evaluate(Calc.constructed,s=@v/sample)",
            "project=evaluate(Calc.project,s=@v/sample)",
            "pair=evaluate(Calc.pair,s=@v/sample)",
        ],
    );
    assert_eq!(f(&result, "status"), &Json::str("partial"));
    for (id, missing) in [
        ("q", vec!["q"]),
        ("f", vec!["f"]),
        ("t", vec!["t"]),
        ("construct", vec!["q"]),
        ("project", vec!["t"]),
        ("pair", vec!["q", "f"]),
    ] {
        let a = answer(&result, id);
        if id == "q" {
            assert_output(
                &result,
                id,
                &Json::str("Q"),
                Json::Arr(vec![Json::str("0"), Json::str("1")]),
            );
        } else if id == "f" {
            assert_output(&result, id, &fp("5"), Json::str("0"));
        } else {
            assert_eq!(f(a, "status"), &Json::str("undetermined"));
            assert!(
                !obj(f(a, "outputs")).contains_key("value"),
                "未決定の欠測を確定値へ補わない: {id}"
            );
        }
        assert_eq!(f(f(a, "scope"), "domain"), &Json::str("all_completions"));
        let actual: BTreeSet<_> = arr(f(a, "reasons"))
            .iter()
            .filter(|r| f(r, "code") == &Json::str("missing_observation"))
            .flat_map(|r| arr(f(r, "missing")))
            .map(|p| txt(f(p, "field")).to_owned())
            .collect();
        let expected: BTreeSet<_> = missing
            .iter()
            .map(|name| format!("Numeric.Sample.{name}"))
            .collect();
        assert_eq!(actual, expected, "各slot identity: {id}");
    }
    audit(&result, &checked);
    let ns = nodes(&result);
    let q_answer = answer(&result, "q");
    let q_root = target(
        &ns,
        f(f(q_answer, "outputs"), "evaluation"),
        &Json::str("Evaluation"),
    );
    assert_eq!(
        f(q_root, "id"),
        f(original_evaluation(&ns, q_root), "id"),
        "Qの定数化を有限個の補完例へ置換しない"
    );
    let q_parts = arr(f(val(q_root), "parts"));
    assert_eq!(q_parts.len(), 1);
    let q_children = arr(f(&q_parts[0], "children"));
    assert_eq!(q_children.len(), 2);
    let missing_q = target(&ns, &q_children[0], &Json::str("Evaluation"));
    assert!(!obj(val(missing_q)).contains_key("value"));
    assert!(arr(f(missing_q, "reasons")).iter().any(|reason| {
        f(reason, "code") == &Json::str("missing_observation")
            && arr(f(reason, "missing")).iter().any(|fact| {
                f(fact, "field") == &Json::str("Numeric.Sample.q")
                    && !obj(fact).contains_key("atom")
            })
    }));
    let q_zero = target(&ns, f(f(q_answer, "outputs"), "value"), &Json::str("Q"));
    assert_eq!(
        f(q_zero, "arguments"),
        &Json::Arr(
            std::iter::once(f(val(q_root), "expression").clone())
                .chain(q_children.iter().cloned())
                .collect()
        ),
        "定数Q零を元Expressionと両子Evaluationから導出する"
    );
    assert_eq!(f(q_zero, "scope"), f(q_root, "scope"));
    assert_eq!(f(q_zero, "support"), f(q_root, "support"));
    let a = answer(&result, "f");
    let root = target(
        &ns,
        f(f(a, "outputs"), "evaluation"),
        &Json::str("Evaluation"),
    );
    let original = original_evaluation(&ns, root);
    assert_ne!(f(root, "id"), f(original, "id"));
    assert!(
        !obj(val(original)).contains_key("value"),
        "元観測評価へ補完値を貼らない"
    );
    let original_parts = arr(f(val(original), "parts"));
    assert_eq!(original_parts.len(), 1);
    assert_eq!(arr(f(&original_parts[0], "children")).len(), 2);
    for child in arr(f(&original_parts[0], "children")) {
        let evaluation = target(&ns, child, &Json::str("Evaluation"));
        assert!(!obj(val(evaluation)).contains_key("value"));
        assert!(
            arr(f(evaluation, "reasons"))
                .iter()
                .any(|reason| f(reason, "code") == &Json::str("missing_observation"))
        );
    }
    let domain = target(&ns, &arr(f(root, "arguments"))[1], &Json::str("Domain"));
    assert_eq!(f(val(domain), "kind"), &Json::str("finite"));
    assert_eq!(f(val(domain), "type"), &fp("5"));
    let members = arr(f(val(domain), "elements"));
    assert_eq!(members.len(), 5);
    let expected = (0..5)
        .map(|value| Json::str(value.to_string()).canonical())
        .collect::<BTreeSet<_>>();
    assert_eq!(
        members
            .iter()
            .map(|r| val(target(&ns, r, &fp("5"))).canonical())
            .collect::<BTreeSet<_>>(),
        expected
    );
    let parts = arr(f(val(root), "parts"));
    assert_eq!(parts.len(), 1);
    let cases = arr(f(&parts[0], "children"));
    assert_eq!(cases.len(), 5);
    let mut assignments = BTreeSet::new();
    for reference in cases {
        let case = target(&ns, reference, &Json::str("Evaluation"));
        let source = target(&ns, f(val(case), "expression"), &Json::str("Expression"));
        let assigned = arr(f(source, "arguments"))
            .iter()
            .filter(|r| members.contains(r))
            .collect::<Vec<_>>();
        assert_eq!(assigned.len(), 1);
        let assigned = val(target(&ns, assigned[0], &fp("5")));
        assert!(assignments.insert(assigned.canonical()));
        assert_eq!(
            val(target(&ns, f(val(case), "value"), &fp("5"))),
            &Json::str("0")
        );
        let parts = arr(f(val(case), "parts"));
        assert_eq!(parts.len(), 1);
        let operands = arr(f(&parts[0], "children"));
        assert_eq!(operands.len(), 2);
        for operand in operands {
            let evaluation = target(&ns, operand, &Json::str("Evaluation"));
            assert_eq!(
                val(target(&ns, f(val(evaluation), "value"), &fp("5"))),
                assigned,
                "同じslotの左右は同じ補完値"
            );
        }
    }
    assert_eq!(assignments, expected);
    let coverage = arr(f(a, "evidence"))
        .iter()
        .map(|r| target(&ns, r, &Json::str("Evidence")))
        .filter(|e| f(val(e), "kind") == &Json::str("finite_exhaustion"))
        .collect::<Vec<_>>();
    assert_eq!(coverage.len(), 1);
    let proof = f(val(coverage[0]), "data");
    assert_eq!(f(proof, "checked"), &Json::Nat(5));
    assert_eq!(
        target(&ns, f(proof, "domain"), &Json::str("Domain")),
        domain
    );
    assert_eq!(f(proof, "instances"), &Json::Arr(cases.to_vec()));
}

#[test]
fn injected_stop_inside_numeric_operation_keeps_prior_values_reason_and_unstarted_requests() {
    let body = r#"
 view seed(s: Sample): Q = s.q + rat(5,6);
 view unknown(s: Sample): Fp(5) = s.f;
 view current(s: Sample): Q = s.q + s.q;
 view later(s: Sample): Fp(7) = s.g;
"#;
    let seed = "seed=evaluate(Calc.seed,s=@v/sample)";
    let unknown = "unknown=evaluate(Calc.unknown,s=@v/sample)";
    let count = Rc::new(Cell::new(0));
    let seen = count.clone();
    let mut baseline = Control::new(Limits::default(), move |point| {
        if point == Checkpoint::Expression {
            seen.set(seen.get() + 1);
        }
        Usage::default()
    });
    let prior = evaluate_observed_bytes(fixture(&["f"], body), &[seed, unknown], &mut baseline)
        .unwrap()
        .wire();
    // Stop after the next expression has entered its first operand.
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
        fixture(&["f"], body),
        &[
            seed,
            unknown,
            "current=evaluate(Calc.current,s=@v/sample)",
            "later=evaluate(Calc.later,s=@v/sample)",
        ],
        &mut c,
    )
    .unwrap()
    .wire();
    assert_eq!(f(&result, "status"), &Json::str("interrupted"));
    assert_output(&result, "seed", &Json::str("Q"), q("1", "6"));
    assert_eq!(
        f(answer(&result, "unknown"), "status"),
        &Json::str("undetermined")
    );
    assert_eq!(
        f(answer(&result, "unknown"), "reasons"),
        f(answer(&prior, "unknown"), "reasons"),
        "先行欠測の元理由を中断理由へ置き換えない"
    );
    assert_eq!(
        f(answer(&result, "unknown"), "scope"),
        f(answer(&prior, "unknown"), "scope")
    );
    assert!(!obj(f(answer(&result, "unknown"), "outputs")).contains_key("value"));
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
    assert_eq!(
        probes.get(),
        before,
        "停止後は同Controlのprobeを再実行しない"
    );
}
