//! AC4のlet/if段階: 三入力byteから値、lexicalな出現、欠測と中断を確認する。
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
fn reached(ns: &BTreeMap<&str, &Json>, roots: &[&Json]) -> BTreeSet<String> {
    let mut todo = vec![];
    for r in roots {
        links(r, &mut todo);
    }
    let mut seen = BTreeSet::new();
    while let Some(id) = todo.pop() {
        if seen.insert(id.clone()) {
            links(ns[id.as_str()], &mut todo);
        }
    }
    seen
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
      "vocabularies":[{"semantics":"archsig/0.6.0","namespace":"Branch","version":"1","dependencies":[],
      "declarations":[{"kind":"entity","name":"Branch.Sample","meaning":"小さい束縛と分岐の対象。","parameters":[],
      "fields":[{"name":"z","type":"Z","meaning":"整数。"},
      {"name":"q","type":"Q","meaning":"有理数。"},
      {"name":"f","type":["Fp","5"],"meaning":"五元体。"},
      {"name":"t","type":["Tuple","Z","Q",["Fp","5"]],"meaning":"数値Tuple。"},
      {"name":"p","type":"Bool","meaning":"条件。"}],"alignments":[]}]}]}"#;
    let definitions_checked =
        check_definitions(&[("definition0", definitions.as_bytes())]).unwrap();
    let digest = &definitions_checked.vocabularies["Branch"].digest;
    let law = format!(
        r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Calc {{
 use vocabulary Branch version "1" digest "{digest}";
 {body}
}}
"#
    );
    let atoms = [("z", r#""3""#), ("q", r#"["-2","3"]"#), ("f", r#""4""#),
        ("t", r#"["3",["-2","3"],"4"]"#), ("p", "false")]
        .into_iter().filter(|(name, _)| !omitted.contains(name)).map(|(name,value)| {
            format!(r#"{{"id":"{name}","subject":"sample","field":"Branch.Sample.{name}","value":{value},"origin":"values"}}"#)
        }).collect::<Vec<_>>().join(",");
    let map = format!(
        r#"{{"format":"archsig.archmap/2","semantics":"archsig/0.6.0",
      "vocabularies":[{{"namespace":"Branch","version":"1","digest":"{digest}"}}],
      "sources":[{{"id":"scan","uri":"urn:fixture:let-if","revision":"r1","digest":"sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"}}],
      "origins":[{{"id":"base","mode":"observed","method":"対象を観測する。","locations":[{{"source":"scan","path":"state.model","span":[0,1]}}]}},
      {{"id":"values","mode":"observed","method":"値を観測する。","locations":[{{"source":"scan","path":"values.model","span":[2,5]}}]}}],
      "snapshots":[{{"id":"v","origin":"base","subjects":[{{"id":"sample","type":"Branch.Sample","origin":"base"}},{{"id":"other","type":"Branch.Sample","origin":"base"}}],"atoms":[{atoms}]}}]}}"#
    );
    InputSources::from_bytes(
        vec![definitions.as_bytes().to_vec()],
        law.into_bytes(),
        map.into_bytes(),
    )
}
fn run(inputs: InputSources, asks: &[&str]) -> (Json, CheckedInputs) {
    let checked = check_inputs(inputs.clone(), &mut control())
        .unwrap_or_else(|failure| panic!("入力検査: {:?}", failure.issues()));
    let result = evaluate_observed_bytes(inputs, asks, &mut control())
        .unwrap_or_else(|failure| {
            if let Some(wire) = failure.wire() {
                panic!("観測評価: {:?}", f(&wire, "issues"));
            }
            panic!("観測評価が失敗した（公開wireなし）");
        })
        .wire();
    (result, checked)
}
fn fp() -> Json {
    Json::Arr(vec![Json::str("Fp"), Json::str("5")])
}
fn q(n: &str, d: &str) -> Json {
    Json::Arr(vec![Json::str(n), Json::str(d)])
}
fn tuple_type() -> Json {
    Json::Arr(vec![
        Json::str("Tuple"),
        Json::str("Z"),
        Json::str("Q"),
        fp(),
    ])
}
fn reference_type() -> Json {
    Json::Arr(vec![Json::str("Ref"), Json::str("Branch.Sample")])
}
fn output<'a>(result: &'a Json, id: &str, ty: &Json) -> Option<&'a Json> {
    let ns = nodes(result);
    obj(f(answer(result, id), "outputs"))
        .get("value")
        .map(|r| val(target(&ns, r, ty)))
}
fn assert_output(result: &Json, id: &str, ty: &Json, expected: Json) {
    let a = answer(result, id);
    assert_eq!(f(a, "status"), &Json::str("established"), "{id}");
    assert!(
        !obj(a).contains_key("claim"),
        "viewのfalseも値として確定する"
    );
    assert_eq!(output(result, id, ty), Some(&expected), "{id}");
}
fn missing(result: &Json, id: &str, fields: &[&str]) {
    let a = answer(result, id);
    assert_eq!(f(f(a, "scope"), "domain"), &Json::str("all_completions"));
    let actual: BTreeSet<_> = arr(f(a, "reasons"))
        .iter()
        .filter(|r| f(r, "code") == &Json::str("missing_observation"))
        .flat_map(|r| arr(f(r, "missing")))
        .map(|m| {
            assert_eq!(f(m, "snapshot"), &Json::str("v"));
            assert_eq!(f(m, "subject"), &Json::str("sample"));
            assert!(!obj(m).contains_key("atom"));
            txt(f(m, "field")).to_owned()
        })
        .collect();
    assert_eq!(
        actual,
        fields
            .iter()
            .map(|name| format!("Branch.Sample.{name}"))
            .collect::<BTreeSet<_>>()
    );
}
fn evaluation_at<'a>(
    ns: &BTreeMap<&str, &'a Json>,
    reach: &BTreeSet<String>,
    at: (usize, usize),
) -> &'a Json {
    reach
        .iter()
        .map(|id| ns[id.as_str()])
        .find(|n| {
            if f(n, "type") != &Json::str("Evaluation") {
                return false;
            }
            let expression = val(target(
                ns,
                f(val(n), "expression"),
                &Json::str("Expression"),
            ));
            f(expression, "kind") == &Json::str("source") && span(f(expression, "location")) == at
        })
        .expect("各typed AST出現に実Evaluationがある")
}
fn part_at(evaluation: &Json, at: (usize, usize)) -> &Json {
    arr(f(val(evaluation), "parts"))
        .iter()
        .find(|part| span(f(part, "location")) == at)
        .unwrap()
}
fn audit(result: &Json, checked: &CheckedInputs) {
    audit_selected(result, checked, None, false)
}
fn audit_selected(
    result: &Json,
    checked: &CheckedInputs,
    originals: Option<&BTreeMap<&str, &Json>>,
    completion_case: bool,
) {
    let ns = nodes(result);
    let mut earlier = BTreeSet::new();
    for n in arr(f(result, "nodes")) {
        let mut refs = vec![];
        links(n, &mut refs);
        for r in refs {
            assert!(
                earlier.contains(r.as_str()),
                "payloadも全Refは既出だけを指す"
            );
        }
        assert!(earlier.insert(txt(f(n, "id"))));
        if f(n, "type") != &Json::str("Proposition") {
            assert!(!obj(n).contains_key("judgment"));
        }
        if let Some(value) = obj(n).get("value") {
            let mut refs = vec![];
            links(value, &mut refs);
            for r in refs {
                assert_ne!(f(ns[r.as_str()], "state"), &Json::str("blocked"));
                assert_ne!(f(ns[r.as_str()], "state"), &Json::str("partial"));
            }
        }
        for fact in arr(f(n, "support")) {
            assert_eq!(f(fact, "snapshot"), &Json::str("v"));
            let subject = checked.archmap().snapshots[0]
                .subjects
                .iter()
                .find(|s| s.id == txt(f(fact, "subject")))
                .unwrap();
            let origin_id = if let Some(field) = obj(fact).get("field") {
                let slot = &subject
                    .fields
                    .iter()
                    .find(|s| s.name == txt(field))
                    .unwrap()
                    .slot;
                let archsig::archmap::Slot::Known { atom, origin, .. } = slot else {
                    panic!("欠測を支持Atomにしない")
                };
                assert_eq!(atom, txt(f(fact, "atom")));
                origin
            } else {
                assert!(!obj(fact).contains_key("atom"));
                &subject.origin
            };
            let origin = checked
                .archmap()
                .origins
                .iter()
                .find(|o| &o.id == origin_id)
                .unwrap();
            assert_eq!(origin.mode, archsig::archmap::Mode::Observed);
            let location = &origin.locations[0];
            let source = checked
                .archmap()
                .sources
                .iter()
                .find(|s| s.id == location.source)
                .unwrap();
            assert_eq!(source.uri, "urn:fixture:let-if");
            assert_eq!(
                location.path,
                if obj(fact).contains_key("field") {
                    "values.model"
                } else {
                    "state.model"
                }
            );
            assert_eq!(
                location.span,
                Some(if obj(fact).contains_key("field") {
                    (2, 5)
                } else {
                    (0, 1)
                })
            );
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
        let decl = &checked.law().declarations[txt(f(f(request, "head"), "name"))];
        let reach = if let Some(originals) = originals {
            let selected = originals[txt(f(a, "id"))];
            if completion_case {
                let mut seen = BTreeSet::new();
                let mut todo = vec![selected];
                while let Some(evaluation) = todo.pop() {
                    if seen.insert(txt(f(evaluation, "id")).to_owned()) {
                        for part in arr(f(val(evaluation), "parts")) {
                            for child in arr(f(part, "children")) {
                                todo.push(target(&ns, child, &Json::str("Evaluation")));
                            }
                        }
                    }
                }
                seen
            } else {
                let mut reach = reached(&ns, &[selected]);
                reach.insert(txt(f(selected, "id")).to_owned());
                reach
            }
        } else {
            reached(&ns, &[f(a, "outputs"), f(a, "evidence")])
        };
        let mut source_ids = BTreeSet::new();
        for (id, expr) in checked
            .law()
            .exprs
            .iter()
            .enumerate()
            .filter(|(_, e)| decl.span.0 <= e.span.0 && e.span.1 <= decl.span.1)
        {
            let Some(ty) = checked.law().expr_type(id) else {
                continue;
            };
            let evaluation = evaluation_at(&ns, &reach, expr.span);
            if completion_case {
                assert_eq!(
                    reach
                        .iter()
                        .map(|id| ns[id.as_str()])
                        .filter(|n| {
                            let source =
                                target(&ns, f(val(n), "expression"), &Json::str("Expression"));
                            f(val(source), "kind") == &Json::str("source")
                                && span(f(val(source), "location")) == expr.span
                        })
                        .count(),
                    1,
                    "完成case内の各元AST出現を一意に選ぶ"
                );
            }
            let ex = target(
                &ns,
                f(val(evaluation), "expression"),
                &Json::str("Expression"),
            );
            assert!(
                source_ids.insert(txt(f(ex, "id"))),
                "別出現のSourceを値共有で統合しない"
            );
            assert!(
                arr(f(val(ex), "parameters")).is_empty(),
                "欠測let名は新しい全称parameterではない"
            );
            assert_eq!(f(val(ex), "bindings"), f(val(evaluation), "bindings"));
            let bindings = arr(f(val(evaluation), "bindings"));
            assert_eq!(
                bindings.len(),
                if completion_case { 2 } else { 1 },
                "宣言の明示parameterだけを通常Bindingに置く"
            );
            assert_eq!(f(&bindings[0], "name"), &Json::str("s"));
            if completion_case {
                assert_eq!(f(&bindings[1], "name"), &Json::str("t"));
                assert_eq!(
                    val(target(&ns, f(&bindings[0], "value"), &reference_type())),
                    &Json::Arr(vec![Json::str("v"), Json::str("sample")])
                );
                assert_eq!(
                    val(target(&ns, f(&bindings[1], "value"), &reference_type())),
                    &Json::Arr(vec![Json::str("v"), Json::str("other")])
                );
            }
            assert_eq!(
                f(ns[txt(f(f(&bindings[0], "value"), "node"))], "type"),
                &reference_type()
            );
            let part = part_at(evaluation, expr.span);
            if let Some(value) = obj(part).get("value") {
                assert_eq!(f(ns[txt(f(value, "node"))], "type"), &ty.wire());
            }
            assert!(
                !obj(part).contains_key("residual"),
                "これらの一般Bool/let/ifは数値残差を持たない"
            );
            let expected = match &expr.kind {
                ExprKind::Let { value, body, .. } => vec![*value, *body],
                ExprKind::If {
                    cond,
                    then_branch,
                    else_branch,
                } => vec![*cond, *then_branch, *else_branch],
                ExprKind::Binary { lhs, rhs, .. } => vec![*lhs, *rhs],
                ExprKind::Group(x)
                | ExprKind::Unary { operand: x, .. }
                | ExprKind::Field { base: x, .. }
                | ExprKind::Index { base: x, .. } => vec![*x],
                ExprKind::Tuple(items) | ExprKind::Call { args: items, .. } => items.clone(),
                ExprKind::Dotted(names) if names.len() == 1 => checked
                    .law()
                    .exprs
                    .iter()
                    .filter_map(|ancestor| {
                        let ExprKind::Let { name, value, body } = &ancestor.kind else {
                            return None;
                        };
                        let scope = checked.law().exprs[*body].span;
                        (name.name == names[0].name
                            && scope.0 <= expr.span.0
                            && expr.span.1 <= scope.1)
                            .then_some(*value)
                    })
                    .collect(),
                _ => vec![],
            };
            if let ExprKind::Dotted(names) = &expr.kind {
                if names.len() == 2 && names[0].name == "s" {
                    let field_name = format!("Branch.Sample.{}", names[1].name);
                    let binding = ns[txt(f(f(&bindings[0], "value"), "node"))];
                    let subject_id = txt(&arr(val(binding))[1]);
                    let subject = checked.archmap().snapshots[0]
                        .subjects
                        .iter()
                        .find(|subject| subject.id == subject_id)
                        .unwrap();
                    let slot = &subject
                        .fields
                        .iter()
                        .find(|field| field.name == field_name)
                        .unwrap()
                        .slot;
                    match slot {
                        archsig::archmap::Slot::Known { atom, .. } => {
                            assert!(
                                arr(f(evaluation, "support"))
                                    .iter()
                                    .any(|fact| obj(fact).get("field")
                                        == Some(&Json::str(&field_name))
                                        && obj(fact).get("atom") == Some(&Json::str(atom))),
                                "原始fieldのEvaluationは元の支持Atomを保持する"
                            );
                        }
                        archsig::archmap::Slot::Missing => {
                            if let Some(value) = obj(part).get("value") {
                                assert!(completion_case, "元観測の欠測fieldは未決のまま");
                                assert_eq!(ty.wire(), Json::str("Bool"));
                                assert_eq!(field_name, "Branch.Sample.p");
                                let scalar = target(&ns, value, &Json::str("Bool"));
                                assert_eq!(f(f(scalar, "rule"), "kind"), &Json::str("law"));
                                assert_eq!(span(f(f(scalar, "rule"), "location")), expr.span);
                                assert!(arr(f(scalar, "support")).is_empty());
                                let args = arr(f(scalar, "arguments"));
                                assert_eq!(args.len(), 3);
                                assert_eq!(&args[0], f(val(evaluation), "expression"));
                                assert_eq!(&args[1], f(&bindings[0], "value"));
                                let projection = target(&ns, &args[2], &Json::str("Bool"));
                                assert_eq!(val(projection), val(scalar));
                                assert_eq!(
                                    f(f(projection, "rule"), "kind"),
                                    &Json::str("construction")
                                );
                                let inputs = arr(f(projection, "arguments"));
                                assert_eq!(inputs.len(), 4);
                                let aggregate = target(
                                    &ns,
                                    f(f(a, "outputs"), "evaluation"),
                                    &Json::str("Evaluation"),
                                );
                                assert_eq!(&inputs[0], f(val(aggregate), "expression"));
                                assert_eq!(&inputs[1], &arr(f(aggregate, "arguments"))[1]);
                                let domain = target(&ns, &inputs[1], &Json::str("Domain"));
                                assert!(arr(f(val(domain), "elements")).contains(&inputs[2]));
                                let selected = originals.expect("case root")[txt(f(a, "id"))];
                                let selected_source = target(
                                    &ns,
                                    f(val(selected), "expression"),
                                    &Json::str("Expression"),
                                );
                                for edge in &inputs[..3] {
                                    assert!(arr(f(ex, "arguments")).contains(edge));
                                    assert!(arr(f(selected_source, "arguments")).contains(edge));
                                }
                                assert!(arr(f(ex, "arguments")).contains(&args[2]));
                                let original_source =
                                    target(&ns, &inputs[3], &Json::str("Expression"));
                                let seed = target(&ns, &inputs[0], &Json::str("Expression"));
                                assert!(arr(f(seed, "arguments")).contains(&inputs[3]));
                                assert_eq!(span(f(val(original_source), "location")), expr.span);
                                assert_eq!(
                                    val(target(&ns, &inputs[2], &Json::str("Bool"))),
                                    val(scalar)
                                );
                            } else {
                                assert!(!obj(part).contains_key("value"));
                            }
                            assert_eq!(
                                f(f(evaluation, "scope"), "domain"),
                                &Json::str("all_completions")
                            );
                        }
                    }
                }
            }
            let children = arr(f(part, "children"));
            for child in children {
                let child_node = target(&ns, child, &Json::str("Evaluation"));
                for fact in arr(f(child_node, "support")) {
                    assert!(
                        arr(f(evaluation, "support")).contains(fact),
                        "let右辺・名前の実束縛・ifの非選択枝の支持を親にも保持する"
                    );
                }
                if f(f(child_node, "scope"), "domain") == &Json::str("all_completions") {
                    assert_eq!(
                        f(f(evaluation, "scope"), "domain"),
                        &Json::str("all_completions")
                    );
                }
            }
            let actual: Vec<_> = children
                .iter()
                .map(|r| {
                    let ev = val(target(&ns, r, &Json::str("Evaluation")));
                    span(f(
                        val(target(&ns, f(ev, "expression"), &Json::str("Expression"))),
                        "location",
                    ))
                })
                .collect();
            let expected_spans = match &expr.kind {
                // Dottedのfield射影は直前のprefixを子に持つ。先頭のparameter tokenは
                // 独立したarena ExprIdを持つとは限らないので元tokenのspanで照合する。
                ExprKind::Dotted(names) if names.len() > 1 => {
                    vec![(names[0].span.0, names[names.len() - 2].span.1)]
                }
                _ => expected
                    .iter()
                    .map(|id| checked.law().exprs[*id].span)
                    .collect(),
            };
            assert_eq!(
                actual, expected_spans,
                "元AST順の子評価とlexical名→実RHSを保つ: {:?} at {:?}",
                expr.kind, expr.span,
            );
            if matches!(&expr.kind,ExprKind::Dotted(names) if names.len()==1)
                && !expected.is_empty()
            {
                let rhs = part_at(
                    target(&ns, &children[0], &Json::str("Evaluation")),
                    checked.law().exprs[expected[0]].span,
                );
                match (obj(rhs).get("value"), obj(part).get("value")) {
                    (Some(rhs), Some(value)) => {
                        assert_eq!(val(ns[txt(f(rhs, "node"))]), val(ns[txt(f(value, "node"))]))
                    }
                    (None, None) => {}
                    _ => panic!("名前使用は実RHSと同じ既知/欠測状態を保つ"),
                }
            }
        }
    }
}

#[test]
fn let_values_preserve_nested_repeated_names_and_all_current_scalar_types() {
    let (result, checked) = run(
        fixture(
            &[],
            r#"
 view integer(s: Sample): Z = let x=s.z+1 in let y=x*2 in x+y+x;
 view rational(s: Sample): Q = let x=s.q in x+1;
 view field(s: Sample): Fp(5) = let x=s.f in x+x;
 view tuple(s: Sample): (Z,Q,Fp(5)) = let x=s.t in x+x;
 view flag(s: Sample): Bool = let x=s.p in x;
 view reference(s: Sample): Sample = let x=s in x;
"#,
        ),
        &[
            "z=evaluate(Calc.integer,s=@v/sample)",
            "q=evaluate(Calc.rational,s=@v/sample)",
            "f=evaluate(Calc.field,s=@v/sample)",
            "t=evaluate(Calc.tuple,s=@v/sample)",
            "b=evaluate(Calc.flag,s=@v/sample)",
            "r=evaluate(Calc.reference,s=@v/sample)",
            "r_other=evaluate(Calc.reference,s=@v/other)",
        ],
    );
    assert_eq!(f(&result, "status"), &Json::str("complete"));
    for (id, ty, value) in [
        ("z", Json::str("Z"), Json::str("16")),
        ("q", Json::str("Q"), q("1", "3")),
        ("f", fp(), Json::str("3")),
        (
            "t",
            tuple_type(),
            Json::Arr(vec![Json::str("6"), q("-4", "3"), Json::str("3")]),
        ),
        ("b", Json::str("Bool"), Json::Bool(false)),
        (
            "r",
            reference_type(),
            Json::Arr(vec![Json::str("v"), Json::str("sample")]),
        ),
        (
            "r_other",
            reference_type(),
            Json::Arr(vec![Json::str("v"), Json::str("other")]),
        ),
    ] {
        assert_output(&result, id, &ty, value);
    }
    let ns = nodes(&result);
    for (id, subject) in [("r", "sample"), ("r_other", "other")] {
        let reach = reached(&ns, &[f(answer(&result, id), "outputs")]);
        for node in reach
            .iter()
            .map(|id| ns[id.as_str()])
            .filter(|n| f(n, "type") == &Json::str("Expression"))
        {
            for binding in arr(f(val(node), "bindings")) {
                assert_eq!(
                    val(ns[txt(f(f(binding, "value"), "node"))]),
                    &Json::Arr(vec![Json::str("v"), Json::str(subject)]),
                    "同じASTへの別Requestの束縛を混ぜない"
                );
            }
        }
    }
    audit(&result, &checked);
}

#[test]
fn known_if_conditions_choose_typed_values_and_keep_both_branch_occurrences() {
    let (result, checked) = run(
        fixture(
            &[],
            r#"
 view integer(s: Sample): Z = if s.p then s.z else 9;
 view rational(s: Sample): Q = if true then s.q else s.q+1;
 view field(s: Sample): Fp(5) = if false then 1 else s.f;
 view tuple(s: Sample): (Z,Q,Fp(5)) = if true then s.t else (0,rat(1,2),1);
 view flag(s: Sample): Bool = if false then true else s.p;
 view reference(s: Sample): Sample = if true then s else s;
"#,
        ),
        &[
            "z=evaluate(Calc.integer,s=@v/sample)",
            "q=evaluate(Calc.rational,s=@v/sample)",
            "f=evaluate(Calc.field,s=@v/sample)",
            "t=evaluate(Calc.tuple,s=@v/sample)",
            "b=evaluate(Calc.flag,s=@v/sample)",
            "r=evaluate(Calc.reference,s=@v/sample)",
        ],
    );
    assert_eq!(f(&result, "status"), &Json::str("complete"));
    for (id, ty, value) in [
        ("z", Json::str("Z"), Json::str("9")),
        ("q", Json::str("Q"), q("-2", "3")),
        ("f", fp(), Json::str("4")),
        (
            "t",
            tuple_type(),
            Json::Arr(vec![Json::str("3"), q("-2", "3"), Json::str("4")]),
        ),
        ("b", Json::str("Bool"), Json::Bool(false)),
        (
            "r",
            reference_type(),
            Json::Arr(vec![Json::str("v"), Json::str("sample")]),
        ),
    ] {
        assert_output(&result, id, &ty, value);
    }
    audit(&result, &checked);
}

#[test]
fn unknown_if_retains_condition_missing_and_both_branches_without_choosing_one() {
    let (result, checked) = run(
        fixture(
            &["p"],
            r#"
 view same_z(s: Sample): Z = if s.p then s.z else 3;
 view same_q(s: Sample): Q = if s.p then s.q+rat(2,3) else rat(0,1);
 view same_f(s: Sample): Fp(5) = if s.p then s.f else 4;
 view same_t(s: Sample): (Z,Q,Fp(5)) = if s.p then s.t else (3,-rat(2,3),4);
 view same_b(s: Sample): Bool = if s.p then false else false;
 view same_r(s: Sample): Sample = if s.p then s else s;
 view different(s: Sample): Q = if s.p then s.q else rat(1,3);
"#,
        ),
        &[
            "z=evaluate(Calc.same_z,s=@v/sample)",
            "q=evaluate(Calc.same_q,s=@v/sample)",
            "f=evaluate(Calc.same_f,s=@v/sample)",
            "t=evaluate(Calc.same_t,s=@v/sample)",
            "b=evaluate(Calc.same_b,s=@v/sample)",
            "r=evaluate(Calc.same_r,s=@v/sample)",
            "different=evaluate(Calc.different,s=@v/sample)",
        ],
    );
    assert_eq!(f(&result, "status"), &Json::str("partial"));
    let expected_outputs = [
        ("z", Json::str("Z"), Json::str("3")),
        ("q", Json::str("Q"), q("0", "1")),
        ("f", fp(), Json::str("4")),
        (
            "t",
            tuple_type(),
            Json::Arr(vec![Json::str("3"), q("-2", "3"), Json::str("4")]),
        ),
        ("b", Json::str("Bool"), Json::Bool(false)),
        (
            "r",
            reference_type(),
            Json::Arr(vec![Json::str("v"), Json::str("sample")]),
        ),
    ];
    for (id, ty, value) in &expected_outputs {
        assert_output(&result, id, ty, value.clone());
        missing(&result, id, &["p"]);
    }
    let different = answer(&result, "different");
    assert_eq!(f(different, "status"), &Json::str("undetermined"));
    assert!(!obj(f(different, "outputs")).contains_key("value"));
    missing(&result, "different", &["p"]);
    let ns = nodes(&result);
    let mut originals = BTreeMap::new();
    for request in arr(f(&result, "requests")) {
        let id = txt(f(request, "id"));
        let aggregate = target(
            &ns,
            f(f(answer(&result, id), "outputs"), "evaluation"),
            &Json::str("Evaluation"),
        );
        let seed = target(
            &ns,
            f(val(aggregate), "expression"),
            &Json::str("Expression"),
        );
        assert_eq!(
            arr(f(aggregate, "arguments")).first(),
            Some(f(val(aggregate), "expression"))
        );
        let decl = &checked.law().declarations[txt(f(f(request, "head"), "name"))];
        let archsig::law::model::Signature::View { body, .. } = &decl.signature else {
            panic!("view")
        };
        let at = checked.law().exprs[*body].span;
        let candidates = arr(f(seed, "arguments"))
            .iter()
            .map(|r| ns[txt(f(r, "node"))])
            .filter(|n| {
                if f(n, "type") != &Json::str("Evaluation") {
                    return false;
                }
                let source = target(&ns, f(val(n), "expression"), &Json::str("Expression"));
                f(val(source), "kind") == &Json::str("source")
                    && span(f(val(source), "location")) == at
                    && f(val(source), "bindings") == f(val(seed), "bindings")
                    && f(val(source), "parameters") == f(val(seed), "parameters")
                    && f(val(n), "bindings") == f(val(seed), "bindings")
                    && arr(f(n, "arguments")).first() == Some(f(val(n), "expression"))
            })
            .collect::<Vec<_>>();
        assert_eq!(
            candidates.len(),
            1,
            "元CompletionSeed直接rootsから元AST/明示bindingsの評価を一意選択"
        );
        originals.insert(id, candidates[0]);
    }
    let reach = reached(&ns, &[originals["different"]]);
    let branch_values: BTreeSet<_> = reach
        .iter()
        .map(|id| ns[id.as_str()])
        .filter(|n| f(n, "type") == &Json::str("Q") && obj(n).contains_key("value"))
        .map(|n| format!("{:?}", val(n)))
        .collect();
    assert!(branch_values.contains(&format!("{:?}", q("-2", "3"))));
    assert!(branch_values.contains(&format!("{:?}", q("1", "3"))));
    audit_selected(&result, &checked, Some(&originals), false);
    for (id, original) in &originals {
        let aggregate = target(
            &ns,
            f(f(answer(&result, id), "outputs"), "evaluation"),
            &Json::str("Evaluation"),
        );
        let domain_ref = &arr(f(aggregate, "arguments"))[1];
        let domain = target(&ns, domain_ref, &Json::str("Domain"));
        assert_eq!(f(val(domain), "kind"), &Json::str("finite"));
        assert_eq!(f(val(domain), "type"), &Json::str("Bool"));
        let members = arr(f(val(domain), "elements"));
        assert_eq!(members.len(), 2);
        let at = span(f(
            val(target(
                &ns,
                f(val(original), "expression"),
                &Json::str("Expression"),
            )),
            "location",
        ));
        let case_refs = arr(f(part_at(aggregate, at), "children"));
        assert_eq!(case_refs.len(), 2);
        let expected = expected_outputs.iter().find(|(name, _, _)| name == id);
        let result_type = expected
            .map(|(_, t, _)| t.clone())
            .unwrap_or(Json::str("Q"));
        let mut flags = BTreeSet::new();
        for case_ref in case_refs {
            let case = target(&ns, case_ref, &Json::str("Evaluation"));
            let source = target(&ns, f(val(case), "expression"), &Json::str("Expression"));
            assert_eq!(span(f(val(source), "location")), at);
            assert_eq!(f(val(source), "kind"), &Json::str("source"));
            assert_eq!(f(val(source), "bindings"), f(val(case), "bindings"));
            let selected = arr(f(source, "arguments"))
                .iter()
                .filter(|r| members.contains(r))
                .collect::<Vec<_>>();
            assert_eq!(selected.len(), 1);
            let Json::Bool(flag) = val(target(&ns, selected[0], &Json::str("Bool"))) else {
                panic!("Bool")
            };
            assert!(flags.insert(*flag));
            let value = target(&ns, f(val(case), "value"), &result_type);
            let wanted = expected
                .map(|(_, _, v)| v.clone())
                .unwrap_or_else(|| if *flag { q("-2", "3") } else { q("1", "3") });
            assert_eq!(val(value), &wanted);
            let ch = arr(f(part_at(case, at), "children"));
            assert_eq!(ch.len(), 3, "caseも元condition/then/elseを保持");
            let original_ch = arr(f(part_at(original, at), "children"));
            for (child, original_child) in ch.iter().zip(original_ch) {
                let actual = target(&ns, child, &Json::str("Evaluation"));
                let before = target(&ns, original_child, &Json::str("Evaluation"));
                let actual_source =
                    target(&ns, f(val(actual), "expression"), &Json::str("Expression"));
                let before_source =
                    target(&ns, f(val(before), "expression"), &Json::str("Expression"));
                assert_eq!(
                    f(val(actual_source), "location"),
                    f(val(before_source), "location"),
                    "各case子を元condition/then/else出現へ照合"
                );
            }
            let cond = target(&ns, &ch[0], &Json::str("Evaluation"));
            assert_eq!(
                val(target(&ns, f(val(cond), "value"), &Json::str("Bool"))),
                &Json::Bool(*flag)
            );
            for child in ch {
                for fact in arr(f(target(&ns, child, &Json::str("Evaluation")), "support")) {
                    assert!(arr(f(case, "support")).contains(fact));
                }
            }
        }
        assert_eq!(flags, BTreeSet::from([false, true]));
        let proofs = arr(f(aggregate, "evidence"))
            .iter()
            .map(|r| target(&ns, r, &Json::str("Evidence")))
            .collect::<Vec<_>>();
        assert_eq!(proofs.len(), 1);
        let data = f(val(proofs[0]), "data");
        if expected.is_some() {
            assert_eq!(f(val(proofs[0]), "kind"), &Json::str("finite_exhaustion"));
            assert_eq!(f(data, "domain"), domain_ref);
            assert_eq!(f(data, "checked"), &Json::Nat(2));
            assert_eq!(f(data, "instances"), &Json::Arr(case_refs.to_vec()));
        } else {
            assert_eq!(f(val(proofs[0]), "kind"), &Json::str("completion_pair"));
            assert_eq!(
                f(data, "fields"),
                &Json::Arr(vec![Json::obj([
                    ("snapshot", Json::str("v")),
                    ("subject", Json::str("sample")),
                    ("field", Json::str("Branch.Sample.p"))
                ])])
            );
            let mut pair_flags = BTreeSet::new();
            for (binding, result) in [("first", "first_result"), ("second", "second_result")] {
                let assignment = arr(f(data, binding));
                assert_eq!(assignment.len(), 1);
                let Json::Bool(flag) = val(target(&ns, &assignment[0], &Json::str("Bool"))) else {
                    panic!("Bool")
                };
                assert!(pair_flags.insert(*flag));
                assert!(case_refs.contains(f(data, result)));
                let case = target(&ns, f(data, result), &Json::str("Evaluation"));
                let source = target(&ns, f(val(case), "expression"), &Json::str("Expression"));
                assert!(arr(f(source, "arguments")).contains(&assignment[0]));
                assert_eq!(
                    val(target(&ns, f(val(case), "value"), &Json::str("Q"))),
                    &if *flag { q("-2", "3") } else { q("1", "3") }
                );
            }
            assert_eq!(pair_flags, BTreeSet::from([false, true]));
        }
    }
}

#[test]
fn missing_let_rhs_keeps_original_slot_and_constant_body_can_still_be_known() {
    let (result, checked) = run(
        fixture(
            &["q"],
            r#"
 view dependent(s: Sample): Q = let x=s.q in x+1;
 view constant(s: Sample): Q = let x=s.q in 7;
"#,
        ),
        &[
            "dependent=evaluate(Calc.dependent,s=@v/sample)",
            "constant=evaluate(Calc.constant,s=@v/sample)",
        ],
    );
    assert_eq!(f(&result, "status"), &Json::str("partial"));
    let dependent = answer(&result, "dependent");
    assert_eq!(f(dependent, "status"), &Json::str("undetermined"));
    assert!(!obj(f(dependent, "outputs")).contains_key("value"));
    assert_output(&result, "constant", &Json::str("Q"), q("7", "1"));
    for id in ["dependent", "constant"] {
        missing(&result, id, &["q"]);
    }
    let ns = nodes(&result);
    for a in arr(f(&result, "answers")) {
        for reason in arr(f(a, "reasons"))
            .iter()
            .filter(|r| f(r, "code") == &Json::str("missing_observation"))
        {
            for dep in arr(f(reason, "dependencies")) {
                let expression = val(target(&ns, dep, &Json::str("Expression")));
                let (start, end) = span(f(expression, "location"));
                assert_eq!(
                    &checked.sources().law().bytes()[start..end],
                    b"s.q",
                    "欠測理由をlet名の新しい未知へ移さない"
                );
            }
        }
    }
    audit(&result, &checked);
}

#[test]
fn false_if_view_is_established_but_false_if_law_is_refuted_without_numeric_residual() {
    let (result, checked) = run(
        fixture(
            &[],
            r#"
 view flag(s: Sample): Bool = let b=s.p in if b then true else false;
 law required flag_law(s: Sample): let b=s.p in if b then true else false;
"#,
        ),
        &[
            "flag_value=evaluate(Calc.flag,s=@v/sample)",
            "flag_check=check(Calc.flag_law,s=@v/sample)",
        ],
    );
    assert_eq!(f(&result, "status"), &Json::str("complete"));
    assert_output(&result, "flag_value", &Json::str("Bool"), Json::Bool(false));
    let a = answer(&result, "flag_check");
    assert_eq!(f(a, "status"), &Json::str("refuted"));
    let ns = nodes(&result);
    let proposition = target(&ns, f(a, "claim"), &Json::str("Proposition"));
    assert_eq!(
        f(f(proposition, "judgment"), "status"),
        &Json::str("refuted")
    );
    assert_eq!(f(f(a, "outputs"), "proposition"), f(a, "claim"));
    let mut counterexample = false;
    for evidence in arr(f(a, "evidence")) {
        let e = val(target(&ns, evidence, &Json::str("Evidence")));
        let data = f(e, "data");
        assert!(!obj(data).contains_key("residual"));
        let (left, right) = if f(e, "kind") == &Json::str("counterexample") {
            counterexample = true;
            ("left", "right")
        } else {
            ("lhs", "rhs")
        };
        assert_eq!(
            val(target(&ns, f(data, left), &Json::str("Bool"))),
            &Json::Bool(false)
        );
        assert_eq!(
            val(target(&ns, f(data, right), &Json::str("Bool"))),
            &Json::Bool(true)
        );
    }
    assert!(counterexample);
    audit(&result, &checked);
}

#[test]
fn static_checks_reject_self_reference_duplicate_names_and_unselected_ill_typed_branches() {
    for body in [
        "view bad(s: Sample): Z = let x=x in 1;",
        "view bad(s: Sample): Z = let x=1 in let x=2 in x;",
        "view bad(s: Sample): Z = let s=1 in s;",
        "view bad(s: Sample): Q = if true then s.q else s.p;",
        "view bad(s: Sample): Q = if false then s.q+s.p else s.q;",
    ] {
        let failure = check_inputs(fixture(&[], body), &mut control()).unwrap_err();
        let wire = failure.wire();
        assert_eq!(f(&wire, "status"), &Json::str("invalid"), "{body}");
        assert_eq!(arr(f(&wire, "issues")).len(), 1);
        let issue = &arr(f(&wire, "issues"))[0];
        assert_eq!(f(f(issue, "location"), "input"), &Json::str("law"));
        for key in ["requests", "nodes", "answers"] {
            assert!(arr(f(&wire, key)).is_empty());
        }
    }
}

#[test]
fn injected_stop_inside_let_if_keeps_prior_values_missing_reason_and_unstarted_requests() {
    let body = r#"
 view seed(s: Sample): Q = let x=s.q in x+1;
 view unknown(s: Sample): Z = if s.p then 1 else 2;
 view current(s: Sample): Q = let x=s.q in if true then x+1 else x;
 view later(s: Sample): Z = let x=s.z in x+1;
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
    let prior = evaluate_observed_bytes(fixture(&["p"], body), &[seed, unknown], &mut baseline)
        .unwrap()
        .wire();
    let target_count = count.get() + 3;
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
                if seen.get() == target_count {
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
        fixture(&["p"], body),
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
    assert_output(&result, "seed", &Json::str("Q"), q("1", "3"));
    for key in ["status", "reasons", "scope", "outputs"] {
        assert_eq!(
            f(answer(&result, "unknown"), key),
            f(answer(&prior, "unknown"), key),
            "先行欠測と元の理由を保持する"
        );
    }
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
    assert_eq!(expressions.get(), target_count);
    assert_eq!(Some(probes.get()), frozen.get());
    let before = probes.get();
    assert!(c.checkpoint(Checkpoint::Expression).is_err());
    assert_eq!(probes.get(), before, "停止した同Controlはprobeも再開しない");
}

#[test]
fn bool_completions_resolve_lexical_reference_fields_and_keep_other_missing() {
    let body = r#"
 view known_dot(s: Sample,t: Sample): Z = let x=if true then s else t in x.z;
 view known_group(s: Sample,t: Sample): Z = let x=if true then s else t in (x).z;
 view unknown_dot(s: Sample,t: Sample): Z = let x=if s.p then s else t in x.z;
 view unknown_group(s: Sample,t: Sample): Z = let x=if s.p then s else t in (x).z;
"#;
    // other.zは欠測だが、既知条件のlet右辺はsampleへ確定する。
    let (known, _) = run(
        fixture(&["p"], body),
        &[
            "dot=evaluate(Calc.known_dot,s=@v/sample,t=@v/other)",
            "grouped=evaluate(Calc.known_group,s=@v/sample,t=@v/other)",
        ],
    );
    assert_eq!(f(&known, "status"), &Json::str("complete"));
    for id in ["dot", "grouped"] {
        assert_output(&known, id, &Json::str("Z"), Json::str("3"));
    }
    for (name, ask) in [
        (
            "Calc.unknown_dot",
            "dot=evaluate(Calc.unknown_dot,s=@v/sample,t=@v/other)",
        ),
        (
            "Calc.unknown_group",
            "grouped=evaluate(Calc.unknown_group,s=@v/sample,t=@v/other)",
        ),
    ] {
        let inputs = fixture(&["p"], body);
        check_inputs(inputs.clone(), &mut control())
            .unwrap_or_else(|failure| panic!("入力検査: {:?}", failure.issues()));
        let (wire, checked) = run(inputs, &[ask]);
        assert_eq!(f(&wire, "status"), &Json::str("partial"));
        let id = ask.split('=').next().unwrap();
        let a = answer(&wire, id);
        assert_eq!(f(a, "status"), &Json::str("undetermined"));
        assert!(!obj(f(a, "outputs")).contains_key("value"));
        assert!(!obj(a).contains_key("claim"));
        assert_eq!(f(f(a, "scope"), "domain"), &Json::str("all_completions"));
        let absent: BTreeSet<_> = arr(f(a, "reasons"))
            .iter()
            .filter(|r| f(r, "code") == &Json::str("missing_observation"))
            .flat_map(|r| arr(f(r, "missing")))
            .map(|fact| {
                assert_eq!(f(fact, "snapshot"), &Json::str("v"));
                assert!(!obj(fact).contains_key("atom"));
                (
                    txt(f(fact, "subject")).to_owned(),
                    txt(f(fact, "field")).to_owned(),
                )
            })
            .collect();
        assert_eq!(
            absent,
            BTreeSet::from([
                ("sample".to_owned(), "Branch.Sample.p".to_owned()),
                ("other".to_owned(), "Branch.Sample.z".to_owned()),
            ])
        );
        let ns = nodes(&wire);
        let reach = reached(&ns, &[f(a, "outputs"), f(a, "evidence"), f(a, "reasons")]);
        assert!(
            reach.iter().any(|id| {
                let n = ns[id.as_str()];
                f(n, "type") == &Json::str("Z")
                    && obj(n).get("value") == Some(&Json::str("3"))
                    && arr(f(n, "support")).iter().any(|fact| {
                        f(fact, "subject") == &Json::str("sample")
                            && obj(fact).get("field") == Some(&Json::str("Branch.Sample.z"))
                    })
            }),
            "true補完の既知field値も到達可能に保持する"
        );
        let declaration = &checked.law().declarations[name];
        let archsig::law::model::Signature::View { body, .. } = &declaration.signature else {
            panic!("view")
        };
        let at = checked.law().exprs[*body].span;
        assert!(
            reach.iter().any(|id| {
                let n = ns[id.as_str()];
                f(n, "type") == &Json::str("Expression")
                    && obj(n).get("value").is_some_and(|value| {
                        obj(value).get("kind") == Some(&Json::str("source"))
                            && obj(value)
                                .get("location")
                                .is_some_and(|location| span(location) == at)
                    })
            }),
            "両綴りが各自の元body出現へ戻る"
        );
        let aggregate = target(
            &ns,
            f(f(a, "outputs"), "evaluation"),
            &Json::str("Evaluation"),
        );
        let seed = target(
            &ns,
            f(val(aggregate), "expression"),
            &Json::str("Expression"),
        );
        let condition_spans=checked.law().exprs.iter().filter(|e| declaration.span.0<=e.span.0 && e.span.1<=declaration.span.1 && matches!(&e.kind,ExprKind::Dotted(parts) if parts.len()==2 && parts[0].name=="s" && parts[1].name=="p")).map(|e|e.span).collect::<Vec<_>>();
        assert_eq!(condition_spans.len(), 1);
        let partial_sources = arr(f(seed, "arguments"))
            .iter()
            .map(|r| ns[txt(f(r, "node"))])
            .filter(|n| {
                if f(n, "type") != &Json::str("Expression") {
                    return false;
                }
                f(val(n), "kind") == &Json::str("source")
                    && span(f(val(n), "location")) == condition_spans[0]
                    && f(val(n), "bindings") == f(val(seed), "bindings")
                    && f(val(n), "parameters") == f(val(seed), "parameters")
            })
            .map(|n| (txt(f(n, "id")), n))
            .collect::<BTreeMap<_, _>>();
        assert_eq!(
            partial_sources.len(),
            1,
            "prepare_sourceの元seed直接partial rootsからs.p Sourceを一意選択"
        );
        let original_source = *partial_sources.values().next().unwrap();
        assert_eq!(f(f(original_source, "rule"), "kind"), &Json::str("law"));
        assert_eq!(
            span(f(f(original_source, "rule"), "location")),
            condition_spans[0]
        );
        assert!(arr(f(original_source, "support")).is_empty());
        assert!(
            arr(f(seed, "arguments"))
                .iter()
                .all(|r| f(ns[txt(f(r, "node"))], "type") != &Json::str("Evaluation")),
            "元prepare_sourceが未知Ref先fieldで止まるためeval_inner由来の元Evalを捏造しない"
        );
        let original_ref = Json::obj([("node", f(original_source, "id").clone())]);
        let slot = Json::obj([
            ("snapshot", Json::str("v")),
            ("subject", Json::str("sample")),
            ("field", Json::str("Branch.Sample.p")),
        ]);
        let original_missing = arr(f(seed, "reasons"))
            .iter()
            .filter(|r| f(r, "code") == &Json::str("missing_observation"))
            .filter(|reason| arr(f(reason, "dependencies")).contains(&original_ref))
            .collect::<Vec<_>>();
        assert_eq!(original_missing.len(), 1);
        assert_eq!(f(original_missing[0], "request"), &Json::str(id));
        assert_eq!(
            f(original_missing[0], "dependencies"),
            &Json::Arr(vec![original_ref])
        );
        assert_eq!(f(original_missing[0], "missing"), &Json::Arr(vec![slot]));
        assert_eq!(span(f(original_missing[0], "location")), condition_spans[0]);
        assert!(
            arr(f(a, "reasons")).contains(original_missing[0]),
            "元s.pの未観測理由と依存Sourceを最終回答も保持"
        );
        let domain = target(
            &ns,
            &arr(f(aggregate, "arguments"))[1],
            &Json::str("Domain"),
        );
        assert_eq!(f(val(domain), "kind"), &Json::str("finite"));
        assert_eq!(f(val(domain), "type"), &Json::str("Bool"));
        let members = arr(f(val(domain), "elements"));
        assert_eq!(members.len(), 2);
        let cases = arr(f(part_at(aggregate, at), "children"));
        assert_eq!(cases.len(), 2);
        let mut flags = BTreeSet::new();
        for case_ref in cases {
            let case = target(&ns, case_ref, &Json::str("Evaluation"));
            let source = target(&ns, f(val(case), "expression"), &Json::str("Expression"));
            assert_eq!(span(f(val(source), "location")), at);
            let selected = arr(f(source, "arguments"))
                .iter()
                .filter(|r| members.contains(r))
                .collect::<Vec<_>>();
            assert_eq!(selected.len(), 1);
            let Json::Bool(flag) = val(target(&ns, selected[0], &Json::str("Bool"))) else {
                panic!("Bool")
            };
            assert!(flags.insert(*flag));
            if *flag {
                assert_eq!(
                    val(target(&ns, f(val(case), "value"), &Json::str("Z"))),
                    &Json::str("3")
                );
                assert!(
                    arr(f(case, "support"))
                        .iter()
                        .any(|fact| f(fact, "subject") == &Json::str("sample")
                            && obj(fact).get("field") == Some(&Json::str("Branch.Sample.z"))
                            && obj(fact).get("atom") == Some(&Json::str("z")))
                );
            } else {
                assert!(!obj(val(case)).contains_key("value"));
                assert!(
                    arr(f(case, "reasons"))
                        .iter()
                        .filter(|r| f(r, "code") == &Json::str("missing_observation"))
                        .flat_map(|r| arr(f(r, "missing")))
                        .any(|fact| f(fact, "subject") == &Json::str("other")
                            && f(fact, "field") == &Json::str("Branch.Sample.z")
                            && !obj(fact).contains_key("atom"))
                );
            }
            audit_selected(&wire, &checked, Some(&BTreeMap::from([(id, case)])), true);
        }
        assert_eq!(flags, BTreeSet::from([false, true]));
        assert!(
            arr(f(aggregate, "evidence")).is_empty(),
            "未知Z caseを同値全検査や異なる既知値の補完対にしない"
        );
    }
}
