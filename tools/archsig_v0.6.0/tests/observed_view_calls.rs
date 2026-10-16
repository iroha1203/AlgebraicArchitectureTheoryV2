//! AC4の非再帰view呼出し: 三入力byteから実引数、元body、値と停止prefixを確認する。
use archsig::{
    canonical::Json,
    definition::check_definitions_controlled,
    law::{ast::ExprKind, model::Signature},
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
    Json::Arr(vec![Json::str("Ref"), Json::str("Calls.Sample")])
}
fn output(result: &Json, id: &str, ty: &Json, expected: Json) {
    let a = answer(result, id);
    assert_eq!(f(a, "status"), &Json::str("established"), "{id}");
    assert!(
        !obj(a).contains_key("claim"),
        "Bool=falseのviewも確定した値"
    );
    let ns = index(result);
    assert_eq!(
        val(target(&ns, f(f(a, "outputs"), "value"), ty)),
        &expected,
        "{id}"
    );
}

fn fixture(omitted: &[&str], helpers: &str, caller: &str) -> InputSources {
    let definitions = r#"{"format":"archsig.atom-definition/1","semantics":"archsig/0.6.0",
      "vocabularies":[{"semantics":"archsig/0.6.0","namespace":"Calls","version":"1","dependencies":[],
      "declarations":[{"kind":"entity","name":"Calls.Sample","meaning":"呼出しを読む小さい対象。","parameters":[],
      "fields":[{"name":"z","type":"Z","meaning":"整数。"},{"name":"q","type":"Q","meaning":"有理数。"},
      {"name":"f","type":["Fp","5"],"meaning":"五元体。"},
      {"name":"t","type":["Tuple","Z","Q",["Fp","5"]],"meaning":"数値Tuple。"},
      {"name":"p","type":"Bool","meaning":"条件。"}],"alignments":[]}]}]}"#;
    let checked =
        check_definitions_controlled(&[("definition0", definitions.as_bytes())], &mut quiet())
            .unwrap();
    let digest = &checked.vocabularies["Calls"].digest;
    // 実在するreading Hよりも、Calcのuse Helpers as Hを優先して解決する。
    let law = format!(
        r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading H {{ view one(): Z = 99; view rawonly(): Z = 90; }}
reading Helpers {{ use vocabulary Calls version "1" digest "{digest}"; {helpers} }}
reading Calc {{ use vocabulary Calls version "1" digest "{digest}"; use Helpers as H; {caller} }}
"#
    );
    let mut atoms = [("z", r#""3""#), ("q", r#"["-2","3"]"#), ("f", r#""4""#),
        ("t", r#"["3",["-2","3"],"4"]"#), ("p", "false")].into_iter()
        .filter(|(name, _)| !omitted.contains(name)).map(|(name, value)|
        format!(r#"{{"id":"{name}","subject":"sample","field":"Calls.Sample.{name}","value":{value},"origin":"values"}}"#)).collect::<Vec<_>>();
    atoms.push(r#"{"id":"other_z","subject":"other","field":"Calls.Sample.z","value":"11","origin":"values"}"#.into());
    let atoms = atoms.join(",");
    let map = format!(
        r#"{{"format":"archsig.archmap/2","semantics":"archsig/0.6.0",
      "vocabularies":[{{"namespace":"Calls","version":"1","digest":"{digest}"}}],
      "sources":[{{"id":"scan","uri":"urn:fixture:view-calls","revision":"r1","digest":"sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"}}],
      "origins":[{{"id":"base","mode":"specification","method":"対象を提示する。","locations":[{{"source":"scan","path":"subjects.model","span":[0,1]}}]}},
      {{"id":"values","mode":"specification","method":"値を提示する。","locations":[{{"source":"scan","path":"values.model","span":[2,5]}}]}}],
      "snapshots":[{{"id":"v","origin":"base","subjects":[{{"id":"sample","type":"Calls.Sample","origin":"base"}},{{"id":"other","type":"Calls.Sample","origin":"base"}}],"atoms":[{atoms}]}}]}}"#
    );
    InputSources::from_bytes(
        vec![definitions.as_bytes().to_vec()],
        law.into_bytes(),
        map.into_bytes(),
    )
}
fn run(inputs: InputSources, asks: &[&str]) -> (Json, CheckedInputs) {
    let checked = check_inputs(inputs.clone(), &mut quiet())
        .unwrap_or_else(|e| panic!("入力検査: {:?}", e.issues()));
    let result = evaluate_observed_bytes(inputs, asks, &mut quiet())
        .unwrap_or_else(|e| panic!("観測評価: {e:?}"))
        .wire();
    assert_ne!(
        f(&result, "status"),
        &Json::str("error"),
        "{:?}",
        f(&result, "issues")
    );
    (result, checked)
}

fn audit_dag(result: &Json, checked: &CheckedInputs) {
    let ns = index(result);
    let mut earlier = BTreeSet::new();
    for node in arr(f(result, "nodes")) {
        let mut links = vec![];
        refs(node, &mut links);
        for link in links {
            assert!(
                earlier.contains(link.as_str()),
                "全Refは既出nodeだけを指す: {link}"
            );
        }
        assert!(earlier.insert(text(f(node, "id"))));
        if f(node, "type") != &Json::str("Proposition") {
            assert!(!obj(node).contains_key("judgment"));
        }
        if let Some(value) = obj(node).get("value") {
            let mut links = vec![];
            refs(value, &mut links);
            for link in links {
                assert_ne!(f(ns[link.as_str()], "state"), &Json::str("blocked"));
                assert!(!obj(ns[link.as_str()]).contains_key("partial"));
            }
        }
        for fact in arr(f(node, "support")) {
            assert_eq!(f(fact, "snapshot"), &Json::str("v"));
            let subject = checked.archmap().snapshots[0]
                .subjects
                .iter()
                .find(|s| s.id == text(f(fact, "subject")))
                .unwrap();
            let origin_id = if let Some(field) = obj(fact).get("field") {
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
                    panic!("欠測slotは支持Atomではない")
                };
                assert_eq!(f(fact, "atom"), &Json::str(atom));
                assert!(pointer.starts_with("/snapshots/0/atoms/"));
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
            assert_eq!(origin.mode, archsig::archmap::Mode::Specification);
            let location = &origin.locations[0];
            assert_eq!(
                location.path,
                if obj(fact).contains_key("field") {
                    "values.model"
                } else {
                    "subjects.model"
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
            let source = checked
                .archmap()
                .sources
                .iter()
                .find(|s| s.id == location.source)
                .unwrap();
            assert_eq!(source.uri, "urn:fixture:view-calls");
        }
        if f(node, "type") == &Json::str("Expression")
            && f(val(node), "kind") == &Json::str("source")
        {
            assert!(
                arr(f(val(node), "parameters")).is_empty(),
                "欠測実引数を自由な全称parameterにしない"
            );
            let at = span(f(val(node), "location"));
            assert_eq!(span(f(f(node, "rule"), "location")), at);
            assert!(
                checked.law().exprs.iter().any(|e| e.span == at)
                    || checked.sources().law().bytes()[at.0..at.1]
                        .iter()
                        .all(|b| b.is_ascii_alphanumeric()),
                "元ASTまたは元field prefixに戻れる"
            );
        }
        if f(node, "type") == &Json::str("Evaluation") {
            if let Some(instance) = aggregate_instance(&ns, node) {
                let instance_value = val(instance);
                let declaration = &checked.law().declarations[text(f(instance_value, "name"))];
                let Signature::Law {
                    guard: Some(guard),
                    body,
                    ..
                } = &declaration.signature
                else {
                    panic!("LawInstanceに基づく集約は明示guard/bodyの適用を保持する")
                };
                assert_eq!(span(f(instance_value, "occurrence")), declaration.span);
                assert_eq!(f(instance_value, "bindings"), f(val(node), "bindings"));
                let parts = arr(f(val(node), "parts"));
                assert_eq!(parts.len(), 2, "Law適用の元guard/bodyの二つの部品");
                let arguments = arr(f(node, "arguments"));
                assert_eq!(arguments.len(), 3);
                for (i, (name, original, argument_index)) in
                    [("guard", guard, 2), ("body", body, 1)]
                        .into_iter()
                        .enumerate()
                {
                    assert_eq!(
                        span(f(&parts[i], "location")),
                        checked.law().exprs[*original].span
                    );
                    let children = arr(f(&parts[i], "children"));
                    assert_eq!(children, &[arguments[argument_index].clone()]);
                    let child = target(&ns, &children[0], &Json::str("Evaluation"));
                    assert_eq!(f(val(child), "expression"), f(instance_value, name));
                    assert_eq!(
                        evaluation_span(&ns, child),
                        checked.law().exprs[*original].span
                    );
                    assert_eq!(obj(&parts[i]).get("value"), obj(val(child)).get("value"));
                }
            } else {
                let ex = expression(&ns, node);
                if f(val(ex), "kind") == &Json::str("source") {
                    assert_eq!(f(val(ex), "bindings"), f(val(node), "bindings"));
                    assert_eq!(span(f(part(node), "location")), evaluation_span(&ns, node));
                }
            }
            for item in arr(f(val(node), "parts")) {
                for child in arr(f(item, "children")) {
                    let child = target(&ns, child, &Json::str("Evaluation"));
                    for fact in arr(f(child, "support")) {
                        assert!(arr(f(node, "support")).contains(fact));
                    }
                }
            }
        }
    }
    for a in arr(f(result, "answers")) {
        assert!(arr(f(f(a, "scope"), "quantifiers")).is_empty());
        let mut links = vec![];
        refs(a, &mut links);
        for link in links {
            assert!(ns.contains_key(link.as_str()));
        }
    }
}

// 完成したcallのwireだけから元call、宣言順の引数、callee元body、別frameへ辿る。
fn audit_calls(result: &Json, checked: &CheckedInputs) -> usize {
    audit_calls_in(result, checked, None)
}
fn audit_calls_in(
    result: &Json,
    checked: &CheckedInputs,
    selected: Option<&BTreeSet<String>>,
) -> usize {
    audit_dag(result, checked);
    let ns = index(result);
    let law = checked.law();
    let mut bodies = BTreeSet::new();
    let mut calls = 0;
    for evaluation in arr(f(result, "nodes"))
        .iter()
        .filter(|n| f(n, "type") == &Json::str("Evaluation"))
        .filter(|n| selected.is_none_or(|ids| ids.contains(text(f(n, "id")))))
    {
        if aggregate_instance(&ns, evaluation).is_some() {
            continue;
        }
        let source = expression(&ns, evaluation);
        if f(val(source), "kind") != &Json::str("source") {
            continue;
        }
        let at = evaluation_span(&ns, evaluation);
        let Some(expr) = law.exprs.iter().find(|e| e.span == at) else {
            continue;
        };
        let ExprKind::Call { callee, args } = &expr.kind else {
            continue;
        };
        let mut callee = *callee;
        while let ExprKind::Group(inner) = &law.exprs[callee].kind {
            callee = *inner;
        }
        let callee_at = law.exprs[callee].span;
        let Some(name) = law
            .infos
            .iter()
            .flat_map(|d| &d.references)
            .find(|(s, _)| *s == callee_at)
            .map(|(_, n)| n)
        else {
            continue;
        };
        let declaration = &law.declarations[name];
        let Signature::View {
            params,
            body,
            returns,
        } = &declaration.signature
        else {
            panic!("検査済みviewだけを呼ぶ")
        };
        calls += 1;
        let children = arr(f(part(evaluation), "children"));
        assert_eq!(
            children.len(),
            args.len() + 1,
            "引数順の後にcalleeの元bodyを保持: {name}"
        );
        let body_ref = children.last().unwrap();
        assert!(
            bodies.insert(text(f(body_ref, "node")).to_owned()),
            "同じAST/値でもcallごとのbody Evaluationを共有しない"
        );
        let body_eval = target(&ns, body_ref, &Json::str("Evaluation"));
        assert_eq!(evaluation_span(&ns, body_eval), law.exprs[*body].span);
        let body_source = expression(&ns, body_eval);
        assert!(
            arr(f(body_source, "arguments")).contains(f(val(evaluation), "expression")),
            "元call Sourceへ戻る"
        );
        let bindings = arr(f(val(body_eval), "bindings"));
        let mut known = vec![];
        for (i, (arg, parameter)) in args.iter().zip(params).enumerate() {
            let arg_eval = target(&ns, &children[i], &Json::str("Evaluation"));
            assert_eq!(
                evaluation_span(&ns, arg_eval),
                law.exprs[*arg].span,
                "実引数の元AST順"
            );
            assert!(
                arr(f(body_source, "arguments")).contains(&children[i]),
                "元ArgEvaluationへ戻る"
            );
            let binding = bindings
                .iter()
                .find(|b| f(b, "name") == &Json::str(&parameter.name));
            if let Some(value_ref) = obj(val(arg_eval)).get("value") {
                let value = target(&ns, value_ref, &parameter.ty.wire());
                assert_eq!(
                    f(binding.unwrap(), "value"),
                    value_ref,
                    "等値だけで別producerに貼り替えない"
                );
                assert_eq!(f(value, "type"), &parameter.ty.wire());
                known.push(parameter.name.as_str());
            } else {
                assert!(
                    binding.is_none(),
                    "欠測実引数に通常Bindingや偽Scalarを作らない"
                );
            }
            // calleeのparameter出現は値が既知でも元ArgEvaluationを子に持つ。
            let reach = reached(&ns, &[body_ref]);
            for name_eval in reach
                .iter()
                .map(|id| ns[id.as_str()])
                .filter(|n| f(n, "type") == &Json::str("Evaluation"))
            {
                let name_source = expression(&ns, name_eval);
                if f(val(name_source), "kind") != &Json::str("source")
                    || !arr(f(name_source, "arguments")).contains(f(val(evaluation), "expression"))
                {
                    continue;
                }
                let name_span = evaluation_span(&ns, name_eval);
                if law.exprs.iter().any(|e| e.span == name_span && matches!(&e.kind, ExprKind::Dotted(names) if names.len()==1 && names[0].name==parameter.name)) {
                    assert_eq!(f(part(name_eval), "children"), &Json::Arr(vec![children[i].clone()]));
                    assert_eq!(obj(val(name_eval)).get("value"), obj(val(arg_eval)).get("value"));
                }
            }
        }
        assert_eq!(
            bindings
                .iter()
                .map(|b| text(f(b, "name")))
                .collect::<Vec<_>>(),
            known,
            "callee宣言順、既知parameterだけ"
        );
        if let Some(body_value) = obj(val(body_eval)).get("value") {
            let body_scalar = target(&ns, body_value, &returns.wire());
            let call_scalar = target(&ns, f(val(evaluation), "value"), &returns.wire());
            assert_eq!(
                val(call_scalar),
                val(body_scalar),
                "callはcalleeの型と値を保つ"
            );
            assert_eq!(f(f(call_scalar, "rule"), "kind"), &Json::str("law"));
            assert_eq!(
                span(f(f(call_scalar, "rule"), "location")),
                at,
                "call値は元のcall位置から導く"
            );
            assert_eq!(
                f(call_scalar, "arguments"),
                &Json::Arr(children.to_vec()),
                "元ArgEvaluation宣言順とcallee body Evaluationがcall値の導出根拠"
            );
            assert_eq!(f(call_scalar, "support"), f(evaluation, "support"));
            assert_eq!(f(call_scalar, "scope"), f(evaluation, "scope"));
            for child in children {
                let child = target(&ns, child, &Json::str("Evaluation"));
                for fact in arr(f(child, "support")) {
                    assert!(arr(f(call_scalar, "support")).contains(fact));
                }
                for key in ["readings", "snapshots", "modes"] {
                    for entry in arr(f(f(child, "scope"), key)) {
                        assert!(arr(f(f(call_scalar, "scope"), key)).contains(entry));
                    }
                }
                if f(f(child, "scope"), "domain") == &Json::str("all_completions") {
                    assert_eq!(
                        f(f(call_scalar, "scope"), "domain"),
                        &Json::str("all_completions")
                    );
                }
            }
        } else {
            assert!(!obj(val(evaluation)).contains_key("value"));
        }
        let scope = f(evaluation, "scope");
        assert!(arr(f(scope, "readings")).contains(&Json::str(&declaration.reading)));
        for fact in arr(f(body_eval, "support")) {
            assert!(arr(f(evaluation, "support")).contains(fact));
        }
        assert!(
            !arr(f(result, "nodes"))
                .iter()
                .any(|n| f(n, "type") == &Json::str("Expression")
                    && f(val(n), "kind") == &Json::str("source")
                    && span(f(val(n), "location")) == callee_at),
            "callee名tokenへ架空のEvaluationを作らない"
        );
    }
    calls
}

#[test]
fn named_calls_keep_six_exact_types_nested_frames_aliases_and_caller_lexical_state() {
    let helpers = r#"
 view one(): Z = 1;
 view bump(x: Z): Z = x+one();
 view rational(x: Q): Q = x+rat(2,6);
 view field(x: Fp(5)): Fp(5) = x+x;
 view tuple(x: (Z,Q,Fp(5))): (Z,Q,Fp(5)) = x+x;
 view flag(x: Bool): Bool = x;
 view reference(s: Sample): Sample = s;
"#;
    let caller = r#"
 view zero(): Z = H.one();
 view integer(s: Sample): Z = let x=H.bump(s.z) in (H.bump)(x)+H.bump(5)+s.z;
 view rational(s: Sample): Q = H.rational(s.q);
 view field(s: Sample): Fp(5) = H.field(s.f);
 view tuple(s: Sample): (Z,Q,Fp(5)) = H.tuple(s.t);
 view flag(s: Sample): Bool = H.flag(s.p);
 view reference(s: Sample): Sample = H.reference(s);
"#;
    let (result, checked) = run(
        fixture(&[], helpers, caller),
        &[
            "zero=evaluate(Calc.zero)",
            "z=evaluate(Calc.integer,s=@v/sample)",
            "q=evaluate(Calc.rational,s=@v/sample)",
            "f=evaluate(Calc.field,s=@v/sample)",
            "t=evaluate(Calc.tuple,s=@v/sample)",
            "b=evaluate(Calc.flag,s=@v/sample)",
            "r=evaluate(Calc.reference,s=@v/sample)",
        ],
    );
    assert_eq!(f(&result, "status"), &Json::str("complete"));
    for (id, ty, expected) in [
        ("zero", Json::str("Z"), Json::str("1")),
        ("z", Json::str("Z"), Json::str("14")),
        ("q", Json::str("Q"), q("-1", "3")),
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
    ] {
        output(&result, id, &ty, expected);
    }
    let zero = checked
        .law()
        .infos
        .iter()
        .find(|d| d.name == "Calc.zero")
        .unwrap();
    assert!(
        zero.references
            .iter()
            .any(|(_, name)| name == "Helpers.one")
    );
    assert!(!zero.references.iter().any(|(_, name)| name == "H.one"));
    assert!(audit_calls(&result, &checked) >= 12);
}

#[test]
fn heterogeneous_arguments_nested_calls_same_parameter_names_and_requests_keep_identity() {
    let helpers = r#"
 view bump(x: Z): Z = x+1;
 view value(s: Sample): Z = s.z;
 view reference(s: Sample): Sample = s;
 view mixed(x: Z,b: Bool,q: Q,s: Sample): (Z,Q,Fp(5)) = if b then (x,q,1) else (x+s.z,q+rat(1,3),4);
"#;
    let caller = r#"
 view nested(s: Sample): Z = H.bump(H.bump(s.z));
 view isolated(s: Sample,t: Sample): Z = H.value(t)+s.z;
 view mixed(s: Sample): (Z,Q,Fp(5)) = H.mixed(s.z,s.p,s.q,s);
 view reference(s: Sample): Sample = H.reference(s);
"#;
    let (result, checked) = run(
        fixture(&[], helpers, caller),
        &[
            "n=evaluate(Calc.nested,s=@v/sample)",
            "isolated=evaluate(Calc.isolated,s=@v/sample,t=@v/other)",
            "mixed=evaluate(Calc.mixed,s=@v/sample)",
            "r=evaluate(Calc.reference,s=@v/sample)",
            "other=evaluate(Calc.reference,s=@v/other)",
            "repeat=evaluate(Calc.reference,s=@v/sample)",
        ],
    );
    output(&result, "n", &Json::str("Z"), Json::str("5"));
    output(&result, "isolated", &Json::str("Z"), Json::str("14"));
    output(
        &result,
        "mixed",
        &tuple_type(),
        Json::Arr(vec![Json::str("6"), q("-1", "3"), Json::str("4")]),
    );
    for (id, subject) in [("r", "sample"), ("other", "other"), ("repeat", "sample")] {
        output(
            &result,
            id,
            &reference_type(),
            Json::Arr(vec![Json::str("v"), Json::str(subject)]),
        );
        let ns = index(&result);
        let reach = reached(&ns, &[f(answer(&result, id), "outputs")]);
        for ev in reach
            .iter()
            .map(|id| ns[id.as_str()])
            .filter(|n| f(n, "type") == &Json::str("Evaluation"))
        {
            for binding in arr(f(val(ev), "bindings")) {
                assert_eq!(
                    val(target(&ns, f(binding, "value"), &reference_type())),
                    &Json::Arr(vec![Json::str("v"), Json::str(subject)])
                );
            }
        }
        let scope = f(answer(&result, id), "scope");
        assert_eq!(
            f(scope, "readings"),
            &Json::Arr(vec![Json::str("Calc"), Json::str("Helpers")])
        );
        assert_eq!(f(scope, "snapshots"), &Json::Arr(vec![Json::str("v")]));
        assert_eq!(
            f(scope, "modes"),
            &Json::Arr(vec![Json::str("specification")])
        );
    }
    assert_eq!(audit_calls(&result, &checked), 7);
}

fn assert_missing(result: &Json, id: &str, fields: &[&str], checked: &CheckedInputs) {
    let a = answer(result, id);
    assert_eq!(f(f(a, "scope"), "domain"), &Json::str("all_completions"));
    let ns = index(result);
    let actual: BTreeSet<_> = arr(f(a, "reasons"))
        .iter()
        .filter(|r| f(r, "code") == &Json::str("missing_observation"))
        .flat_map(|r| {
            for dep in arr(f(r, "dependencies")) {
                let ex = val(target(&ns, dep, &Json::str("Expression")));
                let at = span(f(ex, "location"));
                let original = &checked.sources().law().bytes()[at.0..at.1];
                assert!(
                    original == b"s.z" || original == b"s.p",
                    "元fieldの出現に欠測を保持: {original:?}"
                );
            }
            arr(f(r, "missing"))
        })
        .map(|m| {
            assert_eq!(f(m, "snapshot"), &Json::str("v"));
            assert_eq!(f(m, "subject"), &Json::str("sample"));
            assert!(!obj(m).contains_key("atom"));
            text(f(m, "field")).to_owned()
        })
        .collect();
    assert_eq!(
        actual,
        fields
            .iter()
            .map(|name| format!("Calls.Sample.{name}"))
            .collect()
    );
}

// Evaluation の実際の子だけを辿る。Source の補完seedへの参照を辿って
// 元評価をcaseのcalleeとして再計数しない。
fn evaluation_tree(ns: &BTreeMap<&str, &Json>, root: &Json) -> BTreeSet<String> {
    let mut pending = vec![root];
    let mut seen = BTreeSet::new();
    while let Some(evaluation) = pending.pop() {
        assert_eq!(f(evaluation, "type"), &Json::str("Evaluation"));
        if !seen.insert(text(f(evaluation, "id")).to_owned()) {
            continue;
        }
        for p in arr(f(val(evaluation), "parts")) {
            for child in arr(f(p, "children")) {
                pending.push(target(ns, child, &Json::str("Evaluation")));
            }
        }
    }
    seen
}

#[test]
fn missing_actual_arguments_and_callee_fields_keep_original_slots_without_fake_bindings() {
    let helpers = r#"
 view integer(x: Z): Z = x+1;
 view flag(x: Bool): Bool = not x;
 view ignored_integer(x: Z): Z = 7;
 view ignored_flag(x: Bool): Bool = false;
 view field(s: Sample): Z = s.z;
"#;
    let caller = r#"
 view integer(s: Sample): Z = H.integer(s.z);
 view flag(s: Sample): Bool = H.flag(s.p);
 view ignored_integer(s: Sample): Z = H.ignored_integer(s.z);
 view ignored_flag(s: Sample): Bool = H.ignored_flag(s.p);
 view field(s: Sample): Z = H.field(s);
"#;
    let (result, checked) = run(
        fixture(&["z", "p"], helpers, caller),
        &[
            "z=evaluate(Calc.integer,s=@v/sample)",
            "b=evaluate(Calc.flag,s=@v/sample)",
            "constant_z=evaluate(Calc.ignored_integer,s=@v/sample)",
            "constant_b=evaluate(Calc.ignored_flag,s=@v/sample)",
            "field=evaluate(Calc.field,s=@v/sample)",
        ],
    );
    assert_eq!(f(&result, "status"), &Json::str("partial"));
    for id in ["z", "b", "field"] {
        assert_eq!(f(answer(&result, id), "status"), &Json::str("undetermined"));
        assert!(!obj(f(answer(&result, id), "outputs")).contains_key("value"));
    }
    output(&result, "constant_z", &Json::str("Z"), Json::str("7"));
    output(&result, "constant_b", &Json::str("Bool"), Json::Bool(false));
    for (id, field) in [
        ("z", "z"),
        ("b", "p"),
        ("constant_z", "z"),
        ("constant_b", "p"),
        ("field", "z"),
    ] {
        assert_missing(&result, id, &[field], &checked);
    }
    let ns = index(&result);
    let mut original = BTreeSet::new();
    let mut case_calls = BTreeSet::new();
    let mut aggregates = BTreeSet::new();
    for id in ["z", "b", "constant_z", "constant_b", "field"] {
        let a = answer(&result, id);
        let root = target(
            &ns,
            f(f(a, "outputs"), "evaluation"),
            &Json::str("Evaluation"),
        );
        if !["b", "constant_b"].contains(&id) {
            original.extend(evaluation_tree(&ns, root));
            continue;
        }
        assert!(aggregates.insert(text(f(root, "id")).to_owned()));
        let seed = expression(&ns, root);
        let raw_roots = arr(f(seed, "arguments"))
            .iter()
            .filter_map(|reference| {
                let node = ns[text(f(reference, "node"))];
                (f(node, "type") == &Json::str("Evaluation")).then_some(node)
            })
            .collect::<Vec<_>>();
        assert_eq!(
            raw_roots.len(),
            1,
            "CompletionSeedは元の問いのproducerを保持する"
        );
        let raw = raw_roots[0];
        assert_eq!(evaluation_span(&ns, raw), evaluation_span(&ns, root));
        assert!(!obj(val(raw)).contains_key("value") || id == "constant_b");
        original.extend(evaluation_tree(&ns, raw));
        let arguments = arr(f(root, "arguments"));
        assert_eq!(&arguments[0], f(val(root), "expression"));
        let domain = target(&ns, &arguments[1], &Json::str("Domain"));
        assert_eq!(f(val(domain), "kind"), &Json::str("finite"));
        assert_eq!(f(val(domain), "type"), &Json::str("Bool"));
        let members = arr(f(val(domain), "elements"));
        assert_eq!(members.len(), 2);
        assert_eq!(
            members
                .iter()
                .map(|r| val(target(&ns, r, &Json::str("Bool"))).canonical())
                .collect::<BTreeSet<_>>(),
            BTreeSet::from(["false".into(), "true".into()])
        );
        assert_eq!(
            arr(f(domain, "arguments")).first(),
            Some(f(val(root), "expression"))
        );
        let cases = arr(f(part(root), "children"));
        assert_eq!(cases.len(), 2);
        let mut assignments = BTreeSet::new();
        for case_ref in cases {
            let case = target(&ns, case_ref, &Json::str("Evaluation"));
            assert_eq!(evaluation_span(&ns, case), evaluation_span(&ns, raw));
            for evaluation in [raw, case] {
                let bindings = arr(f(val(evaluation), "bindings"));
                assert_eq!(bindings.len(), 1);
                assert_eq!(f(&bindings[0], "name"), &Json::str("s"));
                assert_eq!(
                    val(target(&ns, f(&bindings[0], "value"), &reference_type())),
                    &Json::Arr(vec![Json::str("v"), Json::str("sample")])
                );
            }
            let source = expression(&ns, case);
            let selected = arr(f(source, "arguments"))
                .iter()
                .filter(|r| members.contains(r))
                .collect::<Vec<_>>();
            assert_eq!(
                selected.len(),
                1,
                "case元Sourceから一つの補完assignmentへ戻る"
            );
            let assignment = val(target(&ns, selected[0], &Json::str("Bool")));
            assert!(assignments.insert(assignment.canonical()));
            let Json::Bool(assigned) = assignment else {
                panic!("Bool assignment")
            };
            let expected = id == "b" && !assigned;
            assert_eq!(
                val(target(&ns, f(val(case), "value"), &Json::str("Bool"))),
                &Json::Bool(expected)
            );
            let tree = evaluation_tree(&ns, case);
            assert_eq!(
                audit_calls_in(&result, &checked, Some(&tree)),
                1,
                "各補完caseも元call/引数/別callee frameを保持"
            );
            assert!(tree.is_disjoint(&original));
            case_calls.extend(tree);
        }
        assert_eq!(assignments, BTreeSet::from(["false".into(), "true".into()]));
        let proofs = arr(f(a, "evidence"))
            .iter()
            .map(|r| target(&ns, r, &Json::str("Evidence")))
            .collect::<Vec<_>>();
        let pairs = proofs
            .iter()
            .filter(|e| f(val(e), "kind") == &Json::str("completion_pair"))
            .collect::<Vec<_>>();
        let coverage = proofs
            .iter()
            .filter(|e| f(val(e), "kind") == &Json::str("finite_exhaustion"))
            .collect::<Vec<_>>();
        if id == "b" {
            assert_eq!(pairs.len(), 1);
            assert!(coverage.is_empty());
            let pair = f(val(pairs[0]), "data");
            assert_eq!(
                f(pair, "fields"),
                &Json::Arr(vec![Json::obj([
                    ("snapshot", Json::str("v")),
                    ("subject", Json::str("sample")),
                    ("field", Json::str("Calls.Sample.p"))
                ])])
            );
            let mut pair_results = BTreeSet::new();
            for (assignment, result) in [("first", "first_result"), ("second", "second_result")] {
                let values = arr(f(pair, assignment));
                assert_eq!(values.len(), 1);
                let assigned = val(target(&ns, &values[0], &Json::str("Bool")));
                let Json::Bool(assigned) = assigned else {
                    panic!("Bool pair")
                };
                assert!(cases.contains(f(pair, result)));
                let evaluation = target(&ns, f(pair, result), &Json::str("Evaluation"));
                let value = val(target(&ns, f(val(evaluation), "value"), &Json::str("Bool")));
                assert_eq!(value, &Json::Bool(!assigned));
                assert!(pair_results.insert(value.canonical()));
            }
            assert_eq!(
                pair_results,
                BTreeSet::from(["false".into(), "true".into()])
            );
        } else {
            assert!(pairs.is_empty());
            assert_eq!(coverage.len(), 1);
            let proof = f(val(coverage[0]), "data");
            assert_eq!(f(proof, "checked"), &Json::Nat(2));
            assert_eq!(
                target(&ns, f(proof, "domain"), &Json::str("Domain")),
                domain
            );
            assert_eq!(f(proof, "instances"), &Json::Arr(cases.to_vec()));
        }
    }
    assert_eq!(
        audit_calls_in(&result, &checked, Some(&original)),
        5,
        "元の五callの欠測実引数とcallee束縛を保持"
    );
    assert_eq!(
        audit_calls_in(&result, &checked, Some(&case_calls)),
        4,
        "二つのBool問いそれぞれに補完callが二つ"
    );
    original.extend(case_calls);
    assert_eq!(
        audit_calls_in(&result, &checked, Some(&original)),
        9,
        "元callとcaseを通してcallee bodyを共有しない"
    );
    let actual = arr(f(&result, "nodes"))
        .iter()
        .filter(|n| {
            f(n, "type") == &Json::str("Evaluation") && !aggregates.contains(text(f(n, "id")))
        })
        .map(|n| text(f(n, "id")).to_owned())
        .collect::<BTreeSet<_>>();
    assert_eq!(
        actual, original,
        "二つの補完集約を除く全Evaluationは元rootか四caseに属する"
    );
}

#[test]
fn calls_in_law_guards_and_bodies_keep_false_values_distinct_from_refutation() {
    let helpers = "view flag(x: Bool): Bool = x; view positive(x: Z): Bool = x>0;";
    let caller = r#"
 view flag(s: Sample): Bool = H.flag(s.p);
 law required guarded(s: Sample) when H.positive(s.z): H.flag(s.p);
 law required skipped(s: Sample) when H.flag(s.p): H.positive(s.z);
"#;
    let (result, checked) = run(
        fixture(&[], helpers, caller),
        &[
            "v=evaluate(Calc.flag,s=@v/sample)",
            "guarded_check=check(Calc.guarded,s=@v/sample)",
            "skip=check(Calc.skipped,s=@v/sample)",
        ],
    );
    output(&result, "v", &Json::str("Bool"), Json::Bool(false));
    let ns = index(&result);
    let law = answer(&result, "guarded_check");
    assert_eq!(f(law, "status"), &Json::str("refuted"));
    let claim = target(&ns, f(law, "claim"), &Json::str("Proposition"));
    assert_eq!(f(f(claim, "judgment"), "status"), &Json::str("refuted"));
    assert_eq!(f(f(law, "outputs"), "proposition"), f(law, "claim"));
    let evidence = arr(f(law, "evidence"))
        .iter()
        .map(|r| val(target(&ns, r, &Json::str("Evidence"))))
        .find(|e| f(e, "kind") == &Json::str("counterexample"))
        .unwrap();
    assert_eq!(
        val(target(
            &ns,
            f(f(evidence, "data"), "left"),
            &Json::str("Bool")
        )),
        &Json::Bool(false)
    );
    assert_eq!(
        val(target(
            &ns,
            f(f(evidence, "data"), "right"),
            &Json::str("Bool")
        )),
        &Json::Bool(true)
    );
    let skip = answer(&result, "skip");
    assert_eq!(f(skip, "status"), &Json::str("established"));
    let reach = reached(&ns, &[f(skip, "outputs"), f(skip, "evidence")]);
    assert!(
        reach
            .iter()
            .map(|id| ns[id.as_str()])
            .any(|n| f(n, "type") == &Json::str("Evaluation")
                && f(val(n), "applicability") == &Json::str("not_applicable"))
    );
    assert_eq!(
        audit_calls(&result, &checked),
        5,
        "view一件と二つのLawのguard/body四件すべてを監査する"
    );
}

#[test]
fn invalid_callee_and_argument_types_are_rejected_from_bytes_at_original_locations() {
    let helpers = "view one(): Z = 1; view integer(x: Z): Z = x+1;";
    let (normal, checked) = run(
        fixture(&[], helpers, "view good(s: Sample): Z = H.integer(s.z);"),
        &["v=evaluate(Calc.good,s=@v/sample)"],
    );
    output(&normal, "v", &Json::str("Z"), Json::str("4"));
    assert_eq!(audit_calls(&normal, &checked), 1);
    for (caller, expected_code) in [
        ("view good(s: Sample): Z = H.unknown(s.z);", "reference"),
        ("view good(s: Sample): Z = H.rawonly();", "reference"),
        ("view good(s: Sample): Z = H.integer(s.p);", "type"),
        (
            "view good(s: Sample): Z = if true then H.integer(s.z) else H.integer(s.p);",
            "type",
        ),
        (
            "view good(s: Sample): Z = H.integer(s.z); view unused(): Z = H.one(false);",
            "syntax",
        ),
    ] {
        let inputs = fixture(&[], helpers, caller);
        let law = inputs.law().bytes().to_vec();
        let failure =
            evaluate_observed_bytes(inputs, &["v=evaluate(Calc.good,s=@v/sample)"], &mut quiet())
                .unwrap_err();
        let wire = failure.wire().expect("静的不正は型付きinvalidを返す");
        assert_eq!(f(&wire, "status"), &Json::str("invalid"), "{caller}");
        let issue = &arr(f(&wire, "issues"))[0];
        // resolve_calleeの未解決名はreference、期待ZへのBool不一致はtype、
        // check_callのarity不一致は既存のsyntaxとして返る。
        assert_eq!(
            text(f(issue, "code")),
            expected_code,
            "caller={caller}, issue={issue:?}"
        );
        let (start, end) = span(f(issue, "location"));
        assert!(start < end && end <= law.len());
        let original = std::str::from_utf8(&law[start..end]).unwrap();
        assert!(caller.contains(original), "元の不正出現: {original}");
        for key in ["requests", "nodes", "answers"] {
            assert!(arr(f(&wire, key)).is_empty());
        }
    }
}

#[test]
fn injected_stops_after_arguments_inside_callee_and_before_caller_return_keep_prefixes() {
    let helpers = "view bump(x: Z): Z = x+1; view flag(x: Bool): Bool = x;";
    let caller = r#"
 view seed(s: Sample): Z = H.bump(s.z);
 view missing(s: Sample): Bool = H.flag(s.p);
 view current(s: Sample): Z = let y=H.bump(s.z) in y+1;
 view later(s: Sample): Z = H.bump(s.z);
"#;
    let asks = [
        "seed=evaluate(Calc.seed,s=@v/sample)",
        "missing=evaluate(Calc.missing,s=@v/sample)",
        "current=evaluate(Calc.current,s=@v/sample)",
        "later=evaluate(Calc.later,s=@v/sample)",
    ];
    let count = Rc::new(Cell::new(0));
    let seen = count.clone();
    let mut baseline = Control::new(Limits::default(), move |point| {
        if point == Checkpoint::Expression {
            seen.set(seen.get() + 1);
        }
        Usage::default()
    });
    let inputs = fixture(&["p"], helpers, caller);
    let checked = check_inputs(inputs.clone(), &mut quiet()).unwrap();
    let prior = evaluate_observed_bytes(inputs.clone(), &asks[..2], &mut baseline)
        .unwrap()
        .wire();
    output(&prior, "seed", &Json::str("Z"), Json::str("4"));
    assert_missing(&prior, "missing", &["p"], &checked);
    // current: let前、call前、引数前後、calleeの二項式前、x前後、1前後、body後、call後。
    // 5は引数完了後、8はcallee内、11はcallee完了後でcallerのlet本体へ戻る前。
    for (offset, kind) in [(5, 0), (8, 1), (11, 2)] {
        let at = count.get() + offset;
        let expression_count = Rc::new(Cell::new(0));
        let probes = Rc::new(Cell::new(0));
        let frozen = Rc::new(Cell::new(None));
        let (expressions, calls, stop) = (expression_count.clone(), probes.clone(), frozen.clone());
        let mut control = Control::new(
            Limits {
                time_ms: (kind == 1).then_some(1),
                memory_mib: (kind == 2).then_some(1),
            },
            move |point| {
                calls.set(calls.get() + 1);
                if point == Checkpoint::Expression {
                    expressions.set(expressions.get() + 1);
                    if expressions.get() == at {
                        stop.set(Some(calls.get()));
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
        let result = evaluate_observed_bytes(inputs.clone(), &asks, &mut control)
            .unwrap()
            .wire();
        assert_eq!(
            f(&result, "status"),
            &Json::str("interrupted"),
            "停止点{offset}"
        );
        output(&result, "seed", &Json::str("Z"), Json::str("4"));
        for key in ["status", "reasons", "scope", "outputs"] {
            assert_eq!(
                f(answer(&result, "missing"), key),
                f(answer(&prior, "missing"), key),
                "元missingと先行導出を保持"
            );
        }
        for id in ["current", "later"] {
            let a = answer(&result, id);
            assert_eq!(f(a, "status"), &Json::str("undetermined"));
            assert!(
                obj(f(a, "outputs")).is_empty(),
                "未完成callerを通常値に昇格しない"
            );
            let reason = arr(f(a, "reasons"))
                .iter()
                .find(|r| {
                    f(r, "code")
                        == &Json::str(if kind == 0 {
                            "cancelled"
                        } else {
                            "budget_exhausted"
                        })
                })
                .unwrap();
            let expected = if kind == 0 {
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
            assert_eq!(f(reason, "details"), &expected);
        }
        audit_dag(&result, &checked);
        let ns = index(&result);
        let current = &checked.law().declarations["Calc.current"];
        let Signature::View { body, .. } = &current.signature else {
            panic!("view")
        };
        let ExprKind::Let { value: call_id, .. } = &checked.law().exprs[*body].kind else {
            panic!("let")
        };
        let ExprKind::Call { args, .. } = &checked.law().exprs[*call_id].kind else {
            panic!("call")
        };
        let call_span = checked.law().exprs[*call_id].span;
        let arg_span = checked.law().exprs[args[0]].span;
        let call_source = arr(f(&result, "nodes"))
            .iter()
            .find(|n| {
                f(n, "type") == &Json::str("Expression")
                    && f(val(n), "kind") == &Json::str("source")
                    && span(f(val(n), "location")) == call_span
            })
            .unwrap();
        let argument = arr(f(&result, "nodes"))
            .iter()
            .find(|n| {
                f(n, "type") == &Json::str("Evaluation") && evaluation_span(&ns, n) == arg_span
            })
            .unwrap();
        assert_eq!(
            val(target(&ns, f(val(argument), "value"), &Json::str("Z"))),
            &Json::str("3")
        );
        let call_ref = Json::obj([("node", f(call_source, "id").clone())]);
        let framed: Vec<_> = arr(f(&result, "nodes"))
            .iter()
            .filter(|n| {
                f(n, "type") == &Json::str("Expression")
                    && arr(f(n, "arguments")).contains(&call_ref)
            })
            .collect();
        if offset == 5 {
            assert!(framed.is_empty(), "callee開始前でも引数Evaluationは保持");
        } else {
            assert!(!framed.is_empty(), "親call未完成のprefixも元callへ戻れる");
        }
        if offset == 11 {
            assert!(
                arr(f(&result, "nodes"))
                    .iter()
                    .any(|n| f(n, "type") == &Json::str("Evaluation")
                        && evaluation_span(&ns, n) == call_span),
                "caller復帰前の完成calleeとcall Evaluationを保持"
            );
        }
        assert_eq!(expression_count.get(), at);
        assert_eq!(
            Some(probes.get()),
            frozen.get(),
            "停止後に新たなprobe/導出を始めない"
        );
        let before = probes.get();
        assert!(control.checkpoint(Checkpoint::Expression).is_err());
        assert_eq!(probes.get(), before);
    }
}

#[test]
fn one_zero_argument_named_call_retains_original_body_and_typed_derivation() {
    let (result, checked) = run(
        fixture(&[], "view one(): Z = 1;", "view zero(): Z = H.one();"),
        &["v=evaluate(Calc.zero)"],
    );
    assert_eq!(f(&result, "status"), &Json::str("complete"));
    output(&result, "v", &Json::str("Z"), Json::str("1"));
    assert_eq!(audit_calls(&result, &checked), 1);
    let scope = f(answer(&result, "v"), "scope");
    assert_eq!(
        f(scope, "readings"),
        &Json::Arr(vec![Json::str("Calc"), Json::str("Helpers")])
    );
    assert_eq!(f(scope, "snapshots"), &Json::Arr(vec![]));
    assert_eq!(f(scope, "modes"), &Json::Arr(vec![]));
    let ns = index(&result);
    let evaluation = target(
        &ns,
        f(f(answer(&result, "v"), "outputs"), "evaluation"),
        &Json::str("Evaluation"),
    );
    let call_span = evaluation_span(&ns, evaluation);
    assert_eq!(
        &checked.sources().law().bytes()[call_span.0..call_span.1],
        b"H.one()"
    );
    let body = target(
        &ns,
        &arr(f(part(evaluation), "children"))[0],
        &Json::str("Evaluation"),
    );
    let body_span = evaluation_span(&ns, body);
    assert_eq!(
        &checked.sources().law().bytes()[body_span.0..body_span.1],
        b"1"
    );
    assert!(arr(f(val(body), "bindings")).is_empty());
    assert!(arr(f(part(body), "children")).is_empty());
    let body_scalar = target(&ns, f(part(body), "value"), &Json::str("Z"));
    let call_scalar = target(&ns, f(val(evaluation), "value"), &Json::str("Z"));
    assert_eq!(val(body_scalar), &Json::str("1"));
    assert_eq!(val(call_scalar), val(body_scalar));
    assert_eq!(f(f(call_scalar, "rule"), "kind"), &Json::str("law"));
    assert_eq!(span(f(f(call_scalar, "rule"), "location")), call_span);
    assert_eq!(f(call_scalar, "arguments"), f(part(evaluation), "children"));
    assert_eq!(f(call_scalar, "support"), f(evaluation, "support"));
    assert_eq!(f(call_scalar, "scope"), scope);
}

#[test]
fn owned_callee_parameters_remain_not_implemented_without_membership_evidence() {
    use archsig::observed::{
        EvaluationFailure, PrepareFailure,
        request::{RequestIssueCode, ResolveFailure},
    };
    let original_law = include_str!("fixtures/reservations.law");
    let original_map = include_str!("fixtures/reservations.archmap.json");
    let law = original_law.replace(
        "  view holdings(s: State): (Z, Z) = (s.free, s.held);",
        r#"  view raw(s: State): Z = s.free;
  view plain(system: System,s: State): Z = raw(s);
  view owned(system: System,s: State[system]): Z = s.free;
  view caller(system: System,s: State): Z = owned(system,s);
  view claimed(system: System,s: State): State[system] = s;
  view return_caller(system: System,s: State): State = claimed(system,s);
  law required member(system: System,s: State): owned(system,s)=4;
  view holdings(s: State): (Z, Z) = (s.free, s.held);"#,
    );
    assert!(law.contains("view owned(system: System,s: State[system])"));
    let missing_map = original_map
        .lines()
        .filter(|line| !line.contains(r#""id": "r-owner""#))
        .collect::<Vec<_>>()
        .join("\n");
    assert_ne!(original_map, missing_map);
    let sources = |map: &str| {
        InputSources::from_bytes(
            vec![include_bytes!("fixtures/reservations.atoms.json").to_vec()],
            law.as_bytes().to_vec(),
            map.as_bytes().to_vec(),
        )
    };
    // plain Ref callは所属を要求せず、直接Owned Requestは所属一致を既存経路で確認する。
    let (normal, checked) = run(
        sources(original_map),
        &[
            "plain=evaluate(Reservations.plain,system=@v/A,s=@v/r)",
            "direct=evaluate(Reservations.owned,system=@v/B,s=@v/r)",
        ],
    );
    assert_eq!(f(&normal, "status"), &Json::str("complete"));
    for id in ["plain", "direct"] {
        output(&normal, id, &Json::str("Z"), Json::str("4"));
    }
    let ns = index(&normal);
    let plain = target(
        &ns,
        f(f(answer(&normal, "plain"), "outputs"), "evaluation"),
        &Json::str("Evaluation"),
    );
    assert_eq!(arr(f(part(plain), "children")).len(), 2);
    let direct_failure = evaluate_observed_bytes(
        sources(original_map),
        &["bad=evaluate(Reservations.owned,system=@v/A,s=@v/r)"],
        &mut quiet(),
    )
    .unwrap_err();
    let direct_invalid = direct_failure
        .wire()
        .expect("既知owner不一致の直接Requestは既存のinvalid");
    let EvaluationFailure::Prepare(PrepareFailure::Requests {
        failure: ResolveFailure::Invalid { issues, .. },
        ..
    }) = &direct_failure
    else {
        panic!("既存のRequest型不一致");
    };
    assert_eq!(issues.len(), 1);
    assert_eq!(issues[0].code, RequestIssueCode::Type);
    assert_eq!(issues[0].request, "bad");
    assert_eq!(issues[0].argument, "bind.s");
    assert_eq!(issues[0].message, "依存 parameter の owner が合わない");
    assert_eq!(f(&direct_invalid, "status"), &Json::str("invalid"));
    let direct_issue = &arr(f(&direct_invalid, "issues"))[0];
    assert_eq!(f(direct_issue, "request"), &Json::str("bad"));
    assert_eq!(
        f(direct_issue, "message"),
        &Json::str("依存 parameter の owner が合わない")
    );
    assert_eq!(arr(f(&direct_invalid, "issues")).len(), 1);
    assert_eq!(
        f(&arr(f(&direct_invalid, "issues"))[0], "code"),
        &Json::str("usage")
    );
    assert_eq!(
        f(&arr(f(&direct_invalid, "issues"))[0], "details"),
        &Json::obj([("argument", Json::str("bind.s"))])
    );
    for key in ["nodes", "answers"] {
        assert!(arr(f(&direct_invalid, key)).is_empty());
    }
    let Signature::View {
        body: caller_body, ..
    } = &checked.law().declarations["Reservations.caller"].signature
    else {
        panic!("caller view");
    };
    let caller_span = checked.law().exprs[*caller_body].span;
    let Signature::Law {
        body: member_body, ..
    } = &checked.law().declarations["Reservations.member"].signature
    else {
        panic!("member Law");
    };
    let ExprKind::Binary {
        lhs: member_call, ..
    } = &checked.law().exprs[*member_body].kind
    else {
        panic!("元等号");
    };
    let member_span = checked.law().exprs[*member_call].span;
    for at in [caller_span, member_span] {
        assert_eq!(&law.as_bytes()[at.0..at.1], b"owned(system,s)");
    }
    let Signature::View {
        body: return_body, ..
    } = &checked.law().declarations["Reservations.return_caller"].signature
    else {
        panic!("return caller view");
    };
    let return_span = checked.law().exprs[*return_body].span;
    assert_eq!(
        &law.as_bytes()[return_span.0..return_span.1],
        b"claimed(system,s)"
    );
    let mut unexpected = Vec::new();
    for (label, map, ask, at) in [
        (
            "known mismatch",
            original_map,
            "bad=evaluate(Reservations.caller,system=@v/A,s=@v/r)",
            caller_span,
        ),
        (
            "missing owner",
            missing_map.as_str(),
            "bad=evaluate(Reservations.caller,system=@v/A,s=@v/r)",
            caller_span,
        ),
        (
            "Law",
            original_map,
            "badcheck=check(Reservations.member,system=@v/A,s=@v/r)",
            member_span,
        ),
        (
            "same owner named call",
            original_map,
            "same=evaluate(Reservations.caller,system=@v/B,s=@v/r)",
            caller_span,
        ),
        (
            "Owned return with plain parameters",
            original_map,
            "returned=evaluate(Reservations.return_caller,system=@v/A,s=@v/r)",
            return_span,
        ),
    ] {
        match evaluate_observed_bytes(sources(map), &[ask], &mut quiet()) {
            Err(failure) => {
                assert!(
                    failure.wire().is_none(),
                    "未確認所属をinvalidへ変えない: {label}"
                );
                let EvaluationFailure::NotImplemented {
                    location: archsig::issue::Location::Law { span },
                    feature,
                    ..
                } = failure
                else {
                    panic!("Owned calleeは専用未実装: {label}");
                };
                assert_eq!(span, at, "元call出現を保持: {label}");
                assert!(
                    feature.contains("owner"),
                    "所属条件の未実装を示す: {feature}"
                );
            }
            Ok(result) => {
                let wire = result.wire();
                unexpected.push(format!(
                    "{label}: status={}, answer={:?}",
                    result.status(),
                    f(&wire, "answers")
                ));
            }
        }
    }
    assert!(
        unexpected.is_empty(),
        "Owned calleeの未確認所属から値/Law判断を確定しない: {unexpected:#?}"
    );
}
