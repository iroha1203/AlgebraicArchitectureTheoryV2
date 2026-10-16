//! AC1 の byte → 型付き回答。期待値は I/O の最小の一周と結果 §§1–3,6 による。
use archsig::{
    canonical::Json,
    definition::check_definitions,
    observed::{
        EvaluationFailure, PrepareFailure,
        control::{Checkpoint, Control, Limits, Usage},
        evaluate_observed, evaluate_observed_bytes,
        input::{InputSources, check_inputs},
        prepare_checked_observed,
    },
    result::Signal,
};
use std::{
    cell::Cell,
    collections::{BTreeMap, BTreeSet},
    rc::Rc,
};

const DEFINITIONS: &[u8] = include_bytes!("fixtures/counter.atoms.json");
const LAW: &[u8] = include_bytes!("fixtures/counter.law");
const MAP: &[u8] = include_bytes!("fixtures/counter.archmap.json");
const ASKS: [&str; 3] = [
    "n=evaluate(CountCheck.amount,s=@v/s)",
    "ok=check(CountCheck.nonnegative,s=@v/s)",
    "audit=check(CountAudit.bounded,s=@v/s)",
];

fn quiet_control() -> Control {
    Control::new(Limits::default(), |_| Usage::default())
}
fn sources(law: &[u8], map: &[u8]) -> InputSources {
    InputSources::from_bytes(vec![DEFINITIONS.to_vec()], law.to_vec(), map.to_vec())
}
fn map_count(value: Option<&str>) -> Vec<u8> {
    let text = String::from_utf8(MAP.to_vec()).unwrap();
    match value {
        Some(value) => text.replace("\"value\": \"2\"", &format!("\"value\": \"{value}\"")).into_bytes(),
        None => text.replace("{\"id\": \"count\", \"subject\": \"s\", \"field\": \"Counter.State.count\", \"value\": \"2\", \"origin\": \"model\"}", "").into_bytes(),
    }
}
fn run(src: InputSources, asks: &[&str]) -> Json {
    evaluate_observed_bytes(src, asks, &mut quiet_control())
        .unwrap()
        .wire()
}
fn obj(value: &Json) -> &BTreeMap<String, Json> {
    let Json::Obj(fields) = value else {
        panic!("object: {value:?}")
    };
    fields
}
fn arr(value: &Json) -> &[Json] {
    let Json::Arr(values) = value else {
        panic!("array: {value:?}")
    };
    values
}
fn text(value: &Json) -> &str {
    let Json::Str(value) = value else {
        panic!("string: {value:?}")
    };
    value
}
fn field<'a>(value: &'a Json, name: &str) -> &'a Json {
    &obj(value)[name]
}
fn number(value: &Json) -> usize {
    let Json::Nat(value) = value else {
        panic!("Nat: {value:?}")
    };
    *value as usize
}
fn nodes(result: &Json) -> BTreeMap<&str, &Json> {
    arr(field(result, "nodes"))
        .iter()
        .map(|node| (text(field(node, "id")), node))
        .collect()
}
fn target<'a>(index: &BTreeMap<&str, &'a Json>, reference: &Json) -> &'a Json {
    assert_eq!(obj(reference).len(), 1, "Ref の欄は node だけ");
    index[text(field(reference, "node"))]
}
fn typed<'a>(index: &BTreeMap<&str, &'a Json>, reference: &Json, ty: &str) -> &'a Json {
    let node = target(index, reference);
    assert_eq!(field(node, "type"), &Json::str(ty));
    node
}
fn value(node: &Json) -> &Json {
    assert_eq!(field(node, "state"), &Json::str("value"));
    field(node, "value")
}
fn answer<'a>(result: &'a Json, id: &str) -> &'a Json {
    arr(field(result, "answers"))
        .iter()
        .find(|a| text(field(a, "id")) == id)
        .unwrap()
}
fn span(location: &Json) -> (usize, usize) {
    assert_eq!(field(location, "input"), &Json::str("law"));
    let pair = arr(field(location, "span"));
    assert_eq!(pair.len(), 2);
    (number(&pair[0]), number(&pair[1]))
}
fn visit_refs(value: &Json, refs: &mut Vec<String>) {
    match value {
        Json::Obj(fields) if fields.len() == 1 && fields.contains_key("node") => {
            refs.push(text(&fields["node"]).to_owned())
        }
        Json::Obj(fields) => {
            for child in fields.values() {
                visit_refs(child, refs);
            }
        }
        Json::Arr(values) => {
            for child in values {
                visit_refs(child, refs);
            }
        }
        _ => {}
    }
}

// 表示番号の個数や具体値には依存せず、参照順、型、blocked の非消費を読む。
fn audit_dag(result: &Json) {
    let index = nodes(result);
    let mut earlier = BTreeSet::new();
    for node in arr(field(result, "nodes")) {
        let id = text(field(node, "id"));
        let mut refs = vec![];
        visit_refs(node, &mut refs);
        for reference in refs {
            assert!(
                earlier.contains(reference.as_str()),
                "{id} → {reference} は既出である"
            );
        }
        assert!(earlier.insert(id));
        let ty = field(node, "type");
        if ty != &Json::str("Proposition") {
            assert!(!obj(node).contains_key("judgment"));
        }
        if field(node, "state") == &Json::str("blocked") {
            assert!(!obj(node).contains_key("value"));
            assert!(!arr(field(node, "reasons")).is_empty());
        }
        if let Some(payload) = obj(node).get("value") {
            let mut consumed = vec![];
            visit_refs(payload, &mut consumed);
            for reference in consumed {
                assert_ne!(
                    field(index[reference.as_str()], "state"),
                    &Json::str("blocked"),
                    "payload に blocked 値を消費しない"
                );
            }
            match ty {
                Json::Str(ty) if ty == "Evaluation" => {
                    typed(&index, field(payload, "expression"), "Expression");
                    for binding in arr(field(payload, "bindings")) {
                        target(&index, field(binding, "value"));
                    }
                    for part in arr(field(payload, "parts")) {
                        for child in arr(field(part, "children")) {
                            typed(&index, child, "Evaluation");
                        }
                    }
                }
                Json::Str(ty) if ty == "LawInstance" => {
                    typed(&index, field(payload, "body"), "Expression");
                    if let Some(guard) = obj(payload).get("guard") {
                        typed(&index, guard, "Expression");
                    }
                }
                Json::Str(ty) if ty == "Proposition" => {
                    assert_eq!(field(payload, "predicate"), &Json::str("law_holds"));
                    for operand in arr(field(payload, "operands")) {
                        typed(&index, operand, "LawInstance");
                    }
                }
                Json::Str(ty) if ty == "Evidence" => {
                    let data = field(payload, "data");
                    if field(payload, "kind") == &Json::str("evaluation") {
                        typed(&index, field(data, "instance"), "LawInstance");
                        for side in ["lhs", "rhs"] {
                            target(&index, field(data, side));
                        }
                    }
                    if field(payload, "kind") == &Json::str("counterexample") {
                        for side in ["left", "right"] {
                            typed(&index, field(data, side), "Z");
                        }
                    }
                }
                _ => {}
            }
        }
        for evidence in arr(field(node, "evidence")) {
            typed(&index, evidence, "Evidence");
        }
        for condition in arr(field(node, "conditions")) {
            typed(&index, condition, "Proposition");
        }
    }
    for answer in arr(field(result, "answers")) {
        let mut refs = vec![];
        visit_refs(answer, &mut refs);
        for reference in refs {
            assert!(
                index.contains_key(reference.as_str()),
                "Answer の全 Ref は生成済み node を指す"
            );
        }
        for (name, reference) in obj(field(answer, "outputs")) {
            match name.as_str() {
                "evaluation" => {
                    typed(&index, reference, "Evaluation");
                }
                "proposition" => {
                    typed(&index, reference, "Proposition");
                }
                "value" => {
                    target(&index, reference);
                }
                _ => panic!("対象二問に未知の output: {name}"),
            }
        }
        for reference in arr(field(answer, "evidence")) {
            typed(&index, reference, "Evidence");
        }
        if let Some(claim) = obj(answer).get("claim") {
            let proposition = typed(&index, claim, "Proposition");
            assert_eq!(
                field(field(proposition, "judgment"), "status"),
                field(answer, "status")
            );
            assert_eq!(claim, field(field(answer, "outputs"), "proposition"));
        }
    }
}

fn counter_scopes(result: &Json, domain: &str) {
    for item in arr(field(result, "answers"))
        .iter()
        .chain(arr(field(result, "nodes")))
    {
        let scope = field(item, "scope");
        if obj(item).contains_key("outputs") {
            assert_eq!(field(scope, "domain"), &Json::str(domain));
        } else {
            assert!(matches!(
                text(field(scope, "domain")),
                "finite_model" | "all_completions"
            ));
        }
        assert_eq!(field(scope, "snapshots"), &Json::Arr(vec![Json::str("v")]));
        assert_eq!(
            field(scope, "modes"),
            &Json::Arr(vec![Json::str("specification")])
        );
        assert!(arr(field(scope, "assumptions")).is_empty());
        assert!(arr(field(scope, "quantifiers")).is_empty());
        let readings = arr(field(scope, "readings"));
        assert!(!readings.is_empty());
        assert!(
            readings
                .iter()
                .all(|r| matches!(text(r), "CountCheck" | "CountAudit"))
        );
    }
}

#[test]
fn counter_two_has_typed_ordered_complete_answers() {
    let result = run(sources(LAW, MAP), &ASKS);
    assert_eq!(field(&result, "status"), &Json::str("complete"));
    assert_eq!(
        arr(field(&result, "answers"))
            .iter()
            .map(|a| text(field(a, "id")))
            .collect::<Vec<_>>(),
        ["n", "ok", "audit"]
    );
    let index = nodes(&result);
    for id in ["n", "ok", "audit"] {
        assert_eq!(
            field(answer(&result, id), "status"),
            &Json::str("established")
        );
    }
    let amount = answer(&result, "n");
    assert!(!obj(amount).contains_key("claim"));
    let output = typed(&index, field(field(amount, "outputs"), "value"), "Z");
    assert_eq!(value(output), &Json::str("2"));
    let evaluation = value(typed(
        &index,
        field(field(amount, "outputs"), "evaluation"),
        "Evaluation",
    ));
    assert_eq!(
        field(evaluation, "value"),
        field(field(amount, "outputs"), "value")
    );
    assert_eq!(field(evaluation, "applicability"), &Json::str("applicable"));
    assert!(!obj(evaluation).contains_key("environment"));
    for (request, original) in arr(field(&result, "requests")).iter().zip(ASKS) {
        assert_eq!(field(request, "text"), &Json::str(original));
        assert_eq!(
            field(&arr(field(request, "arguments"))[0], "origin"),
            &Json::str("explicit")
        );
        assert_eq!(
            field(request, "defaults"),
            &Json::Arr(vec![Json::obj([(
                "rule",
                Json::str("observed_environment")
            )])])
        );
    }
    audit_dag(&result);
    counter_scopes(&result, "finite_model");
}

#[test]
fn counter_twelve_keeps_exact_refutation_and_input_provenance() {
    let map = map_count(Some("12"));
    let result = run(sources(LAW, &map), &ASKS);
    assert_eq!(field(&result, "status"), &Json::str("complete"));
    assert_eq!(
        field(answer(&result, "ok"), "status"),
        &Json::str("established")
    );
    let audit = answer(&result, "audit");
    assert_eq!(field(audit, "status"), &Json::str("refuted"));
    let index = nodes(&result);
    assert_eq!(
        field(answer(&result, "n"), "status"),
        &Json::str("established")
    );
    assert_eq!(
        value(typed(
            &index,
            field(field(answer(&result, "n"), "outputs"), "value"),
            "Z"
        )),
        &Json::str("12")
    );
    let evidence = arr(field(audit, "evidence"))
        .iter()
        .map(|r| value(typed(&index, r, "Evidence")))
        .find(|e| field(e, "kind") == &Json::str("counterexample"))
        .expect("反証には検査できる反例");
    let data = field(evidence, "data");
    assert_eq!(
        value(typed(&index, field(data, "left"), "Z")),
        &Json::str("12")
    );
    assert_eq!(
        value(typed(&index, field(data, "right"), "Z")),
        &Json::str("10")
    );
    let binding = &arr(field(data, "bindings"))[0];
    assert_eq!(field(binding, "name"), &Json::str("s"));
    let subject = target(&index, field(binding, "value"));
    assert_eq!(
        field(subject, "type"),
        &Json::Arr(vec![Json::str("Ref"), Json::str("Counter.State")])
    );
    let expected_fact = Json::obj([
        ("snapshot", Json::str("v")),
        ("subject", Json::str("s")),
        ("field", Json::str("Counter.State.count")),
        ("atom", Json::str("count")),
    ]);
    assert!(arr(field(data, "facts")).contains(&expected_fact));
    let checked = check_inputs(sources(LAW, &map), &mut quiet_control()).unwrap();
    let snapshot = checked
        .archmap()
        .snapshots
        .iter()
        .find(|v| v.id == "v")
        .unwrap();
    let subject = snapshot.subjects.iter().find(|s| s.id == "s").unwrap();
    let slot = &subject
        .fields
        .iter()
        .find(|f| f.name == "Counter.State.count")
        .unwrap()
        .slot;
    let archsig::archmap::Slot::Known { atom, origin, .. } = slot else {
        panic!("反例は既知の原始事実を使う")
    };
    assert_eq!(atom, "count");
    assert!(
        checked
            .archmap()
            .origins
            .iter()
            .any(|o| &o.id == origin && o.mode == archsig::archmap::Mode::Specification)
    );
    for node in index.values() {
        if field(node, "type") == &Json::str("Evidence")
            && field(node, "state") == &Json::str("value")
        {
            let payload = value(node);
            if field(payload, "kind") == &Json::str("evaluation") {
                assert!(
                    !obj(field(payload, "data")).contains_key("residual"),
                    "不等式に整数残差を作らない"
                );
            }
        }
    }
    audit_dag(&result);
    counter_scopes(&result, "finite_model");
}

#[test]
fn absent_count_keeps_subject_missing_expression_and_all_completions() {
    let map = map_count(None);
    let checked = check_inputs(sources(LAW, &map), &mut quiet_control()).unwrap();
    assert!(
        checked
            .archmap()
            .snapshots
            .iter()
            .find(|s| s.id == "v")
            .unwrap()
            .subjects
            .iter()
            .any(|s| s.id == "s")
    );
    let result = run(sources(LAW, &map), &ASKS);
    assert_eq!(field(&result, "status"), &Json::str("partial"));
    let index = nodes(&result);
    assert!(index.values().any(|node| field(node, "type")
        == &Json::Arr(vec![Json::str("Ref"), Json::str("Counter.State")])
        && field(node, "state") == &Json::str("value")
        && value(node) == &Json::Arr(vec![Json::str("v"), Json::str("s")])));
    let missing = Json::obj([
        ("snapshot", Json::str("v")),
        ("subject", Json::str("s")),
        ("field", Json::str("Counter.State.count")),
    ]);
    for a in arr(field(&result, "answers")) {
        assert_eq!(field(a, "status"), &Json::str("undetermined"));
        let reasons = arr(field(a, "reasons"));
        let reason = reasons
            .iter()
            .find(|r| field(r, "code") == &Json::str("missing_observation"))
            .unwrap();
        assert_eq!(field(reason, "missing"), &Json::Arr(vec![missing.clone()]));
        assert!(!arr(field(reason, "dependencies")).is_empty());
        for dependency in arr(field(reason, "dependencies")) {
            typed(&index, dependency, "Expression");
        }
        let evaluation = value(typed(
            &index,
            field(field(a, "outputs"), "evaluation"),
            "Evaluation",
        ));
        assert!(!obj(evaluation).contains_key("value"));
        if let Some(v) = obj(field(a, "outputs")).get("value") {
            assert_eq!(field(target(&index, v), "state"), &Json::str("blocked"));
        }
    }
    for node in index.values() {
        if field(node, "type") == &Json::str("Evaluation")
            && field(node, "state") == &Json::str("value")
        {
            for part in arr(field(value(node), "parts")) {
                let (start, end) = span(field(part, "location"));
                if &LAW[start..end] == b"s.count" {
                    assert!(
                        !obj(part).contains_key("value"),
                        "欠測fieldを零/none/補完値にしない"
                    );
                }
            }
        }
    }
    audit_dag(&result);
    counter_scopes(&result, "all_completions");
}

#[test]
fn every_counter_ast_occurrence_has_source_expression_and_child_evaluation() {
    let checked = check_inputs(sources(LAW, MAP), &mut quiet_control()).unwrap();
    let result = run(sources(LAW, MAP), &ASKS);
    let index = nodes(&result);
    let mut expressions = BTreeMap::new();
    for node in index
        .values()
        .filter(|n| field(n, "type") == &Json::str("Expression"))
    {
        let payload = value(node);
        assert!(
            arr(field(payload, "parameters")).is_empty(),
            "全 parameter を明示束縛した式に自由 parameter を残さない"
        );
        if field(payload, "kind") == &Json::str("source") {
            let position = span(field(payload, "location"));
            assert!(
                checked.law().exprs.iter().any(|e| e.span == position)
                    || &LAW[position.0..position.1] == b"s",
                "省略guardへ架空の原式spanを作らない"
            );
            expressions.insert(position, text(field(node, "id")));
            let declaration = checked
                .law()
                .declarations
                .values()
                .find(|d| {
                    matches!(
                        &d.signature,
                        archsig::law::model::Signature::View { .. }
                            | archsig::law::model::Signature::Law { .. }
                    ) && d.span.0 <= position.0
                        && position.1 <= d.span.1
                })
                .unwrap();
            let params = match &declaration.signature {
                archsig::law::model::Signature::View { params, .. }
                | archsig::law::model::Signature::Law { params, .. } => params,
                _ => unreachable!(),
            };
            for binding in arr(field(payload, "bindings")) {
                let parameter = params
                    .iter()
                    .find(|p| p.name == text(field(binding, "name")))
                    .expect("束縛名は元署名にある");
                let bound = target(&index, field(binding, "value"));
                assert_eq!(field(bound, "type"), &parameter.ty.wire());
                assert_eq!(
                    value(bound),
                    &Json::Arr(vec![Json::str("v"), Json::str("s")])
                );
            }
            if std::str::from_utf8(&LAW[position.0..position.1])
                .unwrap()
                .contains('s')
            {
                assert!(
                    arr(field(payload, "bindings"))
                        .iter()
                        .any(|b| field(b, "name") == &Json::str("s")),
                    "s の自由出現を実束縛へ戻す"
                );
            }
        }
    }
    for (expr_id, expr) in checked.law().exprs.iter().enumerate() {
        if checked.law().expr_type(expr_id).is_none() {
            continue;
        }
        let source = expressions
            .get(&expr.span)
            .expect("各 AST 出現の source Expression");
        let evaluation = index
            .values()
            .find(|n| {
                field(n, "type") == &Json::str("Evaluation")
                    && field(value(n), "expression") == &Json::obj([("node", Json::str(*source))])
            })
            .expect("各出現の評価");
        let part = arr(field(value(evaluation), "parts"))
            .iter()
            .find(|p| span(field(p, "location")) == expr.span)
            .unwrap();
        let output = target(&index, field(part, "value"));
        assert_eq!(
            field(output, "type"),
            &checked.law().expr_type(expr_id).unwrap().wire()
        );
        for child in arr(field(part, "children")) {
            let evaluation = value(typed(&index, child, "Evaluation"));
            let expression = value(typed(&index, field(evaluation, "expression"), "Expression"));
            let child_span = span(field(expression, "location"));
            assert!(expr.span.0 <= child_span.0 && child_span.1 <= expr.span.1);
            assert_ne!(child_span, expr.span);
        }
    }
    for node in index
        .values()
        .filter(|n| field(n, "type") == &Json::str("LawInstance"))
    {
        let payload = value(node);
        let role = match text(field(payload, "name")) {
            "CountCheck.nonnegative" => "required",
            "CountAudit.bounded" => "optional",
            other => panic!("{other}"),
        };
        assert_eq!(field(payload, "role"), &Json::str(role));
        let declaration = &checked.law().declarations[text(field(payload, "name"))];
        assert_eq!(span(field(payload, "occurrence")), declaration.span);
        let archsig::law::model::Signature::Law { body, params, .. } = &declaration.signature
        else {
            panic!("Law")
        };
        let expression = value(typed(&index, field(payload, "body"), "Expression"));
        assert_eq!(
            span(field(expression, "location")),
            checked.law().exprs[*body].span
        );
        let bindings = arr(field(payload, "bindings"));
        assert_eq!(bindings.len(), params.len());
        for (binding, parameter) in bindings.iter().zip(params) {
            assert_eq!(text(field(binding, "name")), parameter.name);
            assert_eq!(
                field(target(&index, field(binding, "value")), "type"),
                &parameter.ty.wire()
            );
        }
        assert!(
            !obj(payload).contains_key("guard"),
            "guard_true は原式ではない"
        );
    }
    audit_dag(&result);
}

#[test]
fn byte_and_checked_bundle_evaluation_have_the_same_semantics() {
    let bytes = run(sources(LAW, MAP), &ASKS);
    let mut control = quiet_control();
    let checked = check_inputs(sources(LAW, MAP), &mut control).unwrap();
    let prepared = prepare_checked_observed(checked, &ASKS, &mut control).unwrap();
    let result = evaluate_observed(prepared, &mut control).unwrap().wire();
    for key in [
        "status",
        "requests",
        "answers",
        "nodes",
        "issues",
        "declarations",
        "vocabularies",
        "inputs",
    ] {
        assert_eq!(field(&bytes, key), field(&result, key), "{key}");
    }
}

#[test]
fn renamed_vocabulary_reading_field_binding_and_large_z_use_the_common_path() {
    let renamed = |bytes: &[u8]| {
        String::from_utf8(bytes.to_vec())
            .unwrap()
            .replace("Counter", "Gauge")
            .replace("State", "Reading")
            .replace("count", "level")
    };
    let definitions = renamed(DEFINITIONS);
    let checked = check_definitions(&[("definition0", definitions.as_bytes())]).unwrap();
    let digest = &checked.vocabularies["Gauge"].digest;
    let old_digest = "sha256:388baddb5f87b80f4448ce9be21a4800c92a11001ab356936b14b6d5fb438a11";
    let law = renamed(LAW)
        .replace(old_digest, digest)
        .replace("CountCheck", "North")
        .replace("CountAudit", "South")
        .replace("s: Reading", "item: Reading")
        .replace("s.level", "item.level")
        .replace("<= 10", "<= 9223372036854775810");
    let map = renamed(MAP)
        .replace(old_digest, digest)
        .replace("\"value\": \"2\"", "\"value\": \"9223372036854775809\"")
        .replace("\"id\": \"v\"", "\"id\": \"snapshot\"")
        .replace("\"id\": \"s\"", "\"id\": \"record\"")
        .replace("\"subject\": \"s\"", "\"subject\": \"record\"")
        .replace("specification", "proposed");
    let result = run(
        InputSources::from_bytes(
            vec![definitions.into_bytes()],
            law.into_bytes(),
            map.into_bytes(),
        ),
        &[
            "read=evaluate(North.amount,item=@snapshot/record)",
            "low=check(North.nonnegative,item=@snapshot/record)",
            "high=check(South.bounded,item=@snapshot/record)",
        ],
    );
    assert_eq!(field(&result, "status"), &Json::str("complete"));
    let index = nodes(&result);
    assert_eq!(
        value(typed(
            &index,
            field(field(answer(&result, "read"), "outputs"), "value"),
            "Z"
        )),
        &Json::str("9223372036854775809")
    );
    for a in arr(field(&result, "answers")) {
        assert_eq!(field(a, "status"), &Json::str("established"));
        assert_eq!(
            field(field(a, "scope"), "snapshots"),
            &Json::Arr(vec![Json::str("snapshot")])
        );
        assert_eq!(
            field(field(a, "scope"), "modes"),
            &Json::Arr(vec![Json::str("proposed")])
        );
    }
    audit_dag(&result);
}

#[test]
fn bool_false_is_an_established_evaluation_value() {
    let law = String::from_utf8(LAW.to_vec()).unwrap().replace(
        "view amount",
        "view flag(s: State): Bool = false;\n  view amount",
    );
    let result = run(
        sources(law.as_bytes(), MAP),
        &["f=evaluate(CountCheck.flag,s=@v/s)"],
    );
    let a = answer(&result, "f");
    assert_eq!(field(a, "status"), &Json::str("established"));
    assert!(!obj(a).contains_key("claim"));
    assert_eq!(
        value(typed(
            &nodes(&result),
            field(field(a, "outputs"), "value"),
            "Bool"
        )),
        &Json::Bool(false)
    );
    audit_dag(&result);
}

#[test]
fn fact_support_resolves_to_the_actual_origin_and_source() {
    let map = String::from_utf8(MAP.to_vec()).unwrap()
        .replace("\"sources\": []", "\"sources\": [{\"id\":\"src\",\"uri\":\"urn:counter:fixture\",\"revision\":\"r1\",\"digest\":\"sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\"}]")
        .replace("\"locations\": []", "\"locations\": [{\"source\":\"src\",\"path\":\"counter.model\",\"span\":[3,8]}]");
    let checked = check_inputs(sources(LAW, map.as_bytes()), &mut quiet_control()).unwrap();
    let result = run(sources(LAW, map.as_bytes()), &ASKS);
    let mut saw_count = false;
    for node in arr(field(&result, "nodes")) {
        for fact in arr(field(node, "support")) {
            let snapshot = checked
                .archmap()
                .snapshots
                .iter()
                .find(|s| s.id == text(field(fact, "snapshot")))
                .unwrap();
            let subject = snapshot
                .subjects
                .iter()
                .find(|s| s.id == text(field(fact, "subject")))
                .unwrap();
            let origin = if let Some(atom) = obj(fact).get("atom") {
                let field_name = text(field(fact, "field"));
                let slot = &subject
                    .fields
                    .iter()
                    .find(|f| f.name == field_name)
                    .unwrap()
                    .slot;
                let archsig::archmap::Slot::Known {
                    atom: actual,
                    origin,
                    ..
                } = slot
                else {
                    panic!("原始事実である")
                };
                assert_eq!(actual, text(atom));
                saw_count = true;
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
            assert_eq!(origin.locations[0].path, "counter.model");
            assert_eq!(origin.locations[0].span, Some((3, 8)));
            let source = checked
                .archmap()
                .sources
                .iter()
                .find(|s| s.id == origin.locations[0].source)
                .unwrap();
            assert_eq!(source.uri, "urn:counter:fixture");
            assert_eq!(source.revision, "r1");
        }
    }
    assert!(saw_count, "値の支持は実在する count Atom へ戻る");
    audit_dag(&result);
}

#[test]
fn preparation_failures_retain_the_original_stage_and_have_no_evaluation() {
    let failure =
        evaluate_observed_bytes(sources(b"bad", MAP), &ASKS, &mut quiet_control()).unwrap_err();
    assert!(matches!(
        &failure,
        EvaluationFailure::Prepare(PrepareFailure::Inputs(_))
    ));
    let wire = failure.wire().unwrap();
    for key in [
        "declarations",
        "vocabularies",
        "requests",
        "answers",
        "nodes",
    ] {
        assert!(arr(field(&wire, key)).is_empty());
    }
    let failure =
        evaluate_observed_bytes(sources(LAW, b"bad"), &ASKS, &mut quiet_control()).unwrap_err();
    assert!(matches!(
        &failure,
        EvaluationFailure::Prepare(PrepareFailure::Inputs(_))
    ));
    let wire = failure.wire().unwrap();
    assert!(!arr(field(&wire, "declarations")).is_empty());
    assert!(!arr(field(&wire, "vocabularies")).is_empty());
    for key in ["requests", "answers", "nodes"] {
        assert!(arr(field(&wire, key)).is_empty());
    }
    let failure = evaluate_observed_bytes(
        sources(LAW, MAP),
        &["n=evaluate(CountCheck.amount)"],
        &mut quiet_control(),
    )
    .unwrap_err();
    assert!(matches!(
        &failure,
        EvaluationFailure::Prepare(PrepareFailure::Requests { .. })
    ));
    let wire = failure.wire().unwrap();
    assert!(!arr(field(&wire, "declarations")).is_empty());
    for key in ["answers", "nodes"] {
        assert!(arr(field(&wire, key)).is_empty());
    }
}

#[test]
fn known_bool_wildcard_match_keeps_counter_value_and_original_children() {
    let law = String::from_utf8(LAW.to_vec()).unwrap().replace(
        "view amount",
        "view conditional(s: State): Z = match true { _ => s.count; };\n  view amount",
    );
    let result = run(
        sources(law.as_bytes(), MAP),
        &["x=evaluate(CountCheck.conditional,s=@v/s)"],
    );
    audit_dag(&result);
    let a = answer(&result, "x");
    assert_eq!(field(a, "status"), &Json::str("established"));
    assert!(!obj(a).contains_key("claim"));
    let ns = nodes(&result);
    assert_eq!(
        value(typed(&ns, field(field(a, "outputs"), "value"), "Z")),
        &Json::str("2")
    );
    let e = typed(&ns, field(field(a, "outputs"), "evaluation"), "Evaluation");
    let parts = arr(field(value(e), "parts"));
    assert_eq!(parts.len(), 1);
    let at = span(field(&parts[0], "location"));
    assert_eq!(&law.as_bytes()[at.0..at.1], b"match true { _ => s.count; }");
    let children = arr(field(&parts[0], "children"));
    assert_eq!(children.len(), 2);
    for (child, original, ty, expected) in [
        (&children[0], b"true".as_slice(), "Bool", Json::Bool(true)),
        (&children[1], b"s.count".as_slice(), "Z", Json::str("2")),
    ] {
        let child = typed(&ns, child, "Evaluation");
        let part = &arr(field(value(child), "parts"))[0];
        let at = span(field(part, "location"));
        assert_eq!(&law.as_bytes()[at.0..at.1], original);
        assert_eq!(
            value(typed(&ns, field(value(child), "value"), ty)),
            &expected
        );
        for fact in arr(field(child, "support")) {
            assert!(arr(field(e, "support")).contains(fact));
        }
    }
}

#[test]
fn unimplemented_valid_quantification_and_answer_dependencies_are_not_results() {
    let law = String::from_utf8(LAW.to_vec()).unwrap().replace(
        "view amount",
        "view conditional(s: State): Z = match true { _ => s.count; };\n  view same(s: State): State = s;\n  view amount",
    );
    for asks in [
        vec!["x=check(CountCheck.nonnegative)"],
        vec![
            "a=evaluate(CountCheck.same,s=@v/s)",
            "b=evaluate(CountCheck.amount,s=$a.value)",
        ],
    ] {
        let failure =
            evaluate_observed_bytes(sources(law.as_bytes(), MAP), &asks, &mut quiet_control())
                .unwrap_err();
        assert!(
            matches!(&failure, EvaluationFailure::NotImplemented { .. }),
            "{failure:?}"
        );
        assert!(
            failure.wire().is_none(),
            "未実装を unsupported_algorithm/partial の結果へ変換しない"
        );
    }
}

fn expression_count(asks: &[&str]) -> usize {
    let count = Rc::new(Cell::new(0));
    let capture = count.clone();
    let mut control = Control::new(Limits::default(), move |point| {
        if point == Checkpoint::Expression {
            capture.set(capture.get() + 1);
        }
        Usage::default()
    });
    evaluate_observed_bytes(sources(LAW, MAP), asks, &mut control).unwrap();
    count.get()
}

fn interrupted_at_expression(
    asks: &[&str],
    stop_at: usize,
    usage: Usage,
    limits: Limits,
    first_complete: bool,
) -> Json {
    let calls = Rc::new(Cell::new(0));
    let capture = calls.clone();
    let expressions = Rc::new(Cell::new(0));
    let observed = expressions.clone();
    let mut control = Control::new(limits, move |point| {
        capture.set(capture.get() + 1);
        if point == Checkpoint::Expression {
            observed.set(observed.get() + 1);
            if observed.get() == stop_at {
                return usage;
            }
        }
        Usage::default()
    });
    let result = evaluate_observed_bytes(sources(LAW, MAP), asks, &mut control)
        .unwrap()
        .wire();
    assert_eq!(field(&result, "status"), &Json::str("interrupted"));
    assert_eq!(expressions.get(), stop_at, "停止後は新しい式を始めない");
    let original = control.stop_reason().unwrap().wire();
    for a in arr(field(&result, "answers"))
        .iter()
        .skip(usize::from(first_complete))
    {
        assert_eq!(field(a, "status"), &Json::str("undetermined"));
        let reason = arr(field(a, "reasons"))
            .iter()
            .find(|r| field(r, "code") == field(&original, "code"))
            .unwrap();
        assert_eq!(
            field(reason, "details"),
            field(&original, "details"),
            "未着手にも最初の停止理由を保持"
        );
    }
    if first_complete {
        let first = answer(&result, "n");
        assert_eq!(field(first, "status"), &Json::str("established"));
        assert_eq!(
            value(typed(
                &nodes(&result),
                field(field(first, "outputs"), "value"),
                "Z"
            )),
            &Json::str("2")
        );
    }
    let before = calls.get();
    assert!(control.checkpoint(Checkpoint::Expression).is_err());
    assert_eq!(calls.get(), before, "停止後はprobeを再実行しない");
    audit_dag(&result);
    result
}

#[test]
fn cancellation_before_the_first_expression_keeps_all_requests_undetermined() {
    interrupted_at_expression(
        &ASKS,
        1,
        Usage {
            signal: Some(Signal::Int),
            ..Usage::default()
        },
        Limits::default(),
        false,
    );
}

#[test]
fn time_budget_inside_the_first_evaluation_keeps_the_original_reason() {
    // 比較の左辺を確認した後、右辺/比較全体が未完了の位置で止める。
    // 単一の Dotted 式である amount の開始点停止とは異なる部分評価を検査する。
    let asks = [ASKS[1], ASKS[0], ASKS[2]];
    let count = expression_count(&asks[..1]);
    assert!(count > 2);
    let midway = count / 2;
    assert!(1 < midway && midway < count);
    let result = interrupted_at_expression(
        &asks,
        midway,
        Usage {
            elapsed_ms: 7,
            ..Usage::default()
        },
        Limits {
            time_ms: Some(7),
            memory_mib: None,
        },
        false,
    );
    let index = nodes(&result);
    let known = index
        .values()
        .find(|n| {
            field(n, "type") == &Json::str("Z")
                && field(n, "state") == &Json::str("value")
                && value(n) == &Json::str("2")
        })
        .expect("途中停止でも確認済みの左辺 count=2 を保持する");
    assert_eq!(field(field(known, "rule"), "kind"), &Json::str("atom"));
    assert!(
        index
            .values()
            .any(|n| field(n, "type") == &Json::str("Evaluation")
                && field(n, "state") == &Json::str("value")
                && obj(value(n)).get("value")
                    == Some(&Json::obj([("node", field(known, "id").clone())]))),
        "確認済み左辺の Evaluation も失わない"
    );
}

#[test]
fn memory_budget_after_the_first_answer_preserves_its_known_value() {
    let first = expression_count(&ASKS[..1]);
    interrupted_at_expression(
        &ASKS,
        first + 1,
        Usage {
            memory_mib: 1,
            ..Usage::default()
        },
        Limits {
            time_ms: None,
            memory_mib: Some(1),
        },
        true,
    );
}

// 公開 checkpoint の列から、先頭 amount の式終了直前を選ぶ。
// FiniteIteration の絶対数や node 数には固定した期待値を置かない。
fn missing_root_expression_finite_interval() -> (usize, usize) {
    let finite = Rc::new(Cell::new(0));
    let expression = Rc::new(Cell::new(0));
    let at_post = Rc::new(Cell::new(None));
    let at_start = Rc::new(Cell::new(None));
    let (seen_finite, seen_expression, captured, started) = (
        finite.clone(),
        expression.clone(),
        at_post.clone(),
        at_start.clone(),
    );
    let mut control = Control::new(Limits::default(), move |point| {
        if point == Checkpoint::FiniteIteration {
            seen_finite.set(seen_finite.get() + 1);
        }
        if point == Checkpoint::Expression {
            seen_expression.set(seen_expression.get() + 1);
            if seen_expression.get() == 1 {
                started.set(Some(seen_finite.get()));
            }
            if seen_expression.get() == 2 {
                captured.set(Some(seen_finite.get()));
            }
        }
        Usage::default()
    });
    let result = evaluate_observed_bytes(sources(LAW, &map_count(None)), &ASKS, &mut control)
        .unwrap()
        .wire();
    assert_eq!(field(&result, "status"), &Json::str("partial"));
    assert_eq!(
        field(field(answer(&result, "n"), "scope"), "domain"),
        &Json::str("all_completions")
    );
    let count = at_post
        .get()
        .expect("先頭 amount の Expression post がある");
    assert!(count > 1);
    (
        at_start
            .get()
            .expect("先頭 amount の Expression pre がある"),
        count,
    )
}

fn missing_scope_survives_finite_stop(offset: usize, limits: Limits, usage: Usage) {
    let stop_at = missing_root_expression_finite_interval().1 - offset;
    missing_scope_survives_at_finite(stop_at, limits, usage);
}

fn missing_scope_survives_at_finite(stop_at: usize, limits: Limits, usage: Usage) -> Json {
    let finite = Rc::new(Cell::new(0));
    let expression = Rc::new(Cell::new(0));
    let probes = Rc::new(Cell::new(0));
    let probes_at_stop = Rc::new(Cell::new(None));
    let (seen_finite, seen_expression, calls, stopped_calls) = (
        finite.clone(),
        expression.clone(),
        probes.clone(),
        probes_at_stop.clone(),
    );
    let mut control = Control::new(limits, move |point| {
        calls.set(calls.get() + 1);
        if point == Checkpoint::Expression {
            seen_expression.set(seen_expression.get() + 1);
        }
        if point == Checkpoint::FiniteIteration {
            seen_finite.set(seen_finite.get() + 1);
            if seen_finite.get() == stop_at {
                stopped_calls.set(Some(calls.get()));
                return usage;
            }
        }
        Usage::default()
    });
    let result = evaluate_observed_bytes(sources(LAW, &map_count(None)), &ASKS, &mut control)
        .unwrap()
        .wire();
    assert_eq!(field(&result, "status"), &Json::str("interrupted"));
    assert_eq!(finite.get(), stop_at);
    assert_eq!(expression.get(), 1, "root の式終了/完成登録より前で止まる");
    assert_eq!(
        Some(probes.get()),
        probes_at_stop.get(),
        "停止確認後に probe を再実行しない"
    );
    let stop = control.stop_reason().expect("元の停止理由を保持").wire();
    if let Some(signal) = usage.signal {
        assert_eq!(field(&stop, "code"), &Json::str("cancelled"));
        assert_eq!(
            field(field(&stop, "details"), "signal"),
            &Json::str(signal.wire())
        );
    } else {
        assert_eq!(field(&stop, "code"), &Json::str("budget_exhausted"));
        let (resource, limit, observed) = match limits.time_ms {
            Some(limit) => ("time_ms", limit, usage.elapsed_ms),
            None => ("memory_mib", limits.memory_mib.unwrap(), usage.memory_mib),
        };
        assert_eq!(
            field(&stop, "details"),
            &Json::obj([
                ("resource", Json::str(resource)),
                ("limit", Json::str(limit.to_string())),
                ("observed", Json::str(observed.to_string())),
            ])
        );
    }
    for a in arr(field(&result, "answers")) {
        assert_eq!(field(a, "status"), &Json::str("undetermined"));
        assert!(
            obj(field(a, "outputs")).is_empty(),
            "完成前rootと未着手Requestに通常値を補わない"
        );
        assert!(!obj(a).contains_key("claim"));
        let reason = arr(field(a, "reasons"))
            .iter()
            .find(|r| field(r, "code") == field(&stop, "code"))
            .unwrap();
        assert_eq!(field(reason, "details"), field(&stop, "details"));
        assert_eq!(field(reason, "request"), field(a, "id"));
    }
    let a = answer(&result, "n");
    let scope = field(a, "scope");
    assert_eq!(
        field(scope, "domain"),
        &Json::str("all_completions"),
        "既知の欠測を有限モデルへ戻さない"
    );
    assert_eq!(
        field(scope, "readings"),
        &Json::Arr(vec![Json::str("CountCheck")])
    );
    assert_eq!(field(scope, "snapshots"), &Json::Arr(vec![Json::str("v")]));
    assert_eq!(
        field(scope, "modes"),
        &Json::Arr(vec![Json::str("specification")])
    );
    let missing = arr(field(a, "reasons"))
        .iter()
        .find(|r| field(r, "code") == &Json::str("missing_observation"))
        .expect("root未完成でも認識済みの欠測理由は保持する");
    assert_eq!(
        field(missing, "missing"),
        &Json::Arr(vec![Json::obj([
            ("snapshot", Json::str("v")),
            ("subject", Json::str("s")),
            ("field", Json::str("Counter.State.count")),
        ])])
    );
    let index = nodes(&result);
    assert!(!arr(field(missing, "dependencies")).is_empty());
    for dependency in arr(field(missing, "dependencies")) {
        let expression = typed(&index, dependency, "Expression");
        assert_eq!(
            field(expression, "scope"),
            scope,
            "Answerと依存原式は同じ全補完域/由来を保持する"
        );
        let payload = value(expression);
        let (start, end) = span(field(payload, "location"));
        assert_eq!(&LAW[start..end], b"s.count");
        let binding = &arr(field(payload, "bindings"))[0];
        assert_eq!(field(binding, "name"), &Json::str("s"));
        let subject = target(&index, field(binding, "value"));
        assert_eq!(
            field(subject, "type"),
            &Json::Arr(vec![Json::str("Ref"), Json::str("Counter.State")])
        );
        assert_eq!(
            value(subject),
            &Json::Arr(vec![Json::str("v"), Json::str("s")])
        );
        assert!(
            arr(field(subject, "support")).contains(&Json::obj([
                ("snapshot", Json::str("v")),
                ("subject", Json::str("s")),
            ])),
            "実在するsubjectの由来を保持する"
        );
    }
    for node in index.values() {
        assert_ne!(
            field(node, "type"),
            &Json::str("Z"),
            "欠測の具体的補完値を作らない"
        );
        assert_ne!(
            field(node, "type"),
            &Json::str("Bool"),
            "未着手の比較を導出しない"
        );
        assert_eq!(
            field(field(node, "scope"), "readings"),
            &Json::Arr(vec![Json::str("CountCheck")])
        );
        if field(node, "type") == &Json::str("Evaluation") {
            let expression = value(typed(
                &index,
                field(value(node), "expression"),
                "Expression",
            ));
            let (start, end) = span(field(expression, "location"));
            if &LAW[start..end] == b"s.count" {
                assert!(
                    !obj(value(node)).contains_key("value"),
                    "欠測依存Evaluationを通常値として消費しない"
                );
            }
        }
    }
    let before = probes.get();
    assert!(control.checkpoint(Checkpoint::FiniteIteration).is_err());
    assert!(control.checkpoint(Checkpoint::Expression).is_err());
    assert_eq!(probes.get(), before);
    audit_dag(&result);
    result
}

#[test]
fn missing_scope_survives_time_stop_during_root_evaluation_push() {
    missing_scope_survives_finite_stop(
        1,
        Limits {
            time_ms: Some(13),
            memory_mib: None,
        },
        Usage {
            elapsed_ms: 13,
            ..Usage::default()
        },
    );
}

#[test]
fn missing_scope_survives_memory_stop_before_root_evaluation_push_completes() {
    missing_scope_survives_finite_stop(
        2,
        Limits {
            time_ms: None,
            memory_mib: Some(1),
        },
        Usage {
            memory_mib: 1,
            ..Usage::default()
        },
    );
}

#[test]
fn missing_scope_survives_sigterm_before_root_expression_completes() {
    missing_scope_survives_finite_stop(
        0,
        Limits::default(),
        Usage {
            signal: Some(Signal::Term),
            ..Usage::default()
        },
    );
}

fn reachable_nodes(index: &BTreeMap<&str, &Json>, roots: &[&Json]) -> BTreeSet<String> {
    let mut pending = vec![];
    for root in roots {
        visit_refs(root, &mut pending);
    }
    let mut reached = BTreeSet::new();
    while let Some(id) = pending.pop() {
        if reached.insert(id.clone()) {
            visit_refs(index[id.as_str()], &mut pending);
        }
    }
    reached
}

fn guarded_counter(count: &str, guard: &str) -> (InputSources, String) {
    let definitions = r#"{"format":"archsig.atom-definition/1","semantics":"archsig/0.6.0",
      "vocabularies":[{"semantics":"archsig/0.6.0","namespace":"Counter","version":"1",
      "dependencies":[],"declarations":[{"kind":"entity","name":"Counter.State",
      "meaning":"一つの状態。","parameters":[],"fields":[
        {"name":"count","type":"Z","meaning":"保持する件数。"},
        {"name":"enabled","type":"Bool","meaning":"この状態に条件を適用する。"}],"alignments":[]}]}]}"#;
    let checked = check_definitions(&[("definition0", definitions.as_bytes())]).unwrap();
    let digest = &checked.vocabularies["Counter"].digest;
    let law = format!(
        r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Guarded {{
  use vocabulary Counter version "1" digest "{digest}";
  law required bounded(s: State) when {guard}: s.count <= 10;
}}
"#
    );
    let map = format!(
        r#"{{"format":"archsig.archmap/2","semantics":"archsig/0.6.0",
      "vocabularies":[{{"namespace":"Counter","version":"1","digest":"{digest}"}}],
      "sources":[{{"id":"gates","uri":"urn:fixture:gate","revision":"gate-r1","digest":"sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"}}],
      "origins":[
        {{"id":"body","mode":"specification","method":"状態と件数を提示する。","locations":[],"note":"件数と適用条件の由来を区別する小さい仕様モデル。"}},
        {{"id":"gate","mode":"specification","method":"適用条件を別の由来で提示する。","locations":[{{"source":"gates","path":"gate.model","span":[1,5]}}]}}],
      "snapshots":[{{"id":"v","origin":"body",
        "subjects":[{{"id":"s","type":"Counter.State","origin":"body"}}],
        "atoms":[{{"id":"count","subject":"s","field":"Counter.State.count","value":"{count}","origin":"body"}},
                 {{"id":"enabled","subject":"s","field":"Counter.State.enabled","value":true,"origin":"gate"}}]}}]}}"#
    );
    (
        InputSources::from_bytes(
            vec![definitions.as_bytes().to_vec()],
            law.as_bytes().to_vec(),
            map.into_bytes(),
        ),
        law,
    )
}

fn guarded_answer_retains_applicability(count: &str, guard: &str, decision: &str) {
    let (sources, law) = guarded_counter(count, guard);
    let checked = check_inputs(sources.clone(), &mut quiet_control()).unwrap();
    let result = run(sources, &["bounded=check(Guarded.bounded,s=@v/s)"]);
    assert_eq!(field(&result, "status"), &Json::str("complete"));
    let a = answer(&result, "bounded");
    assert_eq!(field(a, "status"), &Json::str(decision));
    let index = nodes(&result);
    let reachable = reachable_nodes(
        &index,
        &[field(a, "outputs"), field(a, "claim"), field(a, "evidence")],
    );
    let returned_ref = field(field(a, "outputs"), "evaluation");
    let returned = typed(&index, returned_ref, "Evaluation");
    let returned_payload = value(returned);
    let body_expression = value(typed(
        &index,
        field(returned_payload, "expression"),
        "Expression",
    ));
    let (body_start, body_end) = span(field(body_expression, "location"));
    assert_eq!(&law.as_bytes()[body_start..body_end], b"s.count <= 10");
    assert_eq!(
        field(returned_payload, "applicability"),
        &Json::str("applicable")
    );
    assert_eq!(
        value(typed(&index, field(returned_payload, "value"), "Bool")),
        &Json::Bool(decision == "established")
    );
    let from_returned = reachable_nodes(&index, &[returned_ref]);
    let guard_start = law.find(&format!("when {guard}:")).unwrap() + "when ".len();
    let guard_span = (guard_start, guard_start + guard.len());
    let guard_expression = reachable
        .iter()
        .map(|id| index[id.as_str()])
        .find(|n| {
            field(n, "type") == &Json::str("Expression")
                && obj(value(n)).get("kind") == Some(&Json::str("source"))
                && span(field(value(n), "location")) == guard_span
        })
        .expect("結論から元guard Expressionへ辿れる");
    let guard_expression_ref = Json::obj([("node", field(guard_expression, "id").clone())]);
    let guard_evaluation = reachable
        .iter()
        .map(|id| index[id.as_str()])
        .find(|n| {
            field(n, "type") == &Json::str("Evaluation")
                && field(value(n), "expression") == &guard_expression_ref
        })
        .expect("guardの実Evaluationは結論の到達集合に含まれる");
    assert!(
        from_returned.contains(text(field(guard_evaluation, "id"))),
        "返却Evaluation.applicabilityの根拠からもguard実評価へ戻れる"
    );
    let guard_payload = value(guard_evaluation);
    assert!(arr(field(value(guard_expression), "parameters")).is_empty());
    assert_eq!(
        field(value(guard_expression), "bindings"),
        field(guard_payload, "bindings")
    );
    let true_ref = field(guard_payload, "value");
    assert_eq!(value(typed(&index, true_ref, "Bool")), &Json::Bool(true));
    assert!(from_returned.contains(text(field(true_ref, "node"))));
    assert_eq!(
        field(guard_payload, "bindings"),
        field(returned_payload, "bindings")
    );
    let binding = &arr(field(guard_payload, "bindings"))[0];
    assert_eq!(field(binding, "name"), &Json::str("s"));
    let subject = target(&index, field(binding, "value"));
    assert_eq!(
        field(subject, "type"),
        &Json::Arr(vec![Json::str("Ref"), Json::str("Counter.State")])
    );
    assert_eq!(
        value(subject),
        &Json::Arr(vec![Json::str("v"), Json::str("s")])
    );
    assert!(
        arr(field(guard_payload, "parts"))
            .iter()
            .any(|p| span(field(p, "location")) == guard_span
                && obj(p).get("value") == Some(true_ref))
    );
    let count_fact = Json::obj([
        ("snapshot", Json::str("v")),
        ("subject", Json::str("s")),
        ("field", Json::str("Counter.State.count")),
        ("atom", Json::str("count")),
    ]);
    let guard_fact = Json::obj([
        ("snapshot", Json::str("v")),
        ("subject", Json::str("s")),
        ("field", Json::str("Counter.State.enabled")),
        ("atom", Json::str("enabled")),
    ]);
    let explicit_field = guard == "s.enabled";
    assert_eq!(
        arr(field(guard_evaluation, "support")).contains(&guard_fact),
        explicit_field
    );
    let reached_nodes: Vec<_> = reachable.iter().map(|id| index[id.as_str()]).collect();
    for node in reached_nodes.iter().copied().filter(|n| {
        field(n, "type") == &Json::str("LawInstance")
            || field(n, "type") == &Json::str("Proposition")
            || field(n, "type") == &Json::str("Evidence")
    }) {
        let support = arr(field(node, "support"));
        assert!(
            support.contains(&count_fact),
            "結論/証拠はbodyの原始事実を保持する"
        );
        assert_eq!(
            support.contains(&guard_fact),
            explicit_field,
            "適用guardの支持を結論/証拠へ合流する"
        );
    }
    assert!(arr(field(returned, "support")).contains(&count_fact));
    assert_eq!(
        arr(field(returned, "support")).contains(&guard_fact),
        explicit_field
    );
    let instance = reached_nodes
        .iter()
        .copied()
        .find(|n| field(n, "type") == &Json::str("LawInstance"))
        .unwrap();
    assert_eq!(field(value(instance), "guard"), &guard_expression_ref);
    for item in [a, returned, guard_evaluation, instance] {
        let scope = field(item, "scope");
        assert_eq!(field(scope, "domain"), &Json::str("finite_model"));
        assert_eq!(
            field(scope, "readings"),
            &Json::Arr(vec![Json::str("Guarded")])
        );
        assert_eq!(field(scope, "snapshots"), &Json::Arr(vec![Json::str("v")]));
        assert_eq!(
            field(scope, "modes"),
            &Json::Arr(vec![Json::str("specification")])
        );
    }
    if explicit_field {
        let subject = &checked.archmap().snapshots[0].subjects[0];
        let field = subject
            .fields
            .iter()
            .find(|f| f.name == "Counter.State.enabled")
            .unwrap();
        let archsig::archmap::Slot::Known { atom, origin, .. } = &field.slot else {
            panic!("guardは観測済み")
        };
        assert_eq!(atom, "enabled");
        assert_eq!(origin, "gate");
        let origin = checked
            .archmap()
            .origins
            .iter()
            .find(|o| &o.id == origin)
            .unwrap();
        assert_eq!(origin.locations[0].path, "gate.model");
        assert_eq!(origin.locations[0].span, Some((1, 5)));
        assert_eq!(origin.mode, archsig::archmap::Mode::Specification);
        let body_slot = &subject
            .fields
            .iter()
            .find(|f| f.name == "Counter.State.count")
            .unwrap()
            .slot;
        let archsig::archmap::Slot::Known {
            origin: body_origin,
            ..
        } = body_slot
        else {
            panic!("bodyは観測済み")
        };
        assert_eq!(body_origin, "body");
        assert_ne!(body_origin, &origin.id);
        let source = checked
            .archmap()
            .sources
            .iter()
            .find(|s| s.id == origin.locations[0].source)
            .unwrap();
        assert_eq!(source.uri, "urn:fixture:gate");
        assert_eq!(source.revision, "gate-r1");
    }
    if decision == "refuted" {
        let counterexample = reached_nodes
            .iter()
            .copied()
            .find(|n| {
                field(n, "type") == &Json::str("Evidence")
                    && field(value(n), "kind") == &Json::str("counterexample")
            })
            .expect("反例は結論から到達可能");
        let data = field(value(counterexample), "data");
        assert_eq!(
            value(typed(&index, field(data, "left"), "Z")),
            &Json::str(count)
        );
        assert_eq!(
            value(typed(&index, field(data, "right"), "Z")),
            &Json::str("10")
        );
        assert!(arr(field(data, "facts")).contains(&count_fact));
        assert_eq!(
            arr(field(data, "facts")).contains(&guard_fact),
            explicit_field
        );
    }
    audit_dag(&result);
}

#[test]
fn true_field_guard_refutation_keeps_applicability_reachable_from_the_answer() {
    guarded_answer_retains_applicability("12", "s.enabled", "refuted");
}

#[test]
fn true_field_guard_establishment_keeps_guard_and_body_support() {
    guarded_answer_retains_applicability("2", "s.enabled", "established");
}

#[test]
fn literal_true_guard_keeps_its_evaluation_without_invented_atom_support() {
    guarded_answer_retains_applicability("2", "true", "established");
}

#[test]
fn true_field_guard_with_missing_body_keeps_applicability_and_all_completions() {
    let (original, law) = guarded_counter("2", "s.enabled");
    let map = String::from_utf8(original.archmap().bytes().to_vec()).unwrap()
        .replace(r#"{"id":"count","subject":"s","field":"Counter.State.count","value":"2","origin":"body"},"#, "")
        .replace("specification", "observed")
        .replace(r#""locations":[]"#, r#""locations":[{"source":"gates","path":"count.model","span":[6,9]}]"#);
    let inputs = InputSources::from_bytes(
        original
            .definitions()
            .iter()
            .map(|d| d.bytes().to_vec())
            .collect(),
        original.law().bytes().to_vec(),
        map.into_bytes(),
    );
    let checked = check_inputs(inputs.clone(), &mut quiet_control()).unwrap();
    let subject = &checked.archmap().snapshots[0].subjects[0];
    assert_eq!(subject.id, "s");
    assert!(matches!(
        &subject
            .fields
            .iter()
            .find(|f| f.name == "Counter.State.count")
            .unwrap()
            .slot,
        archsig::archmap::Slot::Missing
    ));
    let result = run(inputs, &["bounded=check(Guarded.bounded,s=@v/s)"]);
    assert_eq!(field(&result, "status"), &Json::str("partial"));
    let a = answer(&result, "bounded");
    assert_eq!(field(a, "status"), &Json::str("undetermined"));
    let index = nodes(&result);
    let evaluation_ref = field(field(a, "outputs"), "evaluation");
    let evaluation = typed(&index, evaluation_ref, "Evaluation");
    let payload = value(evaluation);
    assert_eq!(field(payload, "applicability"), &Json::str("applicable"));
    assert!(
        !obj(payload).contains_key("value"),
        "適用guardがtrueでも欠測bodyへBool値を補わない"
    );
    let proposition = typed(&index, field(a, "claim"), "Proposition");
    assert_eq!(
        field(field(proposition, "judgment"), "status"),
        &Json::str("undetermined")
    );
    assert_eq!(field(field(a, "outputs"), "proposition"), field(a, "claim"));
    let reached = reachable_nodes(
        &index,
        &[field(a, "outputs"), field(a, "claim"), field(a, "evidence")],
    );
    let from_evaluation = reachable_nodes(&index, &[evaluation_ref]);
    let guard_span_start = law.find("when s.enabled:").unwrap() + "when ".len();
    let guard_span = (guard_span_start, guard_span_start + "s.enabled".len());
    let guard_evaluation = reached
        .iter()
        .map(|id| index[id.as_str()])
        .find(|node| {
            if field(node, "type") != &Json::str("Evaluation") {
                return false;
            }
            let expression = value(typed(
                &index,
                field(value(node), "expression"),
                "Expression",
            ));
            span(field(expression, "location")) == guard_span
        })
        .expect("Answerから確認済みguard Evaluationへ到達する");
    assert!(
        from_evaluation.contains(text(field(guard_evaluation, "id"))),
        "返却Evaluationだけから適用根拠へ到達する"
    );
    assert_eq!(
        value(typed(
            &index,
            field(value(guard_evaluation), "value"),
            "Bool"
        )),
        &Json::Bool(true)
    );
    let guard_fact = Json::obj([
        ("snapshot", Json::str("v")),
        ("subject", Json::str("s")),
        ("field", Json::str("Counter.State.enabled")),
        ("atom", Json::str("enabled")),
    ]);
    assert!(arr(field(guard_evaluation, "support")).contains(&guard_fact));
    assert!(arr(field(evaluation, "support")).contains(&guard_fact));
    let missing_fact = Json::obj([
        ("snapshot", Json::str("v")),
        ("subject", Json::str("s")),
        ("field", Json::str("Counter.State.count")),
    ]);
    for item in [a, evaluation] {
        let missing = arr(field(item, "reasons"))
            .iter()
            .find(|r| field(r, "code") == &Json::str("missing_observation"))
            .unwrap();
        assert_eq!(
            field(missing, "missing"),
            &Json::Arr(vec![missing_fact.clone()])
        );
        assert!(!arr(field(missing, "dependencies")).is_empty());
        for dependency in arr(field(missing, "dependencies")) {
            assert!(from_evaluation.contains(text(field(dependency, "node"))));
            let expression = typed(&index, dependency, "Expression");
            let (start, end) = span(field(value(expression), "location"));
            assert_eq!(&law.as_bytes()[start..end], b"s.count");
            assert_eq!(
                field(field(expression, "scope"), "domain"),
                &Json::str("all_completions")
            );
        }
        let scope = field(item, "scope");
        assert_eq!(field(scope, "domain"), &Json::str("all_completions"));
        assert_eq!(
            field(scope, "modes"),
            &Json::Arr(vec![Json::str("observed")])
        );
        assert_eq!(field(scope, "snapshots"), &Json::Arr(vec![Json::str("v")]));
        assert_eq!(
            field(scope, "readings"),
            &Json::Arr(vec![Json::str("Guarded")])
        );
    }
    assert_eq!(
        field(field(guard_evaluation, "scope"), "modes"),
        &Json::Arr(vec![Json::str("observed")])
    );
    for id in &reached {
        let node = index[id.as_str()];
        assert!(
            !arr(field(node, "support"))
                .iter()
                .any(|f| obj(f).get("field") == Some(&Json::str("Counter.State.count"))),
            "欠測slotを観測済みsupportへ昇格しない"
        );
        if field(node, "type") == &Json::str("Evidence") {
            assert_ne!(field(value(node), "kind"), &Json::str("counterexample"));
        }
    }
    audit_dag(&result);
}

fn missing_source_expression_id(result: &Json) -> Option<String> {
    arr(field(result, "nodes")).iter().find_map(|node| {
        if field(node, "type") != &Json::str("Expression")
            || field(field(node, "scope"), "domain") != &Json::str("all_completions")
        {
            return None;
        }
        let (start, end) = span(field(value(node), "location"));
        (&LAW[start..end] == b"s.count").then(|| text(field(node, "id")).to_owned())
    })
}

fn missing_finite_probe(stop_at: usize) -> Json {
    let mut finite = 0;
    let calls = Rc::new(Cell::new(0));
    let stopped_calls = Rc::new(Cell::new(None));
    let (seen_calls, captured_stop) = (calls.clone(), stopped_calls.clone());
    let mut control = Control::new(
        Limits {
            time_ms: Some(1),
            memory_mib: None,
        },
        move |point| {
            seen_calls.set(seen_calls.get() + 1);
            if point == Checkpoint::FiniteIteration {
                finite += 1;
                if finite == stop_at {
                    captured_stop.set(Some(seen_calls.get()));
                    return Usage {
                        elapsed_ms: 1,
                        ..Usage::default()
                    };
                }
            }
            Usage::default()
        },
    );
    let result = evaluate_observed_bytes(sources(LAW, &map_count(None)), &ASKS, &mut control)
        .unwrap()
        .wire();
    assert_eq!(
        Some(calls.get()),
        stopped_calls.get(),
        "停止後のprobe回数は凍結する"
    );
    let before = calls.get();
    assert!(control.checkpoint(Checkpoint::FiniteIteration).is_err());
    assert!(control.checkpoint(Checkpoint::Expression).is_err());
    assert_eq!(calls.get(), before);
    result
}

fn first_missing_source_expression_post_stop() -> (usize, usize) {
    let (start, end) = missing_root_expression_finite_interval();
    assert!(
        start < end && end - start <= 4096,
        "小さい第一式区間だけを対象にする"
    );
    // 挿入済みsource Expressionの存在はこの区間で単調。全停止点の走査はしない。
    let (mut low, mut high) = (start + 1, end);
    let mut probes = 0;
    while low < high {
        assert!(probes < 12, "小さい上限付き二分探索");
        probes += 1;
        let middle = low + (high - low) / 2;
        if missing_source_expression_id(&missing_finite_probe(middle)).is_some() {
            high = middle;
        } else {
            low = middle + 1;
        }
    }
    (low, end)
}

#[test]
fn missing_reason_survives_the_first_source_expression_post_stop() {
    let (low, _) = first_missing_source_expression_post_stop();
    let witness = missing_finite_probe(low);
    let expression =
        missing_source_expression_id(&witness).expect("欠測source Expression挿入直後を選ぶ");
    assert!(
        !arr(field(&witness, "nodes"))
            .iter()
            .any(|n| field(n, "type") == &Json::str("Evaluation")
                && field(value(n), "expression") == &Json::obj([("node", Json::str(&expression))])),
        "root Evaluationはまだ生成されていない"
    );
    for (limits, usage) in [
        (
            Limits {
                time_ms: Some(13),
                memory_mib: None,
            },
            Usage {
                elapsed_ms: 13,
                ..Usage::default()
            },
        ),
        (
            Limits {
                time_ms: None,
                memory_mib: Some(1),
            },
            Usage {
                memory_mib: 1,
                ..Usage::default()
            },
        ),
        (
            Limits::default(),
            Usage {
                signal: Some(Signal::Term),
                ..Usage::default()
            },
        ),
    ] {
        let result = missing_scope_survives_at_finite(low, limits, usage);
        let expression = missing_source_expression_id(&result).unwrap();
        assert!(
            !arr(field(&result, "nodes")).iter().any(|n| field(n, "type")
                == &Json::str("Evaluation")
                && field(value(n), "expression") == &Json::obj([("node", Json::str(&expression))]))
        );
    }
}

#[test]
fn missing_field_through_a_cross_snapshot_reference_keeps_target_scope() {
    let definitions = r#"{"format":"archsig.atom-definition/1","semantics":"archsig/0.6.0",
      "vocabularies":[{"semantics":"archsig/0.6.0","namespace":"Counter","version":"1",
      "dependencies":[],"declarations":[{"kind":"entity","name":"Counter.State","meaning":"参照先を持つ状態。",
      "parameters":[],"fields":[{"name":"count","type":"Z","meaning":"保持する件数。"},
      {"name":"next","type":["Ref","Counter.State"],"meaning":"次の状態。"}],"alignments":[]}]}]}"#;
    let checked_definitions =
        check_definitions(&[("definition0", definitions.as_bytes())]).unwrap();
    let digest = &checked_definitions.vocabularies["Counter"].digest;
    let law = format!(
        r#"law "archsig.law/2" semantics "archsig/0.6.0";
reading Follow {{
  use vocabulary Counter version "1" digest "{digest}";
  view amount(s: State): Z = (s.next).count;
}}
"#
    );
    let map = format!(
        r#"{{"format":"archsig.archmap/2","semantics":"archsig/0.6.0",
      "vocabularies":[{{"namespace":"Counter","version":"1","digest":"{digest}"}}],
      "sources":[{{"id":"source","uri":"urn:fixture:reference","revision":"r1","digest":"sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"}}],
      "origins":[{{"id":"observed","mode":"observed","method":"参照を観測する。","locations":[{{"source":"source","path":"state.model","span":[0,4]}}]}},
                 {{"id":"target","mode":"specification","method":"参照先の存在を提示する。","locations":[],"note":"件数は提示しない。"}}],
      "snapshots":[{{"id":"v","origin":"observed","subjects":[{{"id":"s","type":"Counter.State","origin":"observed"}}],
        "atoms":[{{"id":"next","subject":"s","field":"Counter.State.next","value":["w","t"],"origin":"observed"}}]}},
        {{"id":"w","origin":"target","subjects":[{{"id":"t","type":"Counter.State","origin":"target"}}],"atoms":[]}}]}}"#
    );
    let inputs = InputSources::from_bytes(
        vec![definitions.as_bytes().to_vec()],
        law.as_bytes().to_vec(),
        map.into_bytes(),
    );
    let checked = check_inputs(inputs.clone(), &mut quiet_control()).unwrap();
    let target_subject = &checked
        .archmap()
        .snapshots
        .iter()
        .find(|v| v.id == "w")
        .unwrap()
        .subjects[0];
    assert_eq!(target_subject.id, "t");
    assert!(matches!(
        &target_subject
            .fields
            .iter()
            .find(|f| f.name == "Counter.State.count")
            .unwrap()
            .slot,
        archsig::archmap::Slot::Missing
    ));
    let result = run(inputs, &["n=evaluate(Follow.amount,s=@v/s)"]);
    assert_eq!(field(&result, "status"), &Json::str("partial"));
    let a = answer(&result, "n");
    assert_eq!(field(a, "status"), &Json::str("undetermined"));
    let index = nodes(&result);
    let evaluation_ref = field(field(a, "outputs"), "evaluation");
    let evaluation = typed(&index, evaluation_ref, "Evaluation");
    assert!(!obj(value(evaluation)).contains_key("value"));
    assert!(!obj(field(a, "outputs")).contains_key("value"));
    let missing_fact = Json::obj([
        ("snapshot", Json::str("w")),
        ("subject", Json::str("t")),
        ("field", Json::str("Counter.State.count")),
    ]);
    let reached = reachable_nodes(&index, &[evaluation_ref]);
    for item in [a, evaluation] {
        let scope = field(item, "scope");
        assert_eq!(field(scope, "domain"), &Json::str("all_completions"));
        assert_eq!(
            field(scope, "snapshots"),
            &Json::Arr(vec![Json::str("v"), Json::str("w")])
        );
        assert_eq!(
            field(scope, "modes"),
            &Json::Arr(vec![Json::str("observed"), Json::str("specification")])
        );
        let reason = arr(field(item, "reasons"))
            .iter()
            .find(|r| field(r, "code") == &Json::str("missing_observation"))
            .unwrap();
        assert_eq!(
            field(reason, "missing"),
            &Json::Arr(vec![missing_fact.clone()])
        );
        assert!(!arr(field(reason, "dependencies")).is_empty());
        for reference in arr(field(reason, "dependencies")) {
            assert!(reached.contains(text(field(reference, "node"))));
            let expression = typed(&index, reference, "Expression");
            let (start, end) = span(field(value(expression), "location"));
            assert_eq!(&law.as_bytes()[start..end], b"(s.next).count");
            assert_eq!(field(expression, "scope"), scope);
        }
    }
    let next_fact = Json::obj([
        ("snapshot", Json::str("v")),
        ("subject", Json::str("s")),
        ("field", Json::str("Counter.State.next")),
        ("atom", Json::str("next")),
    ]);
    assert!(
        reached
            .iter()
            .map(|id| index[id.as_str()])
            .any(|n| field(n, "type")
                == &Json::Arr(vec![Json::str("Ref"), Json::str("Counter.State")])
                && value(n) == &Json::Arr(vec![Json::str("w"), Json::str("t")])
                && arr(field(n, "support")).contains(&next_fact)),
        "既知next Atomから実在する別snapshotのtへ辿る"
    );
    assert!(arr(field(evaluation, "support")).contains(&next_fact));
    assert!(
        !arr(field(evaluation, "support"))
            .iter()
            .any(|f| obj(f).get("field") == Some(&Json::str("Counter.State.count")))
    );
    audit_dag(&result);
}

fn collect_published_missing<'a>(wire: &'a Json, reasons: &mut Vec<&'a Json>) {
    match wire {
        Json::Obj(fields) => {
            if fields.get("code") == Some(&Json::str("missing_observation")) {
                reasons.push(wire);
            }
            for value in fields.values() {
                collect_published_missing(value, reasons);
            }
        }
        Json::Arr(values) => {
            for value in values {
                collect_published_missing(value, reasons);
            }
        }
        _ => {}
    }
}

#[test]
fn missing_source_and_canonical_reason_commit_atomically_before_and_after_stop() {
    let (commit, end) = first_missing_source_expression_post_stop();
    assert!(0 < commit && commit < end);
    let missing_fact = Json::obj([
        ("snapshot", Json::str("v")),
        ("subject", Json::str("s")),
        ("field", Json::str("Counter.State.count")),
    ]);
    let subject_fact = Json::obj([("snapshot", Json::str("v")), ("subject", Json::str("s"))]);
    // 第一式内のcommit直前・直後と二つの後続点だけ。全checkpointを走査しない。
    for stop_at in BTreeSet::from([commit - 1, commit, commit + 1, end]) {
        let result = missing_finite_probe(stop_at);
        assert_eq!(field(&result, "status"), &Json::str("interrupted"));
        let a = answer(&result, "n");
        let scope = field(a, "scope");
        assert_eq!(
            field(scope, "domain"),
            &Json::str("all_completions"),
            "認識済み欠測のscopeはcommit前でも保持する"
        );
        assert_eq!(
            field(scope, "readings"),
            &Json::Arr(vec![Json::str("CountCheck")])
        );
        assert_eq!(field(scope, "snapshots"), &Json::Arr(vec![Json::str("v")]));
        assert_eq!(
            field(scope, "modes"),
            &Json::Arr(vec![Json::str("specification")])
        );
        let index = nodes(&result);
        assert!(
            index.values().any(|n| field(n, "type")
                == &Json::Arr(vec![Json::str("Ref"), Json::str("Counter.State")])
                && value(n) == &Json::Arr(vec![Json::str("v"), Json::str("s")])
                && arr(field(n, "support")).contains(&subject_fact)),
            "欠測の実subject存在事実を失わない"
        );
        let source = missing_source_expression_id(&result);
        assert_eq!(
            source.is_some(),
            stop_at >= commit,
            "選択した最初のSource挿入点を跨ぐ"
        );
        let mut published = vec![];
        collect_published_missing(&result, &mut published);
        let has_published = !published.is_empty();
        for reason in published {
            assert_eq!(field(reason, "request"), &Json::str("n"));
            assert_eq!(
                field(reason, "missing"),
                &Json::Arr(vec![missing_fact.clone()])
            );
            let dependencies = arr(field(reason, "dependencies"));
            assert!(
                !dependencies.is_empty(),
                "公開済みの全Missing理由は実在する元式Refを持つ"
            );
            for reference in dependencies {
                let expression = typed(&index, reference, "Expression");
                assert_eq!(text(field(expression, "id")), source.as_deref().unwrap());
                assert_eq!(field(expression, "scope"), scope);
                let payload = value(expression);
                assert_eq!(field(payload, "kind"), &Json::str("source"));
                let (start, end) = span(field(payload, "location"));
                assert_eq!(&LAW[start..end], b"s.count");
                assert_eq!(span(field(reason, "location")), (start, end));
                let binding = &arr(field(payload, "bindings"))[0];
                assert_eq!(field(binding, "name"), &Json::str("s"));
                assert_eq!(
                    value(target(&index, field(binding, "value"))),
                    &Json::Arr(vec![Json::str("v"), Json::str("s")])
                );
            }
        }
        // Source未挿入のPendingはcanonical理由と区別する。空dependenciesでの公開は許さない。
        assert_eq!(
            has_published,
            source.is_some(),
            "Sourceとcanonical Missingを同時に公開し、以後の停止で理由を消さない"
        );
        for container in [field(a, "reasons"), field(&result, "issues")] {
            let found = arr(container)
                .iter()
                .any(|r| field(r, "code") == &Json::str("missing_observation"));
            assert_eq!(
                found,
                source.is_some(),
                "Answerとissuesの双方へ同じcanonical理由を保持する"
            );
        }
        for a in arr(field(&result, "answers")) {
            assert_eq!(field(a, "status"), &Json::str("undetermined"));
            assert!(obj(field(a, "outputs")).is_empty());
            let stopped = arr(field(a, "reasons"))
                .iter()
                .find(|r| field(r, "code") == &Json::str("budget_exhausted"))
                .unwrap();
            assert_eq!(
                field(stopped, "details"),
                &Json::obj([
                    ("resource", Json::str("time_ms")),
                    ("limit", Json::str("1")),
                    ("observed", Json::str("1")),
                ])
            );
        }
        assert!(
            index
                .values()
                .all(|n| field(n, "type") != &Json::str("Z")
                    && field(n, "type") != &Json::str("Bool")),
            "保留中の欠測を通常値や後続の判断へ置換しない"
        );
        audit_dag(&result);
    }
}
