//! 未使用情報の保持、選択した問いだけの評価、全入力の静的検査。
use archsig::{
    canonical::{Json, sha256_digest},
    definition::check_definitions,
    json::{JNode, JValue},
    law::{ast::ExprKind, model::Signature},
    observed::{
        EvaluationFailure, PrepareFailure,
        control::Control,
        evaluate_observed, evaluate_observed_bytes,
        input::{CheckedInputs, InputSources, InputStatus},
        prepare_observed,
    },
    result::{declaration_wire, location_wire, primitive_declarations_wire},
};
use std::collections::BTreeMap;

const COUNTER: &[u8] = include_bytes!("fixtures/counter.atoms.json");
const LIBRARY: &[u8] = include_bytes!("fixtures/counter-library.atoms.json");
const EXTRAS: &[u8] = include_bytes!("fixtures/extras.atoms.json");
const LAW: &str = include_str!("fixtures/counter.law");
const MAP: &str = include_str!("fixtures/counter.archmap.json");
// 要求順も保つ。宣言名の順や reading の順へ並べ替えない。
const ASKS: [&str; 3] = [
    "audit=check(CountAudit.bounded,s=@v/s)",
    "n=evaluate(CountCheck.amount,s=@v/s)",
    "ok=check(CountCheck.nonnegative,s=@v/s)",
];

fn obj(j: &Json) -> &BTreeMap<String, Json> {
    let Json::Obj(fields) = j else {
        panic!("object: {j:?}")
    };
    fields
}
fn arr(j: &Json) -> &[Json] {
    let Json::Arr(items) = j else {
        panic!("array: {j:?}")
    };
    items
}
fn text(j: &Json) -> &str {
    let Json::Str(s) = j else {
        panic!("string: {j:?}")
    };
    s
}
fn get<'a>(j: &'a Json, key: &str) -> &'a Json {
    &obj(j)[key]
}
fn named<'a>(j: &'a Json, table: &str, key: &str, name: &str) -> &'a Json {
    arr(get(j, table))
        .iter()
        .find(|item| text(get(item, key)) == name)
        .unwrap()
}
fn span(j: &Json) -> (usize, usize) {
    let pair = arr(get(j, "span"));
    let [Json::Nat(start), Json::Nat(end)] = pair else {
        panic!("span")
    };
    (*start as usize, *end as usize)
}
fn fixture_json(bytes: &[u8]) -> Json {
    fn convert(node: &JNode) -> Json {
        match &node.value {
            JValue::Str(s) => Json::str(s),
            JValue::Bool(b) => Json::Bool(*b),
            JValue::Num(n) => Json::Nat(n.parse().unwrap()),
            JValue::Arr(items) => Json::Arr(items.iter().map(convert).collect()),
            JValue::Obj(fields) => Json::Obj(
                fields
                    .iter()
                    .map(|(k, v)| (k.clone(), convert(v)))
                    .collect(),
            ),
            JValue::Null => panic!("この小さい入力に null はない"),
        }
    }
    convert(&archsig::json::parse(bytes).unwrap())
}
fn pointer<'a>(root: &'a Json, path: &str) -> &'a Json {
    path.split('/').skip(1).fold(root, |node, part| match node {
        Json::Obj(fields) => &fields[part],
        Json::Arr(items) => &items[part.parse::<usize>().unwrap()],
        _ => panic!("JSON Pointer: {path}"),
    })
}
fn map_count(count: Option<&str>) -> Vec<u8> {
    match count {
        Some(n) => MAP.replace("\"value\": \"2\"", &format!("\"value\": \"{n}\"")).into_bytes(),
        None => MAP.replace("{\"id\": \"count\", \"subject\": \"s\", \"field\": \"Counter.State.count\", \"value\": \"2\", \"origin\": \"model\"}", "").into_bytes(),
    }
}
fn sources(definitions: Vec<Vec<u8>>, script: &str, map: &[u8]) -> InputSources {
    InputSources::from_bytes(definitions, script.as_bytes().to_vec(), map.to_vec())
}
fn extended_law() -> String {
    let definitions = check_definitions(&[("definition0", LIBRARY)]).unwrap();
    let import = format!(
        "use vocabulary Extras version \"1\" digest \"{}\";",
        definitions.vocabularies["Extras"].digest
    );
    let counter_import = format!(
        "use vocabulary Counter version \"1\" digest \"{}\";",
        definitions.vocabularies["Counter"].digest
    );
    // import と alias は Counter の式から参照しない。spare の型に必要な subject も観測しない。
    let script = LAW.replace(
        "reading CountCheck {",
        &format!("reading CountCheck {{\n  {import}\n  use Spare as S;"),
    );
    format!(
        "{script}\nreading Spare {{\n  {import}\n  {counter_import}\n  view untouched(s: State): Z = match s.count {{ _ => 7; }};\n  view caption(note: Note): Text = note.text;\n  law optional spare(n: Z): n >= 0;\n}}\n"
    )
}

fn original<'a>(sources: &'a InputSources, id: &str) -> &'a [u8] {
    match id {
        "law" => sources.law().bytes(),
        "archmap" => sources.archmap().bytes(),
        _ => sources
            .definitions()
            .iter()
            .find(|input| input.id() == id)
            .unwrap()
            .bytes(),
    }
}

fn retained_metadata(checked: &CheckedInputs, result: &Json) {
    let has_extras = checked.sources().definitions().iter().any(|input| {
        std::str::from_utf8(input.bytes())
            .unwrap()
            .contains("Extras.Note")
    });
    assert_eq!(
        checked
            .definitions()
            .vocabularies
            .keys()
            .map(String::as_str)
            .collect::<Vec<_>>(),
        if has_extras {
            vec!["Counter", "Extras"]
        } else {
            vec!["Counter"]
        }
    );
    assert!(
        checked
            .definitions()
            .declarations
            .contains_key("Counter.State")
    );
    assert_eq!(
        checked
            .definitions()
            .declarations
            .contains_key("Extras.Note"),
        has_extras
    );
    let metadata = checked.metadata_wire();
    for key in ["inputs", "declarations", "vocabularies"] {
        assert_eq!(get(result, key), get(&metadata, key));
    }
    let mut expected_ids = checked
        .sources()
        .definitions()
        .iter()
        .map(|i| i.id())
        .collect::<Vec<_>>();
    expected_ids.extend(["law", "archmap"]);
    expected_ids.sort();
    assert_eq!(
        checked
            .inputs()
            .iter()
            .map(|i| i.id.as_str())
            .collect::<Vec<_>>(),
        expected_ids
    );
    for input in checked.inputs() {
        let bytes = original(checked.sources(), &input.id);
        assert_eq!(input.bytes_digest, Some(sha256_digest(bytes)));
        assert!(input.model_digest.is_some());
        assert!(input.path.is_none());
        let row = named(result, "inputs", "id", &input.id);
        assert_eq!(get(row, "bytes_digest"), &Json::str(sha256_digest(bytes)));
        assert_eq!(
            get(row, "model_digest"),
            &Json::str(input.model_digest.as_ref().unwrap())
        );
        assert!(input.read);
        assert_eq!(get(row, "state"), &Json::str("read"));
        assert_eq!(
            get(row, "kind"),
            &Json::str(if input.id.starts_with("definition") {
                "atom_definition"
            } else {
                &input.id
            })
        );
    }
    assert_eq!(checked.definitions(), &checked.law().definitions);
    for vocabulary in checked.definitions().vocabularies.values() {
        let row = arr(get(result, "vocabularies"))
            .iter()
            .find(|row| get(get(row, "manifest"), "namespace") == &Json::str(&vocabulary.namespace))
            .unwrap();
        assert_eq!(get(row, "manifest"), &vocabulary.manifest);
        assert_eq!(
            get(row, "digest"),
            &Json::str(sha256_digest(vocabulary.manifest.canonical().as_bytes()))
        );
        let location = location_wire(&vocabulary.location);
        assert_eq!(get(row, "location"), &location);
        let source = fixture_json(original(checked.sources(), text(get(&location, "input"))));
        let raw = pointer(&source, text(get(&location, "pointer")));
        assert_eq!(
            raw, &vocabulary.manifest,
            "元の語彙と manifest を対応させる"
        );
        for dependency in &vocabulary.dependencies {
            assert_eq!(
                get(&vocabulary.manifest, "dependencies"),
                &Json::Arr(vec![dependency.wire()])
            );
            let location = location_wire(&dependency.location);
            let source = fixture_json(original(checked.sources(), text(get(&location, "input"))));
            assert_eq!(
                pointer(&source, text(get(&location, "pointer"))),
                &dependency.wire()
            );
            let target = &checked.definitions().vocabularies[&dependency.namespace];
            assert_eq!(dependency.version, target.version);
            assert_eq!(dependency.digest, target.digest);
        }
    }
    for primitive in checked.definitions().declarations.values() {
        for row in primitive_declarations_wire(primitive) {
            assert_eq!(
                named(result, "declarations", "name", text(get(&row, "name"))),
                &row
            );
        }
        let location = location_wire(&primitive.location);
        let source = fixture_json(original(checked.sources(), text(get(&location, "input"))));
        let raw = pointer(&source, text(get(&location, "pointer")));
        assert_eq!(get(raw, "name"), &Json::str(&primitive.name));
        assert_eq!(get(raw, "meaning"), &Json::str(&primitive.meaning));
        for field in primitive.signature.record_fields().unwrap().1 {
            let location = location_wire(&field.location);
            let raw = pointer(&source, text(get(&location, "pointer")));
            assert_eq!(get(raw, "name"), &Json::str(&field.name));
            assert_eq!(get(raw, "type"), &field.ty.wire());
            assert_eq!(get(raw, "meaning"), &Json::str(&field.meaning));
        }
    }
    for declaration in &checked.law().infos {
        assert_eq!(
            named(result, "declarations", "name", &declaration.name),
            &declaration_wire(declaration)
        );
        let (start, end) = declaration.span;
        let script = std::str::from_utf8(checked.sources().law().bytes()).unwrap();
        assert!(start < end && end <= script.len());
        assert!(script[start..end].contains(declaration.name.rsplit('.').next().unwrap()));
        for binding in &declaration.vocabularies {
            let location = location_wire(&binding.location);
            let (start, end) = span(&location);
            let expected = format!(
                "use vocabulary {} version \"{}\" digest \"{}\";",
                binding.namespace, binding.version, binding.digest
            );
            assert_eq!(&script[start..end], expected);
            assert_eq!(
                binding.digest,
                checked.definitions().vocabularies[&binding.namespace].digest
            );
        }
    }
    // この観測入力には Counter の一 subject だけがある。Extras 用の観測を補わない。
    let subjects = &checked.archmap().snapshots[0].subjects;
    assert_eq!(subjects.len(), 1);
    assert_eq!(subjects[0].id, "s");
    assert_eq!(subjects[0].ty, "Counter.State");
}

fn typed<'a>(result: &'a Json, reference: &Json, ty: &Json) -> &'a Json {
    assert_eq!(obj(reference).len(), 1);
    let node = named(result, "nodes", "id", text(get(reference, "node")));
    assert_eq!(get(node, "type"), ty);
    node
}
fn value(node: &Json) -> &Json {
    assert_eq!(get(node, "state"), &Json::str("value"));
    get(node, "value")
}

// Ref 表示番号ではなく、実際の型付き値、判断、欠測 identity と Scope を比較する。
fn mathematical_answers(result: &Json, count: Option<&str>) -> Json {
    assert_eq!(
        get(result, "status"),
        &Json::str(if count.is_some() {
            "complete"
        } else {
            "partial"
        })
    );
    assert_eq!(
        arr(get(result, "requests"))
            .iter()
            .map(|r| text(get(r, "text")))
            .collect::<Vec<_>>(),
        ASKS
    );
    assert_eq!(
        arr(get(result, "answers"))
            .iter()
            .map(|r| text(get(r, "id")))
            .collect::<Vec<_>>(),
        ["audit", "n", "ok"]
    );
    let expected_missing = Json::obj([
        ("snapshot", Json::str("v")),
        ("subject", Json::str("s")),
        ("field", Json::str("Counter.State.count")),
    ]);
    let mut summaries = Vec::new();
    for answer in arr(get(result, "answers")) {
        let id = text(get(answer, "id"));
        let expected_status = match (count, id) {
            (None, _) => "undetermined",
            (Some("12"), "audit") => "refuted",
            _ => "established",
        };
        assert_eq!(get(answer, "status"), &Json::str(expected_status));
        let scope = get(answer, "scope");
        assert_eq!(
            get(scope, "readings"),
            &Json::Arr(vec![Json::str(if id == "audit" {
                "CountAudit"
            } else {
                "CountCheck"
            })])
        );
        assert_eq!(
            get(scope, "domain"),
            &Json::str(if count.is_some() {
                "finite_model"
            } else {
                "all_completions"
            })
        );
        assert_eq!(get(scope, "snapshots"), &Json::Arr(vec![Json::str("v")]));
        assert_eq!(
            get(scope, "modes"),
            &Json::Arr(vec![Json::str("specification")])
        );
        assert!(arr(get(scope, "assumptions")).is_empty());
        assert!(arr(get(scope, "quantifiers")).is_empty());
        let outputs = get(answer, "outputs");
        let evaluation = value(typed(
            result,
            get(outputs, "evaluation"),
            &Json::str("Evaluation"),
        ));
        let payload = if id == "n" {
            assert!(!obj(answer).contains_key("claim"));
            if let Some(n) = count {
                let output = typed(result, get(outputs, "value"), &Json::str("Z"));
                assert_eq!(value(output), &Json::str(n));
                assert_eq!(get(evaluation, "value"), get(outputs, "value"));
                value(output).clone()
            } else {
                assert!(!obj(outputs).contains_key("value"));
                assert!(!obj(evaluation).contains_key("value"));
                Json::str("missing Z")
            }
        } else {
            let claim = typed(result, get(answer, "claim"), &Json::str("Proposition"));
            assert_eq!(get(answer, "claim"), get(outputs, "proposition"));
            assert_eq!(
                get(get(claim, "judgment"), "status"),
                &Json::str(expected_status)
            );
            assert_eq!(get(value(claim), "predicate"), &Json::str("law_holds"));
            for operand in arr(get(value(claim), "operands")) {
                let instance = value(typed(result, operand, &Json::str("LawInstance")));
                assert_eq!(
                    get(instance, "name"),
                    &Json::str(if id == "audit" {
                        "CountAudit.bounded"
                    } else {
                        "CountCheck.nonnegative"
                    })
                );
            }
            if let Some(n) = count {
                let boolean = typed(result, get(evaluation, "value"), &Json::str("Bool"));
                assert_eq!(value(boolean), &Json::Bool(id != "audit" || n != "12"));
                value(boolean).clone()
            } else {
                assert!(!obj(evaluation).contains_key("value"));
                Json::str("missing Bool")
            }
        };
        let missing = if count.is_none() {
            for reason in arr(get(answer, "reasons")) {
                assert_eq!(get(reason, "code"), &Json::str("missing_observation"));
                let identities = arr(get(reason, "missing"));
                assert!(!identities.is_empty());
                assert!(
                    identities
                        .iter()
                        .all(|identity| identity == &expected_missing)
                );
            }
            let reason = arr(get(answer, "reasons"))
                .iter()
                .find(|r| get(r, "code") == &Json::str("missing_observation"))
                .unwrap();
            assert_eq!(
                get(reason, "missing"),
                &Json::Arr(vec![expected_missing.clone()])
            );
            assert!(!arr(get(reason, "dependencies")).is_empty());
            for dependency in arr(get(reason, "dependencies")) {
                let expression = value(typed(result, dependency, &Json::str("Expression")));
                assert_eq!(get(expression, "kind"), &Json::str("source"));
                let binding = &arr(get(expression, "bindings"))[0];
                assert_eq!(get(binding, "name"), &Json::str("s"));
                let subject = typed(
                    result,
                    get(binding, "value"),
                    &Json::Arr(vec![Json::str("Ref"), Json::str("Counter.State")]),
                );
                assert_eq!(
                    value(subject),
                    &Json::Arr(vec![Json::str("v"), Json::str("s")])
                );
            }
            get(reason, "missing").clone()
        } else {
            assert!(arr(get(answer, "reasons")).is_empty());
            Json::Arr(vec![])
        };
        if id == "audit" && count == Some("12") {
            let counterexample = arr(get(answer, "evidence"))
                .iter()
                .map(|r| value(typed(result, r, &Json::str("Evidence"))))
                .find(|e| get(e, "kind") == &Json::str("counterexample"))
                .unwrap();
            let data = get(counterexample, "data");
            assert_eq!(
                value(typed(result, get(data, "left"), &Json::str("Z"))),
                &Json::str("12")
            );
            assert_eq!(
                value(typed(result, get(data, "right"), &Json::str("Z"))),
                &Json::str("10")
            );
            assert!(arr(get(data, "facts")).contains(&Json::obj([
                ("snapshot", Json::str("v")),
                ("subject", Json::str("s")),
                ("field", Json::str("Counter.State.count")),
                ("atom", Json::str("count"))
            ])));
        }
        summaries.push(Json::obj([
            ("id", get(answer, "id").clone()),
            ("status", get(answer, "status").clone()),
            ("scope", scope.clone()),
            ("payload", payload),
            ("missing", missing),
        ]));
    }
    Json::Arr(summaries)
}

fn selected_derivations(checked: &CheckedInputs, result: &Json, has_spare: bool) {
    for node in arr(get(result, "nodes")) {
        for reading in arr(get(get(node, "scope"), "readings")) {
            assert!(matches!(text(reading), "CountCheck" | "CountAudit"));
        }
        if get(node, "type") == &Json::str("Expression")
            && get(node, "state") == &Json::str("value")
        {
            let payload = value(node);
            if get(payload, "kind") == &Json::str("source") {
                let location = get(payload, "location");
                assert_eq!(get(location, "input"), &Json::str("law"));
                let (start, end) = span(location);
                assert!(checked.law().declarations.values().any(|d| matches!(
                    d.name.as_str(),
                    "CountCheck.amount" | "CountCheck.nonnegative" | "CountAudit.bounded"
                ) && d.span.0 <= start
                    && end <= d.span.1));
                assert!(start < end && end <= checked.sources().law().bytes().len());
            }
        }
    }
    if has_spare {
        let spare = checked
            .law()
            .infos
            .iter()
            .find(|d| d.name == "Spare")
            .expect("拡張入力の Spare reading を保持する");
        assert_eq!(spare.kind, "reading");
        assert_eq!(
            named(result, "declarations", "name", "Spare"),
            &declaration_wire(spare)
        );
        assert_eq!(
            spare
                .vocabularies
                .iter()
                .map(|v| v.namespace.as_str())
                .collect::<Vec<_>>(),
            ["Counter", "Extras"]
        );
        let script = std::str::from_utf8(checked.sources().law().bytes()).unwrap();
        assert!(script[spare.span.0..spare.span.1].starts_with("reading Spare {"));
        for (name, source, kind) in [
            (
                "Spare.untouched",
                "view untouched(s: State): Z = match s.count { _ => 7; };",
                "view",
            ),
            (
                "Spare.caption",
                "view caption(note: Note): Text = note.text;",
                "view",
            ),
            ("Spare.spare", "law optional spare(n: Z): n >= 0;", "law"),
        ] {
            let declaration = checked
                .law()
                .declarations
                .get(name)
                .expect("拡張入力の非選択宣言を map に保持する");
            assert_eq!(declaration.reading, "Spare");
            assert_eq!(declaration.signature.kind(), kind);
            assert_eq!(&script[declaration.span.0..declaration.span.1], source);
            let info = checked
                .law()
                .infos
                .iter()
                .find(|d| d.name == name)
                .expect("拡張入力の非選択宣言を infos に保持する");
            assert_eq!(info.span, declaration.span);
            assert_eq!(info.kind, kind);
            assert_eq!(
                named(result, "declarations", "name", name),
                &declaration_wire(info)
            );
        }
        let declaration = checked
            .law()
            .declarations
            .get("Spare.untouched")
            .expect("非選択 match view を保持する");
        let Signature::View { body, .. } = &declaration.signature else {
            panic!("view")
        };
        assert!(matches!(
            &checked.law().exprs[*body].kind,
            ExprKind::Match { .. }
        ));
        let expression = &checked.law().exprs[*body];
        assert_eq!(
            &script[expression.span.0..expression.span.1],
            "match s.count { _ => 7; }"
        );
        let reading = checked
            .law()
            .infos
            .iter()
            .find(|d| d.name == "CountCheck")
            .unwrap();
        assert_eq!(
            reading
                .vocabularies
                .iter()
                .map(|v| v.namespace.as_str())
                .collect::<Vec<_>>(),
            ["Counter", "Extras"]
        );
        assert!(reading.dependencies.contains(&"Spare".to_owned()));
        let (position, target) = reading
            .references
            .iter()
            .find(|(_, name)| name == "Spare")
            .unwrap();
        assert_eq!(target, "Spare");
        assert_eq!(
            &checked.sources().law().bytes()[position.0..position.1],
            b"Spare"
        );
        assert!(
            std::str::from_utf8(checked.sources().law().bytes())
                .unwrap()
                .contains("use Spare as S;")
        );
    }
}

fn compare_unused(count: Option<&str>) {
    let map = map_count(count);
    let extended = extended_law();
    let variants = [
        (false, sources(vec![COUNTER.to_vec()], LAW, &map)),
        (false, sources(vec![LIBRARY.to_vec()], LAW, &map)),
        (
            false,
            sources(vec![COUNTER.to_vec(), EXTRAS.to_vec()], LAW, &map),
        ),
        (
            false,
            sources(vec![EXTRAS.to_vec(), COUNTER.to_vec()], LAW, &map),
        ),
        (true, sources(vec![LIBRARY.to_vec()], &extended, &map)),
    ];
    let mut baseline = None;
    for (has_spare, src) in variants {
        let prepared = prepare_observed(src.clone(), &ASKS, &mut Control::unlimited()).unwrap();
        assert_eq!(prepared.inputs().sources(), &src);
        let checked_metadata = prepared.inputs().metadata_wire();
        // 評価前にも元位置と全 metadata を照合し、同じ bundle を評価へ渡す。
        retained_metadata(prepared.inputs(), &checked_metadata);
        let evaluated = evaluate_observed(prepared, &mut Control::unlimited()).unwrap();
        let result = evaluated.wire();
        for key in ["inputs", "declarations", "vocabularies"] {
            assert_eq!(get(&result, key), get(&checked_metadata, key));
        }
        let checked = evaluated.prepared().inputs();
        assert_eq!(checked.sources(), &src);
        retained_metadata(checked, &result);
        selected_derivations(checked, &result, has_spare);
        let current = mathematical_answers(&result, count);
        if let Some(baseline) = &baseline {
            assert_eq!(&current, baseline);
        } else {
            baseline = Some(current);
        }
        assert!(
            arr(get(&result, "issues"))
                .iter()
                .all(|issue| get(issue, "code") == &Json::str("missing_observation"))
        );
        if count == Some("2") && has_spare {
            let Signature::View { body, .. } =
                &checked.law().declarations["Spare.untouched"].signature
            else {
                unreachable!()
            };
            let expected = checked.law().exprs[*body].span;
            let failure = evaluate_observed_bytes(
                src,
                &["probe=evaluate(Spare.untouched,s=@v/s)"],
                &mut Control::unlimited(),
            )
            .unwrap_err();
            assert!(failure.wire().is_none());
            let EvaluationFailure::NotImplemented {
                declaration,
                location,
                feature,
            } = failure
            else {
                panic!("選択した match の評価は未実装")
            };
            assert_eq!(declaration, "Spare.untouched");
            assert_eq!(location, archsig::issue::Location::Law { span: expected });
            assert!(!feature.is_empty());
        }
    }
}

#[test]
fn unused_information_preserves_two() {
    compare_unused(Some("2"));
}
#[test]
fn unused_information_preserves_twelve() {
    compare_unused(Some("12"));
}
#[test]
fn unused_information_preserves_missing() {
    compare_unused(None);
}

fn rejected(
    src: InputSources,
    status: InputStatus,
    code: &str,
    input: &str,
    position: &str,
) -> Json {
    let failure =
        evaluate_observed_bytes(src.clone(), &ASKS, &mut Control::unlimited()).unwrap_err();
    let EvaluationFailure::Prepare(PrepareFailure::Inputs(failure)) = failure else {
        panic!("全入力検査で拒否: {failure:?}")
    };
    assert_eq!(failure.status(), status);
    assert_eq!(failure.sources(), &src);
    let wire = failure.wire();
    assert_eq!(get(&wire, "status"), &Json::str(status.wire()));
    for key in [
        "requests",
        "answers",
        "nodes",
        "declarations",
        "vocabularies",
    ] {
        assert!(arr(get(&wire, key)).is_empty());
    }
    let issues = arr(get(&wire, "issues"));
    assert_eq!(issues.len(), 1);
    let issue = &issues[0];
    assert_eq!(get(issue, "code"), &Json::str(code));
    assert!(!text(get(issue, "message")).is_empty());
    let location = get(issue, "location");
    assert_eq!(get(location, "input"), &Json::str(input));
    if input == "law" {
        let script = std::str::from_utf8(src.law().bytes()).unwrap();
        let start = script.find(position).unwrap();
        let (a, b) = span(location);
        assert!(
            start <= a && a < b && b <= start + position.len(),
            "{location:?}: {position}"
        );
        assert!(!script[a..b].is_empty());
    } else {
        assert_eq!(get(location, "pointer"), &Json::str(position));
        let source = fixture_json(original(&src, input));
        pointer(&source, position);
    }
    for identity in failure.inputs() {
        assert_eq!(
            identity.bytes_digest,
            Some(sha256_digest(original(&src, &identity.id)))
        );
    }
    wire
}

fn accept(src: InputSources) {
    let result = evaluate_observed_bytes(src, &ASKS, &mut Control::unlimited())
        .unwrap()
        .wire();
    mathematical_answers(&result, Some("2"));
    assert!(arr(get(&result, "issues")).is_empty());
}

#[test]
fn unselected_law_reference_and_type_are_rejected() {
    let good = extended_law();
    for (from, to, code) in [
        (
            "view caption(note: Note): Text = note.text;",
            "view caption(note: Note): Text = note.absent;",
            "reference",
        ),
        (
            "law optional spare(n: Z): n >= 0;",
            "law optional spare(n: Z): n >= true;",
            "type",
        ),
    ] {
        accept(sources(vec![LIBRARY.to_vec()], &good, MAP.as_bytes()));
        let bad = good.replace(from, to);
        let wire = rejected(
            sources(vec![LIBRARY.to_vec()], &bad, MAP.as_bytes()),
            InputStatus::Invalid,
            code,
            "law",
            to,
        );
        if code == "type" {
            assert_eq!(
                get(&arr(get(&wire, "issues"))[0], "details"),
                &Json::obj([("expected", Json::str("Z")), ("actual", Json::str("Bool"))])
            );
        }
    }
}

#[test]
fn unused_import_and_dependency_bindings_are_rejected() {
    let good = extended_law();
    let definitions = check_definitions(&[("definition0", LIBRARY)]).unwrap();
    let digest = &definitions.vocabularies["Extras"].digest;
    let import = format!("use vocabulary Extras version \"1\" digest \"{digest}\";");
    for broken in [
        import.replace("version \"1\"", "version \"2\""),
        import.replace(digest, &format!("sha256:{}", "0".repeat(64))),
    ] {
        accept(sources(vec![LIBRARY.to_vec()], &good, MAP.as_bytes()));
        let bad = good.replacen(&import, &broken, 1);
        rejected(
            sources(vec![LIBRARY.to_vec()], &bad, MAP.as_bytes()),
            InputStatus::Invalid,
            "vocabulary_mismatch",
            "law",
            &broken,
        );
    }
    let extras = std::str::from_utf8(EXTRAS).unwrap();
    let counter_digest = &definitions.vocabularies["Counter"].digest;
    let (before_version, after_version) = extras.rsplit_once("\"version\": \"1\"").unwrap();
    for bad in [
        format!("{before_version}\"version\": \"2\"{after_version}"),
        extras.replace(counter_digest, &format!("sha256:{}", "0".repeat(64))),
    ] {
        accept(sources(
            vec![COUNTER.to_vec(), EXTRAS.to_vec()],
            LAW,
            MAP.as_bytes(),
        ));
        // 未使用 dependency の版/digest も Counter と照合する。
        rejected(
            sources(
                vec![COUNTER.to_vec(), bad.into_bytes()],
                LAW,
                MAP.as_bytes(),
            ),
            InputStatus::Invalid,
            "vocabulary_mismatch",
            "definition1",
            "/vocabularies/0/dependencies/0",
        );
    }
}

#[test]
fn unselected_definition_reference_and_type_are_rejected() {
    let extras = std::str::from_utf8(EXTRAS).unwrap();
    let linked = extras.replace(
        "\"type\": \"Text\"",
        "\"type\": [\"Ref\",\"Counter.State\"]",
    );
    accept(sources(
        vec![COUNTER.to_vec(), linked.as_bytes().to_vec()],
        LAW,
        MAP.as_bytes(),
    ));
    let bad = linked.replace(
        "[\"Ref\",\"Counter.State\"]",
        "[\"Ref\",\"Counter.Absent\"]",
    );
    rejected(
        sources(
            vec![COUNTER.to_vec(), bad.into_bytes()],
            LAW,
            MAP.as_bytes(),
        ),
        InputStatus::Invalid,
        "reference",
        "definition1",
        "/vocabularies/0/declarations/0/fields/0/type/1",
    );

    // 左の parameter の型と Owned 添字の根型を照合する、小さい未使用定義。
    let mut owned = fixture_json(EXTRAS);
    let Json::Obj(root) = &mut owned else {
        unreachable!()
    };
    let Json::Arr(vocabularies) = root.get_mut("vocabularies").unwrap() else {
        unreachable!()
    };
    let Json::Obj(vocabulary) = &mut vocabularies[0] else {
        unreachable!()
    };
    let Json::Arr(declarations) = vocabulary.get_mut("declarations").unwrap() else {
        unreachable!()
    };
    declarations.extend(arr(&fixture_json(r#"[
        {"kind":"entity","name":"Extras.Entry","meaning":"メモに属する項目。","parameters":[{"name":"owner","type":["Ref","Extras.Note"],"meaning":"所属先。"}],"fields":[],"alignments":[]},
        {"kind":"entity","name":"Extras.Bundle","meaning":"同じメモの項目。","parameters":[{"name":"basis","type":["Ref","Extras.Note"],"meaning":"所属先。"},{"name":"item","type":["Owned","Extras.Entry","basis"],"meaning":"その項目。"}],"fields":[],"alignments":[]}
    ]"#.as_bytes())).iter().cloned());
    let good = owned.canonical();
    accept(sources(
        vec![COUNTER.to_vec(), good.as_bytes().to_vec()],
        LAW,
        MAP.as_bytes(),
    ));
    let bad = good.replace(
        "\"name\":\"basis\",\"type\":[\"Ref\",\"Extras.Note\"]",
        "\"name\":\"basis\",\"type\":\"Z\"",
    );
    assert_ne!(bad, good);
    let wire = rejected(
        sources(
            vec![COUNTER.to_vec(), bad.into_bytes()],
            LAW,
            MAP.as_bytes(),
        ),
        InputStatus::Invalid,
        "type",
        "definition1",
        "/vocabularies/0/declarations/2/parameters/1/type/2",
    );
    assert_eq!(
        get(&arr(get(&wire, "issues"))[0], "details"),
        &Json::obj([
            (
                "expected",
                Json::Arr(vec![Json::str("Ref"), Json::str("Extras.Note")])
            ),
            ("actual", Json::str("Z"))
        ])
    );
}

#[test]
fn unused_unknown_semantics_is_unsupported() {
    accept(sources(
        vec![COUNTER.to_vec(), EXTRAS.to_vec()],
        LAW,
        MAP.as_bytes(),
    ));
    let extras = std::str::from_utf8(EXTRAS).unwrap();
    let bad = extras.replacen(
        "\"semantics\": \"archsig/0.6.0\"",
        "\"semantics\": \"archsig/future\"",
        2,
    );
    // 対応する wrapper の下にある未使用語彙だけを未知版にする。
    let bad = bad.replacen(
        "\"semantics\": \"archsig/future\"",
        "\"semantics\": \"archsig/0.6.0\"",
        1,
    );
    let wire = rejected(
        sources(
            vec![COUNTER.to_vec(), bad.into_bytes()],
            LAW,
            MAP.as_bytes(),
        ),
        InputStatus::Unsupported,
        "unsupported_version",
        "definition1",
        "/vocabularies/0/semantics",
    );
    assert_eq!(
        get(&arr(get(&wire, "issues"))[0], "details"),
        &Json::obj([
            ("found_format", Json::str("archsig.atom-definition/1")),
            ("found_semantics", Json::str("archsig/future"))
        ])
    );
}
