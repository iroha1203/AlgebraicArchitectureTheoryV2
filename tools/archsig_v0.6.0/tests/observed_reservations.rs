//! AC9: 元 Reservations 三入力の byte API と、各参照 prefix の原式・支持・由来。
use archsig::{
    archmap::{Mode, Slot},
    canonical::{Json, sha256_digest},
    json::{JNode, JValue},
    law::{ast::ExprKind, model::Signature},
    observed::{
        ObservedEvaluation,
        control::{Control, Limits, Usage},
        evaluate_observed, evaluate_observed_bytes,
        input::{CheckedInputs, InputSources, check_inputs},
        prepare_checked_observed,
    },
};
use std::collections::{BTreeMap, BTreeSet};

const DEFINITIONS: &[u8] = include_bytes!("fixtures/reservations.atoms.json");
const LAW: &[u8] = include_bytes!("fixtures/reservations.law");
const MAP: &[u8] = include_bytes!("fixtures/reservations.archmap.json");
const ASK: &str = "c=check(Reservations.conserved,e=@v/e)";

fn quiet() -> Control {
    Control::new(Limits::default(), |_| Usage::default())
}
fn sources(law: &[u8], map: &[u8]) -> InputSources {
    InputSources::from_bytes(vec![DEFINITIONS.to_vec()], law.to_vec(), map.to_vec())
}
fn explicit_law() -> Vec<u8> {
    String::from_utf8(LAW.to_vec())
        .unwrap()
        .replace(
            "conserved(e: Reserve):",
            "conserved(e: Reservations.Reserve) when true:",
        )
        .into_bytes()
}
fn q_free(value: Option<&str>) -> Vec<u8> {
    let original = "      {\"id\": \"q-free\", \"subject\": \"q\", \"field\": \"Reservations.State.free\", \"value\": \"1\", \"origin\": \"model\"},\n";
    let text = std::str::from_utf8(MAP).unwrap();
    assert_eq!(text.matches(original).count(), 1);
    text.replace(
        original,
        &value.map_or_else(String::new, |n| {
            original.replace("\"value\": \"1\"", &format!("\"value\": \"{n}\""))
        }),
    )
    .into_bytes()
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
fn input_at<'a>(mut node: &'a JNode, pointer: &str) -> &'a JNode {
    for token in pointer.strip_prefix('/').unwrap().split('/') {
        node = match &node.value {
            JValue::Obj(fields) => &fields.iter().find(|(key, _)| key == token).unwrap().1,
            JValue::Arr(items) => &items[token.parse::<usize>().unwrap()],
            _ => panic!("実入力内の pointer: {pointer}"),
        };
    }
    node
}
fn primitive_input(node: &JNode) -> Json {
    match &node.value {
        JValue::Str(s) => Json::str(s),
        JValue::Arr(items) => Json::Arr(items.iter().map(primitive_input).collect()),
        _ => panic!("この原fixtureの支持は整数か参照"),
    }
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
    assert_eq!(obj(reference).len(), 1, "Ref は node 一欄");
    let n = ns[text(f(reference, "node"))];
    assert_eq!(f(n, "type"), ty);
    n
}
fn span(j: &Json) -> (usize, usize) {
    assert_eq!(f(j, "input"), &Json::str("law"));
    let pair = arr(f(j, "span"));
    assert_eq!(pair.len(), 2);
    let nat = |j: &Json| match j {
        Json::Nat(n) => *n as usize,
        _ => panic!("Nat: {j:?}"),
    };
    (nat(&pair[0]), nat(&pair[1]))
}
fn refs(j: &Json, out: &mut Vec<String>) {
    match j {
        Json::Obj(m) if m.len() == 1 && m.contains_key("node") => {
            out.push(text(&m["node"]).to_owned());
        }
        Json::Obj(m) => m.values().for_each(|v| refs(v, out)),
        Json::Arr(a) => a.iter().for_each(|v| refs(v, out)),
        _ => {}
    }
}
fn fact(subject: &str, field: Option<&str>, atom: Option<&str>) -> Json {
    let mut f = BTreeMap::from([
        ("snapshot".into(), Json::str("v")),
        ("subject".into(), Json::str(subject)),
    ]);
    if let Some(field) = field {
        f.insert("field".into(), Json::str(field));
    }
    if let Some(atom) = atom {
        f.insert("atom".into(), Json::str(atom));
    }
    Json::Obj(f)
}
fn ref_type(entity: &str) -> Json {
    Json::Arr(vec![Json::str("Ref"), Json::str(entity)])
}
fn binding(ns: &BTreeMap<&str, &Json>, bindings: &Json) {
    let bindings = arr(bindings);
    assert_eq!(bindings.len(), 1);
    assert_eq!(f(&bindings[0], "name"), &Json::str("e"));
    let bound = target(
        ns,
        f(&bindings[0], "value"),
        &ref_type("Reservations.Reserve"),
    );
    assert_eq!(val(bound), &Json::Arr(vec![Json::str("v"), Json::str("e")]));
}
fn expression<'a>(ns: &BTreeMap<&str, &'a Json>, evaluation: &Json) -> &'a Json {
    target(
        ns,
        f(val(evaluation), "expression"),
        &Json::str("Expression"),
    )
}
fn own_part(evaluation: &Json) -> &Json {
    let parts = arr(f(val(evaluation), "parts"));
    assert_eq!(parts.len(), 1);
    &parts[0]
}
fn at<'a>(ns: &BTreeMap<&str, &'a Json>, position: (usize, usize)) -> &'a Json {
    let matches: Vec<_> = ns
        .values()
        .copied()
        .filter(|n| {
            f(n, "type") == &Json::str("Evaluation")
                && arr(f(val(n), "parts")).len() == 1
                && f(val(expression(ns, n)), "kind") == &Json::str("source")
                && span(f(val(expression(ns, n)), "location")) == position
        })
        .collect();
    assert_eq!(matches.len(), 1, "元出現 {position:?} の評価を統合しない");
    matches[0]
}
fn scopes(wire: &Json, missing: bool) {
    let answer = &arr(f(wire, "answers"))[0];
    assert_eq!(
        f(f(answer, "scope"), "domain"),
        &Json::str(if missing {
            "all_completions"
        } else {
            "finite_model"
        })
    );
    for item in arr(f(wire, "nodes")).iter().chain([answer]) {
        let scope = f(item, "scope");
        assert_eq!(
            f(scope, "readings"),
            &Json::Arr(vec![Json::str("Reservations")])
        );
        assert_eq!(f(scope, "snapshots"), &Json::Arr(vec![Json::str("v")]));
        assert_eq!(
            f(scope, "modes"),
            &Json::Arr(vec![Json::str("specification")])
        );
        assert!(arr(f(scope, "quantifiers")).is_empty());
        assert!(arr(f(scope, "assumptions")).is_empty());
        assert!(matches!(
            text(f(scope, "domain")),
            "finite_model" | "all_completions"
        ));
    }
}
fn dag(wire: &Json) {
    let ns = index(wire);
    let mut earlier = BTreeSet::new();
    for node in arr(f(wire, "nodes")) {
        let mut references = vec![];
        refs(node, &mut references);
        for reference in references {
            assert!(
                earlier.contains(reference.as_str()),
                "全 payload/型/理由 Ref は既出"
            );
        }
        assert!(earlier.insert(text(f(node, "id"))));
        if f(node, "type") != &Json::str("Proposition") {
            assert!(!obj(node).contains_key("judgment"));
        }
        if f(node, "state") == &Json::str("blocked") {
            assert!(!obj(node).contains_key("value"));
            assert!(!arr(f(node, "reasons")).is_empty());
        }
        if let Some(payload) = obj(node).get("value") {
            let mut consumed = vec![];
            refs(payload, &mut consumed);
            for r in consumed {
                assert_ne!(f(ns[r.as_str()], "state"), &Json::str("blocked"));
                assert!(!obj(ns[r.as_str()]).contains_key("partial"));
            }
        }
        for r in arr(f(node, "evidence")) {
            target(&ns, r, &Json::str("Evidence"));
        }
        for r in arr(f(node, "conditions")) {
            target(&ns, r, &Json::str("Proposition"));
        }
    }
    for answer in arr(f(wire, "answers")) {
        let mut references = vec![];
        refs(answer, &mut references);
        assert!(references.iter().all(|r| ns.contains_key(r.as_str())));
        let proposition = target(&ns, f(answer, "claim"), &Json::str("Proposition"));
        assert_eq!(f(f(proposition, "judgment"), "status"), f(answer, "status"));
        assert_eq!(f(f(answer, "outputs"), "proposition"), f(answer, "claim"));
    }
}

fn unchanged(expected: &CheckedInputs, actual: &CheckedInputs, law: &[u8], map: &[u8]) {
    assert_eq!(actual.sources(), expected.sources());
    assert_eq!(actual.sources().definitions()[0].bytes(), DEFINITIONS);
    assert_eq!(actual.sources().law().bytes(), law);
    assert_eq!(actual.sources().archmap().bytes(), map);
    assert_eq!(actual.inputs(), expected.inputs());
    assert_eq!(actual.definitions(), expected.definitions());
    assert_eq!(actual.definitions(), &actual.law().definitions);
    assert_eq!(actual.law().declarations, expected.law().declarations);
    assert_eq!(actual.law().exprs, expected.law().exprs);
    assert_eq!(actual.law().expr_types, expected.law().expr_types);
    assert_eq!(actual.law().infos, expected.law().infos);
    assert_eq!(actual.law().bytes_digest, sha256_digest(law));
    assert_eq!(actual.law().model_digest, expected.law().model_digest);
    assert_eq!(actual.archmap().snapshots, expected.archmap().snapshots);
    assert_eq!(actual.archmap().origins, expected.archmap().origins);
    assert_eq!(actual.archmap().sources, expected.archmap().sources);
    assert_eq!(
        actual.archmap().vocabularies,
        expected.archmap().vocabularies
    );
    assert_eq!(actual.archmap().bytes_digest, sha256_digest(map));
    assert_eq!(
        actual.archmap().model_digest,
        expected.archmap().model_digest
    );
}

fn assert_occurrences(checked: &CheckedInputs, wire: &Json, missing: bool) {
    let ns = index(wire);
    let declaration = &checked.law().declarations["Reservations.conserved"];
    let Signature::Law {
        params,
        guard,
        body,
        ..
    } = &declaration.signature
    else {
        panic!("Law")
    };
    assert_eq!(params.len(), 1);
    assert_eq!(params[0].name, "e");
    assert_eq!(params[0].ty.wire(), ref_type("Reservations.Reserve"));
    let body_span = checked.law().exprs[*body].span;
    let law = checked.sources().law().bytes();
    assert_eq!(&law[params[0].span.0..params[0].span.1], b"e");
    let info = checked
        .law()
        .infos
        .iter()
        .find(|d| d.name == "Reservations.conserved")
        .unwrap();
    let defaults: Vec<_> = info
        .supplied
        .iter()
        .filter_map(|r| match r {
            archsig::law::model::SuppliedRule::GuardTrue { span } => Some(*span),
            _ => None,
        })
        .collect();
    assert_eq!(
        defaults,
        if guard.is_none() {
            vec![declaration.span]
        } else {
            vec![]
        }
    );
    let mut dotted_count = 0;
    for (id, expr) in checked.law().exprs.iter().enumerate() {
        if expr.span.0 < body_span.0
            || body_span.1 < expr.span.1
            || checked.law().expr_type(id).is_none()
        {
            continue;
        }
        let evaluation = at(&ns, expr.span);
        let source = expression(&ns, evaluation);
        assert_eq!(f(val(source), "kind"), &Json::str("source"));
        assert!(arr(f(val(source), "parameters")).is_empty());
        binding(&ns, f(val(source), "bindings"));
        binding(&ns, f(val(evaluation), "bindings"));
        assert_eq!(span(f(own_part(evaluation), "location")), expr.span);
        if let Some(reference) = obj(own_part(evaluation)).get("value") {
            target(&ns, reference, &checked.law().expr_type(id).unwrap().wire());
        }
        for child in arr(f(own_part(evaluation), "children")) {
            let child = target(&ns, child, &Json::str("Evaluation"));
            let position = span(f(val(expression(&ns, child)), "location"));
            assert!(expr.span.0 <= position.0 && position.1 <= expr.span.1);
            assert_ne!(position, expr.span);
        }
        let ExprKind::Dotted(parts) = &expr.kind else {
            continue;
        };
        dotted_count += 1;
        assert_eq!(parts.len(), 3);
        assert_eq!(parts[0].name, "e");
        let middle_span = (parts[0].span.0, parts[1].span.1);
        let first = at(&ns, parts[0].span);
        let middle = at(&ns, middle_span);
        let owner = if parts[1].name == "to" {
            "q"
        } else {
            assert_eq!(parts[1].name, "from");
            "p"
        };
        for (prefix, ty, expected) in [
            (first, ref_type("Reservations.Reserve"), "e"),
            (middle, ref_type("Reservations.State"), owner),
        ] {
            let prefix_source = expression(&ns, prefix);
            binding(&ns, f(val(prefix_source), "bindings"));
            binding(&ns, f(val(prefix), "bindings"));
            assert_eq!(f(val(prefix), "applicability"), &Json::str("applicable"));
            assert_eq!(
                val(target(&ns, f(val(prefix), "value"), &ty)),
                &Json::Arr(vec![Json::str("v"), Json::str(expected)])
            );
        }
        assert_eq!(
            &law[middle_span.0..middle_span.1],
            format!("e.{}", parts[1].name).as_bytes()
        );
        let middle_children = arr(f(own_part(middle), "children"));
        let leaf_children = arr(f(own_part(evaluation), "children"));
        assert_eq!(middle_children.len(), 1);
        assert_eq!(leaf_children.len(), 1);
        assert_eq!(
            target(&ns, &middle_children[0], &Json::str("Evaluation")),
            first
        );
        assert_eq!(
            target(&ns, &leaf_children[0], &Json::str("Evaluation")),
            middle
        );
        let middle_value = target(
            &ns,
            f(val(middle), "value"),
            &ref_type("Reservations.State"),
        );
        assert_eq!(f(f(middle_value, "rule"), "kind"), &Json::str("law"));
        assert_eq!(span(f(f(middle_value, "rule"), "location")), middle_span);
        assert_eq!(
            arr(f(middle_value, "arguments")),
            &[
                f(val(first), "value").clone(),
                f(val(middle), "expression").clone(),
            ],
            "元chain fieldのownerと自身のSource出現を固定する"
        );
        let intermediate_fact = fact(
            "e",
            Some(&format!("Reservations.Reserve.{}", parts[1].name)),
            Some(&format!("e-{}", parts[1].name)),
        );
        assert!(arr(f(middle, "support")).contains(&intermediate_fact));
        assert!(arr(f(evaluation, "support")).contains(&intermediate_fact));
        let leaf_field = format!("Reservations.State.{}", parts[2].name);
        let leaf_atom = format!("{owner}-{}", parts[2].name);
        let leaf_fact = fact(owner, Some(&leaf_field), Some(&leaf_atom));
        if missing && owner == "q" && parts[2].name == "free" {
            assert!(!obj(val(evaluation)).contains_key("value"));
            assert!(!obj(own_part(evaluation)).contains_key("value"));
            assert!(!arr(f(evaluation, "support")).contains(&leaf_fact));
        } else {
            assert!(arr(f(evaluation, "support")).contains(&leaf_fact));
            let leaf = target(&ns, f(val(evaluation), "value"), &Json::str("Z"));
            assert_eq!(
                arr(f(leaf, "arguments")),
                &[
                    f(val(middle), "value").clone(),
                    f(val(evaluation), "expression").clone(),
                ]
            );
            assert_eq!(f(f(leaf, "rule"), "kind"), &Json::str("law"));
            assert_eq!(span(f(f(leaf, "rule"), "location")), expr.span);
            let subject = checked.archmap().snapshots[0]
                .subjects
                .iter()
                .find(|s| s.id == owner)
                .unwrap();
            let Slot::Known { value, .. } = &subject
                .fields
                .iter()
                .find(|f| f.name == leaf_field)
                .unwrap()
                .slot
            else {
                panic!("既知数値")
            };
            assert_eq!(val(leaf), &value.canonical_json());
        }
    }
    assert_eq!(dotted_count, 4, "四つの元field出現を保持する");
    let instances: Vec<_> = ns
        .values()
        .copied()
        .filter(|n| f(n, "type") == &Json::str("LawInstance"))
        .collect();
    assert_eq!(instances.len(), 1);
    let instance = val(instances[0]);
    assert_eq!(f(instance, "name"), &Json::str("Reservations.conserved"));
    assert_eq!(f(instance, "role"), &Json::str("required"));
    assert_eq!(span(f(instance, "occurrence")), declaration.span);
    binding(&ns, f(instance, "bindings"));
    assert_eq!(
        span(f(
            val(target(&ns, f(instance, "body"), &Json::str("Expression"))),
            "location"
        )),
        body_span
    );
    if let Some(guard) = guard {
        let guard_span = checked.law().exprs[*guard].span;
        assert_eq!(&law[guard_span.0..guard_span.1], b"true");
        assert_eq!(
            span(f(
                val(target(&ns, f(instance, "guard"), &Json::str("Expression"))),
                "location"
            )),
            guard_span
        );
        let evaluation = at(&ns, guard_span);
        assert_eq!(
            val(target(&ns, f(val(evaluation), "value"), &Json::str("Bool"))),
            &Json::Bool(true)
        );
    } else {
        assert!(
            !obj(instance).contains_key("guard"),
            "省略guardに架空の元出現を作らない"
        );
    }
    let free = checked.definitions().declarations["Reservations.State"]
        .location
        .clone();
    let archsig::issue::Location::Definition { input, pointer, .. } = free else {
        panic!("定義位置")
    };
    assert_eq!(input, "definition0");
    assert_eq!(pointer, "/vocabularies/0/declarations/2");
    let (_, fields) = checked.definitions().declarations["Reservations.State"]
        .signature
        .record_fields()
        .unwrap();
    for (index, expected) in [(0, "free"), (1, "held")] {
        assert_eq!(fields[index].name, expected);
        assert_eq!(fields[index].ty.wire(), Json::str("Z"));
        let archsig::issue::Location::Definition { input, pointer, .. } = &fields[index].location
        else {
            panic!("原始field位置")
        };
        assert_eq!(input, "definition0");
        assert_eq!(
            pointer,
            &format!("/vocabularies/0/declarations/2/fields/{index}")
        );
    }
}

fn assert_support(checked: &CheckedInputs, wire: &Json, uri: Option<&str>) {
    let mut seen = BTreeSet::new();
    let original = archsig::json::parse(checked.sources().archmap().bytes()).unwrap();
    for node in arr(f(wire, "nodes")) {
        for pointer in arr(f(node, "support")) {
            assert_eq!(f(pointer, "snapshot"), &Json::str("v"));
            let snapshot = &checked.archmap().snapshots[0];
            let subject = snapshot
                .subjects
                .iter()
                .find(|s| s.id == text(f(pointer, "subject")))
                .unwrap();
            let origin = if let Some(field) = obj(pointer).get("field") {
                let slot = &subject
                    .fields
                    .iter()
                    .find(|s| s.name == text(field))
                    .unwrap()
                    .slot;
                let Slot::Known {
                    atom,
                    origin,
                    value,
                    pointer: input_pointer,
                } = slot
                else {
                    panic!("欠測は既知支持へ加えない")
                };
                assert_eq!(atom, text(f(pointer, "atom")));
                // chain Scalar の元位置は Law。原始事実の byte 位置は実 slot を通して追う。
                assert_eq!(
                    primitive_input(input_at(&original, input_pointer)),
                    value.canonical_json()
                );
                let atom_pointer = input_pointer.strip_suffix("/value").unwrap();
                for (key, expected) in [
                    ("id", atom.as_str()),
                    ("subject", subject.id.as_str()),
                    ("field", text(field)),
                    ("origin", origin.as_str()),
                ] {
                    assert_eq!(
                        primitive_input(input_at(&original, &format!("{atom_pointer}/{key}"))),
                        Json::str(expected)
                    );
                }
                seen.insert(atom.as_str());
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
            assert_eq!(origin.mode, Mode::Specification);
            if let Some(uri) = uri {
                assert_eq!(origin.locations.len(), 1);
                let location = &origin.locations[0];
                assert_eq!(location.path, "reservations.model");
                assert_eq!(
                    location.span,
                    Some(if uri.ends_with("moved") {
                        (23, 29)
                    } else {
                        (3, 9)
                    })
                );
                let source = checked
                    .archmap()
                    .sources
                    .iter()
                    .find(|s| s.id == location.source)
                    .unwrap();
                assert_eq!(source.uri, uri);
                assert_eq!(
                    source.revision,
                    if uri.ends_with("moved") { "r2" } else { "r1" }
                );
            } else {
                assert_eq!(origin.id, "model");
                assert!(origin.locations.is_empty());
                assert!(!origin.note.as_deref().unwrap_or("").is_empty());
            }
        }
    }
    for atom in ["e-to", "e-from", "p-free", "p-held", "q-held"] {
        assert!(seen.contains(atom), "参照prefixと数値の支持 {atom}");
    }
}

fn assert_case(result: &ObservedEvaluation, decision: &str, left: Option<&str>, uri: Option<&str>) {
    let checked = result.prepared().inputs();
    let wire = result.wire();
    let missing = left.is_none();
    assert_eq!(
        f(&wire, "status"),
        &Json::str(if missing { "partial" } else { "complete" })
    );
    if missing {
        assert!(!arr(f(&wire, "issues")).is_empty());
        assert!(
            arr(f(&wire, "issues"))
                .iter()
                .all(|issue| f(issue, "code") == &Json::str("missing_observation"))
        );
    } else {
        assert!(arr(f(&wire, "issues")).is_empty());
    }
    let answers = arr(f(&wire, "answers"));
    assert_eq!(answers.len(), 1);
    let answer = &answers[0];
    assert_eq!(f(answer, "id"), &Json::str("c"));
    assert_eq!(f(answer, "status"), &Json::str(decision));
    let request = &arr(f(&wire, "requests"))[0];
    assert_eq!(f(request, "text"), &Json::str(ASK));
    let arguments = arr(f(request, "arguments"));
    assert_eq!(arguments.len(), 1);
    assert_eq!(f(&arguments[0], "name"), &Json::str("bind.e"));
    assert_eq!(
        f(&arguments[0], "value"),
        &Json::obj([
            ("kind", Json::str("subject")),
            ("snapshot", Json::str("v")),
            ("subject", Json::str("e")),
        ])
    );
    assert_eq!(f(&arguments[0], "origin"), &Json::str("explicit"));
    assert!(
        arr(f(request, "defaults"))
            .contains(&Json::obj([("rule", Json::str("observed_environment"))]))
    );
    let ns = index(&wire);
    let evaluation = target(
        &ns,
        f(f(answer, "outputs"), "evaluation"),
        &Json::str("Evaluation"),
    );
    assert_eq!(
        f(val(evaluation), "applicability"),
        &Json::str("applicable")
    );
    binding(&ns, f(val(evaluation), "bindings"));
    let Signature::Law { body, .. } =
        &checked.law().declarations["Reservations.conserved"].signature
    else {
        panic!("Law")
    };
    let body = at(&ns, checked.law().exprs[*body].span);
    let children = arr(f(own_part(body), "children"));
    assert_eq!(children.len(), 2);
    let lhs = target(&ns, &children[0], &Json::str("Evaluation"));
    let rhs = target(&ns, &children[1], &Json::str("Evaluation"));
    for (side, expected) in [
        (lhs, b"e.to.free + e.to.held".as_slice()),
        (rhs, b"e.from.free + e.from.held".as_slice()),
    ] {
        let position = span(f(val(expression(&ns, side)), "location"));
        assert_eq!(
            &checked.sources().law().bytes()[position.0..position.1],
            expected
        );
    }
    assert_eq!(
        val(target(&ns, f(val(rhs), "value"), &Json::str("Z"))),
        &Json::str("2")
    );
    if let Some(left) = left {
        assert_eq!(
            val(target(&ns, f(val(lhs), "value"), &Json::str("Z"))),
            &Json::str(left)
        );
        let residual = f(own_part(body), "residual");
        assert_eq!(
            val(target(&ns, residual, &Json::str("Z"))),
            &Json::str(if decision == "refuted" { "1" } else { "0" })
        );
        assert_eq!(
            val(target(&ns, f(val(evaluation), "value"), &Json::str("Bool"))),
            &Json::Bool(decision == "established")
        );
        let proofs: Vec<_> = arr(f(answer, "evidence"))
            .iter()
            .map(|r| val(target(&ns, r, &Json::str("Evidence"))))
            .collect();
        let evaluated = proofs
            .iter()
            .find(|e| f(e, "kind") == &Json::str("evaluation"))
            .unwrap();
        let data = f(evaluated, "data");
        assert_eq!(f(data, "lhs"), f(val(lhs), "value"));
        assert_eq!(f(data, "rhs"), f(val(rhs), "value"));
        assert_eq!(f(data, "residual"), residual);
        let counterexamples: Vec<_> = proofs
            .iter()
            .filter(|e| f(e, "kind") == &Json::str("counterexample"))
            .collect();
        assert_eq!(counterexamples.len(), usize::from(decision == "refuted"));
        for example in counterexamples {
            let data = f(example, "data");
            assert_eq!(f(data, "left"), f(val(lhs), "value"));
            assert_eq!(f(data, "right"), f(val(rhs), "value"));
            binding(&ns, f(data, "bindings"));
            assert!(arr(f(data, "facts")).contains(&fact(
                "q",
                Some("Reservations.State.free"),
                Some("q-free")
            )));
        }
        assert!(arr(f(answer, "reasons")).is_empty());
    } else {
        assert!(!obj(val(lhs)).contains_key("value"));
        assert!(!obj(val(evaluation)).contains_key("value"));
        assert!(!obj(own_part(body)).contains_key("residual"));
        let reasons = arr(f(answer, "reasons"));
        assert!(!reasons.is_empty());
        for reason in reasons {
            assert_eq!(f(reason, "code"), &Json::str("missing_observation"));
            assert_eq!(
                f(reason, "missing"),
                &Json::Arr(vec![fact("q", Some("Reservations.State.free"), None)])
            );
            assert!(!arr(f(reason, "dependencies")).is_empty());
            for reference in arr(f(reason, "dependencies")) {
                let source = target(&ns, reference, &Json::str("Expression"));
                let position = span(f(val(source), "location"));
                assert_eq!(
                    &checked.sources().law().bytes()[position.0..position.1],
                    b"e.to.free"
                );
            }
        }
        assert!(
            arr(f(answer, "evidence")).is_empty(),
            "欠測を観測反例へ昇格しない"
        );
        assert!(
            checked.archmap().snapshots[0]
                .subjects
                .iter()
                .any(|s| s.id == "q")
        );
    }
    assert_occurrences(checked, &wire, missing);
    assert_support(checked, &wire, uri);
    scopes(&wire, missing);
    dag(&wire);
}

fn run_case(
    law: &[u8],
    map: &[u8],
    decision: &str,
    left: Option<&str>,
    uri: Option<&str>,
) -> ObservedEvaluation {
    let checked = check_inputs(sources(law, map), &mut quiet()).unwrap();
    let result = evaluate_observed_bytes(sources(law, map), &[ASK], &mut quiet()).unwrap();
    unchanged(&checked, result.prepared().inputs(), law, map);
    assert_case(&result, decision, left, uri);
    result
}

#[test]
fn reservations_original_bytes_establish_conserved_and_keep_checked_tables() {
    let bytes = run_case(LAW, MAP, "established", Some("2"), None);
    let checked = check_inputs(sources(LAW, MAP), &mut quiet()).unwrap();
    let prepared = prepare_checked_observed(checked, &[ASK], &mut quiet()).unwrap();
    let from_checked = evaluate_observed(prepared, &mut quiet()).unwrap();
    assert_eq!(bytes.wire(), from_checked.wire());
}

#[test]
fn reservations_q_free_two_refutes_with_original_three_two_and_residual_one() {
    run_case(LAW, &q_free(Some("2")), "refuted", Some("3"), None);
}

#[test]
fn reservations_absent_q_free_keeps_subject_missing_slot_and_original_expression() {
    run_case(LAW, &q_free(None), "undetermined", None, None);
}

fn compare_spelling(map: &[u8], decision: &str, left: Option<&str>) {
    let explicit = explicit_law();
    let short = run_case(LAW, map, decision, left, None);
    let long = run_case(&explicit, map, decision, left, None);
    let a = short.prepared().inputs();
    let b = long.prepared().inputs();
    assert_eq!(a.definitions(), b.definitions());
    assert_eq!(a.archmap().snapshots, b.archmap().snapshots);
    assert_eq!(a.archmap().vocabularies, b.archmap().vocabularies);
    assert_eq!(a.archmap().model_digest, b.archmap().model_digest);
    assert_ne!(a.sources().law().bytes(), b.sources().law().bytes());
    assert_ne!(a.law().model_digest, b.law().model_digest);
    let body_span = |c: &CheckedInputs| {
        let Signature::Law { body, .. } = &c.law().declarations["Reservations.conserved"].signature
        else {
            panic!("Law")
        };
        c.law().exprs[*body].span
    };
    assert_ne!(body_span(a), body_span(b), "別原文の元位置を同一化しない");
    let short = short.wire();
    let long = long.wire();
    assert_eq!(f(&short, "status"), f(&long, "status"));
    assert_eq!(
        f(&arr(f(&short, "answers"))[0], "scope"),
        f(&arr(f(&long, "answers"))[0], "scope")
    );
    assert_eq!(f(&short, "vocabularies"), f(&long, "vocabularies"));
}

#[test]
fn reservations_explicit_true_preserves_established_spelling_and_own_occurrences() {
    compare_spelling(MAP, "established", Some("2"));
}

#[test]
fn reservations_explicit_true_preserves_refuted_spelling_and_own_occurrences() {
    compare_spelling(&q_free(Some("2")), "refuted", Some("3"));
}

#[test]
fn reservations_explicit_true_preserves_missing_spelling_and_own_occurrences() {
    compare_spelling(&q_free(None), "undetermined", None);
}

fn provenance(moved: bool) -> Vec<u8> {
    let (id, uri, revision, start, end) = if moved {
        ("relocated", "urn:fixture:reservations:moved", "r2", 23, 29)
    } else {
        ("model", "urn:fixture:reservations", "r1", 3, 9)
    };
    std::str::from_utf8(MAP).unwrap()
        .replace("\"sources\": []", &format!(r#""sources": [{{"id":"src","uri":"{uri}","revision":"{revision}","digest":"sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"}}]"#))
        .replace("\"locations\": []", &format!(r#""locations": [{{"source":"src","path":"reservations.model","span":[{start},{end}]}}]"#))
        .replace("\"model\"", &format!("\"{id}\""))
        .into_bytes()
}

#[test]
fn reservations_provenance_relocation_preserves_judgment_and_tracks_new_source() {
    let a = run_case(
        LAW,
        &provenance(false),
        "established",
        Some("2"),
        Some("urn:fixture:reservations"),
    );
    let b = run_case(
        LAW,
        &provenance(true),
        "established",
        Some("2"),
        Some("urn:fixture:reservations:moved"),
    );
    let a = a.prepared().inputs();
    let b = b.prepared().inputs();
    assert_eq!(a.definitions(), b.definitions());
    assert_eq!(a.law().model_digest, b.law().model_digest);
    assert_ne!(a.archmap().model_digest, b.archmap().model_digest);
    assert_ne!(a.archmap().bytes_digest, b.archmap().bytes_digest);
    for (before, after) in a.archmap().snapshots[0]
        .subjects
        .iter()
        .zip(&b.archmap().snapshots[0].subjects)
    {
        assert_eq!(before.id, after.id);
        assert_eq!(before.ty, after.ty);
        assert_eq!(before.fields.len(), after.fields.len());
        for (left, right) in before.fields.iter().zip(&after.fields) {
            assert_eq!(left.name, right.name);
            assert_eq!(left.ty, right.ty);
            match (&left.slot, &right.slot) {
                (
                    Slot::Known {
                        atom: a, value: av, ..
                    },
                    Slot::Known {
                        atom: b, value: bv, ..
                    },
                ) => {
                    assert_eq!(a, b);
                    assert_eq!(av, bv);
                }
                (Slot::Missing, Slot::Missing) => {}
                _ => panic!("由来だけの移動は既知値/参照/欠測を変えない"),
            }
        }
    }
}
