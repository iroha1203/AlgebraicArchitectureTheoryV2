//! Bool欠測の共有補完を独立三入力から検査し、case whole・型・元slotと支持を照合する。
mod common;
use archsig::{
    canonical::Json,
    definition::check_definitions_controlled,
    law::model::Signature,
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
fn original_body_source<'a>(ns: &BTreeMap<&str, &'a Json>, evaluation: &Json) -> &'a Json {
    let source = if let Some(instance) = aggregate_instance(ns, evaluation) {
        target(ns, f(val(instance), "body"), &Json::str("Expression"))
    } else {
        expression(ns, evaluation)
    };
    assert_eq!(f(val(source), "kind"), &Json::str("source"));
    source
}
fn part(evaluation: &Json) -> &Json {
    let parts = arr(f(val(evaluation), "parts"));
    assert_eq!(parts.len(), 1);
    &parts[0]
}

fn run(inputs: InputSources, asks: &[&str]) -> (Json, CheckedInputs) {
    let checked = check_inputs(inputs.clone(), &mut quiet())
        .unwrap_or_else(|e| panic!("入力: {:?}", e.issues()));
    let evaluated = evaluate_observed_bytes(inputs.clone(), asks, &mut quiet())
        .unwrap_or_else(|e| panic!("評価: {e:?}"));
    assert_eq!(
        evaluated.prepared().inputs().sources().archmap().bytes(),
        inputs.archmap().bytes(),
        "補完で元ArchMap byteを変更しない"
    );
    assert_eq!(
        evaluated.prepared().inputs().archmap().snapshots,
        checked.archmap().snapshots,
        "補完値を観測Atomや既知slotへ追加しない"
    );
    let wire = evaluated.wire();
    audit(&wire, &checked);
    (wire, checked)
}
fn output<'a>(wire: &'a Json, id: &str, ty: &Json, expected: Json) -> &'a Json {
    let a = answer(wire, id);
    assert_eq!(
        f(a, "status"),
        &Json::str("established"),
        "{id}; issues: {:?}",
        f(wire, "issues")
    );
    assert!(
        !obj(a).contains_key("claim"),
        "Boolも値の問いはclaimを持たない"
    );
    assert_eq!(
        val(target(&index(wire), f(f(a, "outputs"), "value"), ty)),
        &expected,
        "{id}"
    );
    a
}
fn root<'a>(wire: &'a Json, id: &str) -> &'a Json {
    target(
        &index(wire),
        f(f(answer(wire, id), "outputs"), "evaluation"),
        &Json::str("Evaluation"),
    )
}
fn source<'a>(checked: &'a CheckedInputs, at: (usize, usize)) -> &'a [u8] {
    &checked.sources().law().bytes()[at.0..at.1]
}
fn declared_body(checked: &CheckedInputs, name: &str) -> usize {
    let (Signature::View { body, .. } | Signature::Law { body, .. }) =
        &checked.law().declarations[name].signature
    else {
        panic!("view/law")
    };
    *body
}

fn ty(kind: &str, item: Json) -> Json {
    Json::Arr(vec![Json::str(kind), item])
}
fn reference(snapshot: &str, subject: &str) -> Json {
    Json::Arr(vec![Json::str(snapshot), Json::str(subject)])
}
fn children<'a>(ns: &BTreeMap<&str, &'a Json>, evaluation: &Json) -> Vec<&'a Json> {
    arr(f(part(evaluation), "children"))
        .iter()
        .map(|r| target(ns, r, &Json::str("Evaluation")))
        .collect()
}
fn evaluations_at<'a>(wire: &'a Json, at: (usize, usize)) -> Vec<&'a Json> {
    let ns = index(wire);
    arr(f(wire, "nodes"))
        .iter()
        .filter(|n| {
            f(n, "type") == &Json::str("Evaluation")
                && aggregate_instance(&ns, n).is_none()
                && evaluation_span(&ns, n) == at
        })
        .collect()
}
fn evidence<'a>(ns: &BTreeMap<&str, &'a Json>, root: &Json, kind: &str) -> Vec<&'a Json> {
    reached(ns, &[root])
        .iter()
        .map(|id| ns[id.as_str()])
        .filter(|n| f(n, "type") == &Json::str("Evidence") && f(val(n), "kind") == &Json::str(kind))
        .collect()
}
fn check_claim(wire: &Json, id: &str, status: &str) {
    let a = answer(wire, id);
    assert_eq!(f(a, "status"), &Json::str(status));
    let ns = index(wire);
    let claim = target(&ns, f(a, "claim"), &Json::str("Proposition"));
    assert_eq!(f(val(claim), "predicate"), &Json::str("law_holds"));
    let operands = arr(f(val(claim), "operands"));
    assert_eq!(operands.len(), 1);
    let instance = target(&ns, &operands[0], &Json::str("LawInstance"));
    target(&ns, f(val(instance), "body"), &Json::str("Expression"));
    assert_eq!(f(claim, "scope"), f(a, "scope"));
    assert_eq!(
        f(val(claim), "quantifiers"),
        f(f(claim, "scope"), "quantifiers")
    );
    assert_eq!(f(f(claim, "judgment"), "status"), &Json::str(status));
    assert!(!arr(f(claim, "evidence")).is_empty());
    assert_eq!(f(f(claim, "judgment"), "evidence"), f(claim, "evidence"));
    for proof in arr(f(claim, "evidence")) {
        target(&ns, proof, &Json::str("Evidence"));
    }
}

#[derive(Clone, Copy)]
enum Shape {
    One,
    Fields,
    Snapshots,
    KnownFalse,
}
fn fixture(script: &str, shape: Shape, moved: bool, reverse: bool) -> InputSources {
    use common::{definition_json, entity_json, field_json, vocabulary_json};
    let entity = entity_json(
        "Completion.Sample",
        "[]",
        &format!(
            "[{},{}]",
            field_json("h", r#""Bool""#),
            field_json("k", r#""Bool""#)
        ),
    );
    let definitions = definition_json(&format!(
        "[{}]",
        vocabulary_json("Completion", &format!("[{entity}]"), "[]")
    ));
    let checked =
        check_definitions_controlled(&[("definition0", definitions.as_bytes())], &mut quiet())
            .unwrap();
    let digest = &checked.vocabularies["Completion"].digest;
    let law = format!(
        r#"law "archsig.law/2" semantics "archsig/0.6.0"; reading Calc {{ use vocabulary Completion version "1" digest "{digest}"; {script} }}"#
    );
    let suffix = if moved { "_moved" } else { "" };
    let shift = if moved { 10 } else { 0 };
    let mut origins = vec![];
    for (snapshot, mode) in [("v", "specification"), ("w", "proposed")] {
        for (kind, start) in [("snapshot", 0), ("subjects", 2), ("values", 4)] {
            origins.push(format!(r#"{{"id":"{snapshot}_{kind}{suffix}","mode":"{mode}","method":"小さいBool観測モデル。","locations":[{{"source":"scan","path":"{snapshot}.{kind}.model","span":[{},{}]}}]}}"#,start+shift,start+shift+1));
        }
    }
    let mut v_subjects = vec![format!(
        r#"{{"id":"item","type":"Completion.Sample","origin":"v_subjects{suffix}"}}"#
    )];
    let mut v_atoms = vec![];
    if !matches!(shape, Shape::Fields) {
        v_atoms.push(format!(r#"{{"id":"knownk","subject":"item","field":"Completion.Sample.k","value":false,"origin":"v_values{suffix}"}}"#));
    }
    if matches!(shape, Shape::KnownFalse) {
        v_subjects.push(format!(
            r#"{{"id":"peer","type":"Completion.Sample","origin":"v_subjects{suffix}"}}"#
        ));
        for (id, field) in [("peerh", "h"), ("peerk", "k")] {
            v_atoms.push(format!(r#"{{"id":"{id}","subject":"peer","field":"Completion.Sample.{field}","value":false,"origin":"v_values{suffix}"}}"#));
        }
    }
    if reverse {
        v_subjects.reverse();
    }
    let v_subjects = v_subjects.join(",");
    let v_atoms = v_atoms.join(",");
    let first = format!(
        r#"{{"id":"v","origin":"v_snapshot{suffix}","subjects":[{v_subjects}],"atoms":[{v_atoms}]}}"#
    );
    let mut snapshots = vec![first];
    if matches!(shape, Shape::Snapshots) {
        snapshots.push(format!(r#"{{"id":"w","origin":"w_snapshot{suffix}","subjects":[{{"id":"item","type":"Completion.Sample","origin":"w_subjects{suffix}"}}],"atoms":[{{"id":"knownk","subject":"item","field":"Completion.Sample.k","value":false,"origin":"w_values{suffix}"}}]}}"#));
    }
    let snapshots = snapshots.join(",");
    let origins = origins.join(",");
    let revision = if moved { "r2" } else { "r1" };
    let uri = if moved {
        "urn:fixture:bool-completions:relocated"
    } else {
        "urn:fixture:bool-completions"
    };
    let map = format!(
        r#"{{"format":"archsig.archmap/2","semantics":"archsig/0.6.0","vocabularies":[{{"namespace":"Completion","version":"1","digest":"{digest}"}}],"sources":[{{"id":"scan","uri":"{uri}","revision":"{revision}","digest":"sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"}}],"origins":[{origins}],"snapshots":[{snapshots}]}}"#
    );
    InputSources::from_bytes(
        vec![definitions.into_bytes()],
        law.into_bytes(),
        map.into_bytes(),
    )
}
fn slot(snapshot: &str, field: &str) -> Json {
    Json::obj([
        ("snapshot", Json::str(snapshot)),
        ("subject", Json::str("item")),
        ("field", Json::str(format!("Completion.Sample.{field}"))),
    ])
}
fn audit(wire: &Json, checked: &CheckedInputs) {
    let ns = index(wire);
    let mut earlier = BTreeSet::new();
    for node in arr(f(wire, "nodes")) {
        let mut links = vec![];
        refs(node, &mut links);
        for link in links {
            assert!(earlier.contains(link.as_str()), "既出Ref: {link}");
        }
        assert!(earlier.insert(text(f(node, "id"))));
        if f(node, "type") != &Json::str("Proposition") {
            assert!(!obj(node).contains_key("judgment"));
        }
        if let Some(payload) = obj(node).get("value") {
            let mut links = vec![];
            refs(payload, &mut links);
            for link in links {
                assert_ne!(f(ns[link.as_str()], "state"), &Json::str("blocked"));
                assert!(!obj(ns[link.as_str()]).contains_key("partial"));
            }
        }
        for fact in arr(f(node, "support")) {
            assert!(arr(f(f(node, "scope"), "snapshots")).contains(f(fact, "snapshot")));
            assert!(arr(f(f(node, "scope"), "modes")).contains(&Json::str(
                if f(fact, "snapshot") == &Json::str("v") {
                    "specification"
                } else {
                    "proposed"
                }
            )));
            let snapshot = checked
                .archmap()
                .snapshots
                .iter()
                .find(|s| s.id == text(f(fact, "snapshot")))
                .unwrap();
            let subject = snapshot
                .subjects
                .iter()
                .find(|s| s.id == text(f(fact, "subject")))
                .unwrap();
            let (origin_id, kind, start) = if let Some(field) = obj(fact).get("field") {
                let field = subject
                    .fields
                    .iter()
                    .find(|s| s.name == text(field))
                    .unwrap();
                match &field.slot {
                    archsig::archmap::Slot::Known { atom, origin, .. } => {
                        assert_eq!(f(fact, "atom"), &Json::str(atom));
                        (origin, "values", 4)
                    }
                    archsig::archmap::Slot::Missing => {
                        assert!(!obj(fact).contains_key("atom"));
                        (&subject.origin, "subjects", 2)
                    }
                }
            } else {
                assert!(!obj(fact).contains_key("atom"));
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
                    "urn:fixture:bool-completions"
                } else {
                    "urn:fixture:bool-completions:relocated"
                }
            );
        }
        if f(node, "type") == &Json::str("Expression")
            && f(val(node), "kind") == &Json::str("source")
        {
            let at = span(f(val(node), "location"));
            assert!(at.0 < at.1 && at.1 <= checked.sources().law().bytes().len());
            assert_eq!(span(f(f(node, "rule"), "location")), at);
        }
        for q in arr(f(f(node, "scope"), "quantifiers")) {
            if let Some(domain) = obj(q).get("domain") {
                let domain = target(&ns, domain, &Json::str("Domain"));
                assert_eq!(f(val(domain), "type"), f(q, "type"));
            }
        }
        if f(node, "type") == &Json::str("Domain") && f(val(node), "kind") == &Json::str("finite") {
            for member in arr(f(val(node), "elements")) {
                val(target(&ns, member, f(val(node), "type")));
            }
        }
    }
    for answer in arr(f(wire, "answers")) {
        let mut links = vec![];
        refs(answer, &mut links);
        for link in links {
            assert!(ns.contains_key(link.as_str()));
        }
    }
}
struct Case<'a> {
    assignment: Vec<bool>,
    evaluation: &'a Json,
}
fn bool_value(value: &Json) -> bool {
    let Json::Bool(value) = value else {
        panic!("Boolの原始encoding")
    };
    *value
}
fn live_evaluations<'a>(ns: &BTreeMap<&str, &'a Json>, root: &'a Json) -> Vec<&'a Json> {
    let mut todo = vec![root];
    let mut seen = BTreeSet::new();
    let mut values = vec![];
    while let Some(evaluation) = todo.pop() {
        if seen.insert(text(f(evaluation, "id"))) {
            values.push(evaluation);
            for part in arr(f(val(evaluation), "parts")) {
                for child in arr(f(part, "children")) {
                    todo.push(target(ns, child, &Json::str("Evaluation")));
                }
            }
        }
    }
    values
}
fn assert_missing_fields(wire: &Json, id: &str, expected: &[Json]) {
    let mut fields = BTreeSet::new();
    for reason in arr(f(answer(wire, id), "reasons")) {
        if f(reason, "code") == &Json::str("missing_observation") {
            assert!(!arr(f(reason, "dependencies")).is_empty());
            for missing in arr(f(reason, "missing")) {
                assert!(!obj(missing).contains_key("atom"));
                fields.insert(missing.canonical());
            }
        }
    }
    assert_eq!(
        fields,
        expected
            .iter()
            .map(Json::canonical)
            .collect::<BTreeSet<_>>(),
        "元slotの欠測を保持"
    );
}
fn case_assignment(ns: &BTreeMap<&str, &Json>, domain: &Json, evaluation: &Json) -> Vec<bool> {
    let mut anchors = vec![expression(ns, evaluation)];
    if let Some(instance) = aggregate_instance(ns, evaluation) {
        anchors.push(target(
            ns,
            f(val(instance), "body"),
            &Json::str("Expression"),
        ));
    }
    let selected = anchors
        .iter()
        .flat_map(|source| arr(f(source, "arguments")))
        .filter(|r| arr(f(val(domain), "elements")).contains(r))
        .map(Json::canonical)
        .collect::<BTreeSet<_>>();
    assert_eq!(
        selected.len(),
        1,
        "case whole/元body Sourceから実assignment memberへ戻る"
    );
    let member_ref = arr(f(val(domain), "elements"))
        .iter()
        .find(|r| selected.contains(&r.canonical()))
        .unwrap();
    let member = target(ns, member_ref, f(val(domain), "type"));
    if f(val(domain), "type") == &Json::str("Bool") {
        vec![bool_value(val(member))]
    } else {
        arr(val(member)).iter().map(bool_value).collect()
    }
}
fn assignment_domain<'a>(ns: &BTreeMap<&str, &'a Json>, root: &Json) -> &'a Json {
    let arguments = arr(f(root, "arguments"));
    assert_eq!(&arguments[0], f(val(root), "expression"));
    let domain = target(ns, &arguments[1], &Json::str("Domain"));
    assert_eq!(
        arr(f(domain, "arguments")).first(),
        Some(f(val(root), "expression"))
    );
    domain
}
fn assert_completed_field(ns: &BTreeMap<&str, &Json>, evaluation: &Json, expected: bool) {
    let value = target(ns, f(val(evaluation), "value"), &Json::str("Bool"));
    assert_eq!(val(value), &Json::Bool(expected));
    let source = expression(ns, evaluation);
    assert_eq!(f(f(value, "rule"), "kind"), &Json::str("law"));
    assert_eq!(f(f(value, "rule"), "location"), f(val(source), "location"));
    assert!(
        arr(f(value, "support")).is_empty(),
        "補完値を観測事実にしない"
    );
    let arguments = arr(f(value, "arguments"));
    assert_eq!(arguments.len(), 3);
    assert_eq!(&arguments[0], f(val(evaluation), "expression"));
    assert_eq!(
        val(target(
            ns,
            &arguments[1],
            &ty("Ref", Json::str("Completion.Sample"))
        )),
        &reference("v", "item")
    );
    let projection = target(ns, &arguments[2], &Json::str("Bool"));
    assert_eq!(val(projection), &Json::Bool(expected));
    assert_eq!(f(f(projection, "rule"), "kind"), &Json::str("construction"));
    let inputs = arr(f(projection, "arguments"));
    assert_eq!(inputs.len(), 4);
    target(ns, &inputs[0], &Json::str("Expression"));
    let domain = target(ns, &inputs[1], &Json::str("Domain"));
    assert!(arr(f(val(domain), "elements")).contains(&inputs[2]));
    target(ns, &inputs[2], f(val(domain), "type"));
    target(ns, &inputs[3], &Json::str("Expression"));
    for edge in &inputs[..3] {
        assert!(
            arr(f(source, "arguments")).contains(edge),
            "元field Sourceから実補完域/選択memberへ戻る"
        );
    }
    assert!(arr(f(source, "arguments")).contains(&arguments[2]));
}
fn assert_cases<'a>(
    wire: &'a Json,
    id: &str,
    fields: &[Json],
    wanted: &[(Vec<bool>, bool)],
) -> Vec<Case<'a>> {
    let ns = index(wire);
    let root = root(wire, id);
    assert_eq!(f(f(root, "scope"), "domain"), &Json::str("all_completions"));
    assert_eq!(
        f(f(answer(wire, id), "scope"), "domain"),
        &Json::str("all_completions")
    );
    assert_missing_fields(wire, id, fields);
    let cases = children(&ns, root);
    assert_eq!(cases.len(), wanted.len());
    let case_refs = arr(f(part(root), "children"))
        .iter()
        .map(Json::canonical)
        .collect::<BTreeSet<_>>();
    let proofs = evidence(&ns, answer(wire, id), "finite_exhaustion")
        .into_iter()
        .filter(|p| {
            arr(f(f(val(p), "data"), "instances"))
                .iter()
                .map(Json::canonical)
                .collect::<BTreeSet<_>>()
                == case_refs
        })
        .collect::<Vec<_>>();
    let domain = assignment_domain(&ns, root);
    if wanted.iter().all(|(_, result)| *result == wanted[0].1) {
        assert_eq!(proofs.len(), 1, "同値な補完case whole全件のcoverage証拠");
        let proof = f(val(proofs[0]), "data");
        assert_eq!(f(proof, "checked"), &Json::Nat(wanted.len() as u64));
        assert_eq!(
            target(&ns, f(proof, "domain"), &Json::str("Domain")),
            domain
        );
    } else {
        assert!(proofs.is_empty(), "異なる結果に全case同値の証拠を作らない");
    }
    assert_eq!(f(val(domain), "kind"), &Json::str("finite"));
    let t = if fields.len() == 1 {
        Json::str("Bool")
    } else {
        Json::Arr(
            std::iter::once(Json::str("Tuple"))
                .chain(fields.iter().map(|_| Json::str("Bool")))
                .collect(),
        )
    };
    assert_eq!(f(val(domain), "type"), &t);
    let assignment_of = |value: &Json| {
        if fields.len() == 1 {
            vec![bool_value(value)]
        } else {
            arr(value).iter().map(bool_value).collect::<Vec<_>>()
        }
    };
    let domain_rows = arr(f(val(domain), "elements"))
        .iter()
        .map(|r| {
            let member = target(&ns, r, &t);
            assert_eq!(
                f(f(member, "rule"), "kind"),
                &Json::str("construction"),
                "補完代入を観測Atomへ変えない"
            );
            assignment_of(val(member))
        })
        .collect::<BTreeSet<_>>();
    assert_eq!(
        domain_rows,
        wanted
            .iter()
            .map(|(a, _)| a.clone())
            .collect::<BTreeSet<_>>()
    );
    assert_eq!(arr(f(val(domain), "elements")).len(), wanted.len());
    let mut result = vec![];
    let mut seen = BTreeSet::new();
    for evaluation in cases {
        assert_eq!(
            f(val(original_body_source(&ns, evaluation)), "location"),
            f(val(original_body_source(&ns, root)), "location"),
            "補完caseは元root AST出現を保つ"
        );
        let assignment = case_assignment(&ns, domain, evaluation);
        assert!(seen.insert(assignment.clone()), "caseを欠落/重複しない");
        let expected = wanted.iter().find(|(a, _)| *a == assignment).unwrap().1;
        assert_eq!(
            val(target(&ns, f(val(evaluation), "value"), &Json::str("Bool"))),
            &Json::Bool(expected)
        );
        assert_eq!(
            f(f(evaluation, "scope"), "domain"),
            &Json::str("all_completions")
        );
        result.push(Case {
            assignment,
            evaluation,
        });
    }
    assert_eq!(seen, domain_rows);
    result
}
fn assert_pair(wire: &Json, id: &str, fields: &[Json]) {
    let ns = index(wire);
    let pairs = evidence(&ns, answer(wire, id), "completion_pair");
    assert_eq!(pairs.len(), 1);
    let pair = f(val(pairs[0]), "data");
    assert_eq!(f(pair, "fields"), &Json::Arr(fields.to_vec()));
    let case_refs = arr(f(part(root(wire, id)), "children"));
    let domain = assignment_domain(&ns, root(wire, id));
    let mut assignments = vec![];
    let mut results = vec![];
    for (binding_key, result_key) in [("first", "first_result"), ("second", "second_result")] {
        let values = arr(f(pair, binding_key));
        assert_eq!(values.len(), fields.len());
        let assignment = values
            .iter()
            .map(|r| {
                let value = target(&ns, r, &Json::str("Bool"));
                assert_eq!(f(f(value, "rule"), "kind"), &Json::str("construction"));
                bool_value(val(value))
            })
            .collect::<Vec<_>>();
        let evaluation = target(&ns, f(pair, result_key), &Json::str("Evaluation"));
        assert!(case_refs.contains(f(pair, result_key)));
        assert_eq!(
            assignment,
            case_assignment(&ns, domain, evaluation),
            "補完対の代入と実whole結果を同じcaseへ照合"
        );
        assignments.push(assignment);
        results.push(bool_value(val(target(
            &ns,
            f(val(evaluation), "value"),
            &Json::str("Bool"),
        ))));
    }
    assert_ne!(assignments[0], assignments[1]);
    assert_ne!(results[0], results[1]);
}

#[test]
fn bool_completions_share_slots_across_expressions_and_calls() {
    let script = r#"
view tautology(s:Sample): Bool = s.h or not s.h;
view branch(s:Sample): Bool = if s.h then s.h else not s.h;
view inequality(s:Sample): Bool = s.h!=s.h;
view helper(s:Sample): Bool = let held=s.h in held;
view shared(s:Sample): Bool = forall b:Bool . helper(s)=s.h;
law required inequality_law(s:Sample): s.h!=s.h;
"#;
    let asks = [
        "a=evaluate(Calc.tautology,s=@v/item)",
        "b=evaluate(Calc.branch,s=@v/item)",
        "c=evaluate(Calc.inequality,s=@v/item)",
        "d=evaluate(Calc.shared,s=@v/item)",
        "e=check(Calc.inequality_law,s=@v/item)",
    ];
    let (wire, checked) = run(fixture(script, Shape::One, false, false), &asks);
    assert_eq!(
        f(&wire, "status"),
        &Json::str("complete"),
        "issues: {:?}",
        f(&wire, "issues")
    );
    for (id, v) in [("a", true), ("b", true), ("c", false), ("d", true)] {
        output(&wire, id, &Json::str("Bool"), Json::Bool(v));
    }
    check_claim(&wire, "e", "refuted");
    let ns = index(&wire);
    for (id, result) in [
        ("a", true),
        ("b", true),
        ("c", false),
        ("d", true),
        ("e", false),
    ] {
        let cases = assert_cases(
            &wire,
            id,
            &[slot("v", "h")],
            &[(vec![false], result), (vec![true], result)],
        );
        for case in cases {
            let fields = live_evaluations(&ns, case.evaluation)
                .into_iter()
                .filter(|n| source(&checked, evaluation_span(&ns, n)) == b"s.h")
                .collect::<Vec<_>>();
            assert!(!fields.is_empty());
            for field in fields {
                assert_completed_field(&ns, field, case.assignment[0]);
            }
        }
    }
}

#[test]
fn bool_completion_slots_are_independent_across_fields_and_snapshots() {
    for (shape, script, ask, fields) in [
        (
            Shape::Fields,
            "view pair(s:Sample): Bool = s.h=s.k;",
            "a=evaluate(Calc.pair,s=@v/item)",
            vec![slot("v", "h"), slot("v", "k")],
        ),
        (
            Shape::Snapshots,
            "view pair(s:Sample,t:Sample): Bool = s.h=t.h;",
            "a=evaluate(Calc.pair,s=@v/item,t=@w/item)",
            vec![slot("v", "h"), slot("w", "h")],
        ),
    ] {
        let (wire, _) = run(fixture(script, shape, false, false), &[ask]);
        assert_eq!(f(&wire, "status"), &Json::str("partial"));
        assert_eq!(f(answer(&wire, "a"), "status"), &Json::str("undetermined"));
        assert!(!obj(f(answer(&wire, "a"), "outputs")).contains_key("value"));
        assert_cases(
            &wire,
            "a",
            &fields,
            &[
                (vec![false, false], true),
                (vec![false, true], false),
                (vec![true, false], false),
                (vec![true, true], true),
            ],
        );
        assert_pair(&wire, "a", &fields);
    }
}

#[test]
fn bool_completion_cases_quantify_whole_law_families_before_aggregation() {
    let script = r#"law required shared_family(s:Sample,b:Bool): b=s.h;"#;
    let (wire, checked) = run(
        fixture(script, Shape::One, false, false),
        &["a=check(Calc.shared_family,s=@v/item)"],
    );
    assert_eq!(f(&wire, "status"), &Json::str("complete"));
    check_claim(&wire, "a", "refuted");
    let ns = index(&wire);
    let claim = target(
        &ns,
        f(answer(&wire, "a"), "claim"),
        &Json::str("Proposition"),
    );
    assert!(
        arr(f(claim, "evidence")).iter().all(|r| {
            f(val(target(&ns, r, &Json::str("Evidence"))), "kind") != &Json::str("counterexample")
        }),
        "各caseで異なる反例bを観測された単一反例として合成しない"
    );
    let cases = assert_cases(
        &wire,
        "a",
        &[slot("v", "h")],
        &[(vec![false], false), (vec![true], false)],
    );
    let case_propositions = arr(f(root(&wire, "a"), "arguments"))
        .iter()
        .map(|r| ns[text(f(r, "node"))])
        .filter(|n| f(n, "type") == &Json::str("Proposition"))
        .collect::<Vec<_>>();
    assert_eq!(case_propositions.len(), cases.len());
    let mut matched_propositions = BTreeSet::new();
    let mut counter_bindings = BTreeSet::new();
    for case in cases {
        let whole = aggregate_instance(&ns, case.evaluation).expect("補完ごとのLaw族whole");
        assert_eq!(f(val(whole), "name"), &Json::str("Calc.shared_family"));
        let whole_ref = &arr(f(case.evaluation, "arguments"))[0];
        let case_ref = Json::obj([("node", f(case.evaluation, "id").clone())]);
        let propositions = case_propositions
            .iter()
            .copied()
            .filter(|p| arr(f(p, "arguments")).get(1) == Some(&case_ref))
            .collect::<Vec<_>>();
        assert_eq!(
            propositions.len(),
            1,
            "集約の実辺から同じcase wholeへの命題を一意に選ぶ"
        );
        let proposition = propositions[0];
        assert!(matched_propositions.insert(text(f(proposition, "id"))));
        assert_eq!(
            f(proposition, "arguments"),
            &Json::Arr(vec![whole_ref.clone(), case_ref])
        );
        assert_eq!(f(val(proposition), "predicate"), &Json::str("law_holds"));
        assert_eq!(
            f(val(proposition), "operands"),
            &Json::Arr(vec![whole_ref.clone()])
        );
        assert_eq!(f(proposition, "scope"), f(case.evaluation, "scope"));
        assert_eq!(
            f(f(proposition, "judgment"), "status"),
            &Json::str("refuted")
        );
        assert_eq!(
            f(f(proposition, "judgment"), "evidence"),
            f(proposition, "evidence")
        );
        let body = target(&ns, f(val(whole), "body"), &Json::str("Expression"));
        assert_eq!(
            f(val(body), "parameters"),
            &Json::Arr(vec![Json::obj([
                ("name", Json::str("b")),
                ("type", Json::str("Bool"))
            ])])
        );
        let fixed = arr(f(val(whole), "bindings"));
        assert_eq!(fixed.len(), 1);
        assert_eq!(f(&fixed[0], "name"), &Json::str("s"));
        assert_eq!(
            val(target(
                &ns,
                f(&fixed[0], "value"),
                &ty("Ref", Json::str("Completion.Sample"))
            )),
            &reference("v", "item")
        );
        let quantified = arr(f(f(case.evaluation, "scope"), "quantifiers"))
            .iter()
            .find(|q| f(q, "name") == &Json::str("b"))
            .unwrap();
        assert_eq!(f(quantified, "kind"), &Json::str("forall"));
        assert_eq!(f(quantified, "type"), &Json::str("Bool"));
        let domain = target(&ns, f(quantified, "domain"), &Json::str("Domain"));
        assert_eq!(
            arr(f(val(domain), "elements"))
                .iter()
                .map(|r| bool_value(val(target(&ns, r, &Json::str("Bool")))))
                .collect::<BTreeSet<_>>(),
            BTreeSet::from([false, true])
        );
        let rows = children(&ns, case.evaluation);
        assert_eq!(rows.len(), 2);
        let mut row_values = BTreeSet::new();
        for row in rows {
            let bindings = arr(f(val(row), "bindings"));
            assert_eq!(bindings.len(), 2);
            assert_eq!(f(&bindings[0], "name"), &Json::str("s"));
            assert_eq!(f(&bindings[1], "name"), &Json::str("b"));
            let b = bool_value(val(target(
                &ns,
                f(&bindings[1], "value"),
                &Json::str("Bool"),
            )));
            assert!(row_values.insert(b));
            assert_eq!(
                val(target(&ns, f(val(row), "value"), &Json::str("Bool"))),
                &Json::Bool(b == case.assignment[0])
            );
            assert_eq!(source(&checked, evaluation_span(&ns, row)), b"b=s.h");
        }
        assert_eq!(row_values, BTreeSet::from([false, true]));
        let examples = evidence(&ns, proposition, "counterexample");
        let examples = examples
            .into_iter()
            .filter(|e| {
                arr(f(f(val(e), "data"), "bindings"))
                    .iter()
                    .any(|b| f(b, "name") == &Json::str("b"))
            })
            .collect::<Vec<_>>();
        assert!(!examples.is_empty());
        for example in examples {
            let data = f(val(example), "data");
            let b = arr(f(data, "bindings"))
                .iter()
                .find(|b| f(b, "name") == &Json::str("b"))
                .unwrap();
            let b = bool_value(val(target(&ns, f(b, "value"), &Json::str("Bool"))));
            assert_eq!(b, !case.assignment[0]);
            counter_bindings.insert(b);
            assert_ne!(
                val(target(&ns, f(data, "left"), &Json::str("Bool"))),
                val(target(&ns, f(data, "right"), &Json::str("Bool")))
            );
        }
    }
    assert_eq!(matched_propositions.len(), case_propositions.len());
    assert_eq!(
        counter_bindings,
        BTreeSet::from([false, true]),
        "補完ごとに異なる反例bを保持"
    );
}

#[test]
fn bool_completion_pairs_keep_guards_missing_and_provenance() {
    let script = r#"law required gated(s:Sample) when s.h: false;"#;
    let (wire, checked) = run(
        fixture(script, Shape::One, false, false),
        &["a=check(Calc.gated,s=@v/item)"],
    );
    assert_eq!(f(&wire, "status"), &Json::str("partial"));
    check_claim(&wire, "a", "undetermined");
    let ns = index(&wire);
    let cases = assert_cases(
        &wire,
        "a",
        &[slot("v", "h")],
        &[(vec![false], true), (vec![true], false)],
    );
    assert_pair(&wire, "a", &[slot("v", "h")]);
    for case in cases {
        let instance = aggregate_instance(&ns, case.evaluation).expect("元guard付きLaw適用");
        let body_source = original_body_source(&ns, case.evaluation);
        assert_eq!(
            span(f(val(body_source), "location")),
            checked.law().exprs[declared_body(&checked, "Calc.gated")].span
        );
        let guard_source = target(&ns, f(val(instance), "guard"), &Json::str("Expression"));
        assert_eq!(f(val(guard_source), "kind"), &Json::str("source"));
        assert_eq!(
            f(val(case.evaluation), "applicability"),
            &Json::str(if case.assignment[0] {
                "applicable"
            } else {
                "not_applicable"
            })
        );
        let parts = arr(f(val(case.evaluation), "parts"));
        assert_eq!(parts.len(), 2);
        assert_eq!(f(&parts[0], "location"), f(val(guard_source), "location"));
        assert_eq!(f(&parts[1], "location"), f(val(body_source), "location"));
        let guard_children = arr(f(&parts[0], "children"));
        assert_eq!(guard_children.len(), 1);
        let guard_eval = target(&ns, &guard_children[0], &Json::str("Evaluation"));
        assert_eq!(f(val(guard_eval), "expression"), f(val(instance), "guard"));
        assert_eq!(f(val(guard_eval), "value"), f(&parts[0], "value"));
        assert_completed_field(&ns, guard_eval, case.assignment[0]);
        assert_eq!(source(&checked, span(f(&parts[0], "location"))), b"s.h");
        assert_eq!(
            bool_value(val(target(&ns, f(&parts[0], "value"), &Json::str("Bool")))),
            case.assignment[0]
        );
        assert_eq!(source(&checked, span(f(&parts[1], "location"))), b"false");
        if !case.assignment[0] {
            assert!(!obj(&parts[1]).contains_key("value"));
            assert!(arr(f(&parts[1], "children")).is_empty());
        } else {
            let body_children = arr(f(&parts[1], "children"));
            assert_eq!(body_children.len(), 1);
            let body_eval = target(&ns, &body_children[0], &Json::str("Evaluation"));
            assert_eq!(f(val(body_eval), "expression"), f(val(instance), "body"));
            assert_eq!(f(val(body_eval), "value"), f(&parts[1], "value"));
            assert_eq!(
                val(target(&ns, f(val(body_eval), "value"), &Json::str("Bool"))),
                &Json::Bool(false)
            );
        }
    }
    for reverse in [false, true] {
        let (wire, _) = run(
            fixture(
                "law required observed(r:Sample): r.h;",
                Shape::KnownFalse,
                false,
                reverse,
            ),
            &["a=check(Calc.observed)"],
        );
        check_claim(&wire, "a", "refuted");
        assert_missing_fields(&wire, "a", &[slot("v", "h")]);
        let ns = index(&wire);
        assert!(
            evidence(&ns, answer(&wire, "a"), "counterexample")
                .into_iter()
                .any(|e| {
                    let data = f(val(e), "data");
                    arr(f(data, "bindings")).iter().any(|b| {
                        f(b, "name") == &Json::str("r")
                            && val(target(
                                &ns,
                                f(b, "value"),
                                &ty("Ref", Json::str("Completion.Sample")),
                            )) == &reference("v", "peer")
                    }) && arr(f(data, "facts"))
                        .iter()
                        .any(|fact| obj(fact).get("atom") == Some(&Json::str("peerh")))
                })
        );
    }
    let moved_script = "view branch(s:Sample): Bool = if s.h then s.h else not s.h;";
    let (original, _) = run(
        fixture(moved_script, Shape::One, false, false),
        &["a=evaluate(Calc.branch,s=@v/item)"],
    );
    let (moved, moved_checked) = run(
        fixture(moved_script, Shape::One, true, false),
        &["a=evaluate(Calc.branch,s=@v/item)"],
    );
    for wire in [&original, &moved] {
        output(wire, "a", &Json::str("Bool"), Json::Bool(true));
        assert_cases(
            wire,
            "a",
            &[slot("v", "h")],
            &[(vec![false], true), (vec![true], true)],
        );
    }
    assert_eq!(moved_checked.archmap().sources[0].revision, "r2");
    assert!(
        moved_checked
            .archmap()
            .origins
            .iter()
            .all(|o| o.id.ends_with("_moved"))
    );
}

#[test]
fn bool_completion_expression_stops_keep_case_prefixes() {
    let input = fixture(
        r#"
view seed(s:Sample): Unit = unit;
view absent(s:Sample): Bool = s.h;
law required known_false(s:Sample): s.k;
view current(s:Sample): Bool = s.h;
view later(s:Sample): Unit = unit;
"#,
        Shape::One,
        false,
        false,
    );
    let checked = check_inputs(input.clone(), &mut quiet()).unwrap();
    let asks = [
        "seed=evaluate(Calc.seed,s=@v/item)",
        "absent=evaluate(Calc.absent,s=@v/item)",
        "known_false=check(Calc.known_false,s=@v/item)",
        "current=evaluate(Calc.current,s=@v/item)",
        "later=evaluate(Calc.later,s=@v/item)",
    ];
    let count = Rc::new(Cell::new(0));
    let c = count.clone();
    let mut prior_control = Control::new(Limits::default(), move |point| {
        if point == Checkpoint::Expression {
            c.set(c.get() + 1);
        }
        Usage::default()
    });
    let prior = evaluate_observed_bytes(input.clone(), &asks[..3], &mut prior_control)
        .unwrap()
        .wire();
    audit(&prior, &checked);
    output(&prior, "seed", &Json::str("Unit"), Json::Arr(vec![]));
    check_claim(&prior, "known_false", "refuted");
    assert_missing_fields(&prior, "absent", &[slot("v", "h")]);
    assert_pair(&prior, "absent", &[slot("v", "h")]);
    let total = Rc::new(Cell::new(0));
    let c = total.clone();
    let mut baseline_control = Control::new(Limits::default(), move |point| {
        if point == Checkpoint::Expression {
            c.set(c.get() + 1);
        }
        Usage::default()
    });
    let baseline = evaluate_observed_bytes(input.clone(), &asks[..4], &mut baseline_control)
        .unwrap()
        .wire();
    audit(&baseline, &checked);
    let baseline_cases = assert_cases(
        &baseline,
        "current",
        &[slot("v", "h")],
        &[(vec![false], false), (vec![true], true)],
    );
    assert_eq!(baseline_cases.len(), 2);
    assert_pair(&baseline, "current", &[slot("v", "h")]);

    let body_span = checked.law().exprs[declared_body(&checked, "Calc.current")].span;
    assert_eq!(source(&checked, body_span), b"s.h");
    // 実際の保持case数から停止点を選ぶ。実補完列挙/集約/再検査phase内部はprivate試験が担う。
    let wanted = [0, 1, 2];
    let offsets = common::completion_stops::offsets(
        &input,
        &asks,
        count.get(),
        total.get(),
        body_span,
        &wanted,
    );
    for (kind, (&offset, &done)) in offsets.iter().zip(&wanted).enumerate() {
        let at = count.get() + offset;
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
                    if e.get() == at {
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
        let wire = evaluate_observed_bytes(input.clone(), &asks, &mut control)
            .unwrap()
            .wire();
        assert_eq!(f(&wire, "status"), &Json::str("interrupted"));
        audit(&wire, &checked);
        output(&wire, "seed", &Json::str("Unit"), Json::Arr(vec![]));
        check_claim(&wire, "known_false", "refuted");
        for id in ["absent", "known_false"] {
            for key in ["status", "outputs", "scope", "reasons", "evidence"] {
                assert_eq!(f(answer(&wire, id), key), f(answer(&prior, id), key));
            }
        }
        let ns = index(&wire);
        assert_eq!(
            evidence(&ns, answer(&wire, "known_false"), "counterexample"),
            evidence(
                &index(&prior),
                answer(&prior, "known_false"),
                "counterexample"
            )
        );
        for id in ["current", "later"] {
            let a = answer(&wire, id);
            assert_eq!(f(a, "status"), &Json::str("undetermined"));
            assert!(!obj(a).contains_key("claim"));
            assert!(obj(f(a, "outputs")).is_empty());
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
        let completed = evaluations_at(&wire, body_span)
            .into_iter()
            .filter(|e| obj(val(e)).contains_key("value"))
            .collect::<Vec<_>>();
        assert_eq!(completed.len(), done);
        let mut values = BTreeSet::new();
        for evaluation in completed {
            let value = target(&ns, f(val(evaluation), "value"), &Json::str("Bool"));
            let assigned = bool_value(val(value));
            assert_completed_field(&ns, evaluation, assigned);
            values.insert(assigned);
            let source = expression(&ns, evaluation);
            assert_eq!(span(f(val(source), "location")), body_span);
            assert!(
                arr(f(source, "arguments"))
                    .iter()
                    .any(|r| f(ns[text(f(r, "node"))], "type") == &Json::str("Domain")),
                "保持caseが実assignment Domainへ戻る"
            );
        }
        assert_eq!(values.len(), done);
        if done == 2 {
            assert_eq!(values, BTreeSet::from([false, true]));
        }
        let raw = evaluations_at(&wire, body_span)
            .into_iter()
            .filter(|e| !obj(val(e)).contains_key("value"))
            .collect::<Vec<_>>();
        assert!(!raw.is_empty(), "元missing評価を保持");
        let all_done = evaluations_at(&wire, body_span);
        let current_ids = all_done
            .iter()
            .map(|e| text(f(e, "id")))
            .collect::<BTreeSet<_>>();
        assert!(
            !arr(f(&wire, "nodes"))
                .iter()
                .any(|n| f(n, "type") == &Json::str("Evidence")
                    && ["finite_exhaustion", "completion_pair"].contains(&text(f(val(n), "kind")))
                    && {
                        let data = f(val(n), "data");
                        if f(val(n), "kind") == &Json::str("finite_exhaustion") {
                            arr(f(data, "instances"))
                                .iter()
                                .any(|r| current_ids.contains(text(f(r, "node"))))
                        } else {
                            ["first_result", "second_result"]
                                .iter()
                                .any(|key| current_ids.contains(text(f(f(data, key), "node"))))
                        }
                    }),
            "停止後に未完成case全coverage/補完対を導出しない"
        );
        assert!(
            evaluations_at(
                &wire,
                checked.law().exprs[declared_body(&checked, "Calc.later")].span
            )
            .is_empty()
        );
        assert_eq!(expressions.get(), at);
        assert_eq!(Some(probes.get()), frozen.get());
        let before = probes.get();
        assert!(control.checkpoint(Checkpoint::Expression).is_err());
        assert_eq!(probes.get(), before);
    }
}

#[test]
fn bool_completions_compare_set_values_extensionally() {
    let script = "view stable(s:Sample): Set<Bool> = if s.h then set<Bool>{false,true} else set<Bool>{true,false};";
    let (wire, checked) = run(
        fixture(script, Shape::One, false, false),
        &["a=evaluate(Calc.stable,s=@v/item)"],
    );
    assert_eq!(f(&wire, "status"), &Json::str("complete"));
    let a = answer(&wire, "a");
    assert_eq!(f(a, "status"), &Json::str("established"));
    assert!(!obj(a).contains_key("claim"));
    assert_missing_fields(&wire, "a", &[slot("v", "h")]);
    let ns = index(&wire);
    let root = root(&wire, "a");
    assert_eq!(f(f(root, "scope"), "domain"), &Json::str("all_completions"));
    assert_eq!(f(a, "scope"), f(root, "scope"));
    let t = ty("Set", Json::str("Bool"));
    let extensional = |node: &Json| {
        assert_eq!(f(node, "type"), &t);
        assert_eq!(arr(val(node)).len(), 2);
        assert_eq!(
            arr(val(node))
                .iter()
                .map(bool_value)
                .collect::<BTreeSet<_>>(),
            BTreeSet::from([false, true])
        );
    };
    let output_ref = f(f(a, "outputs"), "value");
    assert_eq!(f(val(root), "value"), output_ref);
    extensional(target(&ns, output_ref, &t));
    assert_eq!(
        source(
            &checked,
            span(f(val(original_body_source(&ns, root)), "location"))
        ),
        b"if s.h then set<Bool>{false,true} else set<Bool>{true,false}"
    );
    let domain = assignment_domain(&ns, root);
    assert_eq!(f(val(domain), "type"), &Json::str("Bool"));
    assert_eq!(f(val(domain), "kind"), &Json::str("finite"));
    let members = arr(f(val(domain), "elements"));
    assert_eq!(members.len(), 2);
    assert_eq!(
        members
            .iter()
            .map(|r| bool_value(val(target(&ns, r, &Json::str("Bool")))))
            .collect::<BTreeSet<_>>(),
        BTreeSet::from([false, true])
    );
    let case_refs = arr(f(part(root), "children"));
    assert_eq!(case_refs.len(), 2);
    let proofs = arr(f(root, "evidence"))
        .iter()
        .map(|r| target(&ns, r, &Json::str("Evidence")))
        .filter(|p| f(val(p), "kind") == &Json::str("finite_exhaustion"))
        .collect::<Vec<_>>();
    assert_eq!(proofs.len(), 1);
    let proof = f(val(proofs[0]), "data");
    assert_eq!(f(proof, "domain"), &arr(f(root, "arguments"))[1]);
    assert_eq!(f(proof, "checked"), &Json::Nat(2));
    assert_eq!(f(proof, "instances"), &Json::Arr(case_refs.to_vec()));
    assert!(evidence(&ns, root, "completion_pair").is_empty());
    let mut assignments = BTreeSet::new();
    let mut displays = BTreeSet::new();
    for case_ref in case_refs {
        let case = target(&ns, case_ref, &Json::str("Evaluation"));
        assert_eq!(f(f(case, "scope"), "domain"), &Json::str("all_completions"));
        assert_eq!(
            f(val(original_body_source(&ns, case)), "location"),
            f(val(original_body_source(&ns, root)), "location")
        );
        let assignment = case_assignment(&ns, domain, case);
        assert_eq!(assignment.len(), 1);
        assert!(assignments.insert(assignment[0]));
        let bindings = arr(f(val(case), "bindings"));
        assert_eq!(bindings.len(), 1);
        assert_eq!(f(&bindings[0], "name"), &Json::str("s"));
        assert_eq!(
            val(target(
                &ns,
                f(&bindings[0], "value"),
                &ty("Ref", Json::str("Completion.Sample"))
            )),
            &reference("v", "item")
        );
        let value = target(&ns, f(val(case), "value"), &t);
        extensional(value);
        displays.insert(val(value).canonical());
        let parts = children(&ns, case);
        assert_eq!(parts.len(), 3);
        assert_completed_field(&ns, parts[0], assignment[0]);
        for (branch, original) in [
            (parts[1], b"set<Bool>{false,true}".as_slice()),
            (parts[2], b"set<Bool>{true,false}".as_slice()),
        ] {
            assert_eq!(source(&checked, evaluation_span(&ns, branch)), original);
            extensional(target(&ns, f(val(branch), "value"), &t));
        }
        let selected = if assignment[0] { parts[1] } else { parts[2] };
        assert_eq!(val(target(&ns, f(val(selected), "value"), &t)), val(value));
    }
    assert_eq!(assignments, BTreeSet::from([false, true]));
    assert_eq!(
        displays.len(),
        2,
        "表示順の異なるcase Setを同一の数学的値として集約する"
    );
}
