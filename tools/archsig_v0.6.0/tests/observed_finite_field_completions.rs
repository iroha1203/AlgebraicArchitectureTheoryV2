//! 原始Fp欠測の共有補完を三入力から読み、元体・slot・whole・証拠と停止prefixを検査する。
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
                    "urn:fixture:finite-field-completions"
                } else {
                    "urn:fixture:finite-field-completions:relocated"
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
        if f(node, "type") == &Json::str("Evaluation") {
            let source_node = expression(&ns, node);
            if f(val(source_node), "kind") == &Json::str("source") {
                let at = span(f(val(source_node), "location"));
                if let Some((id, _)) = checked
                    .law()
                    .exprs
                    .iter()
                    .enumerate()
                    .find(|(_, e)| e.span == at)
                {
                    if let Some(value) = obj(val(node)).get("value") {
                        target(&ns, value, &checked.law().expr_type(id).unwrap().wire());
                    }
                }
            }
            for part in arr(f(val(node), "parts")) {
                for child in arr(f(part, "children")) {
                    let child = target(&ns, child, &Json::str("Evaluation"));
                    for fact in arr(f(child, "support")) {
                        assert!(arr(f(node, "support")).contains(fact));
                    }
                }
            }
        }
    }
    for answer in arr(f(wire, "answers")) {
        let mut links = vec![];
        refs(answer, &mut links);
        for link in links {
            assert!(ns.contains_key(link.as_str()));
        }
        for reason in arr(f(answer, "reasons"))
            .iter()
            .filter(|r| f(r, "code") == &Json::str("missing_observation"))
        {
            for dependency in arr(f(reason, "dependencies")) {
                let source = target(&ns, dependency, &Json::str("Expression"));
                assert_eq!(f(val(source), "kind"), &Json::str("source"));
                assert_eq!(f(val(source), "location"), f(reason, "location"));
            }
            for fact in arr(f(reason, "missing")) {
                assert!(!obj(fact).contains_key("atom"));
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
                let field = subject
                    .fields
                    .iter()
                    .find(|field| field.name == text(f(fact, "field")))
                    .unwrap();
                assert!(matches!(&field.slot, archsig::archmap::Slot::Missing));
            }
        }
    }
}

fn fp(p: u32) -> Json {
    ty("Fp", Json::str(p.to_string()))
}
fn residues(p: u32) -> Vec<Json> {
    (0..p).map(|n| Json::str(n.to_string())).collect()
}
#[derive(Clone)]
struct Slot {
    snapshot: &'static str,
    field: &'static str,
    ty: Json,
    values: Vec<Json>,
}
fn field(snapshot: &'static str, name: &'static str, prime: u32) -> Slot {
    Slot {
        snapshot,
        field: name,
        ty: fp(prime),
        values: residues(prime),
    }
}
fn flag() -> Slot {
    Slot {
        snapshot: "v",
        field: "h",
        ty: Json::str("Bool"),
        values: vec![Json::Bool(false), Json::Bool(true)],
    }
}
fn fact(slot: &Slot) -> Json {
    Json::obj([
        ("snapshot", Json::str(slot.snapshot)),
        ("subject", Json::str("item")),
        (
            "field",
            Json::str(format!("FiniteFields.Sample.{}", slot.field)),
        ),
    ])
}
fn fixture(script: &str, p: u32, g: u32, slots: &[Slot], peer: bool, moved: bool) -> InputSources {
    use common::{definition_json, entity_json, field_json, vocabulary_json};
    let fields = [
        ("f", fp(p)),
        ("g", fp(g)),
        ("h", Json::str("Bool")),
        ("known", Json::str("Bool")),
        ("z", Json::str("Z")),
        ("q", Json::str("Q")),
        ("missingz", Json::str("Z")),
    ]
    .iter()
    .map(|(name, t)| field_json(name, &t.canonical()))
    .collect::<Vec<_>>()
    .join(",");
    let root = entity_json("FiniteFields.Root", "[]", "[]");
    let sample = entity_json(
        "FiniteFields.Sample",
        &format!(
            "[{}]",
            field_json("owner", r#"["Ref","FiniteFields.Root"]"#)
        ),
        &format!("[{fields}]"),
    );
    let definitions = definition_json(&format!(
        "[{}]",
        vocabulary_json("FiniteFields", &format!("[{root},{sample}]"), "[]")
    ));
    let checked =
        check_definitions_controlled(&[("definition0", definitions.as_bytes())], &mut quiet())
            .unwrap();
    let digest = &checked.vocabularies["FiniteFields"].digest;
    let law = format!(
        r#"law "archsig.law/2" semantics "archsig/0.6.0"; reading Calc {{ use vocabulary FiniteFields version "1" digest "{digest}"; {script} }}"#
    );
    let suffix = if moved { "_moved" } else { "" };
    let shift = if moved { 10 } else { 0 };
    let mut origins = vec![];
    let mut snapshots = vec![];
    for (snapshot, mode) in [("v", "specification"), ("w", "proposed")] {
        if snapshot == "w" && !slots.iter().any(|s| s.snapshot == "w") {
            continue;
        }
        for (kind, start) in [("snapshot", 0), ("subjects", 2), ("values", 4)] {
            origins.push(format!(r#"{{"id":"{snapshot}_{kind}{suffix}","mode":"{mode}","method":"小さい有限体の観測。","locations":[{{"source":"scan","path":"{snapshot}.{kind}.model","span":[{},{}]}}]}}"#,start+shift,start+shift+1));
        }
        let mut subjects = vec![
            format!(
                r#"{{"id":"root","type":"FiniteFields.Root","origin":"{snapshot}_subjects{suffix}"}}"#
            ),
            format!(
                r#"{{"id":"item","type":"FiniteFields.Sample","origin":"{snapshot}_subjects{suffix}"}}"#
            ),
        ];
        let mut atoms = vec![];
        for (name, value) in [
            ("owner", reference(snapshot, "root")),
            ("f", Json::str("0")),
            ("g", Json::str("0")),
            ("h", Json::Bool(false)),
            ("known", Json::Bool(false)),
            ("z", Json::str("7")),
            ("q", Json::Arr(vec![Json::str("1"), Json::str("2")])),
        ] {
            if slots
                .iter()
                .any(|s| s.snapshot == snapshot && s.field == name)
            {
                continue;
            }
            atoms.push(format!(r#"{{"id":"{name}","subject":"item","field":"FiniteFields.Sample.{name}","value":{},"origin":"{snapshot}_values{suffix}"}}"#,value.canonical()));
        }
        if peer && snapshot == "v" {
            subjects.push(format!(
                r#"{{"id":"peer","type":"FiniteFields.Sample","origin":"v_subjects{suffix}"}}"#
            ));
            atoms.push(format!(r#"{{"id":"peerowner","subject":"peer","field":"FiniteFields.Sample.owner","value":["v","root"],"origin":"v_values{suffix}"}}"#));
        }
        snapshots.push(format!(r#"{{"id":"{snapshot}","origin":"{snapshot}_snapshot{suffix}","subjects":[{}],"atoms":[{}]}}"#,subjects.join(","),atoms.join(",")));
    }
    let uri = if moved {
        "urn:fixture:finite-field-completions:relocated"
    } else {
        "urn:fixture:finite-field-completions"
    };
    let revision = if moved { "r2" } else { "r1" };
    let map = format!(
        r#"{{"format":"archsig.archmap/2","semantics":"archsig/0.6.0","vocabularies":[{{"namespace":"FiniteFields","version":"1","digest":"{digest}"}}],"sources":[{{"id":"scan","uri":"{uri}","revision":"{revision}","digest":"sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"}}],"origins":[{}],"snapshots":[{}]}}"#,
        origins.join(","),
        snapshots.join(",")
    );
    InputSources::from_bytes(
        vec![definitions.into_bytes()],
        law.into_bytes(),
        map.into_bytes(),
    )
}
fn root_domain<'a>(ns: &BTreeMap<&str, &'a Json>, root: &Json) -> &'a Json {
    let args = arr(f(root, "arguments"));
    assert_eq!(&args[0], f(val(root), "expression"));
    let domain = target(ns, &args[1], &Json::str("Domain"));
    assert_eq!(arr(f(domain, "arguments")).first(), Some(&args[0]));
    domain
}
fn assignment(ns: &BTreeMap<&str, &Json>, domain: &Json, evaluation: &Json) -> Vec<Json> {
    let source = original_body_source(ns, evaluation);
    let selected = arr(f(source, "arguments"))
        .iter()
        .filter(|r| arr(f(val(domain), "elements")).contains(r))
        .collect::<Vec<_>>();
    assert_eq!(selected.len(), 1);
    let value = val(target(ns, selected[0], f(val(domain), "type")));
    if matches!(f(val(domain),"type"),Json::Arr(ts) if ts.first()==Some(&Json::str("Tuple"))) {
        arr(value).to_vec()
    } else {
        vec![value.clone()]
    }
}
fn expected_rows(slots: &[Slot]) -> Vec<Vec<Json>> {
    let mut rows = vec![vec![]];
    for slot in slots {
        rows = rows
            .into_iter()
            .flat_map(|row| {
                slot.values.iter().map(move |v| {
                    let mut r = row.clone();
                    r.push(v.clone());
                    r
                })
            })
            .collect();
    }
    rows
}
fn missing_fields(wire: &Json, id: &str, wanted: &[Json]) {
    let missing = arr(f(answer(wire, id), "reasons"))
        .iter()
        .filter(|r| f(r, "code") == &Json::str("missing_observation"))
        .flat_map(|r| {
            assert!(!arr(f(r, "dependencies")).is_empty());
            arr(f(r, "missing"))
        })
        .collect::<Vec<_>>();
    for wanted in wanted {
        assert!(missing.contains(&wanted), "元slot理由を保持: {wanted:?}");
    }
}
struct Case<'a> {
    assignment: Vec<Json>,
    evaluation: &'a Json,
}
fn cases<'a>(
    wire: &'a Json,
    id: &str,
    slots: &[Slot],
    t: &Json,
    wanted: &[(Vec<Json>, Option<Json>)],
) -> Vec<Case<'a>> {
    let ns = index(wire);
    let aggregate = root(wire, id);
    assert_eq!(
        f(f(aggregate, "scope"), "domain"),
        &Json::str("all_completions")
    );
    missing_fields(wire, id, &slots.iter().map(fact).collect::<Vec<_>>());
    let domain = root_domain(&ns, aggregate);
    assert_eq!(f(val(domain), "kind"), &Json::str("finite"));
    let domain_type = if slots.len() == 1 {
        slots[0].ty.clone()
    } else {
        Json::Arr(
            std::iter::once(Json::str("Tuple"))
                .chain(slots.iter().map(|s| s.ty.clone()))
                .collect(),
        )
    };
    assert_eq!(f(val(domain), "type"), &domain_type);
    let expected = expected_rows(slots)
        .into_iter()
        .map(|r| Json::Arr(r).canonical())
        .collect::<BTreeSet<_>>();
    let members = arr(f(val(domain), "elements"));
    assert_eq!(members.len(), expected.len());
    let mut member_values = BTreeSet::new();
    for member in members {
        let node = target(&ns, member, &domain_type);
        assert_eq!(f(f(node, "rule"), "kind"), &Json::str("construction"));
        let row = if slots.len() == 1 {
            vec![val(node).clone()]
        } else {
            arr(val(node)).to_vec()
        };
        assert!(member_values.insert(Json::Arr(row).canonical()));
    }
    assert_eq!(member_values, expected);
    let actual = children(&ns, aggregate);
    assert_eq!(actual.len(), wanted.len());
    assert_eq!(actual.len(), members.len());
    let mut seen = BTreeSet::new();
    let mut result = vec![];
    for evaluation in actual {
        assert_eq!(
            f(val(original_body_source(&ns, evaluation)), "location"),
            f(val(expression(&ns, aggregate)), "location")
        );
        let row = assignment(&ns, domain, evaluation);
        assert!(seen.insert(Json::Arr(row.clone()).canonical()));
        let expected = &wanted
            .iter()
            .find(|(r, _)| r == &row)
            .expect("手計算した全case")
            .1;
        if let Some(expected) = expected {
            assert_eq!(val(target(&ns, f(val(evaluation), "value"), t)), expected);
        } else {
            assert!(!obj(val(evaluation)).contains_key("value"));
        }
        assert_eq!(
            f(f(evaluation, "scope"), "domain"),
            &Json::str("all_completions")
        );
        result.push(Case {
            assignment: row,
            evaluation,
        });
    }
    assert_eq!(seen, member_values);
    let same = wanted[0]
        .1
        .as_ref()
        .filter(|v| wanted.iter().all(|(_, w)| w.as_ref() == Some(*v)));
    let direct = arr(f(aggregate, "evidence"))
        .iter()
        .map(|r| target(&ns, r, &Json::str("Evidence")))
        .collect::<Vec<_>>();
    if same.is_some() {
        assert_eq!(direct.len(), 1);
        assert_eq!(f(val(direct[0]), "kind"), &Json::str("finite_exhaustion"));
        let data = f(val(direct[0]), "data");
        assert_eq!(target(&ns, f(data, "domain"), &Json::str("Domain")), domain);
        assert_eq!(f(data, "checked"), &Json::Nat(wanted.len() as u64));
        assert_eq!(f(data, "instances"), f(part(aggregate), "children"));
    } else {
        assert!(
            direct
                .iter()
                .all(|p| f(val(p), "kind") != &Json::str("finite_exhaustion"))
        );
        let known = wanted
            .iter()
            .filter_map(|(_, v)| v.as_ref())
            .map(Json::canonical)
            .collect::<BTreeSet<_>>();
        if known.len() > 1 {
            assert_eq!(direct.len(), 1);
            let pair = f(val(direct[0]), "data");
            assert_eq!(f(val(direct[0]), "kind"), &Json::str("completion_pair"));
            assert_eq!(
                f(pair, "fields"),
                &Json::Arr(slots.iter().map(fact).collect())
            );
            let mut pair_values = vec![];
            let mut pair_results = vec![];
            for (binding, result_key) in [("first", "first_result"), ("second", "second_result")] {
                let values = arr(f(pair, binding));
                assert_eq!(values.len(), slots.len());
                let evaluation = target(&ns, f(pair, result_key), &Json::str("Evaluation"));
                assert!(arr(f(part(aggregate), "children")).contains(f(pair, result_key)));
                let row = assignment(&ns, domain, evaluation);
                for ((value, slot), expected) in values.iter().zip(slots).zip(&row) {
                    let projection = target(&ns, value, &slot.ty);
                    assert_eq!(val(projection), expected);
                    assert_eq!(f(f(projection, "rule"), "kind"), &Json::str("construction"));
                    let args = arr(f(projection, "arguments"));
                    assert_eq!(args.len(), 4);
                    assert_eq!(&args[1], &arr(f(aggregate, "arguments"))[1]);
                    assert!(
                        arr(f(original_body_source(&ns, evaluation), "arguments")).contains(value)
                    );
                }
                pair_values.push(row);
                pair_results.push(val(target(&ns, f(val(evaluation), "value"), t)).canonical());
            }
            assert_ne!(pair_values[0], pair_values[1]);
            assert_ne!(pair_results[0], pair_results[1]);
        } else {
            assert!(direct.is_empty());
        }
    }
    result
}
fn live<'a>(ns: &BTreeMap<&str, &'a Json>, root: &'a Json) -> Vec<&'a Json> {
    let mut todo = vec![root];
    let mut seen = BTreeSet::new();
    let mut result = vec![];
    while let Some(e) = todo.pop() {
        if seen.insert(text(f(e, "id"))) {
            result.push(e);
            for part in arr(f(val(e), "parts")) {
                for child in arr(f(part, "children")) {
                    todo.push(target(ns, child, &Json::str("Evaluation")));
                }
            }
        }
    }
    result
}
fn field_value(ns: &BTreeMap<&str, &Json>, evaluation: &Json, slot: &Slot, expected: &Json) {
    let scalar = target(ns, f(val(evaluation), "value"), &slot.ty);
    assert_eq!(val(scalar), expected);
    let source = expression(ns, evaluation);
    assert_eq!(f(f(scalar, "rule"), "kind"), &Json::str("law"));
    assert_eq!(f(f(scalar, "rule"), "location"), f(val(source), "location"));
    assert!(arr(f(scalar, "support")).is_empty());
    let args = arr(f(scalar, "arguments"));
    assert_eq!(args.len(), 3);
    assert_eq!(&args[0], f(val(evaluation), "expression"));
    assert_eq!(
        val(target(
            ns,
            &args[1],
            &ty("Ref", Json::str("FiniteFields.Sample"))
        )),
        &reference(slot.snapshot, "item")
    );
    let projection = target(ns, &args[2], &slot.ty);
    assert_eq!(val(projection), expected);
    assert_eq!(f(f(projection, "rule"), "kind"), &Json::str("construction"));
    let inputs = arr(f(projection, "arguments"));
    assert_eq!(inputs.len(), 4);
    let domain = target(ns, &inputs[1], &Json::str("Domain"));
    assert!(arr(f(val(domain), "elements")).contains(&inputs[2]));
    let seed = target(ns, &inputs[0], &Json::str("Expression"));
    assert!(arr(f(seed, "arguments")).contains(&inputs[3]));
    assert!(
        arr(f(seed, "reasons"))
            .iter()
            .any(
                |reason| f(reason, "code") == &Json::str("missing_observation")
                    && arr(f(reason, "dependencies")).contains(&inputs[3])
                    && arr(f(reason, "missing")).contains(&fact(slot))
            ),
        "projectionは元slot identityのcanonical missing Sourceへ戻る"
    );
    for edge in &inputs[..3] {
        assert!(arr(f(source, "arguments")).contains(edge));
    }
    assert!(arr(f(source, "arguments")).contains(&args[2]));
}

#[test]
fn finite_field_completions_share_typed_slots_and_residuals() {
    let slots = [field("v", "f", 3)];
    let script = r#"
view delta(s:Sample): Fp(3) = s.f-s.f;
view equal_value(s:Sample): Bool = s.f=s.f;
view unequal_value(s:Sample): Bool = s.f!=s.f;
law required unequal_law(s:Sample): s.f!=s.f;
view helper(s:Sample): Fp(3) = let held=s.f in held;
view shared(s:Sample): Bool = forall b:Fp(3) . helper(s)=s.f;
view changing(s:Sample): Fp(3) = s.f;
view zero_test(s:Sample): Bool = s.f=0;
"#;
    let (wire, checked) = run(
        fixture(script, 3, 3, &slots, false, false),
        &[
            "delta=evaluate(Calc.delta,s=@v/item)",
            "eq=evaluate(Calc.equal_value,s=@v/item)",
            "neq=evaluate(Calc.unequal_value,s=@v/item)",
            "checked=check(Calc.unequal_law,s=@v/item)",
            "shared=evaluate(Calc.shared,s=@v/item)",
            "changing=evaluate(Calc.changing,s=@v/item)",
            "zero_test=evaluate(Calc.zero_test,s=@v/item)",
        ],
    );
    assert_eq!(f(&wire, "status"), &Json::str("partial"));
    output(&wire, "delta", &fp(3), Json::str("0"));
    for (id, value) in [("eq", true), ("neq", false), ("shared", true)] {
        output(&wire, id, &Json::str("Bool"), Json::Bool(value));
    }
    check_claim(&wire, "checked", "refuted");
    let ns = index(&wire);
    for (id, t) in [
        ("delta", fp(3)),
        ("eq", Json::str("Bool")),
        ("neq", Json::str("Bool")),
        ("checked", Json::str("Bool")),
        ("shared", Json::str("Bool")),
        ("changing", fp(3)),
        ("zero_test", Json::str("Bool")),
    ] {
        let wanted = residues(3)
            .into_iter()
            .map(|r| {
                let value = match id {
                    "delta" => Json::str("0"),
                    "eq" | "shared" => Json::Bool(true),
                    "neq" | "checked" => Json::Bool(false),
                    "changing" => r.clone(),
                    "zero_test" => Json::Bool(r == Json::str("0")),
                    _ => unreachable!(),
                };
                (vec![r], Some(value))
            })
            .collect::<Vec<_>>();
        for case in cases(&wire, id, &slots, &t, &wanted) {
            let fields = live(&ns, case.evaluation)
                .into_iter()
                .filter(|e| {
                    f(val(expression(&ns, e)), "kind") == &Json::str("source")
                        && source(&checked, evaluation_span(&ns, e)) == b"s.f"
                })
                .collect::<Vec<_>>();
            assert!(!fields.is_empty());
            for e in fields {
                field_value(&ns, e, &slots[0], &case.assignment[0]);
            }
            if id == "eq" {
                let residual = target(&ns, f(part(case.evaluation), "residual"), &fp(3));
                assert_eq!(val(residual), &Json::str("0"));
            } else if ["neq", "checked"].contains(&id) {
                assert!(!obj(part(case.evaluation)).contains_key("residual"));
            }
        }
    }
    for id in ["changing", "zero_test"] {
        assert_eq!(f(answer(&wire, id), "status"), &Json::str("undetermined"));
        assert!(!obj(f(answer(&wire, id), "outputs")).contains_key("value"));
        assert!(!obj(answer(&wire, id)).contains_key("claim"));
    }
    let shared = cases(
        &wire,
        "shared",
        &slots,
        &Json::str("Bool"),
        &residues(3)
            .into_iter()
            .map(|r| (vec![r], Some(Json::Bool(true))))
            .collect::<Vec<_>>(),
    );
    for case in shared {
        let q = arr(f(f(case.evaluation, "scope"), "quantifiers"))
            .iter()
            .find(|q| f(q, "name") == &Json::str("b"))
            .unwrap();
        assert_eq!(f(q, "type"), &fp(3));
        assert_eq!(f(q, "kind"), &Json::str("forall"));
        let domain = target(&ns, f(q, "domain"), &Json::str("Domain"));
        assert_eq!(f(val(domain), "type"), &fp(3));
        assert_eq!(
            arr(f(val(domain), "elements"))
                .iter()
                .map(|r| val(target(&ns, r, &fp(3))).canonical())
                .collect::<BTreeSet<_>>(),
            residues(3).iter().map(Json::canonical).collect()
        );
        assert_eq!(children(&ns, case.evaluation).len(), 3);
    }
}

#[test]
fn finite_field_completion_products_keep_fields_primes_snapshots_and_bool_distinct() {
    for (slots, p, g, script, ask, result_type, reverse_result) in [
        (
            vec![field("v", "f", 2), field("v", "g", 2)],
            2,
            2,
            "view pair(s:Sample): (Fp(2),Fp(2)) = (s.f,s.g);",
            "a=evaluate(Calc.pair,s=@v/item)",
            Json::Arr(vec![Json::str("Tuple"), fp(2), fp(2)]),
            false,
        ),
        (
            vec![field("v", "f", 2), field("v", "g", 3)],
            2,
            3,
            "view pair(s:Sample): (Fp(2),Fp(3)) = (s.f,s.g);",
            "a=evaluate(Calc.pair,s=@v/item)",
            Json::Arr(vec![Json::str("Tuple"), fp(2), fp(3)]),
            false,
        ),
        (
            vec![field("v", "f", 2), field("w", "f", 2)],
            2,
            2,
            "view pair(s:Sample,t:Sample): (Fp(2),Fp(2)) = (s.f,t.f);",
            "a=evaluate(Calc.pair,s=@v/item,t=@w/item)",
            Json::Arr(vec![Json::str("Tuple"), fp(2), fp(2)]),
            false,
        ),
        (
            vec![field("v", "f", 2), flag()],
            2,
            3,
            "view pair(s:Sample): (Bool,Fp(2)) = (s.h,s.f);",
            "a=evaluate(Calc.pair,s=@v/item)",
            Json::Arr(vec![Json::str("Tuple"), Json::str("Bool"), fp(2)]),
            true,
        ),
    ] {
        let (wire, checked) = run(fixture(script, p, g, &slots, false, false), &[ask]);
        assert_eq!(f(&wire, "status"), &Json::str("partial"));
        assert_eq!(f(answer(&wire, "a"), "status"), &Json::str("undetermined"));
        let wanted = expected_rows(&slots)
            .into_iter()
            .map(|row| {
                let mut result = row.clone();
                if reverse_result {
                    result.reverse();
                }
                (row, Some(Json::Arr(result)))
            })
            .collect::<Vec<_>>();
        let ns = index(&wire);
        for case in cases(&wire, "a", &slots, &result_type, &wanted) {
            for evaluation in live(&ns, case.evaluation) {
                let bytes = source(&checked, evaluation_span(&ns, evaluation));
                let at = match bytes {
                    b"s.f" => Some(0),
                    b"s.g" | b"t.f" | b"s.h" => Some(1),
                    _ => None,
                };
                if let Some(at) = at {
                    field_value(&ns, evaluation, &slots[at], &case.assignment[at]);
                }
            }
        }
    }
}

#[test]
fn finite_field_completions_quantify_each_law_family_before_aggregation() {
    let slots = [field("v", "f", 2)];
    let (wire, checked) = run(
        fixture(
            "law required family(s:Sample,b:Fp(2)): b=s.f;",
            2,
            3,
            &slots,
            false,
            false,
        ),
        &["a=check(Calc.family,s=@v/item)"],
    );
    assert_eq!(f(&wire, "status"), &Json::str("complete"));
    check_claim(&wire, "a", "refuted");
    let ns = index(&wire);
    let aggregate = root(&wire, "a");
    let propositions = arr(f(aggregate, "arguments"))
        .iter()
        .map(|r| ns[text(f(r, "node"))])
        .filter(|n| f(n, "type") == &Json::str("Proposition"))
        .collect::<Vec<_>>();
    assert_eq!(propositions.len(), 2);
    let wanted = residues(2)
        .into_iter()
        .map(|r| (vec![r], Some(Json::Bool(false))))
        .collect::<Vec<_>>();
    let mut counters = BTreeSet::new();
    let mut used = BTreeSet::new();
    for case in cases(&wire, "a", &slots, &Json::str("Bool"), &wanted) {
        let whole = aggregate_instance(&ns, case.evaluation).expect("補完内Law族");
        assert_eq!(f(val(whole), "name"), &Json::str("Calc.family"));
        let body = target(&ns, f(val(whole), "body"), &Json::str("Expression"));
        assert_eq!(
            f(val(body), "parameters"),
            &Json::Arr(vec![Json::obj([("name", Json::str("b")), ("type", fp(2))])])
        );
        let fixed = arr(f(val(whole), "bindings"));
        assert_eq!(fixed.len(), 1);
        assert_eq!(f(&fixed[0], "name"), &Json::str("s"));
        assert_eq!(
            val(target(
                &ns,
                f(&fixed[0], "value"),
                &ty("Ref", Json::str("FiniteFields.Sample"))
            )),
            &reference("v", "item")
        );
        let q = arr(f(f(case.evaluation, "scope"), "quantifiers"))
            .iter()
            .find(|q| f(q, "name") == &Json::str("b"))
            .unwrap();
        assert_eq!(f(q, "type"), &fp(2));
        assert_eq!(f(q, "kind"), &Json::str("forall"));
        let domain = target(&ns, f(q, "domain"), &Json::str("Domain"));
        assert_eq!(f(val(domain), "type"), &fp(2));
        assert_eq!(arr(f(val(domain), "elements")).len(), 2);
        let rows = children(&ns, case.evaluation);
        assert_eq!(rows.len(), 2);
        let mut bs = BTreeSet::new();
        for row in rows {
            let bindings = arr(f(val(row), "bindings"));
            assert_eq!(bindings.len(), 2);
            assert_eq!(f(&bindings[0], "name"), &Json::str("s"));
            assert_eq!(f(&bindings[1], "name"), &Json::str("b"));
            let b = val(target(&ns, f(&bindings[1], "value"), &fp(2)));
            assert!(bs.insert(b.canonical()));
            assert_eq!(
                val(target(&ns, f(val(row), "value"), &Json::str("Bool"))),
                &Json::Bool(b == &case.assignment[0])
            );
            assert_eq!(source(&checked, evaluation_span(&ns, row)), b"b=s.f");
            assert_eq!(
                val(target(&ns, f(part(row), "residual"), &fp(2))),
                &Json::str(if b == &case.assignment[0] { "0" } else { "1" })
            );
        }
        assert_eq!(bs, residues(2).iter().map(Json::canonical).collect());
        let case_ref = Json::obj([("node", f(case.evaluation, "id").clone())]);
        let claims = propositions
            .iter()
            .copied()
            .filter(|p| arr(f(p, "arguments")).get(1) == Some(&case_ref))
            .collect::<Vec<_>>();
        assert_eq!(claims.len(), 1);
        assert!(used.insert(text(f(claims[0], "id"))));
        let whole_ref = &arr(f(case.evaluation, "arguments"))[0];
        assert_eq!(
            f(claims[0], "arguments"),
            &Json::Arr(vec![whole_ref.clone(), case_ref])
        );
        assert_eq!(
            f(val(claims[0]), "operands"),
            &Json::Arr(vec![whole_ref.clone()])
        );
        assert_eq!(f(f(claims[0], "judgment"), "status"), &Json::str("refuted"));
        let examples = evidence(&ns, claims[0], "counterexample");
        assert_eq!(examples.len(), 1);
        let data = f(val(examples[0]), "data");
        let b = arr(f(data, "bindings"))
            .iter()
            .find(|b| f(b, "name") == &Json::str("b"))
            .unwrap();
        let b = val(target(&ns, f(b, "value"), &fp(2)));
        assert_ne!(b, &case.assignment[0]);
        counters.insert(b.canonical());
        assert_eq!(val(target(&ns, f(data, "left"), &fp(2))), b);
        assert_eq!(
            val(target(&ns, f(data, "right"), &fp(2))),
            &case.assignment[0]
        );
    }
    assert_eq!(used.len(), 2);
    assert_eq!(counters, residues(2).iter().map(Json::canonical).collect());
    let claim = target(
        &ns,
        f(answer(&wire, "a"), "claim"),
        &Json::str("Proposition"),
    );
    assert!(
        arr(f(claim, "evidence"))
            .iter()
            .all(|r| f(val(target(&ns, r, &Json::str("Evidence"))), "kind")
                != &Json::str("counterexample")),
        "補完ごとに異なるbを単一の観測反例にしない"
    );
}

#[test]
fn finite_field_completions_keep_guards_and_provenance() {
    let slots = [field("v", "f", 3)];
    let (wire, checked) = run(
        fixture(
            "law required gated(s:Sample) when s.f=0: false;",
            3,
            3,
            &slots,
            false,
            false,
        ),
        &["a=check(Calc.gated,s=@v/item)"],
    );
    check_claim(&wire, "a", "undetermined");
    assert_eq!(f(&wire, "status"), &Json::str("partial"));
    let ns = index(&wire);
    let wanted = residues(3)
        .into_iter()
        .map(|r| {
            let result = r != Json::str("0");
            (vec![r], Some(Json::Bool(result)))
        })
        .collect::<Vec<_>>();
    for case in cases(&wire, "a", &slots, &Json::str("Bool"), &wanted) {
        let instance = aggregate_instance(&ns, case.evaluation).expect("元guard付き適用");
        let body = target(&ns, f(val(instance), "body"), &Json::str("Expression"));
        assert_eq!(source(&checked, span(f(val(body), "location"))), b"false");
        let guard = target(&ns, f(val(instance), "guard"), &Json::str("Expression"));
        assert_eq!(source(&checked, span(f(val(guard), "location"))), b"s.f=0");
        let active = case.assignment[0] == Json::str("0");
        assert_eq!(
            f(val(case.evaluation), "applicability"),
            &Json::str(if active {
                "applicable"
            } else {
                "not_applicable"
            })
        );
        let parts = arr(f(val(case.evaluation), "parts"));
        assert_eq!(parts.len(), 2);
        assert_eq!(f(&parts[0], "location"), f(val(guard), "location"));
        assert_eq!(f(&parts[1], "location"), f(val(body), "location"));
        assert_eq!(
            val(target(&ns, f(&parts[0], "value"), &Json::str("Bool"))),
            &Json::Bool(active)
        );
        assert_eq!(
            val(target(&ns, f(&parts[0], "residual"), &fp(3))),
            &case.assignment[0]
        );
        let g = arr(f(&parts[0], "children"));
        assert_eq!(g.len(), 1);
        let g = target(&ns, &g[0], &Json::str("Evaluation"));
        assert_eq!(f(val(g), "expression"), f(val(instance), "guard"));
        field_value(&ns, children(&ns, g)[0], &slots[0], &case.assignment[0]);
        if active {
            assert_eq!(
                val(target(&ns, f(&parts[1], "value"), &Json::str("Bool"))),
                &Json::Bool(false)
            );
            assert_eq!(arr(f(&parts[1], "children")).len(), 1);
        } else {
            assert!(!obj(&parts[1]).contains_key("value"));
            assert!(arr(f(&parts[1], "children")).is_empty());
        }
    }
    for moved in [false, true] {
        let (wire, checked) = run(
            fixture(
                "view stable(s:Sample): Fp(3) = s.f-s.f;",
                3,
                3,
                &slots,
                false,
                moved,
            ),
            &["a=evaluate(Calc.stable,s=@v/item)"],
        );
        output(&wire, "a", &fp(3), Json::str("0"));
        cases(
            &wire,
            "a",
            &slots,
            &fp(3),
            &residues(3)
                .into_iter()
                .map(|r| (vec![r], Some(Json::str("0"))))
                .collect::<Vec<_>>(),
        );
        assert_eq!(
            checked.archmap().sources[0].revision,
            if moved { "r2" } else { "r1" }
        );
        assert_eq!(
            checked
                .archmap()
                .origins
                .iter()
                .all(|o| o.id.ends_with("_moved")),
            moved
        );
    }
}

#[test]
fn finite_field_reference_selection_keeps_other_numeric_missing() {
    let slots = [field("v", "f", 2)];
    let script = r#"
view selected_z(s:Sample,t:Sample): Z = let selected=if s.f=0 then s else t in selected.z;
view selected_q(s:Sample,t:Sample): Q = let selected=if s.f=0 then s else t in (selected).q;
"#;
    let (wire, checked) = run(
        fixture(script, 2, 3, &slots, true, false),
        &[
            "a=evaluate(Calc.selected_z,s=@v/item,t=@v/peer)",
            "b=evaluate(Calc.selected_q,s=@v/item,t=@v/peer)",
        ],
    );
    assert_eq!(f(&wire, "status"), &Json::str("partial"));
    let ns = index(&wire);
    for (id, t, known, name) in [
        ("a", Json::str("Z"), Json::str("7"), "z"),
        (
            "b",
            Json::str("Q"),
            Json::Arr(vec![Json::str("1"), Json::str("2")]),
            "q",
        ),
    ] {
        assert_eq!(f(answer(&wire, id), "status"), &Json::str("undetermined"));
        assert!(!obj(f(answer(&wire, id), "outputs")).contains_key("value"));
        assert!(!obj(answer(&wire, id)).contains_key("claim"));
        missing_fields(
            &wire,
            id,
            &[
                fact(&slots[0]),
                Json::obj([
                    ("snapshot", Json::str("v")),
                    ("subject", Json::str("peer")),
                    ("field", Json::str(format!("FiniteFields.Sample.{name}"))),
                ]),
            ],
        );
        for case in cases(
            &wire,
            id,
            &slots,
            &t,
            &[
                (vec![Json::str("0")], Some(known.clone())),
                (vec![Json::str("1")], None),
            ],
        ) {
            let bindings = arr(f(val(case.evaluation), "bindings"));
            assert_eq!(bindings.len(), 2);
            for (b, (n, s)) in bindings.iter().zip([("s", "item"), ("t", "peer")]) {
                assert_eq!(f(b, "name"), &Json::str(n));
                assert_eq!(
                    val(target(
                        &ns,
                        f(b, "value"),
                        &ty("Ref", Json::str("FiniteFields.Sample"))
                    )),
                    &reference("v", s)
                );
            }
            for e in live(&ns, case.evaluation) {
                if source(&checked, evaluation_span(&ns, e)) == b"s.f" {
                    field_value(&ns, e, &slots[0], &case.assignment[0]);
                }
            }
            if case.assignment[0] == Json::str("0") {
                assert!(
                    arr(f(case.evaluation, "support"))
                        .iter()
                        .any(|fact| f(fact, "subject") == &Json::str("item")
                            && obj(fact).get("field")
                                == Some(&Json::str(format!("FiniteFields.Sample.{name}")))
                            && obj(fact).get("atom") == Some(&Json::str(name)))
                );
            }
        }
    }
}

#[test]
fn finite_field_completion_expression_stops_keep_case_prefixes() {
    let slots = [field("v", "f", 3)];
    let input = fixture(
        r#"
view seed(s:Sample): Unit = unit;
law required known_false(s:Sample): s.known;
view other_missing(s:Sample): Z = s.missingz;
view current(s:Sample): Fp(3) = s.f;
view later(s:Sample): Unit = unit;
"#,
        3,
        3,
        &slots,
        false,
        false,
    );
    let asks = [
        "seed=evaluate(Calc.seed,s=@v/item)",
        "known_false=check(Calc.known_false,s=@v/item)",
        "other_missing=evaluate(Calc.other_missing,s=@v/item)",
        "current=evaluate(Calc.current,s=@v/item)",
        "later=evaluate(Calc.later,s=@v/item)",
    ];
    let checked = check_inputs(input.clone(), &mut quiet()).unwrap();
    let prior_count = Rc::new(Cell::new(0));
    let n = prior_count.clone();
    let mut control = Control::new(Limits::default(), move |p| {
        if p == Checkpoint::Expression {
            n.set(n.get() + 1);
        }
        Usage::default()
    });
    let prior = evaluate_observed_bytes(input.clone(), &asks[..3], &mut control)
        .unwrap()
        .wire();
    audit(&prior, &checked);
    output(&prior, "seed", &Json::str("Unit"), Json::Arr(vec![]));
    check_claim(&prior, "known_false", "refuted");
    let missing_z = Json::obj([
        ("snapshot", Json::str("v")),
        ("subject", Json::str("item")),
        ("field", Json::str("FiniteFields.Sample.missingz")),
    ]);
    missing_fields(&prior, "other_missing", &[missing_z.clone()]);
    let baseline_count = Rc::new(Cell::new(0));
    let n = baseline_count.clone();
    let mut control = Control::new(Limits::default(), move |p| {
        if p == Checkpoint::Expression {
            n.set(n.get() + 1);
        }
        Usage::default()
    });
    let baseline = evaluate_observed_bytes(input.clone(), &asks[..4], &mut control)
        .unwrap()
        .wire();
    audit(&baseline, &checked);
    cases(
        &baseline,
        "current",
        &slots,
        &fp(3),
        &residues(3)
            .into_iter()
            .map(|r| (vec![r.clone()], Some(r)))
            .collect::<Vec<_>>(),
    );
    assert_eq!(
        baseline_count.get() - prior_count.get(),
        8,
        "元missingと3caseの通常Expression pre/post"
    );
    let current_span = checked.law().exprs[declared_body(&checked, "Calc.current")].span;
    assert_eq!(source(&checked, current_span), b"s.f");
    // 補完の実列挙/証拠/再検査phase内部はprivate試験で検査する。ここは固定Expression3点。
    for (offset, kind, done) in [(3, 0, 0), (5, 1, 1), (8, 2, 3)] {
        let at = prior_count.get() + offset;
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
        for id in ["seed", "known_false", "other_missing"] {
            for key in ["status", "outputs", "scope", "reasons", "evidence"] {
                assert_eq!(f(answer(&wire, id), key), f(answer(&prior, id), key));
            }
        }
        missing_fields(&wire, "other_missing", &[missing_z.clone()]);
        missing_fields(&wire, "current", &[fact(&slots[0])]);
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
        let all = evaluations_at(&wire, current_span);
        let completed = all
            .iter()
            .copied()
            .filter(|e| obj(val(e)).contains_key("value"))
            .collect::<Vec<_>>();
        assert_eq!(completed.len(), done);
        assert!(
            all.iter().any(|e| !obj(val(e)).contains_key("value")),
            "元missing評価を保持"
        );
        let mut values = BTreeSet::new();
        for evaluation in completed {
            let value = val(target(&ns, f(val(evaluation), "value"), &fp(3)));
            assert!(residues(3).contains(value));
            assert!(values.insert(value.canonical()));
            field_value(&ns, evaluation, &slots[0], value);
        }
        assert_eq!(values.len(), done);
        if done == 3 {
            assert_eq!(values, residues(3).iter().map(Json::canonical).collect());
        }
        let current_ids = all
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
            "停止後に未完成coverageや補完対を導出しない"
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
