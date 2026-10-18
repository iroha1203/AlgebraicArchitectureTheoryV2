//! 元Family式のowner・有限Set・In域・支持を三入力byte APIから確かめる。
mod common;

use archsig::{
    archmap::{Mode, Slot},
    canonical::{Json, sha256_digest},
    definition::check_definitions_controlled,
    law::ast::{ExprKind, QuantDomain, QuantSplit},
    observed::{
        ObservedEvaluation,
        control::{Control, Limits, Usage},
        evaluate_observed_bytes,
        input::{CheckedInputs, InputSources, check_inputs},
    },
    types::Type,
};
use std::collections::{BTreeMap, BTreeSet};

fn quiet() -> Control {
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
fn text(j: &Json) -> &str {
    let Json::Str(v) = j else {
        panic!("string {j:?}")
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
fn ty(kind: &str, item: Json) -> Json {
    Json::Arr(vec![Json::str(kind), item])
}
fn reference(snapshot: &str, subject: &str) -> Json {
    Json::Arr(vec![Json::str(snapshot), Json::str(subject)])
}
fn refs(j: &Json, out: &mut Vec<String>) {
    match j {
        Json::Obj(m) if m.len() == 1 && m.contains_key("node") => out.push(text(&m["node"]).into()),
        Json::Obj(m) => m.values().for_each(|v| refs(v, out)),
        Json::Arr(a) => a.iter().for_each(|v| refs(v, out)),
        _ => {}
    }
}
fn index(wire: &Json) -> BTreeMap<&str, &Json> {
    arr(f(wire, "nodes"))
        .iter()
        .map(|n| (text(f(n, "id")), n))
        .collect()
}
fn target<'a>(ns: &BTreeMap<&str, &'a Json>, r: &Json, t: &Json) -> &'a Json {
    assert_eq!(obj(r).len(), 1);
    let n = ns[text(f(r, "node"))];
    assert_eq!(f(n, "type"), t);
    n
}
fn span(location: &Json) -> (usize, usize) {
    assert_eq!(f(location, "input"), &Json::str("law"));
    let a = arr(f(location, "span"));
    let nat = |j: &Json| match j {
        Json::Nat(n) => *n as usize,
        _ => panic!("Nat"),
    };
    (nat(&a[0]), nat(&a[1]))
}
fn answer<'a>(wire: &'a Json, id: &str) -> &'a Json {
    arr(f(wire, "answers"))
        .iter()
        .find(|a| text(f(a, "id")) == id)
        .unwrap()
}
fn output(wire: &Json, id: &str, t: &Json, expected: &Json) {
    let a = answer(wire, id);
    assert_eq!(f(a, "status"), &Json::str("established"));
    assert!(!obj(a).contains_key("claim"));
    assert_eq!(
        val(target(&index(wire), f(f(a, "outputs"), "value"), t)),
        expected
    );
}
fn output_set(wire: &Json, id: &str, entity: &str, wanted: &[Json]) {
    let a = answer(wire, id);
    assert_eq!(f(a, "status"), &Json::str("established"));
    let ns = index(wire);
    let set = val(target(
        &ns,
        f(f(a, "outputs"), "value"),
        &ty("Set", ty("Ref", Json::str(entity))),
    ));
    let actual: BTreeSet<_> = arr(set).iter().map(Json::canonical).collect();
    assert_eq!(actual, wanted.iter().map(Json::canonical).collect());
    assert_eq!(arr(set).len(), wanted.len());
}

fn fixture(
    script: &str,
    omit: Option<&str>,
    false_field: Option<&str>,
    second: bool,
    moved: bool,
) -> InputSources {
    use common::{definition_json, entity_json, field_json, vocabulary_json};
    let root = entity_json("Owned.Root", "[]", "[]");
    let state = entity_json(
        "Owned.State",
        &format!("[{}]", field_json("owner", r#"["Ref","Owned.Root"]"#)),
        &format!(
            "[{},{}]",
            field_json("value", r#""Z""#),
            field_json("ok", r#""Bool""#)
        ),
    );
    let hop = format!(
        r#"{{"kind":"arrow","name":"Owned.Hop","meaning":"小さい所有付き操作。","parameters":[{},{},{}],"fields":[],"alignments":[]}}"#,
        field_json("owner", r#"["Ref","Owned.Root"]"#),
        field_json("from", r#"["Owned","Owned.State","owner"]"#),
        field_json("to", r#"["Owned","Owned.State","owner"]"#)
    );
    let movement = entity_json(
        "Owned.Move",
        "[]",
        &format!("[{}]", field_json("from", r#"["Ref","Owned.Root"]"#)),
    );
    let definitions = definition_json(&format!(
        "[{}]",
        vocabulary_json("Owned", &format!("[{root},{state},{hop},{movement}]"), "[]")
    ));
    let checked =
        check_definitions_controlled(&[("definition0", definitions.as_bytes())], &mut quiet())
            .unwrap();
    let digest = &checked.vocabularies["Owned"].digest;
    let law = format!(
        r#"law "archsig.law/2" semantics "archsig/0.6.0"; reading Inspect {{ use vocabulary Owned version "1" digest "{digest}"; {script} }}"#
    );
    let mut snapshots = vec![];
    let mut origins = vec![];
    for snapshot in if second { vec!["v", "w"] } else { vec!["v"] } {
        let mode = if snapshot == "v" {
            "specification"
        } else {
            "proposed"
        };
        let shift = if moved { 20 } else { 0 };
        for (kind, start) in [("subjects", 1), ("owners", 3), ("values", 5)] {
            origins.push(format!(r#"{{"id":"{snapshot}_{kind}","mode":"{mode}","method":"少数の原始状態と操作を提示する。","locations":[{{"source":"scan","path":"{snapshot}.{kind}.model","span":[{},{}]}}]}}"#,start+shift,start+shift+1));
        }
        let subjects = [
            ("A", "Root"),
            ("B", "Root"),
            ("Z", "Root"),
            ("p", "State"),
            ("q", "State"),
            ("r", "State"),
            ("hA", "Hop"),
            ("hB", "Hop"),
            ("m", "Move"),
        ]
        .map(|(id, t)| {
            format!(r#"{{"id":"{id}","type":"Owned.{t}","origin":"{snapshot}_subjects"}}"#)
        })
        .join(",");
        let (a, b) = if snapshot == "v" {
            ("A", "B")
        } else {
            ("B", "A")
        };
        let mut atoms = vec![];
        for (id, entity, field, value) in [
            ("p", "State", "owner", reference(snapshot, a)),
            ("q", "State", "owner", reference(snapshot, b)),
            ("r", "State", "owner", reference(snapshot, a)),
            ("p", "State", "value", Json::str("2")),
            ("q", "State", "value", Json::str("7")),
            ("r", "State", "value", Json::str("3")),
            ("p", "State", "ok", Json::Bool(false_field != Some("p-ok"))),
            ("q", "State", "ok", Json::Bool(true)),
            ("r", "State", "ok", Json::Bool(false_field != Some("r-ok"))),
            ("hA", "Hop", "owner", reference(snapshot, a)),
            ("hA", "Hop", "from", reference(snapshot, "p")),
            ("hA", "Hop", "to", reference(snapshot, "p")),
            ("hB", "Hop", "owner", reference(snapshot, b)),
            ("hB", "Hop", "from", reference(snapshot, "q")),
            ("hB", "Hop", "to", reference(snapshot, "q")),
            ("m", "Move", "from", reference(snapshot, a)),
        ] {
            let atom = format!("{id}-{field}");
            if snapshot == "v" && omit == Some(atom.as_str()) {
                continue;
            }
            let kind = if field == "owner" { "owners" } else { "values" };
            atoms.push(format!(r#"{{"id":"{atom}","subject":"{id}","field":"Owned.{entity}.{field}","value":{},"origin":"{snapshot}_{kind}"}}"#,value.canonical()));
        }
        snapshots.push(format!(r#"{{"id":"{snapshot}","origin":"{snapshot}_subjects","subjects":[{subjects}],"atoms":[{}]}}"#,atoms.join(",")));
    }
    let (uri, revision) = if moved {
        ("urn:fixture:owned-family:moved", "r2")
    } else {
        ("urn:fixture:owned-family", "r1")
    };
    let map = format!(
        r#"{{"format":"archsig.archmap/2","semantics":"archsig/0.6.0","vocabularies":[{{"namespace":"Owned","version":"1","digest":"{digest}"}}],"sources":[{{"id":"scan","uri":"{uri}","revision":"{revision}","digest":"sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"}}],"origins":[{}],"snapshots":[{}]}}"#,
        origins.join(","),
        snapshots.join(",")
    );
    InputSources::from_bytes(
        vec![definitions.into_bytes()],
        law.into_bytes(),
        map.into_bytes(),
    )
}

fn unchanged(a: &CheckedInputs, b: &CheckedInputs) {
    assert_eq!(a.sources(), b.sources());
    assert_eq!(a.inputs(), b.inputs());
    assert_eq!(a.definitions(), b.definitions());
    assert_eq!(b.definitions(), &b.law().definitions);
    assert_eq!(a.law().declarations, b.law().declarations);
    assert_eq!(a.law().exprs, b.law().exprs);
    assert_eq!(a.law().expr_types, b.law().expr_types);
    assert_eq!(a.law().infos, b.law().infos);
    assert_eq!(a.law().model_digest, b.law().model_digest);
    assert_eq!(
        b.law().bytes_digest,
        sha256_digest(b.sources().law().bytes())
    );
    assert_eq!(a.archmap().snapshots, b.archmap().snapshots);
    assert_eq!(a.archmap().origins, b.archmap().origins);
    assert_eq!(a.archmap().sources, b.archmap().sources);
    assert_eq!(a.archmap().vocabularies, b.archmap().vocabularies);
    assert_eq!(a.archmap().model_digest, b.archmap().model_digest);
    assert_eq!(
        b.archmap().bytes_digest,
        sha256_digest(b.sources().archmap().bytes())
    );
}

fn audit(wire: &Json, checked: &CheckedInputs) {
    let ns = index(wire);
    let mut earlier = BTreeSet::new();
    for n in arr(f(wire, "nodes")) {
        let scope = f(n, "scope");
        assert_eq!(f(scope, "readings"), &Json::Arr(vec![Json::str("Inspect")]));
        assert!(arr(f(scope, "assumptions")).is_empty());
        for snapshot in arr(f(scope, "snapshots")) {
            assert!(
                checked
                    .archmap()
                    .snapshots
                    .iter()
                    .any(|s| s.id == text(snapshot))
            );
        }
        for mode in arr(f(scope, "modes")) {
            assert!(matches!(text(mode), "specification" | "proposed"));
        }
        for q in arr(f(scope, "quantifiers")) {
            if let Some(r) = obj(q).get("domain") {
                let domain = target(&ns, r, &Json::str("Domain"));
                assert_eq!(f(val(domain), "type"), f(q, "type"));
            }
        }
        let mut links = vec![];
        refs(n, &mut links);
        for link in links {
            assert!(earlier.contains(link.as_str()), "既出Ref {link}");
        }
        assert!(earlier.insert(text(f(n, "id"))));
        if f(n, "type") != &Json::str("Proposition") {
            assert!(!obj(n).contains_key("judgment"));
        }
        if f(n, "state") == &Json::str("blocked") {
            assert!(!obj(n).contains_key("value"));
            assert!(!arr(f(n, "reasons")).is_empty());
        }
        if let Some(value) = obj(n).get("value") {
            let mut consumed = vec![];
            refs(value, &mut consumed);
            for r in consumed {
                assert_ne!(f(ns[r.as_str()], "state"), &Json::str("blocked"));
                assert!(!obj(ns[r.as_str()]).contains_key("partial"));
            }
        }
        for pointer in arr(f(n, "support")) {
            let snapshot = checked
                .archmap()
                .snapshots
                .iter()
                .find(|s| s.id == text(f(pointer, "snapshot")))
                .unwrap();
            let subject = snapshot
                .subjects
                .iter()
                .find(|s| s.id == text(f(pointer, "subject")))
                .unwrap();
            let (origin, kind, start) = if let Some(field) = obj(pointer).get("field") {
                let slot = &subject
                    .fields
                    .iter()
                    .find(|f| f.name == text(field))
                    .unwrap()
                    .slot;
                let Slot::Known {
                    atom,
                    origin,
                    value,
                    pointer: at,
                } = slot
                else {
                    panic!("欠測は既知supportにしない")
                };
                assert_eq!(f(pointer, "atom"), &Json::str(atom));
                assert!(at.starts_with("/snapshots/") && at.ends_with("/value"));
                if f(f(n, "rule"), "kind") == &Json::str("atom") {
                    assert_eq!(val(n), &value.canonical_json());
                }
                (
                    origin,
                    if text(field).ends_with(".owner") {
                        "owners"
                    } else {
                        "values"
                    },
                    if text(field).ends_with(".owner") {
                        3
                    } else {
                        5
                    },
                )
            } else {
                (&subject.origin, "subjects", 1)
            };
            let origin = checked
                .archmap()
                .origins
                .iter()
                .find(|o| &o.id == origin)
                .unwrap();
            assert_eq!(
                origin.mode,
                if snapshot.id == "v" {
                    Mode::Specification
                } else {
                    Mode::Proposed
                }
            );
            assert_eq!(origin.locations.len(), 1);
            let location = &origin.locations[0];
            let source = checked
                .archmap()
                .sources
                .iter()
                .find(|s| s.id == location.source)
                .unwrap();
            let moved = source.revision == "r2";
            let shift = if moved { 20 } else { 0 };
            assert_eq!(location.path, format!("{}.{kind}.model", snapshot.id));
            assert_eq!(location.span, Some((start + shift, start + shift + 1)));
            assert_eq!(
                source.uri,
                if moved {
                    "urn:fixture:owned-family:moved"
                } else {
                    "urn:fixture:owned-family"
                }
            );
        }
        if f(n, "type") == &Json::str("Expression") && f(val(n), "kind") == &Json::str("source") {
            let at = span(f(val(n), "location"));
            assert!(at.0 < at.1 && at.1 <= checked.sources().law().bytes().len());
            assert_eq!(span(f(f(n, "rule"), "location")), at);
        }
        if f(n, "type") == &Json::str("Domain") && f(val(n), "kind") == &Json::str("finite") {
            for r in arr(f(val(n), "elements")) {
                target(&ns, r, f(val(n), "type"));
            }
        }
        if f(n, "type") == &Json::str("Evidence")
            && f(val(n), "kind") == &Json::str("finite_exhaustion")
        {
            let data = f(val(n), "data");
            assert_eq!(
                f(data, "checked"),
                &Json::Nat(arr(f(data, "instances")).len() as u64)
            );
            target(&ns, f(data, "domain"), &Json::str("Domain"));
            let domain = target(&ns, f(data, "domain"), &Json::str("Domain"));
            assert_eq!(
                f(data, "checked"),
                &Json::Nat(arr(f(val(domain), "elements")).len() as u64)
            );
        }
    }
    for a in arr(f(wire, "answers")) {
        let mut links = vec![];
        refs(a, &mut links);
        assert!(links.iter().all(|r| ns.contains_key(r.as_str())));
        if let Some(claim) = obj(a).get("claim") {
            let claim = target(&ns, claim, &Json::str("Proposition"));
            assert_eq!(f(f(claim, "judgment"), "status"), f(a, "status"));
        }
    }
    audit_family_occurrences(wire, checked);
}

fn source<'a>(ns: &BTreeMap<&str, &'a Json>, evaluation: &Json) -> &'a Json {
    target(
        ns,
        f(val(evaluation), "expression"),
        &Json::str("Expression"),
    )
}
fn at(ns: &BTreeMap<&str, &Json>, evaluation: &Json) -> (usize, usize) {
    span(f(val(source(ns, evaluation)), "location"))
}
fn audit_family_occurrences(wire: &Json, checked: &CheckedInputs) {
    let ns = index(wire);
    let mut families = 0;
    for evaluation in arr(f(wire, "nodes"))
        .iter()
        .filter(|n| f(n, "type") == &Json::str("Evaluation"))
    {
        let expression = source(&ns, evaluation);
        if f(val(expression), "kind") != &Json::str("source") {
            continue;
        }
        let position = at(&ns, evaluation);
        let Some((id, expr)) = checked
            .law()
            .exprs
            .iter()
            .enumerate()
            .find(|(_, e)| e.span == position)
        else {
            continue;
        };
        let ExprKind::Family { name, owner } = &expr.kind else {
            continue;
        };
        // 補完aggregateはcase評価を子に持つ。実Familyのowner辺を持つ評価だけを選ぶ。
        let parts = arr(f(val(evaluation), "parts"));
        if parts.len() != 1 {
            continue;
        }
        let children = arr(f(&parts[0], "children"));
        if children.len() != 1 {
            continue;
        }
        let owner_evaluation = target(&ns, &children[0], &Json::str("Evaluation"));
        if at(&ns, owner_evaluation) != checked.law().exprs[*owner].span {
            continue;
        }
        families += 1;
        assert_eq!(span(f(&parts[0], "location")), position);
        assert_eq!(
            f(val(expression), "bindings"),
            f(val(evaluation), "bindings")
        );
        assert_eq!(
            &checked.sources().law().bytes()[name.span().0..name.span().1],
            name.text().as_bytes()
        );
        let Type::Set(element) = checked.law().expr_type(id).unwrap() else {
            panic!("Family Set型")
        };
        let Type::Ref(entity) = element.as_ref() else {
            panic!("Family Ref要素型")
        };
        assert!(
            checked.law().infos.iter().any(|d| d
                .references
                .iter()
                .any(|(at, target)| *at == name.span() && target == entity)),
            "元族名の静的解決先を保持する"
        );
        let owner_parts = arr(f(val(owner_evaluation), "parts"));
        assert_eq!(owner_parts.len(), 1);
        assert_eq!(
            span(f(&owner_parts[0], "location")),
            checked.law().exprs[*owner].span
        );
        let original_arguments = arr(f(expression, "arguments"));
        for formal in original_arguments
            .iter()
            .filter(|r| f(ns[text(f(r, "node"))], "type") == &Json::str("Evaluation"))
        {
            assert!(
                arr(f(&owner_parts[0], "children")).contains(formal),
                "callの実owner引数Evaluationを保持する"
            );
        }
        if let ExprKind::Dotted(names) = &checked.law().exprs[*owner].kind {
            if names.len() == 1 {
                for lexical in &checked.law().exprs {
                    if let ExprKind::Let { name, value, body } = &lexical.kind {
                        if name.name == names[0].name
                            && checked.law().exprs[*body].span.0 <= position.0
                            && position.1 <= checked.law().exprs[*body].span.1
                        {
                            let children = arr(f(&owner_parts[0], "children"));
                            assert_eq!(children.len(), 1);
                            assert_eq!(
                                at(&ns, target(&ns, &children[0], &Json::str("Evaluation"))),
                                checked.law().exprs[*value].span
                            );
                        }
                    }
                }
            }
        }
        if let Some(owner_ref) = obj(val(owner_evaluation)).get("value") {
            let owner_value = val(target(&ns, owner_ref, &ty("Ref", Json::str("Owned.Root"))));
            let pair = arr(owner_value);
            if let ExprKind::Dotted(names) = &checked.law().exprs[*owner].kind {
                if names.len() == 1 {
                    if let Some(binding) = arr(f(val(expression), "bindings"))
                        .iter()
                        .find(|b| f(b, "name") == &Json::str(&names[0].name))
                    {
                        assert_eq!(
                            val(target(
                                &ns,
                                f(binding, "value"),
                                &ty("Ref", Json::str("Owned.Root"))
                            )),
                            owner_value
                        );
                    }
                }
            }
            if let Some(value_ref) = obj(val(evaluation)).get("value") {
                let scalar = target(&ns, value_ref, &checked.law().expr_type(id).unwrap().wire());
                assert_eq!(f(f(scalar, "rule"), "kind"), &Json::str("law"));
                assert_eq!(span(f(f(scalar, "rule"), "location")), position);
                assert_eq!(
                    arr(f(scalar, "arguments")),
                    &[
                        f(val(evaluation), "expression").clone(),
                        children[0].clone()
                    ]
                );
                let mut wanted: BTreeSet<_> = members(text(&pair[0]), text(&pair[1]), entity)
                    .iter()
                    .map(Json::canonical)
                    .collect();
                let mut actual: BTreeSet<_> =
                    arr(val(scalar)).iter().map(Json::canonical).collect();
                assert_eq!(arr(val(scalar)).len(), actual.len());
                let snapshot = checked
                    .archmap()
                    .snapshots
                    .iter()
                    .find(|s| s.id == text(&pair[0]))
                    .unwrap();
                assert!(arr(f(f(scalar, "scope"), "snapshots")).contains(&Json::str(&snapshot.id)));
                assert!(arr(f(f(scalar, "scope"), "modes")).contains(&Json::str(
                    if snapshot.id == "v" {
                        "specification"
                    } else {
                        "proposed"
                    }
                )));
                for candidate in snapshot.subjects.iter().filter(|s| &s.ty == entity) {
                    let field = candidate
                        .fields
                        .iter()
                        .find(|f| f.name == format!("{entity}.owner"))
                        .unwrap();
                    let Slot::Known { atom, .. } = &field.slot else {
                        assert_eq!(field.slot, Slot::Missing);
                        assert_eq!(
                            f(f(scalar, "scope"), "domain"),
                            &Json::str("all_completions")
                        );
                        // 元Missingを支持Atomへ偽装しない。所属が変わる実Set対は
                        // unknown()で元owner slotと併せて照合する。
                        let candidate_ref = reference(&snapshot.id, &candidate.id).canonical();
                        wanted.remove(&candidate_ref);
                        actual.remove(&candidate_ref);
                        for node in [scalar, evaluation] {
                            assert!(
                                !arr(f(node, "support"))
                                    .iter()
                                    .any(|fact| obj(fact).get("subject")
                                        == Some(&Json::str(&candidate.id))
                                        && obj(fact).get("field") == Some(&Json::str(&field.name)))
                            );
                        }
                        continue;
                    };
                    let fact = Json::obj([
                        ("snapshot", Json::str(&snapshot.id)),
                        ("subject", Json::str(&candidate.id)),
                        ("field", Json::str(&field.name)),
                        ("atom", Json::str(atom)),
                    ]);
                    assert!(
                        arr(f(scalar, "support")).contains(&fact),
                        "所属/非所属原ownerFactを保つ"
                    );
                    assert!(arr(f(evaluation, "support")).contains(&fact));
                }
                assert_eq!(actual, wanted);
            }
        }
        for fact in arr(f(owner_evaluation, "support")) {
            assert!(
                arr(f(evaluation, "support")).contains(fact),
                "owner子評価の支持を失わない"
            );
        }
    }
    if arr(f(wire, "answers"))
        .iter()
        .any(|a| f(a, "status") == &Json::str("established"))
    {
        assert!(families > 0, "実Family/owner子評価へ戻る");
    }
    audit_in_domains(wire, checked);
}
fn audit_in_domains(wire: &Json, checked: &CheckedInputs) {
    let ns = index(wire);
    for evaluation in arr(f(wire, "nodes"))
        .iter()
        .filter(|n| f(n, "type") == &Json::str("Evaluation"))
    {
        let expression = source(&ns, evaluation);
        if f(val(expression), "kind") != &Json::str("source") {
            continue;
        }
        let Some(expr) = checked
            .law()
            .exprs
            .iter()
            .find(|e| e.span == at(&ns, evaluation))
        else {
            continue;
        };
        let ExprKind::Quant {
            var,
            split:
                QuantSplit::Fixed {
                    domain: QuantDomain::In(input),
                    body,
                },
            ..
        } = &expr.kind
        else {
            continue;
        };
        if !matches!(checked.law().exprs[*input].kind, ExprKind::Family { .. }) {
            continue;
        }
        let parts = arr(f(val(evaluation), "parts"));
        if parts.len() != 1 {
            continue;
        }
        let children = arr(f(&parts[0], "children"));
        let Some(first) = children.first() else {
            continue;
        };
        let family = target(&ns, first, &Json::str("Evaluation"));
        if at(&ns, family) != checked.law().exprs[*input].span {
            continue;
        }
        let Some(family_value) = obj(val(family)).get("value") else {
            continue;
        };
        let items = arr(val(target(
            &ns,
            family_value,
            &checked.law().expr_type(*input).unwrap().wire(),
        )));
        let domains: Vec<_> = arr(f(wire, "nodes"))
            .iter()
            .filter(|n| {
                f(n, "type") == &Json::str("Domain")
                    && arr(f(n, "arguments")).get(..2)
                        == Some(&[f(val(evaluation), "expression").clone(), first.clone()][..])
            })
            .collect();
        assert_eq!(domains.len(), 1, "各Inの実域");
        let domain = domains[0];
        let elements = arr(f(val(domain), "elements"));
        assert_eq!(elements.len(), items.len());
        assert_eq!(children.len(), items.len() + 1, "欠測bodyも実反復に残す");
        assert_eq!(
            &checked.sources().law().bytes()[var.span.0..var.span.1],
            var.name.as_bytes()
        );
        for ((child, member), item) in children[1..].iter().zip(elements).zip(items) {
            let body_eval = target(&ns, child, &Json::str("Evaluation"));
            assert_eq!(at(&ns, body_eval), checked.law().exprs[*body].span);
            assert_eq!(val(target(&ns, member, f(val(domain), "type"))), item);
            let body_source = source(&ns, body_eval);
            assert!(
                arr(f(body_source, "arguments")).contains(member),
                "元binderの実member producerへ戻る"
            );
        }
    }
}
fn run(inputs: InputSources, asks: &[&str]) -> ObservedEvaluation {
    let checked = check_inputs(inputs.clone(), &mut quiet()).unwrap();
    let result = evaluate_observed_bytes(inputs, asks, &mut quiet()).unwrap();
    unchanged(&checked, result.prepared().inputs());
    audit(&result.wire(), result.prepared().inputs());
    result
}

// 原fixtureのowner配置による独立期待。生成Setの要素から期待をコピーしない。
fn members(snapshot: &str, owner: &str, entity: &str) -> Vec<Json> {
    let a = if snapshot == "v" { "A" } else { "B" };
    let b = if snapshot == "v" { "B" } else { "A" };
    let ids = match (entity, owner) {
        ("Owned.State", o) if o == a => vec!["p", "r"],
        ("Owned.State", o) if o == b => vec!["q"],
        ("Owned.Hop", o) if o == a => vec!["hA"],
        ("Owned.Hop", o) if o == b => vec!["hB"],
        (_, "Z") => vec![],
        _ => panic!("未提示の族"),
    };
    ids.into_iter().map(|id| reference(snapshot, id)).collect()
}

#[test]
fn owned_entity_family_sets_distinguish_owners_and_same_ids_in_two_snapshots() {
    let r = run(
        fixture(
            "view states(a:Root):Set<State> = State[a];",
            None,
            None,
            true,
            false,
        ),
        &[
            "a=evaluate(Inspect.states,a=@v/A)",
            "b=evaluate(Inspect.states,a=@v/B)",
            "w=evaluate(Inspect.states,a=@w/A)",
        ],
    );
    let w = r.wire();
    output_set(&w, "a", "Owned.State", &members("v", "A", "Owned.State"));
    output_set(&w, "b", "Owned.State", &members("v", "B", "Owned.State"));
    output_set(&w, "w", "Owned.State", &members("w", "A", "Owned.State"));
}
#[test]
fn owned_arrow_family_uses_declared_owner_and_current_snapshot() {
    let r = run(
        fixture(
            "view hops(a:Root):Set<Hop> = Hop[a];",
            None,
            None,
            true,
            false,
        ),
        &[
            "v=evaluate(Inspect.hops,a=@v/A)",
            "w=evaluate(Inspect.hops,a=@w/A)",
        ],
    );
    let w = r.wire();
    output_set(&w, "v", "Owned.Hop", &members("v", "A", "Owned.Hop"));
    output_set(&w, "w", "Owned.Hop", &members("w", "A", "Owned.Hop"));
}
#[test]
fn owned_arrow_missing_owner_uses_endpoint_constraints_and_keeps_original_missing() {
    let r = run(
        fixture(
            "view hops(a:Root):Set<Hop> = Hop[a];",
            Some("hA-owner"),
            None,
            false,
            false,
        ),
        &["a=evaluate(Inspect.hops,a=@v/A)"],
    );
    let w = r.wire();
    output_set(&w, "a", "Owned.Hop", &[reference("v", "hA")]);
    assert_missing(&w, "a", "hA", "Owned.Hop.owner");
    assert_eq!(
        f(f(answer(&w, "a"), "scope"), "domain"),
        &Json::str("all_completions")
    );
    let ns = index(&w);
    let domains: Vec<_> = ns
        .values()
        .filter(|n| {
            f(n, "type") == &Json::str("Domain")
                && arr(f(n, "arguments")).first().is_some_and(|r| {
                    let node = ns[text(f(r, "node"))];
                    obj(node)
                        .get("value")
                        .is_some_and(|v| obj(v).get("kind") == Some(&Json::str("source")))
                })
        })
        .collect();
    assert!(!domains.is_empty());
    for domain in domains {
        assert_eq!(f(val(domain), "type"), &ty("Ref", Json::str("Owned.Root")));
        let elements = arr(f(val(domain), "elements"));
        assert_eq!(elements.len(), 1);
        assert_eq!(
            val(target(
                &ns,
                &elements[0],
                &ty("Ref", Json::str("Owned.Root"))
            )),
            &reference("v", "A")
        );
        for atom in ["hA-from", "hA-to"] {
            assert!(
                arr(f(domain, "support"))
                    .iter()
                    .any(|fact| obj(fact).get("atom") == Some(&Json::str(atom)))
            );
        }
    }
    let candidate = &r.prepared().inputs().archmap().snapshots[0]
        .subjects
        .iter()
        .find(|s| s.id == "hA")
        .unwrap();
    assert_eq!(
        candidate
            .fields
            .iter()
            .find(|f| f.name == "Owned.Hop.owner")
            .unwrap()
            .slot,
        Slot::Missing
    );
    assert!(
        !arr(f(answer(&w, "a"), "reasons"))
            .iter()
            .any(|r| f(r, "code") == &Json::str("unsupported_algorithm"))
    );
}

#[test]
fn owned_family_count_and_numeric_comprehension_sum_keep_members() {
    let r = run(
        fixture(
            "view size(a:Root):Z=count(State[a]); view total(a:Root):Z=sum(set{s.value|s in State[a]});",
            None,
            None,
            false,
            false,
        ),
        &[
            "n=evaluate(Inspect.size,a=@v/A)",
            "s=evaluate(Inspect.total,a=@v/A)",
        ],
    );
    let w = r.wire();
    output(&w, "n", &Json::str("Z"), &Json::str("2"));
    output(&w, "s", &Json::str("Z"), &Json::str("5"));
}
#[test]
fn owned_family_repeated_occurrences_keep_extensional_set_equality_and_source_spans() {
    let r = run(
        fixture(
            "view equal(a:Root):Bool=State[a]=set{s|s in State[a]};",
            None,
            None,
            false,
            false,
        ),
        &["same=evaluate(Inspect.equal,a=@v/A)"],
    );
    let w = r.wire();
    output(&w, "same", &Json::str("Bool"), &Json::Bool(true));
    let checked = r.prepared().inputs();
    let ns = index(&w);
    let spans: BTreeSet<_> = checked
        .law()
        .exprs
        .iter()
        .filter(|e| matches!(e.kind, ExprKind::Family { .. }))
        .map(|e| e.span)
        .collect();
    assert_eq!(spans.len(), 2);
    for position in spans {
        assert!(
            arr(f(&w, "nodes"))
                .iter()
                .any(|n| f(n, "type") == &Json::str("Evaluation")
                    && f(val(source(&ns, n)), "kind") == &Json::str("source")
                    && at(&ns, n) == position),
            "同値な二つの元Family出現を統合しない"
        );
    }
}
#[test]
fn owned_family_in_quantifiers_keep_domain_binder_and_full_evidence() {
    let r = run(
        fixture(
            "law required positive(a:Root):forall s in State[a] . s.value>0; view exists_state(a:Root):Bool=exists t in State[a] . t.value=3;",
            None,
            None,
            false,
            false,
        ),
        &[
            "all=check(Inspect.positive,a=@v/A)",
            "found=evaluate(Inspect.exists_state,a=@v/A)",
        ],
    );
    let w = r.wire();
    assert_eq!(f(answer(&w, "all"), "status"), &Json::str("established"));
    output(&w, "found", &Json::str("Bool"), &Json::Bool(true));
}
#[test]
fn owned_empty_family_keeps_typed_zero_and_zero_instance_forall_exists() {
    let r = run(
        fixture(
            "view size(a:Root):Z=count(State[a]);view total(a:Root):Z=sum(set{s.value|s in State[a]});view all(a:Root):Bool=forall s in State[a] . s.ok;view any_state(a:Root):Bool=exists s in State[a] . s.ok;",
            None,
            None,
            false,
            false,
        ),
        &[
            "n=evaluate(Inspect.size,a=@v/Z)",
            "z=evaluate(Inspect.total,a=@v/Z)",
            "a=evaluate(Inspect.all,a=@v/Z)",
            "e=evaluate(Inspect.any_state,a=@v/Z)",
        ],
    );
    let w = r.wire();
    for id in ["n", "z"] {
        output(&w, id, &Json::str("Z"), &Json::str("0"));
    }
    output(&w, "a", &Json::str("Bool"), &Json::Bool(true));
    output(&w, "e", &Json::str("Bool"), &Json::Bool(false));
}
#[test]
fn owned_empty_family_still_rejects_invalid_body_at_original_span() {
    let inputs = fixture(
        "view invalid(a:Root):Bool=forall s in State[a] . s.absent;",
        None,
        None,
        false,
        false,
    );
    let failure = evaluate_observed_bytes(
        inputs.clone(),
        &["bad=evaluate(Inspect.invalid,a=@v/Z)"],
        &mut quiet(),
    )
    .unwrap_err();
    let w = failure.wire().unwrap();
    assert_eq!(f(&w, "status"), &Json::str("invalid"));
    assert!(arr(f(&w, "nodes")).is_empty());
    assert!(arr(f(&w, "answers")).is_empty());
    assert!(arr(f(&w, "issues")).iter().any(|i| {
        let p = span(f(i, "location"));
        inputs.law().bytes()[p.0..p.1]
            .windows(6)
            .any(|s| s == b"absent")
    }));
}
#[test]
fn owned_family_owner_field_and_lexical_alias_keep_original_producers() {
    let r = run(
        fixture(
            "view direct(m:Move):Set<State> = State[m.from];view alias(m:Move):Set<State> = let x=m.from in State[x];",
            None,
            None,
            false,
            false,
        ),
        &[
            "d=evaluate(Inspect.direct,m=@v/m)",
            "l=evaluate(Inspect.alias,m=@v/m)",
        ],
    );
    let w = r.wire();
    for id in ["d", "l"] {
        output_set(&w, id, "Owned.State", &members("v", "A", "Owned.State"));
    }
}
#[test]
fn owned_family_inside_plain_view_call_keeps_call_and_parameter_occurrences() {
    let r = run(
        fixture(
            "view inner(x:Root):Set<State> = State[x];view outer(a:Root):Set<State> = inner(a);",
            None,
            None,
            false,
            false,
        ),
        &["c=evaluate(Inspect.outer,a=@v/A)"],
    );
    output_set(
        &r.wire(),
        "c",
        "Owned.State",
        &members("v", "A", "Owned.State"),
    );
}
#[test]
fn owned_family_inside_outer_ref_binder_keeps_each_iteration_owner() {
    let r = run(
        fixture(
            "view every():Bool=forall a:Root . count(State[a])>=0;",
            None,
            None,
            false,
            false,
        ),
        &["all=evaluate(Inspect.every)"],
    );
    output(&r.wire(), "all", &Json::str("Bool"), &Json::Bool(true));
}
#[test]
fn owned_family_missing_numeric_body_keeps_subject_count_and_missing_slot() {
    let r = run(
        fixture(
            "view size(a:Root):Z=count(State[a]);view total(a:Root):Z=sum(set{s.value|s in State[a]});",
            Some("p-value"),
            None,
            false,
            false,
        ),
        &[
            "n=evaluate(Inspect.size,a=@v/A)",
            "s=evaluate(Inspect.total,a=@v/A)",
        ],
    );
    let w = r.wire();
    output(&w, "n", &Json::str("Z"), &Json::str("2"));
    assert_eq!(f(answer(&w, "s"), "status"), &Json::str("undetermined"));
    assert_missing(&w, "s", "p", "Owned.State.value");
}
fn assert_missing(w: &Json, id: &str, subject: &str, field: &str) {
    let reasons = arr(f(answer(w, id), "reasons"));
    let missing = reasons
        .iter()
        .find(|r| f(r, "code") == &Json::str("missing_observation"))
        .unwrap();
    assert!(arr(f(missing, "missing")).contains(&Json::obj([
        ("snapshot", Json::str("v")),
        ("subject", Json::str(subject)),
        ("field", Json::str(field))
    ])));
    assert!(!arr(f(missing, "dependencies")).is_empty());
    assert_eq!(
        f(f(answer(w, id), "scope"), "domain"),
        &Json::str("all_completions")
    );
}
fn missing_counterexample(omit: &str, false_field: &str, missing_subject: &str) {
    let r = run(
        fixture(
            "law required all(a:Root):forall s in State[a] . s.ok;view size(a:Root):Z=count(State[a]);",
            Some(omit),
            Some(false_field),
            false,
            false,
        ),
        &[
            "ok=check(Inspect.all,a=@v/A)",
            "n=evaluate(Inspect.size,a=@v/A)",
        ],
    );
    let w = r.wire();
    assert_eq!(f(answer(&w, "ok"), "status"), &Json::str("refuted"));
    assert_missing(&w, "ok", missing_subject, "Owned.State.ok");
    output(&w, "n", &Json::str("Z"), &Json::str("2"));
    let ns = index(&w);
    let false_subject = false_field.strip_suffix("-ok").unwrap();
    let known_fact = Json::obj([
        ("snapshot", Json::str("v")),
        ("subject", Json::str(false_subject)),
        ("field", Json::str("Owned.State.ok")),
        ("atom", Json::str(false_field)),
    ]);
    let examples: Vec<_> = arr(f(&w, "nodes"))
        .iter()
        .filter(|n| {
            f(n, "type") == &Json::str("Evidence")
                && f(val(n), "kind") == &Json::str("counterexample")
                && arr(f(f(val(n), "data"), "facts")).contains(&known_fact)
                && arr(f(f(val(n), "data"), "bindings"))
                    .iter()
                    .any(|b| f(b, "name") == &Json::str("s"))
        })
        .collect();
    assert!(!examples.is_empty(), "元既知反例の原始支持を保持する");
    for example in examples {
        let data = f(val(example), "data");
        assert_eq!(
            val(target(&ns, f(data, "left"), &Json::str("Bool"))),
            &Json::Bool(false)
        );
        assert_eq!(
            val(target(&ns, f(data, "right"), &Json::str("Bool"))),
            &Json::Bool(true)
        );
        assert!(
            arr(f(data, "bindings"))
                .iter()
                .any(|b| f(b, "name") == &Json::str("s")
                    && val(target(
                        &ns,
                        f(b, "value"),
                        &ty("Ref", Json::str("Owned.State"))
                    )) == &reference("v", false_subject)),
            "反例の元In binderを保持する"
        );
    }
    assert!(
        arr(f(&w, "nodes"))
            .iter()
            .any(|n| f(n, "type") == &Json::str("Evidence")
                && f(val(n), "kind") == &Json::str("counterexample"))
    );
}
#[test]
fn owned_family_missing_body_before_known_counterexample_preserves_membership() {
    missing_counterexample("p-ok", "r-ok", "p");
}
#[test]
fn owned_family_missing_body_after_known_counterexample_preserves_membership() {
    missing_counterexample("r-ok", "p-ok", "r");
}
fn unknown(
    omit: &str,
    script: &str,
    ask: &str,
    subject: &str,
    field: &str,
    owner_expression: bool,
) {
    let r = run(fixture(script, Some(omit), None, false, false), &[ask]);
    let w = r.wire();
    assert_eq!(f(&w, "status"), &Json::str("partial"));
    let answer = answer(&w, "u");
    assert_eq!(f(answer, "status"), &Json::str("undetermined"));
    assert_missing(&w, "u", subject, field);
    let reasons = arr(f(answer, "reasons"));
    assert!(
        !reasons
            .iter()
            .any(|r| f(r, "code") == &Json::str("unsupported_algorithm"))
    );
    let reason = reasons
        .iter()
        .find(|r| f(r, "code") == &Json::str("missing_observation"))
        .unwrap();
    let ns = index(&w);
    let checked = r.prepared().inputs();
    let family = checked
        .law()
        .exprs
        .iter()
        .find(|e| matches!(e.kind, ExprKind::Family { .. }))
        .unwrap();
    let wanted_span = if owner_expression {
        let law = checked.sources().law().bytes();
        let start = law
            .windows(b"m.from".len())
            .position(|b| b == b"m.from")
            .unwrap();
        (start, start + b"m.from".len())
    } else {
        family.span
    };
    assert_eq!(span(f(reason, "location")), wanted_span);
    assert_eq!(
        checked.law().expr_type(
            checked
                .law()
                .exprs
                .iter()
                .position(|e| e.span == family.span)
                .unwrap()
        ),
        Some(&Type::Set(Box::new(Type::Ref("Owned.State".into()))))
    );
    let dependencies = arr(f(reason, "dependencies"));
    assert_eq!(dependencies.len(), 1);
    let expression = target(&ns, &dependencies[0], &Json::str("Expression"));
    assert_eq!(span(f(val(expression), "location")), wanted_span);
    assert!(arr(f(expression, "reasons")).is_empty());
    assert!(!obj(f(answer, "outputs")).contains_key("value"));
    let evaluation = target(
        &ns,
        f(f(answer, "outputs"), "evaluation"),
        &Json::str("Evaluation"),
    );
    let domain = target(
        &ns,
        &arr(f(evaluation, "arguments"))[1],
        &Json::str("Domain"),
    );
    assert_eq!(f(val(domain), "type"), &ty("Ref", Json::str("Owned.Root")));
    let domain_values: BTreeSet<_> = arr(f(val(domain), "elements"))
        .iter()
        .map(|r| val(target(&ns, r, &ty("Ref", Json::str("Owned.Root")))).canonical())
        .collect();
    assert_eq!(
        domain_values,
        ["A", "B", "Z"]
            .map(|id| reference("v", id).canonical())
            .into_iter()
            .collect()
    );
    let wanted: BTreeSet<String> = if owner_expression {
        [
            Json::Arr(vec![]),
            Json::Arr(vec![reference("v", "p"), reference("v", "r")]),
            Json::Arr(vec![reference("v", "q")]),
        ]
        .iter()
        .map(Json::canonical)
        .collect()
    } else {
        [
            Json::Arr(vec![reference("v", "p")]),
            Json::Arr(vec![reference("v", "p"), reference("v", "r")]),
        ]
        .iter()
        .map(Json::canonical)
        .collect()
    };
    let parts = arr(f(val(evaluation), "parts"));
    assert_eq!(parts.len(), 1);
    let cases = arr(f(&parts[0], "children"));
    assert_eq!(cases.len(), 3);
    let actual: BTreeSet<_> = cases
        .iter()
        .map(|c| {
            let e = target(&ns, c, &Json::str("Evaluation"));
            val(target(
                &ns,
                f(val(e), "value"),
                &ty("Set", ty("Ref", Json::str("Owned.State"))),
            ))
            .canonical()
        })
        .collect();
    assert_eq!(actual, wanted);
    let pairs:Vec<_>=arr(f(answer,"evidence")).iter().map(|r|ns[text(f(r,"node"))]).filter(|n|obj(n).get("value").is_some_and(|v|if let Json::Obj(m)=v{m.get("kind")}else{None}==Some(&Json::str("completion_pair")))).collect();
    assert!(!pairs.is_empty());
    for pair in pairs {
        let data = f(val(pair), "data");
        let fields = arr(f(data, "fields"));
        assert_eq!(fields.len(), 1);
        assert_eq!(f(&fields[0], "subject"), &Json::str(subject));
        assert_eq!(f(&fields[0], "field"), &Json::str(field));
        let values: BTreeSet<_> = ["first_result", "second_result"]
            .iter()
            .map(|key| {
                let e = target(&ns, f(data, key), &Json::str("Evaluation"));
                val(target(
                    &ns,
                    f(val(e), "value"),
                    &ty("Set", ty("Ref", Json::str("Owned.State"))),
                ))
                .canonical()
            })
            .collect();
        assert_eq!(values.len(), 2);
        assert!(values.is_subset(&wanted));
        if !owner_expression {
            assert_eq!(values, wanted);
        }
    }
}
#[test]
fn owned_family_missing_owner_expression_keeps_source_type_and_all_completions() {
    unknown(
        "m-from",
        "view states(m:Move):Set<State> = State[m.from];",
        "u=evaluate(Inspect.states,m=@v/m)",
        "m",
        "Owned.Move.from",
        true,
    );
}
#[test]
fn owned_family_missing_candidate_owner_does_not_drop_subject_into_success() {
    unknown(
        "r-owner",
        "view states(a:Root):Set<State> = State[a];",
        "u=evaluate(Inspect.states,a=@v/A)",
        "r",
        "Owned.State.owner",
        false,
    );
}
#[test]
fn owned_family_provenance_move_preserves_set_and_current_owner_sources() {
    let script = "view states(a:Root):Set<State> = State[a];";
    let asks = ["a=evaluate(Inspect.states,a=@v/A)"];
    let a = run(fixture(script, None, None, false, false), &asks);
    let b = run(fixture(script, None, None, false, true), &asks);
    for r in [&a, &b] {
        output_set(
            &r.wire(),
            "a",
            "Owned.State",
            &members("v", "A", "Owned.State"),
        );
    }
    let a = a.prepared().inputs();
    let b = b.prepared().inputs();
    assert_eq!(a.definitions(), b.definitions());
    assert_eq!(a.law().model_digest, b.law().model_digest);
    assert_eq!(a.archmap().snapshots, b.archmap().snapshots);
    assert_ne!(a.archmap().model_digest, b.archmap().model_digest);
}
