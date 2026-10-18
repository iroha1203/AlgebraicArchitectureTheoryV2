//! 既知 owner と二段以上の束縛 prefix に従う有限 Law parameter 族を元三入力 byte から検査する。
mod common;

use archsig::{
    archmap::{Mode, Slot},
    canonical::{Json, sha256_digest},
    definition::check_definitions_controlled,
    law::model::Signature,
    observed::{
        ObservedEvaluation,
        control::{Control, Limits, Usage},
        evaluate_observed_bytes,
        input::{CheckedInputs, InputSources, check_inputs},
        request::Selector,
    },
    types::Type,
};
use std::collections::{BTreeMap, BTreeSet};

const CHAIN: &str = "law required chain(a: Root, b: Child[a], c: Leaf[a]) when true: c.ok;";
const MIXED: &str =
    "law required chain(a: Root, b: Child[a], c: Leaf[a], flag: Bool) when true: c.ok or flag;";

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
    obj(j)
        .get(key)
        .unwrap_or_else(|| panic!("missing {key}; keys {:?}", obj(j).keys()))
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
fn target<'a>(ns: &BTreeMap<&str, &'a Json>, r: &Json, ty: &Json) -> &'a Json {
    assert_eq!(obj(r).len(), 1);
    let node = ns[text(f(r, "node"))];
    assert_eq!(f(node, "type"), ty);
    node
}
fn subject(snapshot: &str, id: &str) -> Json {
    Json::Arr(vec![Json::str(snapshot), Json::str(id)])
}
fn ref_type(name: &str) -> Json {
    Json::Arr(vec![Json::str("Ref"), Json::str(format!("Dep.{name}"))])
}
fn span(location: &Json) -> (usize, usize) {
    assert_eq!(f(location, "input"), &Json::str("law"));
    let a = arr(f(location, "span"));
    let nat = |j: &Json| match j {
        Json::Nat(n) => *n as usize,
        _ => panic!("Nat"),
    };
    assert_eq!(a.len(), 2);
    (nat(&a[0]), nat(&a[1]))
}
fn refs(j: &Json, out: &mut Vec<String>) {
    match j {
        Json::Obj(m) if m.len() == 1 && m.contains_key("node") => out.push(text(&m["node"]).into()),
        Json::Obj(m) => m.values().for_each(|v| refs(v, out)),
        Json::Arr(a) => a.iter().for_each(|v| refs(v, out)),
        _ => {}
    }
}
fn reachable(ns: &BTreeMap<&str, &Json>, root: &Json) -> BTreeSet<String> {
    let mut todo = vec![];
    refs(root, &mut todo);
    let mut seen = BTreeSet::new();
    while let Some(id) = todo.pop() {
        if seen.insert(id.clone()) {
            refs(ns[id.as_str()], &mut todo);
        }
    }
    seen
}
fn fixture(
    script: &str,
    flags: [Option<bool>; 2],
    second: bool,
    unknown_owner: bool,
    moved: bool,
) -> InputSources {
    use common::{definition_json, entity_json, field_json, vocabulary_json};
    let root = entity_json("Dep.Root", "[]", "[]");
    let child = entity_json(
        "Dep.Child",
        &format!("[{}]", field_json("owner", r#"["Ref","Dep.Root"]"#)),
        "[]",
    );
    let leaf = entity_json(
        "Dep.Leaf",
        &format!("[{}]", field_json("owner", r#"["Ref","Dep.Root"]"#)),
        &format!("[{}]", field_json("ok", r#""Bool""#)),
    );
    let definitions = definition_json(&format!(
        "[{}]",
        vocabulary_json("Dep", &format!("[{root},{child},{leaf}]"), "[]")
    ));
    let checked =
        check_definitions_controlled(&[("definition0", definitions.as_bytes())], &mut quiet())
            .unwrap();
    let digest = &checked.vocabularies["Dep"].digest;
    let law = format!(
        r#"law "archsig.law/2" semantics "archsig/0.6.0"; reading Inspect {{ use vocabulary Dep version "1" digest "{digest}"; {script} }}"#
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
            origins.push(format!(r#"{{"id":"{snapshot}_{kind}","mode":"{mode}","method":"小さい依存参照族を提示する。","locations":[{{"source":"scan","path":"{snapshot}.{kind}.model","span":[{},{}]}}]}}"#, start+shift, start+shift+1));
        }
        let subjects = [
            ("A", "Root"),
            ("B", "Root"),
            ("Z", "Root"),
            ("p", "Child"),
            ("q", "Child"),
            ("l", "Leaf"),
            ("m", "Leaf"),
        ]
        .map(|(id, ty)| {
            format!(r#"{{"id":"{id}","type":"Dep.{ty}","origin":"{snapshot}_subjects"}}"#)
        })
        .join(",");
        let mut atoms = vec![];
        let (p_owner, q_owner) = if snapshot == "v" {
            ("A", "B")
        } else {
            ("B", "A")
        };
        for (id, ty, owner) in [
            ("p", "Child", p_owner),
            ("q", "Child", q_owner),
            ("l", "Leaf", p_owner),
            ("m", "Leaf", q_owner),
        ] {
            if unknown_owner && snapshot == "v" && id == "p" {
                continue;
            }
            atoms.push(format!(r#"{{"id":"{id}-owner","subject":"{id}","field":"Dep.{ty}.owner","value":["{snapshot}","{owner}"],"origin":"{snapshot}_owners"}}"#));
        }
        for (id, value) in ["l", "m"].into_iter().zip(if snapshot == "v" {
            flags
        } else {
            [Some(true), Some(true)]
        }) {
            if let Some(value) = value {
                atoms.push(format!(r#"{{"id":"{id}-ok","subject":"{id}","field":"Dep.Leaf.ok","value":{value},"origin":"{snapshot}_values"}}"#));
            }
        }
        snapshots.push(format!(r#"{{"id":"{snapshot}","origin":"{snapshot}_subjects","subjects":[{subjects}],"atoms":[{}]}}"#, atoms.join(",")));
    }
    let (uri, revision) = if moved {
        ("urn:fixture:dependent:moved", "r2")
    } else {
        ("urn:fixture:dependent", "r1")
    };
    let map = format!(
        r#"{{"format":"archsig.archmap/2","semantics":"archsig/0.6.0","vocabularies":[{{"namespace":"Dep","version":"1","digest":"{digest}"}}],"sources":[{{"id":"scan","uri":"{uri}","revision":"{revision}","digest":"sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"}}],"origins":[{}],"snapshots":[{}]}}"#,
        origins.join(","),
        snapshots.join(",")
    );
    InputSources::from_bytes(
        vec![definitions.into_bytes()],
        law.into_bytes(),
        map.into_bytes(),
    )
}

fn unchanged(before: &CheckedInputs, after: &CheckedInputs) {
    assert_eq!(before.sources(), after.sources());
    assert_eq!(before.inputs(), after.inputs());
    assert_eq!(before.definitions(), after.definitions());
    assert_eq!(after.definitions(), &after.law().definitions);
    assert_eq!(before.law().declarations, after.law().declarations);
    assert_eq!(before.law().exprs, after.law().exprs);
    assert_eq!(before.law().expr_types, after.law().expr_types);
    assert_eq!(before.law().infos, after.law().infos);
    assert_eq!(before.law().model_digest, after.law().model_digest);
    assert_eq!(
        after.law().bytes_digest,
        sha256_digest(after.sources().law().bytes())
    );
    assert_eq!(before.archmap().snapshots, after.archmap().snapshots);
    assert_eq!(before.archmap().vocabularies, after.archmap().vocabularies);
    assert_eq!(before.archmap().origins, after.archmap().origins);
    assert_eq!(before.archmap().sources, after.archmap().sources);
    assert_eq!(before.archmap().model_digest, after.archmap().model_digest);
    assert_eq!(
        after.archmap().bytes_digest,
        sha256_digest(after.sources().archmap().bytes())
    );
}

fn audit(wire: &Json, checked: &CheckedInputs) {
    let ns = index(wire);
    let mut earlier = BTreeSet::new();
    for node in arr(f(wire, "nodes")) {
        let mut links = vec![];
        refs(node, &mut links);
        for link in links {
            assert!(earlier.contains(link.as_str()), "既出 Ref {link}");
        }
        assert!(earlier.insert(text(f(node, "id"))));
        if f(node, "type") != &Json::str("Proposition") {
            assert!(!obj(node).contains_key("judgment"));
        }
        if f(node, "state") == &Json::str("blocked") {
            assert!(!obj(node).contains_key("value"));
            assert!(!arr(f(node, "reasons")).is_empty());
        }
        if let Some(value) = obj(node).get("value") {
            let mut consumed = vec![];
            refs(value, &mut consumed);
            for r in consumed {
                assert_ne!(f(ns[r.as_str()], "state"), &Json::str("blocked"));
                assert!(!obj(ns[r.as_str()]).contains_key("partial"));
            }
        }
        if f(node, "type") == &Json::str("Expression")
            && f(val(node), "kind") == &Json::str("source")
        {
            let position = span(f(val(node), "location"));
            assert!(position.0 < position.1 && position.1 <= checked.sources().law().bytes().len());
            assert_eq!(span(f(f(node, "rule"), "location")), position);
        }
        if f(node, "type") == &Json::str("Domain") && f(val(node), "kind") == &Json::str("type") {
            assert!([Json::str("Z"), Json::str("Q")].contains(f(val(node), "type")));
            assert!(!obj(val(node)).contains_key("elements"));
        } else if f(node, "type") == &Json::str("Domain") {
            assert_eq!(f(val(node), "kind"), &Json::str("finite"));
            let elements = arr(f(val(node), "elements"));
            let mut seen = BTreeSet::new();
            for r in elements {
                let v = val(target(&ns, r, f(val(node), "type")));
                assert!(seen.insert(v.canonical()), "実Domainの重複を除く");
            }
        }
        for pointer in arr(f(node, "support")) {
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
            let (origin_id, kind, start) = if let Some(field) = obj(pointer).get("field") {
                let slot = &subject
                    .fields
                    .iter()
                    .find(|f| f.name == text(field))
                    .unwrap()
                    .slot;
                let Slot::Known {
                    atom,
                    origin,
                    pointer: input_at,
                    ..
                } = slot
                else {
                    panic!("欠測はsupportへ追加しない")
                };
                assert_eq!(f(pointer, "atom"), &Json::str(atom));
                assert!(input_at.starts_with("/snapshots/") && input_at.ends_with("/value"));
                if text(field).ends_with(".owner") {
                    (origin, "owners", 3)
                } else {
                    (origin, "values", 5)
                }
            } else {
                (&subject.origin, "subjects", 1)
            };
            let origin = checked
                .archmap()
                .origins
                .iter()
                .find(|o| &o.id == origin_id)
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
                    "urn:fixture:dependent:moved"
                } else {
                    "urn:fixture:dependent"
                }
            );
        }
    }
    for answer in arr(f(wire, "answers")) {
        let mut links = vec![];
        refs(answer, &mut links);
        assert!(links.iter().all(|r| ns.contains_key(r.as_str())));
        if let Some(claim) = obj(answer).get("claim") {
            let claim = target(&ns, claim, &Json::str("Proposition"));
            assert_eq!(f(f(claim, "judgment"), "status"), f(answer, "status"));
        } else if f(answer, "status") == &Json::str("established") {
            let request = arr(f(wire, "requests"))
                .iter()
                .find(|r| f(r, "id") == f(answer, "id"))
                .unwrap();
            assert_eq!(f(request, "kind"), &Json::str("evaluate"));
            assert!(obj(f(answer, "outputs")).contains_key("value"));
        } else {
            assert_eq!(f(answer, "status"), &Json::str("undetermined"));
        }
    }
}

fn run(inputs: InputSources, ask: &str) -> ObservedEvaluation {
    let checked = check_inputs(inputs.clone(), &mut quiet()).unwrap();
    let result = evaluate_observed_bytes(inputs, &[ask], &mut quiet()).unwrap();
    unchanged(&checked, result.prepared().inputs());
    audit(&result.wire(), result.prepared().inputs());
    result
}

fn binding_values(ns: &BTreeMap<&str, &Json>, bindings: &Json, mixed: bool) -> Vec<Json> {
    let expected = if mixed {
        vec![
            ("a", ref_type("Root")),
            ("b", ref_type("Child")),
            ("c", ref_type("Leaf")),
            ("flag", Json::str("Bool")),
        ]
    } else {
        vec![
            ("a", ref_type("Root")),
            ("b", ref_type("Child")),
            ("c", ref_type("Leaf")),
        ]
    };
    let bindings = arr(bindings);
    assert_eq!(bindings.len(), expected.len());
    bindings
        .iter()
        .zip(expected)
        .map(|(b, (name, ty))| {
            assert_eq!(f(b, "name"), &Json::str(name));
            val(target(ns, f(b, "value"), &ty)).clone()
        })
        .collect()
}
fn row(snapshot: &str, root: &str, child: &str, leaf: &str) -> Vec<Json> {
    vec![
        subject(snapshot, root),
        subject(snapshot, child),
        subject(snapshot, leaf),
    ]
}

// 元署名・固定selector・原始ownerだけから実prefix域を列挙する。
// 出力のrow/domain/owner Scalarは期待値を作る入力へ戻さない。
fn domains(result: &ObservedEvaluation, wire: &Json, family_root: &Json) {
    let checked = result.prepared().inputs();
    let request = &result.prepared().requests().requests()[0];
    let Signature::Law { params, body, .. } =
        &checked.law().declarations["Inspect.chain"].signature
    else {
        panic!("Law")
    };
    let mut prefixes = vec![Vec::<Json>::new()];
    let mut wanted = BTreeMap::new();
    for (parameter_index, p) in params.iter().enumerate() {
        let fixed = request
            .arguments
            .iter()
            .find(|a| a.name == format!("bind.{}", p.name))
            .map(|a| {
                let Selector::Subject {
                    snapshot,
                    subject: id,
                } = &a.value
                else {
                    panic!("元の固定subject selector")
                };
                subject(snapshot, id)
            });
        let mut next = vec![];
        for prefix in prefixes {
            let mut support = vec![];
            let mut values = match &p.ty {
                Type::Bool => vec![Json::Bool(false), Json::Bool(true)],
                Type::Ref(entity) | Type::Owned(entity, _) => {
                    let owner = match &p.ty {
                        Type::Owned(_, owner) => {
                            Some(&prefix[params.iter().position(|p| &p.name == owner).unwrap()])
                        }
                        _ => None,
                    };
                    let mut values = vec![];
                    for snapshot in &checked.archmap().snapshots {
                        for candidate in &snapshot.subjects {
                            if &candidate.ty != entity {
                                continue;
                            }
                            let value = subject(&snapshot.id, &candidate.id);
                            if fixed.as_ref().is_some_and(|fixed| fixed != &value) {
                                continue;
                            }
                            if let Some(owner) = owner {
                                if arr(owner)[0] != Json::str(&snapshot.id) {
                                    continue;
                                }
                                let field = candidate
                                    .fields
                                    .iter()
                                    .find(|f| f.name == format!("{entity}.owner"))
                                    .unwrap();
                                let Slot::Known {
                                    atom,
                                    value: actual_owner,
                                    ..
                                } = &field.slot
                                else {
                                    panic!("このauditは既知ownerだけ")
                                };
                                support.push(Json::obj([
                                    ("snapshot", Json::str(&snapshot.id)),
                                    ("subject", Json::str(&candidate.id)),
                                    ("field", Json::str(&field.name)),
                                    ("atom", Json::str(atom)),
                                ]));
                                if &actual_owner.canonical_json() != owner {
                                    continue;
                                }
                            }
                            values.push(value);
                        }
                    }
                    values.sort_by_key(Json::canonical);
                    values
                }
                ty => panic!("小fixtureの有限parameter型 {ty:?}"),
            };
            if let Some(fixed) = &fixed {
                values.retain(|v| v == fixed);
            }
            for value in &values {
                let mut row = prefix.clone();
                row.push(value.clone());
                next.push(row);
            }
            assert!(
                wanted
                    .insert(
                        (parameter_index, Json::Arr(prefix).canonical()),
                        (values, support)
                    )
                    .is_none()
            );
        }
        prefixes = next;
    }
    let ns = index(wire);
    let source_ref = f(val(family_root), "expression");
    let family_reached = reachable(&ns, family_root);
    let mut seen = BTreeSet::new();
    let mut actual_domain_refs = vec![];
    for domain in arr(f(wire, "nodes")).iter().filter(|n| {
        f(n, "type") == &Json::str("Domain")
            && family_reached.contains(text(f(n, "id")))
            && arr(f(n, "arguments")).first() == Some(source_ref)
    }) {
        let position = span(f(f(domain, "rule"), "location"));
        let Some(parameter_index) = params.iter().position(|p| p.span == position) else {
            continue;
        };
        let p = &params[parameter_index];
        actual_domain_refs.push(Json::obj([("node", f(domain, "id").clone())]));
        assert_eq!(f(val(domain), "type"), &p.ty.erase().wire());
        let elements = arr(f(val(domain), "elements"));
        let arguments = arr(f(domain, "arguments"));
        let prefix_len = 1 + parameter_index * 2;
        assert_eq!(arguments.len(), prefix_len + elements.len());
        let source = target(&ns, &arguments[0], &Json::str("Expression"));
        assert_eq!(
            span(f(val(source), "location")),
            checked.law().exprs[*body].span
        );
        let mut prefix = vec![];
        for (i, pair) in arguments[1..prefix_len].chunks_exact(2).enumerate() {
            let prior = target(&ns, &pair[0], &Json::str("Domain"));
            assert_eq!(span(f(f(prior, "rule"), "location")), params[i].span);
            assert!(arr(f(val(prior), "elements")).contains(&pair[1]));
            prefix.push(val(target(&ns, &pair[1], &params[i].ty.erase().wire())).clone());
        }
        assert_eq!(&arguments[prefix_len..], elements);
        let key = (parameter_index, Json::Arr(prefix).canonical());
        assert!(seen.insert(key.clone()), "同じbinder/prefixの実域は一つ");
        let (expected, support) = &wanted[&key];
        let actual: Vec<_> = elements
            .iter()
            .map(|r| val(target(&ns, r, &p.ty.erase().wire())).clone())
            .collect();
        assert_eq!(&actual, expected, "元owner/selectorに従う実域");
        for fact in support {
            assert!(
                arr(f(domain, "support")).contains(fact),
                "所属/非所属を判断した原ownerFact"
            );
        }
        for r in elements {
            let element = target(&ns, r, &p.ty.erase().wire());
            assert_eq!(arr(f(element, "arguments")), &arguments[..prefix_len]);
        }
    }
    assert_eq!(
        seen.len(),
        wanted.len(),
        "空fiberを含む各実prefix域を保持する"
    );
    let free_indices: Vec<_> = params
        .iter()
        .enumerate()
        .filter(|(_, p)| {
            !request
                .arguments
                .iter()
                .any(|a| a.name == format!("bind.{}", p.name))
        })
        .map(|(i, _)| i)
        .collect();
    let expected_rows: Vec<_> = prefixes
        .iter()
        .map(|row| {
            let values: Vec<_> = free_indices.iter().map(|i| row[*i].clone()).collect();
            if values.len() == 1 {
                values[0].clone()
            } else {
                Json::Arr(values)
            }
        })
        .collect();
    let total: Vec<_> = arr(f(wire, "nodes"))
        .iter()
        .filter(|n| {
            f(n, "type") == &Json::str("Domain")
                && family_reached.contains(text(f(n, "id")))
                && arr(f(n, "arguments")).first() == Some(source_ref)
                && span(f(f(n, "rule"), "location"))
                    == checked.law().declarations["Inspect.chain"].span
        })
        .collect();
    assert_eq!(total.len(), 1, "実row全域");
    let total = total[0];
    let elements = arr(f(val(total), "elements"));
    let rows: Vec<_> = elements
        .iter()
        .map(|r| val(target(&ns, r, f(val(total), "type"))).clone())
        .collect();
    assert_eq!(rows, expected_rows);
    let total_arguments = arr(f(total, "arguments"));
    assert_eq!(
        total_arguments.len(),
        1 + actual_domain_refs.len() + elements.len()
    );
    assert_eq!(
        &total_arguments[1..1 + actual_domain_refs.len()],
        actual_domain_refs.as_slice()
    );
    assert_eq!(&total_arguments[1 + actual_domain_refs.len()..], elements);
    for r in elements {
        let member = target(&ns, r, f(val(total), "type"));
        let args = arr(f(member, "arguments"));
        assert_eq!(args.len(), 1 + params.len() * 2);
        assert_eq!(&args[0], &total_arguments[0]);
        for (i, pair) in args[1..].chunks_exact(2).enumerate() {
            let domain = target(&ns, &pair[0], &Json::str("Domain"));
            assert_eq!(span(f(f(domain, "rule"), "location")), params[i].span);
            assert!(arr(f(val(domain), "elements")).contains(&pair[1]));
        }
    }
}

// Whole の直接辺にある実適用だけを調べ、補完例や別contextの同値nodeと混ぜない。
fn assert_family(
    result: &ObservedEvaluation,
    ask: &str,
    expected: &[Vec<Json>],
    decision: &str,
    mixed: bool,
) {
    assert_family_selected(result, ask, expected, decision, mixed, None, None);
}

#[allow(clippy::too_many_arguments)]
fn assert_family_selected(
    result: &ObservedEvaluation,
    ask: &str,
    expected: &[Vec<Json>],
    decision: &str,
    mixed: bool,
    selected: Option<(&str, &str)>,
    completion: Option<(&str, bool)>,
) {
    let checked = result.prepared().inputs();
    let wire = result.wire();
    assert_eq!(
        f(&wire, "status"),
        &Json::str(if decision == "undetermined" {
            "partial"
        } else {
            "complete"
        })
    );
    let answers = arr(f(&wire, "answers"));
    assert_eq!(answers.len(), 1);
    let answer = &answers[0];
    assert_eq!(
        f(answer, "status"),
        &Json::str(decision),
        "issues {:?}",
        f(&wire, "issues")
    );
    let request = &arr(f(&wire, "requests"))[0];
    assert_eq!(f(request, "text"), &Json::str(ask));
    let ns = index(&wire);
    let root = selected.map_or_else(
        || {
            target(
                &ns,
                f(f(answer, "outputs"), "evaluation"),
                &Json::str("Evaluation"),
            )
        },
        |(root, _)| ns[root],
    );
    assert_eq!(f(root, "type"), &Json::str("Evaluation"));
    domains(result, &wire, root);
    assert_eq!(f(val(root), "applicability"), &Json::str("applicable"));
    let claim = selected.map_or_else(
        || target(&ns, f(answer, "claim"), &Json::str("Proposition")),
        |(_, claim)| ns[claim],
    );
    assert_eq!(f(claim, "type"), &Json::str("Proposition"));
    assert_eq!(f(f(claim, "judgment"), "status"), &Json::str(decision));
    let whole = target(
        &ns,
        &arr(f(val(claim), "operands"))[0],
        &Json::str("LawInstance"),
    );
    assert_eq!(f(val(whole), "name"), &Json::str("Inspect.chain"));
    assert_eq!(f(val(whole), "role"), &Json::str("required"));
    let declaration = &checked.law().declarations["Inspect.chain"];
    let Signature::Law {
        params,
        guard: Some(guard),
        body,
        ..
    } = &declaration.signature
    else {
        panic!("明示guard付きLaw")
    };
    let resolved = &result.prepared().requests().requests()[0];
    let fixed: Vec<_> = params
        .iter()
        .filter_map(|p| {
            resolved
                .arguments
                .iter()
                .find(|a| a.name == format!("bind.{}", p.name))
                .map(|a| (p, a))
        })
        .collect();
    let bindings = arr(f(val(whole), "bindings"));
    assert_eq!(bindings.len(), fixed.len());
    for (binding, (p, argument)) in bindings.iter().zip(&fixed) {
        assert_eq!(f(binding, "name"), &Json::str(&p.name));
        let Selector::Subject {
            snapshot,
            subject: id,
        } = &argument.value
        else {
            panic!("元selector")
        };
        assert_eq!(
            val(target(&ns, f(binding, "value"), &p.ty.erase().wire())),
            &subject(snapshot, id)
        );
    }
    let source = target(&ns, f(val(whole), "body"), &Json::str("Expression"));
    let free_parameters: Vec<_> = params
        .iter()
        .filter(|p| !fixed.iter().any(|(f, _)| f.name == p.name))
        .map(|p| Json::obj([("name", Json::str(&p.name)), ("type", p.ty.erase().wire())]))
        .collect();
    assert_eq!(f(val(source), "parameters"), &Json::Arr(free_parameters));
    assert_eq!(f(val(source), "bindings"), f(val(whole), "bindings"));
    assert_eq!(span(f(val(whole), "occurrence")), declaration.span);
    assert_eq!(
        params[1].ty.wire(),
        Json::Arr(vec![
            Json::str("Owned"),
            Json::str("Dep.Child"),
            Json::str("a")
        ])
    );
    assert_eq!(
        params[2].ty.wire(),
        Json::Arr(vec![
            Json::str("Owned"),
            Json::str("Dep.Leaf"),
            Json::str("a")
        ])
    );
    let body_span = checked.law().exprs[*body].span;
    let guard_span = checked.law().exprs[*guard].span;
    for (name, wanted) in [("body", body_span), ("guard", guard_span)] {
        let expression = target(&ns, f(val(whole), name), &Json::str("Expression"));
        assert_eq!(span(f(val(expression), "location")), wanted);
    }
    assert_eq!(
        &checked.sources().law().bytes()[guard_span.0..guard_span.1],
        b"true"
    );
    let parts = arr(f(val(root), "parts"));
    assert_eq!(parts.len(), 1);
    assert_eq!(span(f(&parts[0], "location")), body_span);
    let rows = arr(f(&parts[0], "children"));
    assert_eq!(rows.len(), expected.len());
    let whole_refs = arr(f(whole, "arguments"));
    let mut actual = vec![];
    for r in rows {
        let evaluation = target(&ns, r, &Json::str("Evaluation"));
        let instance_ref = &arr(f(evaluation, "arguments"))[0];
        assert!(whole_refs.contains(instance_ref));
        let instance = target(&ns, instance_ref, &Json::str("LawInstance"));
        assert_eq!(f(val(instance), "bindings"), f(val(evaluation), "bindings"));
        let values = binding_values(&ns, f(val(instance), "bindings"), mixed);
        assert_eq!(f(val(instance), "role"), &Json::str("required"));
        assert_eq!(span(f(val(instance), "occurrence")), declaration.span);
        for (name, wanted) in [("body", body_span), ("guard", guard_span)] {
            let expression = target(&ns, f(val(instance), name), &Json::str("Expression"));
            assert_eq!(span(f(val(expression), "location")), wanted);
            assert!(arr(f(val(expression), "parameters")).is_empty());
            assert_eq!(f(val(expression), "bindings"), f(val(instance), "bindings"));
        }
        assert_eq!(
            f(val(evaluation), "applicability"),
            &Json::str("applicable")
        );
        let row_parts = arr(f(val(evaluation), "parts"));
        assert_eq!(row_parts.len(), 2);
        assert_eq!(span(f(&row_parts[0], "location")), guard_span);
        assert_eq!(span(f(&row_parts[1], "location")), body_span);
        for p in row_parts {
            assert_eq!(arr(f(p, "children")).len(), 1);
            target(&ns, &arr(f(p, "children"))[0], &Json::str("Evaluation"));
        }
        let body_evaluation = target(
            &ns,
            &arr(f(&row_parts[1], "children"))[0],
            &Json::str("Evaluation"),
        );
        let leaf = arr(&values[2]);
        let snapshot = checked
            .archmap()
            .snapshots
            .iter()
            .find(|s| s.id == text(&leaf[0]))
            .unwrap();
        let leaf = snapshot
            .subjects
            .iter()
            .find(|s| s.id == text(&leaf[1]))
            .unwrap();
        let slot = &leaf
            .fields
            .iter()
            .find(|f| f.name == "Dep.Leaf.ok")
            .unwrap()
            .slot;
        let expected_body = if mixed && values[3] == Json::Bool(true) {
            Some(Json::Bool(true))
        } else {
            match slot {
                Slot::Known { value, .. } => Some(value.canonical_json()),
                Slot::Missing => completion
                    .filter(|(id, _)| *id == leaf.id)
                    .map(|(_, value)| Json::Bool(value)),
            }
        };
        if let Some(expected) = expected_body {
            assert_eq!(
                val(target(
                    &ns,
                    f(val(body_evaluation), "value"),
                    &Json::str("Bool")
                )),
                &expected
            );
        } else {
            assert!(
                !obj(val(body_evaluation)).contains_key("value"),
                "欠測rowを通常Boolへ補わない"
            );
        }
        let row_reached = reachable(&ns, r);
        for (id, expr) in checked.law().exprs.iter().enumerate().filter(|(id, e)| {
            checked.law().expr_type(*id).is_some()
                && ((body_span.0 <= e.span.0 && e.span.1 <= body_span.1) || e.span == guard_span)
        }) {
            let source: Vec<_> = row_reached
                .iter()
                .map(|id| ns[id.as_str()])
                .filter(|n| {
                    f(n, "type") == &Json::str("Expression")
                        && f(val(n), "kind") == &Json::str("source")
                        && span(f(val(n), "location")) == expr.span
                        && f(val(n), "bindings") == f(val(instance), "bindings")
                })
                .collect();
            assert_eq!(source.len(), 1, "rowごとの元AST出現{id}を保持");
        }
        actual.push(values);
    }
    assert_eq!(
        actual, expected,
        "宣言順の依存row。Cartesianや同ID別snapshotとの混同を拒む"
    );
    if decision != "undetermined" {
        assert_eq!(
            val(target(&ns, f(val(root), "value"), &Json::str("Bool"))),
            &Json::Bool(decision == "established")
        );
    }
    let reached = reachable(&ns, claim);
    let exhaustion: Vec<_> = reached
        .iter()
        .map(|id| ns[id.as_str()])
        .filter(|n| {
            f(n, "type") == &Json::str("Evidence")
                && f(val(n), "kind") == &Json::str("finite_exhaustion")
        })
        .collect();
    if decision == "established" {
        assert_eq!(exhaustion.len(), 1);
        let data = f(val(exhaustion[0]), "data");
        assert_eq!(f(data, "checked"), &Json::Nat(expected.len() as u64));
        assert_eq!(arr(f(data, "instances")), rows);
        let domain = target(&ns, f(data, "domain"), &Json::str("Domain"));
        assert_eq!(arr(f(val(domain), "elements")).len(), expected.len());
    }
    if decision == "refuted" {
        assert!(
            reached
                .iter()
                .map(|id| ns[id.as_str()])
                .any(|n| f(n, "type") == &Json::str("Evidence")
                    && f(val(n), "kind") == &Json::str("counterexample"))
        );
    }
    for item in [answer, root, whole, claim] {
        let scope = f(item, "scope");
        assert_eq!(f(scope, "readings"), &Json::Arr(vec![Json::str("Inspect")]));
        assert!(arr(f(scope, "assumptions")).is_empty());
        let has_missing_body = checked
            .archmap()
            .snapshots
            .iter()
            .flat_map(|s| &s.subjects)
            .flat_map(|s| &s.fields)
            .any(|f| f.name == "Dep.Leaf.ok" && f.slot == Slot::Missing);
        assert_eq!(
            f(scope, "domain"),
            &Json::str(if has_missing_body {
                "all_completions"
            } else {
                "finite_model"
            })
        );
        let expected_modes = if checked.archmap().snapshots.len() == 2 {
            vec![Json::str("proposed"), Json::str("specification")]
        } else {
            vec![Json::str("specification")]
        };
        assert_eq!(f(scope, "modes"), &Json::Arr(expected_modes));
        let snapshots = arr(f(scope, "snapshots"));
        assert!(snapshots.contains(&Json::str("v")));
        if checked.archmap().snapshots.len() == 2 {
            assert!(snapshots.contains(&Json::str("w")));
        }
        let quantifiers = arr(f(scope, "quantifiers"));
        assert!(!quantifiers.is_empty());
        for q in quantifiers {
            assert_eq!(f(q, "kind"), &Json::str("forall"));
            let parameter = params
                .iter()
                .find(|p| p.name == text(f(q, "name")))
                .unwrap();
            assert_eq!(f(q, "type"), &parameter.ty.erase().wire());
            assert!(
                !fixed.iter().any(|(p, _)| p.name == parameter.name),
                "固定parameterへ全称を捏造しない"
            );
            if let Json::Arr(ty) = f(q, "type") {
                assert_ne!(ty.first(), Some(&Json::str("Owned")));
            }
            if let Some(domain) = obj(q).get("domain") {
                let d = target(&ns, domain, &Json::str("Domain"));
                assert_eq!(f(val(d), "type"), f(q, "type"));
                assert_eq!(span(f(f(d, "rule"), "location")), parameter.span);
            }
        }
    }
}

#[test]
fn dependent_free_parameters_follow_owner_and_two_binding_prefixes() {
    let ask = "all=check(Inspect.chain)";
    let result = run(
        fixture(CHAIN, [Some(true), Some(true)], false, false, false),
        ask,
    );
    assert_family(
        &result,
        ask,
        &[row("v", "A", "p", "l"), row("v", "B", "q", "m")],
        "established",
        false,
    );
}

#[test]
fn dependent_fixed_root_enumerates_only_its_children_and_leaves() {
    let ask = "all=check(Inspect.chain,a=@v/A)";
    let result = run(
        fixture(CHAIN, [Some(true), Some(true)], false, false, false),
        ask,
    );
    assert_family(
        &result,
        ask,
        &[row("v", "A", "p", "l")],
        "established",
        false,
    );
}

#[test]
fn dependent_fixed_child_filters_free_owner_without_fabricating_root_binding() {
    let ask = "all=check(Inspect.chain,b=@v/p)";
    let result = run(
        fixture(CHAIN, [Some(true), Some(true)], false, false, false),
        ask,
    );
    assert_family(
        &result,
        ask,
        &[row("v", "A", "p", "l")],
        "established",
        false,
    );
    let wire = result.wire();
    let request = &arr(f(&wire, "requests"))[0];
    assert_eq!(arr(f(request, "arguments")).len(), 1);
    assert_eq!(
        f(&arr(f(request, "arguments"))[0], "name"),
        &Json::str("bind.b")
    );
    let defaults = arr(f(request, "defaults"));
    let universal = defaults
        .iter()
        .find(|d| f(d, "rule") == &Json::str("universal_parameters"))
        .unwrap();
    assert_eq!(
        f(universal, "parameters"),
        &Json::Arr(vec![Json::str("a"), Json::str("c")])
    );
}

#[test]
fn dependent_ref_parameters_mix_with_independent_bool_parameter() {
    let ask = "all=check(Inspect.chain)";
    let result = run(
        fixture(MIXED, [Some(true), Some(true)], false, false, false),
        ask,
    );
    let mut expected = vec![];
    for base in [row("v", "A", "p", "l"), row("v", "B", "q", "m")] {
        for flag in [false, true] {
            let mut row = base.clone();
            row.push(Json::Bool(flag));
            expected.push(row);
        }
    }
    assert_family(&result, ask, &expected, "established", true);
}

#[test]
fn dependent_same_ids_in_two_snapshots_keep_snapshot_and_owner_identity() {
    let ask = "all=check(Inspect.chain)";
    let result = run(
        fixture(CHAIN, [Some(true), Some(true)], true, false, false),
        ask,
    );
    assert_family(
        &result,
        ask,
        &[
            row("v", "A", "p", "l"),
            row("v", "B", "q", "m"),
            row("w", "A", "q", "m"),
            row("w", "B", "p", "l"),
        ],
        "established",
        false,
    );
}

#[test]
fn dependent_fixed_child_in_second_snapshot_filters_same_id_owners() {
    let ask = "all=check(Inspect.chain,b=@w/p)";
    let result = run(
        fixture(CHAIN, [Some(true), Some(true)], true, false, false),
        ask,
    );
    assert_family(
        &result,
        ask,
        &[row("w", "B", "p", "l")],
        "established",
        false,
    );
}

#[test]
fn dependent_empty_fiber_has_true_forall_and_zero_checked_rows() {
    let ask = "all=check(Inspect.chain,a=@v/Z)";
    let result = run(
        fixture(CHAIN, [Some(true), Some(true)], false, false, false),
        ask,
    );
    assert_family(&result, ask, &[], "established", false);
}

fn missing_and_counterexample(flags: [Option<bool>; 2], missing_leaf: &str) {
    let ask = "all=check(Inspect.chain)";
    let result = run(fixture(CHAIN, flags, false, false, false), ask);
    let wire = result.wire();
    let answer = &arr(f(&wire, "answers"))[0];
    let ns = index(&wire);
    let aggregate = target(
        &ns,
        f(f(answer, "outputs"), "evaluation"),
        &Json::str("Evaluation"),
    );
    let seed_ref = f(val(aggregate), "expression");
    let seed = target(&ns, seed_ref, &Json::str("Expression"));
    assert_eq!(arr(f(aggregate, "arguments")).first(), Some(seed_ref));
    let direct: Vec<_> = arr(f(seed, "arguments"))
        .iter()
        .map(|r| ns[text(f(r, "node"))])
        .collect();
    let observed_claims: Vec<_> = direct
        .iter()
        .copied()
        .filter(|n| {
            f(n, "type") == &Json::str("Proposition")
                && f(val(n), "predicate") == &Json::str("law_holds")
        })
        .collect();
    assert_eq!(
        observed_claims.len(),
        1,
        "seedの元observed whole命題を直接選ぶ"
    );
    let observed_claim = observed_claims[0];
    let observed_args = arr(f(observed_claim, "arguments"));
    assert_eq!(observed_args.len(), 2);
    assert_eq!(
        &observed_args[0],
        &arr(f(val(observed_claim), "operands"))[0]
    );
    let observed = target(&ns, &observed_args[1], &Json::str("Evaluation"));
    assert!(
        direct.iter().any(|n| f(n, "id") == f(observed, "id")),
        "元whole評価もseedの直接root"
    );
    assert_eq!(
        arr(f(observed, "arguments")).first(),
        Some(&observed_args[0])
    );
    let expected_rows = [row("v", "A", "p", "l"), row("v", "B", "q", "m")];
    assert_family_selected(
        &result,
        ask,
        &expected_rows,
        "refuted",
        false,
        Some((text(f(observed, "id")), text(f(observed_claim, "id")))),
        None,
    );

    // 外側の全補完証拠と、各assignmentの独立した実Law族を分けて検査する。
    let aggregate_args = arr(f(aggregate, "arguments"));
    let completion_domain_ref = &aggregate_args[1];
    let completion_domain = target(&ns, completion_domain_ref, &Json::str("Domain"));
    assert_eq!(f(val(completion_domain), "type"), &Json::str("Bool"));
    let assignments = arr(f(val(completion_domain), "elements"));
    assert_eq!(assignments.len(), 2);
    let parts = arr(f(val(aggregate), "parts"));
    assert_eq!(parts.len(), 1);
    let cases = arr(f(&parts[0], "children"));
    assert_eq!(cases.len(), 2);
    let mut covered = BTreeSet::new();
    for (case_ref, assignment_ref) in cases.iter().zip(assignments) {
        assert!(aggregate_args.contains(case_ref));
        let case = target(&ns, case_ref, &Json::str("Evaluation"));
        let case_source = target(&ns, f(val(case), "expression"), &Json::str("Expression"));
        let arguments = arr(f(case_source, "arguments"));
        assert_eq!(arguments.len(), 4);
        assert_eq!(
            &arguments[..3],
            &[
                seed_ref.clone(),
                completion_domain_ref.clone(),
                assignment_ref.clone()
            ]
        );
        let assigned = target(&ns, &arguments[3], &Json::str("Bool"));
        let assignment = target(&ns, assignment_ref, &Json::str("Bool"));
        assert_eq!(val(assigned), val(assignment));
        let Json::Bool(value) = val(assignment) else {
            panic!("Bool補完assignment")
        };
        assert!(covered.insert(*value));
        let assigned_args = arr(f(assigned, "arguments"));
        assert_eq!(assigned_args.len(), 4);
        assert_eq!(&assigned_args[..3], &arguments[..3]);
        let original_slot_source = target(&ns, &assigned_args[3], &Json::str("Expression"));
        let position = span(f(val(original_slot_source), "location"));
        assert_eq!(
            &result.prepared().inputs().sources().law().bytes()[position.0..position.1],
            b"c.ok"
        );
        let case_claims: Vec<_> = aggregate_args
            .iter()
            .map(|r| ns[text(f(r, "node"))])
            .filter(|n| {
                f(n, "type") == &Json::str("Proposition")
                    && arr(f(n, "arguments")).get(1) == Some(case_ref)
            })
            .collect();
        assert_eq!(case_claims.len(), 1);
        let case_claim = case_claims[0];
        assert_family_selected(
            &result,
            ask,
            &expected_rows,
            "refuted",
            false,
            Some((text(f(case, "id")), text(f(case_claim, "id")))),
            Some((missing_leaf, *value)),
        );
    }
    assert_eq!(covered, BTreeSet::from([false, true]));
    let proofs: Vec<_> = arr(f(answer, "evidence"))
        .iter()
        .map(|r| target(&ns, r, &Json::str("Evidence")))
        .collect();
    assert_eq!(proofs.len(), 1);
    assert_eq!(f(val(proofs[0]), "kind"), &Json::str("finite_exhaustion"));
    let data = f(val(proofs[0]), "data");
    assert_eq!(f(data, "domain"), completion_domain_ref);
    assert_eq!(f(data, "checked"), &Json::Nat(2));
    assert_eq!(arr(f(data, "instances")), cases);
    assert_eq!(
        val(target(&ns, f(val(aggregate), "value"), &Json::str("Bool"))),
        &Json::Bool(false)
    );
    assert_eq!(f(answer, "status"), &Json::str("refuted"));
    let reason = arr(f(answer, "reasons"))
        .iter()
        .find(|r| f(r, "code") == &Json::str("missing_observation"))
        .unwrap();
    assert_eq!(
        f(reason, "missing"),
        &Json::Arr(vec![Json::obj([
            ("snapshot", Json::str("v")),
            ("subject", Json::str(missing_leaf)),
            ("field", Json::str("Dep.Leaf.ok"))
        ])])
    );
    assert!(!arr(f(reason, "dependencies")).is_empty());
    assert!(
        result.prepared().inputs().archmap().snapshots[0]
            .subjects
            .iter()
            .any(|s| s.id == missing_leaf)
    );
}

#[test]
fn dependent_missing_body_row_before_known_counterexample_stays_in_family() {
    missing_and_counterexample([None, Some(false)], "l");
}

#[test]
fn dependent_missing_body_row_after_known_counterexample_stays_in_family() {
    missing_and_counterexample([Some(false), None], "m");
}

#[test]
fn dependent_empty_fiber_still_rejects_statically_invalid_body_at_original_location() {
    let inputs = fixture(
        &CHAIN.replace("c.ok", "c.absent"),
        [Some(true), Some(true)],
        false,
        false,
        false,
    );
    let failure = check_inputs(inputs.clone(), &mut quiet()).unwrap_err();
    assert_eq!(failure.status().wire(), "invalid");
    assert_eq!(failure.sources(), &inputs);
    let wire = failure.wire();
    assert!(arr(f(&wire, "answers")).is_empty());
    assert!(arr(f(&wire, "nodes")).is_empty());
    assert!(arr(f(&wire, "issues")).iter().any(|i| {
        let location = f(i, "location");
        obj(location).get("input") == Some(&Json::str("law")) && {
            let position = span(location);
            inputs.law().bytes()[position.0..position.1]
                .windows(b"absent".len())
                .any(|w| w == b"absent")
        }
    }));
}

#[test]
fn dependent_unknown_owner_is_undetermined_and_keeps_algorithm_and_missing_reasons() {
    let ask = "all=check(Inspect.chain)";
    let result = run(
        fixture(CHAIN, [Some(true), Some(true)], false, true, false),
        ask,
    );
    let wire = result.wire();
    assert_eq!(f(&wire, "status"), &Json::str("partial"));
    let answer = &arr(f(&wire, "answers"))[0];
    assert_eq!(f(answer, "status"), &Json::str("undetermined"));
    assert_eq!(
        f(f(answer, "scope"), "domain"),
        &Json::str("all_completions")
    );
    assert!(obj(f(answer, "outputs")).is_empty());
    assert!(!obj(answer).contains_key("claim"));
    assert!(arr(f(answer, "evidence")).is_empty());
    let reasons = arr(f(answer, "reasons"));
    let unsupported = reasons
        .iter()
        .find(|r| f(r, "code") == &Json::str("unsupported_algorithm"))
        .unwrap();
    assert_eq!(
        f(f(unsupported, "details"), "method"),
        &Json::str("unresolved_dependent_owner")
    );
    assert_eq!(
        f(f(unsupported, "details"), "operand_types"),
        &Json::Arr(vec![ref_type("Child")])
    );
    let missing = reasons
        .iter()
        .find(|r| f(r, "code") == &Json::str("missing_observation"))
        .unwrap();
    assert_eq!(
        f(missing, "missing"),
        &Json::Arr(vec![Json::obj([
            ("snapshot", Json::str("v")),
            ("subject", Json::str("p")),
            ("field", Json::str("Dep.Child.owner"))
        ])])
    );
    assert!(!arr(f(missing, "dependencies")).is_empty());
    let checked = result.prepared().inputs();
    let Signature::Law { params, body, .. } =
        &checked.law().declarations["Inspect.chain"].signature
    else {
        panic!("Law")
    };
    let ns = index(&wire);
    for reason in [missing, unsupported] {
        assert_eq!(span(f(reason, "location")), params[1].span);
        let dependencies = arr(f(reason, "dependencies"));
        let source = target(&ns, &dependencies[0], &Json::str("Expression"));
        assert_eq!(
            span(f(val(source), "location")),
            checked.law().exprs[*body].span
        );
    }
    assert!(
        !arr(f(&wire, "nodes"))
            .iter()
            .any(|n| f(n, "type") == &Json::str("LawInstance")),
        "未知所属を除いてwhole Lawを確定しない"
    );
    assert!(
        result.prepared().inputs().archmap().snapshots[0]
            .subjects
            .iter()
            .any(|s| s.id == "p")
    );
}

#[test]
fn dependent_provenance_relocation_keeps_rows_and_traces_current_owner_sources() {
    let ask = "all=check(Inspect.chain)";
    let original = run(
        fixture(CHAIN, [Some(true), Some(true)], false, false, false),
        ask,
    );
    let relocated = run(
        fixture(CHAIN, [Some(true), Some(true)], false, false, true),
        ask,
    );
    let rows = [row("v", "A", "p", "l"), row("v", "B", "q", "m")];
    for result in [&original, &relocated] {
        assert_family(result, ask, &rows, "established", false);
    }
    let a = original.prepared().inputs();
    let b = relocated.prepared().inputs();
    assert_eq!(a.definitions(), b.definitions());
    assert_eq!(a.law().model_digest, b.law().model_digest);
    assert_ne!(a.archmap().model_digest, b.archmap().model_digest);
    assert_eq!(
        a.archmap().snapshots,
        b.archmap().snapshots,
        "原始参照/値/owner/subject/Atomを固定する"
    );
}

#[test]
fn dependent_numeric_parameters_keep_each_actual_fiber_and_full_z_q_domain() {
    for ty in ["Z", "Q"] {
        for parameters in [
            format!("z:{ty},a:Root,b:Child[a],c:Leaf[a]"),
            format!("a:Root,z:{ty},b:Child[a],c:Leaf[a]"),
            format!("a:Root,b:Child[a],z:{ty},c:Leaf[a]"),
            format!("a:Root,b:Child[a],c:Leaf[a],z:{ty}"),
        ] {
            let script = format!("law required chain({parameters}):z+1=z+1;");
            let result = run(
                fixture(&script, [Some(true); 2], false, false, false),
                "all=check(Inspect.chain)",
            );
            assert_eq!(
                result.status(),
                "complete",
                "{:?}",
                f(&result.wire(), "issues")
            );
            let wire = result.wire();
            let ns = index(&wire);
            let answer = &arr(f(&wire, "answers"))[0];
            assert_eq!(f(answer, "status"), &Json::str("established"));
            let aggregate = target(
                &ns,
                f(f(answer, "outputs"), "evaluation"),
                &Json::str("Evaluation"),
            );
            let arguments = arr(f(aggregate, "arguments"));
            let domain = target(&ns, &arguments[1], &Json::str("Domain"));
            assert_eq!(arr(f(val(domain), "elements")).len(), 2);
            assert_eq!(arguments.len(), 4);
            let Signature::Law { params, .. } =
                &result.prepared().inputs().law().declarations["Inspect.chain"].signature
            else {
                panic!()
            };
            let ordered: Vec<_> = arr(f(f(answer, "scope"), "quantifiers"))
                .iter()
                .map(|q| {
                    params
                        .iter()
                        .position(|p| p.name == text(f(q, "name")))
                        .unwrap()
                })
                .collect();
            assert!(ordered.windows(2).all(|w| w[0] <= w[1]));
            assert_eq!(
                ordered.iter().copied().collect::<BTreeSet<_>>(),
                (0..4).collect()
            );
            for (position, row_ref) in arguments[2..].iter().enumerate() {
                let evaluation = target(&ns, row_ref, &Json::str("Evaluation"));
                let bindings = f(val(evaluation), "bindings");
                assert_eq!(
                    binding_values(&ns, bindings, false),
                    if position == 0 {
                        row("v", "A", "p", "l")
                    } else {
                        row("v", "B", "q", "m")
                    }
                );
                assert!(
                    !arr(bindings)
                        .iter()
                        .any(|b| f(b, "name") == &Json::str("z"))
                );
                let row_args = arr(f(evaluation, "arguments"));
                let numeric_domain = target(&ns, &row_args[1], &Json::str("Domain"));
                assert_eq!(f(val(numeric_domain), "kind"), &Json::str("type"));
                assert_eq!(f(val(numeric_domain), "type"), &Json::str(ty));
                assert!(!obj(val(numeric_domain)).contains_key("elements"));
                let value = target(&ns, f(val(evaluation), "value"), &Json::str("Bool"));
                assert_eq!(val(value), &Json::Bool(true));
            }
        }
    }
}

fn numeric_batch(inputs: InputSources, asks: &[&str]) -> ObservedEvaluation {
    let checked = check_inputs(inputs.clone(), &mut quiet())
        .unwrap_or_else(|e| panic!("input issues {:?}", e.issues()));
    let result = evaluate_observed_bytes(inputs, asks, &mut quiet()).unwrap();
    unchanged(&checked, result.prepared().inputs());
    audit(&result.wire(), result.prepared().inputs());
    assert_ne!(
        result.status(),
        "error",
        "{:?}",
        f(&result.wire(), "issues")
    );
    result
}
fn numeric_rows(result: &ObservedEvaluation, request_index: usize, expected: usize, status: &str) {
    let wire = result.wire();
    let ns = index(&wire);
    let answer = &arr(f(&wire, "answers"))[request_index];
    assert_eq!(f(answer, "status"), &Json::str(status));
    let evaluation = target(
        &ns,
        f(f(answer, "outputs"), "evaluation"),
        &Json::str("Evaluation"),
    );
    let args = arr(f(evaluation, "arguments"));
    let domain = target(&ns, &args[1], &Json::str("Domain"));
    assert_eq!(arr(f(val(domain), "elements")).len(), expected);
    assert_eq!(args.len(), 2 + expected);
}

#[test]
fn dependent_numeric_empty_fixed_and_compound_answer_fibers_keep_original_bindings() {
    let script = r#"
        view pick(b:Child):Option<Child> = some(b);
        view number():Z=3;
        view fraction():Q=rat(1,2);
        law required chain(z:Z,a:Root,b:Child[a],q:Q,c:Leaf[a]):z+1=z+1 and q+rat(1,2)+rat(1,2)=q+1;
        law required wrapped(z:Z,a:Root,b:Option<Child[a]>,q:Q,c:Leaf[a]):z+1=z+1 and q+1=q+1;
    "#;
    let result = numeric_batch(
        fixture(script, [Some(true); 2], false, false, false),
        &[
            "free=check(Inspect.chain)",
            "empty=check(Inspect.chain,a=@v/Z)",
            "fixed=check(Inspect.chain,b=@v/p)",
            "take=check(Inspect.wrapped,b=$pick.value)",
            "pick=evaluate(Inspect.pick,b=@v/p)",
            "wrapped=check(Inspect.wrapped)",
            "fixedz=check(Inspect.chain,z=$number.value)",
            "number=evaluate(Inspect.number)",
            "fixedboth=check(Inspect.chain,z=$number.value,q=$fraction.value)",
            "fraction=evaluate(Inspect.fraction)",
        ],
    );
    assert_eq!(result.status(), "complete");
    numeric_rows(&result, 0, 2, "established");
    numeric_rows(&result, 1, 0, "established");
    numeric_rows(&result, 2, 1, "established");
    numeric_rows(&result, 3, 1, "established");
    numeric_rows(&result, 5, 4, "established");
    numeric_rows(&result, 6, 2, "established");
    numeric_rows(&result, 8, 2, "established");
    let wire = result.wire();
    let ns = index(&wire);
    let empty = &arr(f(&wire, "answers"))[1];
    let proof = arr(f(empty, "evidence"))
        .iter()
        .map(|r| target(&ns, r, &Json::str("Evidence")))
        .find(|n| obj(val(n)).get("kind") == Some(&Json::str("finite_exhaustion")))
        .unwrap();
    assert_eq!(f(f(val(proof), "data"), "checked"), &Json::Nat(0));
    let take = &arr(f(&wire, "answers"))[3];
    let pick = &arr(f(&wire, "answers"))[4];
    let reach = reachable(&ns, take);
    assert!(reach.contains(text(f(f(f(pick, "outputs"), "value"), "node"))));
}

#[test]
fn dependent_numeric_known_counterexample_survives_missing_other_row_in_both_orders() {
    for ty in ["Z", "Q"] {
        for flags in [[None, Some(false)], [Some(false), None]] {
            let script = format!(
                "law required chain(a:Root,z:{ty},b:Child[a],c:Leaf[a]):if c.ok then z+1=z+1 else z+1=z+2;"
            );
            let result = numeric_batch(
                fixture(&script, flags, false, false, false),
                &["all=check(Inspect.chain)"],
            );
            let wire = result.wire();
            let ns = index(&wire);
            let answer = &arr(f(&wire, "answers"))[0];
            assert_eq!(f(answer, "status"), &Json::str("refuted"));
            let row_type = Type::Tuple(vec![
                Type::Ref("Dep.Root".into()),
                Type::Ref("Dep.Child".into()),
                Type::Ref("Dep.Leaf".into()),
            ])
            .wire();
            let actual_domains: Vec<_> = arr(f(&wire, "nodes"))
                .iter()
                .filter(|n| {
                    f(n, "type") == &Json::str("Domain")
                        && obj(val(n)).get("type") == Some(&row_type)
                })
                .collect();
            assert!(!actual_domains.is_empty());
            for d in actual_domains {
                assert_eq!(arr(f(val(d), "elements")).len(), 2);
            }
            assert!(
                arr(f(&wire, "nodes"))
                    .iter()
                    .any(|n| f(n, "type") == &Json::str("Domain")
                        && obj(val(n)).get("kind") == Some(&Json::str("type"))
                        && f(val(n), "type") == &Json::str(ty))
            );
            assert!(!arr(f(answer, "reasons")).is_empty());
            let kept = reachable(&ns, answer);
            let examples: Vec<_> = kept
                .iter()
                .map(|id| ns[id.as_str()])
                .filter(|n| {
                    f(n, "type") == &Json::str("Evidence")
                        && f(val(n), "kind") == &Json::str("counterexample")
                })
                .collect();
            assert!(!examples.is_empty());
            let number = |n: &str| {
                if ty == "Z" {
                    Json::str(n)
                } else {
                    Json::Arr(vec![Json::str(n), Json::str("1")])
                }
            };
            let numeric_examples: Vec<_> = examples
                .iter()
                .filter(|n| {
                    arr(f(f(val(n), "data"), "bindings"))
                        .iter()
                        .any(|b| f(b, "name") == &Json::str("z"))
                })
                .collect();
            assert!(!numeric_examples.is_empty());
            for example in numeric_examples {
                let data = f(val(example), "data");
                let binding = arr(f(data, "bindings"))
                    .iter()
                    .find(|b| f(b, "name") == &Json::str("z"))
                    .unwrap();
                assert_eq!(
                    val(target(&ns, f(binding, "value"), &Json::str(ty))),
                    &number("0")
                );
                let left = target(&ns, f(data, "left"), &Json::str("Evaluation"));
                let right = target(&ns, f(data, "right"), &Json::str("Evaluation"));
                assert_eq!(
                    val(target(&ns, f(val(left), "value"), &Json::str(ty))),
                    &number("1")
                );
                assert_eq!(
                    val(target(&ns, f(val(right), "value"), &Json::str(ty))),
                    &number("2")
                );
            }
            let reason = arr(f(answer, "reasons"))
                .iter()
                .find(|r| f(r, "code") == &Json::str("missing_observation"))
                .unwrap();
            assert_eq!(
                f(reason, "missing"),
                &Json::Arr(vec![Json::obj([
                    ("snapshot", Json::str("v")),
                    (
                        "subject",
                        Json::str(if flags[0].is_none() { "l" } else { "m" })
                    ),
                    ("field", Json::str("Dep.Leaf.ok"))
                ])])
            );
        }
    }
}

#[test]
fn dependent_numeric_unknown_owner_nonlinear_and_current_provenance_keep_their_boundaries() {
    let script = "law required chain(a:Root,z:Z,b:Child[a],q:Q,c:Leaf[a]):z+1=z+1 and q+1=q+1;";
    let unknown = numeric_batch(
        fixture(script, [Some(true); 2], false, true, false),
        &["all=check(Inspect.chain)"],
    );
    let wire = unknown.wire();
    let answer = &arr(f(&wire, "answers"))[0];
    assert_eq!(f(answer, "status"), &Json::str("undetermined"));
    assert!(obj(f(answer, "outputs")).is_empty());
    assert!(
        arr(f(answer, "reasons"))
            .iter()
            .any(|r| f(r, "code") == &Json::str("missing_observation"))
    );
    assert!(
        arr(f(answer, "reasons"))
            .iter()
            .any(|r| f(r, "code") == &Json::str("unsupported_algorithm"))
    );
    let nonlinear = "law required chain(a:Root,z:Z,b:Child[a],c:Leaf[a]):z*z=0;";
    let nonlinear = numeric_batch(
        fixture(nonlinear, [Some(true); 2], false, false, false),
        &["all=check(Inspect.chain)"],
    );
    numeric_rows(&nonlinear, 0, 2, "undetermined");
    assert!(
        arr(f(&arr(f(&nonlinear.wire(), "answers"))[0], "reasons"))
            .iter()
            .any(|r| f(r, "code") == &Json::str("unsupported_algorithm"))
    );
    let a = numeric_batch(
        fixture(script, [Some(true); 2], true, false, false),
        &["all=check(Inspect.chain)"],
    );
    let b = numeric_batch(
        fixture(script, [Some(true); 2], true, false, true),
        &["all=check(Inspect.chain)"],
    );
    for r in [&a, &b] {
        numeric_rows(r, 0, 4, "established");
    }
    assert_eq!(
        a.prepared().inputs().definitions(),
        b.prepared().inputs().definitions()
    );
    assert_eq!(
        a.prepared().inputs().archmap().snapshots,
        b.prepared().inputs().archmap().snapshots
    );
    assert_ne!(
        a.prepared().inputs().archmap().sources,
        b.prepared().inputs().archmap().sources
    );
    let wire = b.wire();
    let subject_tuples: Vec<_> = arr(f(&wire, "nodes"))
        .iter()
        .filter(|n| {
            f(n, "type")
                == &Type::Tuple(vec![
                    Type::Ref("Dep.Root".into()),
                    Type::Ref("Dep.Child".into()),
                    Type::Ref("Dep.Leaf".into()),
                ])
                .wire()
        })
        .map(|n| val(n).clone())
        .collect();
    assert!(
        subject_tuples
            .iter()
            .any(|t| t == &Json::Arr(row("w", "A", "q", "m")))
    )
}
