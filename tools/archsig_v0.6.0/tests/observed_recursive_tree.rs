//! 三入力から既知有限木の構造再帰と元由来までを接続する。
#[path = "common/recursive_tree.rs"]
mod tree;
use archsig::{
    canonical::Json,
    definition::check_definitions,
    observed::{
        control::{Control, Limits, Usage},
        evaluate_observed_bytes,
        input::{InputSources, check_inputs},
    },
};
use std::collections::{BTreeMap, BTreeSet};

fn quiet() -> Control {
    Control::new(Limits::default(), |_| Usage::default())
}
fn sources(missing: bool, extra: &str, revision: &str) -> InputSources {
    let checked = check_definitions(&[("definition0", tree::DEFINITIONS.as_bytes())]).unwrap();
    let digest = &checked.vocabularies["Trees"].digest;
    InputSources::from_bytes(
        vec![tree::DEFINITIONS.as_bytes().to_vec()],
        tree::law(digest, extra).into_bytes(),
        tree::archmap(digest, missing, revision).into_bytes(),
    )
}
fn object(j: &Json) -> &BTreeMap<String, Json> {
    let Json::Obj(x) = j else {
        panic!("object: {j:?}")
    };
    x
}
fn array(j: &Json) -> &[Json] {
    let Json::Arr(x) = j else {
        panic!("array: {j:?}")
    };
    x
}
fn text(j: &Json) -> &str {
    let Json::Str(x) = j else {
        panic!("string: {j:?}")
    };
    x
}
fn get<'a>(j: &'a Json, name: &str) -> &'a Json {
    &object(j)[name]
}
fn answer<'a>(wire: &'a Json, id: &str) -> &'a Json {
    array(get(wire, "answers"))
        .iter()
        .find(|a| get(a, "id") == &Json::str(id))
        .unwrap()
}
fn value<'a>(wire: &'a Json, id: &str, ty: Json) -> &'a Json {
    let a = answer(wire, id);
    assert_eq!(get(a, "status"), &Json::str("established"), "{a:?}");
    let r = get(get(get(a, "outputs"), "value"), "node");
    let node = array(get(wire, "nodes"))
        .iter()
        .find(|n| get(n, "id") == r)
        .unwrap();
    assert_eq!(get(node, "type"), &ty);
    assert_eq!(get(node, "state"), &Json::str("value"));
    get(node, "value")
}

fn refs(j: &Json, result: &mut Vec<String>) {
    match j {
        Json::Obj(fields) if fields.len() == 1 && fields.contains_key("node") => {
            result.push(text(&fields["node"]).into())
        }
        Json::Obj(fields) => {
            for j in fields.values() {
                refs(j, result);
            }
        }
        Json::Arr(items) => {
            for j in items {
                refs(j, result);
            }
        }
        _ => {}
    }
}
fn audit(result: &archsig::observed::ObservedEvaluation) {
    let wire = result.wire();
    let nodes: BTreeMap<_, _> = array(get(&wire, "nodes"))
        .iter()
        .map(|n| (text(get(n, "id")), n))
        .collect();
    let mut seen = BTreeSet::new();
    for n in array(get(&wire, "nodes")) {
        let mut rs = vec![];
        refs(n, &mut rs);
        assert!(rs.iter().all(|r| seen.contains(r.as_str())), "{n:?}");
        assert!(seen.insert(text(get(n, "id"))));
        if get(n, "type") != &Json::str("Proposition") {
            assert!(!object(n).contains_key("judgment"));
        }
        if let Some(v) = object(n).get("value") {
            let mut rs = vec![];
            refs(v, &mut rs);
            for r in rs {
                assert_eq!(get(nodes[r.as_str()], "state"), &Json::str("value"));
                assert!(!object(nodes[r.as_str()]).contains_key("partial"));
            }
        }
        for fact in array(get(n, "support")) {
            assert_eq!(get(fact, "snapshot"), &Json::str("v"));
            assert_eq!(get(fact, "subject"), &Json::str("sample"));
            let map = result.prepared().inputs().archmap();
            let subject = &map.snapshots[0].subjects[0];
            let origin = if let Some(field) = object(fact).get("field") {
                let slot = &subject
                    .fields
                    .iter()
                    .find(|f| f.name == text(field))
                    .unwrap()
                    .slot;
                let archsig::archmap::Slot::Known {
                    atom,
                    origin,
                    pointer,
                    ..
                } = slot
                else {
                    panic!("支持は元の既知事実")
                };
                assert_eq!(get(fact, "atom"), &Json::str(atom));
                assert!(pointer.starts_with("/snapshots/0/atoms/"));
                origin
            } else {
                &subject.origin
            };
            let origin = map.origins.iter().find(|o| &o.id == origin).unwrap();
            assert_eq!(origin.mode, archsig::archmap::Mode::Specification);
            for location in &origin.locations {
                let source = map
                    .sources
                    .iter()
                    .find(|s| s.id == location.source)
                    .unwrap();
                assert_eq!(source.uri, "urn:fixture:recursive-tree");
                assert!(location.span.is_some());
            }
        }
    }
    for a in array(get(&wire, "answers")) {
        let mut rs = vec![];
        refs(a, &mut rs);
        assert!(rs.iter().all(|r| nodes.contains_key(r.as_str())));
    }
}
fn data(tag: &str, args: Vec<Json>) -> Json {
    Json::obj([("tag", Json::str(tag)), ("args", Json::Arr(args))])
}
fn expected_tree() -> Json {
    data(
        "Branch",
        vec![
            data("Leaf", vec![Json::str("2")]),
            data(
                "Branch",
                vec![data("Leaf", vec![Json::str("2")]), data("Empty", vec![])],
            ),
        ],
    )
}
fn tree_type() -> Json {
    Json::Arr(vec![Json::str("Data"), Json::str("Trees.Tree")])
}

#[test]
fn recursive_tree_known_branch_calls_compute_from_original_bytes() {
    let inputs = sources(false, "", "r1");
    let checked = check_inputs(inputs.clone(), &mut quiet()).unwrap();
    let before = checked.metadata_wire();
    let result = evaluate_observed_bytes(
        inputs,
        &["a=evaluate(Trees.read,s=@v/sample)"],
        &mut quiet(),
    )
    .unwrap();
    assert_eq!(result.prepared().inputs().metadata_wire(), before);
    let after = result.prepared().inputs();
    assert_eq!(
        format!("{:?}", checked.definitions()),
        format!("{:?}", after.definitions())
    );
    assert_eq!(format!("{:?}", checked.law()), format!("{:?}", after.law()));
    assert_eq!(
        format!("{:?}", checked.archmap()),
        format!("{:?}", after.archmap())
    );
    assert_eq!(
        format!("{:?}", checked.sources()),
        format!("{:?}", after.sources())
    );
    let wire = result.wire();
    audit(&result);
    assert_eq!(get(&wire, "status"), &Json::str("complete"), "{wire:?}");
    assert_eq!(value(&wire, "a", Json::str("Z")), &Json::str("4"));
    let body = match &result.prepared().inputs().law().declarations["Trees.total"].signature {
        archsig::law::model::Signature::View { body, .. } => *body,
        _ => unreachable!(),
    };
    let span = result.prepared().inputs().law().exprs[body].span;
    let ns: BTreeMap<_, _> = array(get(&wire, "nodes"))
        .iter()
        .map(|n| (text(get(n, "id")), n))
        .collect();
    let calls: Vec<_> = ns
        .values()
        .filter(|n| {
            get(n, "type") == &Json::str("Evaluation")
                && object(n).get("value").is_some_and(|v| {
                    object(v).get("expression").is_some_and(|r| {
                        let e = ns[text(get(r, "node"))];
                        let loc = get(get(e, "value"), "location");
                        get(loc, "span")
                            == &Json::Arr(vec![Json::Nat(span.0 as u64), Json::Nat(span.1 as u64)])
                    })
                })
        })
        .collect();
    assert_eq!(calls.len(), 5, "各有限subtreeの実bodyを別々に保持する");
    let leaves: Vec<_> = calls
        .iter()
        .filter(|n| {
            let bs = array(get(get(n, "value"), "bindings"));
            let v = ns[text(get(get(&bs[0], "value"), "node"))];
            get(v, "value") == &data("Leaf", vec![Json::str("2")])
        })
        .collect();
    assert_eq!(leaves.len(), 2);
    assert_ne!(get(leaves[0], "id"), get(leaves[1], "id"));
}

#[test]
fn recursive_tree_values_preserve_constructors_wrappers_and_structural_equality() {
    let result = evaluate_observed_bytes(
        sources(false, "", "r1"),
        &[
            "raw=evaluate(Trees.raw,s=@v/sample)",
            "copy=evaluate(Trees.copied,s=@v/sample)",
            "wrapped=evaluate(Trees.wrapped,s=@v/sample)",
            "same=evaluate(Trees.same,s=@v/sample)",
        ],
        &mut quiet(),
    )
    .unwrap();
    audit(&result);
    let wire = result.wire();
    assert_eq!(get(&wire, "status"), &Json::str("complete"));
    assert_eq!(value(&wire, "raw", tree_type()), &expected_tree());
    assert_eq!(value(&wire, "copy", tree_type()), &expected_tree());
    assert_eq!(value(&wire, "same", Json::str("Bool")), &Json::Bool(true));
    assert_eq!(
        value(&wire, "wrapped", tree_type()),
        &data(
            "Packed",
            vec![Json::Arr(vec![
                expected_tree(),
                Json::obj([("some", expected_tree())]),
                Json::Arr(vec![data("Empty", vec![]), expected_tree()])
            ])]
        )
    );
}

#[test]
fn recursive_tree_let_nested_patterns_and_finite_containers_use_actual_values() {
    let extra = r#"
      view nested(s:Sample):Z=let t=copy(s.tree) in match t {Branch(Leaf(n),_)=>n;_=>0;};
      view bag(s:Sample):Z=count(set<Tree>{s.tree,copy(s.tree)});
      view literals(s:Sample):Z=total(Empty)+total(Leaf(7));
    "#;
    let result = evaluate_observed_bytes(
        sources(false, extra, "r1"),
        &[
            "n=evaluate(Trees.nested,s=@v/sample)",
            "b=evaluate(Trees.bag,s=@v/sample)",
            "l=evaluate(Trees.literals,s=@v/sample)",
        ],
        &mut quiet(),
    )
    .unwrap();
    audit(&result);
    let wire = result.wire();
    assert_eq!(get(&wire, "status"), &Json::str("complete"));
    for (id, n) in [("n", "2"), ("b", "1"), ("l", "7")] {
        assert_eq!(value(&wire, id, Json::str("Z")), &Json::str(n));
    }
}

#[test]
fn recursive_tree_missing_preserves_original_slot_without_inventing_a_tree() {
    let result = evaluate_observed_bytes(
        sources(true, "", "r1"),
        &[
            "a=evaluate(Trees.read,s=@v/sample)",
            "c=evaluate(Trees.ignores,s=@v/sample)",
        ],
        &mut quiet(),
    )
    .unwrap();
    audit(&result);
    let wire = result.wire();
    assert_eq!(get(&wire, "status"), &Json::str("partial"));
    let a = answer(&wire, "a");
    assert_eq!(get(a, "status"), &Json::str("undetermined"));
    assert!(!object(get(a, "outputs")).contains_key("value"));
    assert_eq!(
        get(get(a, "scope"), "domain"),
        &Json::str("all_completions")
    );
    let missing: Vec<_> = array(get(a, "reasons"))
        .iter()
        .filter(|r| get(r, "code") == &Json::str("missing_observation"))
        .collect();
    assert!(!missing.is_empty());
    for r in missing {
        assert!(!array(get(r, "dependencies")).is_empty());
        for m in array(get(r, "missing")) {
            assert_eq!(get(m, "snapshot"), &Json::str("v"));
            assert_eq!(get(m, "subject"), &Json::str("sample"));
            assert_eq!(get(m, "field"), &Json::str("Trees.Sample.tree"));
        }
    }
    assert_eq!(value(&wire, "c", Json::str("Z")), &Json::str("9"));
    assert!(
        !array(get(&wire, "nodes"))
            .iter()
            .any(|n| get(n, "type") == &tree_type() && object(n).contains_key("value"))
    );
}

#[test]
fn recursive_tree_provenance_pair_and_law_judgments_keep_current_sources() {
    let asks = [
        "a=evaluate(Trees.read,s=@v/sample)",
        "ok=check(Trees.four,s=@v/sample)",
    ];
    let first = evaluate_observed_bytes(sources(false, "", "r1"), &asks, &mut quiet()).unwrap();
    let second = evaluate_observed_bytes(sources(false, "", "r2"), &asks, &mut quiet()).unwrap();
    audit(&first);
    audit(&second);
    let (a, b) = (first.wire(), second.wire());
    assert_eq!(get(&a, "answers"), get(&b, "answers"));
    assert_eq!(get(answer(&a, "ok"), "status"), &Json::str("established"));
    assert_ne!(
        first.prepared().inputs().archmap().bytes_digest,
        second.prepared().inputs().archmap().bytes_digest
    );
    assert_eq!(
        second.prepared().inputs().archmap().sources[0].revision,
        "r2"
    );
    let mut inputs = sources(false, "", "r1");
    // 独立した不成立例は同じ木の合計4を5と比較する。
    let checked = check_inputs(inputs.clone(), &mut quiet()).unwrap();
    let law = String::from_utf8(checked.sources().law().bytes().to_vec())
        .unwrap()
        .replace("total(s.tree)=4", "total(s.tree)=5");
    inputs = InputSources::from_bytes(
        vec![tree::DEFINITIONS.as_bytes().to_vec()],
        law.into_bytes(),
        checked.sources().archmap().bytes().to_vec(),
    );
    let refuted =
        evaluate_observed_bytes(inputs, &["bad=check(Trees.four,s=@v/sample)"], &mut quiet())
            .unwrap();
    audit(&refuted);
    let wire = refuted.wire();
    assert_eq!(get(&wire, "status"), &Json::str("complete"));
    let a = answer(&wire, "bad");
    assert_eq!(get(a, "status"), &Json::str("refuted"));
    assert!(!array(get(a, "evidence")).is_empty());
}

#[test]
fn recursive_tree_infinite_domains_keep_typed_results_and_invalid_self_calls_are_rejected() {
    for predicate in ["true", "t=t"] {
        for view in [true, false] {
            let extra = if view {
                format!("view bad(s:Sample):Bool=forall t:Tree . {predicate};")
            } else {
                format!("law required bad(t:Tree):{predicate};")
            };
            let ask = if view {
                "a=evaluate(Trees.bad,s=@v/sample)"
            } else {
                "a=check(Trees.bad)"
            };
            let input = sources(false, &extra, "r1");
            let result = evaluate_observed_bytes(input.clone(), &[ask], &mut quiet()).unwrap();
            assert_eq!(result.prepared().inputs().sources(), &input);
            audit(&result);
            let wire = result.wire();
            let a = answer(&wire, "a");
            let decided = predicate == "true";
            assert_eq!(
                result.status(),
                if decided { "complete" } else { "partial" }
            );
            assert_eq!(
                get(a, "status"),
                &Json::str(if decided {
                    "established"
                } else {
                    "undetermined"
                })
            );
            let qs = array(get(get(a, "scope"), "quantifiers"));
            let q = qs
                .iter()
                .find(|q| get(q, "name") == &Json::str("t"))
                .unwrap();
            assert_eq!(get(q, "kind"), &Json::str("forall"));
            assert_eq!(get(q, "type"), &tree_type());
            let domain = array(get(&wire, "nodes"))
                .iter()
                .find(|n| get(n, "id") == get(get(q, "domain"), "node"))
                .unwrap();
            assert_eq!(get(domain, "type"), &Json::str("Domain"));
            assert_eq!(get(get(domain, "value"), "kind"), &Json::str("type"));
            assert_eq!(get(get(domain, "value"), "type"), &tree_type());
            if view && decided {
                assert_eq!(value(&wire, "a", Json::str("Bool")), &Json::Bool(true));
            }
            if !view {
                let claim = array(get(&wire, "nodes"))
                    .iter()
                    .find(|n| get(n, "id") == get(get(a, "claim"), "node"))
                    .unwrap();
                assert_eq!(get(claim, "type"), &Json::str("Proposition"));
                assert_eq!(get(get(claim, "judgment"), "status"), get(a, "status"));
            }
            if !decided {
                assert!(!object(get(a, "outputs")).contains_key("value"));
                let reason = array(get(a, "reasons"))
                    .iter()
                    .find(|r| get(r, "code") == &Json::str("unsupported_algorithm"))
                    .unwrap();
                assert!(array(get(get(reason, "details"), "operand_types")).contains(&tree_type()));
                let span = array(get(get(reason, "location"), "span"));
                let (Json::Nat(start), Json::Nat(end)) = (&span[0], &span[1]) else {
                    panic!("Law span")
                };
                assert!(!input.law().bytes()[*start as usize..*end as usize].is_empty());
            }
        }
    }
    for extra in [
        "view bad(t:Tree):Z=bad(t);",
        "view bad(t:Tree):Z=match t {Empty=>0;Leaf(_)=>0;Branch(l,r)=>bad(t);Packed(_)=>0;};",
        "view one(t:Tree):Z=two(t);view two(t:Tree):Z=one(t);",
    ] {
        let error = check_inputs(sources(false, extra, "r1"), &mut quiet()).unwrap_err();
        assert!(
            error
                .issues()
                .iter()
                .any(|i| get(i, "code") == &Json::str("cycle")),
            "{error:?}"
        );
    }
}
