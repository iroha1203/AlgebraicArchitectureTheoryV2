#[allow(dead_code)]
#[path = "common/path_answer_projections.rs"]
mod fixture;
use archsig::{
    canonical::Json,
    observed::{
        control::{Control, Limits, Usage},
        evaluate_observed_bytes,
        input::InputSources,
    },
};
fn quiet() -> Control {
    Control::new(Limits::default(), |_| Usage::default())
}
fn f<'a>(value: &'a Json, name: &str) -> &'a Json {
    let Json::Obj(fields) = value else {
        panic!("object")
    };
    &fields[name]
}
fn arr(value: &Json) -> &[Json] {
    let Json::Arr(items) = value else {
        panic!("array")
    };
    items
}
fn node<'a>(wire: &'a Json, reference: &Json) -> &'a Json {
    arr(f(wire, "nodes"))
        .iter()
        .find(|node| f(node, "id") == f(reference, "node"))
        .unwrap()
}
fn answer<'a>(wire: &'a Json, id: &str) -> &'a Json {
    arr(f(wire, "answers"))
        .iter()
        .find(|answer| f(answer, "id") == &Json::str(id))
        .unwrap()
}
fn output<'a>(wire: &'a Json, id: &str) -> &'a Json {
    let a = answer(wire, id);
    assert_eq!(f(a, "status"), &Json::str("established"));
    let value = node(wire, f(f(a, "outputs"), "value"));
    assert_eq!(f(value, "state"), &Json::str("value"));
    value
}
fn binding<'a>(wire: &'a Json, id: &str, name: &str) -> &'a Json {
    let evaluation = node(wire, f(f(answer(wire, id), "outputs"), "evaluation"));
    f(
        arr(f(f(evaluation, "value"), "bindings"))
            .iter()
            .find(|binding| f(binding, "name") == &Json::str(name))
            .unwrap(),
        "value",
    )
}
fn refs(value: &Json, found: &mut Vec<String>) {
    match value {
        Json::Obj(fields) if fields.len() == 1 && fields.contains_key("node") => {
            let Json::Str(id) = &fields["node"] else {
                panic!("node id")
            };
            found.push(id.clone());
        }
        Json::Obj(fields) => fields.values().for_each(|value| refs(value, found)),
        Json::Arr(items) => items.iter().for_each(|value| refs(value, found)),
        _ => {}
    }
}
fn run(input: InputSources, asks: &[&str]) -> archsig::observed::ObservedEvaluation {
    let result =
        evaluate_observed_bytes(input.clone(), asks, &mut quiet()).unwrap_or_else(|error| {
            panic!("{:?}", error.wire().map(|wire| f(&wire, "issues").clone()))
        });
    assert_eq!(result.prepared().inputs().sources(), &input);
    let wire = result.wire();
    for (index, node) in arr(f(&wire, "nodes")).iter().enumerate() {
        assert_eq!(f(node, "id"), &Json::str(format!("n{index}")));
        let mut references = vec![];
        refs(node, &mut references);
        for reference in references {
            assert!(
                reference
                    .strip_prefix('n')
                    .unwrap()
                    .parse::<usize>()
                    .unwrap()
                    < index
            );
        }
    }
    result
}
#[test]
fn identity_path_endpoints_are_consumed_as_original_refs_in_request_order() {
    for endpoint in ["source", "target"] {
        let input = fixture::identity(false);
        let take = format!("q=evaluate(Walk.id,x=$p.value.{endpoint})");
        let result = evaluate_observed_bytes(
            input.clone(),
            &[&take, "p=evaluate(Walk.id,x=@v/a)"],
            &mut quiet(),
        )
        .unwrap();
        assert_eq!(result.status(), "complete");
        assert_eq!(result.prepared().inputs().sources(), &input);
        let wire = result.wire();
        let original = node(&wire, f(f(answer(&wire, "p"), "outputs"), "value"));
        let selected = f(f(original, "value"), endpoint);
        let evaluation = node(&wire, f(f(answer(&wire, "q"), "outputs"), "evaluation"));
        let bindings = arr(f(f(evaluation, "value"), "bindings"));
        assert_eq!(bindings.len(), 1);
        assert_eq!(f(&bindings[0], "name"), &Json::str("x"));
        assert_eq!(f(&bindings[0], "value"), selected);
        let actual = node(&wire, f(f(answer(&wire, "q"), "outputs"), "value"));
        for field in ["source", "target"] {
            assert_eq!(f(f(actual, "value"), field), selected);
            assert_eq!(
                f(node(&wire, selected), "value"),
                &Json::Arr(vec![Json::str("v"), Json::str("a")])
            );
        }
        assert_eq!(f(&arr(f(&wire, "answers"))[0], "id"), &Json::str("q"));
    }
}

#[test]
fn composed_path_components_keep_word_order_nested_refs_and_law_decisions() {
    let asks = [
        "source=evaluate(Walk.keep_node,x=$p.value.source)",
        "target=evaluate(Walk.keep_node,x=$p.evaluation.value.target)",
        "first=evaluate(Walk.keep_hop,e=$p.value.generators[0])",
        "last=evaluate(Walk.keep_hop,e=$p.evaluation.value.generators[1])",
        "deep=evaluate(Walk.keep_node,x=$n.evaluation.value.some[0][1].target)",
        "deepgen=evaluate(Walk.keep_hop,e=$n.value.some[1][1].generators[1])",
        "kept=evaluate(Walk.keep,p=$n.value.some[0][1])",
        "flag=evaluate(Walk.keep_bool,x=$n.value.some[0][0])",
        "yes=check(Walk.node_equal,x=$p.value.source,y=@v/p)",
        "no=check(Walk.node_equal,x=$p.value.target,y=@v/p)",
        "p=evaluate(Walk.join,e=@v/e,f=@v/next)",
        "n=evaluate(Walk.join_nested,e=@v/e,f=@v/next)",
    ];
    let result = run(fixture::composed(false, "r1"), &asks);
    assert_eq!(result.status(), "complete");
    let wire = result.wire();
    let path = f(output(&wire, "p"), "value");
    let generators = arr(f(path, "generators"));
    assert_eq!(generators.len(), 2);
    for (id, name, selected, subject, entity) in [
        ("source", "x", f(path, "source"), "p", "Paths.Node"),
        ("target", "x", f(path, "target"), "r", "Paths.Node"),
        ("first", "e", &generators[0], "e", "Paths.Hop"),
        ("last", "e", &generators[1], "next", "Paths.Hop"),
    ] {
        assert_eq!(binding(&wire, id, name), selected);
        assert_eq!(f(f(answer(&wire, id), "outputs"), "value"), selected);
        let value = output(&wire, id);
        assert_eq!(
            f(value, "type"),
            &Json::Arr(vec![Json::str("Ref"), Json::str(entity)])
        );
        assert_eq!(
            f(value, "value"),
            &Json::Arr(vec![Json::str("v"), Json::str(subject)])
        );
    }
    let list = node(&wire, f(f(output(&wire, "n"), "value"), "some"));
    let first_tuple = node(&wire, &arr(f(list, "value"))[0]);
    let fields = arr(f(first_tuple, "value"));
    for (id, parameter, index) in [("kept", "p", 1), ("flag", "x", 0)] {
        assert_eq!(binding(&wire, id, parameter), &fields[index]);
        assert_eq!(f(f(answer(&wire, id), "outputs"), "value"), &fields[index]);
    }
    for (row, id, field) in [(0, "deep", "target"), (1, "deepgen", "generators")] {
        let tuple = node(&wire, &arr(f(list, "value"))[row]);
        let path = f(node(&wire, &arr(f(tuple, "value"))[1]), "value");
        let selected = if field == "generators" {
            &arr(f(path, field))[1]
        } else {
            f(path, field)
        };
        assert_eq!(f(f(answer(&wire, id), "outputs"), "value"), selected);
        assert_eq!(
            binding(&wire, id, if id == "deep" { "x" } else { "e" }),
            selected
        );
    }
    for (id, status) in [("yes", "established"), ("no", "refuted")] {
        let a = answer(&wire, id);
        assert_eq!(f(a, "status"), &Json::str(status));
        let claim = node(&wire, f(a, "claim"));
        assert_eq!(f(claim, "type"), &Json::str("Proposition"));
        assert_eq!(f(f(claim, "judgment"), "status"), f(a, "status"));
        assert_eq!(f(f(claim, "judgment"), "evidence"), f(a, "evidence"));
        assert!(!arr(f(a, "evidence")).is_empty());
    }
    assert_eq!(
        arr(f(&wire, "answers"))
            .iter()
            .map(|a| f(a, "id").clone())
            .collect::<Vec<_>>(),
        asks.iter()
            .map(|ask| Json::str(ask.split('=').next().unwrap()))
            .collect::<Vec<_>>()
    );
    for request in arr(f(&wire, "requests")).iter().take(8) {
        assert_eq!(
            f(&arr(f(request, "arguments"))[0], "origin"),
            &Json::str("explicit")
        );
        assert!(
            arr(f(request, "defaults"))
                .iter()
                .any(|d| f(d, "rule") == &Json::str("observed_environment"))
        );
    }
}

#[test]
fn correspondence_path_reuses_its_endpoint_and_generator_refs() {
    let result = run(
        fixture::correspondence("normal", "r1"),
        &[
            "a=evaluate(Reservations.keep_system,a=$p.value.source)",
            "b=evaluate(Reservations.keep_system,a=$p.evaluation.value.target)",
            "m=evaluate(Reservations.keep_migration,m=$p.value.generators[0])",
            "p=evaluate(Reservations.step,m=@v/m)",
        ],
    );
    assert_eq!(result.status(), "complete");
    let wire = result.wire();
    let path = f(output(&wire, "p"), "value");
    assert_eq!(arr(f(path, "generators")).len(), 1);
    for (id, parameter, selected, subject, entity) in [
        ("a", "a", f(path, "source"), "A", "Reservations.System"),
        ("b", "a", f(path, "target"), "B", "Reservations.System"),
        (
            "m",
            "m",
            &arr(f(path, "generators"))[0],
            "m",
            "Reservations.Migration",
        ),
    ] {
        assert_eq!(binding(&wire, id, parameter), selected);
        assert_eq!(f(f(answer(&wire, id), "outputs"), "value"), selected);
        assert_eq!(
            f(output(&wire, id), "type"),
            &Json::Arr(vec![Json::str("Ref"), Json::str(entity)])
        );
        assert_eq!(
            f(output(&wire, id), "value"),
            &Json::Arr(vec![Json::str("v"), Json::str(subject)])
        );
    }
}

fn condition(wire: &Json, id: &str, producer: &str) {
    let a = answer(wire, id);
    assert_eq!(f(a, "status"), &Json::str("undetermined"));
    assert_eq!(f(a, "outputs"), &Json::obj([]));
    let reasons = arr(f(a, "reasons"));
    let failure = reasons
        .iter()
        .find(|reason| f(reason, "code") == &Json::str("condition_failed"))
        .unwrap();
    let proof = node(wire, f(f(failure, "details"), "condition"));
    assert_eq!(f(proof, "type"), &Json::str("Proposition"));
    assert_eq!(f(f(proof, "judgment"), "status"), &Json::str("refuted"));
    assert!(!arr(f(proof, "evidence")).is_empty());
    assert!(reasons.iter().any(
        |reason| f(reason, "code") == &Json::str("dependency_blocked")
            && f(f(reason, "details"), "request") == &Json::str(producer)
    ));
}
#[test]
fn path_projection_dynamic_index_owner_and_type_failures_keep_independent_answers() {
    for index in [2_u64, 9_007_199_254_740_991] {
        let bad = format!("index=evaluate(Walk.keep_hop,e=$p.value.generators[{index}])");
        let result = run(
            fixture::composed(false, "r1"),
            &[
                "seed=evaluate(Walk.seed)",
                "prior=check(Walk.prior)",
                "owner=evaluate(Walk.own_node,a=@w/A,x=$p.value.source)",
                &bad,
                "later=evaluate(Walk.keep_hop,e=$index.value)",
                "p=evaluate(Walk.join,e=@v/e,f=@v/next)",
            ],
        );
        assert_eq!(result.status(), "partial");
        let wire = result.wire();
        condition(&wire, "owner", "p");
        condition(&wire, "index", "p");
        assert_eq!(f(output(&wire, "seed"), "value"), &Json::str("1"));
        assert_eq!(f(answer(&wire, "prior"), "status"), &Json::str("refuted"));
        let prior_claim = node(&wire, f(answer(&wire, "prior"), "claim"));
        assert_eq!(f(prior_claim, "type"), &Json::str("Proposition"));
        assert_eq!(
            f(f(prior_claim, "judgment"), "status"),
            &Json::str("refuted")
        );
        assert!(!arr(f(answer(&wire, "prior"), "evidence")).is_empty());
        assert_eq!(
            arr(f(f(output(&wire, "p"), "value"), "generators")).len(),
            2
        );
        let later = answer(&wire, "later");
        assert_eq!(f(later, "status"), &Json::str("undetermined"));
        assert_eq!(f(later, "outputs"), &Json::obj([]));
        assert!(
            arr(f(later, "reasons"))
                .iter()
                .any(
                    |reason| f(reason, "code") == &Json::str("dependency_blocked")
                        && f(f(reason, "details"), "request") == &Json::str("index")
                )
        );
        for reason in arr(f(answer(&wire, "index"), "reasons")) {
            assert!(arr(f(later, "reasons")).contains(reason));
        }
    }
    let result = run(
        fixture::correspondence("normal", "r1"),
        &[
            "take=evaluate(Reservations.keep_reserve,r=$p.value.generators[0])",
            "p=evaluate(Reservations.step,m=@v/m)",
        ],
    );
    assert_eq!(result.status(), "partial");
    condition(&result.wire(), "take", "p");
}

#[test]
fn empty_path_word_none_and_missing_producer_keep_distinct_typed_failures() {
    let result = run(
        fixture::internal("normal", "r1"),
        &[
            "take=evaluate(Walk.keep_hop,e=$p.value.generators[0])",
            "p=evaluate(Walk.identity_node,x=@v/p)",
        ],
    );
    assert_eq!(result.status(), "partial");
    condition(&result.wire(), "take", "p");
    let result = run(
        fixture::identity(false),
        &[
            "take=evaluate(Walk.id,x=$p.value.some.source)",
            "p=evaluate(Walk.absent)",
        ],
    );
    assert_eq!(result.status(), "partial");
    condition(&result.wire(), "take", "p");
    let result = run(
        fixture::internal("missing_to", "r1"),
        &[
            "take=evaluate(Walk.keep_node,x=$p.value.source)",
            "later=evaluate(Walk.keep_node,x=$take.value)",
            "p=evaluate(Walk.step,e=@v/e)",
            "seed=evaluate(Walk.seed)",
            "prior=check(Walk.prior)",
        ],
    );
    assert_eq!(result.status(), "partial");
    let wire = result.wire();
    let reasons = arr(f(answer(&wire, "p"), "reasons"));
    assert!(
        reasons
            .iter()
            .any(|reason| f(reason, "code") == &Json::str("missing_observation"))
    );
    for (id, dependency) in [("take", "p"), ("later", "take")] {
        let a = answer(&wire, id);
        assert_eq!(f(a, "status"), &Json::str("undetermined"));
        assert_eq!(f(a, "outputs"), &Json::obj([]));
        assert!(arr(f(a, "reasons")).iter().any(|reason| f(reason, "code")
            == &Json::str("dependency_blocked")
            && f(f(reason, "details"), "request") == &Json::str(dependency)));
        assert!(
            !arr(f(a, "reasons"))
                .iter()
                .any(|reason| f(reason, "code") == &Json::str("condition_failed"))
        );
        for reason in arr(f(answer(&wire, dependency), "reasons")) {
            assert!(arr(f(a, "reasons")).contains(reason));
        }
    }
    assert_eq!(f(output(&wire, "seed"), "value"), &Json::str("1"));
    assert_eq!(f(answer(&wire, "prior"), "status"), &Json::str("refuted"));
}

#[test]
fn path_projection_rejects_private_fields_unindexed_words_and_ref_encodings_statically() {
    for path in [
        ".reading",
        ".generators",
        ".generators[0].subject",
        ".source[0]",
        ".target.body",
        ".generators[0]",
        ".generators[18446744073709551615]",
    ] {
        let take = format!("take=evaluate(Walk.keep_node,x=$p.value{path})");
        let error = evaluate_observed_bytes(
            fixture::internal("normal", "r1"),
            &[&take, "p=evaluate(Walk.step,e=@v/e)"],
            &mut quiet(),
        )
        .unwrap_err();
        let wire = error.wire().unwrap();
        assert_eq!(f(&wire, "status"), &Json::str("invalid"));
        assert!(arr(f(&wire, "nodes")).is_empty());
        assert!(arr(f(&wire, "answers")).is_empty());
    }
}

#[test]
fn path_projection_preserves_producer_prefix_support_scope_and_current_provenance() {
    let make = "p=evaluate(Walk.join,e=@v/e,f=@v/next)";
    let asks = [
        "source=evaluate(Walk.keep_node,x=$p.value.source)",
        "target=evaluate(Walk.keep_node,x=$p.value.target)",
        "generator=evaluate(Walk.keep_hop,e=$p.value.generators[1])",
        make,
    ];
    let mut wires = vec![];
    for revision in ["r1", "r2"] {
        let input = fixture::composed(false, revision);
        let producer = run(input.clone(), &[make]);
        let result = run(input, &asks);
        assert_eq!(result.status(), "complete");
        let wire = result.wire();
        let producer_wire = producer.wire();
        let prefix = arr(f(&producer_wire, "nodes"));
        assert_eq!(&arr(f(&wire, "nodes"))[..prefix.len()], prefix);
        let checked = result.prepared().inputs();
        for id in ["source", "target", "generator"] {
            let value = output(&wire, id);
            assert!(arr(f(f(value, "scope"), "snapshots")).contains(&Json::str("v")));
            let support = arr(f(value, "support"));
            assert!(!support.is_empty());
            for fact in support {
                let Json::Obj(fields) = fact else {
                    panic!("fact")
                };
                let text = |key: &str| {
                    let Json::Str(value) = &fields[key] else {
                        panic!("fact field")
                    };
                    value.as_str()
                };
                let snapshot = checked
                    .archmap()
                    .snapshots
                    .iter()
                    .find(|s| s.id == text("snapshot"))
                    .unwrap();
                let subject = snapshot
                    .subjects
                    .iter()
                    .find(|s| s.id == text("subject"))
                    .unwrap();
                let origin = if fields.contains_key("field") {
                    let field = subject
                        .fields
                        .iter()
                        .find(|f| f.name == text("field"))
                        .unwrap();
                    let archsig::archmap::Slot::Known { atom, origin, .. } = &field.slot else {
                        panic!("known support")
                    };
                    assert_eq!(atom, text("atom"));
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
                assert!(!origin.locations.is_empty());
                for location in &origin.locations {
                    let source = checked
                        .archmap()
                        .sources
                        .iter()
                        .find(|s| s.id == location.source)
                        .unwrap();
                    assert_eq!(source.revision, revision);
                    assert_eq!(
                        location.span,
                        Some(if revision == "r1" { (0, 1) } else { (10, 11) })
                    );
                }
            }
        }
        wires.push(wire);
    }
    assert_ne!(f(&wires[0], "inputs"), f(&wires[1], "inputs"));
    assert_eq!(f(&wires[0], "nodes"), f(&wires[1], "nodes"));
    assert_eq!(f(&wires[0], "answers"), f(&wires[1], "answers"));
}
