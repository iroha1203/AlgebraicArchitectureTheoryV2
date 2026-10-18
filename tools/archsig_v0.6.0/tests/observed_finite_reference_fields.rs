mod common;
#[path = "common/finite_reference_fields.rs"]
mod fixture;
use archsig::{
    canonical::Json,
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
        panic!("text {j:?}")
    };
    v
}
fn f<'a>(j: &'a Json, k: &str) -> &'a Json {
    obj(j).get(k).unwrap_or_else(|| panic!("missing key {k}"))
}
fn refs(j: &Json, out: &mut Vec<String>) {
    match j {
        Json::Obj(v) if v.len() == 1 && v.contains_key("node") => out.push(text(&v["node"]).into()),
        Json::Obj(v) => {
            for j in v.values() {
                refs(j, out)
            }
        }
        Json::Arr(v) => {
            for j in v {
                refs(j, out)
            }
        }
        _ => {}
    }
}
fn nodes(j: &Json) -> BTreeMap<&str, &Json> {
    arr(f(j, "nodes"))
        .iter()
        .map(|n| (text(f(n, "id")), n))
        .collect()
}
fn answer<'a>(j: &'a Json, id: &str) -> &'a Json {
    arr(f(j, "answers"))
        .iter()
        .find(|a| f(a, "id") == &Json::str(id))
        .unwrap()
}
fn value<'a>(j: &'a Json, id: &str) -> &'a Json {
    let ns = nodes(j);
    f(
        ns[text(f(f(f(answer(j, id), "outputs"), "value"), "node"))],
        "value",
    )
}
fn run(i: InputSources, asks: &[&str]) -> Json {
    let checked =
        check_inputs(i.clone(), &mut quiet()).unwrap_or_else(|e| panic!("input {:?}", e.issues()));
    let r = evaluate_observed_bytes(i.clone(), asks, &mut quiet())
        .unwrap_or_else(|e| panic!("evaluate {e:?}"));
    assert_ne!(r.status(), "error", "{:?}", r.wire());
    assert_eq!(r.prepared().inputs().sources(), &i);
    assert_eq!(
        r.prepared().inputs().archmap().snapshots,
        checked.archmap().snapshots
    );
    assert_eq!(
        r.prepared().inputs().archmap().origins,
        checked.archmap().origins
    );
    assert_eq!(
        r.prepared().inputs().archmap().sources,
        checked.archmap().sources
    );
    let j = r.wire();
    let ns = nodes(&j);
    for a in arr(f(&j, "answers")) {
        assert!(
            !arr(f(a, "reasons"))
                .iter()
                .any(
                    |reason| obj(reason).get("code") == Some(&Json::str("unsupported_algorithm"))
                        && obj(f(reason, "details")).get("method")
                            == Some(&Json::str("unresolved_owned_expression_family"))
                        || obj(reason).get("code") == Some(&Json::str("unsupported_algorithm"))
                            && obj(f(reason, "details")).get("method")
                                == Some(&Json::str("unresolved_dependent_owner"))
                )
        );
        if let Some(claim) = obj(a).get("claim") {
            let claim = ns[text(f(claim, "node"))];
            assert_eq!(f(claim, "type"), &Json::str("Proposition"));
            assert_eq!(f(f(claim, "judgment"), "status"), f(a, "status"));
            assert_eq!(f(claim, "scope"), f(a, "scope"));
        }
    }
    let mut earlier = BTreeSet::new();
    for n in arr(f(&j, "nodes")) {
        let mut links = vec![];
        refs(n, &mut links);
        assert!(
            links.iter().all(|s| earlier.contains(s)),
            "earlier {links:?}"
        );
        earlier.insert(text(f(n, "id")).to_string());
        if let Some(v) = obj(n).get("value") {
            let mut links = vec![];
            refs(v, &mut links);
            for l in links {
                assert_ne!(f(ns[l.as_str()], "state"), &Json::str("blocked"));
                assert!(!obj(ns[l.as_str()]).contains_key("partial"));
            }
        }
        for fact in arr(f(n, "support")) {
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
            assert!(arr(f(f(n, "scope"), "snapshots")).contains(f(fact, "snapshot")));
            let origin = if let Some(field) = obj(fact).get("field") {
                let field = subject
                    .fields
                    .iter()
                    .find(|s| s.name == text(field))
                    .unwrap();
                match &field.slot {
                    archsig::archmap::Slot::Known { atom, origin, .. } => {
                        assert_eq!(f(fact, "atom"), &Json::str(atom));
                        origin
                    }
                    archsig::archmap::Slot::Missing => {
                        assert!(!obj(fact).contains_key("atom"));
                        &subject.origin
                    }
                }
            } else {
                &subject.origin
            };
            let origin = checked
                .archmap()
                .origins
                .iter()
                .find(|o| &o.id == origin)
                .unwrap();
            assert!(arr(f(f(n, "scope"), "modes")).contains(&Json::str(origin.mode.wire())));
            for location in &origin.locations {
                let source = checked
                    .archmap()
                    .sources
                    .iter()
                    .find(|s| s.id == location.source)
                    .unwrap();
                assert!(source.uri.starts_with("urn:fixture:"));
                assert!(!location.path.starts_with('/'));
                if source.revision == "r2" {
                    assert_eq!(location.span, Some((10, 11)));
                    assert!(source.uri.ends_with(":relocated"));
                }
            }
        }
    }
    j
}

fn original_missing(j: &Json, id: &str, subject: &str, field: &str) {
    let wanted = Json::obj([
        ("snapshot", Json::str("v")),
        ("subject", Json::str(subject)),
        ("field", Json::str(field)),
    ]);
    assert!(
        arr(f(answer(j, id), "reasons"))
            .iter()
            .any(|r| f(r, "code") == &Json::str("missing_observation")
                && arr(f(r, "missing")).contains(&wanted)
                && !arr(f(r, "dependencies")).is_empty()),
        "{id} {wanted:?}"
    );
}
fn assert_boolean_completion_pairs(j: &Json, id: &str, expected: &[Json]) {
    let ns = nodes(j);
    let pairs: Vec<_> = arr(f(answer(j, id), "evidence")).iter().map(|r| ns[text(f(r,"node"))]).filter(|n|obj(n).get("value").is_some_and(|v|if let Json::Obj(m)=v{m.get("kind")}else{None}==Some(&Json::str("completion_pair")))).collect();
    assert!(!pairs.is_empty());
    for pair in pairs {
        assert_eq!(f(pair, "type"), &Json::str("Evidence"));
        let data = f(f(pair, "value"), "data");
        let fields = arr(f(data, "fields"));
        assert_eq!(fields.len(), expected.len());
        for field in fields {
            assert_eq!(f(field, "snapshot"), &Json::str("v"));
            assert_eq!(f(field, "subject"), &Json::str("h"));
            assert!(!obj(field).contains_key("atom"));
        }
        for key in ["first", "second"] {
            let values = arr(f(data, key));
            assert_eq!(values.len(), expected.len());
            for (value, ty) in values.iter().zip(expected) {
                assert_eq!(f(ns[text(f(value, "node"))], "type"), ty);
            }
        }
        let results: BTreeSet<_> = ["first_result", "second_result"]
            .iter()
            .map(|key| {
                let evaluation = ns[text(f(f(data, key), "node"))];
                assert_eq!(f(evaluation, "type"), &Json::str("Evaluation"));
                let scalar = ns[text(f(f(f(evaluation, "value"), "value"), "node"))];
                assert_eq!(f(scalar, "type"), &Json::str("Bool"));
                f(scalar, "value").canonical()
            })
            .collect();
        assert_eq!(
            results,
            [Json::Bool(false), Json::Bool(true)]
                .iter()
                .map(Json::canonical)
                .collect()
        );
    }
}

fn domain<'a>(j: &'a Json, id: &str) -> &'a Json {
    let ns = nodes(j);
    let evaluation = ns[text(f(f(f(answer(j, id), "outputs"), "evaluation"), "node"))];
    let d = ns[text(f(&arr(f(evaluation, "arguments"))[1], "node"))];
    assert_eq!(f(d, "type"), &Json::str("Domain"));
    d
}
fn assignments(j: &Json, id: &str) -> BTreeSet<String> {
    let ns = nodes(j);
    arr(f(f(domain(j, id), "value"), "elements"))
        .iter()
        .map(|r| f(ns[text(f(r, "node"))], "value").canonical())
        .collect()
}
#[test]
fn finite_owned_field_completions_keep_shared_values_independent_slots_and_exact_type() {
    let input = fixture::input(false, false, false);
    let checked = check_inputs(input.clone(), &mut quiet()).unwrap();
    let original = checked.archmap().snapshots[0]
        .subjects
        .iter()
        .find(|s| s.id == "h")
        .unwrap()
        .fields
        .iter()
        .find(|f| f.name == "Fields.Holder.chosen")
        .unwrap();
    assert_eq!(
        original.ty,
        archsig::types::Type::Owned("Fields.Sample".into(), "owner".into())
    );
    assert_eq!(original.slot, archsig::archmap::Slot::Missing);
    let j = run(
        input,
        &[
            "same=evaluate(Inspect.same,h=@v/h)",
            "pair=evaluate(Inspect.pair,h=@v/h)",
            "independent=evaluate(Inspect.independent,h=@v/h)",
            "known=evaluate(Inspect.chosen,h=@v/k)",
            "called=evaluate(Inspect.called,h=@v/h)",
        ],
    );
    for id in ["same", "called"] {
        assert_eq!(value(&j, id), &Json::Bool(true));
        assert_eq!(f(answer(&j, id), "status"), &Json::str("established"));
    }
    assert_eq!(f(answer(&j, "pair"), "status"), &Json::str("undetermined"));
    assert_eq!(
        f(answer(&j, "independent"), "status"),
        &Json::str("undetermined")
    );
    assert_eq!(value(&j, "known"), &fixture::reference("v", "r"));
    for id in ["same", "pair", "independent", "called"] {
        original_missing(&j, id, "h", "Fields.Holder.chosen");
    }
    original_missing(&j, "independent", "h", "Fields.Holder.second");
    original_missing(&j, "known", "k", "Fields.Holder.chosen");
    let expected = ["p", "q"].map(|x| fixture::reference("v", x));
    assert_eq!(
        assignments(&j, "pair"),
        expected.iter().map(Json::canonical).collect()
    );
    let product: BTreeSet<_> = expected
        .iter()
        .flat_map(|a| {
            expected
                .iter()
                .map(move |b| Json::Arr(vec![a.clone(), b.clone()]).canonical())
        })
        .collect();
    assert_eq!(assignments(&j, "independent"), product);
    let ty = Json::Arr(vec![Json::str("Ref"), Json::str("Fields.Sample")]);
    assert_eq!(f(f(domain(&j, "pair"), "value"), "type"), &ty);
    assert_boolean_completion_pairs(&j, "independent", &[ty.clone(), ty]);
    let ns = nodes(&j);
    for reason in arr(f(answer(&j, "pair"), "reasons"))
        .iter()
        .filter(|r| f(r, "code") == &Json::str("missing_observation"))
    {
        for dependency in arr(f(reason, "dependencies")) {
            let source = ns[text(f(dependency, "node"))];
            let span = arr(f(f(f(source, "value"), "location"), "span"));
            let (Json::Nat(start), Json::Nat(end)) = (&span[0], &span[1]) else {
                panic!()
            };
            assert_eq!(
                &checked.sources().law().bytes()[*start as usize..*end as usize],
                b"h.chosen"
            );
            assert!(arr(f(f(source, "value"), "parameters")).is_empty());
            let bindings = arr(f(f(source, "value"), "bindings"));
            assert_eq!(bindings.len(), 1);
            assert_eq!(f(&bindings[0], "name"), &Json::str("h"));
            assert_eq!(
                f(ns[text(f(f(&bindings[0], "value"), "node"))], "type"),
                &Json::Arr(vec![Json::str("Ref"), Json::str("Fields.Holder")])
            );
        }
    }
}
#[test]
fn finite_reference_containers_and_data_keep_every_typed_value_and_empty_rosters() {
    let j = run(
        fixture::input(false, false, false),
        &[
            "maybe_value=evaluate(Inspect.maybe_value,h=@v/h)",
            "members=evaluate(Inspect.members,h=@v/h)",
            "mixed=evaluate(Inspect.mixed,h=@v/h)",
            "choice=evaluate(Inspect.choice,h=@v/h)",
            "empty_option=evaluate(Inspect.empty_option,h=@v/h)",
            "empty_set=evaluate(Inspect.empty_set,h=@v/h)",
        ],
    );
    let refs = ["p", "q"].map(|s| fixture::reference("v", s));
    let options = std::iter::once(Json::obj([("none", Json::Bool(true))]))
        .chain(refs.iter().cloned().map(|v| Json::obj([("some", v)])))
        .map(|v| v.canonical())
        .collect();
    assert_eq!(assignments(&j, "maybe_value"), options);
    let sets = [
        Json::Arr(vec![]),
        Json::Arr(vec![refs[0].clone()]),
        Json::Arr(vec![refs[1].clone()]),
        Json::Arr(refs.to_vec()),
    ]
    .into_iter()
    .map(|v| v.canonical())
    .collect();
    assert_eq!(assignments(&j, "members"), sets);
    let tuples = refs
        .iter()
        .flat_map(|v| [false, true].map(|b| Json::Arr(vec![v.clone(), Json::Bool(b)]).canonical()))
        .collect();
    assert_eq!(assignments(&j, "mixed"), tuples);
    let choice = std::iter::once(Json::obj([
        ("tag", Json::str("empty")),
        ("args", Json::Arr(vec![])),
    ]))
    .chain(["A", "B"].iter().flat_map(|s| {
        [false, true].map(|b| {
            Json::obj([
                ("tag", Json::str("pick")),
                (
                    "args",
                    Json::Arr(vec![fixture::reference("v", s), Json::Bool(b)]),
                ),
            ])
        })
    }))
    .map(|v| v.canonical())
    .collect();
    assert_eq!(assignments(&j, "choice"), choice);
    assert_eq!(
        value(&j, "empty_option"),
        &Json::obj([("none", Json::Bool(true))])
    );
    assert_eq!(value(&j, "empty_set"), &Json::Arr(vec![]));
    for id in [
        "maybe_value",
        "members",
        "mixed",
        "choice",
        "empty_option",
        "empty_set",
    ] {
        original_missing(&j, id, "h", &format!("Fields.Holder.{id}"));
        assert_eq!(
            f(f(answer(&j, id), "scope"), "domain"),
            &Json::str("all_completions")
        );
    }
}
#[test]
fn finite_owned_fields_share_unknown_owner_constraints_and_keep_current_snapshot_sources() {
    let joint = run(
        fixture::input(false, false, true),
        &["valid=check(Inspect.valid,h=@v/h)"],
    );
    assert_eq!(
        f(answer(&joint, "valid"), "status"),
        &Json::str("established")
    );
    for field in ["chosen", "owner"] {
        original_missing(&joint, "valid", "h", &format!("Fields.Holder.{field}"));
    }
    let wanted = [("p", "A"), ("q", "A"), ("r", "B")]
        .map(|(s, a)| {
            Json::Arr(vec![fixture::reference("v", s), fixture::reference("v", a)]).canonical()
        })
        .into_iter()
        .collect();
    assert_eq!(assignments(&joint, "valid"), wanted);
    let mut judgments = vec![];
    for moved in [false, true] {
        let j = run(
            fixture::input(true, moved, false),
            &[
                "plain=evaluate(Inspect.plain,h=@v/h)",
                "chosen=evaluate(Inspect.chosen,h=@v/h)",
            ],
        );
        let opts = std::iter::once(Json::obj([("none", Json::Bool(true))]))
            .chain(
                [("v", "A"), ("v", "B"), ("w", "C")]
                    .map(|(s, a)| Json::obj([("some", fixture::reference(s, a))])),
            )
            .map(|v| v.canonical())
            .collect();
        assert_eq!(assignments(&j, "plain"), opts);
        assert_eq!(
            assignments(&j, "chosen"),
            ["p", "q"]
                .map(|s| fixture::reference("v", s).canonical())
                .into_iter()
                .collect()
        );
        judgments.push(["plain", "chosen"].map(|id| f(answer(&j, id), "status").canonical()));
    }
    assert_eq!(judgments[0], judgments[1]);
}
#[test]
fn finite_owned_field_values_keep_known_map_totality_and_raw_missing_slots() {
    let input = fixture::map_constrained();
    let checked = check_inputs(input.clone(), &mut quiet()).unwrap();
    let holder = &checked.archmap().snapshots[0]
        .subjects
        .iter()
        .find(|s| s.id == "p")
        .unwrap();
    assert!(
        holder
            .fields
            .iter()
            .filter(|f| f.name.ends_with(".owner") || f.name.ends_with(".chosen"))
            .all(|f| f.slot == archsig::archmap::Slot::Missing)
    );
    let j = run(
        input,
        &[
            "chosen=evaluate(Applications.chosen,p=@v/p)",
            "valid=check(Applications.valid,p=@v/p)",
        ],
    );
    assert_eq!(
        f(answer(&j, "chosen"), "status"),
        &Json::str("undetermined")
    );
    assert_eq!(f(answer(&j, "valid"), "status"), &Json::str("established"));
    original_missing(&j, "chosen", "p", "Reservations.State.chosen");
    original_missing(&j, "valid", "p", "Reservations.State.owner");
    assert_eq!(
        assignments(&j, "chosen"),
        ["p", "q"]
            .map(|s| fixture::reference("v", s).canonical())
            .into_iter()
            .collect()
    );
    assert_eq!(
        assignments(&j, "valid"),
        ["p", "q"]
            .map(|s| Json::Arr(vec![
                fixture::reference("v", s),
                fixture::reference("v", "A")
            ])
            .canonical())
            .into_iter()
            .collect()
    );
    assert!(
        arr(f(domain(&j, "valid"), "support"))
            .iter()
            .any(|f| obj(f).get("atom") == Some(&Json::str("m-states")))
    );
}
#[test]
fn finite_reference_field_law_families_keep_full_numeric_axes_and_known_counterexamples() {
    let j = run(
        fixture::input(false, false, false),
        &["all=check(Inspect.each)", "numeric=check(Inspect.numeric)"],
    );
    for id in ["all", "numeric"] {
        assert_eq!(f(answer(&j, id), "status"), &Json::str("established"));
        for s in ["h", "k"] {
            original_missing(&j, id, s, "Fields.Holder.chosen");
        }
    }
    for (name, ty) in [("z", "Z"), ("q", "Q")] {
        assert!(
            arr(f(f(answer(&j, "numeric"), "scope"), "quantifiers"))
                .iter()
                .any(|v| f(v, "name") == &Json::str(name)
                    && f(v, "type") == &Json::str(ty)
                    && f(v, "kind") == &Json::str("forall"))
        );
    }
    for reverse in [false, true] {
        let j = run(
            fixture::counterexample(reverse),
            &["flags=check(Inspect.flags)", "later=evaluate(Inspect.seed)"],
        );
        assert_eq!(f(answer(&j, "flags"), "status"), &Json::str("refuted"));
        assert_eq!(value(&j, "later"), &Json::str("1"));
        original_missing(&j, "flags", "h", "Fields.Holder.flag");
        original_missing(&j, "flags", "h", "Fields.Holder.chosen");
        let ns = nodes(&j);
        let fact = Json::obj([
            ("snapshot", Json::str("v")),
            ("subject", Json::str("k")),
            ("field", Json::str("Fields.Holder.flag")),
            ("atom", Json::str("k-flag")),
        ]);
        let actual:Vec<_>=ns.values().filter(|n|obj(n).get("value").is_some_and(|v|if let Json::Obj(m)=v{m.get("kind")}else{None}==Some(&Json::str("counterexample")))).filter(|n|arr(f(f(f(n,"value"),"data"),"facts")).contains(&fact)).collect();
        assert!(!actual.is_empty());
        for n in actual {
            let d = f(f(n, "value"), "data");
            assert_eq!(
                f(ns[text(f(f(d, "left"), "node"))], "value"),
                &Json::Bool(false)
            );
            assert_eq!(
                f(ns[text(f(f(d, "right"), "node"))], "value"),
                &Json::Bool(true)
            );
            assert!(
                arr(f(d, "bindings"))
                    .iter()
                    .any(|v| f(v, "name") == &Json::str("h")
                        && f(ns[text(f(f(v, "value"), "node"))], "value")
                            == &fixture::reference("v", "k"))
            );
        }
    }
}
#[test]
fn finite_reference_fields_keep_known_owned_container_values_and_atom_sources() {
    let j = run(
        fixture::known_values(),
        &[
            "chosen=evaluate(Inspect.chosen,h=@v/h)",
            "maybe_value=evaluate(Inspect.maybe_value,h=@v/h)",
            "members=evaluate(Inspect.members,h=@v/h)",
            "mixed=evaluate(Inspect.mixed,h=@v/h)",
            "choice=evaluate(Inspect.choice,h=@v/h)",
        ],
    );
    for (id, expected) in [
        ("chosen", fixture::reference("v", "p")),
        (
            "maybe_value",
            Json::obj([("some", fixture::reference("v", "q"))]),
        ),
        (
            "members",
            Json::Arr(vec![
                fixture::reference("v", "p"),
                fixture::reference("v", "q"),
            ]),
        ),
        (
            "mixed",
            Json::Arr(vec![fixture::reference("v", "p"), Json::Bool(true)]),
        ),
        (
            "choice",
            Json::obj([
                ("tag", Json::str("pick")),
                (
                    "args",
                    Json::Arr(vec![fixture::reference("v", "A"), Json::Bool(false)]),
                ),
            ]),
        ),
    ] {
        assert_eq!(value(&j, id), &expected);
        assert_eq!(f(answer(&j, id), "status"), &Json::str("established"));
        assert!(arr(f(answer(&j, id), "reasons")).is_empty());
        assert_ne!(
            f(f(answer(&j, id), "scope"), "domain"),
            &Json::str("all_completions")
        );
        let ns = nodes(&j);
        let v = ns[text(f(f(f(answer(&j, id), "outputs"), "value"), "node"))];
        assert!(
            arr(f(v, "support"))
                .iter()
                .any(|fact| obj(fact).get("atom") == Some(&Json::str(format!("known-{id}"))))
        );
    }
}
