mod common;
#[path = "common/map_field_completions.rs"]
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
    run_with_family_state(i, asks, false)
}
fn run_with_family_state(i: InputSources, asks: &[&str], pending: bool) -> Json {
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
                        && !pending
                        || obj(reason).get("code") == Some(&Json::str("unsupported_algorithm"))
                            && obj(f(reason, "details")).get("method")
                                == Some(&Json::str("unresolved_dependent_owner"))
                ),
            "answer {:?} reasons {:?}",
            f(a, "id"),
            f(a, "reasons")
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
fn map_field_completions_share_tables_keep_independent_slots_and_actual_application() {
    let input = fixture::input(false, false, false, false);
    let checked = check_inputs(input.clone(), &mut quiet()).unwrap();
    let field = checked.archmap().snapshots[0]
        .subjects
        .iter()
        .find(|s| s.id == "h")
        .unwrap()
        .fields
        .iter()
        .find(|f| f.name == "MapFields.Holder.table")
        .unwrap();
    assert_eq!(
        field.ty,
        archsig::types::Type::Map(
            Box::new(archsig::types::Type::Owned(
                "MapFields.Key".into(),
                "owner".into()
            )),
            Box::new(archsig::types::Type::Owned(
                "MapFields.Image".into(),
                "owner".into()
            ))
        )
    );
    assert_eq!(field.slot, archsig::archmap::Slot::Missing);
    let j = run(
        input,
        &[
            "same=evaluate(Inspect.same,h=@v/h)",
            "pair=evaluate(Inspect.pair,h=@v/h)",
            "independent=evaluate(Inspect.independent,h=@v/h)",
            "read=evaluate(Inspect.read,h=@v/h)",
            "apply=evaluate(Inspect.apply,h=@v/h,x=@v/k)",
            "lexical=evaluate(Inspect.lexical,h=@v/h,x=@v/k)",
            "called=evaluate(Inspect.called,h=@v/h,x=@v/k)",
        ],
    );
    assert_eq!(value(&j, "same"), &Json::Bool(true));
    let maps = [fixture::table("v", "k", "x"), fixture::table("v", "k", "y")];
    assert_eq!(
        assignments(&j, "read"),
        maps.iter().map(Json::canonical).collect()
    );
    assert_eq!(
        assignments(&j, "pair"),
        maps.iter().map(Json::canonical).collect()
    );
    let product = maps
        .iter()
        .flat_map(|a| {
            maps.iter()
                .map(move |b| Json::Arr(vec![a.clone(), b.clone()]).canonical())
        })
        .collect();
    assert_eq!(assignments(&j, "independent"), product);
    for id in ["pair", "independent", "read", "apply", "lexical", "called"] {
        assert_eq!(f(answer(&j, id), "status"), &Json::str("undetermined"));
        original_missing(&j, id, "h", "MapFields.Holder.table");
    }
    let ty = Json::Arr(vec![
        Json::str("Map"),
        Json::Arr(vec![Json::str("Ref"), Json::str("MapFields.Key")]),
        Json::Arr(vec![Json::str("Ref"), Json::str("MapFields.Image")]),
    ]);
    assert_boolean_completion_pairs(&j, "independent", &[ty.clone(), ty]);
    original_missing(&j, "same", "h", "MapFields.Holder.table");
    let ns = nodes(&j);
    for reason in arr(f(answer(&j, "read"), "reasons"))
        .iter()
        .filter(|r| f(r, "code") == &Json::str("missing_observation"))
    {
        for dependency in arr(f(reason, "dependencies")) {
            let source = ns[text(f(dependency, "node"))];
            let span = arr(f(f(f(source, "value"), "location"), "span"));
            let (Json::Nat(a), Json::Nat(z)) = (&span[0], &span[1]) else {
                panic!()
            };
            assert_eq!(
                &checked.sources().law().bytes()[*a as usize..*z as usize],
                b"h.table"
            );
            let bindings = arr(f(f(source, "value"), "bindings"));
            assert_eq!(bindings.len(), 1);
            assert_eq!(f(&bindings[0], "name"), &Json::str("h"));
            assert_eq!(
                f(ns[text(f(f(&bindings[0], "value"), "node"))], "type"),
                &Json::Arr(vec![Json::str("Ref"), Json::str("MapFields.Holder")])
            );
        }
    }
}
#[test]
fn map_field_unknown_owner_keeps_conditional_key_sets_and_known_map_constraints() {
    let maps = [fixture::table("v", "k", "x"), fixture::table("v", "k", "y")];
    for anchor in [false, true] {
        let j = run(
            fixture::input(false, false, true, anchor),
            &[
                "read=evaluate(Inspect.read,h=@v/h)",
                "summary=evaluate(Inspect.summary,h=@v/h)",
                "valid=check(Inspect.valid,h=@v/h)",
            ],
        );
        let mut expected: BTreeSet<_> = maps.iter().map(Json::canonical).collect();
        if !anchor {
            expected.insert(Json::Arr(vec![]).canonical());
        }
        assert_eq!(assignments(&j, "read"), expected);
        let mut joint: BTreeSet<_> = maps
            .iter()
            .map(|m| Json::Arr(vec![fixture::reference("v", "A"), m.clone()]).canonical())
            .collect();
        if !anchor {
            joint.insert(
                Json::Arr(vec![fixture::reference("v", "B"), Json::Arr(vec![])]).canonical(),
            );
        }
        assert_eq!(assignments(&j, "summary"), joint);
        assert_eq!(assignments(&j, "valid"), joint);
        assert_eq!(f(answer(&j, "valid"), "status"), &Json::str("established"));
        for id in ["read", "summary", "valid"] {
            original_missing(&j, id, "h", "MapFields.Holder.table");
        }
        for id in ["summary", "valid"] {
            original_missing(&j, id, "h", "MapFields.Holder.owner");
        }
        if anchor {
            assert!(
                arr(f(domain(&j, "read"), "support"))
                    .iter()
                    .any(|v| obj(v).get("atom") == Some(&Json::str("anchor")))
            );
        }
    }
}
#[test]
fn map_field_finite_containers_keep_each_shared_owner_and_typed_whole_value() {
    let maps = [fixture::table("v", "k", "x"), fixture::table("v", "k", "y")];
    for unknown in [false, true] {
        let j = run(
            fixture::input(false, false, unknown, false),
            &[
                "maybe_value=evaluate(Inspect.maybe_value,h=@v/h)",
                "mixed=evaluate(Inspect.mixed,h=@v/h)",
                "bag=evaluate(Inspect.bag,h=@v/h)",
                "choice=evaluate(Inspect.choice,h=@v/h)",
            ],
        );
        let mut map_values = maps.to_vec();
        if unknown {
            map_values.push(Json::Arr(vec![]));
        }
        let option_values = std::iter::once(Json::obj([("none", Json::Bool(true))]))
            .chain(map_values.iter().cloned().map(|v| Json::obj([("some", v)])))
            .map(|v| v.canonical())
            .collect();
        assert_eq!(assignments(&j, "maybe_value"), option_values);
        let tuple_values = map_values
            .iter()
            .flat_map(|m| {
                [false, true].map(|b| Json::Arr(vec![Json::Bool(b), m.clone()]).canonical())
            })
            .collect();
        assert_eq!(assignments(&j, "mixed"), tuple_values);
        let mut sets: BTreeSet<_> = [
            Json::Arr(vec![]),
            Json::Arr(vec![maps[0].clone()]),
            Json::Arr(vec![maps[1].clone()]),
            Json::Arr(maps.to_vec()),
        ]
        .iter()
        .map(Json::canonical)
        .collect();
        if unknown {
            sets.insert(Json::Arr(vec![Json::Arr(vec![])]).canonical());
        }
        assert_eq!(
            assignments(&j, "bag"),
            sets,
            "same holder owner applies to every Map in a Set"
        );
        let choices = std::iter::once(Json::obj([
            ("tag", Json::str("blank")),
            ("args", Json::Arr(vec![])),
        ]))
        .chain(
            maps.iter()
                .cloned()
                .map(|m| Json::obj([("tag", Json::str("wrap")), ("args", Json::Arr(vec![m]))])),
        )
        .map(|v| v.canonical())
        .collect();
        assert_eq!(assignments(&j, "choice"), choices);
        for id in ["maybe_value", "mixed", "bag", "choice"] {
            original_missing(&j, id, "h", &format!("MapFields.Holder.{id}"));
        }
    }
}
#[test]
fn map_field_empty_domains_and_inconsistent_nonempty_to_empty_keep_input_stages() {
    let j = run(
        fixture::empty_rosters(),
        &[
            "read=evaluate(Inspect.read,h=@v/h)",
            "empty=evaluate(Inspect.empty,h=@v/h)",
            "maybe_value=evaluate(Inspect.maybe_value,h=@v/h)",
            "bag=evaluate(Inspect.bag,h=@v/h)",
        ],
    );
    for id in ["read", "empty"] {
        assert_eq!(value(&j, id), &Json::Arr(vec![]));
        assert_eq!(f(answer(&j, id), "status"), &Json::str("established"));
        assert_eq!(
            assignments(&j, id),
            [Json::Arr(vec![]).canonical()].into_iter().collect()
        );
    }
    assert_eq!(
        assignments(&j, "maybe_value"),
        [
            Json::obj([("none", Json::Bool(true))]),
            Json::obj([("some", Json::Arr(vec![]))])
        ]
        .iter()
        .map(Json::canonical)
        .collect()
    );
    assert_eq!(
        assignments(&j, "bag"),
        [Json::Arr(vec![]), Json::Arr(vec![Json::Arr(vec![])])]
            .iter()
            .map(Json::canonical)
            .collect()
    );
    original_missing(&j, "read", "h", "MapFields.Holder.table");
    original_missing(&j, "empty", "h", "MapFields.Holder.empty");
    let failure = check_inputs(fixture::no_images(), &mut quiet()).unwrap_err();
    assert_eq!(
        failure.status(),
        archsig::observed::input::InputStatus::Invalid
    );
    assert!(
        failure
            .issues()
            .iter()
            .any(|v| f(v, "code") == &Json::str("inconsistent_observation"))
    );
    assert!(!failure.declarations().is_empty());
    assert!(!failure.primitives().is_empty());
    let w = failure.wire();
    for key in ["requests", "answers", "nodes"] {
        assert!(arr(f(&w, key)).is_empty());
    }
}
#[test]
fn map_field_cross_snapshot_keys_and_current_provenance_keep_every_full_table() {
    let mut statuses = vec![];
    for moved in [false, true] {
        let j = run(
            fixture::input(true, moved, false, false),
            &[
                "plain=evaluate(Inspect.plain,h=@v/h)",
                "same=evaluate(Inspect.same,h=@v/h)",
            ],
        );
        let images = [
            fixture::reference("v", "x"),
            fixture::reference("v", "y"),
            fixture::reference("w", "x"),
        ];
        let tables = images
            .iter()
            .flat_map(|a| {
                images.iter().map(move |b| {
                    Json::Arr(vec![
                        Json::Arr(vec![fixture::reference("v", "k"), a.clone()]),
                        Json::Arr(vec![fixture::reference("w", "k"), b.clone()]),
                    ])
                    .canonical()
                })
            })
            .collect();
        assert_eq!(assignments(&j, "plain"), tables);
        assert_eq!(
            assignments(&j, "same"),
            [fixture::table("v", "k", "x"), fixture::table("v", "k", "y")]
                .iter()
                .map(Json::canonical)
                .collect()
        );
        assert_eq!(value(&j, "same"), &Json::Bool(true));
        original_missing(&j, "plain", "h", "MapFields.Holder.plain");
        original_missing(&j, "same", "h", "MapFields.Holder.table");
        statuses.push(["plain", "same"].map(|id| f(answer(&j, id), "status").canonical()));
    }
    assert_eq!(statuses[0], statuses[1]);
}
#[test]
fn map_field_law_wholes_keep_full_numeric_axes_and_counterexamples_in_both_orders() {
    let j = run(
        fixture::input(false, false, false, false),
        &["all=check(Inspect.each)", "numeric=check(Inspect.numeric)"],
    );
    for id in ["all", "numeric"] {
        assert_eq!(f(answer(&j, id), "status"), &Json::str("established"));
        for s in ["h", "j"] {
            original_missing(&j, id, s, "MapFields.Holder.table");
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
        original_missing(&j, "flags", "h", "MapFields.Holder.table");
        original_missing(&j, "flags", "h", "MapFields.Holder.flag");
        let ns = nodes(&j);
        let fact = Json::obj([
            ("snapshot", Json::str("v")),
            ("subject", Json::str("j")),
            ("field", Json::str("MapFields.Holder.flag")),
            ("atom", Json::str("j-flag")),
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
                    .any(|b| f(b, "name") == &Json::str("h")
                        && f(ns[text(f(f(b, "value"), "node"))], "value")
                            == &fixture::reference("v", "j"))
            );
        }
    }
}
#[test]
fn map_field_known_values_keep_original_map_container_atoms_and_sources() {
    let j = run(
        fixture::known_values(),
        &[
            "table=evaluate(Inspect.read,h=@v/h)",
            "maybe_value=evaluate(Inspect.maybe_value,h=@v/h)",
            "mixed=evaluate(Inspect.mixed,h=@v/h)",
            "bag=evaluate(Inspect.bag,h=@v/h)",
            "choice=evaluate(Inspect.choice,h=@v/h)",
        ],
    );
    for (id, expected) in [
        ("table", fixture::table("v", "k", "x")),
        (
            "maybe_value",
            Json::obj([("some", fixture::table("v", "k", "y"))]),
        ),
        (
            "mixed",
            Json::Arr(vec![Json::Bool(true), fixture::table("v", "k", "x")]),
        ),
        (
            "bag",
            Json::Arr(vec![
                fixture::table("v", "k", "x"),
                fixture::table("v", "k", "y"),
            ]),
        ),
        (
            "choice",
            Json::obj([
                ("tag", Json::str("wrap")),
                ("args", Json::Arr(vec![fixture::table("v", "k", "x")])),
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
        let n = ns[text(f(f(f(answer(&j, id), "outputs"), "value"), "node"))];
        assert!(
            arr(f(n, "support"))
                .iter()
                .any(|p| obj(p).get("atom") == Some(&Json::str(format!("known-{id}"))))
        );
    }
}
#[test]
fn map_field_owner_rediscovery_keeps_other_numeric_missing_without_stale_algorithm_reason() {
    let input = fixture::input(false, false, true, false);
    let checked = check_inputs(input.clone(), &mut quiet()).unwrap();
    let j = run(
        input,
        &[
            "seed=evaluate(Inspect.seed)",
            "prior=check(Inspect.prior)",
            "partial=evaluate(Inspect.partial,h=@v/h)",
            "later=evaluate(Inspect.seed)",
        ],
    );
    assert_eq!(value(&j, "seed"), &Json::str("1"));
    assert_eq!(value(&j, "later"), &Json::str("1"));
    assert_eq!(f(answer(&j, "prior"), "status"), &Json::str("refuted"));
    assert_eq!(
        f(answer(&j, "partial"), "status"),
        &Json::str("undetermined")
    );
    assert!(!obj(f(answer(&j, "partial"), "outputs")).contains_key("value"));
    for name in ["table", "owner", "level"] {
        original_missing(&j, "partial", "h", &format!("MapFields.Holder.{name}"));
    }
    let ns = nodes(&j);
    let mut counts = BTreeSet::new();
    for n in ns
        .values()
        .filter(|n| f(n, "type") == &Json::str("Evaluation"))
    {
        let v = f(n, "value");
        let Some(e) = obj(v).get("expression") else {
            continue;
        };
        let source = ns[text(f(e, "node"))];
        let Some(location) = obj(f(source, "value")).get("location") else {
            continue;
        };
        let Some(span) = obj(location).get("span") else {
            continue;
        };
        let span = arr(span);
        let (Json::Nat(a), Json::Nat(z)) = (&span[0], &span[1]) else {
            panic!()
        };
        if &checked.sources().law().bytes()[*a as usize..*z as usize] != b"count(Key[h.owner])" {
            continue;
        }
        if let Some(r) = obj(v).get("value") {
            let n = ns[text(f(r, "node"))];
            assert_eq!(f(n, "type"), &Json::str("Z"));
            counts.insert(f(n, "value").canonical());
        }
    }
    assert_eq!(
        counts,
        [Json::str("0"), Json::str("1")]
            .iter()
            .map(Json::canonical)
            .collect()
    );
}
#[test]
fn map_field_unresolved_nonfinite_owner_case_retains_its_algorithm_and_missing_sources() {
    let input = fixture::input(false, false, false, false);
    let checked = check_inputs(input.clone(), &mut quiet()).unwrap();
    let j = run_with_family_state(
        input,
        &["pending=evaluate(Inspect.pending,h=@v/h,a=@v/B)"],
        true,
    );
    assert_eq!(
        f(answer(&j, "pending"), "status"),
        &Json::str("undetermined")
    );
    assert!(!obj(f(answer(&j, "pending"), "outputs")).contains_key("value"));
    for name in ["table", "level"] {
        original_missing(&j, "pending", "h", &format!("MapFields.Holder.{name}"));
    }
    let d = domain(&j, "pending");
    let order: BTreeMap<_, _> = arr(f(&j, "nodes"))
        .iter()
        .enumerate()
        .map(|(i, n)| (text(f(n, "id")), i))
        .collect();
    let ns = nodes(&j);
    let mut actual_case_reason = false;
    for r in arr(f(answer(&j, "pending"), "reasons")).iter().filter(|r| {
        f(r, "code") == &Json::str("unsupported_algorithm")
            && obj(f(r, "details")).get("method")
                == Some(&Json::str("unresolved_owned_expression_family"))
    }) {
        assert_eq!(
            f(f(r, "details"), "operand_types"),
            &Json::Arr(vec![Json::Arr(vec![
                Json::str("Set"),
                Json::Arr(vec![Json::str("Ref"), Json::str("MapFields.Key")])
            ])])
        );
        for dep in arr(f(r, "dependencies")) {
            let id = text(f(dep, "node"));
            let source = ns[id];
            let span = arr(f(f(f(source, "value"), "location"), "span"));
            let (Json::Nat(a), Json::Nat(z)) = (&span[0], &span[1]) else {
                panic!()
            };
            assert_eq!(
                &checked.sources().law().bytes()[*a as usize..*z as usize],
                b"Key[if h.level=0 then h.owner else a]"
            );
            actual_case_reason |= order[id] > order[text(f(d, "id"))];
        }
    }
    assert!(
        actual_case_reason,
        "case内でも未解決ならseedの古い理由の削除だけで消さない"
    );
}
