//! 実prefixのownerに従う有限複合Law parameterの三入力接続。
#[path = "common/completion_evidence.rs"]
mod completion_evidence;
#[path = "common/owned_compound_family.rs"]
mod fixture;
use archsig::{
    canonical::Json,
    observed::{
        control::{Control, Limits, Usage},
        evaluate_observed_bytes,
    },
};
use std::collections::{BTreeMap, BTreeSet};
fn quiet() -> Control {
    Control::new(Limits::default(), |_| Usage::default())
}
fn obj(j: &Json) -> &BTreeMap<String, Json> {
    let Json::Obj(x) = j else { panic!("object") };
    x
}
fn arr(j: &Json) -> &[Json] {
    let Json::Arr(x) = j else { panic!("array") };
    x
}
fn get<'a>(j: &'a Json, k: &str) -> &'a Json {
    &obj(j)[k]
}
fn node<'a>(w: &'a Json, r: &Json) -> &'a Json {
    arr(get(w, "nodes"))
        .iter()
        .find(|n| get(n, "id") == get(r, "node"))
        .unwrap()
}
fn answers(w: &Json) -> &[Json] {
    arr(get(w, "answers"))
}
fn domains<'a>(w: &'a Json, ty: &Json) -> Vec<&'a Json> {
    arr(get(w, "nodes"))
        .iter()
        .filter(|n| {
            get(n, "type") == &Json::str("Domain")
                && obj(n)
                    .get("value")
                    .is_some_and(|v| obj(v).get("type") == Some(ty))
        })
        .collect()
}
fn state_ty() -> Json {
    Json::Arr(vec![Json::str("Ref"), Json::str("Reservations.State")])
}
fn map_ty() -> Json {
    Json::Arr(vec![Json::str("Map"), state_ty(), state_ty()])
}
fn run(ask: &str) -> archsig::observed::ObservedEvaluation {
    let outcome = evaluate_observed_bytes(fixture::input(false, false, "r1"), &[ask], &mut quiet());
    match outcome {
        Ok(r) => r,
        Err(e) => panic!("evaluation failed: {:?}", e.wire()),
    }
}
#[test]
fn owned_compound_fixed_map_parameters_have_all_four_functions_and_original_rows() {
    let r = run("c=check(Reservations.maps,a=@v/A,b=@v/B)");
    assert_eq!(r.status(), "complete");
    let w = r.wire();
    assert_eq!(get(&answers(&w)[0], "status"), &Json::str("established"));
    let ds = domains(&w, &map_ty());
    assert_eq!(ds.len(), 2); // parameter fiber and whole one-free-parameter product
    for d in ds {
        assert_eq!(arr(get(get(d, "value"), "elements")).len(), 4);
    }
    let rows: Vec<_> = arr(get(&w, "nodes"))
        .iter()
        .filter(|n| get(n, "type") == &Json::str("LawInstance"))
        .collect();
    let concrete: Vec<_> = rows
        .iter()
        .filter(|n| arr(get(get(n, "value"), "bindings")).len() == 3)
        .collect();
    assert_eq!(concrete.len(), 4);
    let mut tables = BTreeSet::new();
    for row in concrete {
        let bs = arr(get(get(row, "value"), "bindings"));
        let m = node(&w, get(&bs[2], "value"));
        assert_eq!(get(m, "type"), &map_ty());
        let pairs = arr(get(m, "value"));
        assert_eq!(pairs.len(), 2);
        assert_eq!(
            pairs
                .iter()
                .map(|p| arr(p)[0].canonical())
                .collect::<BTreeSet<_>>(),
            [
                Json::Arr(vec![Json::str("v"), Json::str("p")]).canonical(),
                Json::Arr(vec![Json::str("v"), Json::str("q")]).canonical()
            ]
            .into_iter()
            .collect()
        );
        assert!(pairs.iter().all(|p| {
            [
                Json::Arr(vec![Json::str("v"), Json::str("r")]),
                Json::Arr(vec![Json::str("v"), Json::str("s")]),
            ]
            .contains(&arr(p)[1])
        }));
        assert!(tables.insert(get(m, "value").canonical()));
    }
    assert_eq!(tables.len(), 4);
    audit(&r);
}

fn text(j: &Json) -> &str {
    let Json::Str(s) = j else { panic!("string") };
    s
}
fn refs(j: &Json, rs: &mut Vec<String>) {
    match j {
        Json::Obj(m) if m.len() == 1 && m.contains_key("node") => rs.push(text(&m["node"]).into()),
        Json::Obj(m) => {
            for v in m.values() {
                refs(v, rs);
            }
        }
        Json::Arr(a) => {
            for v in a {
                refs(v, rs);
            }
        }
        _ => {}
    }
}
fn audit(result: &archsig::observed::ObservedEvaluation) {
    let w = result.wire();
    let mut seen = BTreeSet::new();
    let checked = result.prepared().inputs();
    for n in arr(get(&w, "nodes")) {
        let mut rs = vec![];
        refs(n, &mut rs);
        assert!(rs.iter().all(|r| seen.contains(r)));
        assert!(seen.insert(text(get(n, "id")).to_string()));
        if get(n, "type") != &Json::str("Proposition") {
            assert!(!obj(n).contains_key("judgment"));
        }
        if let Some(v) = obj(n).get("value") {
            let mut rs = vec![];
            refs(v, &mut rs);
            for r in rs {
                let target = arr(get(&w, "nodes"))
                    .iter()
                    .find(|n| get(n, "id") == &Json::str(r.clone()))
                    .unwrap();
                assert_eq!(get(target, "state"), &Json::str("value"));
                assert!(!obj(target).contains_key("partial"));
            }
        }
        for fact in arr(get(n, "support")) {
            let subject = checked
                .archmap()
                .snapshots
                .iter()
                .find(|s| s.id == text(get(fact, "snapshot")))
                .unwrap()
                .subjects
                .iter()
                .find(|s| s.id == text(get(fact, "subject")))
                .unwrap();
            let origin = if let Some(field) = obj(fact).get("field") {
                let f = subject
                    .fields
                    .iter()
                    .find(|f| f.name == text(field))
                    .unwrap();
                let archsig::archmap::Slot::Known { atom, origin, .. } = &f.slot else {
                    panic!("support is known")
                };
                assert_eq!(get(fact, "atom"), &Json::str(atom));
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
            for loc in &origin.locations {
                assert!(checked.archmap().sources.iter().any(|s| s.id == loc.source));
            }
        }
        if get(n, "type") == &Json::str("Domain")
            && obj(n)
                .get("value")
                .is_some_and(|v| obj(v).get("kind") == Some(&Json::str("finite")))
        {
            let payload = get(n, "value");
            for member in arr(get(payload, "elements")) {
                let target = node(&w, member);
                assert_eq!(get(target, "type"), get(payload, "type"));
                assert_eq!(get(target, "state"), &Json::str("value"));
            }
        }
        if get(n, "type") == &Json::str("Evidence")
            && obj(n)
                .get("value")
                .is_some_and(|v| obj(v).get("kind") == Some(&Json::str("finite_exhaustion")))
        {
            let data = get(get(n, "value"), "data");
            let instances = arr(get(data, "instances"));
            assert_eq!(get(data, "checked"), &Json::Nat(instances.len() as u64));
            for r in instances {
                assert_eq!(get(node(&w, r), "type"), &Json::str("Evaluation"));
            }
        }
    }
    for a in arr(get(&w, "answers")) {
        if let Some(claim) = obj(a).get("claim") {
            let claim = node(&w, claim);
            assert_eq!(get(claim, "type"), &Json::str("Proposition"));
            assert_eq!(get(get(claim, "judgment"), "status"), get(a, "status"));
        }
    }
}

fn concrete_rows(w: &Json) -> Vec<&Json> {
    arr(get(w, "nodes"))
        .iter()
        .filter(|n| {
            get(n, "type") == &Json::str("LawInstance")
                && arr(get(get(n, "value"), "bindings"))
                    .iter()
                    .any(|b| get(b, "name") == &Json::str("f"))
        })
        .collect()
}
fn row_bindings(w: &Json, row: &Json) -> BTreeMap<String, Json> {
    arr(get(get(row, "value"), "bindings"))
        .iter()
        .map(|b| {
            (
                text(get(b, "name")).into(),
                get(node(w, get(b, "value")), "value").clone(),
            )
        })
        .collect()
}
fn owner_members(owner: &Json) -> Vec<Json> {
    let a = arr(owner);
    let ids = match text(&a[1]) {
        "A" => vec!["p", "q"],
        "B" => vec!["r", "s"],
        "Z" => vec![],
        _ => panic!("owner"),
    };
    ids.into_iter()
        .map(|s| Json::Arr(vec![a[0].clone(), Json::str(s)]))
        .collect()
}
fn oracle_map(a: &Json, b: &Json) -> BTreeSet<String> {
    let keys = owner_members(a);
    let images = owner_members(b);
    let mut tables = vec![vec![]];
    for key in keys {
        let mut next = vec![];
        for table in tables {
            for image in &images {
                let mut row = table.clone();
                row.push(Json::Arr(vec![key.clone(), image.clone()]));
                next.push(row);
            }
        }
        tables = next;
    }
    tables
        .into_iter()
        .map(|r| Json::Arr(r).canonical())
        .collect()
}
#[test]
fn owned_compound_free_owner_map_rows_keep_every_prefix_and_false_law_domain() {
    let mut by_status = vec![];
    for (name, status) in [("maps", "established"), ("impossible", "refuted")] {
        let r = run(&format!("c=check(Reservations.{name})"));
        assert_eq!(r.status(), "complete");
        let w = r.wire();
        assert_eq!(get(&answers(&w)[0], "status"), &Json::str(status));
        let rows = concrete_rows(&w);
        assert_eq!(rows.len(), 19);
        let mut groups = BTreeMap::<String, BTreeSet<String>>::new();
        for row in rows {
            let bs = row_bindings(&w, row);
            let key = format!("{}:{}", bs["a"].canonical(), bs["b"].canonical());
            assert!(groups.entry(key).or_default().insert(bs["f"].canonical()));
        }
        for a in ["A", "B", "Z"] {
            for b in ["A", "B", "Z"] {
                let av = Json::Arr(vec![Json::str("v"), Json::str(a)]);
                let bv = Json::Arr(vec![Json::str("v"), Json::str(b)]);
                let key = format!("{}:{}", av.canonical(), bv.canonical());
                assert_eq!(
                    groups.get(&key).cloned().unwrap_or_default(),
                    oracle_map(&av, &bv)
                );
            }
        }
        audit(&r);
        by_status.push(groups);
    }
    assert_eq!(by_status[0], by_status[1]);
}
#[test]
fn owned_compound_optional_tuple_set_rows_keep_concrete_members_and_empty_fibers() {
    for (name, total) in [("option_values", 7), ("tupled", 4), ("subset", 9)] {
        let r = run(&format!("c=check(Reservations.{name})"));
        assert_eq!(r.status(), "complete");
        let w = r.wire();
        let rows = concrete_rows(&w);
        assert_eq!(rows.len(), total);
        let mut actual = BTreeMap::<String, BTreeSet<String>>::new();
        for row in rows {
            let bs = row_bindings(&w, row);
            assert!(
                actual
                    .entry(bs["a"].canonical())
                    .or_default()
                    .insert(bs["f"].canonical())
            );
        }
        for a in ["A", "B", "Z"] {
            let av = Json::Arr(vec![Json::str("v"), Json::str(a)]);
            let members = owner_members(&av);
            let expected: BTreeSet<_> = match name {
                "option_values" => std::iter::once(Json::obj([("none", Json::Bool(true))]))
                    .chain(members.into_iter().map(|v| Json::obj([("some", v)])))
                    .map(|v| v.canonical())
                    .collect(),
                "tupled" => members
                    .into_iter()
                    .map(|v| Json::Arr(vec![Json::Arr(vec![]), v]).canonical())
                    .collect(),
                _ => {
                    let mut subsets = vec![vec![]];
                    for v in members {
                        let more: Vec<_> = subsets
                            .iter()
                            .map(|s| {
                                let mut s = s.clone();
                                s.push(v.clone());
                                s
                            })
                            .collect();
                        subsets.extend(more);
                    }
                    subsets
                        .into_iter()
                        .map(|s| Json::Arr(s).canonical())
                        .collect()
                }
            };
            assert_eq!(
                actual.get(&av.canonical()).cloned().unwrap_or_default(),
                expected
            );
        }
        audit(&r);
    }
}
#[test]
fn owned_compound_map_wrappers_keep_all_elements_and_empty_map_boundaries() {
    for (name, a, b, count) in [
        ("map_option", "A", "B", 5),
        ("map_tuple", "A", "B", 4),
        ("map_set", "A", "B", 16),
        ("maps", "Z", "A", 1),
        ("maps", "A", "Z", 0),
        ("map_option", "A", "Z", 1),
        ("map_set", "A", "Z", 1),
        ("map_tuple", "A", "Z", 0),
    ] {
        let r = run(&format!("c=check(Reservations.{name},a=@v/{a},b=@v/{b})"));
        assert_eq!(r.status(), "complete");
        let w = r.wire();
        assert_eq!(get(&answers(&w)[0], "status"), &Json::str("established"));
        let rows = concrete_rows(&w);
        assert_eq!(rows.len(), count);
        let mut signatures = BTreeSet::new();
        let av = Json::Arr(vec![Json::str("v"), Json::str(a)]);
        let bv = Json::Arr(vec![Json::str("v"), Json::str(b)]);
        let maps = oracle_map(&av, &bv);
        for row in rows {
            let bs = row_bindings(&w, row);
            let v = &bs["f"];
            assert!(signatures.insert(v.canonical()));
            let actual: Vec<&Json> = match name {
                "map_option" => {
                    if obj(v).contains_key("none") {
                        vec![]
                    } else {
                        vec![get(v, "some")]
                    }
                }
                "map_tuple" => vec![&arr(v)[1]],
                "map_set" => arr(v).iter().collect(),
                _ => vec![v],
            };
            for m in actual {
                assert!(maps.contains(&m.canonical()));
            }
        }
        assert_eq!(signatures.len(), count);
        audit(&r);
    }
}
#[test]
fn owned_compound_cross_snapshot_prefix_keeps_missing_fields_and_original_inputs() {
    let input = fixture::input(false, true, "r1");
    let checked = archsig::observed::input::check_inputs(input.clone(), &mut quiet()).unwrap();
    let before = format!("{:?}", checked.archmap());
    let r = evaluate_observed_bytes(
        input,
        &["c=check(Reservations.maps,a=@w/A,b=@v/B)"],
        &mut quiet(),
    )
    .unwrap();
    assert_eq!(r.status(), "complete");
    let w = r.wire();
    let rows = concrete_rows(&w);
    assert_eq!(rows.len(), 4);
    let av = Json::Arr(vec![Json::str("w"), Json::str("A")]);
    let bv = Json::Arr(vec![Json::str("v"), Json::str("B")]);
    assert_eq!(
        rows.into_iter()
            .map(|row| row_bindings(&w, row)["f"].canonical())
            .collect::<BTreeSet<_>>(),
        oracle_map(&av, &bv)
    );
    assert_eq!(format!("{:?}", r.prepared().inputs().archmap()), before);
    assert_eq!(
        format!("{:?}", r.prepared().inputs().sources()),
        format!("{:?}", checked.sources())
    );
    assert_eq!(
        format!("{:?}", r.prepared().inputs().law()),
        format!("{:?}", checked.law())
    );
    assert_eq!(
        format!("{:?}", r.prepared().inputs().definitions()),
        format!("{:?}", checked.definitions())
    );
    assert!(
        checked
            .archmap()
            .snapshots
            .iter()
            .flat_map(|s| &s.subjects)
            .filter(|s| s.ty == "Reservations.State")
            .all(|s| s
                .fields
                .iter()
                .filter(|f| f.name.ends_with(".free"))
                .all(|f| matches!(f.slot, archsig::archmap::Slot::Missing)))
    );
    audit(&r);
}
#[test]
fn owned_compound_unknown_membership_completes_each_consistent_fiber() {
    for name in ["maps", "map_option", "map_set", "option_values", "subset"] {
        let ask = if name == "option_values" || name == "subset" {
            format!("c=check(Reservations.{name},a=@v/A)")
        } else {
            format!("c=check(Reservations.{name},a=@v/A,b=@v/B)")
        };
        let input = fixture::input(true, false, "r1");
        let original = input.clone();
        let r = evaluate_observed_bytes(input, &[&ask], &mut quiet()).unwrap();
        assert_eq!(r.status(), "complete");
        assert_eq!(r.prepared().inputs().sources(), &original);
        completion_evidence::original_owner_is_missing(&r, "v");
        let w = r.wire();
        let (domain, cases) = completion_evidence::established_cases(&w, "c", 3);
        let owners: BTreeSet<_> = arr(get(get(domain, "value"), "elements"))
            .iter()
            .map(|r| get(node(&w, r), "value").canonical())
            .collect();
        assert_eq!(
            owners,
            ["A", "B", "Z"]
                .map(|id| Json::Arr(vec![Json::str("v"), Json::str(id)]).canonical())
                .into()
        );
        for (member, evaluation) in arr(get(get(domain, "value"), "elements")).iter().zip(cases) {
            let owner = text(&arr(get(node(&w, member), "value"))[1]);
            let parts = arr(get(get(evaluation, "value"), "parts"));
            assert_eq!(parts.len(), 1);
            let mut actual = BTreeSet::new();
            for child in arr(get(&parts[0], "children")) {
                let bindings = arr(get(get(node(&w, child), "value"), "bindings"));
                let value = get(
                    bindings
                        .iter()
                        .find(|b| get(b, "name") == &Json::str("f"))
                        .unwrap(),
                    "value",
                );
                assert!(actual.insert(fiber_value_key(name, get(node(&w, value), "value"))));
            }
            assert_eq!(actual, unknown_fiber_values(name, owner));
        }
        assert!(
            answers(&w)[0]
                .canonical()
                .contains("Reservations.State.owner")
        );
        assert!(answers(&w)[0].canonical().contains("all_completions"));
        // 各owner補完の実fiberを列挙した総数。全称のtrueを先に集約しない。
        let count = match name {
            "maps" => 9,
            "map_option" => 12,
            "map_set" => 28,
            "option_values" => 7,
            "subset" => 8,
            _ => unreachable!(),
        };
        assert_eq!(concrete_rows(&w).len(), count);
        audit(&r);
    }
}

fn unknown_fiber_values(name: &str, owner: &str) -> BTreeSet<String> {
    let subject = |id: &str| Json::Arr(vec![Json::str("v"), Json::str(id)]);
    let tables: Vec<Vec<(&str, &str)>> = match owner {
        "A" => vec![
            vec![("p", "r"), ("q", "r")],
            vec![("p", "r"), ("q", "s")],
            vec![("p", "s"), ("q", "r")],
            vec![("p", "s"), ("q", "s")],
        ],
        "B" => vec![vec![("q", "p")], vec![("q", "r")], vec![("q", "s")]],
        "Z" => vec![vec![("q", "r")], vec![("q", "s")]],
        _ => panic!("owner"),
    };
    let maps: Vec<_> = tables
        .into_iter()
        .map(|pairs| {
            Json::Arr(
                pairs
                    .into_iter()
                    .map(|(a, b)| Json::Arr(vec![subject(a), subject(b)]))
                    .collect(),
            )
        })
        .collect();
    let values = match name {
        "maps" => maps,
        "map_option" => std::iter::once(Json::obj([("none", Json::Bool(true))]))
            .chain(maps.into_iter().map(|m| Json::obj([("some", m)])))
            .collect(),
        "map_set" => subsets(maps),
        "option_values" => std::iter::once(Json::obj([("none", Json::Bool(true))]))
            .chain(
                (if owner == "A" {
                    vec![subject("p"), subject("q")]
                } else {
                    vec![subject("q")]
                })
                .into_iter()
                .map(|s| Json::obj([("some", s)])),
            )
            .collect(),
        "subset" => subsets(if owner == "A" {
            vec![subject("p"), subject("q")]
        } else {
            vec![subject("q")]
        }),
        _ => unreachable!(),
    };
    values
        .iter()
        .map(|value| fiber_value_key(name, value))
        .collect()
}

fn fiber_value_key(name: &str, value: &Json) -> String {
    // Mapの行順とSetの要素順は数学的な候補の区別に使わない。
    let map = |value: &Json| {
        let mut rows = arr(value).to_vec();
        rows.sort_by_key(Json::canonical);
        Json::Arr(rows)
    };
    let normalized = match name {
        "maps" => map(value),
        "map_option" if obj(value).contains_key("some") => {
            Json::obj([("some", map(get(value, "some")))])
        }
        "map_set" | "subset" => {
            let mut items: Vec<_> = arr(value)
                .iter()
                .map(|item| {
                    if name == "map_set" {
                        map(item)
                    } else {
                        item.clone()
                    }
                })
                .collect();
            items.sort_by_key(Json::canonical);
            Json::Arr(items)
        }
        _ => value.clone(),
    };
    normalized.canonical()
}

fn subsets(values: Vec<Json>) -> Vec<Json> {
    let mut subsets = vec![vec![]];
    for value in values {
        let more: Vec<_> = subsets
            .iter()
            .map(|subset| {
                let mut next = subset.clone();
                next.push(value.clone());
                next
            })
            .collect();
        subsets.extend(more);
    }
    subsets.into_iter().map(Json::Arr).collect()
}
#[test]
fn owned_compound_provenance_changes_keep_answers_and_current_sources() {
    let a = evaluate_observed_bytes(
        fixture::input(false, false, "r1"),
        &["c=check(Reservations.maps,a=@v/A,b=@v/B)"],
        &mut quiet(),
    )
    .unwrap();
    let b = evaluate_observed_bytes(
        fixture::input(false, false, "r2"),
        &["c=check(Reservations.maps,a=@v/A,b=@v/B)"],
        &mut quiet(),
    )
    .unwrap();
    assert_eq!(get(&a.wire(), "answers"), get(&b.wire(), "answers"));
    assert_ne!(
        a.prepared().inputs().sources().archmap().bytes(),
        b.prepared().inputs().sources().archmap().bytes()
    );
    for (r, rev) in [(&a, "r1"), (&b, "r2")] {
        assert_eq!(r.prepared().inputs().archmap().sources[0].revision, rev);
        audit(r);
    }
}
