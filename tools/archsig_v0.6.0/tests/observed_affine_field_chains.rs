#[allow(dead_code)]
#[path = "common/affine_field_chains.rs"]
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
fn f<'a>(j: &'a Json, k: &str) -> &'a Json {
    let Json::Obj(xs) = j else { panic!("object") };
    xs.get(k)
        .unwrap_or_else(|| panic!("key {k}; keys={:?}", xs.keys().collect::<Vec<_>>()))
}
fn arr(j: &Json) -> &[Json] {
    let Json::Arr(xs) = j else { panic!("array") };
    xs
}
fn text(j: &Json) -> &str {
    let Json::Str(s) = j else { panic!("string") };
    s
}
fn node<'a>(w: &'a Json, r: &Json) -> &'a Json {
    arr(f(w, "nodes"))
        .iter()
        .find(|n| f(n, "id") == f(r, "node"))
        .unwrap()
}
fn answer<'a>(w: &'a Json, id: &str) -> &'a Json {
    arr(f(w, "answers"))
        .iter()
        .find(|n| f(n, "id") == &Json::str(id))
        .unwrap()
}
fn run(input: InputSources, asks: &[&str], status: &str) -> Json {
    let result = evaluate_observed_bytes(input.clone(), asks, &mut quiet()).unwrap();
    let wire = result.wire();
    assert_eq!(result.status(), status, "{:?}", f(&wire, "issues"));
    assert_eq!(result.prepared().inputs().sources(), &input);
    let mut earlier = std::collections::BTreeSet::new();
    fn refs(j: &Json, ids: &mut Vec<String>) {
        match j {
            Json::Obj(xs) if xs.len() == 1 && xs.contains_key("node") => {
                ids.push(text(&xs["node"]).into())
            }
            Json::Obj(xs) => {
                for x in xs.values() {
                    refs(x, ids)
                }
            }
            Json::Arr(xs) => {
                for x in xs {
                    refs(x, ids)
                }
            }
            _ => {}
        }
    }
    for n in arr(f(&wire, "nodes")) {
        let mut ids = vec![];
        refs(n, &mut ids);
        assert!(ids.iter().all(|id| earlier.contains(id)));
        assert!(earlier.insert(text(f(n, "id")).to_owned()));
    }
    wire
}
fn check(w: &Json, id: &str, status: &str) {
    let a = answer(w, id);
    assert_eq!(f(a, "status"), &Json::str(status));
    let c = node(w, f(a, "claim"));
    assert_eq!(f(c, "type"), &Json::str("Proposition"));
    assert_eq!(f(f(c, "judgment"), "status"), f(a, "status"));
    assert_eq!(f(f(c, "judgment"), "evidence"), f(a, "evidence"));
    assert!(!arr(f(a, "evidence")).is_empty());
}
fn prefixes(w: &Json, law: &[u8], number: &str) {
    let expected = [("n", "Ref"), ("n.link", "Ref"), ("n.link.mark", number)];
    for (token, kind) in expected {
        let evaluations: Vec<_> = arr(f(w, "nodes"))
            .iter()
            .filter(|n| f(n, "type") == &Json::str("Evaluation"))
            .filter(|n| {
                let e = node(w, f(f(n, "value"), "expression"));
                let Json::Obj(value) = f(e, "value") else {
                    return false;
                };
                let Some(location) = value.get("location") else {
                    return false;
                };
                let span = arr(f(location, "span"));
                let (Json::Nat(a), Json::Nat(b)) = (&span[0], &span[1]) else {
                    panic!()
                };
                &law[*a as usize..*b as usize] == token.as_bytes()
            })
            .collect();
        assert!(!evaluations.is_empty(), "{token}");
        for e in evaluations {
            let value = f(e, "value");
            let scalar = node(w, f(value, "value"));
            let ty = f(scalar, "type");
            if kind == "Ref" {
                assert_eq!(arr(ty)[0], Json::str("Ref"));
            } else {
                assert_eq!(ty, &Json::str(kind));
            }
            if token != "n" {
                let children = arr(f(&arr(f(value, "parts"))[0], "children"));
                assert_eq!(children.len(), 1);
                let child = node(w, &children[0]);
                let before = node(w, f(f(child, "value"), "expression"));
                let span = arr(f(f(f(before, "value"), "location"), "span"));
                let (Json::Nat(a), Json::Nat(b)) = (&span[0], &span[1]) else {
                    panic!()
                };
                let owner = if token == "n.link" { "n" } else { "n.link" };
                assert_eq!(&law[*a as usize..*b as usize], owner.as_bytes());
            }
        }
    }
}
#[test]
fn all_integer_assignments_keep_known_multifield_chain_in_original_affine_law() {
    let input = fixture::input(
        "law required chain(n:Node,z:Z):n.link.mark+z=z+n.link.mark;",
        "Z",
        &[],
        "r1",
    );
    let w = run(input.clone(), &["a=check(Walk.chain,n=@v/p)"], "complete");
    check(&w, "a", "established");
    prefixes(&w, input.law().bytes(), "Z");
    let e = node(&w, f(f(answer(&w, "a"), "outputs"), "evaluation"));
    let q = &arr(f(f(e, "scope"), "quantifiers"))[0];
    assert_eq!(f(q, "name"), &Json::str("z"));
    assert_eq!(f(q, "type"), &Json::str("Z"));
    let domain = node(&w, f(q, "domain"));
    assert_eq!(f(f(domain, "value"), "kind"), &Json::str("type"));
}
#[test]
fn rational_chain_and_counterexample_keep_exact_field_and_original_prefixes() {
    let script = "law required chain(n:Node,z:Q):n.link.mark+z=z+n.link.mark; law required wrong(n:Node,z:Q):n.link.mark+z=z+n.link.mark+1;";
    let input = fixture::input(script, "Q", &[], "r1");
    let w = run(
        input.clone(),
        &["a=check(Walk.chain,n=@v/p)", "bad=check(Walk.wrong,n=@v/p)"],
        "complete",
    );
    check(&w, "a", "established");
    check(&w, "bad", "refuted");
    prefixes(&w, input.law().bytes(), "Q");
    assert!(
        arr(f(&w, "nodes"))
            .iter()
            .any(|n| f(n, "type") == &Json::str("Q")
                && f(n, "value") == &Json::Arr(vec![Json::str("2"), Json::str("3")]))
    );
}
#[test]
fn lexical_pattern_and_named_calls_preserve_multifield_producers_in_all_assignments() {
    for script in [
        "law required chain(n:Node,z:Z):let alias=n in alias.link.mark+z=z+alias.link.mark;",
        "law required chain(n:Node,z:Z):match n { alias => alias.link.mark+z=z+alias.link.mark; };",
        "view amount(n:Node,z:Z):Z=n.link.mark+z; view middle(n:Node,z:Z):Z=amount(n,z); law required chain(n:Node,z:Z):middle(n,z)=z+n.link.mark;",
    ] {
        let w = run(
            fixture::input(script, "Z", &[], "r1"),
            &["a=check(Walk.chain,n=@v/p)"],
            "complete",
        );
        check(&w, "a", "established");
    }
}
#[test]
fn missing_chained_slots_share_symbols_without_correlating_distinct_subjects() {
    let script = "law required stable(n:Node,z:Z):z+n.link.mark-n.link.mark=z; law required wrong(n:Node,z:Z):z+n.link.mark-n.link.mark=z+1; law required apart(n:Node,m:Node,z:Z):z+n.link.mark-m.link.mark=z;";
    let w = run(
        fixture::input(script, "Z", &["p-mark", "q-mark"], "r1"),
        &[
            "same=check(Walk.stable,n=@v/p)",
            "bad=check(Walk.wrong,n=@v/p)",
            "apart=check(Walk.apart,n=@v/p,m=@v/q)",
        ],
        "partial",
    );
    check(&w, "same", "established");
    check(&w, "bad", "refuted");
    assert_eq!(f(answer(&w, "apart"), "status"), &Json::str("undetermined"));
    let reasons = arr(f(answer(&w, "apart"), "reasons"));
    for subject in ["p", "q"] {
        assert!(reasons.iter().any(|r| {
            f(r, "code") == &Json::str("missing_observation")
                && arr(f(r, "missing")).iter().any(|m| {
                    f(m, "snapshot") == &Json::str("v")
                        && f(m, "subject") == &Json::str(subject)
                        && f(m, "field") == &Json::str("Paths.Node.mark")
                })
        }));
    }
}
#[test]
fn explicit_quantified_chain_and_current_provenance_preserve_mathematical_answers() {
    let asks = ["a=evaluate(Walk.current,n=@v/p)"];
    let mut rows = vec![];
    for revision in ["r1", "r2"] {
        let w = run(
            fixture::input(fixture::SCRIPT, "Z", &[], revision),
            &asks,
            "complete",
        );
        assert_eq!(f(answer(&w, "a"), "status"), &Json::str("established"));
        assert_eq!(
            f(node(&w, f(f(answer(&w, "a"), "outputs"), "value")), "value"),
            &Json::Bool(true)
        );
        let inputs = fixture::input(fixture::SCRIPT, "Z", &[], revision);
        let checked = archsig::observed::input::check_inputs(inputs, &mut quiet()).unwrap();
        let map = checked.archmap();
        let subject = map
            .snapshots
            .iter()
            .find(|s| s.id == "v")
            .unwrap()
            .subjects
            .iter()
            .find(|s| s.id == "p")
            .unwrap();
        for field in ["Paths.Node.link", "Paths.Node.mark"] {
            let fact=arr(f(&w,"nodes")).iter().flat_map(|n|arr(f(n,"support"))).find(|fact|matches!(fact,Json::Obj(fs)if fs.get("field")==Some(&Json::str(field))&&fs.get("snapshot")==Some(&Json::str("v"))&&fs.get("subject")==Some(&Json::str("p")))).unwrap();
            let field = subject.fields.iter().find(|f| f.name == field).unwrap();
            let archsig::archmap::Slot::Known { atom, origin, .. } = &field.slot else {
                panic!()
            };
            assert_eq!(f(fact, "atom"), &Json::str(atom));
            let origin = map.origins.iter().find(|o| &o.id == origin).unwrap();
            for location in &origin.locations {
                let source = map
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
        rows.push(w);
    }
    assert_ne!(f(&rows[0], "inputs"), f(&rows[1], "inputs"));
    assert_eq!(f(&rows[0], "answers"), f(&rows[1], "answers"));
    assert_eq!(f(&rows[0], "nodes"), f(&rows[1], "nodes"));
}
#[test]
fn finite_reference_completions_preserve_unknown_chain_and_independent_results() {
    let script = format!(
        "{} view vary(n:Node):Z=n.link.mark; view plus(z:Z):Z=z+1;",
        fixture::SCRIPT
    );
    let w = run(
        fixture::input(&script, "Z", &["p-link"], "r1"),
        &[
            "seed=evaluate(Walk.seed)",
            "prior=check(Walk.prior)",
            "vary=evaluate(Walk.vary,n=@v/p)",
            "stable=check(Walk.chain,n=@v/p)",
            "later=evaluate(Walk.plus,z=$vary.value)",
        ],
        "partial",
    );
    check(&w, "prior", "refuted");
    check(&w, "stable", "established");
    assert_eq!(
        f(
            node(&w, f(f(answer(&w, "seed"), "outputs"), "value")),
            "value"
        ),
        &Json::str("1")
    );
    for id in ["vary", "later"] {
        let a = answer(&w, id);
        assert_eq!(f(a, "status"), &Json::str("undetermined"));
        let Json::Obj(outputs) = f(a, "outputs") else {
            panic!()
        };
        assert!(!outputs.contains_key("value"));
        if id == "later" {
            assert!(outputs.is_empty())
        } else {
            assert!(outputs.contains_key("evaluation"));
        }
        assert!(arr(f(a, "reasons")).iter().any(|r| {
            f(r, "code") == &Json::str("missing_observation")
                && arr(f(r, "missing")).iter().any(|m| {
                    f(m, "snapshot") == &Json::str("v")
                        && f(m, "subject") == &Json::str("p")
                        && f(m, "field") == &Json::str("Paths.Node.link")
                })
        }));
    }
    assert!(
        arr(f(answer(&w, "later"), "reasons"))
            .iter()
            .any(|r| f(r, "code") == &Json::str("dependency_blocked"))
    );
    let expected: std::collections::BTreeSet<_> = [("v", "p"), ("v", "q"), ("v", "r"), ("w", "p")]
        .into_iter()
        .map(|(s, x)| Json::Arr(vec![Json::str(s), Json::str(x)]).canonical())
        .collect();
    let domains:Vec<_>=arr(f(&w,"nodes")).iter().filter(|n|f(n,"type")==&Json::str("Domain")).filter(|n|matches!(f(n,"value"),Json::Obj(v)if v.get("kind")==Some(&Json::str("finite"))&&v.get("type")==Some(&Json::Arr(vec![Json::str("Ref"),Json::str("Paths.Node")])))).collect();
    assert_eq!(domains.len(), 2);
    for domain in domains {
        let elements = arr(f(f(domain, "value"), "elements"));
        assert_eq!(elements.len(), 4);
        let actual: std::collections::BTreeSet<_> = elements
            .iter()
            .map(|r| f(node(&w, r), "value").canonical())
            .collect();
        assert_eq!(actual, expected);
    }
}
