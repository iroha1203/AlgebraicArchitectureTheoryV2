//! 部分Option/Setの所属を元三入力から計算する。
use crate::common::helpers::get;
use crate::common::owned_partial_containers as fixture;
use archsig::{
    canonical::Json, control::Control, input::InputSources, observed::evaluate_observed_bytes,
};
fn arr(j: &Json) -> &[Json] {
    let Json::Arr(a) = j else { panic!("array") };
    a
}
fn answer<'a>(w: &'a Json, id: &str) -> &'a Json {
    arr(get(w, "answers"))
        .iter()
        .find(|a| get(a, "id") == &Json::str(id))
        .unwrap()
}
fn node<'a>(w: &'a Json, r: &Json) -> &'a Json {
    arr(get(w, "nodes"))
        .iter()
        .find(|n| get(n, "id") == get(r, "node"))
        .unwrap()
}
fn run_input(i: InputSources, asks: &[&str]) -> archsig::observed::ObservedEvaluation {
    let original = i.clone();
    let r = evaluate_observed_bytes(i, asks, &Control::unlimited())
        .unwrap_or_else(|e| panic!("{:?}", e.wire()));
    assert_ne!(r.status(), "error", "{:?}", get(&r.wire(), "issues"));
    assert_eq!(r.prepared().inputs().sources(), &original);
    r
}
fn run(asks: &[&str]) -> archsig::observed::ObservedEvaluation {
    run_input(fixture::input(false, "r1"), asks)
}
fn codes(a: &Json) -> Vec<&Json> {
    arr(get(a, "reasons"))
        .iter()
        .map(|r| get(r, "code"))
        .collect()
}
fn assert_failed(w: &Json, id: &str) {
    let a = answer(w, id);
    assert_eq!(get(a, "status"), &Json::str("undetermined"), "{id}");
    let Json::Obj(o) = get(a, "outputs") else {
        panic!()
    };
    assert!(!o.contains_key("value"));
    let reason = arr(get(a, "reasons"))
        .iter()
        .find(|r| get(r, "code") == &Json::str("condition_failed"))
        .expect(id);
    let c = node(w, get(get(reason, "details"), "condition"));
    assert_eq!(get(get(c, "judgment"), "status"), &Json::str("refuted"));
    assert!(!arr(get(c, "support")).is_empty());
}
fn assert_original_arrow_owner(r: &archsig::observed::ObservedEvaluation) {
    use archsig::{
        archmap::{Slot, Value},
        types::Type,
    };
    let snapshot = r
        .prepared()
        .inputs()
        .archmap()
        .snapshots()
        .iter()
        .find(|s| s.id == "v")
        .unwrap();
    let e = snapshot.subjects.iter().find(|s| s.id == "e").unwrap();
    let field = |name: &str| {
        e.fields
            .iter()
            .find(|f| f.name == format!("Reservations.Reserve.{name}"))
            .unwrap()
    };
    assert!(
        matches!(&field("owner").slot,Slot::Known{value:Value::Ref{snapshot,subject},..} if snapshot=="v" && subject=="A")
    );
    assert_eq!(
        field("to").ty,
        Type::Owned("Reservations.State".into(), "owner".into())
    );
    assert!(matches!(field("to").slot, Slot::Missing));
}
fn assert_completion_domain(w: &Json, id: &str, kind: &str, entity: &str, expected: &[&str]) {
    let evaluation = node(w, get(get(answer(w, id), "outputs"), "evaluation"));
    let domain = node(w, &arr(get(evaluation, "arguments"))[1]);
    assert_eq!(get(domain, "type"), &Json::str("Domain"));
    let payload = get(domain, "value");
    assert_eq!(get(payload, "kind"), &Json::str("finite"));
    assert_eq!(
        get(payload, "type"),
        &Json::Arr(vec![Json::str(kind), Json::str(entity)])
    );
    let actual: std::collections::BTreeSet<_> = arr(get(payload, "elements"))
        .iter()
        .map(|r| get(node(w, r), "value").canonical())
        .collect();
    let expected: std::collections::BTreeSet<_> = expected
        .iter()
        .map(|s| Json::Arr(vec![Json::str("v"), Json::str(*s)]).canonical())
        .collect();
    assert_eq!(actual, expected);
}
#[test]
fn partial_option_set_calls_keep_z_q_nested_members_and_return_boundaries() {
    // Option引数はnested(Option<List<Set<..>>>)が含み、返り値の境界はreturnsetが確かめる。
    let r = run(&[
        "collectionCase=check(Reservations.ocSetGood,a=@v/A,p=@v/p,q=@v/q)",
        "nested=check(Reservations.ocNestedGood,a=@v/A,b=@v/B,p=@v/p,q=@v/r)",
        "returnset=check(Reservations.ocReturnedSet,a=@v/A,p=@v/p)",
    ]);
    assert_eq!(r.status(), "complete");
    let w = r.wire();
    for a in arr(get(&w, "answers")) {
        assert_eq!(get(a, "status"), &Json::str("established"));
        assert!(codes(a).is_empty());
    }
    let law = r.prepared().inputs().law();
    let mut seen = std::collections::BTreeSet::new();
    for n in arr(get(&w, "nodes")) {
        if get(n, "type") != &Json::str("Evaluation") {
            continue;
        }
        let ev = get(n, "value");
        let src = get(node(&w, get(ev, "expression")), "value");
        let Json::Obj(sm) = src else { panic!() };
        let Some(location) = sm.get("location") else {
            continue;
        };
        let span = arr(get(location, "span"));
        let (Json::Nat(a), Json::Nat(b)) = (&span[0], &span[1]) else {
            panic!()
        };
        let id = law
            .exprs()
            .iter()
            .position(|e| e.span == (*a as usize, *b as usize))
            .unwrap();
        if matches!(
            law.expr_type(id),
            Some(archsig::types::Type::Set(_) | archsig::types::Type::Option(_))
        ) {
            let Json::Obj(m) = ev else { panic!() };
            assert!(!m.contains_key("value"));
            seen.insert(get(n, "id").canonical());
        }
    }
    assert!(seen.len() >= 3);
    let law = r.prepared().inputs().law();
    let declared_parameters: std::collections::BTreeSet<_> = law
        .infos()
        .iter()
        .flat_map(|info| &info.parameters)
        .map(|(name, ty)| (Json::str(name).canonical(), ty.erase().wire().canonical()))
        .collect();
    let mut axes = std::collections::BTreeSet::new();
    for n in arr(get(&w, "nodes")) {
        if get(n, "type") == &Json::str("Expression") {
            if let Json::Obj(v) = get(n, "value") {
                if let Some(Json::Arr(ps)) = v.get("parameters") {
                    for p in ps {
                        assert!(
                            declared_parameters.contains(&(
                                get(p, "name").canonical(),
                                get(p, "type").canonical()
                            )),
                            "parameter: {p:?}; declared: {declared_parameters:?}"
                        );
                        if [Json::str("Z"), Json::str("Q")].contains(get(p, "type")) {
                            axes.insert(get(p, "type").canonical());
                        }
                    }
                }
            }
        }
    }
    assert_eq!(
        axes,
        std::collections::BTreeSet::from([Json::str("Z").canonical(), Json::str("Q").canonical()])
    );

    for id in ["collectionCase", "nested", "returnset"] {
        let claim = node(&w, get(answer(&w, id), "claim"));
        assert!(
            arr(get(claim, "support"))
                .iter()
                .any(|f| matches!(f,Json::Obj(m) if m.get("atom")==Some(&Json::str("p-owner"))))
        );
        assert!(arr(get(get(claim, "scope"), "snapshots")).contains(&Json::str("v")));
    }
}
#[test]
fn partial_option_set_known_owner_and_snapshot_failures_keep_typed_conditions() {
    let r = run(&[
        "optionCase=check(Reservations.ocSomeGood,a=@v/B,p=@v/p)",
        "returnset=check(Reservations.ocReturnedSet,a=@v/B,p=@v/p)",
        "snapshot=check(Reservations.ocSomeGood,a=@v/A,p=@w/p)",
    ]);
    assert_eq!(r.status(), "partial");
    let w = r.wire();
    for id in ["optionCase", "returnset", "snapshot"] {
        assert_failed(&w, id);
        assert!(!codes(answer(&w, id)).contains(&&Json::str("unsupported_algorithm")));
    }
    let a = answer(&w, "optionCase");
    let reason = arr(get(a, "reasons"))
        .iter()
        .find(|r| get(r, "code") == &Json::str("condition_failed"))
        .unwrap();
    let c = node(&w, get(get(reason, "details"), "condition"));
    for (v, id) in arr(get(get(c, "value"), "operands")).iter().zip(["A", "B"]) {
        let n = node(&w, v);
        assert_eq!(
            get(n, "type"),
            &Json::Arr(vec![Json::str("Ref"), Json::str("Reservations.System")])
        );
        assert_eq!(
            get(n, "value"),
            &Json::Arr(vec![Json::str("v"), Json::str(id)])
        );
    }
}
#[test]
fn partial_option_set_numeric_missing_keeps_known_members_without_fake_set_cardinality() {
    // Tuple内の数値欠測は
    // observed_owned_partial_calls::partial_owned_numeric_missing_keeps_same_slot_correlation_and_known_members
    // が確かめるので、ここではSetの要素と件数で確かめる。
    let r = run(&[
        "collectionCase=evaluate(Reservations.ocMissingSet,a=@v/A,p=@v/p,q=@v/q)",
        "bad=evaluate(Reservations.ocMissingSet,a=@v/B,p=@v/p,q=@v/q)",
        "counted=evaluate(Reservations.ocCount,a=@v/A,p=@v/p,q=@v/q)",
        "empty=evaluate(Reservations.ocEmpty,a=@v/B)",
        "emptyvalues=evaluate(Reservations.ocEmptyValuesUse,a=@v/B)",
        "extensional=evaluate(Reservations.ocKnownSet,a=@v/A,p=@v/p)",
    ]);
    let w = r.wire();
    assert_eq!(r.status(), "partial");
    for id in ["collectionCase", "empty", "extensional"] {
        let a = answer(&w, id);
        assert_eq!(get(a, "status"), &Json::str("established"));
        assert_eq!(
            get(node(&w, get(get(a, "outputs"), "value")), "value"),
            &Json::Bool(true)
        );
    }
    for id in ["collectionCase", "counted"] {
        assert!(codes(answer(&w, id)).contains(&&Json::str("missing_observation")));
    }
    assert_failed(&w, "bad");
    let a = answer(&w, "counted");
    assert_eq!(get(a, "status"), &Json::str("undetermined"));
    let Json::Obj(o) = get(a, "outputs") else {
        panic!()
    };
    assert!(!o.contains_key("value"));
    assert!(codes(answer(&w, "empty")).is_empty());
    let a = answer(&w, "emptyvalues");
    assert_eq!(get(a, "status"), &Json::str("established"));
    assert_eq!(
        get(node(&w, get(get(a, "outputs"), "value")), "value"),
        &Json::Arr(vec![
            Json::obj([("none", Json::Bool(true))]),
            Json::Arr(vec![]),
            Json::str("0")
        ])
    );
    assert!(codes(a).is_empty());
}
#[test]
fn partial_option_set_pending_and_missing_members_keep_independent_known_mismatch() {
    let r = run_input(
        fixture::missing_reference_input(),
        &["bad=evaluate(Reservations.ocMixed,a=@v/B,e=@v/e,p=@v/p,q=@v/q)"],
    );
    assert_eq!(r.status(), "partial");
    assert_original_arrow_owner(&r);
    let w = r.wire();
    let a = answer(&w, "bad");
    assert_eq!(get(a, "status"), &Json::str("undetermined"));
    let cs = codes(a);
    assert!(cs.contains(&&Json::str("missing_observation")));
    // e.owner=A と to:State[owner] により、欠測toの全補完はp/q。
    // a=Bへのreadは両caseで失敗する(二つ)。三つ目は既知p.owner=Aの独立な失敗で、補完と混ざらずに残る。
    assert_completion_domain(&w, "bad", "Ref", "Reservations.State", &["p", "q"]);
    assert_eq!(
        cs.iter()
            .filter(|c| ***c == Json::str("condition_failed"))
            .count(),
        3
    );
    assert_failed(&w, "bad");
}
#[test]
fn partial_option_missing_reference_resolves_known_owner_and_quantified_unknown_owner() {
    let r = run_input(
        fixture::missing_reference_input(),
        &["x=evaluate(Reservations.ocUnknown,a=@v/A,e=@v/e,q=@v/q)"],
    );
    assert_eq!(r.status(), "complete");
    assert_original_arrow_owner(&r);
    let w = r.wire();
    let a = answer(&w, "x");
    assert_eq!(get(a, "status"), &Json::str("established"));
    assert_eq!(
        get(node(&w, get(get(a, "outputs"), "value")), "value"),
        &Json::Bool(true)
    );
    assert!(codes(a).contains(&&Json::str("missing_observation")));
    assert!(!codes(a).contains(&&Json::str("condition_failed")));
    assert_completion_domain(&w, "x", "Ref", "Reservations.State", &["p", "q"]);
    // ownerが欠測の同じ要求(ocSomeGood,a=A,p=p)は
    // observed_owned_universal_calls::unknown_owner_and_free_z_keep_membership_and_missing が確かめる。
}
