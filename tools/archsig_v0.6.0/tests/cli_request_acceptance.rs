use crate::common::cli;
use crate::common::quiet;
use crate::common::request_acceptance_data as fixture;
use archsig::{
    json::{JNode, JValue, parse},
    observed::{
        PrepareFailure, evaluate_observed_bytes, prepare_observed,
        request::{ArgumentOrigin, RequestDefault, RequestIssueCode, ResolveFailure},
    },
};
use cli::*;
use std::path::{Path, PathBuf};
fn internal(asks: &[&str]) -> JNode {
    let r = evaluate_observed_bytes(fixture::input(), asks, &quiet())
        .unwrap_or_else(|e| panic!("{:?}", e.wire()));
    parse(r.wire().canonical().as_bytes()).unwrap()
}
fn files(name: &str) -> PathBuf {
    let d = workdir(name);
    let i = fixture::input();
    std::fs::write(d.join("d.json"), i.definitions()[0].bytes()).unwrap();
    std::fs::write(d.join("l.law"), i.law().bytes()).unwrap();
    std::fs::write(d.join("a.json"), i.archmap().bytes()).unwrap();
    d
}
fn asks(d: &Path, texts: &[&str]) -> Run {
    let mut args = vec![
        "run",
        "--atom-definition",
        "d.json",
        "--law",
        "l.law",
        "--archmap",
        "a.json",
        "--out",
        "out",
    ];
    for t in texts {
        args.extend(["--ask", *t]);
    }
    run(d, &args)
}
fn answer<'a>(w: &'a JNode, id: &str) -> &'a JNode {
    arr(get(w, "answers"))
        .iter()
        .find(|a| s(get(a, "id")) == id)
        .unwrap()
}
fn node<'a>(w: &'a JNode, r: &JNode) -> &'a JNode {
    arr(get(w, "nodes"))
        .iter()
        .find(|n| s(get(n, "id")) == s(get(r, "node")))
        .unwrap()
}
fn value<'a>(w: &'a JNode, id: &str) -> &'a JNode {
    node(w, get(get(answer(w, id), "outputs"), "value"))
}
fn saved(d: &Path, r: &Run, code: i32) -> JNode {
    assert_eq!(r.code, code, "{}", r.stdout);
    let w = result_json(d, r);
    assert_eq!(num(get(&r.receipt, "exit_code")), code as u64);
    assert_eq!(num(get(&w, "exit_code")), code as u64);
    assert_eq!(s(get(&w, "status")), s(get(&r.receipt, "status")));
    w
}
fn no_artifacts(d: &Path) {
    let names: std::collections::BTreeSet<_> = std::fs::read_dir(d)
        .unwrap()
        .map(|entry| entry.unwrap().file_name())
        .collect();
    assert_eq!(
        names,
        ["a.json", "d.json", "l.law"]
            .into_iter()
            .map(std::ffi::OsString::from)
            .collect()
    );
    assert!(!d.join("out").exists());
}
fn ids(w: &JNode, key: &str) -> Vec<String> {
    arr(get(w, key))
        .iter()
        .map(|n| s(get(n, "id")).into())
        .collect()
}
#[test]
fn ready_priority_backward_references_and_answer_order_match_internal_and_cli() {
    let ts = [
        "take=evaluate(R.plus,x=$seed.value)",
        "second=evaluate(R.second)",
        "first=evaluate(R.first)",
        "seed=evaluate(R.seed)",
        "copy=evaluate(R.plus,x=$first.value)",
    ];
    let p = prepare_observed(fixture::input(), &ts, &quiet()).unwrap();
    assert_eq!(p.requests().evaluation_order(), &[1, 2, 3, 0, 4]);
    let d = files("request-order");
    let r = asks(&d, &ts);
    let w = saved(&d, &r, 0);
    for (_inspection, w) in [(true, internal(&ts)), (false, w)] {
        assert_eq!(s(get(&w, "status")), "complete");
        for key in ["requests", "answers"] {
            assert_eq!(ids(&w, key), ["take", "second", "first", "seed", "copy"]);
        }
        for (a, t) in arr(get(&w, "requests")).iter().zip(ts) {
            assert_eq!(s(get(a, "text")), t);
        }
        let mut positions = vec![];
        for (id, n) in [
            ("second", "20"),
            ("first", "10"),
            ("seed", "30"),
            ("take", "31"),
            ("copy", "11"),
        ] {
            assert_eq!(s(get(value(&w, id), "type")), "Z");
            assert_eq!(s(get(value(&w, id), "value")), n);
            positions.push(
                arr(get(&w, "nodes"))
                    .iter()
                    .position(|v| s(get(v, "id")) == s(get(value(&w, id), "id")))
                    .unwrap(),
            );
        }
        assert!(positions.windows(2).all(|p| p[0] < p[1]), "{positions:?}");
    }
    std::fs::remove_dir_all(d).unwrap();
}
#[test]
fn partial_binding_quantifies_every_remaining_root_and_keeps_explicit_and_defaulted_metadata() {
    let ts = [
        "partial=check(R.same,a=@v/A)",
        "full=check(R.same,a=@v/A,b=@v/A)",
    ];
    let p = prepare_observed(fixture::input(), &ts, &quiet()).unwrap();
    let rs = p.requests().requests();
    assert_eq!(rs[0].arguments.len(), 1);
    assert_eq!(rs[0].arguments[0].origin, ArgumentOrigin::Explicit);
    assert_eq!(
        rs[0].defaults,
        vec![
            RequestDefault::ObservedEnvironment,
            RequestDefault::UniversalParameters {
                declaration: "R.same".into(),
                parameters: vec!["b".into()]
            }
        ]
    );
    assert_eq!(rs[1].defaults, vec![RequestDefault::ObservedEnvironment]);
    let d = files("request-partial");
    let r = asks(&d, &ts);
    let w = saved(&d, &r, 1);
    for (inspection, w) in [(true, internal(&ts)), (false, w)] {
        assert_eq!(s(get(answer(&w, "partial"), "status")), "refuted");
        assert_eq!(s(get(answer(&w, "full"), "status")), "established");
        let req = &arr(get(&w, "requests"))[0];
        for (request, count) in arr(get(&w, "requests")).iter().zip([2, 1]) {
            let defaults = arr(get(request, "defaults"));
            assert_eq!(defaults.len(), count);
            assert_eq!(
                defaults
                    .iter()
                    .filter(|d| s(get(d, "rule")) == "observed_environment")
                    .count(),
                1
            );
        }
        assert_eq!(arr(get(req, "arguments")).len(), 1);
        assert_eq!(s(get(&arr(get(req, "arguments"))[0], "origin")), "explicit");
        let default = arr(get(req, "defaults"))
            .iter()
            .find(|d| s(get(d, "rule")) == "universal_parameters")
            .unwrap();
        assert_eq!(s(get(default, "declaration")), "R.same");
        assert_eq!(
            arr(get(default, "parameters"))
                .iter()
                .map(s)
                .collect::<Vec<_>>(),
            ["b"]
        );
        let e = if inspection {
            node(&w, get(get(answer(&w, "partial"), "outputs"), "evaluation"))
        } else {
            answer(&w, "partial")
        };
        let q = arr(get(get(e, "scope"), "quantifiers"))
            .iter()
            .find(|q| s(get(q, "name")) == "b")
            .unwrap();
        assert_eq!(s(get(q, "kind")), "forall");
        let domain = node(&w, get(q, "domain"));
        let elements = arr(get(get(domain, "value"), "elements"));
        assert_eq!(elements.len(), 2);
        let subjects: Vec<_> = elements
            .iter()
            .map(|r| {
                let v = arr(get(node(&w, r), "value"));
                assert_eq!(s(&v[0]), "v");
                s(&v[1])
            })
            .collect();
        assert_eq!(subjects, ["A", "B"]);
        if inspection {
            let rows = arr(get(&arr(get(get(e, "value"), "parts"))[0], "children"));
            assert_eq!(rows.len(), 2);
            let mut actual = vec![];
            for r in rows {
                let e = node(&w, r);
                let bindings = arr(get(get(e, "value"), "bindings"));
                let a = bindings.iter().find(|b| s(get(b, "name")) == "a").unwrap();
                assert_eq!(s(&arr(get(node(&w, get(a, "value")), "value"))[1]), "A");
                let b = bindings.iter().find(|b| s(get(b, "name")) == "b").unwrap();
                let subject = s(&arr(get(node(&w, get(b, "value")), "value"))[1]);
                let v = get(node(&w, get(get(e, "value"), "value")), "value");
                let JValue::Bool(holds) = v.value else {
                    panic!("Bool")
                };
                actual.push((subject, holds));
            }
            assert_eq!(actual, [("A", true), ("B", false)]);
        }

        assert!(
            !arr(get(
                answer(&w, "partial"),
                if inspection {
                    "evidence"
                } else {
                    "counterexamples"
                }
            ))
            .is_empty()
        );
    }
    std::fs::remove_dir_all(d).unwrap();
}
#[test]
fn static_duplicates_unknown_names_types_owners_indices_and_private_fields_are_usage() {
    use RequestIssueCode as C;
    let cases: Vec<(C, Vec<&str>)> = vec![
        (
            C::DuplicateId,
            vec!["a=evaluate(R.first)", "a=evaluate(R.second)"],
        ),
        (C::DuplicateArgument, vec!["a=check(R.same,a=@v/A,a=@v/A)"]),
        (
            C::DuplicateArgument,
            vec!["a=check(R.same,a=@v/A,bind.a=@v/A)"],
        ),
        (C::Reference, vec!["a=evaluate(R.unknown)"]),
        (C::Reference, vec!["a=evaluate(R.plus,x=$unknown.value)"]),
        (C::Reference, vec!["a=evaluate(R.root,a=@v/missing)"]),
        (C::Reference, vec!["a=evaluate(R.root,unknown=@v/A)"]),
        (C::Type, vec!["a=evaluate(R.plus,x=@v/A)"]),
        (C::Type, vec!["a=evaluate(R.belongs,a=@v/B,p=@v/i)"]),
        (
            C::Projection,
            vec!["a=evaluate(R.pair)", "b=evaluate(R.plus,x=$a.value[2])"],
        ),
        (
            C::Projection,
            vec![
                "a=evaluate(R.first)",
                "b=evaluate(R.plus,x=$a.evaluation.parts[0])",
            ],
        ),
        (C::MissingBinding, vec!["a=evaluate(R.plus)"]),
    ];
    for (i, (code, ts)) in cases.into_iter().enumerate() {
        let failure = prepare_observed(fixture::input(), &ts, &quiet()).unwrap_err();
        let PrepareFailure::Requests {
            failure: ResolveFailure::Invalid { issues, .. },
            ..
        } = failure
        else {
            panic!("{failure:?}")
        };
        assert_eq!(issues.len(), 1);
        assert_eq!(issues[0].code, code, "{ts:?}");
        let d = files(&format!("request-static-{i}"));
        let r = without_file_changes(&d, || asks(&d, &ts));
        let w = notified(&d, &r, "invalid", 64);
        no_artifacts(&d);
        assert!(
            arr(get(&w, "issues"))
                .iter()
                .all(|i| s(get(i, "code")) == "usage")
        );
        std::fs::remove_dir_all(d).unwrap();
    }
}
#[test]
fn multiple_cycles_preserve_the_whole_internal_graph_and_report_only_cyclic_members() {
    let ts = [
        "a=evaluate(R.plus,x=$b.value)",
        "b=evaluate(R.plus,x=$a.value)",
        "self=evaluate(R.plus,x=$self.value)",
        "d=evaluate(R.plus,x=$e.value)",
        "e=evaluate(R.plus,x=$d.value)",
        "tail=evaluate(R.plus,x=$a.value)",
        "free=evaluate(R.first)",
    ];
    let failure = evaluate_observed_bytes(fixture::input(), &ts, &quiet()).unwrap_err();
    let w = parse(failure.wire().unwrap().canonical().as_bytes()).unwrap();
    assert_eq!(
        ids(&w, "requests"),
        ["a", "b", "self", "d", "e", "tail", "free"]
    );
    assert!(arr(get(&w, "nodes")).is_empty());
    assert!(arr(get(&w, "answers")).is_empty());
    for (r, deps) in arr(get(&w, "requests")).iter().zip([
        vec!["b"],
        vec!["a"],
        vec!["self"],
        vec!["e"],
        vec!["d"],
        vec!["a"],
        vec![],
    ]) {
        assert_eq!(
            arr(get(r, "dependencies"))
                .iter()
                .map(s)
                .collect::<Vec<_>>(),
            deps
        );
    }
    let d = files("request-cycles");
    let r = without_file_changes(&d, || asks(&d, &ts));
    let cli = notified(&d, &r, "invalid", 64);
    no_artifacts(&d);
    for w in [w, cli] {
        let issues = arr(get(&w, "issues"));
        assert_eq!(issues.len(), 5);
        assert_eq!(
            issues
                .iter()
                .map(|i| s(get(i, "request")))
                .collect::<std::collections::BTreeSet<_>>(),
            ["a", "b", "self", "d", "e"].into_iter().collect()
        );
        for i in issues {
            assert_eq!(s(get(i, "code")), "cycle");
            assert!(!has(i, "location"));
            let id = s(get(i, "request"));
            let m = s(get(i, "message"));
            assert!(m.contains(id) && m.contains(" -> "), "{m}");
            let edge = match id {
                "a" => "a -> b",
                "b" => "b -> a",
                "self" => "self -> self",
                "d" => "d -> e",
                "e" => "e -> d",
                _ => unreachable!(),
            };
            assert!(m.contains(edge), "{m}: {edge}");
            assert!(!m.contains("tail") && !m.contains("free"));
        }
    }
    std::fs::remove_dir_all(d).unwrap();
}
#[test]
fn dynamic_projection_failures_keep_original_condition_and_block_each_later_consumer() {
    let cases = [
        (
            "take=evaluate(R.plus,x=$producer.value[9])",
            "producer=evaluate(R.empty)",
            "tail=evaluate(R.plus,x=$take.value)",
        ),
        (
            "take=evaluate(R.plus,x=$producer.value.some)",
            "producer=evaluate(R.absent)",
            "tail=evaluate(R.plus,x=$take.value)",
        ),
        (
            "take=evaluate(R.plus,x=$producer.value[0])",
            "producer=evaluate(R.choice)",
            "tail=evaluate(R.plus,x=$take.value)",
        ),
        (
            "take=evaluate(R.belongs,a=$producer.value,p=@v/i)",
            "producer=evaluate(R.root,a=@v/B)",
            "tail=check(R.require,b=$take.value)",
        ),
        (
            "take=evaluate(R.root,a=$producer.evaluation.environment.root)",
            "producer=evaluate(R.seed)",
            "tail=evaluate(R.root,a=$take.value)",
        ),
    ];
    for (i, (take, producer, tail)) in cases.into_iter().enumerate() {
        let ts = [
            tail,
            take,
            producer,
            "known=evaluate(R.first)",
            "prior=check(R.prior)",
        ];
        let p = prepare_observed(fixture::input(), &ts, &quiet()).unwrap();
        assert!(
            p.requests().requests()[1]
                .constraints
                .iter()
                .any(|c| c.dynamic)
        );
        let d = files(&format!("request-dynamic-{i}"));
        let r = asks(&d, &ts);
        let w = saved(&d, &r, 2);
        for (inspection, w) in [(true, internal(&ts)), (false, w)] {
            assert_eq!(s(get(&w, "status")), "partial");
            assert_eq!(s(get(answer(&w, "producer"), "status")), "established");
            assert_eq!(s(get(answer(&w, "prior"), "status")), "refuted");
            assert!(
                !arr(get(
                    answer(&w, "prior"),
                    if inspection {
                        "evidence"
                    } else {
                        "counterexamples"
                    }
                ))
                .is_empty()
            );
            assert_eq!(s(get(value(&w, "known"), "value")), "10");
            let mut original: Option<&JNode> = None;
            for (id, parent) in [("take", "producer"), ("tail", "take")] {
                let a = answer(&w, id);
                assert_eq!(s(get(a, "status")), "undetermined");
                assert!(matches!(&get(a,"outputs").value,JValue::Obj(m) if m.is_empty()));
                let rs = arr(get(a, "reasons"));
                assert!(rs.iter().any(|r| s(get(r, "code")) == "dependency_blocked"
                    && s(get(get(r, "details"), "request")) == parent));
                let reason = rs
                    .iter()
                    .find(|r| s(get(r, "code")) == "condition_failed")
                    .unwrap();
                assert_eq!(s(get(get(reason, "details"), "construction")), "projection");
                if inspection {
                    let condition = node(&w, get(get(reason, "details"), "condition"));
                    assert_eq!(s(get(get(condition, "judgment"), "status")), "refuted");
                    assert!(!arr(get(condition, "evidence")).is_empty());
                } else {
                    assert!(!has(get(reason, "details"), "condition"));
                }
                if let Some(expected) = original {
                    assert_eq!(reason, expected);
                } else {
                    original = Some(reason);
                }
                assert!(
                    rs.iter()
                        .all(|r| s(get(r, "code")) != "missing_observation")
                );
                for r in rs {
                    for dep in arr(get(r, "dependencies")) {
                        node(&w, dep);
                    }
                }
            }
        }
        std::fs::remove_dir_all(d).unwrap();
    }
}

#[test]
fn unavailable_evaluation_environment_preserves_all_original_reasons_through_two_consumers() {
    for (i, (producer, code)) in [
        ("producer=evaluate(R.missing,p=@v/i)", "missing_observation"),
        ("producer=evaluate(R.opaque)", "unsupported_algorithm"),
    ]
    .into_iter()
    .enumerate()
    {
        let ts = [
            "tail=evaluate(R.root,a=$take.evaluation.environment.root)",
            "take=evaluate(R.root,a=$producer.evaluation.environment.root)",
            producer,
            "known=evaluate(R.first)",
            "prior=check(R.prior)",
        ];
        let d = files(&format!("request-unavailable-environment-{i}"));
        let r = asks(&d, &ts);
        let w = saved(&d, &r, 2);
        for (inspection, w) in [(true, internal(&ts)), (false, w)] {
            let source = answer(&w, "producer");
            assert_eq!(s(get(source, "status")), "undetermined");
            assert_eq!(has(get(source, "outputs"), "evaluation"), inspection);
            assert!(!has(get(source, "outputs"), "value"));
            assert!(
                arr(get(source, "reasons"))
                    .iter()
                    .any(|r| s(get(r, "code")) == code)
            );
            for (consumer, parent) in [("take", "producer"), ("tail", "take")] {
                let a = answer(&w, consumer);
                assert_eq!(s(get(a, "status")), "undetermined");
                assert!(matches!(&get(a,"outputs").value,JValue::Obj(v) if v.is_empty()));
                let rs = arr(get(a, "reasons"));
                for original in arr(get(answer(&w, parent), "reasons")) {
                    assert!(rs.contains(original), "{consumer} lost {original:?}");
                }
                assert!(rs.iter().any(|r| s(get(r, "code")) == "dependency_blocked"
                    && s(get(get(r, "details"), "request")) == parent));
                assert!(rs.iter().any(|r| s(get(r, "code")) == "condition_failed"));
                for r in rs {
                    for dep in arr(get(r, "dependencies")) {
                        node(&w, dep);
                    }
                }
            }
            let take = answer(&w, "take");
            let condition = arr(get(take, "reasons"))
                .iter()
                .find(|r| s(get(r, "code")) == "condition_failed" && s(get(r, "request")) == "take")
                .unwrap();
            if inspection {
                let c = node(&w, get(get(condition, "details"), "condition"));
                assert_eq!(
                    &arr(get(c, "arguments"))[0],
                    get(get(source, "outputs"), "evaluation")
                );
                assert_eq!(s(get(get(c, "judgment"), "status")), "refuted");
                assert!(!arr(get(c, "evidence")).is_empty());
            } else {
                assert!(!has(get(condition, "details"), "condition"));
            }
            assert_eq!(s(get(value(&w, "known"), "value")), "10");
            assert_eq!(s(get(answer(&w, "prior"), "status")), "refuted");
        }
        std::fs::remove_dir_all(d).unwrap();
    }
}
