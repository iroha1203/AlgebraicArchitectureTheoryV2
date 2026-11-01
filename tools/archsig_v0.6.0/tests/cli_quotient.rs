//! 公開候補域と解集合を混同しない有限view商。
use crate::common::cli;
use archsig_common::json::{JNode, JValue};
use archsig_input::definition;
use cli::*;
fn input(name: &str) -> std::path::PathBuf {
    let d = r#"{"format":"archsig.atom-definition/1","semantics":"archsig/0.6.0","vocabularies":[{"semantics":"archsig/0.6.0","namespace":"Pair","version":"1","dependencies":[],"declarations":[{"kind":"entity","name":"Pair.State","meaning":"二つの条件。","parameters":[],"fields":[{"name":"x","type":"Bool","meaning":"第一条件。"},{"name":"y","type":"Bool","meaning":"第二条件。"}],"alignments":[]}]}]}"#;
    let checked = definition::check_definitions(&[("d", d.as_bytes())]).unwrap();
    let digest = &checked.vocabularies()["Pair"].digest;
    let a=r#"{"format":"archsig.archmap/2","semantics":"archsig/0.6.0","vocabularies":[{"namespace":"Pair","version":"1","digest":"@D@"}],"sources":[],"origins":[{"id":"o","mode":"specification","method":"有限商の独立試験。","locations":[],"note":"候補と解を分ける。"}],"snapshots":[{"id":"v","origin":"o","subjects":[{"id":"s","type":"Pair.State","origin":"o"}],"atoms":[{"id":"x","subject":"s","field":"Pair.State.x","value":false,"origin":"o"},{"id":"y","subject":"s","field":"Pair.State.y","value":false,"origin":"o"}]}]}"#.replace("@D@",digest);
    let l = format!(
        "law \"archsig.law/2\" semantics \"archsig/0.6.0\";reading Pair{{use vocabulary Pair version \"1\" digest \"{digest}\";change choose(s:State,a:Bool,b:Bool)=s with{{x=a,y=b}};law required valid(s:State):s.x;law optional empty(s:State):false;view last(s:State):Bool=s.y;}}"
    );
    let dir = workdir(name);
    for (n, v) in [("d.json", d), ("a.json", a.as_str()), ("l.law", l.as_str())] {
        std::fs::write(dir.join(n), v).unwrap();
    }
    dir
}
fn execute(dir: &std::path::Path, out: &str, asks: &[&str], reuse: Option<&str>) -> Run {
    let mut args = vec![
        "run",
        "--atom-definition",
        "d.json",
        "--archmap",
        "a.json",
        "--law",
        "l.law",
        "--out",
        out,
    ];
    if let Some(reuse) = reuse {
        args.extend(["--reuse", reuse]);
    }
    for ask in asks {
        args.extend(["--ask", ask]);
    }
    run(dir, &args)
}
fn node<'a>(result: &'a JNode, reference: &JNode) -> &'a JNode {
    arr(get(result, "nodes"))
        .iter()
        .find(|n| s(get(n, "id")) == s(get(reference, "node")))
        .unwrap()
}
fn quotient<'a>(result: &'a JNode, index: usize) -> &'a JNode {
    get(
        node(
            result,
            get(
                get(&arr(get(result, "answers"))[index], "outputs"),
                "quotient",
            ),
        ),
        "value",
    )
}
fn fiber_sizes(result: &JNode, index: usize) -> Vec<usize> {
    let q = quotient(result, index);
    let fibers = arr(get(get(q, "representation"), "fibers"));
    let mut sizes = vec![];
    for fiber in fibers {
        let class = node(result, get(fiber, "image"));
        let preimage = node(result, get(fiber, "preimage"));
        let points = arr(get(get(preimage, "value"), "elements"));
        assert_eq!(arr(get(class, "value")).len(), points.len());
        sizes.push(points.len());
    }
    let projection = node(result, get(q, "projection"));
    assert_eq!(
        arr(get(get(projection, "value"), "pairs")).len(),
        sizes.iter().sum::<usize>()
    );
    sizes.sort();
    sizes
}
fn pair(value: &JNode) -> (bool, bool) {
    let values = arr(value);
    assert_eq!(values.len(), 2);
    let boolean = |v: &JNode| match &v.value {
        JValue::Bool(b) => *b,
        _ => panic!("expected Bool"),
    };
    (boolean(&values[0]), boolean(&values[1]))
}
fn members(value: &JNode) -> Vec<(bool, bool)> {
    let mut values = arr(value).iter().map(pair).collect::<Vec<_>>();
    values.sort();
    values
}
fn exact_fibers(result: &JNode, index: usize, mut expected: Vec<Vec<(bool, bool)>>) {
    for class in &mut expected {
        class.sort();
    }
    expected.sort();
    let q = quotient(result, index);
    let class_domain = node(result, get(q, "classes"));
    let mut actual = arr(get(get(class_domain, "value"), "elements"))
        .iter()
        .map(|r| members(get(node(result, r), "value")))
        .collect::<Vec<_>>();
    actual.sort();
    assert_eq!(actual, expected);
    let mut fibers = vec![];
    for fiber in arr(get(get(q, "representation"), "fibers")) {
        let class = members(get(node(result, get(fiber, "image")), "value"));
        let preimage = node(result, get(fiber, "preimage"));
        let mut points = arr(get(get(preimage, "value"), "elements"))
            .iter()
            .map(|r| pair(get(node(result, r), "value")))
            .collect::<Vec<_>>();
        points.sort();
        assert_eq!(points, class);
        fibers.push(class);
    }
    fibers.sort();
    assert_eq!(fibers, expected);
    let projection = node(result, get(q, "projection"));
    let mut pairs = arr(get(get(projection, "value"), "pairs"))
        .iter()
        .map(|p| {
            let p = arr(p);
            assert_eq!(p.len(), 2);
            (
                pair(get(node(result, &p[0]), "value")),
                members(get(node(result, &p[1]), "value")),
            )
        })
        .collect::<Vec<_>>();
    let mut expected_pairs = expected
        .iter()
        .flat_map(|class| class.iter().map(|point| (*point, class.clone())))
        .collect::<Vec<_>>();
    pairs.sort();
    expected_pairs.sort();
    assert_eq!(pairs, expected_pairs);
}
#[test]
fn finite_quotient_distinguishes_all_candidates_from_solutions() {
    let dir = input("quotient-domains");
    let asks = [
        "all=quotient(Pair.last,on=$s.domain,s=@v/s)",
        "good=quotient(Pair.last,on=$s.solutions,s=@v/s)",
        "s=solve(Pair.valid,on=@v/s,using=Pair.choose,s=@v/s)",
    ];
    let first = execute(&dir, "out", &asks, None);
    assert_eq!(first.code, 0, "{}", first.stdout);
    let original = result_json(&dir, &first);
    for request in &arr(get(&original, "requests"))[..2] {
        let defaults = arr(get(request, "defaults"));
        assert_eq!(defaults.len(), 1);
        assert_eq!(s(get(&defaults[0], "rule")), "no_law_check");
    }
    assert_eq!(fiber_sizes(&original, 0), vec![2, 2]);
    assert_eq!(fiber_sizes(&original, 1), vec![1, 1]);
    exact_fibers(
        &original,
        0,
        vec![
            vec![(false, false), (true, false)],
            vec![(false, true), (true, true)],
        ],
    );
    exact_fibers(&original, 1, vec![vec![(true, false)], vec![(true, true)]]);
}
#[test]
fn empty_solution_quotient_keeps_its_type_and_has_no_fibers() {
    let dir = input("quotient-empty");
    let r = execute(
        &dir,
        "out",
        &[
            "s=solve(Pair.empty,on=@v/s,using=Pair.choose,s=@v/s)",
            "q=quotient(Pair.last,on=$s.solutions,s=@v/s)",
        ],
        None,
    );
    assert_eq!(r.code, 1, "{}", r.stdout);
    let result = result_json(&dir, &r);
    assert!(fiber_sizes(&result, 1).is_empty());
    let classes = node(&result, get(quotient(&result, 1), "classes"));
    assert_eq!(s(&arr(get(get(classes, "value"), "type"))[0]), "Set");
    assert!(arr(get(get(classes, "value"), "elements")).is_empty());
    assert!(!has(classes, "arguments"));
    assert_eq!(
        s(get(&arr(get(&result, "answers"))[1], "status")),
        "established"
    );
}

#[test]
fn quotient_rejects_wrong_domain_missing_bindings_private_fields_and_cycles() {
    let cases: &[&[&str]] = &[
        &[
            "v=evaluate(Pair.last,s=@v/s)",
            "q=quotient(Pair.last,on=$v.value,s=@v/s)",
        ],
        &[
            "s=solve(Pair.valid,on=@v/s,using=Pair.choose,s=@v/s)",
            "q=quotient(Pair.last,on=$s.domain)",
        ],
        &[
            "s=solve(Pair.valid,on=@v/s,using=Pair.choose,s=@v/s)",
            "q=quotient(Pair.last,on=$s.domain,s=@v/s)",
            "v=evaluate(Pair.last,s=$q.quotient.representation)",
        ],
        &["q=quotient(Pair.last,on=$q.quotient.domain,s=@v/s)"],
    ];
    for (i, asks) in cases.iter().enumerate() {
        let dir = input(&format!("quotient-static-{i}"));
        let r = execute(&dir, "out", asks, None);
        assert_eq!(r.code, 64, "{}", r.stdout);
        assert!(!has(&r.receipt, "result"));
    }
}

#[test]
fn stopped_quotient_keeps_prior_solve_without_publishing_incomplete_classes() {
    use archsig_common::control::{Checkpoint, Control};
    use archsig_computation::observed::evaluate::evaluate_observed_bytes;
    use archsig_input::input::InputSources;
    use std::{cell::Cell, rc::Rc};
    let dir = law_input("quotient-stop", "law optional same(s:State,b:Bool):s.x=b;");
    for case in [0, 3, 6] {
        let seen = Rc::new(Cell::new(0));
        let count = seen.clone();
        let c = Control::new(move |point| {
            if point == Checkpoint::Quotient {
                count.set(count.get() + 1);
            }
            let stop = if case == 6 {
                count.get() >= 2 && point == Checkpoint::FiniteLawOperand
            } else {
                count.get() == 2
            };
            stop.then_some(archsig_input::result::Signal::Term)
        });
        let sources = InputSources::from_bytes(
            vec![std::fs::read(dir.join("d.json")).unwrap()],
            std::fs::read(dir.join("l.law")).unwrap(),
            std::fs::read(dir.join("a.json")).unwrap(),
        );
        let quotient = if case < 3 {
            "q=quotient(Pair.last,on=$s.domain,s=@v/s)"
        } else {
            "q=quotient(Pair.last,on=$s.domain,s=@v/s,law=Pair.same)"
        };
        let result = evaluate_observed_bytes(
            sources,
            &[
                "s=solve(Pair.valid,on=@v/s,using=Pair.choose,s=@v/s)",
                quotient,
                "later=evaluate(Pair.last,s=@v/s)",
            ],
            &c,
        )
        .unwrap();
        if case == 6 {
            assert!(seen.get() >= 2);
        } else {
            assert_eq!(seen.get(), 2);
        }
        let wire = archsig_common::json::parse(result.wire().canonical().as_bytes()).unwrap();
        let answers = arr(get(&wire, "answers"));
        assert_eq!(s(get(&answers[0], "status")), "established");
        assert!(has(get(&answers[0], "outputs"), "solutions"));
        assert!(!has(get(&answers[1], "outputs"), "quotient"));

        for answer in &answers[1..] {
            assert_eq!(s(get(answer, "status")), "undetermined");
            assert!(
                arr(get(answer, "reasons"))
                    .iter()
                    .any(|r| s(get(r, "code")) == "cancelled")
            );
        }
    }
}

#[test]
fn quotient_of_new_solutions_reads_the_previous_repaired_state() {
    let dir = input("quotient-repaired");
    let law=std::fs::read_to_string(dir.join("l.law")).unwrap().replace("view last", "change toggle(s:State,b:Bool)=s with{x=not s.x,y=b};law optional pinned(s:State):s.x and s.y;law optional opposite(s:State):not s.x;view last");
    std::fs::write(dir.join("l.law"), law).unwrap();
    let r = execute(
        &dir,
        "out",
        &[
            "r=repair(Pair.pinned,on=@v/s,using=Pair.choose,s=@v/s)",
            "s=solve(Pair.opposite,on=$r.object,using=Pair.toggle,s=@v/s)",
            "q=quotient(Pair.last,on=$s.solutions,s=@v/s)",
        ],
        None,
    );
    assert_eq!(r.code, 0, "{}", r.stdout);
    let result = result_json(&dir, &r);
    assert_eq!(fiber_sizes(&result, 2), vec![1, 1]);
}

#[test]
fn missing_view_keeps_quotient_undetermined_and_independent_followup_available() {
    let dir = input("quotient-missing");
    let law = std::fs::read_to_string(dir.join("l.law"))
        .unwrap()
        .replace("x=a,y=b", "x=a")
        .replace("Bool=s.y", "Bool=s.x and s.y");
    std::fs::write(dir.join("l.law"), law).unwrap();
    let map=std::fs::read_to_string(dir.join("a.json")).unwrap()
        .replace(",{\"id\":\"y\",\"subject\":\"s\",\"field\":\"Pair.State.y\",\"value\":false,\"origin\":\"o\"}","");
    std::fs::write(dir.join("a.json"), map).unwrap();
    let asks = [
        "s=solve(Pair.valid,on=@v/s,using=Pair.choose,s=@v/s)",
        "q=quotient(Pair.last,on=$s.domain,s=@v/s)",
        "later=check(Pair.empty,s=@v/s)",
    ];
    let first = execute(&dir, "out", &asks, None);
    assert_eq!(first.code, 2, "{}", first.stdout);
    let result = result_json(&dir, &first);
    let answers = arr(get(&result, "answers"));
    assert_eq!(s(get(&answers[0], "status")), "established");
    assert_eq!(s(get(&answers[1], "status")), "undetermined");
    assert!(!has(get(&answers[1], "outputs"), "quotient"));
    for key in ["snapshots", "modes"] {
        assert_eq!(
            get(get(&answers[1], "scope"), key).value,
            get(get(&answers[0], "scope"), key).value
        );
    }
    assert_eq!(s(get(&answers[2], "status")), "refuted");
    let reason = arr(get(&answers[1], "reasons"))
        .iter()
        .find(|r| s(get(r, "code")) == "missing_observation")
        .unwrap();
    assert!(arr(get(reason, "dependencies")).is_empty());
    assert!(
        arr(get(reason, "missing"))
            .iter()
            .any(|f| s(get(f, "field")) == "Pair.State.y")
    );
    let defaults = arr(get(&arr(get(&result, "requests"))[1], "defaults"));
    assert_eq!(defaults.len(), 1);
    assert_eq!(s(get(&defaults[0], "rule")), "no_law_check");
}

#[test]
fn unavailable_view_binding_blocks_quotient_without_breaking_independent_requests() {
    let dir = input("quotient-binding-missing");
    let law = std::fs::read_to_string(dir.join("l.law"))
        .unwrap()
        .replace("x=a,y=b", "x=a")
        .replace(
            "view last",
            "view echo(b:Bool):Bool=b;view first(s:State):Bool=s.x;view last",
        );
    std::fs::write(dir.join("l.law"), law).unwrap();
    let map=std::fs::read_to_string(dir.join("a.json")).unwrap()
        .replace(",{\"id\":\"y\",\"subject\":\"s\",\"field\":\"Pair.State.y\",\"value\":false,\"origin\":\"o\"}","");
    std::fs::write(dir.join("a.json"), map).unwrap();
    let asks = [
        "s=solve(Pair.valid,on=@v/s,using=Pair.choose,s=@v/s)",
        "v=evaluate(Pair.last,s=@v/s)",
        "q=quotient(Pair.echo,on=$s.domain,b=$v.value)",
        "later=check(Pair.empty,s=@v/s)",
    ];
    let first = execute(&dir, "out", &asks, None);
    assert_eq!(first.code, 2, "{}", first.stdout);
    let result = result_json(&dir, &first);
    let answers = arr(get(&result, "answers"));
    assert_eq!(s(get(&answers[0], "status")), "established");
    assert_eq!(s(get(&answers[2], "status")), "undetermined");
    assert!(!has(get(&answers[2], "outputs"), "quotient"));
    assert_eq!(s(get(&answers[3], "status")), "refuted");
    let reasons = arr(get(&answers[2], "reasons"));
    assert!(
        reasons
            .iter()
            .any(|r| s(get(r, "code")) == "dependency_blocked")
    );
    assert!(reasons.iter().any(|r| {
        s(get(r, "code")) == "missing_observation"
            && arr(get(r, "missing"))
                .iter()
                .any(|f| s(get(f, "field")) == "Pair.State.y")
    }));
    let mut known = asks;
    known[1] = "v=evaluate(Pair.first,s=@v/s)";
    let available = execute(&dir, "known", &known, None);
    assert_eq!(available.code, 1, "{}", available.stdout);
    let complete = result_json(&dir, &available);
    assert_eq!(
        s(get(&arr(get(&complete, "answers"))[2], "status")),
        "established"
    );
    exact_fibers(
        &complete,
        2,
        vec![vec![
            (false, false),
            (false, true),
            (true, false),
            (true, true),
        ]],
    );
}

#[test]
fn quotient_keeps_view_quantifiers_and_binding_producer_scope() {
    let dir = input("quotient-scope");
    let law = std::fs::read_to_string(dir.join("l.law")).unwrap();
    let vocabulary = law
        .split("reading Pair{")
        .nth(1)
        .unwrap()
        .split(';')
        .next()
        .unwrap();
    let extra = format!("reading Other{{{vocabulary};view flag(s:State):Bool=s.x;}}");
    let law = law.replace(
        "view last",
        "view all(s:State):Bool=forall b:Bool . b or not b;view echo(b:Bool):Bool=b;view last",
    ) + &extra;
    std::fs::write(dir.join("l.law"), law).unwrap();
    let r = execute(
        &dir,
        "out",
        &[
            "s=solve(Pair.valid,on=@v/s,using=Pair.choose,s=@v/s)",
            "v=evaluate(Other.flag,s=@v/s)",
            "q=quotient(Pair.echo,on=$s.domain,b=$v.value)",
            "all=quotient(Pair.all,on=$s.domain,s=@v/s)",
            "ev=evaluate(Pair.all,s=@v/s)",
        ],
        None,
    );
    let result = result_json(&dir, &r);
    let answers = arr(get(&result, "answers"));
    assert_eq!(r.code, 0, "{} {answers:?}", r.stdout);
    assert!(
        arr(get(get(&answers[2], "scope"), "readings"))
            .iter()
            .any(|x| s(x) == "Other")
    );
    assert!(
        arr(get(get(&answers[2], "scope"), "snapshots"))
            .iter()
            .any(|x| s(x) == "v")
    );
    let ordinary = arr(get(get(&answers[4], "scope"), "quantifiers"));
    assert!(!ordinary.is_empty());
    for scope in [get(&answers[3], "scope")] {
        let quantifiers = arr(get(scope, "quantifiers"));
        for q in ordinary {
            assert!(quantifiers.iter().any(|actual| {
                ["kind", "name", "type"]
                    .iter()
                    .all(|key| get(actual, key).value == get(q, key).value)
            }));
        }
    }
}

#[test]
fn inapplicable_view_binding_preserves_projection_condition_and_followup() {
    let dir = input("quotient-inapplicable");
    let law = std::fs::read_to_string(dir.join("l.law")).unwrap().replace(
        "view last",
        "view no():Option<Bool> = none<Bool>;view echo(b:Bool):Bool=b;view last",
    );
    std::fs::write(dir.join("l.law"), law).unwrap();
    let r = execute(
        &dir,
        "out",
        &[
            "s=solve(Pair.valid,on=@v/s,using=Pair.choose,s=@v/s)",
            "v=evaluate(Pair.no)",
            "q=quotient(Pair.echo,on=$s.domain,b=$v.value.some)",
            "later=check(Pair.empty,s=@v/s)",
        ],
        None,
    );
    assert_eq!(r.code, 2, "{}", r.stdout);
    let result = result_json(&dir, &r);
    let answers = arr(get(&result, "answers"));
    assert_eq!(s(get(&answers[2], "status")), "undetermined");
    assert!(!has(get(&answers[2], "outputs"), "quotient"));
    assert_eq!(s(get(&answers[3], "status")), "refuted");
    for code in ["condition_failed", "dependency_blocked"] {
        assert!(
            arr(get(&answers[2], "reasons"))
                .iter()
                .any(|r| s(get(r, "code")) == code)
        );
    }
    let law = std::fs::read_to_string(dir.join("l.law"))
        .unwrap()
        .replace("none<Bool>", "some(true)");
    std::fs::write(dir.join("l.law"), law).unwrap();
    let asks = [
        "s=solve(Pair.valid,on=@v/s,using=Pair.choose,s=@v/s)",
        "v=evaluate(Pair.no)",
        "q=quotient(Pair.echo,on=$s.domain,b=$v.value.some)",
    ];
    let available = execute(&dir, "known", &asks, None);
    assert_eq!(available.code, 0, "{}", available.stdout);
    let complete = result_json(&dir, &available);
    exact_fibers(
        &complete,
        2,
        vec![vec![
            (false, false),
            (false, true),
            (true, false),
            (true, true),
        ]],
    );
}

fn law_input(name: &str, extra: &str) -> std::path::PathBuf {
    let dir = input(name);
    let path = dir.join("l.law");
    let mut law = std::fs::read_to_string(&path).unwrap();
    law.pop();
    law.push_str(extra);
    law.push('}');
    std::fs::write(path, law).unwrap();
    dir
}
#[test]
fn law_descent_compares_typed_pairs_instead_of_truth() {
    let dir = law_input(
        "quotient-law-pairs",
        "law optional same(s:State):s.x=s.x;law optional last_eq(s:State):s.y=s.y;",
    );
    let asks = [
        "s=solve(Pair.valid,on=@v/s,using=Pair.choose,s=@v/s)",
        "bad=quotient(Pair.last,on=$s.domain,s=@v/s,law=Pair.same)",
        "good=quotient(Pair.last,on=$s.domain,s=@v/s,law=Pair.last_eq)",
        "solutions=quotient(Pair.last,on=$s.solutions,s=@v/s,law=Pair.same)",
    ];
    let r = execute(&dir, "out", &asks, None);
    assert_eq!(r.code, 1, "{}", r.stdout);
    let result = result_json(&dir, &r);
    let answers = arr(get(&result, "answers"));
    assert_eq!(s(get(&answers[1], "status")), "refuted");
    for index in [2, 3] {
        assert_eq!(s(get(&answers[index], "status")), "established");
        let q = quotient(&result, index);
        let map = node(&result, get(q, "descent"));
        assert_eq!(arr(get(get(map, "value"), "pairs")).len(), 2);
        for entry in arr(get(get(map, "value"), "pairs")) {
            let entry = arr(entry);
            let class = members(get(node(&result, &entry[0]), "value"));
            let family = arr(get(node(&result, &entry[1]), "value"));
            assert_eq!(family.len(), 1);
            let value = arr(get(&arr(&family[0])[1], "some"));
            assert_eq!(value.len(), 2);
            let expected = if index == 2 { class[0].1 } else { true };
            for side in value {
                assert_eq!(side.value, JValue::Bool(expected));
            }
        }
    }
    let evidence = node(&result, &arr(get(&answers[1], "counterexamples"))[0]);
    assert_eq!(s(get(get(evidence, "value"), "kind")), "separating_pair");
    let data = get(get(evidence, "value"), "data");
    let points = [
        pair(get(node(&result, get(data, "first")), "value")),
        pair(get(node(&result, get(data, "second")), "value")),
    ];
    assert_eq!(points[0].1, points[1].1);
    assert_ne!(points[0].0, points[1].0);
    let values = arr(get(data, "law_values"));
    assert_ne!(
        get(node(&result, &values[0]), "value").value,
        get(node(&result, &values[1]), "value").value
    );
    for evaluation in arr(get(quotient(&result, 1), "evaluations")) {
        let evaluation = get(node(&result, evaluation), "value");
        assert_eq!(
            get(node(&result, get(evaluation, "value")), "value").value,
            JValue::Bool(true)
        );
        let environment = get(node(&result, get(evaluation, "environment")), "value");
        assert_eq!(arr(get(environment, "overrides")).len(), 2);
    }
}
#[test]
fn law_descent_preserves_unbound_instance_keys_and_additional_binding() {
    let dir = law_input(
        "quotient-law-quantified",
        "law optional indexed(s:State,b:Bool):s.y=b;view fixed():Bool=false;view yes():Bool=true;",
    );
    let asks = [
        "s=solve(Pair.valid,on=@v/s,using=Pair.choose,s=@v/s)",
        "v=evaluate(Pair.yes)",
        "q=quotient(Pair.last,on=$s.domain,s=@v/s,law=Pair.indexed)",
        "bound=quotient(Pair.last,on=$s.domain,s=@v/s,b=$v.value,law=Pair.indexed)",
        "bad=quotient(Pair.fixed,on=$s.domain,s=@v/s,law=Pair.indexed)",
    ];
    let r = execute(&dir, "out", &asks, None);
    assert_eq!(r.code, 1, "{}", r.stdout);
    let result = result_json(&dir, &r);
    let answers = arr(get(&result, "answers"));
    assert_eq!(s(get(&answers[2], "status")), "established");
    assert_eq!(s(get(&answers[3], "status")), "established");
    assert_eq!(s(get(&answers[4], "status")), "refuted");
    assert!(
        arr(get(get(&answers[2], "scope"), "quantifiers"))
            .iter()
            .any(|q| s(get(q, "name")) == "b" && s(get(q, "kind")) == "forall")
    );
    assert_eq!(arr(get(quotient(&result, 2), "evaluations")).len(), 8);
    assert_eq!(arr(get(quotient(&result, 3), "evaluations")).len(), 4);
    let map = get(node(&result, get(quotient(&result, 2), "descent")), "value");
    for entry in arr(get(map, "pairs")) {
        let family = get(node(&result, &arr(entry)[1]), "value");
        assert_eq!(arr(family).len(), 2);
        let keys = arr(family)
            .iter()
            .map(|item| matches!(arr(&arr(item)[0])[1].value, JValue::Bool(true)))
            .collect::<Vec<_>>();
        assert!(keys.contains(&false) && keys.contains(&true));
    }
}
#[test]
fn law_descent_distinguishes_guard_and_preserves_empty_domain_type() {
    let dir = law_input(
        "quotient-law-guard",
        "law optional guarded(s:State) when s.x:s.y=s.y;",
    );
    let asks = [
        "s=solve(Pair.valid,on=@v/s,using=Pair.choose,s=@v/s)",
        "bad=quotient(Pair.last,on=$s.domain,s=@v/s,law=Pair.guarded)",
        "good=quotient(Pair.last,on=$s.solutions,s=@v/s,law=Pair.guarded)",
        "empty=solve(Pair.empty,on=@v/s,using=Pair.choose,s=@v/s)",
        "q=quotient(Pair.last,on=$empty.solutions,s=@v/s,law=Pair.guarded)",
    ];
    let r = execute(&dir, "out", &asks, None);
    assert_eq!(r.code, 1, "{}", r.stdout);
    let result = result_json(&dir, &r);
    let answers = arr(get(&result, "answers"));
    assert_eq!(s(get(&answers[1], "status")), "refuted");
    assert_eq!(s(get(&answers[2], "status")), "established");
    assert_eq!(s(get(&answers[4], "status")), "established");
    let q = quotient(&result, 4);
    assert!(arr(get(q, "evaluations")).is_empty());
    let map = get(node(&result, get(q, "descent")), "value");
    assert!(arr(get(map, "pairs")).is_empty());
    let target = get(node(&result, get(map, "target")), "value");
    assert!(arr(get(target, "elements")).is_empty());
    assert_eq!(s(&arr(get(target, "type"))[0]), "Set");
    let evaluations = arr(get(quotient(&result, 1), "evaluations"));
    let inactive = evaluations
        .iter()
        .map(|r| get(node(&result, r), "value"))
        .filter(|e| s(get(e, "applicability")) == "not_applicable")
        .collect::<Vec<_>>();
    assert_eq!(inactive.len(), 2);
    for e in inactive {
        assert!(!has(e, "value"));
        assert!(!has(e, "parts"));
    }
}
#[test]
fn missing_law_values_remain_missing_and_independent_followup_runs() {
    let dir = law_input(
        "quotient-law-missing",
        "law optional both(s:State):s.y=s.y;view fixed(s:State):Bool=false;",
    );
    let path = dir.join("l.law");
    let law = std::fs::read_to_string(&path)
        .unwrap()
        .replace("with{x=a,y=b}", "with{x=a}");
    std::fs::write(path, law).unwrap();
    let path = dir.join("a.json");
    let map = std::fs::read_to_string(&path).unwrap().replace(
        r#",{"id":"y","subject":"s","field":"Pair.State.y","value":false,"origin":"o"}"#,
        "",
    );
    std::fs::write(path, map).unwrap();
    let asks = [
        "s=solve(Pair.valid,on=@v/s,using=Pair.choose,s=@v/s)",
        "q=quotient(Pair.fixed,on=$s.domain,s=@v/s,law=Pair.both)",
        "later=check(Pair.valid,s=@v/s)",
    ];
    let r = execute(&dir, "out", &asks, None);
    assert_eq!(r.code, 2, "{}", r.stdout);
    let result = result_json(&dir, &r);
    let answers = arr(get(&result, "answers"));
    assert_eq!(s(get(&answers[1], "status")), "undetermined");
    assert!(!has(get(&answers[1], "outputs"), "quotient"));
    assert_eq!(s(get(&answers[2], "status")), "refuted");
    assert!(format!("{:?}", get(&answers[1], "reasons")).contains("Pair.State.y"));
}
#[test]
fn quotient_law_rejects_wrong_kind_and_shared_parameter_type() {
    let dir = law_input("quotient-law-usage", "law optional other(s:Bool):s=s;");
    for ask in [
        "q=quotient(Pair.last,on=$s.domain,s=@v/s,law=Pair.last)",
        "q=quotient(Pair.last,on=$s.domain,s=@v/s,law=Pair.other)",
        "q=quotient(Pair.last,on=$s.domain,s=@v/s,law=Pair.valid,law=Pair.valid)",
    ] {
        let r = execute(
            &dir,
            "out",
            &["s=solve(Pair.valid,on=@v/s,using=Pair.choose,s=@v/s)", ask],
            None,
        );
        assert_eq!(r.code, 64, "{}", r.stdout);
    }
}
#[test]
fn quotient_law_preserves_composite_operand_and_guard_evaluation_children() {
    let dir = law_input(
        "quotient-law-children",
        "law optional composite(s:State) when s.x or s.y:(s.x and s.y)=s.y;",
    );
    let r = execute(
        &dir,
        "out",
        &[
            "s=solve(Pair.valid,on=@v/s,using=Pair.choose,s=@v/s)",
            "q=quotient(Pair.last,on=$s.domain,s=@v/s,law=Pair.composite)",
        ],
        None,
    );
    assert_eq!(r.code, 1, "{}", r.stdout);
    let result = result_json(&dir, &r);
    let saved_result = result;
    let result = internal_graph(&dir, &saved_result);
    let law = std::fs::read_to_string(dir.join("l.law")).unwrap();
    let check_children = |children: &[JNode], expected: &[bool]| {
        assert_eq!(children.len(), 2);
        for ((child, source), expected) in children.iter().zip(["s.x", "s.y"]).zip(expected) {
            let evaluation = get(node(&result, child), "value");
            assert_eq!(
                get(node(&result, get(evaluation, "value")), "value").value,
                JValue::Bool(*expected)
            );
            let expression = get(node(&result, get(evaluation, "expression")), "value");
            let span = arr(get(get(expression, "location"), "span"));
            assert_eq!(&law[num(&span[0]) as usize..num(&span[1]) as usize], source);
        }
    };
    for reference in arr(get(quotient(&result, 1), "evaluations")) {
        let evaluation = get(node(&result, reference), "value");
        let environment = get(node(&result, get(evaluation, "environment")), "value");
        let mut values = std::collections::BTreeMap::new();
        for row in arr(get(environment, "overrides")) {
            values.insert(
                s(get(get(row, "slot"), "field")),
                matches!(
                    get(node(&result, get(row, "value")), "value").value,
                    JValue::Bool(true)
                ),
            );
        }
        let expected = [values["Pair.State.x"], values["Pair.State.y"]];
        let parts = arr(get(evaluation, "parts"));
        let guard = get(node(&result, &arr(get(&parts[0], "children"))[0]), "value");
        check_children(
            arr(get(&arr(get(guard, "parts"))[0], "children")),
            &expected,
        );
        if s(get(evaluation, "applicability")) == "applicable" {
            let body = arr(get(&parts[1], "children"));
            assert_eq!(body.len(), 2);
            let group = get(node(&result, &body[0]), "value");
            let and = get(
                node(
                    &result,
                    &arr(get(&arr(get(group, "parts"))[0], "children"))[0],
                ),
                "value",
            );
            check_children(arr(get(&arr(get(and, "parts"))[0], "children")), &expected);
            assert_eq!(
                get(node(&result, get(and, "value")), "value").value,
                JValue::Bool(expected[0] && expected[1])
            );
        }
    }
}
#[test]
fn quotient_numeric_law_retains_typed_residual_and_false_values_under_true_descent() {
    let dir = law_input(
        "quotient-law-numeric",
        "law optional numeric(s:State):1=2;law optional tuple(s:State):(1,2)=(3,1);view rational():Q=rat(1,2);view modular():Fp(3)=1;law optional ratio(s:State):rational()=1;law optional prime(s:State):modular()=2;",
    );
    let r = execute(
        &dir,
        "out",
        &[
            "s=solve(Pair.valid,on=@v/s,using=Pair.choose,s=@v/s)",
            "q=quotient(Pair.last,on=$s.domain,s=@v/s,law=Pair.numeric)",
            "t=quotient(Pair.last,on=$s.domain,s=@v/s,law=Pair.tuple)",
            "qrat=quotient(Pair.last,on=$s.domain,s=@v/s,law=Pair.ratio)",
            "qfp=quotient(Pair.last,on=$s.domain,s=@v/s,law=Pair.prime)",
        ],
        None,
    );
    assert_eq!(r.code, 0, "{}", r.stdout);
    let result = result_json(&dir, &r);
    let result = internal_graph(&dir, &result);
    for index in 1..=4 {
        assert_eq!(
            s(get(&arr(get(&result, "answers"))[index], "status")),
            "established"
        );
        for reference in arr(get(quotient(&result, index), "evaluations")) {
            let evaluation = get(node(&result, reference), "value");
            assert_eq!(
                get(node(&result, get(evaluation, "value")), "value").value,
                JValue::Bool(false)
            );
            let residual = get(
                node(&result, get(&arr(get(evaluation, "parts"))[0], "residual")),
                "value",
            );
            match index {
                1 => assert_eq!(s(residual), "-1"),
                2 => {
                    let values = arr(residual);
                    assert_eq!(s(&values[0]), "-2");
                    assert_eq!(s(&values[1]), "1");
                }
                3 => {
                    let values = arr(residual);
                    assert_eq!(s(&values[0]), "-1");
                    assert_eq!(s(&values[1]), "2");
                }
                4 => assert_eq!(s(residual), "2"),
                _ => unreachable!(),
            }
        }
    }
}

#[test]
fn option_quotient_keeps_none_fibers_and_typed_laws() {
    let dir = law_input(
        "quotient-option",
        "view tagged(s:State):Option<Bool> = if s.x then some(s.y) else none<Bool>;law optional visible(s:State):some(s.x)=some(s.x);law optional hidden(s:State):some(s.y)=some(s.y);",
    );
    let asks = [
        "s=solve(Pair.valid,on=@v/s,using=Pair.choose,s=@v/s)",
        "good=quotient(Pair.tagged,on=$s.domain,s=@v/s,law=Pair.visible)",
        "bad=quotient(Pair.tagged,on=$s.domain,s=@v/s,law=Pair.hidden)",
    ];
    let first = execute(&dir, "out", &asks, None);
    assert_eq!(first.code, 1, "{}", first.stdout);
    let result = result_json(&dir, &first);
    let answers = arr(get(&result, "answers"));
    assert_eq!(s(get(&answers[1], "status")), "established");
    assert_eq!(s(get(&answers[2], "status")), "refuted");
    for index in [1, 2] {
        exact_fibers(
            &result,
            index,
            vec![
                vec![(false, false), (false, true)],
                vec![(true, false)],
                vec![(true, true)],
            ],
        );
    }
    let evidence = node(&result, &arr(get(&answers[2], "counterexamples"))[0]);
    assert_eq!(s(get(get(evidence, "value"), "kind")), "separating_pair");
    let data = get(get(evidence, "value"), "data");
    let points = [
        pair(get(node(&result, get(data, "first")), "value")),
        pair(get(node(&result, get(data, "second")), "value")),
    ];
    assert!(!points[0].0 && !points[1].0);
    assert_ne!(points[0].1, points[1].1);
    let values = arr(get(data, "law_values"));
    assert_ne!(
        get(node(&result, &values[0]), "value").value,
        get(node(&result, &values[1]), "value").value
    );
}

#[test]
fn finite_option_quotient_recurses_and_preserves_none_zero_and_binding_order() {
    use archsig_common::control::Control;
    use archsig_computation::observed::evaluate::evaluate_observed_bytes;
    use archsig_input::input::InputSources;
    let views = [
        (
            "Option<Z>",
            "if s.x then some(if s.y then 1 else 0) else none<Z>",
        ),
        (
            "Option<Option<Bool>>",
            "if s.x then some(if s.y then some(false) else none<Bool>) else none<Option<Bool>>",
        ),
        (
            "Option<(Bool,Z)>",
            "if s.x then some((s.y,0)) else none<(Bool,Z)>",
        ),
        (
            "(Option<Bool>,Z)",
            "(if s.x then some(s.y) else none<Bool>,0)",
        ),
    ];
    for (case, (ty, body)) in views.iter().enumerate() {
        let dir = law_input(
            &format!("quotient-option-recursive-{case}"),
            &format!(
                "view tagged(s:State):{ty} = {body};law optional visible(s:State):some(s.x)=some(s.x);law optional hidden(s:State,z:Bool,a:Bool):(if s.y then some(0) else none<Z>)=some(if z then 1 else 0);"
            ),
        );
        let sources = InputSources::from_bytes(
            vec![std::fs::read(dir.join("d.json")).unwrap()],
            std::fs::read(dir.join("l.law")).unwrap(),
            std::fs::read(dir.join("a.json")).unwrap(),
        );
        let result = evaluate_observed_bytes(
            sources,
            &[
                "s=solve(Pair.valid,on=@v/s,using=Pair.choose,s=@v/s)",
                "good=quotient(Pair.tagged,on=$s.domain,s=@v/s,law=Pair.visible)",
                "bad=quotient(Pair.tagged,on=$s.domain,s=@v/s,law=Pair.hidden)",
            ],
            &Control::unlimited(),
        )
        .unwrap();
        let wire = archsig_common::json::parse(result.wire().canonical().as_bytes()).unwrap();
        let answers = arr(get(&wire, "answers"));
        assert_eq!(s(get(&answers[1], "status")), "established");
        assert_eq!(s(get(&answers[2], "status")), "refuted");
        for index in [1, 2] {
            exact_fibers(
                &wire,
                index,
                vec![
                    vec![(false, false), (false, true)],
                    vec![(true, false)],
                    vec![(true, true)],
                ],
            );
        }
        let evidence = node(&wire, &arr(get(&answers[2], "evidence"))[0]);
        let data = get(get(evidence, "value"), "data");
        let points = [
            pair(get(node(&wire, get(data, "first")), "value")),
            pair(get(node(&wire, get(data, "second")), "value")),
        ];
        assert!(!points[0].0 && !points[1].0);
        assert_ne!(points[0].1, points[1].1);
        // Each family key follows the Law declaration s,z,a, including z != a.
        for (side, reference) in arr(get(data, "law_values")).iter().enumerate() {
            let family = arr(get(node(&wire, reference), "value"));
            assert_eq!(family.len(), 4);
            let mut keys = vec![];
            for entry in family {
                let entry = arr(entry);
                let key = arr(&entry[0]);
                assert_eq!(key.len(), 3);
                assert_eq!(s(&arr(&key[0])[0]), "v");
                assert_eq!(s(&arr(&key[0])[1]), "s");
                let bool_value = |n: &JNode| match n.value {
                    JValue::Bool(b) => b,
                    _ => panic!("Bool key"),
                };
                let (z, a) = (bool_value(&key[1]), bool_value(&key[2]));
                keys.push((z, a));
                let operands = arr(get(&entry[1], "some"));
                if points[side].1 {
                    assert_eq!(s(get(&operands[0], "some")), "0");
                } else {
                    assert_eq!(get(&operands[0], "none").value, JValue::Bool(true));
                }
                assert_eq!(s(get(&operands[1], "some")), if z { "1" } else { "0" });
            }
            keys.sort();
            assert_eq!(
                keys,
                vec![(false, false), (false, true), (true, false), (true, true)]
            );
        }
    }
}

#[test]
fn container_quotient_preserves_list_and_set_fibers() {
    let dir = law_input(
        "quotient-containers",
        "view ordered(s:State):List<Bool> = if s.x then list<Bool>[s.y] else list<Bool>[];view unordered(s:State):Set<Bool> = set<Bool>{s.x,s.y};law optional visible(s:State):list<Bool>[s.x]=list<Bool>[s.x];law optional hidden(s:State):list<Bool>[s.y]=list<Bool>[s.y];law optional unordered_values(s:State):set<Bool>{s.x,s.y}=set<Bool>{s.x,s.y};",
    );
    let asks = [
        "s=solve(Pair.valid,on=@v/s,using=Pair.choose,s=@v/s)",
        "list_good=quotient(Pair.ordered,on=$s.domain,s=@v/s,law=Pair.visible)",
        "list_bad=quotient(Pair.ordered,on=$s.domain,s=@v/s,law=Pair.hidden)",
        "set_good=quotient(Pair.unordered,on=$s.domain,s=@v/s,law=Pair.unordered_values)",
        "set_bad=quotient(Pair.unordered,on=$s.domain,s=@v/s,law=Pair.visible)",
    ];
    let first = execute(&dir, "out", &asks, None);
    assert_eq!(first.code, 1, "{}", first.stdout);
    let result = result_json(&dir, &first);
    let answers = arr(get(&result, "answers"));
    for index in [1, 3] {
        assert_eq!(s(get(&answers[index], "status")), "established");
    }
    for index in [2, 4] {
        assert_eq!(s(get(&answers[index], "status")), "refuted");
        let data = get(
            get(
                node(&result, &arr(get(&answers[index], "counterexamples"))[0]),
                "value",
            ),
            "data",
        );
        let points = [
            pair(get(node(&result, get(data, "first")), "value")),
            pair(get(node(&result, get(data, "second")), "value")),
        ];
        if index == 2 {
            assert!(!points[0].0 && !points[1].0);
            assert_ne!(points[0].1, points[1].1);
        } else {
            assert_eq!(points, [(false, true), (true, false)]);
        }
        let values = arr(get(data, "law_values"));
        assert_ne!(
            get(node(&result, &values[0]), "value").value,
            get(node(&result, &values[1]), "value").value
        );
    }
    for index in [1, 2] {
        exact_fibers(
            &result,
            index,
            vec![
                vec![(false, false), (false, true)],
                vec![(true, false)],
                vec![(true, true)],
            ],
        );
    }
    for index in [3, 4] {
        exact_fibers(
            &result,
            index,
            vec![
                vec![(false, false)],
                vec![(false, true), (true, false)],
                vec![(true, true)],
            ],
        );
    }
}

#[test]
fn finite_container_quotient_uses_typed_recursive_equality() {
    use archsig_common::control::Control;
    use archsig_computation::observed::evaluate::evaluate_observed_bytes;
    use archsig_input::input::InputSources;
    let separate = vec![
        vec![(false, false)],
        vec![(false, true)],
        vec![(true, false)],
        vec![(true, true)],
    ];
    let tagged = vec![
        vec![(false, false), (false, true)],
        vec![(true, false)],
        vec![(true, true)],
    ];
    let unordered = vec![
        vec![(false, false)],
        vec![(false, true), (true, false)],
        vec![(true, true)],
    ];
    // Expected classes are independently enumerated from the four (a,b) updates.
    let cases = [
        (
            "List<Bool>",
            "list<Bool>[s.x,s.y]",
            r#"["List","Bool"]"#,
            separate.clone(),
            false,
        ),
        (
            "List<Bool>",
            "if s.x then list<Bool>[s.y,s.y] else list<Bool>[s.y]",
            r#"["List","Bool"]"#,
            separate.clone(),
            false,
        ),
        (
            "List<Z>",
            "if s.x then list<Z>[if s.y then 1 else 0] else list<Z>[]",
            r#"["List","Z"]"#,
            tagged.clone(),
            false,
        ),
        (
            "List<Option<Bool>>",
            "list<Option<Bool>>[if s.x then some(s.y) else none<Bool>]",
            r#"["List",["Option","Bool"]]"#,
            tagged.clone(),
            false,
        ),
        (
            "(List<Bool>,Option<List<Z>>)",
            "(if s.x then list<Bool>[s.y] else list<Bool>[],some(list<Z>[0]))",
            r#"["Tuple",["List","Bool"],["Option",["List","Z"]]]"#,
            tagged.clone(),
            false,
        ),
        (
            "Set<Bool>",
            "set<Bool>{s.x,s.y,s.x}",
            r#"["Set","Bool"]"#,
            unordered.clone(),
            true,
        ),
        (
            "List<Set<Bool>>",
            "list<Set<Bool>>[set<Bool>{s.x,s.y}]",
            r#"["List",["Set","Bool"]]"#,
            unordered.clone(),
            true,
        ),
        (
            "Set<List<Bool>>",
            "set<List<Bool>>{list<Bool>[s.x,s.y],list<Bool>[s.y,s.x]}",
            r#"["Set",["List","Bool"]]"#,
            unordered,
            true,
        ),
        (
            "Set<List<Bool>>",
            "set<List<Bool>>{if s.x then list<Bool>[s.y,s.y] else list<Bool>[s.y]}",
            r#"["Set",["List","Bool"]]"#,
            separate,
            false,
        ),
        (
            "Option<Set<Bool>>",
            "if s.x then some(set<Bool>{}) else none<Set<Bool>>",
            r#"["Option",["Set","Bool"]]"#,
            vec![
                vec![(false, false), (false, true)],
                vec![(true, false), (true, true)],
            ],
            false,
        ),
    ];
    for (case, (ty, body, wire_type, expected, mixed)) in cases.iter().enumerate() {
        let dir = law_input(
            &format!("quotient-container-equality-{case}"),
            &format!(
                "view shape(s:State):{ty} = {body};law optional self(s:State):shape(s)=shape(s);law optional hidden(s:State,z:Bool,a:Bool):list<Bool>[s.x,s.y]=list<Bool>[z,a];"
            ),
        );
        let sources = InputSources::from_bytes(
            vec![std::fs::read(dir.join("d.json")).unwrap()],
            std::fs::read(dir.join("l.law")).unwrap(),
            std::fs::read(dir.join("a.json")).unwrap(),
        );
        let result = evaluate_observed_bytes(
            sources,
            &[
                "s=solve(Pair.valid,on=@v/s,using=Pair.choose,s=@v/s)",
                "v=evaluate(Pair.shape,s=@v/s)",
                "good=quotient(Pair.shape,on=$s.domain,s=@v/s,law=Pair.self)",
                "bad=quotient(Pair.shape,on=$s.domain,s=@v/s,law=Pair.hidden)",
            ],
            &Control::unlimited(),
        )
        .unwrap();
        let wire = archsig_common::json::parse(result.wire().canonical().as_bytes()).unwrap();
        let answers = arr(get(&wire, "answers"));
        let value = node(&wire, get(get(&answers[1], "outputs"), "value"));
        assert_eq!(
            get(value, "type").value,
            archsig_common::json::parse(wire_type.as_bytes())
                .unwrap()
                .value
        );
        assert_eq!(s(get(&answers[2], "status")), "established");
        for index in [2, 3] {
            exact_fibers(&wire, index, expected.clone());
        }
        let nontrivial = expected.iter().any(|class| class.len() > 1);
        assert_eq!(
            s(get(&answers[3], "status")),
            if nontrivial { "refuted" } else { "established" }
        );
        if nontrivial {
            let data = get(
                get(node(&wire, &arr(get(&answers[3], "evidence"))[0]), "value"),
                "data",
            );
            let points = [
                pair(get(node(&wire, get(data, "first")), "value")),
                pair(get(node(&wire, get(data, "second")), "value")),
            ];
            assert_eq!(
                points,
                if *mixed {
                    [(false, true), (true, false)]
                } else {
                    [(false, false), (false, true)]
                }
            );
            let view_values = arr(get(data, "view_values"));
            for reference in view_values {
                assert_eq!(
                    get(node(&wire, reference), "type").value,
                    get(value, "type").value
                );
            }
            for (side, reference) in arr(get(data, "law_values")).iter().enumerate() {
                let family = arr(get(node(&wire, reference), "value"));
                assert_eq!(family.len(), 4);
                let mut keys = vec![];
                for entry in family {
                    let entry = arr(entry);
                    let key = arr(&entry[0]);
                    assert_eq!(key.len(), 3);
                    let b = |v: &JNode| match v.value {
                        JValue::Bool(b) => b,
                        _ => panic!("Bool"),
                    };
                    let (z, a) = (b(&key[1]), b(&key[2]));
                    keys.push((z, a));
                    let sides = arr(get(&entry[1], "some"));
                    assert_eq!(pair(&sides[0]), points[side]);
                    assert_eq!(pair(&sides[1]), (z, a));
                }
                keys.sort();
                assert_eq!(
                    keys,
                    vec![(false, false), (false, true), (true, false), (true, true)]
                );
            }
        }
    }
}

#[test]
fn finite_container_fiber_comparison_propagates_signal_stops() {
    use archsig_common::control::{Checkpoint, Control};
    use archsig_computation::observed::evaluate::evaluate_observed_bytes;
    use archsig_input::{input::InputSources, result::Signal};
    use std::{cell::Cell, rc::Rc};
    let dir = law_input(
        "quotient-container-stop",
        "view shape(s:State):Set<Bool> = set<Bool>{s.x,s.y};",
    );
    for signal in [Signal::Int, Signal::Term] {
        let count = Rc::new(Cell::new(0));
        let seen = count.clone();
        let hit = Rc::new(Cell::new(false));
        let stopped = hit.clone();
        let control = Control::new(move |point| {
            if point == Checkpoint::Quotient {
                seen.set(seen.get() + 1);
            }
            // Four candidate evaluations precede the first actual fiber comparison.
            if seen.get() == 5 && point == Checkpoint::FiniteIteration {
                stopped.set(true);
                Some(signal)
            } else {
                None
            }
        });
        let sources = InputSources::from_bytes(
            vec![std::fs::read(dir.join("d.json")).unwrap()],
            std::fs::read(dir.join("l.law")).unwrap(),
            std::fs::read(dir.join("a.json")).unwrap(),
        );
        let result = evaluate_observed_bytes(
            sources,
            &[
                "s=solve(Pair.valid,on=@v/s,using=Pair.choose,s=@v/s)",
                "q=quotient(Pair.shape,on=$s.domain,s=@v/s)",
                "later=evaluate(Pair.last,s=@v/s)",
            ],
            &control,
        )
        .unwrap();
        assert!(hit.get());
        assert_eq!(count.get(), 5);
        let wire = archsig_common::json::parse(result.wire().canonical().as_bytes()).unwrap();
        let answers = arr(get(&wire, "answers"));
        assert_eq!(s(get(&answers[0], "status")), "established");
        assert!(has(get(&answers[0], "outputs"), "solutions"));
        assert!(!has(get(&answers[1], "outputs"), "quotient"));
        for answer in &answers[1..] {
            assert_eq!(s(get(answer, "status")), "undetermined");
            let reason = arr(get(answer, "reasons"))
                .iter()
                .find(|r| s(get(r, "code")) == "cancelled")
                .unwrap();
            let details = get(reason, "details");
            assert_eq!(s(get(details, "signal")), signal.wire());
        }
    }
}

#[path = "common/quotient_data.rs"]
mod data_tests;

#[path = "common/atomic_bool_quotient.rs"]
mod atomic_bool;
