//! R2 の在庫引当、会計、由来比較を一つの公開 run で検査する。
use crate::common::architecture_environment::owned;
use crate::common::cli::*;
use archsig_common::{
    canonical::{Json, JsonObject},
    json::JNode,
};

const LAW: &str = include_str!("fixtures/r2-backing/laws.law");
const QUERIES: &str = include_str!("fixtures/r2-backing/queries.txt");

fn referenced<'a>(result: &'a JNode, reference: &JNode) -> &'a JNode {
    arr(get(result, "nodes"))
        .iter()
        .find(|node| s(get(node, "id")) == s(get(reference, "node")))
        .unwrap()
}

#[test]
fn unsupported_r2_backing_blocks_only_its_consumer() {
    let dir = workdir("r2-backing");
    // An existential over symbolic changes is outside the supported conjunction.
    let law = LAW.replacen("forall b in Pool.Cell", "exists b in Pool.Cell", 1);
    for (name, contents) in [
        (
            "definitions.json",
            include_str!("fixtures/r2-backing/definitions.json"),
        ),
        ("laws.law", law.as_str()),
        (
            "archmap.json",
            include_str!("fixtures/r2-backing/archmap.json"),
        ),
    ] {
        std::fs::write(dir.join(name), contents).unwrap();
    }
    let mut args = vec![
        "run",
        "--atom-definition",
        "definitions.json",
        "--law",
        "laws.law",
        "--archmap",
        "archmap.json",
        "--out",
        "first",
    ];
    for query in QUERIES.lines() {
        args.extend(["--ask", query]);
    }
    let run = run_binary(&dir, &args);
    assert_eq!(run.code, 2, "{}{}", run.stdout, run.stderr);
    let result = result_json(&dir, &run);
    assert_eq!(s(get(&result, "status")), "partial");
    let answers = arr(get(&result, "answers"));
    assert_eq!(
        answers
            .iter()
            .map(|a| (s(get(a, "id")), s(get(a, "status"))))
            .collect::<Vec<_>>(),
        [
            ("before", "established"),
            ("backing", "undetermined"),
            ("consumer", "undetermined"),
            ("accounting", "established"),
            ("edgeA", "established"),
            ("edgeB", "established"),
            ("sameEdge", "refuted"),
        ]
    );
    let [reason] = arr(get(&answers[1], "reasons")) else {
        panic!("Backing の理由は一つ")
    };
    assert_eq!(s(get(reason, "code")), "unsupported_algorithm");
    let details = get(reason, "details");
    assert_eq!(s(get(details, "method")), "rational_change_quantification");
    assert_eq!(s(get(details, "question")), "solve");
    let [ty] = arr(get(details, "operand_types")) else {
        panic!("係数型は一つ")
    };
    assert_eq!(s(ty), "Q");
    let location = get(reason, "location");
    assert_eq!(s(get(location, "input")), "law");
    let [lo, hi] = arr(get(location, "span")) else {
        panic!("元の量化式の範囲")
    };
    assert_eq!(
        &law[num(lo) as usize..num(hi) as usize],
        concat!(
            "exists b in Pool.Cell[w] . b.quantity>=rat(0,1) and\n",
            "    (not(b.stock in b.claim.eligible) implies b.quantity=rat(0,1)) and ",
            "b.stock.quantityUnit=b.claim.quantityUnit"
        )
    );
    let consumer = arr(get(&answers[2], "reasons"));
    assert!(consumer.iter().any(|r| {
        s(get(r, "code")) == "dependency_blocked"
            && s(get(get(r, "details"), "request")) == "backing"
    }));
    assert!(consumer.iter().any(|r| r.value == reason.value));
    let [counterexample] = arr(get(&answers[6], "counterexamples")) else {
        panic!("由来の異なる二つの辺が反例になる")
    };
    let counterexample = get(get(referenced(&result, counterexample), "value"), "data");
    for (side, origin) in [("left", "sourceA"), ("right", "sourceB")] {
        let edge = arr(get(referenced(&result, get(counterexample, side)), "value"));
        assert_eq!(s(&edge[1]), origin);
        let q = arr(get(&edge[3], "some"));
        assert_eq!((s(&q[0]), s(&q[1])), ("1", "32"));
    }

    args[8] = "rechecked";
    args.extend(["--reuse", "first"]);
    let run = run_binary(&dir, &args);
    assert_eq!(run.code, 2, "{}{}", run.stdout, run.stderr);
    let rechecked = result_json(&dir, &run);
    assert!(warnings(&rechecked).is_empty());
    for key in ["answers", "nodes", "issues"] {
        assert_eq!(get(&result, key).value, get(&rechecked, key).value);
    }
}

#[test]
fn r2_backing_projects_one_quantity_per_owned_cell() {
    use archsig_common::json::JValue;

    let dir = workdir("r2-backing-projection");
    let law = LAW.replace(
        " view claimLoad",
        concat!(
            " view eligibleLoad(c:Pool.Claim):Q=sum(list{b.quantity | b in Pool.Cell[c.owner] where b.claim=c and b.stock in c.eligible});\n",
            " view copies(b:Pool.Cell):Q=sum(list{x.quantity | x in list<Pool.Cell>[b,b]});\n",
            " view empty(c:Pool.Claim):Q=sum(list{b.quantity | b in Pool.Cell[c.owner] where false});\n",
            " view missingQuantity(c:Pool.Claim):Q=sum(list{b.quantity | b in Pool.Cell[c.owner] where b.claim=c});\n",
            " view missingFilter(c:Pool.Claim):Q=sum(list{rat(1,2) | b in Pool.Cell[c.owner] where b.claim=c and b.stock in c.eligible});\n",
            " view claimLoad",
        ),
    );
    let map = include_str!("fixtures/r2-backing/archmap.json")
        .lines()
        .filter(|line| {
            !line.contains(r#""id": "overlapFeasible.B2.Z.quantity""#)
                && !line.contains(r#""id": "overlapFeasible.B2.Y.stock""#)
        })
        .map(|line| {
            if ["B1.X", "B1.Y"]
                .iter()
                .any(|cell| line.contains(&format!(r#""id": "overlapFeasible.{cell}.quantity""#)))
            {
                line.replace(r#"["0", "1"]"#, r#"["1", "2"]"#)
            } else if line.contains(r#""id": "overlapFeasible.B1.Z.quantity""#) {
                line.replace(r#"["0", "1"]"#, r#"["11", "2"]"#)
            } else {
                line.to_owned()
            }
        })
        .collect::<Vec<_>>()
        .join("\n");
    for (name, contents) in [
        (
            "definitions.json",
            include_str!("fixtures/r2-backing/definitions.json"),
        ),
        ("laws.law", &law),
        ("archmap.json", &map),
    ] {
        std::fs::write(dir.join(name), contents).unwrap();
    }
    let mut args = vec![
        "run",
        "--atom-definition",
        "definitions.json",
        "--law",
        "laws.law",
        "--archmap",
        "archmap.json",
        "--out",
        "first",
    ];
    for query in [
        "load=evaluate(Backing.eligibleLoad,c=@fixture/overlapFeasible.B1)",
        "repeat=evaluate(Backing.copies,b=@fixture/overlapFeasible.B1.X)",
        "empty=evaluate(Backing.empty,c=@fixture/overlapFeasible.B1)",
        "quantity=evaluate(Backing.missingQuantity,c=@fixture/overlapFeasible.B2)",
        "filter=evaluate(Backing.missingFilter,c=@fixture/overlapFeasible.B2)",
    ] {
        args.extend(["--ask", query]);
    }
    let run = run_binary(&dir, &args);
    assert_eq!(run.code, 2, "{}{}", run.stdout, run.stderr);
    let result = result_json(&dir, &run);
    let answers = arr(get(&result, "answers"));
    for (answer, numerator) in answers[..3].iter().zip(["1", "1", "0"]) {
        assert_eq!(s(get(answer, "status")), "established");
        let value = referenced(&result, get(get(answer, "outputs"), "value"));
        assert_eq!(s(get(value, "type")), "Q");
        let [n, d] = arr(get(value, "value")) else {
            panic!("Q numerator and denominator");
        };
        assert_eq!((s(n), s(d)), (numerator, "1"));
    }
    for (answer, subject, field) in [
        (&answers[3], "overlapFeasible.B2.Z", "Pool.Cell.quantity"),
        (&answers[4], "overlapFeasible.B2.Y", "Pool.Cell.stock"),
    ] {
        assert_eq!(s(get(answer, "status")), "undetermined");
        assert!(
            matches!(&get(answer, "outputs").value, JValue::Obj(values) if !values.iter().any(|(key, _)| key == "value"))
        );
        assert!(arr(get(answer, "reasons")).iter().any(|reason| {
            s(get(reason, "code")) == "missing_observation"
                && arr(get(reason, "missing")).iter().any(|fact| {
                    s(get(fact, "snapshot")) == "fixture"
                        && s(get(fact, "subject")) == subject
                        && s(get(fact, "field")) == field
                })
        }));
    }
    args[8] = "rechecked";
    args.extend(["--reuse", "first"]);
    let rechecked = run_binary(&dir, &args);
    assert_eq!(
        rechecked.code, 2,
        "{}{}",
        rechecked.stdout, rechecked.stderr
    );
    let rechecked = result_json(&dir, &rechecked);
    assert!(warnings(&rechecked).is_empty());
    for key in ["answers", "nodes", "issues"] {
        assert_eq!(get(&result, key).value, get(&rechecked, key).value);
    }
}

const POLY_MAP: &[u8] = include_bytes!("fixtures/r2-backing-polyhedron/archmap.json");
const POLY_LAW: &str = include_str!("fixtures/r2-backing-polyhedron/laws.law");
const POLY_QUERIES: &str = include_str!("fixtures/r2-backing-polyhedron/queries.txt");

fn fields(json: &mut Json) -> &mut JsonObject {
    let Json::Obj(fields) = json else {
        panic!("JSON object")
    };
    fields
}

fn items(json: &mut Json) -> &mut Vec<Json> {
    let Json::Arr(items) = json else {
        panic!("JSON array")
    };
    items
}

fn polyhedron_inputs(dir: &std::path::Path, case: &str) -> Json {
    let mut map = owned(&archsig_common::json::parse(POLY_MAP).unwrap());
    let snapshot = &mut items(fields(&mut map).get_mut("snapshots").unwrap())[0];
    for (group, key) in [("subjects", "id"), ("atoms", "subject")] {
        items(fields(snapshot).get_mut(group).unwrap()).retain_mut(|row| {
            let Json::Str(id) = &fields(row)[key] else {
                panic!("R2 identity");
            };
            id.split('.').next() == Some(case)
        });
    }
    std::fs::write(
        dir.join("definitions.json"),
        include_bytes!("fixtures/r2-backing-polyhedron/definitions.json"),
    )
    .unwrap();
    std::fs::write(dir.join("laws.law"), POLY_LAW).unwrap();
    std::fs::write(dir.join("archmap.json"), map.canonical()).unwrap();
    map
}

fn polyhedron_run(dir: &std::path::Path, ask: &str, out: &str, reuse: Option<&str>) -> BinaryRun {
    polyhedron_asks(dir, &[ask], out, reuse)
}

fn polyhedron_asks(
    dir: &std::path::Path,
    asks: &[&str],
    out: &str,
    reuse: Option<&str>,
) -> BinaryRun {
    let mut args = vec![
        "run",
        "--atom-definition",
        "definitions.json",
        "--law",
        "laws.law",
        "--archmap",
        "archmap.json",
        "--out",
        out,
    ];
    for ask in asks {
        args.extend(["--ask", ask]);
    }
    if let Some(reuse) = reuse {
        args.extend(["--reuse", reuse]);
    }
    run_binary(dir, &args)
}

fn solution<'a>(result: &'a JNode, field: &str) -> &'a JNode {
    let answer = &arr(get(result, "answers"))[0];
    get(
        referenced(result, get(get(answer, "outputs"), field)),
        "value",
    )
}

fn certificate(result: &JNode) -> &JNode {
    let representation = get(solution(result, "solutions"), "representation");
    assert_eq!(s(get(representation, "kind")), "rational_polyhedron");
    let node = referenced(result, get(representation, "certificate"));
    assert_eq!(s(get(node, "type")), "Evidence");
    let proof = get(node, "value");
    assert_eq!(s(get(proof, "kind")), "rational_polyhedron");
    let proof = get(proof, "data");
    for key in ["equalities", "rhs", "inequalities", "upper_bounds"] {
        assert_eq!(get(representation, key).value, get(proof, key).value);
    }
    proof
}

fn coordinates<'a>(result: &'a JNode, vector: &JNode) -> Vec<(&'a str, &'a str)> {
    arr(get(get(referenced(result, vector), "value"), "coordinates"))
        .iter()
        .map(|reference| {
            let scalar = referenced(result, reference);
            assert_eq!(s(get(scalar, "type")), "Q");
            let [n, d] = arr(get(scalar, "value")) else {
                panic!("Q")
            };
            (s(n), s(d))
        })
        .collect()
}

#[test]
fn r2_exact_backing_solves_all_four_frozen_constraint_sets() {
    let asks: Vec<_> = POLY_QUERIES.lines().collect();
    assert_eq!(asks.len(), 4);
    for (ask, (case, exit, outcome)) in asks.into_iter().zip([
        ("overlapFeasible", 0, "unique"),
        ("overlapInsufficient", 1, "empty"),
        ("threeUsesExact", 0, "unique"),
        ("threeUsesMicroShortage", 1, "empty"),
    ]) {
        assert_eq!(ask.split_once('=').unwrap().0, case);
        let dir = workdir(case);
        polyhedron_inputs(&dir, case);
        let run = polyhedron_run(&dir, ask, "out", None);
        assert_eq!(run.code, exit, "{}{}", run.stdout, run.stderr);
        let result = result_json(&dir, &run);
        assert_eq!(s(get(&result, "status")), "complete");
        let answer = &arr(get(&result, "answers"))[0];
        assert_eq!(
            s(get(answer, "status")),
            if exit == 0 { "established" } else { "refuted" }
        );
        let proof = certificate(&result);
        assert_eq!(s(get(proof, "outcome")), outcome);
        if exit == 1 {
            assert!(
                coordinates(&result, get(proof, "contradiction"))
                    .iter()
                    .all(|(n, _)| !n.starts_with('-'))
            );
        }
        if case == "threeUsesExact" {
            let point = coordinates(&result, get(proof, "point"));
            let instances = arr(get(solution(&result, "domain"), "instances"));
            assert_eq!(instances.len(), 12);
            assert_eq!(arr(get(proof, "coordinate_bounds")).len(), 12);
            for row in instances {
                let id = s(&arr(get(referenced(&result, get(row, "subject")), "value"))[1]);
                let [position] = arr(get(row, "positions")) else {
                    panic!("one change parameter")
                };
                let expected = match id {
                    "threeUsesExact.M1.N" => ("1", "4"),
                    "threeUsesExact.Sale.N" => ("1", "8"),
                    "threeUsesExact.Transfer.N" => ("3", "16"),
                    "threeUsesExact.M2.N" => ("7", "16"),
                    _ => ("0", "1"),
                };
                assert_eq!(point[num(position) as usize], expected, "{id}");
            }

            let rechecked = polyhedron_run(&dir, ask, "rechecked", Some("out"));
            assert_eq!(rechecked.code, exit);
            let rechecked = result_json(&dir, &rechecked);
            assert!(warnings(&rechecked).is_empty());
            for key in ["answers", "nodes", "issues"] {
                assert_eq!(get(&result, key).value, get(&rechecked, key).value);
            }

            // Change each saved constraint component or the owner-scoped instance
            // order while keeping the checked inputs unchanged.
            for (tag, target, field) in [
                (
                    "coefficients",
                    referenced(&result, get(proof, "inequalities")),
                    "columns",
                ),
                (
                    "bounds",
                    referenced(&result, get(proof, "upper_bounds")),
                    "coordinates",
                ),
                (
                    "instances",
                    referenced(&result, get(get(answer, "outputs"), "domain")),
                    "instances",
                ),
            ] {
                let mut changed = owned(&result);
                let id = s(get(target, "id"));
                let target = items(fields(&mut changed).get_mut("nodes").unwrap())
                    .iter_mut()
                    .find(|node| matches!(node, Json::Obj(fields) if fields["id"] == Json::str(id)))
                    .unwrap();
                let values = items(
                    fields(fields(target).get_mut("value").unwrap())
                        .get_mut(field)
                        .unwrap(),
                );
                let values = if field == "columns" {
                    items(&mut values[0])
                } else {
                    values
                };
                let index = values.iter().position(|value| value != &values[0]).unwrap();
                values.swap(0, index);
                let saved = format!("changed-{tag}");
                std::fs::create_dir(dir.join(&saved)).unwrap();
                std::fs::write(dir.join(&saved).join("result.json"), changed.canonical()).unwrap();
                let rejected = polyhedron_run(&dir, ask, &format!("rejected-{tag}"), Some(&saved));
                assert_eq!(rejected.code, exit);
                let rejected = result_json(&dir, &rejected);
                assert!(!warnings(&rejected).is_empty(), "{tag}");
                for key in ["answers", "nodes", "issues"] {
                    assert_eq!(get(&result, key).value, get(&rejected, key).value);
                }
            }
        }
    }
}

#[test]
fn rational_backing_reuse_rejects_a_different_registered_owner() {
    let dir = workdir("r2-polyhedron-owner");
    polyhedron_inputs(&dir, "threeUsesExact");
    // Keep the alternate owner registered and well typed in the current input.
    std::fs::write(dir.join("archmap.json"), POLY_MAP).unwrap();
    let ask = POLY_QUERIES.lines().nth(2).unwrap();
    let run = polyhedron_run(&dir, ask, "first", None);
    assert_eq!(run.code, 0, "{}{}", run.stdout, run.stderr);
    let first = result_json(&dir, &run);
    let domain = solution(&first, "domain");
    let root = get(
        get(referenced(&first, get(domain, "base")), "value"),
        "root",
    );
    let id = s(get(root, "node"));
    let mut changed = owned(&first);
    let node = items(fields(&mut changed).get_mut("nodes").unwrap())
        .iter_mut()
        .find(|node| matches!(node, Json::Obj(fields) if fields["id"] == Json::str(id)))
        .unwrap();
    let identity = items(fields(node).get_mut("value").unwrap());
    assert_eq!(identity[1], Json::str("threeUsesExact"));
    identity[1] = Json::str("threeUsesMicroShortage");
    std::fs::create_dir(dir.join("changed")).unwrap();
    std::fs::write(dir.join("changed/result.json"), changed.canonical()).unwrap();
    let replay = polyhedron_run(&dir, ask, "replayed", Some("changed"));
    assert_eq!(replay.code, 0, "{}{}", replay.stdout, replay.stderr);
    let replay = result_json(&dir, &replay);
    assert!(!warnings(&replay).is_empty());
    for key in ["answers", "nodes", "issues"] {
        assert_eq!(get(&first, key).value, get(&replay, key).value);
    }
}

#[test]
fn rational_backing_distinguishes_nonunique_repair_and_missing_capacity() {
    let case = "overlapFeasible";
    let dir = workdir("r2-polyhedron-decisions");
    let map = polyhedron_inputs(&dir, case);
    let solve = POLY_QUERIES.lines().next().unwrap();
    let repair = solve.replacen("=solve(", "=repair(", 1);

    let mut slack = map.clone();
    let snapshot = &mut items(fields(&mut slack).get_mut("snapshots").unwrap())[0];
    let atoms = items(fields(snapshot).get_mut("atoms").unwrap());
    let x_capacity = Json::str("overlapFeasible.X.available");
    let stock = atoms
        .iter_mut()
        .find(|node| matches!(node, Json::Obj(fields) if fields["id"] == x_capacity))
        .unwrap();
    fields(stock).insert(
        "value".into(),
        Json::Arr(vec![Json::str("6"), Json::str("1")]),
    );
    std::fs::write(dir.join("archmap.json"), slack.canonical()).unwrap();
    let run = polyhedron_run(&dir, &repair, "multiple", None);
    assert_eq!(run.code, 1, "{}{}", run.stdout, run.stderr);
    let result = result_json(&dir, &run);
    let proof = certificate(&result);
    assert_eq!(s(get(proof, "outcome")), "multiple");
    assert_ne!(
        coordinates(&result, get(proof, "point")),
        coordinates(&result, get(proof, "second"))
    );
    let answer = &arr(get(&result, "answers"))[0];
    assert_eq!(s(get(answer, "status")), "refuted");
    let outputs = get(answer, "outputs");
    assert!(!has(outputs, "assignment"));
    assert!(!has(outputs, "object"));
    assert_eq!(
        s(get(
            get(referenced(&result, get(outputs, "existence")), "judgment"),
            "status"
        )),
        "established"
    );

    let mut missing = map;
    let snapshot = &mut items(fields(&mut missing).get_mut("snapshots").unwrap())[0];
    items(fields(snapshot).get_mut("atoms").unwrap())
        .retain(|node| !matches!(node, Json::Obj(fields) if fields["id"] == x_capacity));
    std::fs::write(dir.join("archmap.json"), missing.canonical()).unwrap();
    let run = polyhedron_run(&dir, solve, "missing", None);
    assert_eq!(run.code, 2, "{}{}", run.stdout, run.stderr);
    let result = result_json(&dir, &run);
    let answer = &arr(get(&result, "answers"))[0];
    assert_eq!(s(get(answer, "status")), "undetermined");
    assert!(!has(get(answer, "outputs"), "solutions"));
    let [reason] = arr(get(answer, "reasons")) else {
        panic!("missing capacity only")
    };
    assert_eq!(s(get(reason, "code")), "missing_observation");
    let [fact] = arr(get(reason, "missing")) else {
        panic!("exact missing capacity")
    };
    assert_eq!(s(get(fact, "snapshot")), "fixture");
    assert_eq!(s(get(fact, "subject")), "overlapFeasible.X");
    assert_eq!(s(get(fact, "field")), "Pool.Stock.available");
}

#[test]
fn rational_backing_stops_before_unchecked_solutions_and_saves_the_completed_prefix() {
    use archsig::run::{CheckArgs, FileIo, RunArgs, Signals, run_requests};
    use archsig_common::control::{Checkpoint, Control, Signal};
    use std::{cell::Cell, rc::Rc};

    #[derive(Default)]
    struct NoSignal(usize);
    impl Signals for NoSignal {
        fn freeze(&mut self) -> Option<Signal> {
            self.0 += 1;
            None
        }
    }

    let dir = workdir("r2-polyhedron-stop");
    let ask = POLY_QUERIES.lines().next().unwrap();
    let before = "before=evaluate(Backing.claimLoad,c=@fixture/overlapFeasible.B1)";
    let after = "after=evaluate(Backing.claimLoad,c=@fixture/overlapFeasible.B2)";
    let mut slack = polyhedron_inputs(&dir, "overlapFeasible");
    let snapshot = &mut items(fields(&mut slack).get_mut("snapshots").unwrap())[0];
    let stock = items(fields(snapshot).get_mut("atoms").unwrap()).iter_mut()
        .find(|node| matches!(node, Json::Obj(fields) if fields["id"] == Json::str("overlapFeasible.X.available")))
        .unwrap();
    fields(stock).insert(
        "value".into(),
        Json::Arr(vec![Json::str("6"), Json::str("1")]),
    );
    std::fs::write(dir.join("archmap.json"), slack.canonical()).unwrap();
    let repair = ask.replacen("=solve(", "=repair(", 1);
    for (checkpoint, at, ask, out) in [
        (
            Checkpoint::RationalPolyhedronElimination,
            1,
            ask,
            "elimination",
        ),
        (
            Checkpoint::ChangeWitness,
            2,
            repair.as_str(),
            "second-witness",
        ),
    ] {
        let args = RunArgs {
            inputs: CheckArgs {
                atom_definitions: vec![dir.join("definitions.json")],
                law: dir.join("laws.law"),
                archmap: Some(dir.join("archmap.json")),
                out: Some(dir.join(out)),
            },
            asks: [before, ask, after].map(str::to_owned).to_vec(),
            reuse: None,
        };
        let seen = Rc::new(Cell::new(0));
        let count = Rc::clone(&seen);
        let control = Control::new(move |point| {
            if point == checkpoint {
                count.set(count.get() + 1);
            }
            (count.get() == at).then_some(Signal::Term)
        });
        let mut signals = NoSignal::default();
        let outcome = run_requests(&mut FileIo, &mut signals, &args, &control);
        assert_eq!(outcome.exit_code, 143, "{}", outcome.receipt());
        assert_eq!(seen.get(), at);
        assert_eq!(signals.0, 1);
        let saved = std::fs::read(dir.join(out).join("result.json")).unwrap();
        let result = archsig_common::json::parse(&saved).unwrap();
        assert_eq!(s(get(&result, "status")), "interrupted");
        let answers = arr(get(&result, "answers"));
        assert_eq!(s(get(&answers[0], "id")), "before");
        assert_eq!(s(get(&answers[0], "status")), "established");
        let value = referenced(&result, get(get(&answers[0], "outputs"), "value"));
        let [n, d] = arr(get(value, "value")) else {
            panic!("completed exact Q answer");
        };
        assert_eq!((s(n), s(d)), ("0", "1"));
        assert_eq!(answers.len(), 3);
        for (answer, id) in answers[1..].iter().zip(["overlapFeasible", "after"]) {
            assert_eq!(s(get(answer, "id")), id);
            assert_eq!(s(get(answer, "status")), "undetermined");
            assert!(
                matches!(&get(answer, "outputs").value, archsig_common::json::JValue::Obj(values) if values.is_empty())
            );
            let [reason] = arr(get(answer, "reasons")) else {
                panic!("signal reason")
            };
            assert_eq!(s(get(reason, "code")), "cancelled");
            assert_eq!(s(get(get(reason, "details"), "signal")), "SIGTERM");
        }
        assert!(arr(get(&result, "nodes")).iter().all(|node|
            !matches!(&get(node, "type").value, archsig_common::json::JValue::Str(ty) if ty == "SolutionSet")));
    }
}

#[test]
fn rational_backing_keeps_unsupported_quotients_and_independent_answers_separate() {
    let ask = POLY_QUERIES.lines().nth(1).unwrap();
    let dir = workdir("r2-polyhedron-quotient");
    polyhedron_inputs(&dir, "overlapInsufficient");
    let asks = [
        ask,
        "q=quotient(Backing.stockLoad,on=$overlapInsufficient.solutions,s=@fixture/overlapInsufficient.X)",
        "domain=quotient(Backing.stockLoad,on=$overlapInsufficient.domain,s=@fixture/overlapInsufficient.X)",
        "independent=evaluate(Backing.stockLoad,s=@fixture/overlapInsufficient.X)",
    ];
    let first = polyhedron_asks(&dir, &asks, "first", None);
    assert_eq!(first.code, 2, "{}{}", first.stdout, first.stderr);
    let result = result_json(&dir, &first);
    let [solve, quotient, domain, independent] = arr(get(&result, "answers")) else {
        panic!("all requests remain");
    };
    assert_eq!(s(get(solve, "status")), "refuted");
    assert_eq!(s(get(certificate(&result), "outcome")), "empty");
    assert_eq!(s(get(quotient, "status")), "undetermined");
    assert!(!has(get(quotient, "outputs"), "quotient"));
    let [reason] = arr(get(quotient, "reasons")) else {
        panic!("typed quotient reason")
    };
    assert_eq!(s(get(reason, "code")), "unsupported_algorithm");
    assert_eq!(
        s(get(get(reason, "details"), "method")),
        "rational_polyhedron_quotient"
    );
    assert_eq!(s(get(domain, "status")), "established");
    assert_eq!(s(get(independent, "status")), "established");
    let replay = polyhedron_asks(&dir, &asks, "same", Some("first"));
    assert_eq!(replay.code, 2, "{}{}", replay.stdout, replay.stderr);
    let replay = result_json(&dir, &replay);
    assert!(warnings(&replay).is_empty());
    for key in ["answers", "nodes", "issues"] {
        assert_eq!(get(&result, key).value, get(&replay, key).value);
    }
}

#[test]
fn rational_backing_reports_missing_references_units_and_unsupported_disjunction() {
    let case = "overlapFeasible";
    let dir = workdir("r2-polyhedron-scope");
    let map = polyhedron_inputs(&dir, case);
    let ask = POLY_QUERIES.lines().next().unwrap();
    let independent = "independent=evaluate(Backing.stockLoad,s=@fixture/overlapFeasible.Y)";
    for (atom, subject, field) in [
        ("B1.eligible", "B1", "Pool.Claim.eligible"),
        ("B1.X.stock", "B1.X", "Pool.Cell.stock"),
        ("B1.X.owner", "B1.X", "Pool.Cell.owner"),
        ("X.quantityUnit", "X", "Pool.Stock.quantityUnit"),
        ("B1.quantity", "B1", "Pool.Claim.quantity"),
    ] {
        let mut missing = map.clone();
        let snapshot = &mut items(fields(&mut missing).get_mut("snapshots").unwrap())[0];
        let atom = Json::str(format!("{case}.{atom}"));
        items(fields(snapshot).get_mut("atoms").unwrap())
            .retain(|node| !matches!(node, Json::Obj(fields) if fields["id"] == atom));
        std::fs::write(dir.join("archmap.json"), missing.canonical()).unwrap();
        let run = polyhedron_asks(&dir, &[ask, independent], &format!("missing-{field}"), None);
        assert_eq!(run.code, 2, "{}{}", run.stdout, run.stderr);
        let result = result_json(&dir, &run);
        let [solve, independent] = arr(get(&result, "answers")) else {
            panic!("retained answers")
        };
        assert_eq!(s(get(solve, "status")), "undetermined");
        assert_eq!(s(get(independent, "status")), "established");
        assert!(!has(get(solve, "outputs"), "solutions"));
        let [reason] = arr(get(solve, "reasons")) else {
            panic!("only missing observations")
        };
        assert_eq!(s(get(reason, "code")), "missing_observation");
        assert!(arr(get(reason, "missing")).iter().any(|fact| {
            s(get(fact, "snapshot")) == "fixture"
                && s(get(fact, "subject")) == format!("{case}.{subject}")
                && s(get(fact, "field")) == field
        }));
    }
    std::fs::write(dir.join("archmap.json"), map.canonical()).unwrap();
    let law = POLY_LAW.replacen(
        "b.quantity>=rat(0,1)",
        "(b.quantity>=rat(1,1) or b.quantity<=rat(0,1))",
        1,
    );
    std::fs::write(dir.join("laws.law"), law).unwrap();
    let run = polyhedron_asks(&dir, &[ask, independent], "unsupported", None);
    assert_eq!(run.code, 2, "{}{}", run.stdout, run.stderr);
    let result = result_json(&dir, &run);
    let [solve, independent] = arr(get(&result, "answers")) else {
        panic!("retained answers")
    };
    assert_eq!(s(get(independent, "status")), "established");
    assert_eq!(s(get(solve, "status")), "undetermined");
    assert!(!has(get(solve, "outputs"), "solutions"));
    let [reason] = arr(get(solve, "reasons")) else {
        panic!("only unsupported")
    };
    assert_eq!(s(get(reason, "code")), "unsupported_algorithm");
}

#[test]
fn rational_backing_separates_guard_observation_from_unsupported_change_condition() {
    let case = "overlapFeasible";
    let dir = workdir("r2-polyhedron-guard");
    let mut map = polyhedron_inputs(&dir, case);
    let ask = POLY_QUERIES.lines().next().unwrap();
    let snapshot = &mut items(fields(&mut map).get_mut("snapshots").unwrap())[0];
    let atoms = items(fields(snapshot).get_mut("atoms").unwrap());
    atoms.retain(|node| !matches!(node, Json::Obj(fields) if fields["id"] == Json::str("overlapFeasible.X.available")));
    std::fs::write(dir.join("archmap.json"), map.canonical()).unwrap();
    let disjunction = "(b.quantity>=rat(10,1) or b.quantity<=rat(0,1))";
    let dead_read = POLY_LAW.replacen(
        "stockLoad(s)<=s.available",
        "stockLoad(s)<=rat(5,1) and (false implies s.available>=rat(0,1))",
        1,
    );
    let known_bound = POLY_LAW.replacen("stockLoad(s)<=s.available", "stockLoad(s)<=rat(5,1)", 1);
    let nonnegative = "b.quantity>=rat(0,1)";
    let direct_equality = known_bound.replacen(
        "legal(w:Pool.World):",
        "legal(w:Pool.World,x:Pool.Stock): stockLoad(x)=x.available and",
        1,
    );
    for (out, law, codes) in [
        ("direct-equality", direct_equality, &["missing_observation"][..]),
        ("change-guard", known_bound.replacen("q:Q)=b with",
            "q:Q) when q=b.stock.available=b with", 1), &["missing_observation"][..]),
        ("unsupported-guard-bound", known_bound.replacen("q:Q)=b with",
            "q:Q) when q<=b.stock.available=b with", 1),
            &["missing_observation", "unsupported_algorithm"][..]),
        ("fixed-quantified-guard", known_bound.replacen("q:Q)=b with",
            "q:Q) when (forall n in list<Q>[b.stock.available] . n>=rat(0,1))=b with", 1),
            &["missing_observation"][..]),
        ("fixed-existential", known_bound.replacen(nonnegative,
            "(b.quantity>=rat(0,1) and (exists n in list<Q>[b.stock.available] . n>=rat(0,1)))", 1),
            &["missing_observation"][..]),
        ("change-offset", known_bound.replacen("quantity=q", "quantity=q+b.stock.available", 1),
            &["missing_observation"][..]),
        ("change-branch", known_bound.replacen("quantity=q",
            "quantity=if b.stock.available>=rat(0,1) then q else -q", 1),
            &["missing_observation"][..]),
        ("let-product", known_bound.replacen(nonnegative,
            "(let weighted=b.quantity*b.stock.available in weighted>=rat(0,1))", 1),
            &["missing_observation"][..]),
        ("view-argument", known_bound.replacen(" law required legal",
            " view keep(q:Q):Q=q;\n law required legal", 1)
            .replacen(nonnegative, "keep(b.quantity*b.stock.available)>=rat(0,1)", 1),
            &["missing_observation"][..]),
        ("let-implication", known_bound.replacen(nonnegative,
            "(let cap=b.stock.available in (cap>=rat(0,1) implies b.quantity>=rat(0,1)))", 1),
            &["missing_observation"][..]),
        ("let-law-guard", known_bound.replacen("legal(w:Pool.World):",
            "legal(w:Pool.World) when (forall b in Pool.Cell[w] . let cap=b.stock.available in cap>=rat(0,1)):", 1),
            &["missing_observation"][..]),
        ("comprehension-domain", known_bound.replacen("legal(w:Pool.World):",
            "legal(w:Pool.World): forall flag in list{true | t in Pool.Cell[w] where t.quantity-t.quantity+t.stock.available>=rat(0,1)} .", 1),
            &["missing_observation"][..]),
        ("sum-coefficient", known_bound.replacen(nonnegative,
            "sum(list<Q>[b.quantity*b.stock.available])>=rat(0,1)", 1),
            &["missing_observation"][..]),
        ("sum-update", known_bound.replacen("quantity=q",
            "quantity=sum(list<Q>[q*b.stock.available])", 1),
            &["missing_observation"][..]),
        ("observational-branch-equalities", known_bound.replacen(nonnegative,
            "(if b.stock.available>=rat(0,1) then b.quantity=rat(0,1) else b.quantity=rat(1,1))", 1),
            &["missing_observation"][..]),
        ("conditionally-chosen-term", known_bound.replacen(nonnegative,
            "(((if b.stock.available>=rat(0,1) then fn(x:Q)=>true else fn(x:Q)=>false)(b.quantity)) implies b.quantity>=rat(0,1))", 1),
            &["missing_observation"][..]),
        ("bound-conditionally-chosen-term", known_bound.replacen(nonnegative,
            "(let f=if b.stock.available>=rat(0,1) then (fn(x:Q)=>true) else (fn(x:Q)=>false) in (f(rat(0,1)) implies b.quantity>=rat(0,1)))", 1),
            &["missing_observation"][..]),
        ("tuple-branch-projection", known_bound.replacen(nonnegative,
            "(((if b.stock.available>=rat(0,1) then (b.quantity,true) else (b.quantity,false)).1) implies b.quantity>=rat(0,1))", 1),
            &["missing_observation"][..]),
        ("type-quantified-guard", known_bound.replacen("legal(w:Pool.World):",
            "legal(w:Pool.World) when (forall b in Pool.Cell[w] . forall f:Bool . b.quantity-b.quantity+b.stock.available>=rat(0,1)):", 1),
            &["missing_observation"][..]),
        ("term-projected-guard", known_bound.replacen("legal(w:Pool.World):",
            "legal(w:Pool.World) when (forall b in Pool.Cell[w] . ((fn(t:(Q,Q))=>t.1>=rat(0,1))((b.quantity,b.stock.available)))):", 1),
            &["missing_observation"][..]),
        ("candidate-filter-in-unknown-domain", known_bound.replacen("legal(w:Pool.World):",
            "legal(w:Pool.World,x:Pool.Stock): forall flag in list{true | v in list<Q>[x.available] where (forall b in Pool.Cell[w] . b.quantity>=rat(0,1))} .", 1),
            &["missing_observation", "unsupported_algorithm"][..]),
        ("match-ignored-tuple", known_bound.replacen(nonnegative,
            "((match (b.quantity,b.stock.available) { _=>b.stock.available>=rat(0,1); }) implies b.quantity>=rat(0,1))", 1),
            &["missing_observation"][..]),
        ("match-projected-tuple", known_bound.replacen(nonnegative,
            "((match (b.quantity,b.stock.available) { pair=>pair.1>=rat(0,1); }) implies b.quantity>=rat(0,1))", 1),
            &["missing_observation"][..]),
        ("exists-dependent-domain", known_bound.replacen(nonnegative,
            "(exists n in list<Q>[b.stock.available] . b.quantity>=rat(0,1) and n-n=rat(0,1))", 1),
            &["missing_observation", "unsupported_algorithm"][..]),
        ("match-nonlinear-update", known_bound.replacen("quantity=q",
            "quantity=match true { _=>q*q+b.stock.available; }", 1),
            &["missing_observation", "unsupported_algorithm"][..]),
        ("match-fixed-antecedent", known_bound.replacen(nonnegative,
            "((match true { _=>b.quantity-b.quantity+b.stock.available>=rat(0,1); }) implies b.quantity>=rat(0,1))", 1),
            &["missing_observation"][..]),
        ("match-cancelled-antecedent", known_bound.replacen(nonnegative,
            "((match true { _=>b.quantity+b.stock.available-b.stock.available>=rat(10,1); }) implies b.quantity>=rat(0,1))", 1),
            &["unsupported_algorithm"][..]),
        ("cancelled-implication", known_bound.replacen(nonnegative,
            "((b.quantity+b.stock.available-b.stock.available>=rat(10,1)) implies b.quantity>=rat(0,1))", 1),
            &["unsupported_algorithm"][..]),
        ("cancelled-view", known_bound.replacen(" law required legal",
            " view eligible(b:Pool.Cell):Bool=let cap=b.stock.available in b.quantity+cap-cap>=rat(10,1);\n law required legal", 1)
            .replacen(nonnegative, "not(eligible(b))", 1),
            &["unsupported_algorithm"][..]),
        ("let-coefficient", POLY_LAW.replacen("b.quantity>=rat(0,1)",
            "(let capacity=b.stock.available in b.quantity*capacity>=rat(0,1))", 1), &["missing_observation"][..]),
        ("view-coefficient", POLY_LAW.replacen(" law required legal",
            " view weighted(b:Pool.Cell):Q=b.quantity*b.stock.available;\n law required legal", 1)
            .replacen("b.quantity>=rat(0,1)", "weighted(b)>=rat(0,1)", 1), &["missing_observation"][..]),
        ("guard-dead", POLY_LAW.replacen("stockLoad(s)<=s.available", "stockLoad(s)<=rat(5,1)", 1)
            .replacen("legal(w:Pool.World):", "legal(w:Pool.World) when (forall b in Pool.Cell[w] . if true then b.quantity>=rat(0,1) else b.stock.available>=rat(10,1)):", 1),
            &["unsupported_algorithm"][..]),
        ("guard-live", POLY_LAW.replacen("legal(w:Pool.World):",
            "legal(w:Pool.World) when (forall b in Pool.Cell[w] . if true then b.stock.available>=rat(0,1) else b.quantity>=rat(10,1)):", 1),
            &["missing_observation"][..]),
        ("cancelled-coefficient", POLY_LAW.replacen("stockLoad(s)<=s.available", "stockLoad(s)<=rat(5,1)", 1)
            .replacen("b.quantity>=rat(0,1)", "(b.quantity+b.stock.available-b.stock.available>=rat(10,1) or b.quantity<=rat(0,1))", 1),
            &["unsupported_algorithm"][..]),

        ("cancelled-symbol", POLY_LAW.replacen("legal(w:Pool.World):",
            "legal(w:Pool.World) when (forall b in Pool.Cell[w] . b.quantity-b.quantity+b.stock.available>=rat(0,1)):", 1),
            &["missing_observation"][..]),
        ("unknown-coefficient", POLY_LAW.replacen("b.quantity>=rat(0,1)",
            "b.quantity*b.stock.available>=rat(0,1)", 1), &["missing_observation"][..]),
        ("dependent-domain", POLY_LAW.replacen("legal(w:Pool.World):",
            "legal(w:Pool.World): forall flag in (if (forall t in Pool.Cell[w] . t.quantity<=t.stock.available) then list<Bool>[true] else list<Bool>[]) .", 1),
            &["missing_observation", "unsupported_algorithm"][..]),
        ("dead-read", dead_read.replacen("b.quantity>=rat(0,1)", disjunction, 1),
            &["unsupported_algorithm"][..]),

        (
            "guard",
            POLY_LAW.replacen(
                "legal(w:Pool.World):",
                "legal(w:Pool.World) when (forall s in Pool.Stock[w] . s.available>=rat(0,1)):",
                1,
            ),
            &["missing_observation"][..],
        ),
        (
            "mixed",
            POLY_LAW.replacen(
                "b.quantity>=rat(0,1)",
                "(b.quantity>=rat(10,1) or b.quantity<=b.stock.available)",
                1,
            ),
            &["missing_observation", "unsupported_algorithm"][..],
        ),
    ] {
        std::fs::write(dir.join("laws.law"), law).unwrap();
        let ask_with_stock = format!("{},bind.x=@fixture/overlapFeasible.X)", ask.strip_suffix(')').unwrap());
        let ask = if matches!(out, "direct-equality" | "candidate-filter-in-unknown-domain") { ask_with_stock.as_str() } else { ask };
        let run = polyhedron_asks(&dir, &[ask, "plan=needed($overlapFeasible)"], out, None);
        assert_eq!(run.code, 2, "{}{}", run.stdout, run.stderr);
        let result = result_json(&dir, &run);
        let answer = &arr(get(&result, "answers"))[0];
        assert!(!has(get(answer, "outputs"), "solutions"));
        let mut reasons = arr(get(answer, "reasons"))
            .iter()
            .map(|r| s(get(r, "code")))
            .collect::<Vec<_>>();
        reasons.sort_unstable();
        assert_eq!(reasons, codes, "{out}");
        let plan = &arr(get(&result, "answers"))[1];
        let plan = referenced(&result, get(get(plan, "outputs"), "plan"));
        let requirements = arr(get(get(plan, "value"), "requirements"));
        if codes.contains(&"missing_observation") {
            let [requirement] = requirements else { panic!("{out}: expected one requirement") };
            assert_eq!(s(get(get(requirement, "field"), "field")), "Pool.Stock.available", "{out}");
        } else {
            assert!(requirements.is_empty(), "{out}");
        }
    }
}
