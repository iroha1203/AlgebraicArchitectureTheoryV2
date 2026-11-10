//! R2 の在庫引当、会計、由来比較を一つの公開 run で検査する。
use crate::common::cli::*;
use archsig_common::json::JNode;

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
    for (name, contents) in [
        (
            "definitions.json",
            include_str!("fixtures/r2-backing/definitions.json"),
        ),
        ("laws.law", LAW),
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
        &LAW[num(lo) as usize..num(hi) as usize],
        concat!(
            "forall b in Pool.Cell[w] . b.quantity>=rat(0,1) and\n",
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
