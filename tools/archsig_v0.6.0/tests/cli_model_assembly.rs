//! 組立対象の保存結果を現在の入力で再検証する。
use crate::common::{cli::*, model_assembly_data as fixture};
use archsig_common::canonical::Json;
use std::path::Path;
fn execute(dir: &Path, out: &str, reuse: Option<&str>) -> BinaryRun {
    execute_asks(
        dir,
        out,
        reuse,
        &[
            fixture::ASSEMBLE,
            "c=check(Assembly.zero,on=$a.object)",
            "o=evaluate(Assembly.ownerOf,on=$a.object,p=@v/b)",
        ],
    )
}
fn execute_asks(dir: &Path, out: &str, reuse: Option<&str>, asks: &[&str]) -> BinaryRun {
    let mut args = vec![
        "run",
        "--atom-definition",
        "d.json",
        "--law",
        "l.law",
        "--archmap",
        "a.json",
        "--out",
        out,
    ];
    if let Some(path) = reuse {
        args.extend(["--reuse", path]);
    }
    for &ask in asks {
        args.extend(["--ask", ask]);
    }
    run_binary(dir, &args)
}
fn write_inputs(dir: &Path, input: &archsig_input::input::InputSources) {
    for (name, data) in [
        ("d.json", input.definitions()[0].bytes()),
        ("a.json", input.archmap().bytes()),
        ("l.law", input.law().bytes()),
    ] {
        std::fs::write(dir.join(name), data).unwrap();
    }
}
#[test]
fn saved_assembly_rechecks_current_fields_and_withdrawn_observations() {
    let dir = workdir("model-assembly");
    write_inputs(&dir, &fixture::input(|s| s));
    let first = execute(&dir, "first", None);
    assert_eq!(first.code, 0, "{}", first.stdout);
    let same = execute(&dir, "same", Some("first"));
    assert_eq!(same.code, 0, "{}", same.stdout);
    let result = result_json(&dir, &same);
    assert!(warnings(&result).is_empty());
    assert!(
        arr(get(&result, "answers"))
            .iter()
            .all(|a| s(get(a, "status")) == "established")
    );
    // 保存済み主張の改変を現在の導出の代わりに採用しない。
    let saved_path = dir.join("first/result.json");
    let saved = std::fs::read_to_string(&saved_path).unwrap();
    let forged = saved.replace("\"established\"", "\"refuted\"");
    assert_ne!(forged, saved);
    std::fs::write(&saved_path, forged).unwrap();
    let tampered = execute(&dir, "tampered", Some("first"));
    assert_eq!(tampered.code, 0, "{}", tampered.stdout);
    let checked = result_json(&dir, &tampered);
    assert!(!warnings(&checked).is_empty());
    assert!(
        arr(get(&checked, "answers"))
            .iter()
            .all(|a| s(get(a, "status")) == "established")
    );
    std::fs::write(&saved_path, saved).unwrap();
    // 重なりの現在値が矛盾したら保存済みの完成対象は採用しない。
    write_inputs(
        &dir,
        &fixture::input(|s| fixture::atom(s, "mb-quantity", Some(Json::str("1")))),
    );
    let changed = execute(&dir, "changed", Some("first"));
    let result = result_json(&dir, &changed);
    assert!(!warnings(&result).is_empty());
    let answer = &arr(get(&result, "answers"))[0];
    assert_eq!(s(get(answer, "status")), "refuted");
    assert!(!has(get(answer, "outputs"), "object"));
    // 観測の撤回をゼロや古い値で埋めず、元位置を欠測に戻す。
    write_inputs(
        &dir,
        &fixture::input(|s| fixture::atom(s, "mb-quantity", None)),
    );
    let missing = execute(&dir, "missing", Some("first"));
    let result = result_json(&dir, &missing);
    let answer = &arr(get(&result, "answers"))[0];
    assert_eq!(s(get(answer, "status")), "undetermined");
    assert!(!has(get(answer, "outputs"), "object"));
    // 修正された現在入力から完成対象を作り直せる。
    write_inputs(&dir, &fixture::input(|s| s));
    let restored = execute(&dir, "restored", Some("first"));
    assert_eq!(restored.code, 0, "{}", restored.stdout);
    let law = String::from_utf8(fixture::input(|s| s).law().bytes().to_vec())
        .unwrap()
        .replace(
            "law required zero",
            "law required atMostTwo(r:Root):count(Part[r])=2;\n  law required zero",
        );
    std::fs::write(dir.join("l.law"), law).unwrap();
    let unsupported = execute(&dir, "unsupported", Some("first"));
    assert_eq!(unsupported.code, 2, "{}", unsupported.stdout);
    let result = result_json(&dir, &unsupported);
    assert!(
        arr(get(&result, "answers"))
            .iter()
            .all(|a| s(get(a, "status")) == "undetermined")
    );
    assert!(
        arr(get(&result, "issues"))
            .iter()
            .all(|r| s(get(r, "code")) != "internal")
    );
}

#[test]
fn saved_map_assembly_rechecks_local_correspondences_and_serializes_square_failure() {
    use crate::common::model_map_assembly_data as maps;
    let dir = workdir("model-map-assembly");
    let execute = |out: &str, reuse: Option<&str>, target: &str| {
        let mut args = vec![
            "run",
            "--atom-definition",
            "d.json",
            "--law",
            "l.law",
            "--archmap",
            "a.json",
            "--out",
            out,
        ];
        if let Some(path) = reuse {
            args.extend(["--reuse", path]);
        }
        for ask in [
            maps::ASSEMBLE,
            target,
            "m=assemble_map(Assembly.moves,from=$a.assembly,to=$b.assembly,x=@v/moveA,y=@v/moveB)",
        ] {
            args.extend(["--ask", ask]);
        }
        run_binary(&dir, &args)
    };
    let target = "b=assemble(Assembly.fragments,on=@v/G,along=Assembly.interfaces,a=@v/A,b=@v/B,ma=@v/ma,mb=@v/mb)";
    write_inputs(&dir, &maps::query(|s| s));
    let first = execute("first", None, target);
    assert_eq!(first.code, 0, "{}", first.stdout);
    let same = execute("same", Some("first"), target);
    assert_eq!(same.code, 0, "{}", same.stdout);
    assert!(warnings(&result_json(&dir, &same)).is_empty());
    write_inputs(&dir, &maps::query(|s| maps::atom(s, "a-quantity", None)));
    let blocked = execute("blocked-model", Some("first"), target);
    assert_eq!(blocked.code, 2, "{}", blocked.stdout);
    let result = result_json(&dir, &blocked);
    let answer = &arr(get(&result, "answers"))[2];
    assert_eq!(s(get(answer, "status")), "undetermined");
    assert!(
        arr(get(answer, "reasons"))
            .iter()
            .any(|r| s(get(r, "code")) == "dependency_blocked")
    );
    assert!(
        arr(get(answer, "reasons"))
            .iter()
            .any(|r| s(get(r, "code")) == "missing_observation")
    );
    write_inputs(&dir, &maps::query(|s| maps::atom(s, "moveB-parts", None)));
    let missing = execute("missing", Some("first"), target);
    let result = result_json(&dir, &missing);
    assert!(!warnings(&result).is_empty());
    let answer = &arr(get(&result, "answers"))[2];
    assert_eq!(s(get(answer, "status")), "undetermined");
    assert!(!has(get(answer, "outputs"), "map"));
    write_inputs(
        &dir,
        &maps::replace_law(
            maps::query(maps::folding_with_arrows),
            "law required zero(p:Part):p.quantity=0;",
            "view only(a:Root):Set<Root> = set<Root>{a};view emptyInterfaces(a:Root):Unit=unit;law required zero(p:Part):p.quantity=0;",
        ),
    );
    let failed = execute(
        "square",
        None,
        "b=assemble(Assembly.only,on=@v/G,along=Assembly.emptyInterfaces,a=@v/A)",
    );
    assert_eq!(failed.code, 1, "{}", failed.stdout);
    let result = result_json(&dir, &failed);
    let answer = &arr(get(&result, "answers"))[2];
    assert!(has(get(answer, "outputs"), "configuration_map"));
    assert!(!has(get(answer, "outputs"), "map"));
    let evidence = &arr(get(answer, "counterexamples"))[0];
    let node = arr(get(&result, "nodes"))
        .iter()
        .find(|n| get(n, "id") == get(evidence, "node"))
        .unwrap();
    let difference = get(get(get(node, "value"), "data"), "action_difference");
    assert!(
        arr(get(answer, "reasons"))
            .iter()
            .any(|r| s(get(r, "code")) == "condition_failed")
    );
    assert_eq!(s(get(difference, "kind")), "generator");
    assert_ne!(get(difference, "left"), get(difference, "right"));
}

#[test]
fn saved_assembly_accepts_supported_law_updates_and_restores_the_original_law() {
    let dir = workdir("model-assembly-law-updates");
    let input = fixture::input(|s| s);
    write_inputs(&dir, &input);
    let asks = [
        fixture::ASSEMBLE,
        "o=evaluate(Assembly.ownerOf,on=$a.object,p=@v/b)",
    ];
    assert_eq!(execute_asks(&dir, "original", None, &asks).code, 0);
    let original = std::str::from_utf8(input.law().bytes()).unwrap();
    let unsupported = "law required sizeLaw(p:Part):count(Part[p.owner])>=1;";
    let law = original.replace(
        "law required zero",
        &format!("{unsupported} law required zero"),
    );
    let expression = "count(Part[p.owner])>=1";
    let begin = law.find(expression).unwrap();
    std::fs::write(dir.join("l.law"), law).unwrap();
    let run = execute_asks(&dir, "coexisting-law", Some("original"), &asks);
    assert_eq!(run.code, 2, "{}", run.stdout);
    let result = result_json(&dir, &run);
    let answers = arr(get(&result, "answers"));
    assert_eq!(s(get(&answers[0], "status")), "undetermined");
    assert!(!has(get(&answers[0], "outputs"), "object"));
    for answer in answers {
        let reasons = arr(get(answer, "reasons"));
        let reason = reasons
            .iter()
            .find(|r| s(get(r, "code")) == "unsupported_algorithm")
            .unwrap();
        let location = get(reason, "location");
        assert_eq!(s(get(location, "input")), "law");
        let span = arr(get(location, "span"));
        assert_eq!(
            (num(&span[0]), num(&span[1])),
            (begin as u64, (begin + expression.len()) as u64)
        );
        assert_eq!(
            s(get(get(reason, "details"), "method")),
            "integer_order_equation_presentation"
        );
    }
    assert!(
        arr(get(&answers[1], "reasons"))
            .iter()
            .any(|r| s(get(r, "code")) == "dependency_blocked")
    );
    for (name, added) in [
        ("integer", "law required parameter(r:Root,n:Z):n=n;"),
        (
            "count",
            "law required size(p:Part):count(Part[p.owner])>=1;",
        ),
        ("restored", "law required zero(p:Part):p.quantity=0;"),
    ] {
        let law = original.replace("law required zero(p:Part):p.quantity=0;", added);
        std::fs::write(dir.join("l.law"), law).unwrap();
        let current = execute_asks(&dir, name, Some("original"), &asks);
        assert_eq!(current.code, 0, "{name}: {}", current.stdout);
        let result = result_json(&dir, &current);
        assert!(
            arr(get(&result, "answers"))
                .iter()
                .all(|a| s(get(a, "status")) == "established")
        );
        assert!(arr(get(&result, "issues")).is_empty());
    }
}

#[test]
fn r2_e12_consume_assembles_local_routes_and_preserves_named_actions() {
    use archsig_common::json::{JNode, parse};
    use std::collections::BTreeMap;

    let dir = workdir("r2-e12-consume");
    let input = archsig_input::input::InputSources::from_bytes(
        vec![include_bytes!("fixtures/r2-e12-consume/definitions.json").to_vec()],
        include_bytes!("fixtures/r2-e12-consume/laws.law").to_vec(),
        include_bytes!("fixtures/r2-e12-consume/archmap.json").to_vec(),
    );
    write_inputs(&dir, &input);
    let asks: Vec<_> = include_str!("fixtures/r2-e12-consume/queries.txt")
        .lines()
        .collect();
    let run = execute_asks(&dir, "first", None, &asks);
    assert_eq!(run.code, 0, "{}{}", run.stdout, run.stderr);
    let result = result_json(&dir, &run);
    let nodes: BTreeMap<_, _> = arr(get(&result, "nodes"))
        .iter()
        .map(|node| (s(get(node, "id")), node))
        .collect();
    let node = |reference: &JNode| nodes[s(get(reference, "node"))];
    let value = |reference: &JNode| get(node(reference), "value");
    let subject = |reference: &JNode| {
        let [snapshot, id] = arr(value(reference)) else {
            panic!("typed subject reference");
        };
        assert_eq!(s(snapshot), "comparison");
        Json::str(s(id))
    };
    let root = |reference: &JNode| subject(get(value(reference), "root"));
    let answers = arr(get(&result, "answers"));
    assert!(
        answers.iter().all(|a| s(get(a, "status")) == "established"),
        "{:?}",
        get(&result, "issues")
    );
    let output = |index: usize, field| get(get(&answers[index], "outputs"), field);
    let assembled = value(output(2, "map"));
    assert_eq!(s(get(node(output(2, "map")), "type")), "ModelMapAssembly");
    assert_eq!(
        get(assembled, "source_assembly").value,
        output(0, "assembly").value
    );
    assert_eq!(
        get(assembled, "target_assembly").value,
        output(1, "assembly").value
    );
    assert_eq!(
        get(assembled, "configuration_map").value,
        output(2, "configuration_map").value
    );
    let locals = arr(get(assembled, "locals"))
        .iter()
        .map(|local| {
            Json::Arr(vec![
                subject(get(local, "correspondence")),
                root(get(local, "source")),
                root(get(local, "target")),
            ])
        })
        .collect();
    let generators = arr(get(assembled, "generators"))
        .iter()
        .map(|generator| {
            let src = get(generator, "source");
            let tgt = get(generator, "target");
            let proposition = node(get(generator, "proposition"));
            assert_eq!(s(get(proposition, "type")), "Proposition");
            assert_eq!(
                s(get(get(proposition, "judgment"), "status")),
                "established"
            );
            let operands = arr(get(get(proposition, "value"), "operands"));
            for edge in [src, tgt, output(2, "configuration_map")] {
                assert!(operands.iter().any(|operand| operand.value == edge.value));
            }
            let endpoints = |operation: &JNode| {
                let op = value(operation);
                let name = get(op, "name");
                assert_eq!(s(get(node(operation), "type")), "Operation");
                assert_eq!(s(get(name, "kind")), "generator");
                Json::Arr(vec![
                    subject(get(name, "subject")),
                    root(get(op, "source")),
                    root(get(op, "target")),
                ])
            };
            Json::Arr(vec![endpoints(src), endpoints(tgt)])
        })
        .collect();
    let configuration_map = value(get(assembled, "configuration_map"));
    let candidate = get(configuration_map, "candidate");
    assert_eq!(candidate.value, output(2, "candidate").value);
    let action = value(get(value(candidate), "action"));
    let atoms = arr(get(value(get(action, "universe")), "atoms"));
    let images = arr(get(action, "images"));
    assert_eq!(atoms.len(), images.len());
    let point_images = [
        "native-output1",
        "native-N-before",
        "native-N-after",
        "native-T3-after",
        "native-N-consume",
        "native-T3-consume",
    ]
    .map(|id| {
        let position = atoms
            .iter()
            .position(|a| s(get(a, "subject")) == id && !has(a, "field") && !has(a, "atom"));
        let image = &images[position.expect("source point in the full action")];
        assert_eq!(s(get(image, "snapshot")), "comparison");
        Json::Arr(vec![Json::str(id), Json::str(s(get(image, "subject")))])
    });
    let report = Json::obj([
        ("status", Json::str(s(get(&result, "status")))),
        (
            "roots",
            Json::Arr(vec![
                root(get(assembled, "source")),
                root(get(assembled, "target")),
            ]),
        ),
        ("locals", Json::Arr(locals)),
        ("generators", Json::Arr(generators)),
        ("point_images", Json::Arr(point_images.into())),
        (
            "after_quantities",
            Json::Arr(
                [3, 4]
                    .into_iter()
                    .map(|i| Json::str(s(value(output(i, "value")))))
                    .collect(),
            ),
        ),
    ]);
    let expected = parse(include_bytes!("fixtures/r2-e12-consume/expected.json")).unwrap();
    let actual = parse(report.canonical().as_bytes()).unwrap();
    assert_eq!(actual.value, expected.value, "{}", report.canonical());

    let wrong_endpoint = std::str::from_utf8(input.archmap().bytes())
        .unwrap()
        .replacen(
            r#""field":"E12.Consume.to","value":["comparison","rust-N-after"]"#,
            r#""field":"E12.Consume.to","value":["comparison","rust-N-before"]"#,
            1,
        );
    assert_ne!(wrong_endpoint.as_bytes(), input.archmap().bytes());
    std::fs::write(dir.join("a.json"), wrong_endpoint).unwrap();
    let refuted = execute_asks(&dir, "refuted", None, &asks[..3]);
    assert_eq!(refuted.code, 1, "{}{}", refuted.stdout, refuted.stderr);
    let refuted = result_json(&dir, &refuted);
    let answers = arr(get(&refuted, "answers"));
    assert!(
        answers[..2]
            .iter()
            .all(|a| s(get(a, "status")) == "established")
    );
    assert_eq!(s(get(&answers[2], "status")), "refuted");
    assert!(
        arr(get(&answers[2], "reasons"))
            .iter()
            .any(|reason| { s(get(reason, "code")) == "condition_failed" })
    );
    assert!(!arr(get(&answers[2], "counterexamples")).is_empty());

    let bad = std::str::from_utf8(input.archmap().bytes())
        .unwrap()
        .replacen(
            r#""field":"E12.Consume.to","value":["comparison","rust-N-after"]"#,
            r#""field":"E12.Consume.to","value":["comparison","unregistered-N"]"#,
            1,
        );
    assert_ne!(bad.as_bytes(), input.archmap().bytes());
    std::fs::write(dir.join("a.json"), bad).unwrap();
    let rejected = execute_asks(&dir, "invalid", None, &asks);
    assert_eq!(rejected.code, 65, "{}{}", rejected.stdout, rejected.stderr);
    assert!(arr(get(&rejected.receipt, "issues")).iter().any(|issue| {
        s(get(issue, "code")) == "reference"
            && s(get(issue, "message")).contains("comparison/unregistered-N")
            && s(get(get(issue, "location"), "input")) == "archmap"
    }));
}

#[test]
fn refuted_e12_map_blocks_only_its_target_consumers_and_rechecks() {
    let dir = workdir("r2-e12-refuted-dependent");
    let original = include_str!("fixtures/r2-e12-consume/archmap.json");
    let refuted = original.replacen(
        r#""field":"E12.Consume.to","value":["comparison","rust-N-after"]"#,
        r#""field":"E12.Consume.to","value":["comparison","rust-N-before"]"#,
        1,
    );
    assert_ne!(refuted, original);
    write_inputs(
        &dir,
        &archsig_input::input::InputSources::from_bytes(
            vec![include_bytes!("fixtures/r2-e12-consume/definitions.json").to_vec()],
            include_bytes!("fixtures/r2-e12-consume/laws.law").to_vec(),
            refuted.into_bytes(),
        ),
    );
    let mut asks: Vec<_> = include_str!("fixtures/r2-e12-consume/queries.txt")
        .lines()
        .collect();
    asks.push("independent=evaluate(E12Compare.amount,s=@comparison/rust-N-after,on=$rust.object)");
    let run = execute_asks(&dir, "first", None, &asks);
    assert_eq!(run.code, 2, "{}{}", run.stdout, run.stderr);
    let result = result_json(&dir, &run);
    assert_eq!(s(get(&result, "status")), "partial");
    let answers = arr(get(&result, "answers"));
    assert_eq!(
        answers
            .iter()
            .map(|answer| s(get(answer, "status")))
            .collect::<Vec<_>>(),
        [
            "established",
            "established",
            "refuted",
            "undetermined",
            "undetermined",
            "established"
        ]
    );
    let [original_reason] = arr(get(&answers[2], "reasons")) else {
        panic!("the map has one original refutation");
    };
    assert_eq!(s(get(original_reason, "code")), "condition_failed");
    let [counterexample] = arr(get(&answers[2], "counterexamples")) else {
        panic!("the refutation keeps its witness");
    };
    let nodes = arr(get(&result, "nodes"));
    let dereference = |reference: &archsig_common::json::JNode| {
        nodes
            .iter()
            .find(|node| s(get(node, "id")) == s(get(reference, "node")))
            .unwrap()
    };
    let counterexample = dereference(counterexample);
    assert_eq!(s(get(counterexample, "type")), "Counterexample");
    let facts = arr(get(get(get(counterexample, "value"), "data"), "facts"));
    assert!(facts.iter().any(|fact| s(get(fact, "subject")) == "move-N"));
    for endpoint in ["native-N-consume.to", "rust-N-consume.to"] {
        assert!(facts.iter().any(|fact| {
            has(fact, "atom")
                && s(get(fact, "snapshot")) == "comparison"
                && s(get(fact, "field")) == "E12.Consume.to"
                && s(get(fact, "atom")) == endpoint
        }));
    }
    for consumer in &answers[3..5] {
        let reasons = arr(get(consumer, "reasons"));
        assert!(
            reasons
                .iter()
                .any(|reason| reason.value == original_reason.value)
        );
        let dependency = reasons
            .iter()
            .find(|reason| s(get(reason, "code")) == "dependency_blocked")
            .unwrap();
        assert_eq!(s(get(get(dependency, "details"), "request")), "move");
        assert!(!has(get(consumer, "outputs"), "value"));
    }
    let independent = dereference(get(get(&answers[5], "outputs"), "value"));
    assert_eq!(s(get(independent, "value")), "1");

    let rechecked = execute_asks(&dir, "rechecked", Some("first"), &asks);
    assert_eq!(
        rechecked.code, 2,
        "{}{}",
        rechecked.stdout, rechecked.stderr
    );
    let rechecked = result_json(&dir, &rechecked);
    assert!(warnings(&rechecked).is_empty());
    for key in ["nodes", "answers", "issues"] {
        assert_eq!(get(&result, key).value, get(&rechecked, key).value);
    }

    let mut invalid_asks = asks[..3].to_vec();
    invalid_asks.push(
        "invalid=evaluate(E12Compare.amount,s=@comparison/rust-N-after,on=$move.map.unknown)",
    );
    let invalid = execute_asks(&dir, "invalid", None, &invalid_asks);
    assert_eq!(invalid.code, 64, "{}{}", invalid.stdout, invalid.stderr);
    assert!(arr(get(&invalid.receipt, "issues")).iter().any(|issue| {
        s(get(issue, "code")) == "usage" && s(get(issue, "request")) == "invalid"
    }));
    assert!(!dir.join("invalid").exists());
}

#[test]
fn r2_repairs_keep_local_freedom_and_reassemble_actual_objects() {
    use archsig_common::json::JNode;
    let dir = workdir("r2-repaired-locals");
    write_inputs(
        &dir,
        &archsig_input::input::InputSources::from_bytes(
            vec![include_bytes!("fixtures/r2-repaired-locals/definitions.json").to_vec()],
            include_bytes!("fixtures/r2-repaired-locals/laws.law").to_vec(),
            include_bytes!("fixtures/r2-repaired-locals/archmap.json").to_vec(),
        ),
    );
    let asks = include_str!("fixtures/r2-repaired-locals/queries.txt")
        .lines()
        .collect::<Vec<_>>();
    let run = execute_asks(&dir, "first", None, &asks);
    assert_eq!(run.code, 1, "{}{}", run.stdout, run.stderr);
    let result = result_json(&dir, &run);
    let answers = arr(get(&result, "answers"));
    let nodes = arr(get(&result, "nodes"));
    let answer = |id: &str| answers.iter().find(|a| s(get(a, "id")) == id).unwrap();
    let output = |id: &str, field: &str| get(get(answer(id), "outputs"), field);
    let node = |reference: &JNode| {
        nodes
            .iter()
            .find(|node| s(get(node, "id")) == s(get(reference, "node")))
            .unwrap()
    };
    let value = |reference: &JNode| get(node(reference), "value");
    let id = |reference: &JNode| s(&arr(value(reference))[1]);
    let expected =
        archsig_common::json::parse(include_bytes!("fixtures/r2-repaired-locals/expected.json"))
            .unwrap();
    assert_eq!(s(get(&result, "status")), "complete");
    let actual = answers
        .iter()
        .map(|a| (s(get(a, "id")), s(get(a, "status"))))
        .collect::<std::collections::BTreeMap<_, _>>();
    let archsig_common::json::JValue::Obj(expected_answers) = &get(&expected, "answers").value
    else {
        panic!("saved answer projection");
    };
    let expected_answers = expected_answers
        .iter()
        .map(|(id, status)| (id.as_str(), s(status)))
        .collect::<std::collections::BTreeMap<_, _>>();
    assert_eq!(actual.len(), answers.len());
    assert_eq!(actual, expected_answers);

    for (assembled, local_a, local_b) in [
        ("made0", "aApply0", "bApply0"),
        ("made1", "aApply1", "bApply1"),
    ] {
        let object = output(assembled, "object");
        let assembly = value(output(assembled, "assembly"));
        assert_eq!(get(assembly, "object").value, object.value);
        let algebra = value(output(assembled, "algebra"));
        let equations = value(get(algebra, "equations"));
        let boundary = arr(get(equations, "indices"))
            .iter()
            .position(|index| {
                let law = value(index);
                s(get(law, "name")) == "Assembly.boundary"
                    && arr(get(law, "bindings"))
                        .iter()
                        .any(|binding| id(get(binding, "value")) == "a")
            })
            .unwrap();
        let owned = arr(get(equations, "objects"))
            .iter()
            .find(|row| {
                let component = value(get(row, "object"));
                s(get(component, "kind")) == "owned" && id(get(component, "subject")) == "a"
            })
            .unwrap();
        let component = value(get(owned, "object"));
        assert_eq!(
            get(value(get(component, "object")), "state_of").value,
            object.value
        );
        let holds = node(&arr(get(owned, "holds"))[boundary]);
        assert_eq!(
            s(get(get(holds, "judgment"), "status")),
            if assembled == "made0" {
                "established"
            } else {
                "refuted"
            }
        );
        let expected_values = get(get(&expected, "global_quantities"), assembled);
        let mut found = 0;
        let mut transported_endpoint = false;
        for row in arr(get(value(object), "overrides")) {
            let slot = get(row, "slot");
            if s(get(slot, "field")) == "Assemble.Part.quantity" {
                assert_eq!(
                    s(value(get(row, "value"))),
                    s(get(expected_values, id(get(slot, "subject"))))
                );
                found += 1;
            }
            if s(get(slot, "field")) == "Assemble.Step.from" {
                assert_eq!(id(get(slot, "subject")), "right");
                assert_eq!(id(get(row, "value")), "ma");
                transported_endpoint = true;
            }
        }
        assert_eq!(found, 3);
        assert!(transported_endpoint);
        let [a, b] = arr(get(assembly, "inclusions")) else {
            panic!("two local inclusions");
        };
        for (row, apply, owner, operation) in
            [(a, local_a, "A", "left"), (b, local_b, "B", "right")]
        {
            assert_eq!(get(row, "applied").value, output(apply, "object").value);
            let fragment = get(row, "fragment");
            assert_eq!(id(get(value(fragment), "root")), owner);
            assert_eq!(
                get(value(fragment), "overrides").value,
                get(value(output(apply, "object")), "overrides").value
            );
            let inclusion = value(get(value(get(row, "map")), "candidate"));
            let restriction = value(get(value(get(row, "restriction")), "candidate"));
            assert_eq!(get(inclusion, "source").value, fragment.value);
            assert_eq!(get(inclusion, "target").value, object.value);
            assert_eq!(get(restriction, "target").value, fragment.value);
            assert_eq!(id(get(value(get(restriction, "source")), "root")), "G");
            let [generator] = arr(get(row, "generators")) else {
                panic!("one operation per site");
            };
            for side in ["source", "target"] {
                assert_eq!(
                    id(get(get(value(get(generator, side)), "name"), "subject")),
                    operation
                );
            }
            assert_eq!(
                s(get(
                    get(node(get(generator, "proposition")), "judgment"),
                    "status"
                )),
                "established"
            );
        }
    }
    assert_eq!(id(output("shared", "value")), "G");
    for (check, assembly) in [("globalZero", "made0"), ("globalOne", "made1")] {
        assert_eq!(
            output(check, "environment").value,
            output(assembly, "object").value
        );
    }
    let [conflict] = arr(get(answer("madeConflict"), "counterexamples")) else {
        panic!("actual repaired overlap differs");
    };
    let conflict = get(value(conflict), "data");
    assert_eq!(s(value(get(conflict, "left"))), "1");
    assert_eq!(s(value(get(conflict, "right"))), "0");
    assert!(arr(get(conflict, "facts")).is_empty());
    let repaired = arr(get(conflict, "repaired"));
    assert_eq!(repaired.len(), 2);
    for (operand, side, subject, apply) in [
        (&repaired[0], "left", "mb", "bApplyOne"),
        (&repaired[1], "right", "ma", "aApply0"),
    ] {
        assert_eq!(s(get(operand, "side")), side);
        assert_eq!(get(operand, "object").value, output(apply, "object").value);
        let slot = get(operand, "slot");
        assert_eq!(id(get(slot, "subject")), subject);
        assert_eq!(s(get(slot, "field")), "Assemble.Part.quantity");
    }
    let different = answer("moveBetweenChoices");
    assert!(has(get(different, "outputs"), "configuration_map"));
    assert!(!has(get(different, "outputs"), "map"));
    let [counter] = arr(get(different, "counterexamples")) else {
        panic!("Law preservation distinguishes the chosen states");
    };
    let data = get(value(counter), "data");
    assert_eq!(
        value(get(data, "left")).value,
        archsig_common::json::JValue::Bool(true)
    );
    assert_eq!(
        value(get(data, "right")).value,
        archsig_common::json::JValue::Bool(false)
    );
    for rejected in ["raw", "madeConflict", "madePartial", "mixedOwner"] {
        assert!(!has(get(answer(rejected), "outputs"), "object"));
        assert_eq!(
            s(get(&arr(get(answer(rejected), "reasons"))[0], "code")),
            "condition_failed"
        );
    }

    let prefix: Vec<_> = asks
        .into_iter()
        .filter(|ask| {
            let (id, _) = ask.split_once('=').unwrap();
            matches!(
                id,
                "aWithin"
                    | "bWithin"
                    | "aProblem"
                    | "bProblem"
                    | "aSolve"
                    | "bSolve"
                    | "aPick0"
                    | "bPick0"
                    | "aApply0"
                    | "bApply0"
                    | "made0"
                    | "globalZero"
            )
        })
        .collect();
    let saved = execute_asks(&dir, "saved", None, &prefix);
    assert_eq!(saved.code, 0, "{}{}", saved.stdout, saved.stderr);
    let same = execute_asks(&dir, "same", Some("saved"), &prefix);
    assert_eq!(same.code, 0, "{}{}", same.stdout, same.stderr);
    let saved = result_json(&dir, &saved);
    let same = result_json(&dir, &same);
    assert!(warnings(&same).is_empty());
    for key in ["answers", "nodes", "issues"] {
        assert_eq!(get(&saved, key).value, get(&same, key).value);
    }
}

fn repaired_boolean_inputs(extra_law: &str, gate: bool) -> archsig_input::input::InputSources {
    let original = include_str!("fixtures/r2-repaired-locals/definitions.json");
    let mut definitions = original.replace("\"Z\"", "\"Bool\"");
    if gate {
        definitions = definitions.replace(
            r#""name": "quantity","#,
            r#""name":"gate","type":"Bool","meaning":"Enable the Law reading."},
               {"name": "quantity","#,
        );
    }
    let digest = |text: &str| {
        archsig_input::definition::check_definitions(&[("definition0", text.as_bytes())])
            .unwrap()
            .vocabularies()["Assemble"]
            .digest
            .clone()
    };
    let original_digest = digest(original);
    let new_digest = digest(&definitions);
    let law = include_str!("fixtures/r2-repaired-locals/laws.law")
        .replace(&original_digest, &new_digest)
        .replace(":Z", ":Bool")
        .replace("quantity=if q then 1 else 0", "quantity=q")
        .replace("a.quantity+b.quantity=1", "a.quantity!=b.quantity")
        .replace("p.quantity=0", "p.quantity=false")
        .replace("p.quantity=1", "p.quantity=true")
        .replace(
            "  law optional pair",
            &format!("{extra_law}\n  law optional pair"),
        );
    let mut map = include_str!("fixtures/r2-repaired-locals/archmap.json")
        .replace(&original_digest, &new_digest);
    for (id, value) in [
        ("a-quantity", true),
        ("ma-quantity", false),
        ("mb-quantity", true),
        ("b-quantity", false),
    ] {
        map = fixture::atom(map, id, Some(Json::Bool(value)));
    }
    if gate {
        let atoms = ["a", "b", "ma", "mb"].map(|subject| {
            format!(r#"{{"id":"{subject}-gate","subject":"{subject}","field":"Assemble.Part.gate","value":{},"origin":"model"}}"#, subject == "a")
        });
        map = map.replacen(
            r#""atoms":["#,
            &format!(r#""atoms":[{},"#, atoms.join(",")),
            1,
        );
    }
    archsig_input::input::InputSources::from_bytes(
        vec![definitions.into_bytes()],
        law.into_bytes(),
        map.into_bytes(),
    )
}

#[test]
fn repaired_boolean_assembly_uses_the_selected_point_in_finite_law_tables() {
    let dir = workdir("repaired-boolean-assembly");
    write_inputs(&dir, &repaired_boolean_inputs("", false));
    let asks = include_str!("fixtures/r2-repaired-locals/queries.txt")
        .lines()
        .filter(|line| {
            matches!(
                line.split_once('=').unwrap().0,
                "aWithin"
                    | "bWithin"
                    | "aProblem"
                    | "bProblem"
                    | "aSolve"
                    | "bSolve"
                    | "aPick0"
                    | "bPick0"
                    | "aApply0"
                    | "bApply0"
                    | "made0"
                    | "globalZero"
            )
        })
        .collect::<Vec<_>>();
    let run = execute_asks(&dir, "first", None, &asks);
    assert_eq!(run.code, 0, "{}{}", run.stdout, run.stderr);
    let result = result_json(&dir, &run);
    let answers = arr(get(&result, "answers"));
    assert_eq!(answers.len(), asks.len());
    assert!(answers.iter().all(|a| s(get(a, "status")) == "established"));
    let assembly = &answers[answers.len() - 2];
    let global = answers.last().unwrap();
    assert!(has(get(assembly, "outputs"), "algebra"));
    assert_eq!(
        get(get(assembly, "outputs"), "object").value,
        get(get(global, "outputs"), "environment").value
    );
}

#[test]
fn repaired_map_saves_finite_law_domain_and_actual_boolean_counterexample() {
    let dir = workdir("repaired-model-map-finite-law");
    write_inputs(
        &dir,
        &repaired_boolean_inputs(
            "  law optional active(flag:Bool,p:Part):if flag then (not p.gate or not p.quantity) else true;",
            true,
        ),
    );
    let original = include_str!("fixtures/r2-repaired-locals/queries.txt");
    let mut asks = original
        .lines()
        .filter(|ask| {
            let id = ask.split_once('=').unwrap().0;
            !matches!(
                id,
                "madeConflict" | "madePartial" | "mixedOwner" | "moveBetweenChoices"
            )
        })
        .collect::<Vec<_>>();
    asks.extend([
        "same=assemble_map(Assembly.moves,from=$made0.assembly,to=$made0.assembly,x=@v/moveA,y=@v/moveB)",
        "different=assemble_map(Assembly.moves,from=$made0.assembly,to=$made1.assembly,x=@v/moveA,y=@v/moveB)",
    ]);
    let first = execute_asks(&dir, "out", None, &asks);
    let result = result_json(&dir, &first);
    let ns = arr(get(&result, "nodes"));
    let referenced = |r: &archsig_common::json::JNode| {
        let id = s(get(r, "node"));
        ns.iter().find(|n| s(get(n, "id")) == id).unwrap()
    };
    let answers = arr(get(&result, "answers"));
    let same = &answers[answers.len() - 2];
    let different = answers.last().unwrap();
    assert_eq!(s(get(same, "status")), "established", "{}", first.stdout);
    let map = get(referenced(get(get(same, "outputs"), "map")), "value");
    let domains = arr(get(map, "laws"))
        .iter()
        .filter(|row| has(row, "parameter_domains"))
        .collect::<Vec<_>>();
    assert!(!domains.is_empty());
    for row in domains {
        let [domain] = arr(get(row, "parameter_domains")) else {
            panic!("one Bool domain")
        };
        assert_eq!(num(get(domain, "position")), 0);
        assert_eq!(
            arr(get(domain, "source"))
                .iter()
                .map(|value| &value.value)
                .collect::<Vec<_>>(),
            [
                &archsig_common::json::JValue::Bool(false),
                &archsig_common::json::JValue::Bool(true)
            ]
        );
        assert_eq!(get(domain, "images").value, get(domain, "target").value);
    }
    assert_eq!(s(get(different, "status")), "refuted");
    assert!(has(get(different, "outputs"), "configuration_map"));
    let [evidence] = arr(get(different, "counterexamples")) else {
        panic!("one counterexample")
    };
    let evidence = referenced(evidence);
    let counterexample = get(get(evidence, "value"), "data");
    let observed = |key| &get(referenced(get(counterexample, key)), "value").value;
    assert_eq!(observed("left"), &archsig_common::json::JValue::Bool(true));
    assert_eq!(
        observed("right"),
        &archsig_common::json::JValue::Bool(false)
    );
    let flag = arr(get(counterexample, "bindings"))
        .iter()
        .find(|binding| s(get(binding, "name")) == "flag")
        .expect("actual flag");
    assert_eq!(
        get(referenced(get(flag, "value")), "value").value,
        archsig_common::json::JValue::Bool(true)
    );
    let facts = arr(get(counterexample, "facts"));
    assert!(facts.iter().any(|fact| {
        has(fact, "atom")
            && s(get(fact, "atom")) == "a-gate"
            && s(get(fact, "field")) == "Assemble.Part.gate"
    }));
    assert!(
        !facts
            .iter()
            .any(|fact| has(fact, "field") && s(get(fact, "field")) == "Assemble.Part.quantity")
    );
    let occurrences = get(counterexample, "law_transport");
    for (end, assembly) in [("source", "made0"), ("target", "made1")] {
        let evidence = get(occurrences, end);
        let actual_assembly = answers
            .iter()
            .find(|a| s(get(a, "id")) == assembly)
            .unwrap();
        assert_eq!(
            get(evidence, "assembly").value,
            get(get(actual_assembly, "outputs"), "assembly").value
        );
        assert_eq!(
            s(get(referenced(get(evidence, "object")), "type")),
            "ObjectComponent"
        );
        let law = referenced(get(evidence, "law"));
        assert_eq!(s(get(law, "type")), "LawInstance");
        let occurrence = get(law, "value");
        assert_eq!(s(get(occurrence, "name")), "Assembly.active");
        let [parameter] = arr(get(occurrence, "parameters")) else {
            panic!("one Bool parameter");
        };
        assert_eq!(s(get(parameter, "name")), "flag");
        assert_eq!(s(get(parameter, "type")), "Bool");
    }
    let [reason] = arr(get(different, "reasons")) else {
        panic!("one failed Law condition");
    };
    let location = get(reason, "location");
    assert_eq!(s(get(location, "input")), "law");
    let span = arr(get(location, "span"));
    let source_law = std::fs::read_to_string(dir.join("l.law")).unwrap();
    assert!(
        source_law[num(&span[0]) as usize..num(&span[1]) as usize].contains("active(flag:Bool")
    );
    let replay = execute_asks(&dir, "checked", Some("out"), &asks);
    assert_eq!(replay.code, first.code);
    let replay = result_json(&dir, &replay);
    assert!(warnings(&replay).is_empty());
    assert_eq!(get(&result, "answers").value, get(&replay, "answers").value);
}

#[test]
fn repaired_map_skips_the_body_of_a_law_when_its_guard_is_false() {
    let dir = workdir("repaired-model-map-false-guard");
    write_inputs(
        &dir,
        &repaired_boolean_inputs(
            "view owned(r:Root,p:Part[r]):Bool=true;
             law optional scoped(p:Part,q:Bool) when false: forall b:Root . owned(b,p);",
            false,
        ),
    );
    let mut asks = include_str!("fixtures/r2-repaired-locals/queries.txt")
        .lines()
        .filter(|ask| {
            matches!(
                ask.split_once('=').unwrap().0,
                "aWithin"
                    | "bWithin"
                    | "aProblem"
                    | "bProblem"
                    | "aSolve"
                    | "bSolve"
                    | "aPick0"
                    | "bPick0"
                    | "aApply0"
                    | "bApply0"
                    | "made0"
            )
        })
        .collect::<Vec<_>>();
    asks.extend([
        "off=check(Assembly.scoped,p=@v/a,on=$made0.object)",
        "same=assemble_map(Assembly.moves,from=$made0.assembly,to=$made0.assembly,x=@v/moveA,y=@v/moveB)",
    ]);
    let first = execute_asks(&dir, "out", None, &asks);
    assert_eq!(first.code, 0, "{}{}", first.stdout, first.stderr);
    let result = result_json(&dir, &first);
    let answers = arr(get(&result, "answers"));
    assert_eq!(answers.len(), asks.len());
    assert!(answers.iter().all(|a| s(get(a, "status")) == "established"));
    assert!(has(get(answers.last().unwrap(), "outputs"), "map"));
}

fn repaired_folding_fixture(dir: &Path, parameter_type: &str) -> Vec<String> {
    let input = repaired_boolean_inputs(
        &format!("law optional aConstant(r:Root,t:{parameter_type}):true;"),
        false,
    );
    let law = std::str::from_utf8(input.law().bytes())
        .unwrap()
        .replace(
            "law optional pair(a:Part,b:Part):a.quantity!=b.quantity;",
            "",
        )
        .replace(
            "law optional boundary(p:Part):p.quantity=false;",
            "law optional boundary(r:Root):true;",
        )
        .replace(
            "law optional boundaryOne(p:Part):p.quantity=true;",
            "law optional boundaryOne(r:Root):true;",
        );
    let mut map = fixture::without_arrows(
        std::str::from_utf8(input.archmap().bytes())
            .unwrap()
            .to_owned(),
    );
    for id in ["moveA-steps", "moveB-steps"] {
        map = fixture::atom(map, id, Some(Json::Arr(vec![])));
    }
    let reference = |subject| Json::Arr(vec![Json::str("v"), Json::str(subject)]);
    map = fixture::atom(map, "moveB-to", Some(reference("A")));
    let pairs = [("mb", "ma"), ("b", "a")]
        .into_iter()
        .map(|(source, target)| Json::Arr(vec![reference(source), reference(target)]))
        .collect();
    map = fixture::atom(map, "moveB-parts", Some(Json::Arr(pairs)));
    write_inputs(
        dir,
        &archsig_input::input::InputSources::from_bytes(
            vec![input.definitions()[0].bytes().to_vec()],
            law.into_bytes(),
            map.into_bytes(),
        ),
    );
    let mut asks = include_str!("fixtures/r2-repaired-locals/queries.txt")
        .lines()
        .filter(|ask| {
            matches!(
                ask.split_once('=').unwrap().0,
                "aWithin"
                    | "bWithin"
                    | "aProblem"
                    | "bProblem"
                    | "aSolve"
                    | "bSolve"
                    | "aPick0"
                    | "bPick0"
                    | "aApply0"
                    | "bApply0"
                    | "made0"
            )
        })
        .map(|ask| {
            if ask.contains("Problem=prepare") {
                ask.replace("p=@v/ma", "r=@v/A")
                    .replace("p=@v/mb", "r=@v/B")
            } else {
                ask.to_owned()
            }
        })
        .collect::<Vec<_>>();
    asks.push("fold=assemble_map(Assembly.moves,from=$made0.assembly,to=$made0.assembly,x=@v/moveA,y=@v/moveB)".to_owned());
    asks
}

#[test]
fn repaired_map_saves_the_colliding_finite_parameter_values() {
    let dir = workdir("repaired-model-map-parameter-collision");
    let asks = repaired_folding_fixture(&dir, "(Part,Bool)");
    let asks = asks.iter().map(String::as_str).collect::<Vec<_>>();
    let run = execute_asks(&dir, "out", None, &asks);
    assert_eq!(run.code, 1, "{}{}", run.stdout, run.stderr);
    let result = result_json(&dir, &run);
    let answer = arr(get(&result, "answers")).last().unwrap();
    assert_eq!(s(get(answer, "status")), "refuted");
    assert!(has(get(answer, "outputs"), "configuration_map"));
    let nodes = arr(get(&result, "nodes"));
    let dereference = |r: &archsig_common::json::JNode| {
        nodes
            .iter()
            .find(|n| s(get(n, "id")) == s(get(r, "node")))
            .unwrap()
    };
    let [point] = arr(get(answer, "counterexamples")) else {
        panic!("one parameter transport failure");
    };
    let data = get(get(dereference(point), "value"), "data");
    let witness = get(data, "parameter_transport");
    assert_eq!(num(get(witness, "position")), 1);
    assert_eq!(s(get(witness, "kind")), "collision");
    let [first, second] = arr(get(witness, "source_indices")) else {
        panic!("two distinct source values");
    };
    let (first, second) = (num(first) as usize, num(second) as usize);
    let source = arr(get(witness, "source"));
    let target = arr(get(witness, "target"));
    let images = arr(get(witness, "images"));
    assert_ne!(source[first].value, source[second].value);
    assert_eq!(images[first].value, images[second].value);
    assert_eq!(
        images[first].value,
        target[num(get(witness, "target_index")) as usize].value
    );
    assert_eq!(
        get(dereference(get(data, "left")), "value").value,
        source[first].value
    );
    assert_eq!(
        get(dereference(get(data, "right")), "value").value,
        source[second].value
    );
    let supporting_law = dereference(get(get(get(data, "law_transport"), "source"), "law"));
    assert_eq!(
        s(get(get(supporting_law, "value"), "name")),
        "Assembly.aConstant"
    );

    let replay = execute_asks(&dir, "checked", Some("out"), &asks);
    assert_eq!(replay.code, run.code);
    let replay = result_json(&dir, &replay);
    assert!(warnings(&replay).is_empty());
    assert_eq!(get(&replay, "answers").value, get(&result, "answers").value);
}

#[test]
fn repaired_map_saves_an_outside_candidate_as_diagnostic_data() {
    let dir = workdir("repaired-model-map-outside-target");
    let asks = repaired_folding_fixture(&dir, "Map<Part,Root>");
    let asks = asks.iter().map(String::as_str).collect::<Vec<_>>();
    let run = execute_asks(&dir, "out", None, &asks);
    assert_eq!(run.code, 1, "{}{}", run.stdout, run.stderr);
    let result = result_json(&dir, &run);
    let answer = arr(get(&result, "answers")).last().unwrap();
    assert_eq!(s(get(answer, "status")), "refuted");
    assert!(has(get(answer, "outputs"), "configuration_map"));
    let nodes = arr(get(&result, "nodes"));
    let dereference = |r: &archsig_common::json::JNode| {
        nodes
            .iter()
            .find(|n| s(get(n, "id")) == s(get(r, "node")))
            .unwrap()
    };
    let [point] = arr(get(answer, "counterexamples")) else {
        panic!("one parameter transport failure");
    };
    let data = get(get(dereference(point), "value"), "data");
    let witness = get(data, "parameter_transport");
    assert_eq!(s(get(witness, "kind")), "outside_target");
    assert_eq!(num(get(witness, "position")), 1);
    let [i] = arr(get(witness, "source_indices")) else {
        panic!("one source value")
    };
    let i = num(i) as usize;
    let left = dereference(get(data, "left"));
    let right = dereference(get(data, "right"));
    let source = &arr(get(witness, "source"))[i];
    let image = &arr(get(witness, "images"))[i];
    assert_eq!(get(left, "value").value, source.value);
    let keys = |map: &archsig_common::json::JNode| {
        arr(map)
            .iter()
            .map(|entry| s(&arr(&arr(entry)[0])[1]).to_owned())
            .collect::<Vec<_>>()
    };
    assert_eq!(keys(source), ["a", "b", "ma", "mb"]);
    assert_eq!(keys(image), ["a", "ma", "mb"]);
    assert_eq!(s(&arr(get(right, "type"))[0]), "List");
    assert_eq!(get(right, "value").value, get(witness, "target").value);
    for value in arr(get(right, "value")) {
        assert_eq!(keys(value), ["a", "b", "ma", "mb"]);
    }
}
