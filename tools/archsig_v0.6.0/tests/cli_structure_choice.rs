use crate::common::cli::*;
use archsig_common::{
    canonical::Json,
    json::{JNode, JValue},
};
use std::collections::BTreeMap;

#[test]
fn a_checked_design_assignment_selects_a_typed_assembly_and_migration() {
    let dir = workdir("structure-choice");
    for (name, bytes) in [
        (
            "definitions.json",
            include_bytes!("fixtures/r2-structure-choice/definitions.json").as_slice(),
        ),
        (
            "laws.law",
            include_bytes!("fixtures/r2-structure-choice/laws.law").as_slice(),
        ),
        (
            "archmap.json",
            include_bytes!("fixtures/r2-structure-choice/archmap.json").as_slice(),
        ),
    ] {
        std::fs::write(dir.join(name), bytes).unwrap();
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
        "out",
    ];
    for ask in include_str!("fixtures/r2-structure-choice/queries.txt").lines() {
        args.extend(["--ask", ask]);
    }
    let run = run_binary(&dir, &args);
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
    let subject = |reference: &JNode| s(&arr(value(reference))[1]);
    let expected =
        archsig_common::json::parse(include_bytes!("fixtures/r2-structure-choice/expected.json"))
            .unwrap();
    let JValue::Obj(expected) = &expected.value else {
        panic!("expected answers")
    };
    let expected = expected
        .iter()
        .map(|(id, status)| (id.as_str(), s(status)))
        .collect::<BTreeMap<_, _>>();
    let actual = answers
        .iter()
        .map(|a| (s(get(a, "id")), s(get(a, "status"))))
        .collect::<BTreeMap<_, _>>();
    assert_eq!(actual.len(), answers.len());
    assert_eq!(actual, expected);

    for (layout, selected, root, value_) in [
        ("layout0", "planApply0", "native-T3", false),
        ("layout1", "planApply1", "rust-T3", true),
        ("otherLayout", "otherApply1", "native-T3", true),
    ] {
        let assembly = value(output(layout, "assembly"));
        assert_eq!(
            get(assembly, "design").value,
            output(selected, "object").value
        );
        let [local] = arr(get(assembly, "inclusions")) else {
            panic!("one selected owner")
        };
        assert_eq!(subject(get(value(get(local, "fragment")), "root")), root);
        let [change] = arr(get(value(output(selected, "object")), "overrides")) else {
            panic!("selection coordinate")
        };
        assert_eq!(value(get(change, "value")).value, JValue::Bool(value_));
    }
    let [imposter] = arr(get(value(output("otherApply1", "object")), "overrides")) else {
        panic!("another assignment")
    };
    assert_eq!(value(get(imposter, "value")).value, JValue::Bool(true));
    for rejected in ["wrongIdentity", "wrongDomain", "wrongEndpoint"] {
        let reasons = arr(get(answer(rejected), "reasons"));
        assert!(
            reasons
                .iter()
                .any(|r| s(get(r, "code")) == "condition_failed")
        );
    }
    for (id, expected, solve) in [
        ("wrongDomain", "apply_same_candidate_domain", "otherSolve"),
        (
            "excludedAssignment",
            "apply_assignment_in_solution_set",
            "restrictedSolve",
        ),
    ] {
        let operands = arr(get(value(output(id, "proposition")), "operands"));
        assert_eq!(s(value(&operands[0])), expected);
        assert_eq!(operands.len(), 3);
        assert_eq!(operands[1].value, output("planPick1", "assignment").value);
        assert_eq!(operands[2].value, output(solve, "solutions").value);
    }
    let [failure] = arr(get(answer("wrongIdentity"), "counterexamples")) else {
        panic!("design identity counterexample");
    };
    assert!(s(get(get(value(failure), "data"), "condition_detail")).contains("元root"));
    let details = get(value(failure), "data");
    assert_eq!(subject(get(details, "left")), "plan");
    assert_eq!(subject(get(details, "right")), "lookalike");
    for id in ["layout0", "layout1", "migrate", "wrongEndpoint"] {
        assert_eq!(
            s(get(get(answer(id), "scope"), "domain")),
            "finite_model",
            "{id}"
        );
    }
    let [provenance] = arr(get(answer("wrongProvenance"), "counterexamples")) else {
        panic!("provenance counterexample");
    };
    let provenance = get(value(provenance), "data");
    assert_eq!(s(value(get(provenance, "left"))), "apply.object");
    assert_eq!(
        get(provenance, "right").value,
        output("observedDesign", "object").value
    );
    let [endpoint] = arr(get(answer("wrongEndpoint"), "counterexamples")) else {
        panic!("endpoint counterexample");
    };
    let endpoint = get(value(endpoint), "data");
    assert_eq!(subject(get(endpoint, "left")), "rust-T3");
    assert_eq!(
        get(endpoint, "right").value,
        output("layout0", "assembly").value
    );
    assert!(s(get(endpoint, "condition_detail")).contains("target fragments"));
    let migration = value(output("migrate", "map"));
    assert_eq!(
        get(migration, "target_assembly").value,
        output("layout1", "assembly").value
    );
    assert_eq!(
        get(migration, "target").value,
        output("lawAfter", "environment").value
    );
    let [generator] = arr(get(migration, "generators")) else {
        panic!("one named operation")
    };
    assert_eq!(
        s(get(
            get(node(get(generator, "proposition")), "judgment"),
            "status"
        )),
        "established"
    );
    assert_eq!(
        subject(get(get(value(get(generator, "source")), "name"), "subject")),
        "native-T3-consume"
    );
    assert_eq!(
        subject(get(get(value(get(generator, "target")), "name"), "subject")),
        "rust-T3-consume"
    );
    for request in ["planLabel", "otherLabel"] {
        assert_eq!(s(value(output(request, "value"))), "shared-label");
    }

    args[8] = "same";
    args.extend(["--reuse", "out"]);
    let same = run_binary(&dir, &args);
    assert_eq!(same.code, 1, "{}{}", same.stdout, same.stderr);
    let same = result_json(&dir, &same);
    assert!(warnings(&same).is_empty());
    for field in ["answers", "nodes", "issues"] {
        assert_eq!(get(&result, field).value, get(&same, field).value);
    }
    let map = include_str!("fixtures/r2-structure-choice/archmap.json");
    let before = concat!(
        "\"id\": \"rust-T3-consume.to\",\n          \"subject\": \"rust-T3-consume\",\n",
        "          \"field\": \"E12.Consume.to\",\n          \"value\": [\n            \"comparison\",\n            \"rust-T3-after\"",
    );
    let changed = map.replacen(
        before,
        &before.replace("rust-T3-after", "rust-T3-before"),
        1,
    );
    assert_ne!(changed, map);
    std::fs::write(dir.join("archmap.json"), changed).unwrap();
    args.truncate(args.len() - 2);
    args[8] = "changed-operation";
    let changed = run_binary(&dir, &args);
    assert_eq!(changed.code, 2, "{}{}", changed.stdout, changed.stderr);
    let changed = result_json(&dir, &changed);
    let answers = arr(get(&changed, "answers"));
    let layout = answers
        .iter()
        .find(|a| s(get(a, "id")) == "layout1")
        .unwrap();
    let map = answers
        .iter()
        .find(|a| s(get(a, "id")) == "migrate")
        .unwrap();
    assert_eq!(s(get(layout, "status")), "established");
    assert_eq!(s(get(map, "status")), "refuted");
    let [failure] = arr(get(map, "counterexamples")) else {
        panic!("operation refutation");
    };
    let nodes = arr(get(&changed, "nodes"));
    let value = |reference: &JNode| {
        get(
            nodes
                .iter()
                .find(|node| s(get(node, "id")) == s(get(reference, "node")))
                .unwrap(),
            "value",
        )
    };
    let data = get(value(failure), "data");
    assert!(s(get(data, "condition_detail")).contains("observed reference"));
    assert_eq!(s(&arr(value(get(data, "left")))[1]), "rust-T3-after");
    assert_eq!(s(&arr(value(get(data, "right")))[1]), "rust-T3-before");
    let original = include_str!("fixtures/r2-structure-choice/archmap.json");
    let fact = concat!(
        "\"id\": \"rust-T3-after.quantity\",\n          \"subject\": \"rust-T3-after\",\n",
        "          \"field\": \"E12.State.quantity\",\n          \"value\": \"16\"",
    );
    let changed = original.replacen(fact, &fact.replace("16", "17"), 1);
    assert_ne!(changed, original);
    std::fs::write(dir.join("archmap.json"), changed).unwrap();
    args[8] = "changed-law";
    let run = run_binary(&dir, &args);
    assert_eq!(run.code, 2, "{}{}", run.stdout, run.stderr);
    let result = result_json(&dir, &run);
    let answers = arr(get(&result, "answers"));
    let answer = |id| answers.iter().find(|a| s(get(a, "id")) == id).unwrap();
    assert_eq!(s(get(answer("layout1"), "status")), "established");
    let migration = answer("migrate");
    assert_eq!(s(get(migration, "status")), "refuted");
    let outputs = get(migration, "outputs");
    assert!(has(outputs, "configuration_map"));
    assert!(!has(outputs, "map"));
    let [counterexample] = arr(get(migration, "counterexamples")) else {
        panic!("actual comparison in the Law refutation");
    };
    let nodes = arr(get(&result, "nodes"));
    let value = |reference: &JNode| {
        get(
            nodes
                .iter()
                .find(|node| s(get(node, "id")) == s(get(reference, "node")))
                .unwrap(),
            "value",
        )
    };
    let evidence = get(value(counterexample), "data");
    assert_eq!(value(get(evidence, "left")).value, JValue::Bool(true));
    assert_eq!(value(get(evidence, "right")).value, JValue::Bool(false));
    let proposition = value(get(outputs, "proposition"));
    assert_eq!(
        arr(get(proposition, "operands"))
            .iter()
            .filter(|operand| nodes.iter().any(|node| {
                s(get(node, "id")) == s(get(operand, "node"))
                    && s(get(node, "type")) == "LawInstance"
            }))
            .count(),
        2
    );
    let [reason] = arr(get(migration, "reasons")) else {
        panic!("one actual Law refutation");
    };
    assert_eq!(s(get(get(reason, "location"), "input")), "law");

    std::fs::write(dir.join("archmap.json"), original).unwrap();
    let law = include_str!("fixtures/r2-structure-choice/laws.law").replace(
        "routes(t:Route):Set<Route> = set<Route>{t}",
        "routes(t:Route,p:Design):Set<Route> = if p.split then set<Route>{t} else set<Route>{}",
    );
    std::fs::write(dir.join("laws.law"), law).unwrap();
    let map_asks = args[9..]
        .chunks_exact(2)
        .map(|pair| {
            let ask = pair[1];
            if ask.starts_with("migrate=") || ask.starts_with("wrongEndpoint=") {
                format!("{},p=@comparison/plan)", ask.strip_suffix(')').unwrap())
            } else {
                ask.to_owned()
            }
        })
        .collect::<Vec<_>>();
    let mut conditional_args = args[..9].to_vec();
    conditional_args[8] = "conditional-route";
    for ask in &map_asks {
        conditional_args.extend(["--ask", ask]);
    }
    let run = run_binary(&dir, &conditional_args);
    let result = result_json(&dir, &run);
    let answers = arr(get(&result, "answers"));
    let answer = |id| answers.iter().find(|a| s(get(a, "id")) == id).unwrap();
    let nodes = arr(get(&result, "nodes"));
    let resolve = |reference: &JNode| {
        nodes
            .iter()
            .find(|node| s(get(node, "id")) == s(get(reference, "node")))
            .unwrap()
    };
    for (id, expected, target, design) in [
        ("migrate", "established", "layout1", "planApply1"),
        ("wrongEndpoint", "refuted", "layout0", "planApply0"),
    ] {
        let map = answer(id);
        assert_eq!(s(get(map, "status")), expected, "{}", run.stdout);
        let claim = resolve(get(get(map, "outputs"), "proposition"));
        let endpoint = get(get(answer(target), "outputs"), "assembly");
        let applied = get(get(answer(design), "outputs"), "object");
        assert!(
            arr(get(get(claim, "value"), "operands"))
                .iter()
                .any(|operand| {
                    let local = resolve(operand);
                    s(get(local, "type")) == "Proposition" && {
                        let operands = arr(get(get(local, "value"), "operands"));
                        operands
                            .iter()
                            .any(|operand| operand.value == endpoint.value)
                            && operands
                                .iter()
                                .any(|operand| operand.value == applied.value)
                    }
                }),
            "{id}: actual endpoint and design point"
        );
    }
    let law = include_str!("fixtures/r2-structure-choice/laws.law").replace("  view selected", concat!(
        "  change chooseDirection(p:Design,q:Bool)=p with {reversed=q};
",
        "  view sourceSelected(p:Design,t:Route):Set<Root> = if p.split then set<Root>{t.from} else set<Root>{t.to};
",
        "  view routesByTarget(p:Design,t:Route):Set<Route> = if p.split then set<Route>{} else set<Route>{t};
",
        "  view routesBySource(p:Design,t:Route):Set<Route> = if p.split then set<Route>{t} else set<Route>{};
",
        "  view selected",
    ));
    std::fs::write(dir.join("laws.law"), law).unwrap();
    let fixture_asks = include_str!("fixtures/r2-structure-choice/queries.txt")
        .lines()
        .collect::<Vec<_>>();
    let mut effective_args = args[..9].to_vec();
    effective_args[8] = "target-effective-state";
    for ask in fixture_asks[1..8].iter().copied().chain([
        "targetProblem=prepare(E12Compare.allowed,using=E12Compare.chooseDirection,on=@comparison/plan,p=@comparison/plan)",
        "targetSolve=solve($targetProblem.problem,within=$planWithin.value)",
        "targetPick1=candidate($targetSolve.solutions,index=1)",
        "targetApply1=apply($targetPick1.assignment,in=$targetSolve.solutions)",
        "source=assemble(E12Compare.sourceSelected,on=@comparison/native-output1,along=E12Compare.interfaces,p=@comparison/plan,t=@comparison/move-T3,design.p=$planApply1.object)",
        "target=assemble(E12Compare.selected,on=@comparison/rust-output1,along=E12Compare.interfaces,p=@comparison/plan,t=@comparison/move-T3,design.p=$targetApply1.object)",
        "byTarget=assemble_map(E12Compare.routesByTarget,from=$source.assembly,to=$target.assembly,p=@comparison/plan,t=@comparison/move-T3)",
        "bySource=assemble_map(E12Compare.routesBySource,from=$source.assembly,to=$target.assembly,p=@comparison/plan,t=@comparison/move-T3)",
    ]) {
        effective_args.extend(["--ask", ask]);
    }
    let run = run_binary(&dir, &effective_args);
    assert_eq!(run.code, 1, "{}{}", run.stdout, run.stderr);
    let result = result_json(&dir, &run);
    let answers = arr(get(&result, "answers"));
    for (id, expected) in [
        ("source", "established"),
        ("target", "established"),
        ("byTarget", "established"),
        ("bySource", "refuted"),
    ] {
        let answer = answers.iter().find(|a| s(get(a, "id")) == id).unwrap();
        assert_eq!(s(get(answer, "status")), expected, "{id}");
    }
}

#[test]
fn a_selected_shared_view_refutation_is_scoped_to_its_concrete_point() {
    let dir = workdir("structure-choice-scope");
    std::fs::write(
        dir.join("definitions.json"),
        include_bytes!("fixtures/r2-structure-choice/definitions.json"),
    )
    .unwrap();
    let map = include_str!("fixtures/r2-structure-choice/archmap.json");
    std::fs::write(dir.join("archmap.json"), map).unwrap();
    let law = include_str!("fixtures/r2-structure-choice/laws.law")
        .replace("  view selected", concat!(
            "  view external(p:Design):Design=let k=forall z:Z . z=z in if k then p else p;
",
            "  view same(f:Set<Root>):Bool=forall r in f . r=r;
",
            "  view holds(s:State):Bool=forall v in list<Option<Path<State,State>>>[some(identity(s))] . v=v;
",
            "  view selected",
        ))
        .replace("selected(p:Design,t:Route)", "selected(p:Design,t:Route,x:State,y:State)")
        .replace(
            "if p.split!=p.reversed then set<Root>{t.to}",
            concat!(
                "if holds(x) and holds(x) and (forall b in list<Bool>[true] . p.split=b) ",
                "and (forall ignored in list<Bool>[true] . y.quantity=0) then ",
                "(if (forall absent in list<Bool>[true] . y.quantity=0) then set<Root>{t.to} else set<Root>{t.to})",
            ),
        )
        .replace("interfaces(p:Design,t:Route):Unit = unit", "interfaces(p:Design,t:Route,x:State,y:State):List<(State,State)> = if p.split then list<(State,State)>[(x,y)] else list<(State,State)>[]");
    std::fs::write(dir.join("laws.law"), law).unwrap();
    let original = include_str!("fixtures/r2-structure-choice/queries.txt")
        .lines()
        .collect::<Vec<_>>();
    let mut asks = original[1..8]
        .iter()
        .map(|ask| (*ask).to_owned())
        .collect::<Vec<_>>();
    asks.push("bindDesign=evaluate(E12Compare.external,p=@comparison/plan)".into());
    let endpoints = ",x=@comparison/native-T3-before,y=@comparison/rust-T3-before";
    for (id, selected) in [
        ("fixed0", ",design.p=$planApply0.object"),
        ("fixed1", ",design.p=$planApply1.object"),
    ] {
        asks.push(format!("{id}=assemble(E12Compare.selected,on=@comparison/rust-output1,along=E12Compare.interfaces,p=$bindDesign.value,t=@comparison/move-T3{endpoints}{selected})"));
    }
    asks.push("reuseFragments=evaluate(E12Compare.same,f=$fixed0.assembly.fragments)".into());
    let mut args = vec![
        "run",
        "--atom-definition",
        "definitions.json",
        "--law",
        "laws.law",
        "--archmap",
        "archmap.json",
        "--out",
        "out",
    ];
    for ask in &asks {
        args.extend(["--ask", ask]);
    }
    let run = run_binary(&dir, &args);
    assert_eq!(run.code, 1, "{}{}", run.stdout, run.stderr);
    let result = result_json(&dir, &run);
    let answers = arr(get(&result, "answers"));
    let fixed0 = answers
        .iter()
        .find(|a| s(get(a, "id")) == "fixed0")
        .unwrap();
    let fixed1 = answers
        .iter()
        .find(|a| s(get(a, "id")) == "fixed1")
        .unwrap();
    let reused = answers
        .iter()
        .find(|a| s(get(a, "id")) == "reuseFragments")
        .unwrap();
    assert_eq!(s(get(reused, "status")), "established");
    assert_eq!(s(get(fixed0, "status")), "established");
    assert_eq!(s(get(fixed1, "status")), "refuted");
    assert_eq!(s(get(get(fixed1, "scope"), "domain")), "finite_model");
    assert_eq!(s(get(get(fixed0, "scope"), "domain")), "finite_model");
    let nodes = arr(get(&result, "nodes"));
    let node = |reference: &JNode| {
        nodes
            .iter()
            .find(|node| s(get(node, "id")) == s(get(reference, "node")))
            .unwrap()
    };
    for answer in [fixed0, fixed1] {
        let quantifiers = arr(get(get(answer, "scope"), "quantifiers"));
        assert!(quantifiers.iter().any(|q| s(get(q, "name")) == "z"));
        let paths = quantifiers
            .iter()
            .filter(|q| s(get(q, "name")) == "v")
            .collect::<Vec<_>>();
        assert_eq!(paths.len(), 2);
        for path in paths {
            let domain = get(node(get(path, "domain")), "value");
            let [option] = arr(get(domain, "elements")) else {
                panic!("singleton optional Path")
            };
            let value = get(node(get(get(node(option), "value"), "some")), "value");
            assert!(arr(get(value, "generators")).is_empty());
            let source = get(node(get(value, "source")), "value");
            assert_eq!(s(&arr(source)[1]), "native-T3-before");
        }
        let binder = quantifiers
            .iter()
            .find(|q| s(get(q, "name")) == "b")
            .unwrap();
        let domain = get(node(get(binder, "domain")), "value");
        assert_eq!(s(get(domain, "kind")), "finite");
        let [element] = arr(get(domain, "elements")) else {
            panic!("the actual singleton Bool domain");
        };
        assert_eq!(get(node(element), "value").value, JValue::Bool(true));
    }
    let map = archsig_common::json::parse(map.as_bytes()).unwrap();
    let mut map = crate::common::architecture_environment::owned(&map);
    let Json::Obj(document) = &mut map else {
        panic!("map")
    };
    let Json::Arr(snapshots) = document.get_mut("snapshots").unwrap() else {
        panic!("snapshots")
    };
    let Json::Obj(snapshot) = &mut snapshots[0] else {
        panic!("snapshot")
    };
    let Json::Arr(atoms) = snapshot.get_mut("atoms").unwrap() else {
        panic!("atoms")
    };
    let original = atoms.len();
    atoms.retain(|atom| !matches!(atom, Json::Obj(fields)
        if fields["subject"] == Json::str("rust-T3-before") && fields["field"] == Json::str("E12.State.quantity")));
    assert_eq!(atoms.len() + 1, original);
    std::fs::write(dir.join("archmap.json"), map.canonical()).unwrap();
    args[8] = "inactive";
    args.truncate(args.len() - 4);
    let run = run_binary(&dir, &args);
    assert_eq!(run.code, 0, "{}{}", run.stdout, run.stderr);
    let result = result_json(&dir, &run);
    let fixed0 = arr(get(&result, "answers"))
        .iter()
        .find(|a| s(get(a, "id")) == "fixed0")
        .unwrap();
    let quantifiers = arr(get(get(fixed0, "scope"), "quantifiers"));
    assert!(
        quantifiers
            .iter()
            .all(|q| !matches!(s(get(q, "name")), "absent" | "ignored"))
    );
}

#[test]
fn selected_domains_survive_an_unsupported_view_and_its_consumers() {
    let dir = workdir("structure-choice-unsupported-domain");
    std::fs::write(
        dir.join("definitions.json"),
        include_bytes!("fixtures/r2-structure-choice/definitions.json"),
    )
    .unwrap();
    let map = include_str!("fixtures/r2-structure-choice/archmap.json")
        .replace(
            r#""origins": ["#,
            r#""origins": [
          {"id":"alternate","mode":"proposed","method":"fixture","note":"scope","locations":[]},"#,
        )
        .replace(
            r#""snapshots": ["#,
            r#""snapshots": [
          {"id":"alternate","origin":"alternate",
           "subjects":[{"id":"extra","type":"E12.Root","origin":"alternate"}],"atoms":[]},"#,
        );
    std::fs::write(dir.join("archmap.json"), map).unwrap();
    let law = include_str!("fixtures/r2-structure-choice/laws.law").replace(
        "if p.split!=p.reversed then set<Root>{t.to} else set<Root>{t.from}",
        "let seen=forall b:Root . b=b in if seen and (exists z:Z . z*z=2) then set<Root>{t.to} else set<Root>{t.from}",
    );
    std::fs::write(dir.join("laws.law"), law).unwrap();
    let original = include_str!("fixtures/r2-structure-choice/queries.txt")
        .lines()
        .collect::<Vec<_>>();
    let mut asks = original[1..8].to_vec();
    asks.extend([
        "layout=assemble(E12Compare.selected,on=@comparison/rust-output1,along=E12Compare.interfaces,p=@comparison/plan,t=@comparison/move-T3,design.p=$planApply1.object)",
        "blocked=check(E12Compare.consumed,on=$layout.object,s=@comparison/rust-T3-after)",
    ]);
    let mut args = vec![
        "run",
        "--atom-definition",
        "definitions.json",
        "--law",
        "laws.law",
        "--archmap",
        "archmap.json",
        "--out",
        "out",
    ];
    for ask in &asks {
        args.extend(["--ask", ask]);
    }
    let run = run_binary(&dir, &args);
    assert_eq!(run.code, 2, "{}{}", run.stdout, run.stderr);
    let result = result_json(&dir, &run);
    let answers = arr(get(&result, "answers"));
    let layout = answers
        .iter()
        .find(|a| s(get(a, "id")) == "layout")
        .unwrap();
    assert_eq!(s(get(layout, "status")), "undetermined");
    let quantifiers = arr(get(get(layout, "scope"), "quantifiers"));
    let finite = quantifiers
        .iter()
        .find(|q| s(get(q, "name")) == "b")
        .unwrap();
    let nodes = arr(get(&result, "nodes"));
    let domain = nodes
        .iter()
        .find(|node| s(get(node, "id")) == s(get(get(finite, "domain"), "node")))
        .unwrap();
    assert!(
        arr(get(get(domain, "value"), "elements"))
            .iter()
            .any(|element| {
                let node = nodes
                    .iter()
                    .find(|n| s(get(n, "id")) == s(get(element, "node")))
                    .unwrap();
                let value = arr(get(node, "value"));
                s(&value[0]) == "alternate" && s(&value[1]) == "extra"
            })
    );
    let blocked = answers
        .iter()
        .find(|a| s(get(a, "id")) == "blocked")
        .unwrap();
    for answer in [layout, blocked] {
        let scope = get(answer, "scope");
        assert!(
            arr(get(scope, "snapshots"))
                .iter()
                .any(|value| s(value) == "alternate")
        );
        assert!(
            arr(get(scope, "modes"))
                .iter()
                .any(|value| s(value) == "proposed")
        );
    }
    let reasons = arr(get(blocked, "reasons"));
    assert!(
        reasons
            .iter()
            .any(|reason| s(get(reason, "code")) == "dependency_blocked")
    );
    assert!(
        arr(get(&result, "issues"))
            .iter()
            .all(|reason| s(get(reason, "code")) != "internal")
    );
    let law = include_str!("fixtures/r2-structure-choice/laws.law").replace(
        "  view selected",
        "  law required ordered(s:State):s.quantity<20;\n  view selected",
    );
    std::fs::write(dir.join("laws.law"), law).unwrap();
    args[8] = "later-algebra";
    let run = run_binary(&dir, &args);
    assert_eq!(run.code, 2, "{}{}", run.stdout, run.stderr);
    let result = result_json(&dir, &run);
    let answers = arr(get(&result, "answers"));
    let layout = answers
        .iter()
        .find(|a| s(get(a, "id")) == "layout")
        .unwrap();
    let applied = answers
        .iter()
        .find(|a| s(get(a, "id")) == "planApply1")
        .unwrap();
    assert_eq!(s(get(layout, "status")), "undetermined");
    let nodes = arr(get(&result, "nodes"));
    let node = |reference: &JNode| {
        nodes
            .iter()
            .find(|node| s(get(node, "id")) == s(get(reference, "node")))
            .unwrap()
    };
    let claim = node(get(get(layout, "outputs"), "proposition"));
    let operands = arr(get(get(claim, "value"), "operands"));
    let applied = get(get(applied, "outputs"), "object");
    assert!(operands.iter().any(|value| value.value == applied.value));
    assert_eq!(
        operands
            .iter()
            .filter(|value| matches!(&get(node(value), "type").value, JValue::Str(name) if name == "Expression"))
            .count(),
        2
    );
    assert!(operands.iter().any(|value| {
        let value = get(node(value), "value");
        matches!(&value.value, JValue::Arr(elements) if elements.len() == 1
            && matches!(&elements[0].value, JValue::Arr(pair) if pair.len() == 2 && s(&pair[1]) == "rust-T3"))
    }));
    let law = include_str!("fixtures/r2-structure-choice/laws.law")
        .replace(
            "selected(p:Design,t:Route)",
            "selected(p:Design,t:Route,x:State,y:State)",
        )
        .replace(
            "interfaces(p:Design,t:Route)",
            "interfaces(p:Design,t:Route,x:State,y:State)",
        )
        .replace(
            "if p.split!=p.reversed then set<Root>{t.to}",
            "if source(then(identity(x),identity(y)))=x and p.split then set<Root>{t.to}",
        );
    std::fs::write(dir.join("laws.law"), law).unwrap();
    let path_ask = format!(
        "{},x=@comparison/native-T3-before,y=@comparison/rust-T3-before)",
        asks[asks.len() - 2].strip_suffix(')').unwrap()
    );
    let at = args.len() - 3;
    args[at] = &path_ask;
    args[8] = "failed-path";
    let run = run_binary(&dir, &args);
    assert_eq!(run.code, 2, "{}{}", run.stdout, run.stderr);
    let result = result_json(&dir, &run);
    let layout = arr(get(&result, "answers"))
        .iter()
        .find(|a| s(get(a, "id")) == "layout")
        .unwrap();
    assert_eq!(s(get(layout, "status")), "refuted");
    let [counterexample] = arr(get(layout, "counterexamples")) else {
        panic!("the failed View comparison");
    };
    let nodes = arr(get(&result, "nodes"));
    let value = |reference: &JNode| {
        get(
            nodes
                .iter()
                .find(|node| s(get(node, "id")) == s(get(reference, "node")))
                .unwrap(),
            "value",
        )
    };
    let data = get(value(counterexample), "data");
    assert_eq!(s(&arr(value(get(data, "left")))[1]), "native-T3-before");
    assert_eq!(s(&arr(value(get(data, "right")))[1]), "rust-T3-before");
    let [reason] = arr(get(layout, "reasons")) else {
        panic!("one checked condition failure");
    };
    assert_eq!(s(get(get(reason, "location"), "input")), "law");

    let base_law = include_str!("fixtures/r2-structure-choice/laws.law")
        .replace(
            "selected(p:Design,t:Route)",
            "selected(p:Design,t:Route,x:State,y:State)",
        )
        .replace(
            "interfaces(p:Design,t:Route)",
            "interfaces(p:Design,t:Route,x:State,y:State)",
        );
    let selected = "if p.split!=p.reversed then set<Root>{t.to} else set<Root>{t.from}";
    let term = base_law.replace(
        selected,
        "if (fn(k:Z)=>forall b in list<Z>[k] . b=0)(x.quantity) then set<Root>{t.to} else set<Root>{t.from}",
    );
    std::fs::write(dir.join("laws.law"), term).unwrap();
    args[8] = "term-domain";
    let run = run_binary(&dir, &args);
    assert_eq!(run.code, 0, "{}{}", run.stdout, run.stderr);
    let result = result_json(&dir, &run);
    let layout = arr(get(&result, "answers"))
        .iter()
        .find(|a| s(get(a, "id")) == "layout")
        .unwrap();
    let quantifier = arr(get(get(layout, "scope"), "quantifiers"))
        .iter()
        .find(|q| s(get(q, "name")) == "b")
        .expect("evaluated Term body quantifier");
    let nodes = arr(get(&result, "nodes"));
    let resolve = |reference: &JNode| {
        nodes
            .iter()
            .find(|node| s(get(node, "id")) == s(get(reference, "node")))
            .unwrap()
    };
    let domain = resolve(get(quantifier, "domain"));
    let [member] = arr(get(get(domain, "value"), "elements")) else {
        panic!("actual singleton Term domain");
    };
    assert_eq!(s(get(resolve(member), "value")), "0");

    let unavailable = concat!(
        "        {\n          \"id\": \"rust-T3-before.quantity\",\n",
        "          \"subject\": \"rust-T3-before\",\n",
        "          \"field\": \"E12.State.quantity\",\n",
        "          \"value\": \"0\",\n          \"origin\": \"reduced-e12\"\n        },\n",
    );
    let original = include_str!("fixtures/r2-structure-choice/archmap.json");
    let missing = original.replacen(unavailable, "", 1);
    assert_ne!(original, missing);
    std::fs::write(dir.join("archmap.json"), missing).unwrap();
    let conditional = base_law.replace(
        selected,
        "if y.quantity=0 then (if source(then(identity(x),identity(y)))=x then set<Root>{t.to} else set<Root>{t.from}) else set<Root>{t.to}",
    );
    std::fs::write(dir.join("laws.law"), conditional).unwrap();
    args[8] = "unknown-branch";
    let run = run_binary(&dir, &args);
    assert_eq!(run.code, 2, "{}{}", run.stdout, run.stderr);
    let result = result_json(&dir, &run);
    let layout = arr(get(&result, "answers"))
        .iter()
        .find(|a| s(get(a, "id")) == "layout")
        .unwrap();
    assert_eq!(s(get(layout, "status")), "undetermined");
    let [reason] = arr(get(layout, "reasons")) else {
        panic!("the missing branch condition");
    };
    assert_eq!(s(get(reason, "code")), "missing_observation");
    let [slot] = arr(get(reason, "missing")) else {
        panic!("the actual missing slot");
    };
    assert_eq!(s(get(slot, "subject")), "rust-T3-before");
    assert_eq!(s(get(slot, "field")), "E12.State.quantity");

    let decisive = base_law.replace(
        selected,
        "if p.split then (if y.quantity=0 and false then set<Root>{t.to} else set<Root>{t.from}) else set<Root>{t.to}",
    );
    std::fs::write(dir.join("laws.law"), decisive).unwrap();
    let native_ask = path_ask.replace("rust-output1", "native-output1");
    args[at] = &native_ask;
    args[8] = "decisive-right";
    let run = run_binary(&dir, &args);
    let result = result_json(&dir, &run);
    let layout = arr(get(&result, "answers"))
        .iter()
        .find(|a| s(get(a, "id")) == "layout")
        .unwrap();
    assert_eq!(s(get(layout, "status")), "established", "{}", run.stdout);
    assert!(arr(get(layout, "reasons")).is_empty());
}

#[test]
fn a_projected_assembly_endpoint_preserves_the_same_evaluated_domains() {
    let dir = workdir("structure-choice-projected-endpoint");
    std::fs::write(
        dir.join("definitions.json"),
        include_bytes!("fixtures/r2-structure-choice/definitions.json"),
    )
    .unwrap();
    std::fs::write(
        dir.join("archmap.json"),
        include_bytes!("fixtures/r2-structure-choice/archmap.json"),
    )
    .unwrap();
    let law = include_str!("fixtures/r2-structure-choice/laws.law").replace(
        "if p.split!=p.reversed then",
        "if (forall b in list<Bool>[true] . b=b) and (fn(k:Bool)=>forall m in list<Bool>[k] . m=k)(true) and p.split!=p.reversed then",
    );
    std::fs::write(dir.join("laws.law"), law).unwrap();
    let asks = include_str!("fixtures/r2-structure-choice/queries.txt")
        .lines()
        .collect::<Vec<_>>();
    let mut args = vec![
        "run",
        "--atom-definition",
        "definitions.json",
        "--law",
        "laws.law",
        "--archmap",
        "archmap.json",
        "--out",
        "out",
    ];
    for ask in asks[..8].iter().copied().chain([
        asks[14],
        "legacyTarget=assemble(E12Compare.selected,on=@comparison/rust-output1,along=E12Compare.interfaces,p=@comparison/lookalike,t=@comparison/move-T3)",
        "legacy=assemble_map(E12Compare.routes,from=$native.assembly,to=$legacyTarget.assembly,t=@comparison/move-T3)",
        "projected=assemble_map(E12Compare.routes,from=$legacy.map.source_assembly,to=$layout1.assembly,t=@comparison/move-T3)",
        "direct=assemble_map(E12Compare.routes,from=$native.assembly,to=$layout1.assembly,t=@comparison/move-T3)",
    ]) {
        args.extend(["--ask", ask]);
    }
    let run = run_binary(&dir, &args);
    assert_eq!(run.code, 0, "{}{}", run.stdout, run.stderr);
    let result = result_json(&dir, &run);
    let answers = arr(get(&result, "answers"));
    let scope = |id| {
        let answer = answers
            .iter()
            .find(|answer| s(get(answer, "id")) == id)
            .unwrap();
        arr(get(get(answer, "scope"), "quantifiers"))
    };
    let projected = scope("projected");
    let direct = scope("direct");
    assert_eq!(projected.len(), 4);
    for name in ["b", "m"] {
        assert_eq!(
            projected
                .iter()
                .filter(|q| s(get(q, "name")) == name && has(q, "domain"))
                .count(),
            2
        );
    }
    assert_eq!(
        projected.iter().map(|q| &q.value).collect::<Vec<_>>(),
        direct.iter().map(|q| &q.value).collect::<Vec<_>>()
    );
}
