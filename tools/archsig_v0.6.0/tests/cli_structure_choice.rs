use crate::common::cli::*;
use archsig_common::json::{JNode, JValue};
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
    let [failure] = arr(get(answer("wrongIdentity"), "counterexamples")) else {
        panic!("design identity counterexample");
    };
    assert!(s(get(get(value(failure), "data"), "condition_detail")).contains("元root"));
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
        .replace("selected(p:Design)", "selected(p:Design,x:State,y:State)")
        .replace("interfaces(p:Design):Unit = unit", "interfaces(p:Design,x:State,y:State):List<(State,State)> = if p.split then list<(State,State)>[(x,y)] else list<(State,State)>[]");
    std::fs::write(dir.join("laws.law"), law).unwrap();
    let original = include_str!("fixtures/r2-structure-choice/queries.txt")
        .lines()
        .collect::<Vec<_>>();
    let mut asks = original[1..8]
        .iter()
        .map(|ask| (*ask).to_owned())
        .collect::<Vec<_>>();
    let endpoints = ",x=@comparison/native-T3-before,y=@comparison/rust-T3-before";
    for (id, selected) in [
        ("fixed0", ",design.p=$planApply0.object"),
        ("fixed1", ",design.p=$planApply1.object"),
    ] {
        asks.push(format!("{id}=assemble(E12Compare.selected,on=@comparison/rust-output1,along=E12Compare.interfaces,p=@comparison/plan{endpoints}{selected})"));
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
    assert_eq!(s(get(fixed0, "status")), "established");
    assert_eq!(s(get(fixed1, "status")), "refuted");
    assert_eq!(s(get(get(fixed1, "scope"), "domain")), "finite_model");
    assert!(arr(get(get(fixed1, "scope"), "quantifiers")).is_empty());
}
