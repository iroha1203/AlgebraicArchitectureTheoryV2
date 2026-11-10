use crate::common::cli::*;
use archsig_common::json::{JNode, JValue};
use std::collections::BTreeMap;

#[test]
fn migration_consumes_the_applied_state_and_preserves_only_the_selected_e12_operations() {
    let dir = workdir("repaired-migration");
    for (name, bytes) in [
        ("definitions.json", include_bytes!("fixtures/r2-repaired-migration/definitions.json").as_slice()),
        ("laws.law", include_bytes!("fixtures/r2-repaired-migration/laws.law").as_slice()),
        ("archmap.json", include_bytes!("fixtures/r2-repaired-migration/archmap.json").as_slice()),
    ] {
        std::fs::write(dir.join(name), bytes).unwrap();
    }
    let mut args = vec!["run", "--atom-definition", "definitions.json", "--law", "laws.law",
        "--archmap", "archmap.json", "--out", "out"];
    for ask in include_str!("fixtures/r2-repaired-migration/queries.txt").lines() {
        args.extend(["--ask", ask]);
    }
    let run = run_binary(&dir, &args);
    assert_eq!(run.code, 1, "{}{}", run.stdout, run.stderr);
    let result = result_json(&dir, &run);
    let answers = arr(get(&result, "answers"));
    let nodes = arr(get(&result, "nodes"));
    let answer = |id: &str| answers.iter().find(|a| s(get(a, "id")) == id).unwrap();
    let output = |id: &str, field: &str| get(get(answer(id), "outputs"), field);
    let node = |reference: &JNode| nodes.iter()
        .find(|node| s(get(node, "id")) == s(get(reference, "node"))).unwrap();
    let value = |reference: &JNode| get(node(reference), "value");
    let expected = archsig_common::json::parse(include_bytes!("fixtures/r2-repaired-migration/expected.json")).unwrap();
    let JValue::Obj(expected) = &expected.value else { panic!("expected answers") };
    let expected = expected.iter().map(|(id, status)| (id.as_str(), s(status))).collect::<BTreeMap<_, _>>();
    let actual = answers.iter().map(|a| (s(get(a, "id")), s(get(a, "status")))).collect::<BTreeMap<_, _>>();
    assert_eq!(actual.len(), answers.len());
    assert_eq!(actual, expected);

    let selection = value(output("fixed", "selection"));
    assert_eq!(get(selection, "parameters").value, output("chosen", "assignment").value);
    assert_eq!(get(selection, "solutions").value, output("solveIt", "solutions").value);
    assert_eq!(output("after", "environment").value, output("fixed", "object").value);
    for assembly in ["native", "nativeWide"] {
        let assembly = value(output(assembly, "assembly"));
        let applied = arr(get(assembly, "inclusions")).iter()
            .find(|row| has(row, "applied")).unwrap();
        assert_eq!(get(applied, "applied").value, output("fixed", "object").value);
    }

    let migration = value(output("migrate", "map"));
    assert_eq!(get(migration, "source_assembly").value, output("native", "assembly").value);
    assert_eq!(get(migration, "target_assembly").value, output("rust", "assembly").value);
    assert_eq!(get(migration, "target").value, output("target", "environment").value);
    let [generator] = arr(get(migration, "generators")) else { panic!("only selected consume") };
    assert_eq!(s(get(get(node(get(generator, "proposition")), "judgment"), "status")), "established");
    for (side, id) in [("source", "native-T3-consume"), ("target", "rust-T3-consume")] {
        let subject = get(get(value(get(generator, side)), "name"), "subject");
        assert_eq!(s(&arr(value(subject))[1]), id);
    }
    let wide = answer("extended");
    assert!(!has(get(wide, "outputs"), "map"));
    let [counterexample] = arr(get(wide, "counterexamples")) else { panic!("raw cancel refutation") };
    let facts = arr(get(get(value(counterexample), "data"), "facts"));
    for atom in ["native-cancel-raw.to", "rust-cancel-raw.to"] {
        assert!(facts.iter().any(|fact| has(fact, "atom") && s(get(fact, "atom")) == atom));
    }
    for (answer, building, code) in [("nativeCancel", true, "10"), ("rustCancel", false, "65")] {
        let [is_building, status] = arr(value(output(answer, "value"))) else { panic!("cancel result") };
        assert_eq!(is_building.value, JValue::Bool(building));
        assert_eq!(s(status), code);
    }
}
