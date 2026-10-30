//! 有限な欠測値の全補完と、具体的な状態値の確定を区別する。
#[allow(dead_code)]
#[path = "common/cli.rs"]
mod cli;
use archsig::json::JNode;
use cli::*;
fn setup(body: &str) -> std::path::PathBuf {
    let dir = workdir(&format!("finite-value-completion-{body}"));
    let d = include_bytes!("fixtures/engine.atoms.json");
    let checked = archsig::definition::check_definitions(&[("definition0", d)]).unwrap();
    let digest = &checked.vocabularies()["Engine"].digest;
    let a = format!(
        r#"{{"format":"archsig.archmap/2","semantics":"archsig/0.6.0","vocabularies":[{{"namespace":"Engine","version":"1","digest":"{digest}"}}],"sources":[],"origins":[{{"id":"model","mode":"specification","method":"有限二値の欠測。","locations":[],"note":"元Assignmentは空積。"}}],"snapshots":[{{"id":"engine","origin":"model","subjects":[{{"id":"add","type":"Engine.Compiler","origin":"model"}}],"atoms":[{{"id":"source","subject":"add","field":"Engine.Compiler.source","value":{{"tag":"Lit","args":["1"]}},"origin":"model"}}]}}]}}"#
    );
    let law = format!(
        "law \"archsig.law/2\" semantics \"archsig/0.6.0\";reading Engine{{use vocabulary Engine version \"1\" digest \"{digest}\";law optional valid(c:Compiler):{body};change keep(c:Compiler)=c with{{operator=c.operator}};view op(c:Compiler):Operator=c.operator;}}"
    );
    std::fs::write(dir.join("d.json"), d).unwrap();
    std::fs::write(dir.join("a.json"), a).unwrap();
    std::fs::write(dir.join("l.law"), law).unwrap();
    dir
}
fn node<'a>(j: &'a JNode, r: &JNode) -> &'a JNode {
    arr(get(j, "nodes"))
        .iter()
        .find(|n| s(get(n, "id")) == s(get(r, "node")))
        .unwrap()
}
#[test]
fn finite_missing_data_keeps_verified_existence_and_reports_unavailable_states() {
    let dir = setup("true");
    let daily = run(
        &dir,
        &[
            "run",
            "--atom-definition",
            "d.json",
            "--law",
            "l.law",
            "--archmap",
            "a.json",
            "--ask",
            "s=solve(Engine.valid,on=@engine/add,using=Engine.keep,c=@engine/add)",
        ],
    );
    assert_eq!(daily.code, 2, "{}", daily.stdout);
    let daily_answer = &arr(get(&daily.receipt, "answers"))[0];
    assert_eq!(s(get(daily_answer, "existence")), "established");
    assert_eq!(std::fs::read_dir(&dir).unwrap().count(), 3);
    let result = run(
        &dir,
        &[
            "run",
            "--atom-definition",
            "d.json",
            "--law",
            "l.law",
            "--archmap",
            "a.json",
            "--ask",
            "s=solve(Engine.valid,on=@engine/add,using=Engine.keep,c=@engine/add)",
            "--ask",
            "n=needed($s)",
            "--out",
            "out",
        ],
    );
    assert_eq!(result.code, 2, "{}", result.stdout);
    let saved = result_json(&dir, &result);
    assert_eq!(s(get(&saved, "status")), "partial");
    let answer = &arr(get(&saved, "answers"))[0];
    assert_eq!(s(get(answer, "status")), "undetermined");
    let existence = node(&saved, get(get(answer, "outputs"), "proposition"));
    assert_eq!(s(get(get(existence, "judgment"), "status")), "established");
    assert!(!has(get(answer, "outputs"), "solutions"));
    let certificates: Vec<_> = arr(get(&saved, "nodes"))
        .iter()
        .filter(|n| {
            has(n, "value")
                && has(get(n, "value"), "kind")
                && s(get(get(n, "value"), "kind")) == "completion_fibers"
        })
        .collect();
    assert_eq!(certificates.len(), 1);
    let data = get(get(certificates[0], "value"), "data");
    let fields = arr(get(data, "fields"));
    assert_eq!(fields.len(), 1);
    assert_eq!(s(get(&fields[0], "field")), "Engine.Compiler.operator");
    let cases = arr(get(data, "cases"));
    assert_eq!(cases.len(), 2);
    let mut tags = Vec::new();
    for case in cases {
        let values = arr(get(case, "values"));
        assert_eq!(values.len(), 1);
        tags.push(s(get(get(node(&saved, &values[0]), "value"), "tag")).to_owned());
        let assignments = arr(get(case, "assignments"));
        assert_eq!(assignments.len(), 1);
        let entries = arr(&assignments[0]);
        assert_eq!(entries.len(), 1);
        assert!(arr(get(&entries[0], "parameters")).is_empty());
    }
    tags.sort();
    assert_eq!(tags, ["AddOp", "SubtractOp"]);
    let needed = &arr(get(&saved, "answers"))[1];
    let plan = node(&saved, get(get(needed, "outputs"), "plan"));
    let requirements = arr(get(get(plan, "value"), "requirements"));
    assert_eq!(requirements.len(), 1);
    assert_eq!(
        s(get(get(&requirements[0], "field"), "field")),
        "Engine.Compiler.operator"
    );
    assert!(
        arr(get(&saved, "issues"))
            .iter()
            .all(|i| s(get(i, "code")) != "internal")
    );
}

fn completion_counts(saved: &JNode) -> Vec<usize> {
    let certificate = arr(get(saved, "nodes"))
        .iter()
        .find(|n| {
            has(n, "value")
                && has(get(n, "value"), "kind")
                && s(get(get(n, "value"), "kind")) == "completion_fibers"
        })
        .unwrap();
    let mut counts: Vec<_> = arr(get(get(get(certificate, "value"), "data"), "cases"))
        .iter()
        .map(|case| arr(get(case, "assignments")).len())
        .collect();
    counts.sort();
    counts
}
#[test]
fn finite_missing_values_keep_empty_and_conditional_solution_fibers_distinct() {
    for (body, expected, code, counts) in [
        ("false", "refuted", 1, vec![0, 0]),
        (
            "match c.operator {AddOp => true; SubtractOp => false;}",
            "undetermined",
            2,
            vec![0, 1],
        ),
    ] {
        let dir = setup(body);
        let result = run(
            &dir,
            &[
                "run",
                "--atom-definition",
                "d.json",
                "--law",
                "l.law",
                "--archmap",
                "a.json",
                "--ask",
                "s=solve(Engine.valid,on=@engine/add,using=Engine.keep,c=@engine/add)",
                "--ask",
                "n=needed($s)",
                "--out",
                "out",
            ],
        );
        assert_eq!(result.code, code, "{}", result.stdout);
        let saved = result_json(&dir, &result);
        let answer = &arr(get(&saved, "answers"))[0];
        assert_eq!(s(get(answer, "status")), expected);
        let proposition = node(&saved, get(get(answer, "outputs"), "proposition"));
        assert_eq!(s(get(get(proposition, "judgment"), "status")), expected);
        assert_eq!(completion_counts(&saved), counts);
        let needed = &arr(get(&saved, "answers"))[1];
        let plan = node(&saved, get(get(needed, "outputs"), "plan"));
        assert_eq!(
            arr(get(get(plan, "value"), "requirements")).len(),
            usize::from(code == 2)
        );
        assert!(
            arr(get(&saved, "issues"))
                .iter()
                .all(|i| s(get(i, "code")) != "internal")
        );
    }
}
#[test]
fn finite_missing_law_values_use_the_same_completion_proof() {
    let dir = setup("match c.operator {AddOp => true; SubtractOp => false;}");
    let path = dir.join("l.law");
    let law = std::fs::read_to_string(&path)
        .unwrap()
        .replace("operator=c.operator", "source=Lit(1)");
    std::fs::write(path, law).unwrap();
    let result = run(
        &dir,
        &[
            "run",
            "--atom-definition",
            "d.json",
            "--law",
            "l.law",
            "--archmap",
            "a.json",
            "--ask",
            "s=solve(Engine.valid,on=@engine/add,using=Engine.keep,c=@engine/add)",
            "--out",
            "out",
        ],
    );
    assert_eq!(result.code, 2, "{}", result.stdout);
    let saved = result_json(&dir, &result);
    assert_eq!(completion_counts(&saved), vec![0, 1]);
    let answer = &arr(get(&saved, "answers"))[0];
    assert_eq!(s(get(answer, "status")), "undetermined");
    assert!(arr(get(answer, "reasons")).iter().any(|r| {
        s(get(r, "code")) == "missing_observation"
            && arr(get(r, "missing"))
                .iter()
                .any(|f| s(get(f, "field")) == "Engine.Compiler.operator")
    }));
}
#[test]
fn finite_missing_state_does_not_create_a_unique_repair_object() {
    let dir = setup("true");
    let result = run(
        &dir,
        &[
            "run",
            "--atom-definition",
            "d.json",
            "--law",
            "l.law",
            "--archmap",
            "a.json",
            "--ask",
            "r=repair(Engine.valid,on=@engine/add,using=Engine.keep,c=@engine/add)",
            "--ask",
            "later=evaluate(Engine.op,on=$r.object,c=@engine/add)",
            "--out",
            "out",
        ],
    );
    assert_eq!(result.code, 2, "{}", result.stdout);
    let saved = result_json(&dir, &result);
    assert_eq!(completion_counts(&saved), vec![1, 1]);
    let answers = arr(get(&saved, "answers"));
    assert_eq!(s(get(&answers[0], "status")), "undetermined");
    let outputs = get(&answers[0], "outputs");
    assert!(!has(outputs, "repair") && !has(outputs, "object"));
    let existence = node(&saved, get(outputs, "existence"));
    assert_eq!(s(get(get(existence, "judgment"), "status")), "established");
    assert!(
        arr(get(&answers[1], "reasons"))
            .iter()
            .any(|r| s(get(r, "code")) == "dependency_blocked")
    );
    assert!(
        arr(get(&saved, "issues"))
            .iter()
            .all(|i| s(get(i, "code")) != "internal")
    );
}
#[test]
fn finite_completion_reuse_rejects_a_changed_case_and_recomputes() {
    let dir = setup("true");
    let execute = |out: &str, reuse: bool| {
        let mut args = vec![
            "run",
            "--atom-definition",
            "d.json",
            "--law",
            "l.law",
            "--archmap",
            "a.json",
            "--ask",
            "s=solve(Engine.valid,on=@engine/add,using=Engine.keep,c=@engine/add)",
            "--out",
            out,
        ];
        if reuse {
            args.extend(["--reuse", "first"]);
        }
        run(&dir, &args)
    };
    let first = execute("first", false);
    assert_eq!(first.code, 2, "{}", first.stdout);
    let original = result_json(&dir, &first);
    let same = execute("same", true);
    assert_eq!(same.code, 2, "{}", same.stdout);
    let saved = result_json(&dir, &same);
    assert!(warnings(&saved).is_empty());
    let path = dir.join("first/result.json");
    let bytes = std::fs::read_to_string(&path).unwrap();
    assert!(bytes.contains("\"tag\":\"AddOp\""));
    std::fs::write(
        path,
        bytes.replacen("\"tag\":\"AddOp\"", "\"tag\":\"SubtractOp\"", 1),
    )
    .unwrap();
    let changed = execute("changed", true);
    assert_eq!(changed.code, 2, "{}", changed.stdout);
    let checked = result_json(&dir, &changed);
    assert!(!warnings(&checked).is_empty());
    for key in ["answers", "nodes"] {
        assert_eq!(get(&original, key).value, get(&checked, key).value);
    }
}

#[test]
fn finite_completion_discovers_selected_reads_and_ignores_unselected_missing_slots() {
    let dir = setup("true");
    let old = std::fs::read_to_string(dir.join("d.json")).unwrap();
    let old_checked =
        archsig::definition::check_definitions(&[("definition0", old.as_bytes())]).unwrap();
    let old_digest = &old_checked.vocabularies()["Engine"].digest;
    let definition = old.replacen(
        "\"fields\": [",
        "\"fields\": [{\"name\":\"extra\",\"type\":\"Bool\",\"meaning\":\"分岐値。\"},",
        1,
    );
    assert_ne!(old, definition);
    let checked =
        archsig::definition::check_definitions(&[("definition0", definition.as_bytes())]).unwrap();
    let digest = &checked.vocabularies()["Engine"].digest;
    let map = std::fs::read_to_string(dir.join("a.json"))
        .unwrap()
        .replace(old_digest, digest);
    let law=std::fs::read_to_string(dir.join("l.law")).unwrap().replace(old_digest,digest)
        .replace("c with{operator=c.operator}", "if match c.operator {AddOp => true; SubtractOp => false;} then c with{operator=if c.extra then AddOp else SubtractOp} else c with{operator=SubtractOp}");
    std::fs::write(dir.join("d.json"), definition).unwrap();
    std::fs::write(dir.join("l.law"), law).unwrap();
    for known in [false, true] {
        let map = if known {
            map.replace("\"atoms\":[", "\"atoms\":[{\"id\":\"operator\",\"subject\":\"add\",\"field\":\"Engine.Compiler.operator\",\"value\":{\"tag\":\"SubtractOp\",\"args\":[]},\"origin\":\"model\"},")
        } else {
            map.clone()
        };
        std::fs::write(dir.join("a.json"), map).unwrap();
        let result = run(
            &dir,
            &[
                "run",
                "--atom-definition",
                "d.json",
                "--law",
                "l.law",
                "--archmap",
                "a.json",
                "--ask",
                "s=solve(Engine.valid,on=@engine/add,using=Engine.keep,c=@engine/add)",
                "--ask",
                "n=needed($s)",
                "--out",
                if known { "known" } else { "missing" },
            ],
        );
        assert_eq!(result.code, if known { 0 } else { 2 }, "{}", result.stdout);
        let saved = result_json(&dir, &result);
        if !known {
            assert_eq!(completion_counts(&saved), vec![1, 1, 1, 1]);
        }
        let needed = &arr(get(&saved, "answers"))[1];
        let plan = node(&saved, get(get(needed, "outputs"), "plan"));
        assert_eq!(
            arr(get(get(plan, "value"), "requirements")).len(),
            if known { 0 } else { 2 }
        );
    }
}

#[test]
fn identical_completed_updates_deliver_native_repair_without_observing_missing_input() {
    let dir = setup("true");
    let law = std::fs::read_to_string(dir.join("l.law")).unwrap().replace(
        "operator=c.operator",
        "operator=match c.operator {AddOp => AddOp; SubtractOp => AddOp;}",
    );
    std::fs::write(dir.join("l.law"), law).unwrap();
    let result = run(
        &dir,
        &[
            "run",
            "--atom-definition",
            "d.json",
            "--law",
            "l.law",
            "--archmap",
            "a.json",
            "--ask",
            "r=repair(Engine.valid,on=@engine/add,using=Engine.keep,c=@engine/add)",
            "--ask",
            "v=evaluate(Engine.op,on=$r.object,c=@engine/add)",
            "--out",
            "out",
        ],
    );
    assert_eq!(result.code, 0, "{} {}", result.stdout, result.stderr);
    let saved = result_json(&dir, &result);
    let answers = arr(get(&saved, "answers"));
    let repair = &answers[0];
    assert_eq!(s(get(repair, "status")), "established");
    assert!(has(get(repair, "outputs"), "object"));
    let value = node(&saved, get(get(&answers[1], "outputs"), "value"));
    assert_eq!(s(get(get(value, "value"), "tag")), "AddOp");
    // The original input is still missing the operator; only the change supplies its override.
    let original = std::fs::read_to_string(dir.join("a.json")).unwrap();
    assert!(!original.contains("Engine.Compiler.operator"));
}
