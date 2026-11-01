//! 元changeのparameter全域を公開solveで解く。
use crate::common::cli;
use crate::common::object_view_compatibility_data as fixture;
fn input() -> std::sync::Arc<archsig_input::input::CheckedInputs> {
    let definitions = fixture::D.replace(
        r#"{"name":"quantity","type":"Z","meaning":"数量。"}"#,
        r#"{"name":"flag","type":"Bool","meaning":"条件。"}"#,
    );
    let checked =
        definition::check_definitions(&[("definition0", definitions.as_bytes())]).unwrap();
    let digest = &checked.vocabularies()["Pattern"].digest;
    let map=r#"{"format":"archsig.archmap/2","semantics":"archsig/0.6.0","vocabularies":[{"namespace":"Pattern","version":"1","digest":"@DIGEST@"}],"sources":[],"origins":[{"id":"model","mode":"specification","method":"有限変更の試験。","locations":[],"note":"公開有限変更の正常系。"}],"snapshots":[{"id":"v","origin":"model","subjects":[{"id":"root","type":"Pattern.Root","origin":"model"},{"id":"p","type":"Pattern.Part","origin":"model"},{"id":"q","type":"Pattern.Part","origin":"model"}],"atoms":[{"id":"op","subject":"p","field":"Pattern.Part.owner","value":["v","root"],"origin":"model"},{"id":"oq","subject":"q","field":"Pattern.Part.owner","value":["v","root"],"origin":"model"},{"id":"fp","subject":"p","field":"Pattern.Part.flag","value":true,"origin":"model"},{"id":"fq","subject":"q","field":"Pattern.Part.flag","value":false,"origin":"model"}]}]}"#.replace("@DIGEST@",digest);
    let law = format!(
        "law \"archsig.law/2\" semantics \"archsig/0.6.0\";reading Selected{{use vocabulary Pattern version \"1\" digest \"{digest}\";change choose(c:Part,b:Bool)=c with {{flag=b}};law required valid(c:Part):c.flag;view flag(c:Part):Bool=c.flag;}}"
    );
    let sources = archsig_input::input::InputSources::from_bytes(
        vec![definitions.into_bytes()],
        law.into_bytes(),
        map.into_bytes(),
    );
    std::sync::Arc::new(
        archsig_input::input::check_inputs(sources, &archsig_common::control::Control::unlimited())
            .unwrap(),
    )
}
use archsig_computation::observed;
pub use archsig_input::definition;
use cli::*;

#[test]
fn finite_solve_returns_original_assignments_for_all_local_subjects() {
    let input = input();
    let dir = workdir("finite-change");
    for (name, data) in [
        ("d.json", input.sources().definitions()[0].bytes()),
        ("a.json", input.sources().archmap().bytes()),
        ("l.law", input.sources().law().bytes()),
    ] {
        std::fs::write(dir.join(name), data).unwrap();
    }
    let run = run(
        &dir,
        &[
            "run",
            "--atom-definition",
            "d.json",
            "--archmap",
            "a.json",
            "--law",
            "l.law",
            "--out",
            "out",
            "--ask",
            "s=solve(Selected.valid,on=@v/root,using=Selected.choose)",
        ],
    );
    assert!(has(&run.receipt, "result"), "{}", run.stdout);
    let result = result_json(&dir, &run);
    assert_eq!(run.code, 0, "{}\n{:?}", run.stdout, result);
    let answer = &arr(get(&result, "answers"))[0];
    assert_eq!(s(get(answer, "status")), "established");
    let reference = get(get(answer, "outputs"), "solutions");
    let node = arr(get(&result, "nodes"))
        .iter()
        .find(|n| s(get(n, "id")) == s(get(reference, "node")))
        .unwrap();
    let representation = get(get(node, "value"), "representation");
    assert_eq!(s(get(representation, "kind")), "finite");
    assert_eq!(arr(get(representation, "values")).len(), 1);
    for node in arr(get(&result, "nodes")) {
        assert!(!has(node, "rule"));
        assert!(!has(node, "arguments"));
    }
}

#[test]
fn unique_repair_is_consumed_by_evaluate_and_check() {
    let input = input();
    let dir = workdir("finite-repair");
    for (name, data) in [
        ("d.json", input.sources().definitions()[0].bytes()),
        ("a.json", input.sources().archmap().bytes()),
        ("l.law", input.sources().law().bytes()),
    ] {
        std::fs::write(dir.join(name), data).unwrap();
    }
    let run = run(
        &dir,
        &[
            "run",
            "--atom-definition",
            "d.json",
            "--archmap",
            "a.json",
            "--law",
            "l.law",
            "--out",
            "out",
            "--ask",
            "r=repair(Selected.valid,on=@v/root,using=Selected.choose)",
            "--ask",
            "e=evaluate(Selected.flag,on=$r.object,c=@v/q)",
            "--ask",
            "c=check(Selected.valid,on=$r.object)",
        ],
    );
    assert!(has(&run.receipt, "result"), "{}", run.stdout);
    let result = result_json(&dir, &run);
    assert_eq!(run.code, 0, "{}\n{:?}", run.stdout, result);
    for answer in arr(get(&result, "answers")) {
        assert_eq!(s(get(answer, "status")), "established");
    }
}

fn case(
    name: &str,
    effect: &str,
    asks: &[&str],
) -> (std::path::PathBuf, Run, archsig_common::json::JNode) {
    let input = input();
    let dir = workdir(name);
    let law = String::from_utf8(input.sources().law().bytes().to_vec())
        .unwrap()
        .replace("flag=b", &format!("flag={effect}"))
        .replace(
            "view flag",
            "change keep(c:Part)=c with {flag=c.flag};view flag",
        );
    for (name, data) in [
        ("d.json", input.sources().definitions()[0].bytes()),
        ("a.json", input.sources().archmap().bytes()),
        ("l.law", law.as_bytes()),
    ] {
        std::fs::write(dir.join(name), data).unwrap();
    }
    let mut args = vec![
        "run",
        "--atom-definition",
        "d.json",
        "--archmap",
        "a.json",
        "--law",
        "l.law",
        "--out",
        "out",
    ];
    for ask in asks {
        args.extend(["--ask", ask]);
    }
    let run = run(&dir, &args);
    assert!(has(&run.receipt, "result"), "{}", run.stdout);
    let result = result_json(&dir, &run);
    (dir, run, result)
}
fn answer<'a>(
    result: &'a archsig_common::json::JNode,
    id: &str,
) -> &'a archsig_common::json::JNode {
    arr(get(result, "answers"))
        .iter()
        .find(|a| s(get(a, "id")) == id)
        .unwrap()
}
fn node<'a>(
    result: &'a archsig_common::json::JNode,
    r: &archsig_common::json::JNode,
) -> &'a archsig_common::json::JNode {
    arr(get(result, "nodes"))
        .iter()
        .find(|n| s(get(n, "id")) == s(get(r, "node")))
        .unwrap()
}
#[test]
fn empty_and_nonunique_repairs_keep_existence_separate_and_do_not_choose_an_assignment() {
    for (effect, existence) in [("false", "refuted"), ("true", "established")] {
        let (_dir, run, result) = case(
            &format!("finite-repair-{effect}"),
            effect,
            &["r=repair(Selected.valid,on=@v/root,using=Selected.choose)"],
        );
        assert_eq!(run.code, 1, "{}", run.stdout);
        let a = answer(&result, "r");
        assert_eq!(s(get(a, "status")), "refuted");
        let outputs = get(a, "outputs");
        assert!(!has(outputs, "object"));
        assert!(!has(outputs, "repair"));
        assert_eq!(
            s(get(
                get(node(&result, get(outputs, "existence")), "judgment"),
                "status"
            )),
            existence
        );
        let representation = get(
            get(node(&result, get(outputs, "solutions")), "value"),
            "representation",
        );
        if effect == "true" {
            assert_eq!(arr(get(representation, "values")).len(), 4);
            assert!(arr(get(&result,"nodes")).iter().filter(|n|matches!(&get(n,"type").value,archsig_common::json::JValue::Str(t) if t=="Assignment")).count()>=2);
        } else {
            assert_eq!(s(get(representation, "kind")), "empty");
        }
    }
}
#[test]
fn repeated_repair_reads_previous_overrides_and_leaves_original_observations_fixed() {
    let (_dir, run, result) = case(
        "finite-repair-chain",
        "b",
        &[
            "before=evaluate(Selected.flag,c=@v/q)",
            "r=repair(Selected.valid,on=@v/root,using=Selected.choose)",
            "again=repair(Selected.valid,on=$r.object,using=Selected.keep)",
            "e=evaluate(Selected.flag,on=$again.object,c=@v/q)",
            "c=check(Selected.valid,on=$again.object)",
            "after=evaluate(Selected.flag,c=@v/q)",
        ],
    );
    assert_eq!(run.code, 0, "{}", run.stdout);
    for id in ["before", "after", "e"] {
        let v = get(
            node(&result, get(get(answer(&result, id), "outputs"), "value")),
            "value",
        );
        assert_eq!(v.value, archsig_common::json::JValue::Bool(id == "e"));
    }
    for id in ["r", "again", "c"] {
        assert_eq!(s(get(answer(&result, id), "status")), "established");
    }
}
#[test]
fn public_build_object_and_candidate_base_projection_connect_to_solve() {
    let (_dir, run, result) = case(
        "finite-build-solve",
        "b",
        &[
            "b=build(Selected,on=@v/root)",
            "s=solve(Selected.valid,on=$b.object,using=Selected.choose)",
            "r=repair(Selected.valid,on=$s.domain.base,using=Selected.choose)",
            "e=evaluate(Selected.flag,on=$r.object,c=@v/q)",
        ],
    );
    assert_eq!(run.code, 0, "{}", run.stdout);
    for id in ["b", "s", "r", "e"] {
        assert_eq!(s(get(answer(&result, id), "status")), "established");
    }
}

#[test]
fn explicit_law_binding_keeps_unconstrained_change_parameters_in_the_solution_set() {
    let (_dir, run, result) = case(
        "finite-bound-law",
        "b",
        &["s=solve(Selected.valid,on=@v/root,using=Selected.choose,c=@v/p)"],
    );
    assert_eq!(run.code, 0, "{}", run.stdout);
    let outputs = get(answer(&result, "s"), "outputs");
    let domain = get(node(&result, get(outputs, "domain")), "value");
    assert_eq!(arr(get(domain, "bindings")).len(), 1);
    assert_eq!(s(get(&arr(get(domain, "bindings"))[0], "name")), "c");
    let solutions = get(node(&result, get(outputs, "solutions")), "value");
    assert_eq!(
        arr(get(get(solutions, "representation"), "values")).len(),
        2
    );
}
#[test]
fn saved_finite_repair_is_rechecked_with_its_followup_request() {
    let asks = [
        "r=repair(Selected.valid,on=@v/root,using=Selected.choose)",
        "e=evaluate(Selected.flag,on=$r.object,c=@v/q)",
    ];
    let (dir, first, original) = case("finite-repair-reuse", "b", &asks);
    assert_eq!(first.code, 0, "{}", first.stdout);
    let mut args = vec![
        "run",
        "--atom-definition",
        "d.json",
        "--archmap",
        "a.json",
        "--law",
        "l.law",
        "--out",
        "out2",
        "--reuse",
        "out",
    ];
    for ask in &asks {
        args.extend(["--ask", ask]);
    }
    let repeated = run(&dir, &args);
    assert_eq!(repeated.code, 0, "{}", repeated.stdout);
    let result = result_json(&dir, &repeated);
    assert!(!has(&result, "reuse"));
    for field in ["answers", "nodes"] {
        assert_eq!(get(&result, field).value, get(&original, field).value);
    }
}

#[test]
fn nonunique_repair_blocks_only_consumption_of_its_uncreated_object() {
    let (_dir, run, result) = case(
        "finite-repair-blocked",
        "true",
        &[
            "r=repair(Selected.valid,on=@v/root,using=Selected.choose)",
            "e=evaluate(Selected.flag,on=$r.object,c=@v/q)",
        ],
    );
    assert_eq!(run.code, 2, "{}", run.stdout);
    assert_eq!(s(get(answer(&result, "r"), "status")), "refuted");
    assert_eq!(s(get(answer(&result, "e"), "status")), "undetermined");
    assert!(
        arr(get(answer(&result, "e"), "reasons"))
            .iter()
            .any(|r| s(get(r, "code")) == "dependency_blocked")
    );
}

#[test]
fn change_dependency_cycles_are_rejected_before_output_type_resolution() {
    let input = input();
    let dir = workdir("change-cycles");
    for (name, data) in [
        ("d.json", input.sources().definitions()[0].bytes()),
        ("a.json", input.sources().archmap().bytes()),
        ("l.law", input.sources().law().bytes()),
    ] {
        std::fs::write(dir.join(name), data).unwrap();
    }
    for asks in [
        vec!["s=solve(Selected.valid,on=$s.domain.base,using=Selected.choose)"],
        vec!["r=repair(Selected.valid,on=$r.object,using=Selected.choose)"],
        vec![
            "s=solve(Selected.valid,on=$r.object,using=Selected.choose)",
            "r=repair(Selected.valid,on=$s.domain.base,using=Selected.choose)",
        ],
    ] {
        let mut args = vec![
            "run",
            "--atom-definition",
            "d.json",
            "--archmap",
            "a.json",
            "--law",
            "l.law",
            "--out",
            "out",
        ];
        for ask in asks {
            args.extend(["--ask", ask]);
        }
        let result = run(&dir, &args);
        assert_eq!(result.code, 64, "{}", result.stdout);
        assert!(result.stdout.contains("cycle"), "{}", result.stdout);
    }
}

#[test]
fn finite_owner_solution_and_unimplemented_change_have_distinct_outcomes() {
    let input = input();
    for missing in [false, true] {
        let law = String::from_utf8(input.sources().law().bytes().to_vec()).unwrap();
        let map = String::from_utf8(input.sources().archmap().bytes().to_vec()).unwrap();
        let law = if missing {
            law
        } else {
            law.replace("b:Bool)=c with {flag=b}", "b:Z)=c with {flag=true}")
        };
        let map = if missing {
            map.replace(r#"{"id":"oq","subject":"q","field":"Pattern.Part.owner","value":["v","root"],"origin":"model"},"#,"").replace(r#""subjects":["#, r#""subjects":[{"id":"other","type":"Pattern.Root","origin":"model"},"#)
        } else {
            map
        };
        let sources = archsig_input::input::InputSources::from_bytes(
            vec![input.sources().definitions()[0].bytes().to_vec()],
            law.into_bytes(),
            map.into_bytes(),
        );
        let control = archsig_common::control::Control::unlimited();
        let prepared = observed::prepare_observed(
            sources,
            &["s=solve(Selected.valid,on=@v/root,using=Selected.choose)"],
            &control,
        )
        .unwrap();
        let evaluated = observed::evaluate_observed(prepared, &control);
        if missing {
            let evaluated = evaluated.unwrap();
            assert_eq!(evaluated.status(), "partial");
            let j = archsig_common::json::parse(evaluated.wire().canonical().as_bytes()).unwrap();
            let a = &arr(get(&j, "answers"))[0];
            assert_eq!(s(get(a, "status")), "undetermined");
            let existence = node(&j, get(get(a, "outputs"), "proposition"));
            assert_eq!(s(get(get(existence, "judgment"), "status")), "established");
            assert!(format!("{:?}", get(a, "reasons")).contains("missing_observation"));
            assert!(!format!("{:?}", get(&j, "issues")).contains("internal"));
            continue;
        }
        let failure = evaluated.unwrap_err();
        let observed::EvaluationFailure::NotImplemented {
            declaration,
            partial,
            ..
        } = failure
        else {
            panic!("未実装の分類を保持する");
        };
        assert_eq!(declaration, "Selected.valid");
        assert_eq!(partial.status(), "error");
    }
}

#[test]
fn unused_let_cannot_erase_an_invalid_path_condition() {
    let input = input();
    let definitions=String::from_utf8(input.sources().definitions()[0].bytes().to_vec()).unwrap().replace(r#""fields":[{"name":"flag","type":"Bool","meaning":"条件。"}]"#,r#""fields":[{"name":"flag","type":"Bool","meaning":"条件。"},{"name":"link","type":["Ref","Pattern.Part"],"meaning":"接続。"}]"#);
    let defs = definition::check_definitions(&[("definition0", definitions.as_bytes())]).unwrap();
    let old = &input.definitions().vocabularies()["Pattern"].digest;
    let new = &defs.vocabularies()["Pattern"].digest;
    assert_ne!(old, new);
    let map=String::from_utf8(input.sources().archmap().bytes().to_vec()).unwrap().replace(old,new).replace(r#""atoms":["#,r#""atoms":[{"id":"lp","subject":"p","field":"Pattern.Part.link","value":["v","q"],"origin":"model"},{"id":"lq","subject":"q","field":"Pattern.Part.link","value":["v","p"],"origin":"model"},"#);
    for (case, body, code, count) in [
        (
            "invalid",
            "change choose(c:Part)=let ignored=then(identity(c),identity(c.link)) in c with {flag=true};",
            1,
            0,
        ),
        (
            "mixed",
            "change choose(c:Part,b:Bool)=let ignored=if b then identity(c) else then(identity(c),identity(c.link)) in c with {flag=true};",
            0,
            1,
        ),
    ] {
        let law = String::from_utf8(input.sources().law().bytes().to_vec())
            .unwrap()
            .replace(old, new)
            .replace("change choose(c:Part,b:Bool)=c with {flag=b};", body);
        let dir = workdir(&format!("change-invalid-let-{case}"));
        for (name, data) in [("d.json", &definitions), ("a.json", &map), ("l.law", &law)] {
            std::fs::write(dir.join(name), data).unwrap();
        }
        let result = run(
            &dir,
            &[
                "run",
                "--atom-definition",
                "d.json",
                "--archmap",
                "a.json",
                "--law",
                "l.law",
                "--out",
                "out",
                "--ask",
                "r=repair(Selected.valid,on=@v/root,using=Selected.choose)",
            ],
        );
        assert_eq!(result.code, code, "{}", result.stdout);
        let saved = result_json(&dir, &result);
        let answer = &arr(get(&saved, "answers"))[0];
        assert_eq!(
            s(get(answer, "status")),
            if code == 0 { "established" } else { "refuted" }
        );
        let outputs = get(answer, "outputs");
        assert_eq!(has(outputs, "object"), code == 0);
        let nodes = arr(get(&saved, "nodes"));
        let domain = nodes
            .iter()
            .find(|n| s(get(n, "id")) == s(get(get(outputs, "domain"), "node")))
            .unwrap();
        let parameters = nodes
            .iter()
            .find(|n| s(get(n, "id")) == s(get(get(get(domain, "value"), "parameters"), "node")))
            .unwrap();
        assert_eq!(arr(get(get(parameters, "value"), "elements")).len(), count);
    }
}

#[test]
fn explicitly_bound_external_owner_keeps_its_dependent_law_family() {
    let input = input();
    let map = String::from_utf8(input.sources().archmap().bytes().to_vec())
        .unwrap()
        .replace(
            r#""subjects":["#,
            r#""subjects":[{"id":"r2","type":"Pattern.Root","origin":"model"},"#,
        )
        .replace(
            r#""id":"oq","subject":"q","field":"Pattern.Part.owner","value":["v","root"]"#,
            r#""id":"oq","subject":"q","field":"Pattern.Part.owner","value":["v","r2"]"#,
        );
    let law = String::from_utf8(input.sources().law().bytes().to_vec())
        .unwrap()
        .replace(
            "change choose(c:Part,b:Bool)=c with {flag=b};",
            "change choose(c:Part)=c with {flag=c.flag};",
        )
        .replace("valid(c:Part):c.flag", "valid(r:Root,c:Part[r]):c.flag");
    let dir = workdir("change-external-owner");
    std::fs::write(dir.join("d.json"), input.sources().definitions()[0].bytes()).unwrap();
    std::fs::write(dir.join("a.json"), map).unwrap();
    std::fs::write(dir.join("l.law"), law).unwrap();
    for (index, ask, code) in [
        (
            0,
            "s=solve(Selected.valid,on=@v/root,using=Selected.choose,r=@v/r2)",
            1,
        ),
        (
            1,
            "s=solve(Selected.valid,on=@v/root,using=Selected.choose,r=@v/root)",
            0,
        ),
        (
            2,
            "s=solve(Selected.valid,on=@v/root,using=Selected.choose)",
            1,
        ),
    ] {
        let out = format!("out{index}");
        let result = run(
            &dir,
            &[
                "run",
                "--atom-definition",
                "d.json",
                "--archmap",
                "a.json",
                "--law",
                "l.law",
                "--out",
                &out,
                "--ask",
                ask,
            ],
        );
        assert_eq!(result.code, code, "{}", result.stdout);
        let result = result_json(&dir, &result);
        assert_eq!(
            s(get(answer(&result, "s"), "status")),
            if code == 0 { "established" } else { "refuted" }
        );
    }
}

#[test]
fn finite_owner_completion_produces_a_solution_judgment_instead_of_not_implemented() {
    let original = input();
    let map = String::from_utf8(original.sources().archmap().bytes().to_vec()).unwrap();
    let missing = map.replace(
        r#"{"id":"oq","subject":"q","field":"Pattern.Part.owner","value":["v","root"],"origin":"model"},"#,
        "",
    );
    assert_ne!(map, missing);
    let sources = archsig_input::input::InputSources::from_bytes(
        original
            .sources()
            .definitions()
            .iter()
            .map(|d| d.bytes().to_vec())
            .collect(),
        original.sources().law().bytes().to_vec(),
        missing.into_bytes(),
    );
    let control = archsig_common::control::Control::unlimited();
    let prepared = observed::prepare_observed(
        sources,
        &["s=solve(Selected.valid,on=@v/root,using=Selected.choose)"],
        &control,
    )
    .expect("既存の有限owner欠測fixtureは三入力と要求が有効");
    let result = match observed::evaluate_observed(prepared, &control) {
        Ok(result) => result,
        Err(observed::EvaluationFailure::NotImplemented {
            partial, feature, ..
        }) if feature.contains("存在・一意性は検査済み") => *partial,
        Err(observed::EvaluationFailure::NotImplemented {
            declaration,
            feature,
            ..
        }) => {
            panic!("有限owner補完の計算結果が必要: {declaration}: {feature}")
        }
        Err(other) => panic!("予期しない評価失敗: {other:?}"),
    };
    let wire = archsig_common::json::parse(result.wire().canonical().as_bytes()).unwrap();
    let outputs = get(answer(&wire, "s"), "outputs");
    let proposition = node(&wire, get(outputs, "proposition"));
    // 登録Rootはroot一つ。整合するowner補完は一つで、p/q双方をtrueにする解が存在する。
    assert_eq!(
        s(get(get(proposition, "judgment"), "status")),
        "established"
    );
}

#[path = "common/owner_completion_change.rs"]
mod owner_completion;

#[test]
fn change_projections_expose_the_candidate_base_but_not_state_metadata_or_witnesses() {
    let input = input();
    let dir = workdir("change-private-projections");
    for (name, bytes) in [
        ("d.json", input.sources().definitions()[0].bytes()),
        ("a.json", input.sources().archmap().bytes()),
        ("l.law", input.sources().law().bytes()),
    ] {
        std::fs::write(dir.join(name), bytes).unwrap();
    }
    let solve = "s=solve(Selected.valid,on=@v/root,using=Selected.choose)";
    let execute = |query: &str| {
        run(
            &dir,
            &[
                "run",
                "--atom-definition",
                "d.json",
                "--archmap",
                "a.json",
                "--law",
                "l.law",
                "--out",
                "out",
                "--ask",
                solve,
                "--ask",
                query,
            ],
        )
    };
    for path in [
        "domain.states.base",
        "solutions.representation",
        "solutions.representation.particular",
        "solutions.representation.directions",
        "solutions.representation.basis",
        "solutions.representation.certificate",
        "solutions.witness",
    ] {
        let query = format!("v=evaluate(Selected.flag,on=$s.{path},c=@v/q)");
        let rejected = without_file_changes(&dir, || execute(&query));
        let receipt = notified(&dir, &rejected, "invalid", 64);
        assert!(
            arr(get(&receipt, "issues")).iter().all(|r| {
                s(get(r, "code")) == "usage"
                    && s(get(r, "message")).contains("does not expose this projection")
            }),
            "{path}: {}",
            rejected.stdout
        );
        assert!(!dir.join("out").exists());
    }
    let accepted = execute("v=evaluate(Selected.flag,on=$s.domain.base,c=@v/q)");
    assert_eq!(accepted.code, 0, "{}", accepted.stdout);
    let result = result_json(&dir, &accepted);
    let answer = &arr(get(&result, "answers"))[1];
    assert_eq!(s(get(answer, "status")), "established");
    let value_ref = get(get(answer, "outputs"), "value");
    let value = arr(get(&result, "nodes"))
        .iter()
        .find(|n| get(n, "id").value == get(value_ref, "node").value)
        .unwrap();
    assert_eq!(
        get(value, "value").value,
        archsig_common::json::JValue::Bool(false)
    );
}
