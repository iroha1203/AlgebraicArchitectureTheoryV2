//! 整数不等式の算法非対応と、後続要求の依存停止を実CLIで区別する。
use crate::common::cli::*;
use archsig_input::definition;

const DEFINITION: &str = r#"{"format":"archsig.atom-definition/1","semantics":"archsig/0.6.0","vocabularies":[{"semantics":"archsig/0.6.0","namespace":"M","version":"1","dependencies":[],"declarations":[{"kind":"entity","name":"M.State","meaning":"整数状態。","parameters":[],"fields":[{"name":"x","type":"Z","meaning":"座標。"}],"alignments":[]}]}]}"#;

#[test]
fn integer_localize_reports_unsupported_condition_and_keeps_independent_check() {
    for condition in [
        "s.x < 1",
        "s.x <= 1",
        "s.x > -1",
        "s.x >= -1",
        "s.x != 1",
        "s.x = 0",
    ] {
        let dir = workdir("local-numeric-condition");
        let definitions = definition::check_definitions(&[("d", DEFINITION.as_bytes())]).unwrap();
        let digest = &definitions.vocabularies()["M"].digest;
        let law = format!(
            r#"law "archsig.law/2" semantics "archsig/0.6.0"; reading R {{ use vocabulary M version "1" digest "{digest}"; law required ok(s:M.State): {condition}; local part(s:M.State) reads s.x; change move(s:M.State,x:Z)=s with {{x=x}}; }}"#
        );
        let map = format!(
            r#"{{"format":"archsig.archmap/2","semantics":"archsig/0.6.0","vocabularies":[{{"namespace":"M","version":"1","digest":"{digest}"}}],"sources":[],"origins":[{{"id":"model","mode":"specification","method":"整数条件の独立試験。","locations":[],"note":"既知の零を観測する。"}}],"snapshots":[{{"id":"v","origin":"model","subjects":[{{"id":"s","type":"M.State","origin":"model"}}],"atoms":[{{"id":"x","subject":"s","field":"M.State.x","value":"0","origin":"model"}}]}}]}}"#
        );
        for (name, text) in [("d.json", DEFINITION), ("l.law", &law), ("a.json", &map)] {
            std::fs::write(dir.join(name), text).unwrap();
        }
        let run = run_binary(
            &dir,
            &[
                "run",
                "--atom-definition",
                "d.json",
                "--law",
                "l.law",
                "--archmap",
                "a.json",
                "--out",
                "out",
                "--ask",
                "b=build(R,on=@v/s)",
                "--ask",
                "l=localize($b.object,using=R.move)",
                "--ask",
                "d=diagnose($l.system)",
                "--ask",
                "c=check(R.ok,bind.s=@v/s)",
            ],
        );
        let equality = condition == "s.x = 0";
        assert_eq!(
            run.code,
            if equality { 0 } else { 2 },
            "{condition}: {}",
            run.stdout
        );
        let result = result_json(&dir, &run);
        let answers = arr(get(&result, "answers"));
        assert!(has(get(&answers[0], "outputs"), "object"));
        assert_eq!(s(get(&answers[3], "status")), "established");
        if equality {
            assert!(has(get(&answers[1], "outputs"), "system"));
            assert_eq!(s(get(&answers[1], "status")), "established");
            assert_eq!(s(get(&answers[2], "status")), "established");
        } else {
            assert!(!has(get(&answers[1], "outputs"), "system"));
            assert_eq!(s(get(&answers[1], "status")), "undetermined");
            let reasons = arr(get(&answers[1], "reasons"));
            assert_eq!(reasons.len(), 1);
            assert_eq!(s(get(&reasons[0], "code")), "unsupported_algorithm");
            let details = get(&reasons[0], "details");
            assert_eq!(s(get(details, "question")), "localize");
            assert_eq!(s(get(details, "method")), "numeric_change_condition");
            assert_eq!(s(&arr(get(details, "operand_types"))[0]), "Z");
            assert!(
                arr(get(&answers[2], "reasons"))
                    .iter()
                    .any(|r| s(get(r, "code")) == "dependency_blocked")
            );
        }
    }
}

#[test]
fn unsupported_localize_retains_typed_source_and_unbound_integer_domain() {
    use crate::common::helpers::{arr, f, index, target, text, val};
    use crate::common::quiet;
    use archsig_common::canonical::Json;
    use archsig_computation::observed::evaluate_observed_bytes;
    use archsig_input::input::InputSources;

    let definitions = definition::check_definitions(&[("d", DEFINITION.as_bytes())]).unwrap();
    let digest = &definitions.vocabularies()["M"].digest;
    let law = format!(
        r#"law "archsig.law/2" semantics "archsig/0.6.0"; reading R {{ use vocabulary M version "1" digest "{digest}"; law required ok(s:M.State,k:Z): s.x < k; local part(s:M.State) reads s.x; change move(s:M.State,x:Z)=s with {{x=x}}; }}"#
    );
    let map = format!(
        r#"{{"format":"archsig.archmap/2","semantics":"archsig/0.6.0","vocabularies":[{{"namespace":"M","version":"1","digest":"{digest}"}}],"sources":[],"origins":[{{"id":"model","mode":"specification","method":"整数域の独立試験。","locations":[],"note":"既知の零を観測する。"}}],"snapshots":[{{"id":"v","origin":"model","subjects":[{{"id":"s","type":"M.State","origin":"model"}}],"atoms":[{{"id":"x","subject":"s","field":"M.State.x","value":"0","origin":"model"}}]}}]}}"#
    );
    let inputs = InputSources::from_bytes(
        vec![DEFINITION.as_bytes().to_vec()],
        law.clone().into_bytes(),
        map.into_bytes(),
    );
    let evaluated = evaluate_observed_bytes(
        inputs.clone(),
        &["b=build(R,on=@v/s)", "l=localize($b.object,using=R.move)"],
        &quiet(),
    )
    .unwrap();
    assert_eq!(evaluated.prepared().inputs().sources(), &inputs);
    let wire = evaluated.wire();
    let answer = &arr(f(&wire, "answers"))[1];
    assert_eq!(f(answer, "status"), &Json::str("undetermined"));
    let reason = &arr(f(answer, "reasons"))[0];
    assert_eq!(f(reason, "code"), &Json::str("unsupported_algorithm"));
    let nodes = index(&wire);
    let source = target(
        &nodes,
        &arr(f(reason, "dependencies"))[0],
        &Json::str("Expression"),
    );
    let value = val(source);
    assert_eq!(f(value, "kind"), &Json::str("source"));
    assert_eq!(
        f(value, "parameters"),
        &Json::Arr(vec![Json::obj([
            ("name", Json::str("k")),
            ("type", Json::str("Z"))
        ])])
    );
    assert_eq!(text(f(&arr(f(value, "bindings"))[0], "name")), "s");
    let span = arr(f(f(value, "location"), "span"));
    let start: usize = span[0].canonical().parse().unwrap();
    let end: usize = span[1].canonical().parse().unwrap();
    assert_eq!(&law[start..end], "s.x < k");
    assert_eq!(f(reason, "location"), f(value, "location"));
}
