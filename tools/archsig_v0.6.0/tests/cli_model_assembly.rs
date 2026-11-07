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
