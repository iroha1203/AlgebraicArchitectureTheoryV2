//! 組立対象の保存結果を現在の入力で再検証する。
use crate::common::{cli::*, model_assembly_data as fixture};
use archsig_common::canonical::Json;
use std::path::Path;
fn execute(dir: &Path, out: &str, reuse: Option<&str>) -> BinaryRun {
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
        fixture::ASSEMBLE,
        "c=check(Assembly.zero,on=$a.object)",
        "o=evaluate(Assembly.ownerOf,on=$a.object,p=@v/b)",
    ] {
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
}
