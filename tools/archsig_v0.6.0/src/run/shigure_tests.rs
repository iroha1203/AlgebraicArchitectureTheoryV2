use super::*;
use crate::run::{CheckArgs, FileIo};
use std::path::PathBuf;
use std::sync::Arc;
use std::sync::atomic::AtomicI32;

struct NoFreezeSignals;
impl Signals for NoFreezeSignals {
    fn freeze(&mut self) -> Option<archsig_input::result::Signal> {
        None
    }
}

#[test]
fn deliver_shigure_records_cancelled_issue_when_signal_arrives_during_final_task() {
    let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/shigure-ledger");
    let defs = vec![std::fs::read(dir.join("ledger.atoms.json")).unwrap()];
    let law = std::fs::read(dir.join("ledger.law")).unwrap();
    let map = std::fs::read(dir.join("ledger.archmap.json")).unwrap();
    let checked = check_inputs(
        InputSources::from_bytes(defs, law, map),
        &Control::unlimited(),
    )
    .unwrap();
    let task = ShigureConverter::for_task("LedgerMigration.P1AtomicMarked")
        .convert(&checked)
        .unwrap();
    let outcome = execute_shigure_task(&task, ShigureQueryKind::ConditionalSolutionSpace);

    // 最終タスク実行中に SIGINT が到着した状態（interrupted_reason=None, control.stop_reason()=Some(Int)）
    let flag = Arc::new(AtomicI32::new(2));
    let control = Control::from_signal_flag(flag, 2, 15);
    assert_eq!(
        control.stop_reason(),
        Some(archsig_input::result::Signal::Int)
    );

    let req = ResolvedShigureRequest {
        parsed: ParsedShigureRequest {
            id: "p1m".into(),
            text: "p1m=shigure_solve(LedgerMigration.P1AtomicMarked)".into(),
            query_kind: ShigureQueryKind::ConditionalSolutionSpace,
            task_name: "LedgerMigration.P1AtomicMarked".into(),
            snapshot: None,
        },
        resolved_task_name: "LedgerMigration.P1AtomicMarked".into(),
        reading_name: "LedgerMigration".into(),
        task,
    };
    let args = RunArgs {
        inputs: CheckArgs {
            atom_definitions: vec![],
            law: PathBuf::new(),
            archmap: None,
            out: None,
        },
        asks: vec![req.parsed.text.clone()],
        reuse: None,
    };
    let mut io = FileIo;
    let mut sigs = NoFreezeSignals;
    let delivered = deliver_shigure(
        &mut io,
        &mut sigs,
        &args,
        &checked,
        vec![(req, Some(outcome))],
        vec![],
        None,
        &control,
    );
    assert_eq!(delivered.status, Status::Interrupted);
    assert_eq!(delivered.exit_code, 130);
    assert_eq!(
        delivered.issues.len(),
        1,
        "interrupted outcome must carry non-empty cancelled issue"
    );
    assert_eq!(
        delivered.issues[0],
        archsig_input::result::Signal::Int.issue()
    );
    let summary = delivered.summary.expect("completed answer summary kept");
    let Json::Obj(fields) = &summary else {
        panic!("summary must be object");
    };
    let Json::Arr(summary_issues) = fields.get("issues").expect("summary must include issues")
    else {
        panic!("summary issues must be array");
    };
    assert_eq!(summary_issues.len(), 1);
    let Json::Obj(issue_obj) = &summary_issues[0] else {
        panic!("summary issue must be object");
    };
    assert!(
        !issue_obj.contains_key("dependencies"),
        "archsig.summary/1 issues must omit `dependencies`"
    );
}

#[test]
fn shigure_ask_classifier_and_head_error_match_execution_spec() {
    // ID= 欠落かつ snapshot= を含む SHIGURE 問いを混在誤分類せず AllShigure として構文検査へ渡す
    let missing_id = "shigure_solve(LedgerMigration.P1AtomicMarked, snapshot=snap1)".to_owned();
    let valid_ask = "p=shigure_solve(LedgerMigration.P1AtomicMarked)".to_owned();
    assert_eq!(
        classify_asks(&[missing_id.clone(), valid_ask]),
        AskPartition::AllShigure
    );
    assert!(parse_single_ask(&missing_id).is_err());

    // 宣言名位置の先頭 `.` / `[` では `$` シェル展開案内を加えない（execution.md §2）
    for bad in ["a=shigure_solve(.foo)", "a=shigure_solve([0])"] {
        let msg = parse_single_ask(bad).unwrap_err();
        assert!(
            !msg.contains("shell expanded"),
            "declaration head error must not emit `$` shell expansion hint: {msg}"
        );
    }
}
