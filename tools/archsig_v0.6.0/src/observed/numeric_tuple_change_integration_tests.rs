//! 数値Tuple changeの各条件を、実際のmap評価経路で検査する。CLI配送は別targetが所有する。
#[path = "../../tests/common/numeric_tuple_change.rs"]
mod fixture;
use super::result::ReasonKind;
use archsig::{
    control::{Checkpoint, Control, Limits, Usage},
    input::check_inputs,
    observed::{EvaluationFailure, evaluate::evaluate_observed, prepare_shared_observed},
};
use std::sync::Arc;
#[test]
fn numeric_tuple_change_transport_preserves_each_condition() {
    // 条件ごとに、型と入れ子で結果の終了コードが変わる組だけを残す。
    let mut seen = std::collections::BTreeSet::new();
    let cases: Vec<_> = fixture::cases()
        .into_iter()
        .filter(|case| seen.insert((case.name, case.code)))
        .collect();
    for case in cases {
        let started = std::time::Instant::now();
        let input = case.input();
        // 元のfresh CLIと同じ120秒の計算予算。fixture構築と表示・assertionは別に測る。
        let budget_started = std::time::Instant::now();
        let mut c = Control::new(
            Limits {
                time_ms: (case.code != 70).then_some(120000),
                memory_mib: None,
            },
            move |_| Usage {
                elapsed_ms: budget_started.elapsed().as_millis(),
                ..Usage::default()
            },
        );
        let inputs = Arc::new(check_inputs(input, &mut c).unwrap());
        let asks = if case.code == 70 {
            &fixture::REQUESTS[..1]
        } else {
            &fixture::REQUESTS[..]
        };
        let prepared = prepare_shared_observed(inputs, asks, &mut c).unwrap();
        let setup = started.elapsed();
        let evaluated = evaluate_observed(prepared, &mut c);
        let evaluation = started.elapsed() - setup;
        assert!(
            c.stop_reason().is_none(),
            "{}: calculation budget exhausted",
            case.label()
        );
        if case.code == 70 {
            match evaluated {
                Err(EvaluationFailure::NotImplemented { feature, .. }) => {
                    assert!(!feature.is_empty())
                }
                Ok(result) => {
                    // 現行map入口は未対応混在を実行失敗として返す。数学的な未決とは区別する。
                    assert_eq!(result.status(), "error", "{}", case.label());
                    assert!(!result.issues.is_empty());
                    assert!(
                        result
                            .issues
                            .iter()
                            .all(|r| matches!(r.kind, ReasonKind::Internal(_)))
                    );
                    assert_eq!(result.answers.len(), 1);
                    assert!(!result.answers[0].outputs.contains_key("map"));
                }
                Err(EvaluationFailure::Prepare(_)) => {
                    panic!("{}: failed before evaluation", case.label())
                }
            }
        } else {
            let result = evaluated.unwrap_or_else(|e| match e {
                EvaluationFailure::NotImplemented { feature, .. } => {
                    panic!("{}: {feature}", case.label())
                }
                EvaluationFailure::Prepare(_) => {
                    panic!("{}: failed before evaluation", case.label())
                }
            });
            // 数学的な結果投影を照合する。OS計測の配送はCLI testが所有する。
            let mut display = Control::new(Limits::default(), |_| Usage::default());
            let result = result
                .result_wire_controlled(&mut display, Checkpoint::Expression)
                .unwrap();
            let result = archsig::json::parse(result.canonical().as_bytes()).unwrap();
            case.assert_result(&result);
        }
        eprintln!(
            "{} setup={setup:?} evaluation={evaluation:?} wire/assert={:?}",
            case.label(),
            started.elapsed() - setup - evaluation
        );
    }
}
