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
// 結果の種類(成立・反証・未決・未対応混在)と、欠測・guard・有理数の違いで経路が変わる代表だけを残す。
// 同じ判断を別の値や入れ子で繰り返す組(simultaneous・target-extra・kernel・guard・inequality・source-fraction)は外す。
// index % 5 で5本に分けて並列に回す。
const KEPT: [(&str, &str); 10] = [
    ("same-fields", "Z"),
    ("slanted", "Z"),
    ("fraction", "Q"),
    ("reverse-guard", "Z"),
    ("empty", "Z"),
    ("mixed", "Z"),
    ("fraction", "Z"),
    ("missing", "Z"),
    ("nonlinear", "Z"),
    ("partial", "Z"),
];
#[test]
fn numeric_tuple_change_transport_preserves_each_condition_0() {
    check_part(0);
}
#[test]
fn numeric_tuple_change_transport_preserves_each_condition_1() {
    check_part(1);
}
#[test]
fn numeric_tuple_change_transport_preserves_each_condition_2() {
    check_part(2);
}
#[test]
fn numeric_tuple_change_transport_preserves_each_condition_3() {
    check_part(3);
}
#[test]
fn numeric_tuple_change_transport_preserves_each_condition_4() {
    check_part(4);
}
fn check_part(part: usize) {
    for (index, (name, ty)) in KEPT.iter().enumerate() {
        if index % 5 != part {
            continue;
        }
        let case = fixture::cases()
            .into_iter()
            .find(|case| !case.nested && case.name == *name && case.ty == *ty)
            .unwrap();
        let input = case.input();
        // 元のfresh CLIと同じ120秒の計算予算。
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
        // needed は欠測の計画を照合する組だけが使う。
        let asks = if case.code == 70 {
            &fixture::REQUESTS[..1]
        } else if matches!(case.name, "missing" | "partial") {
            &fixture::REQUESTS[..]
        } else {
            &fixture::REQUESTS[..2]
        };
        let prepared = prepare_shared_observed(inputs, asks, &mut c).unwrap();
        let evaluated = evaluate_observed(prepared, &mut c);
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
            let mut display = Control::unlimited();
            let result = result
                .result_wire_controlled(&mut display, Checkpoint::Expression)
                .unwrap();
            let result = archsig::json::parse(result.canonical().as_bytes()).unwrap();
            case.assert_result(&result);
        }
    }
}
