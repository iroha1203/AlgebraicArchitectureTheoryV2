//! 意味保存・条件付き解空間・相互作用エンジン（Step 3 実装）。
//!
//! 責務:
//! - `preservation`: 検証済み IR（`CheckedShigureTask`）からの 4 族の保存義務生成、
//!   商環上の状態 Law 閉性層別、ideal 交わりと Zariski 閉性判定
//! - `restore` / `restore_format`: 抽出されたアフィン／具体解からの操作式・状態表示・状態比較 h・
//!   語翻訳 τ 復元と独立した数学モデル再評価検算（`ReevalCheck`）
//! - `solve` / `domain_solve` / `interaction_query`: 適用条件検査、係数域・点集合域ごとの計算分岐、
//!   沈黙（`Verdict::Undetermined`）規律、座標面支持による相互作用解析の統合実行

mod artin;
mod artin_z;
mod atlas;
mod atlas_condition_c;
mod atlas_ext;
mod atlas_graph;
mod atlas_refinement;
mod atlas_repair;
mod chevalley;
mod chevalley_sections;
mod common_format;
mod common_morph;
mod common_solve;
mod common_solve_q;
mod context;
mod diagnostics;
mod diagnostics_change;
mod diagnostics_collision;
mod diagnostics_strat;
mod diagram;
mod domain_solve;
mod family_direct;
mod family_eval;
mod family_existential;
mod interaction_query;
mod lift;
mod lift_affine;
mod lift_backend;
mod lift_common;
mod lift_extensions;
mod observation;
mod occurrence;
mod occurrence_attr;
mod partial_affine;
mod partial_completions;
mod partial_eval;
mod partial_kleene;
mod partial_open;
mod path;
mod path_fixed;
mod path_protocol;
pub(crate) mod preservation;
pub(crate) mod restore;
mod restore_format;
mod robustness;
mod robustness_reading;
mod robustness_symbolic;
mod robustness_universal;
pub(crate) mod solve;
mod transfer;
mod transfer_compose;
mod transfer_lift;
mod transfer_words;

#[cfg(test)]
mod tests;
#[cfg(test)]
mod tests_artin;
#[cfg(test)]
mod tests_atlas;
#[cfg(test)]
mod tests_atlas_extra;
#[cfg(test)]
mod tests_chevalley;
#[cfg(test)]
mod tests_diagnostics;
#[cfg(test)]
mod tests_diagram;
#[cfg(test)]
mod tests_diagram_extra;
#[cfg(test)]
mod tests_extra;
#[cfg(test)]
mod tests_lift;
#[cfg(test)]
mod tests_lift_extra;
#[cfg(test)]
mod tests_lift_r3_r4;
#[cfg(test)]
mod tests_observation;
#[cfg(test)]
mod tests_occurrence;
#[cfg(test)]
mod tests_partial;
#[cfg(test)]
mod tests_path;
#[cfg(test)]
mod tests_path_extra;
#[cfg(test)]
mod tests_phase3_audit_regressions;
#[cfg(test)]
mod tests_phase3_regressions;
#[cfg(test)]
mod tests_phase3_rerun3_regressions;
#[cfg(test)]
mod tests_phase3_rerun4_regressions;
#[cfg(test)]
mod tests_regressions;
#[cfg(test)]
mod tests_robustness;
#[cfg(test)]
mod tests_robustness_extra;
#[cfg(test)]
mod tests_transfer;
#[cfg(test)]
mod tests_transfer_extra;

pub use artin::solve_artin_task;
pub use atlas::solve_atlas_task;
pub use chevalley::solve_chevalley_task;
pub use diagnostics::solve_diagnostics_task;
pub use diagram::solve_diagram_task;
pub use lift::solve_lift_task;
pub use observation::solve_observation_task;
pub use occurrence::solve_occurrence_task;
pub use partial_eval::solve_partial_task;
pub use path::solve_path_task;
pub use robustness::solve_robustness_task;
pub use transfer::solve_transfer_task;

use crate::ir::result::ShigureOutcome;
use crate::ir::validate::CheckedShigureTask;

/// SHIGURE の問い種別。
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ShigureQueryKind {
    /// 意味保存変更の検査（生成操作の保存・商環での状態 Law 閉性・全許可有限語の保存根拠）。
    SemanticPreservation,
    /// 条件付き解空間 F_{a,H,P} の計算と操作式・状態表示・h・τ への復元。
    ConditionalSolutionSpace,
    /// 座標面支持による相互作用参加変数数 r と極小不成立部分族の解析。
    InteractionAnalysis,
}

/// solver 入口の共通トレイト境界。
pub trait ShigureEngine {
    fn execute(&self, task: &CheckedShigureTask, query: ShigureQueryKind) -> ShigureOutcome;
}

/// 標準の SHIGURE 計算エンジン。
#[derive(Clone, Copy, Debug, Default)]
pub struct DefaultShigureEngine;

impl ShigureEngine for DefaultShigureEngine {
    fn execute(&self, task: &CheckedShigureTask, query: ShigureQueryKind) -> ShigureOutcome {
        solve::execute_task(task, query)
    }
}

/// 検証済み SHIGURE タスクを実行する便利関数。
pub fn execute_shigure_task(task: &CheckedShigureTask, query: ShigureQueryKind) -> ShigureOutcome {
    DefaultShigureEngine.execute(task, query)
}
