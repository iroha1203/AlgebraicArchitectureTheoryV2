//! 意味保存・条件付き解空間・相互作用エンジン（Step 3 実装）。
//!
//! 責務:
//! - `preservation`: 検証済み IR（`CheckedShigureTask`）からの 4 族の保存義務生成、
//!   商環上の状態 Law 閉性層別、ideal 交わりと Zariski 閉性判定
//! - `restore` / `restore_format`: 抽出されたアフィン／具体解からの操作式・状態表示・状態比較 h・
//!   語翻訳 τ 復元と独立した数学モデル再評価検算（`ReevalCheck`）
//! - `solve` / `domain_solve` / `interaction_query`: 適用条件検査、係数域・点集合域ごとの計算分岐、
//!   沈黙（`Verdict::Undetermined`）規律、座標面支持による相互作用解析の統合実行

mod domain_solve;
mod interaction_query;
pub mod preservation;
pub mod restore;
mod restore_format;
pub mod solve;

#[cfg(test)]
mod tests;
#[cfg(test)]
mod tests_extra;

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
