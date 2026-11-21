//! 意味保存・条件付き解空間・相互作用エンジンのモジュール境界（Step 3 で実装）。
//!
//! 責務:
//! - 検証済み IR（`CheckedShigureTask`）からの保存残差方程式と商環上の状態 Law 閉性の生成
//! - 条件付き解空間 F_{a,H,P} の計算、空性 witness・具体解・自由パラメータの導出
//! - 操作式・状態表示・状態比較 h・語翻訳 τ への復元と元式への再評価検算
//! - 座標面支持による相互作用参加変数数と極小不成立部分族の解析
//! - 適用条件外の入力・未観測欠測に対する沈黙（`Verdict::Undetermined`）の返却

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
