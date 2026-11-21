//! `archsig-input` → `archsig-shigure` 変換層のモジュール境界（Step 4 で実装）。
//!
//! 責務:
//! - 同一 Atom 定義の検証済み三入力束（`archsig_input::input::CheckedInputs`）から SHIGURE IR への明示的変換
//! - 結論注入禁止（残差 ideal・解・空性・参加変数数を外部入力として拒否）の型と検証による強制
//! - `Origin`（静的解析・実行観測・LLM 読解候補・人間採用）と参照位置の完全な保持

use crate::ir::validate::{CheckedShigureTask, ValidationError};
use archsig_input::input::CheckedInputs;

/// 変換層の共通トレイト境界。
///
/// 既存の `CheckedInputs`（Atom 定義・Law・ArchMap の同一性を検証済みの不変束）を直接受け取り、
/// 異なる Atom 定義で検査された Law と ArchMap の混在を型レベルで防ぐ。
pub trait ToShigureTask {
    fn convert(&self, inputs: &CheckedInputs) -> Result<CheckedShigureTask, ValidationError>;
}
