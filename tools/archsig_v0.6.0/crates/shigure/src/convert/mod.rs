//! `archsig-input` → `archsig-shigure` 変換層のモジュール境界（Step 4 で実装）。
//!
//! 責務:
//! - 検査済み `archsig-input`（Atom 定義・Law・ArchMap）から SHIGURE IR への明示的変換
//! - 結論注入禁止（残差 ideal・解・空性・参加変数数を外部入力として拒否）の型と検証による強制
//! - `Origin`（静的解析・実行観測・LLM 読解候補・人間採用）と参照位置の完全な保持

use crate::ir::validate::{CheckedShigureTask, ValidationError};
use archsig_input::archmap::CheckedArchMap;
use archsig_input::law::CheckedLaw;

/// 変換層が受け取る検査済み入力参照の組。
pub struct InputRef<'a> {
    pub law: &'a CheckedLaw,
    pub archmap: &'a CheckedArchMap,
}

/// 変換層の共通トレイト境界。
pub trait ToShigureTask {
    fn convert(&self, input: InputRef<'_>) -> Result<CheckedShigureTask, ValidationError>;
}
