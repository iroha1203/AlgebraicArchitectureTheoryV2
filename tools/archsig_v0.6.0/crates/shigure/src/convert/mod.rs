//! `archsig-input` → `archsig-shigure` 変換層の公開境界。
//!
//! 責務:
//! - 同一 Atom 定義の検証済み三入力束（`archsig_input::input::CheckedInputs`）から SHIGURE IR への明示的変換
//! - 結論注入禁止（残差 ideal・解・空性・参加変数数を外部入力として拒否）の型と検証による強制
//! - `Origin`（静的解析・実行観測・LLM 読解候補・人間採用）と参照位置・欠測スロットの完全な保持

mod lower;
mod lower_diagram;
mod lower_expr;
mod lower_morphism;
mod lower_path;
mod lower_transfer;
#[cfg(test)]
mod tests;
#[cfg(test)]
mod tests_extra;
#[cfg(test)]
mod tests_phase2;
#[cfg(test)]
mod tests_phase2_neg;

use crate::ir::diagram::CheckedDiagramTask;
use crate::ir::path::CheckedPathTask;
use crate::ir::transfer::CheckedTransferTask;
use crate::ir::validate::{CheckedShigureTask, ValidationError};
use archsig_input::input::CheckedInputs;

/// 変換層の共通トレイト境界。
///
/// 既存の `CheckedInputs`（Atom 定義・Law・ArchMap の同一性を検証済みの不変束）を直接受け取り、
/// 異なる Atom 定義で検査された Law と ArchMap の混在を型レベルで防ぐ。
pub trait ToShigureTask {
    fn convert(&self, inputs: &CheckedInputs) -> Result<CheckedShigureTask, ValidationError>;
}

/// `CheckedInputs` から図式補完タスク `CheckedDiagramTask` への変換境界。
pub trait ToShigureDiagramTask {
    fn convert_diagram(
        &self,
        inputs: &CheckedInputs,
    ) -> Result<CheckedDiagramTask, ValidationError>;
}

/// `CheckedInputs` から一段変更経路タスク `CheckedPathTask` への変換境界。
pub trait ToShigurePathTask {
    fn convert_path(&self, inputs: &CheckedInputs) -> Result<CheckedPathTask, ValidationError>;
}

/// `CheckedInputs` から合法状態移送タスク `CheckedTransferTask` への変換境界。
pub trait ToShigureTransferTask {
    fn convert_transfer(
        &self,
        inputs: &CheckedInputs,
    ) -> Result<CheckedTransferTask, ValidationError>;
}

/// `CheckedInputs` から指定 SHIGURE タスクを抽出して `CheckedShigureTask` へ変換する標準変換器。
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ShigureConverter {
    /// 明示指定する `shigure task` 名（完全名 `Reading.Task` または一意な短名 `Task`）。
    /// `None` のときは Law 内の一意な `shigure task`、または task 未宣言かつ
    /// `(comparison, change_spec)` が一意に定まる場合のみ自動選択する。
    pub task_name: Option<String>,
    /// ArchMap の `observed` 座標参照で対象を絞る snapshot ID（省略時は全 snapshot で一意一致を要求）。
    pub snapshot_id: Option<String>,
}

impl ShigureConverter {
    pub fn for_task(task_name: impl Into<String>) -> Self {
        Self {
            task_name: Some(task_name.into()),
            snapshot_id: None,
        }
    }

    pub fn with_snapshot(mut self, snapshot_id: impl Into<String>) -> Self {
        self.snapshot_id = Some(snapshot_id.into());
        self
    }
}

impl ToShigureTask for ShigureConverter {
    fn convert(&self, inputs: &CheckedInputs) -> Result<CheckedShigureTask, ValidationError> {
        lower::convert_checked_inputs(
            inputs,
            self.task_name.as_deref(),
            self.snapshot_id.as_deref(),
        )
    }
}

impl ToShigureDiagramTask for ShigureConverter {
    fn convert_diagram(
        &self,
        inputs: &CheckedInputs,
    ) -> Result<CheckedDiagramTask, ValidationError> {
        lower_diagram::convert_diagram_task(
            inputs,
            self.task_name.as_deref(),
            self.snapshot_id.as_deref(),
        )
    }
}

impl ToShigurePathTask for ShigureConverter {
    fn convert_path(&self, inputs: &CheckedInputs) -> Result<CheckedPathTask, ValidationError> {
        lower_path::convert_path_task(
            inputs,
            self.task_name.as_deref(),
            self.snapshot_id.as_deref(),
        )
    }
}

impl ToShigureTransferTask for ShigureConverter {
    fn convert_transfer(
        &self,
        inputs: &CheckedInputs,
    ) -> Result<CheckedTransferTask, ValidationError> {
        lower_transfer::convert_transfer_task(
            inputs,
            self.task_name.as_deref(),
            self.snapshot_id.as_deref(),
        )
    }
}

/// `CheckedInputs` 内の Law に宣言されている全 `shigure task` の完全名一覧を返す。
pub fn list_shigure_tasks(inputs: &CheckedInputs) -> Vec<String> {
    inputs.law().shigure().tasks.keys().cloned().collect()
}

/// `CheckedInputs` 内の Law に宣言されている全 `shigure diagram` の完全名一覧を返す。
pub fn list_shigure_diagrams(inputs: &CheckedInputs) -> Vec<String> {
    inputs.law().shigure().diagrams.keys().cloned().collect()
}

/// `CheckedInputs` 内の Law に宣言されている全 `shigure path` の完全名一覧を返す。
pub fn list_shigure_paths(inputs: &CheckedInputs) -> Vec<String> {
    inputs.law().shigure().paths.keys().cloned().collect()
}

/// `CheckedInputs` 内の Law に宣言されている全 `shigure transfer` の完全名一覧を返す。
pub fn list_shigure_transfers(inputs: &CheckedInputs) -> Vec<String> {
    inputs.law().shigure().transfers.keys().cloned().collect()
}
