# 証明義務と実証仮説

この文書は Lean proof obligation / empirical hypothesis 台帳の入口である。
詳細台帳は、古典 AAT、代数幾何 AAT、研究ループを混ぜないために分割して管理する。

## 分割台帳

| 台帳 | 対象 | 主な用途 |
| --- | --- | --- |
| [古典 AAT / downstream Lean proof obligation 台帳](proof_obligations_classical_aat.md) | `Formal/Arch`、finite static structural core、Atom-generated kernel、SFT / tooling bridge、empirical hypothesis | 既存 bounded theorem package、古典 AAT 由来の proof obligation、tooling / empirical claim boundary を確認する。 |
| [代数幾何 AAT Lean proof obligation 台帳](proof_obligations_ag_aat.md) | `Formal/AG`、AG 版 AAT Part I〜10、本文ラベルと Lean status の対応 | 現行 AAT 数学本文に対応する Lean proof obligation と証明済みラベルを確認する。 |
| [研究ループ theorem status 台帳](proof_obligations_research.md) | `research/lean/ResearchLean`、`research/goals/`、target-theorem / research-loop の成果 | 研究ループで固定された theorem package、tracking issue、最終 review status を確認する。 |

## Source of Truth

| 対象 | Source of truth |
| --- | --- |
| 数学的定義と第一級理論 | [AAT 総合理論](README.md), [代数幾何的 AAT 数学本文](algebraic_geometric_theory/README.md) |
| Tooling、AIR、Feature Extension Report、claim taxonomy、CI / empirical 接続 | [AAT Tooling Documentation](../tool/README.md) |
| 実装済み Lean API | [Lean 定義・定理索引](lean_theorem_index.md) |
| GitHub Issue の状態、優先度、milestone | GitHub Issues |
| empirical hypotheses と pilot protocol | [古典 AAT / downstream Lean proof obligation 台帳](proof_obligations_classical_aat.md)、GitHub Issues、旧 pilot record は [archive](../archive/2026-05-09-first-class-docs/empirical/README.md) |

`docs/aat/algebraic_geometric_theory/` は純粋な理論文書であり、Lean 実装の進捗状態、
QED 境界、Issue 管理状態を持たせない。Lean status はこの入口と分割台帳、
[Lean 定義・定理索引](lean_theorem_index.md) で管理する。

## 更新ルール

- `Formal/Arch`、SFT bridge、tooling-side theorem metadata、古典 Atom-generated kernel を更新した場合は、原則として [proof_obligations_classical_aat.md](proof_obligations_classical_aat.md) を更新する。
- `Formal/AG` の AG 版 AAT Part / 本文ラベル対応を更新した場合は、[proof_obligations_ag_aat.md](proof_obligations_ag_aat.md) を更新する。
- `research/lean/ResearchLean` や `research/goals/` の target-theorem / research-loop 成果を更新した場合は、[proof_obligations_research.md](proof_obligations_research.md) を更新する。
- 実装済み Lean API の宣言一覧を更新する場合は、対応する分割版の [Lean 定義・定理索引](lean_theorem_index.md) も更新する。
- この入口は分割方針とリンクだけを持つ。詳細な proof obligation、Issue 履歴、status 行は分割台帳へ置く。
