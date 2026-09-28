# research — AAT / SFT の研究領域

`research/` は、AAT / SFT の研究目標、候補、証明設計、検証成果を置く領域である。
研究の方向は [研究の全体目標](../docs/research_goal.md) に従う。
数学本文は `docs/`、研究用の Lean 証拠は独立 package の `research/lean/`、
本体の Lean 形式化は `Formal/AG` にある。

## 研究の種類

研究は GOAL ごとに目的と達成条件を定める。

| 種類 | 研究対象 | 実行手順 |
| --- | --- | --- |
| 探索型 (`score-phase`) | 研究で獲得したい能力。候補の貢献を既存手法との比較と SCORE で評価する | [research-loop](../.codex/skills/research-loop/SKILL.md) |
| 大定理証明型 (`target-theorem`) | 固定された定理と、その証明・構成に必要な義務 | [target-theorem-loop](../.codex/skills/target-theorem-loop/SKILL.md) |

GOAL の一覧と記載基準は [goals/README.md](goals/README.md) にある。

## 成果物の所在

以下のパスは `research/` からの相対パスである。

| 場所 | 役割 |
| --- | --- |
| [goals/](goals/README.md) | 個別 GOAL の研究目的、固定 target、評価基準、達成条件 |
| [designs/](designs/README.md) | GOAL ごとの構成・証明方針、依存関係、既存宣言との対応 |
| `ideas/` | 探索型の候補カードと証拠段階。`archived/` は不採用・保留の候補 |
| `reports/` | GOAL ごとの成果、主張と証拠の対応、未解決事項 |
| [lean/](lean/README.md) | 研究用 Lean package。本体を参照できるが、本体からは依存しない |
| [DESIGN.md](DESIGN.md) | 研究方式の設計背景 |

検証方法と build 制約は [Lean package の案内](lean/README.md) と
[AAT guideline](../docs/aat/guideline.md#lean-build-運用hard-rule) を参照する。

## 定義・証拠・進行状態

GOAL カードは研究目標と達成条件を定義し、候補カード・report・Lean 成果物は
主張と証拠を対応させる。実行・査読・PR・merge の履歴と再開に必要な進行状態は、
GOAL ごとに一本の GitHub tracking Issue `Research Loop: <goal-id>` に集約する。

完了した GOAL の Lean 成果物を退役できる既定条件は、本体への蒸留完了である。
未蒸留部分が残る場合は、本体に必要な内容の unported 台帳への Issue 起票、または
本体に不要という人間の判断記録を退役条件とする。退役した成果物は現役 tree に残さず、
report または proof record に最終検証 commit と成果物一覧を保持し、現行文書からも
その固定版を参照する。

過去の ideas / reports には package 移動に合わせてパス・検証コマンドを正規化した
記録がある。当時の `pass` は当時の実行結果を表し、正規化後のコマンドの再実行を意味しない。
