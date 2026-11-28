---
name: lean-prd-loop
description: Lean形式化PRDを全体スケルトン作成と分散並列証明で完了まで実装する。"$lean-prd-loop path/to/prd.md"やLean PRDの実装依頼で使う。非Lean PRDにはprd-loop、完了判定だけならprd-completion-reviewを使う。
---

# Lean PRD Loop

Lean 形式化 PRD を、**全体スケルトン先行 → 依存順の分散並列証明 → 最終完了レビュー** の 3 段階で完了まで進める。

- 起動: `$lean-prd-loop docs/prd/<prd-file>.md`（任意: `max-iterations <N>`、対象範囲の指定）
- PRD は編集しない。矛盾・実装不能・固定 statement の変更が必要なら `PRD 欠陥` で止まる。
- 既存 SKILL をそのまま使う: Issue 作成は `$issue-creater`、PR レビューは `$review-pr`（`$math-lean-review` 独立 4 lane）、最終判定は `$prd-completion-review`（独立 4 lane）。

## 参照先

基準や反証観点はリンク先をそのまま適用し、ここで言い換えない。

- 横断規律・PR 共通確認・語彙・PRD 削除: [Workflow guideline](../../../docs/workflow/guideline.md)、[語彙ルール](../../../docs/workflow/vocabulary.md)、[PRD guideline](../../../docs/prd/guideline.md)
- Lean 規律・`lake build` 運用・statement 品質: [AAT guideline](../../../docs/aat/guideline.md)、[Lean 品質基準](../../../docs/aat/lean_quality_standard.md)
- 共有レビュー手順・反証チェック: [review-protocol](../_shared/review-protocol.md)、[refutation-checklist](../_shared/refutation-checklist.md)、[lean-refutation-checklist](../_shared/lean-refutation-checklist.md)
- ビルド性能と高速化: [performance.md](references/performance.md)

## 手順

### 0. 開始確認と再開位置の特定

1. `git status --short --branch` が clean であることを確認し、`git switch main && git pull --ff-only` で最新化する（未コミット変更があれば始めずに報告する）。
2. PRD と `.github/workflows/` を読み、実装先・許可 import・検証コマンド・一次仕様を確認する（一次仕様から対象を読み取れなければ `PRD 欠陥` で止まる）。
3. tracking Issue（`Lean PRD Loop: <PRD ファイル名>`、既存の `PRD Loop: <PRD ファイル名>` があれば再利用）を探すか作成し、PRD パス・AC checklist・進捗/性能ログの置き場とする。
4. tracking Issue と `main` の実体から再開位置を判断する（全体スケルトン確定済みなら Phase 2、全 AC が揃った候補状態なら Phase 3 へ進む）。

### 1. Phase 1: 全体スケルトン作成と設計チェック（初回のみ）

1. PRD 全体で使う mathlib API・型クラス・宇宙パラメータ・未収録の標準事実を並列 `rg` で調べる。
2. 全体の依存 DAG（上流を薄く、下流を横に広げる構成）と、依存順に並列実装して `sorry` ゼロで閉じられる PR 単位（Wave / トラック）を設計する。
3. `main` からローカル専用ブランチ（例: `lean-prd-skeleton-<slug>`。push・PR はしない）を切り、PRD 全体の公開 `def` / `structure` / 基本 API（`def` は極力 `sorry` なし）と全主要 `theorem` / 具体例の statement（証明本体のみ一時 `sorry`）を書き切る。
4. 親が対象モジュールを型チェックし、全体を通じて型・宇宙・mathlib 接続・許可 import が矛盾なく通ることを確認する。
5. 新規・履歴なし（`fork_turns: "none"`）の subagent を 1 本起動し、一次仕様と全体スケルトンを突き合わせて設計チェックを行う（弱化・余計な仮定・definitional escape・mathlib 重複・退化例・性能リスク）。指摘があれば Phase 2 前に設計ブランチ上で直す。なお、これは手戻り防止のローカル確認であり、PR 後の 4 lane 査読の代わりにはしない。
6. 確定した Wave / PR 計画を tracking Issue に記録する。

### 2. Phase 2: 依存順の分散並列実装（全 AC 完了まで反復）

依存が満たされた Wave / トラックから順に進める。

1. **取り込みと Issue**: 最新 `main` から PR 用ブランチを切り、設計ブランチから対象単位のファイルだけを取り込む（未完単位のファイルは混ぜない）。対応する sub-issue が無ければ `$issue-creater` で作成して tracking Issue に紐付ける（`受け入れ要件` に該当 AC 文言を引用する）。
2. **土台ビルド（親）**: 共有される `Defs` / 基本 API を `sorry` ゼロで仕上げ、親が対象モジュールだけ `lake build` して `.olean` を作る。
3. **分散並列証明（複数 worker）**: 土台にのみ依存して互いに独立な定理・補題・具体例ファイルを、新規・履歴なし（`fork_turns: "none"`）の複数 worker へ担当が重ならないように配分し、`sorry` を証明で埋める。
   - worker は担当ファイルだけ編集し、`lake build` 禁止（`lake env lean <file>` のみ）、statement 変更禁止、`sorry` / 禁止構文ゼロ、[performance.md](references/performance.md) の原則に従う。
   - statement 変更や大幅な heartbeat 引き上げが必要になった場合、worker は勝手に変えず親へ返す。親は一次仕様と全体スケルトンの整合を確認し、下流へ波及する修正は設計ブランチ側も更新する（一次仕様の矛盾なら `PRD 欠陥` で止まる）。
   - 依存が多段なら、親が前段を `lake build` してから次段の worker を起動する。
4. **統合・ローカル検証（親）**: 親が成果を統合し、入口ファイル・公理監査ファイル（対象 PRD にある場合）を更新した上で、次をすべて通す。
   - 対象モジュール `lake build`、`sorry` / `native_decide` / `skipKernelTC` 0 件
   - [performance.md](references/performance.md) の性能確認（計測結果を PR 本文に含める）
   - PRD と CI workflow が定めるローカル実行可能な機械チェック
   - `Workflow guideline`・`refutation-checklist` §6 の共通確認
5. **PR・4 lane 査読・CI・マージ**:
   - `.github/pull_request_template.md` と `Lean 品質基準`（対応表・material premise 三分類・性能結果・使用モデル名）を満たして PR を作成し、CI 完走を待たずに `$review-pr <PR>` を起動する。`$math-lean-review`（独立 4 lane）へ委譲されたことを確認し、未委譲・実行不能なら `Blocked / cannot determine` とする。
   - 指摘が出たら `review-protocol` に沿ってまとめて直し、手順 2.4 を再実行する（1 PR あたり正式 4 lane 再実行は初回 + 本筋修正後 2 回まで）。
   - 独立トラックがある場合、前 PR のレビュー・CI 待ちの裏で次トラックの実装を別ブランチで先行してよい（共有ファイルの競合を避け、マージは `main` へ 1 本ずつ追従して行う）。
   - `$review-pr` の `Mergeable`（または条件を満たす直接対応で全指摘解消）、`gh pr checks <PR>` の全 CI green（失敗は `Needs changes` として直す）、PR への監査コメント投稿済み、の 3 条件が揃ったら `gh pr merge <PR> --merge --delete-branch` でマージする。
6. **同期と性能振り返り**: `git switch main && git pull --ff-only` で同期し、tracking Issue を更新する。節目や CI 時間悪化時は [performance.md](references/performance.md) の点検を行い、改善不能なら `性能予算超過` で止まる。`max-iterations` 未達なら次へ進む。

### 3. Phase 3: 最終完了レビュー（独立 4 lane）と完了処理

1. 未着手・未達・blocked・stalled がすべて無くなったら、ローカル設計ブランチを削除し、`main` に `sorry` が無いことを確認する。
2. `$prd-completion-review <PRD パス>` を独立 4 lane で実行する（checklist のチェック状態や親の見込みは渡さない）。
3. `達成済み` なら結果を tracking Issue にコメントし、`PRD guideline` に従って PRD 削除と tracking Issue クローズを行う。`未達あり` / `未確認あり` なら指摘を Issue 化して Phase 2 に戻る（修正後は新 commit で 4 lane 再実行）。`PRD 欠陥あり` なら `PRD 欠陥` で止まる。

## 停止条件

```text
完了:             全 AC 充足かつ `$prd-completion-review`（4 lane）が `達成済み`。
全 blocked:       未達項目がすべて blocked / stalled で次へ進めない。
stall:            同じ Wave / マイルストーンが 5 周連続でマージできない。
性能予算超過:     elaboration 時間・heartbeat・CI 時間の悪化が局所修正で解消しない。
PRD 欠陥:         PRD の矛盾、実装不能、または固定 statement の変更が必要。
budget:           指定された `max-iterations` に達した。
final review gap: `$prd-completion-review` が未達 / 未確認を返し、この実行では次へ進めない。
```

## 終了時の報告

終了理由、AC・Wave スコアボード、性能サマリ（重いファイル・`maxHeartbeats` 件数・直近 CI 時間）、最終完了レビュー結果、周回ログ、マージ済み PR と最新 `main` commit、人間判断事項と次回再開点を報告する。
