---
name: prd-completion-review
description: PRD を入力に、その Acceptance Criteria / 達成条件が現状の実装・docs・tests・GitHub 状態で満たされているかをレビューする。Use when the user says "$prd-completion-review path/to/prd.md", "PRD達成条件レビュー", "このPRDが達成済みか確認して", or asks Codex to audit PRD completion without implementing fixes. This skill uses subagents for multiple review perspectives when available.
---

# PRD Completion Review

PRD の達成条件を、実装作業に進まずレビューする。このリポジトリでは、ユーザーへの報告は日本語で行う。

## 基本方針

- レビュー姿勢を取る。PRD が要求する concrete condition を満たしているかを項目単位で確認する。
- PRD の達成条件を勝手に縮めない、広げない。現実コード全体、意味宇宙全体、未来予測全体のような無制限 claim を残タスク化しない。
- 実装、Issue 作成、PR 作成、PRD 編集はしない。ユーザーが明示した場合だけ次作業を提案または実行する。
- AAT / Lean / ArchSig / FieldSig / Website / docs の責務境界を分ける。AAT の完了判定に source extraction や tooling validation の完全性を持ち込まない。
- 既存の未コミット変更はユーザー変更として扱い、勝手に戻さない。破壊的操作をしない。
- 判定は証拠ベースにする。該当ファイル、テスト、CI、Issue / PR、台帳、生成物が確認できない項目は `未確認` または `未達` として扱う。

## 入力

- PRD ファイルパスは必須。見つからない場合だけ短く確認する。
- 任意で、対象範囲を限定できる。例: `AC1-AC4 のみ`, `Lean surface だけ`, `PR #123 マージ後の状態で確認`。
- ユーザーが PR 番号や Issue 番号を添えた場合は、それらを証拠候補として読む。ただし PRD 本文を主基準にする。

## 標準手順

1. 前提を確認する。
   - `git status --short --branch`
   - PRD ファイル全体
   - PRD の Acceptance Criteria / 達成条件 / 完了条件 / Non-goals / Scope
   - 関連する Issue / PR / tracking checklist が明示されている場合はそれら

2. 達成条件を抽出する。
   - PRD の文言を 1 条件 1 行に分解する。
   - 条件 ID がある場合は保持する。ない場合は `AC1`, `AC2` のように仮番号を付ける。
   - `must`, `should`, `acceptance test`, `done`, `out of scope` を区別する。
   - PRD 本文自体の記述要件と、実装・テスト・docs・CI で検証すべき要件を分ける。
   - 親 Codex が条件リストを確定し、sub-agent にはこの条件リストをレビュー対象として渡す。

3. 証拠を集める。
   - `rg` と対象ディレクトリの読み取りで、各達成条件に対応するコード、Lean 定理、schema、fixtures、tests、docs、website surface を確認する。
   - PRD が GitHub 状態を要求する場合は、関連 Issue / PR / CI / merge 状態を確認する。
   - PRD が検証コマンドを指定している場合は実行する。指定がなければ変更領域に応じて最小限の検証を選ぶ。
   - 実行できない検証は、理由と判定への影響を明記する。

4. サブエージェントで複数観点レビューを行う。
   - multi-agent tool が使える場合は、原則として下の 4 観点を並列 sub-agent に分ける。
   - 使えない場合は、親 Codex が同じ 4 観点を順番に実行する。
   - sub-agent には PRD パス、親が抽出した条件リスト、担当観点、対象範囲、必要な raw context、出力形式だけを渡す。親の推測や期待 finding は渡さない。

5. 親 Codex が統合判定する。
   - sub-agent の指摘を PRD 条件単位に統合する。
   - 重複、矛盾、過剰 claim、PRD 外要求を整理する。
   - 各条件を `満たした`, `未達`, `未確認`, `PRD欠陥`, `範囲外` に分類する。

## Review Perspectives

sub-agent を使う場合は、親 Codex が抽出した同じ達成条件リストに対して、次のレビュー観点を分担する。

1. **要件充足レビュー**
   - 各条件に対して、提示された実装・docs・台帳の根拠が PRD 文言を直接満たしているかを確認する。
   - 似た概念の存在、部分実装、名前だけの対応を `満たした` と誤判定していないかを疑う。

2. **欠落・反例レビュー**
   - 条件を満たさない edge case、未接続の surface、docs drift、fixture 不足、negative path 不足を探す。
   - ある条件の達成が別条件や未確認前提に依存していないかを確認する。

3. **検証再現性レビュー**
   - PRD 指定の acceptance tests、ローカル検証、CI、GitHub PR / Issue 状態が条件の証拠として十分か確認する。
   - 検証コマンドが対象条件を実際に覆っているか、green でも未検証領域が残っていないかを確認する。

4. **境界・状態整合性レビュー**
   - PRD 外の巨大 claim を持ち込んでいないか、AAT / Lean / tooling / website の責務境界を混同していないか確認する。
   - Lean status、proof obligation、Issue / PR checklist、docs の完了主張が実体と矛盾していないか確認する。

## Sub-Agent Prompt

```text
Use the prd-completion-review skill context. Review only the assigned perspective.
PRD: <path>
Criteria list: <parent-extracted criteria IDs and short text>
Perspective: <要件充足レビュー | 欠落・反例レビュー | 検証再現性レビュー | 境界・状態整合性レビュー>
Scope: <all criteria or selected criteria>

Report in Japanese:
1. Findings or concerns, ordered by severity.
2. PRD criteria checked.
3. Evidence checked, with file/line, command, PR, Issue, or CI references when available.
4. Criteria status suggestions: 満たした / 未達 / 未確認 / PRD欠陥 / 範囲外.
5. Coverage limits.

Do not edit files. Do not implement fixes. Stay anchored in the assigned perspective and the PRD text.
Do not re-scope or replace the parent-extracted criteria list. If the list itself appears wrong, report it as a review finding.
```

## 判定基準

- `満たした`: PRD 条件に対応する実体と検証結果が確認できる。
- `未達`: 条件が要求する実体、挙動、docs、test、CI、GitHub 状態が不足している。
- `未確認`: 必要な証拠にアクセスできない、検証が未実行、または環境制約で確認不能。
- `PRD欠陥`: 条件が矛盾、曖昧すぎる、または実装対象として成立しない。
- `範囲外`: PRD の Non-goals / Scope により判定対象ではない。

## 検証の選び方

- Lean 変更または Lean 達成条件: `lake build`、必要なら focused `lake env lean <file>`
- ArchSig 変更または tooling 達成条件: `cargo test --manifest-path tools/archsig/Cargo.toml`
- FieldSig 変更または measurement handoff 達成条件: `cargo test --manifest-path tools/fieldsig/Cargo.toml`
- Website 達成条件: local static preview、link / asset / title / layout check
- 共通: `git diff --check`
- 共通 hidden / bidi scan: `rg -nP "[\x{200B}-\x{200F}\x{202A}-\x{202E}\x{2066}-\x{2069}]" <changed-files>`

PRD がこれより狭い検証を指定している場合は、PRD 指定を優先する。PRD が要求していない広範な検証を、未達条件として扱わない。

## 報告形式

終了時は次の順で簡潔に報告する。

1. 総合判定: `達成済み`, `未達あり`, `未確認あり`, `PRD欠陥あり`, `範囲限定レビュー`
2. Scoreboard: `満たした / 未達 / 未確認 / PRD欠陥 / 範囲外` の件数
3. 条件別レビュー表: 条件 ID、PRD 文言の要約、判定、根拠、残リスク
4. Findings: 重大度順。未達・PRD欠陥・重要な未確認を先に出す
5. 実行した検証: コマンドと結果
6. Coverage limits: 読んだ範囲、未確認範囲、実行できなかった検証
7. 次アクション案: 実装 Issue 化、PRD 修正相談、追加検証など。ただしユーザーが依頼するまで実行しない
