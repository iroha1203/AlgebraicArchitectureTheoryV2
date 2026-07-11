---
name: prd-completion-review
description: PRD全文から達成条件・拘束条件・must-not-remainを抽出し、一次証拠と独立査読で現状の完了可否を判定する。"$prd-completion-review path/to/prd.md"、PRD達成条件レビュー、prd-loopの最終確認で使う。実装・Issue作成・PR作成は行わない。完了まで実装する依頼にはprd-loopを使う。
---

# PRD Completion Review

PRD の達成条件を、実装作業に進まずレビューする。

## 必須契約

`.codex/skills/_shared/review-protocol.md`、
`.codex/skills/_shared/refutation-checklist.md`を読み、
非編集・独立査読・fail-closed・一次証拠・報告形式を適用する。
Lean要件を含むPRDでは
`.codex/skills/_shared/lean-refutation-checklist.md`も読む。

## 基本方針

- レビュー姿勢を取る。PRD が要求する concrete condition を満たしているかを項目単位で確認する。
- **アウトカム判定を AC scoreboard から独立させる。** PRD 冒頭の「## 問い」に
  現状が答えているかを、AC の充足とは別の判定項目として出す。AC 全充足でも
  問いが未回答なら総合判定を `達成済み` にしない(ユーザー判断事項として報告する)。
- PRD の達成条件を勝手に縮めない、広げない。現実コード全体、意味宇宙全体、未来予測全体のような無制限 claim を残タスク化しない。
- AAT / Lean / ArchSig / FieldSig / Website / docs の責務を分ける。AAT の完了判定に source extraction や tooling validation の完全性を持ち込まない。
- 判定は証拠ベースにする。該当ファイル、テスト、CI、Issue / PR、台帳、生成物が確認できない項目は `未確認` または `未達` として扱う。
- 証拠には階層を置く。一次証拠は、コード・Lean 宣言の statement 実読、instance の実在確認、実行した検証、kernel 検査。二次証拠は、台帳、inventory、tracking Issue の checklist、Issue / PR 本文、iteration コメントなど、レビュー対象の作業自身が生成した記録。`満たした` 判定は一次証拠でのみ行う。二次証拠は主張の索引として使い、単独では判定根拠にしない。
- 対象 PRD がループ(prd-loop 等)で実装された場合、台帳・checklist・closure 記録はそのループの出力であり、監査対象であって証拠ではない。checklist が check 済みであることは「主張がある」ことしか意味しない。
- 公開物に入る可能性がある code、fixture、docs、schema catalog、website、release asset、tool output contract に、個人名、ローカル絶対パス、private/internal 風の fixture 値、作業環境固有名が混入している場合は、PRD 条件が他に満たされていても重要 finding として扱う。

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
   - Acceptance Criteria に加えて、PRD の採否規律・中心方針・非主張(claim scope)から
     拘束条件を抽出し、別リストとして保持する。特に、処置の降格が許される対象
     (等級リスト等)、anti-weakening、停止規律。
   - AC の文言が字義的に満たされていても、拘束条件に反する充足
     (許可外の降格、記載のみの完了)は `未達` とする。
   - **requirement matrix を作る。** AC だけでなく、PRD の `改修`(R 番号)、
     `Implementation Plan`、`Failure Contract`、`Changed / Removed Fields` を抽出し、
     各 AC がどの R / PR 区分に依存するかの対応表にする。これは AC を置き換える
     合否基準ではない(R 群を独立の合否条件へ昇格させてスコープを広げない)。
     用途は 2 つ: (i) AC 充足の証拠を探す索引、(ii) 見落とし検出 —
     どの周回・どの PR にも接続していない R 群(実装計画の丸ごと欠落)が、
     依存する AC の充足を空洞化していないかを確認し、空洞化していれば該当 AC を `未達` とする。
   - **must-not-remain リストを作る。** PRD の `現状診断` が解消対象として名指しした
     旧構造・旧挙動・旧文言(型、フィールド、fail-fast 挙動、hardcode、docs 記述)を
     1 項目 1 行で抽出する。PRD が明示的に「別 PRD の管轄」「既知の残置」とした項目は
     除外し、除外理由を併記する。
   - 親 Codex が条件リストと拘束条件リストを確定し、sub-agent には両方をレビュー対象として渡す。
     ただし親リストは単一障害点になりうるため、手順4の独立抽出レーンで検算する。

3. 証拠を集める。
   - `rg` と対象ディレクトリの読み取りで、各達成条件に対応するコード、Lean 定理、schema、fixtures、tests、docs、website surface を確認する。
   - 台帳・checklist・inventory の記載は宣言単位でコードと突合する。全数を
     確認できない範囲はsamplingだけで充足扱いせず、coverage不足として`未確認`にする。
   - 記載と実体の不一致が1件でも見つかった場合、その文書は証拠から外し、
     対象範囲の突合を全数に切り替える。
   - **must-not-remain 検査(anti-regression gate)。** must-not-remain リストの各項目を
     `rg` と実読で再検査する。PRD が解消を宣言した旧構造・旧挙動が残存している場合、
     テストや CI が green でも、対応する条件を `未達` とする。残存の検出には、
     旧挙動を「正」として固定し続けている既存テストの発見を含める。
   - **テストは assertion 内容で証拠にする。** テストを `満たした` の根拠にする場合、
     テスト名ではなく assertion の内容(何を入力し、何を断言しているか)を実読して記録する。
     条件文言と assertion 内容の対応が取れないテスト(似た名前・隣接領域のテスト)は
     証拠にしない。
   - PRD が GitHub 状態を要求する場合は、関連 Issue / PR / CI / merge 状態を確認する。
   - PRD が検証コマンドを指定している場合は実行する。指定がなければ変更領域に応じて最小限の検証を選ぶ。
   - 実行できない検証は、理由と判定への影響を明記する。

4. subagentで複数観点レビューを行う。
   - [references/reviewer-lanes.md](references/reviewer-lanes.md)の横断4観点と
     独立抽出laneを、共有契約どおり利用可能枠まで並行する。
   - 条件数ではなくcoverageで判断し、横断laneだけでは一次証拠を実読できない
     条件群ごとに深掘りlaneを追加する。

5. 親 Codex が統合判定する。
   - sub-agent の指摘を PRD 条件単位に統合する。
   - 重複、矛盾、過剰 claim、PRD 外要求を整理する。
   - 各条件を `満たした`, `未達`, `未確認`, `PRD欠陥`, `範囲外` に分類する。

## Lean 反証チェックリスト

昇格・証明・発火を主張する条件では、statement を実読して反証を試みる。
台帳のstatus記載は根拠にしない。Lean固有項目は
`.codex/skills/_shared/lean-refutation-checklist.md` §1–§3、scope資格・帰属は
`.codex/skills/_shared/refutation-checklist.md` §4–§5を正本として適用する。

## 判定基準

- `満たした`: PRD 条件に対応する実体と検証結果が一次証拠で確認できる。
- `未達`: 条件が要求する実体、挙動、docs、test、CI、GitHub 状態が不足している。
  拘束条件に反する充足(許可外の降格、記載のみの完了)もここに入れる。
- `未確認`: 必要な証拠にアクセスできない、検証が未実行、または環境制約で確認不能。
- `PRD欠陥`: 条件が矛盾、曖昧すぎる、または実装対象として成立しない。
- `範囲外`: PRD の Non-goals / Scope により判定対象ではない。

## 検証の選び方

- Lean 変更または Lean 達成条件: `lake build`、必要なら focused `lake env lean <file>`
- ArchSig 変更または tooling 達成条件: `cargo test --manifest-path tools/archsig/Cargo.toml`
- FieldSig 変更または measurement handoff 達成条件: `cargo test --manifest-path tools/fieldsig/Cargo.toml`
- Website 達成条件: local static preview、link / asset / title / layout check
- 共通scanは `.codex/skills/_shared/refutation-checklist.md` §6 を実行する。

PRD がこれより狭い検証を指定している場合は、PRD 指定を優先する。PRD が要求していない広範な検証を、未達条件として扱わない。

## 報告形式

共有契約と[references/reviewer-lanes.md](references/reviewer-lanes.md)の
報告schemaに従う。

**監査コメントの投稿義務**: prd-loop の最終達成条件レビューとして実行された
場合、監査結果を tracking Issue へコメント投稿する(投稿は本 SKILL の
義務であり、外部の記録転記に依存しない)。単独起動の場合も、
対象 PRD に tracking Issue があれば同様に投稿する。
