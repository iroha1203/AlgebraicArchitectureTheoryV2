---
name: prd-completion-review
description: PRD の Acceptance Criteria / 達成条件が現状で満たされているかを実装せず敵対レビューする。"$prd-completion-review path/to/prd.md"、"PRD達成条件レビュー"、PRD 完了確認の依頼で使う。
---

# PRD Completion Review

PRD の達成条件を、実装作業に進まずレビューする。このリポジトリでは、ユーザーへの報告は日本語で行う。

## 敵対レビュー原則

これは**敵対レビュー**である。目的は PRD を完了扱いにすることではなく、
完了主張を落とす根拠を探すこと。レビュワーの成果は反証の試行記録であり、
チェックリストの消化ではない。承認(`達成済み`)は反証の失敗としてのみ
与える。反証の手がかりの正本は
`.codex/skills/_shared/refutation-checklist.md` であり、各レーンは項目を
複製せず参照する。finding ゼロの報告には資格条件(反証試行3件の明記)が
課される(同 reference §7)。

## 基本方針

- レビュー姿勢を取る。PRD が要求する concrete condition を満たしているかを項目単位で確認する。
- **アウトカム判定を AC scoreboard から独立させる。** PRD 冒頭の「## 問い」に
  現状が答えているかを、AC の充足とは別の判定項目として出す。AC 全充足でも
  問いが未回答なら総合判定を `達成済み` にしない(ユーザー判断事項として報告する)。
- PRD の達成条件を勝手に縮めない、広げない。現実コード全体、意味宇宙全体、未来予測全体のような無制限 claim を残タスク化しない。
- 実装、Issue 作成、PR 作成、PRD 編集はしない。ユーザーが明示した場合だけ次作業を提案または実行する。
- AAT / Lean / ArchSig / FieldSig / Website / docs の責務境界を分ける。AAT の完了判定に source extraction や tooling validation の完全性を持ち込まない。
- 既存の未コミット変更はユーザー変更として扱い、勝手に戻さない。破壊的操作をしない。
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
   - Acceptance Criteria に加えて、PRD の採否規律・中心方針・非主張(claim boundary)から
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
   - 台帳・checklist・inventory の記載は宣言単位でコードと突合する。全数が困難な場合は
     部・セクションごとに最低3件、完了主張が強い行(昇格・発火・実装済み)を優先して
     サンプル突合する。
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

4. サブエージェントで複数観点レビューを行う。
   - 下の 4 観点を**必ず**並列 sub-agent に分ける。sub-agent が起動できない
     場合、親 Codex が代替実行してはならない(fail-closed)。総合判定を
     `Blocked / cannot determine` 相当(`未確認あり`)に落とし、
     `達成済み` を出さない。
   - **独立抽出レーンを 1 つ立てる。** 4 観点とは別に、親の条件リスト・拘束条件リスト・
     requirement matrix を一切渡さず、PRD 全文だけから達成条件・拘束条件・must-not-remain を
     独立に抽出させる sub-agent を実行する。親リストとの差分(親が落とした条件、
     粒度の粗い写し、拘束の欠落)を finding として返させ、差分があれば親はリストを
     更新してから手順5の統合判定を行う。親が条件を落とすと全観点レーンが同じ穴に落ちるため、
     このレーンも省略しない(起動できなければ同様に fail-closed)。
   - 条件数が多い場合(目安: AC が 10 を超える、または対象が複数部・複数領域にまたがる)、
     横断4観点だけで全条件を薄く覆う分割をしない。部・条件群単位の深掘りレーンを立て、
     各レーンに担当条件の一次証拠の実読(structure / theorem statement)を必須として課す。
   - sub-agent には PRD パス、親が抽出した条件リストと拘束条件リスト、担当観点、対象範囲、必要な raw context、出力形式だけを渡す。親の推測や期待 finding は渡さない。tracking Issue の checklist の check 状態を完了根拠として渡さない。

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
   - **帰属の実在(theoremRef 検査)**: コード・fixture・出力 artifact・docs が数学本文へ
     帰属する参照(theoremRef、部・定理・補題番号)を持つ場合、参照先の部に該当番号の
     定理が実在し、主張の方向(肯定 / 否定、対偶)が本文・設計正本の写像と一致することを
     本文で確認する。存在しない定理番号への帰属、番号の入れ替わりは、テストが green でも
     重要 finding として扱う。
   - public / release surface にセンシティブな path、個人環境名、private/internal 風 fixture、repo-local docs path が runtime output として混入していないか確認する。

## Lean 反証チェックリスト

昇格・証明・発火を主張する条件では、statement を実読して反証を試みる。
台帳の status 記載は根拠にしない。**チェックリストの正本は
`.codex/skills/_shared/refutation-checklist.md`** であり、基底6項目
(結論射影 / True 充足 / instance 実在 / 非退化発火 / 公理 /
anti-weakening)に加えて次を必ず適用する。

- 意味レベルの空虚化(同 reference §2): subsingleton 等式型、
  proof-irrelevance 恒真、answer-encoding、装飾的係数、恒真フィールド、
  instance ペアの欠如。
- 移植元 conjunct 対応(同 §3): 蒸留・移植を含む条件では「疑いがある場合」
  ではなく**必須**で実施し、Research 側受理 theorem を下限として照合する。
- no-go 適用範囲(同 §4): 境界記載を含む条件では資格条件を検証する。
- 帰属・ロック値・監査カバレッジ(同 §5)。

## Sub-Agent Prompt

```text
Use the prd-completion-review skill context. Review only the assigned perspective.
You are an adversarial referee: you are called to find grounds for rejecting
the completion claim, not to confirm it. Read
.codex/skills/_shared/refutation-checklist.md and use it as refutation leads.
When you report no findings for your perspective, record at least 3
refutation attempts and the evidence that defeated each.
PRD: <path>
Criteria list: <parent-extracted criteria IDs and short text>
Binding constraints: <parent-extracted 採否規律 / 中心方針 / 非主張 constraints>
Must-not-remain list: <parent-extracted 現状診断の旧構造・旧挙動、除外項目と理由>
Perspective: <要件充足レビュー | 欠落・反例レビュー | 検証再現性レビュー | 境界・状態整合性レビュー | 部・条件群深掘りレビュー>
Scope: <all criteria or selected criteria>
Evidence rule: `満たした` requires first-order evidence (code / Lean statement / executed check).
When a test is cited as evidence, read and record what it asserts; do not accept test names.
Ledger, inventory, tracking checklist, and Issue/PR text are claims under audit, not evidence.

Report in Japanese:
1. Findings or concerns, ordered by severity.
2. PRD criteria checked.
3. Evidence checked, with file/line, command, PR, Issue, or CI references when available.
4. Criteria status suggestions: 満たした / 未達 / 未確認 / PRD欠陥 / 範囲外.
5. Coverage limits.

Do not edit files. Do not implement fixes. Stay anchored in the assigned perspective and the PRD text.
Do not re-scope or replace the parent-extracted criteria list. If the list itself appears wrong, report it as a review finding.
```

独立抽出レーンには、上のプロンプトから Criteria list / Binding constraints / Must-not-remain list を
渡さず、次だけを渡す。

```text
Use the prd-completion-review skill context. Perspective: 独立抽出レーン.
PRD: <path>
Task: Extract, from the PRD full text alone, (1) 達成条件 (2) 拘束条件(採否規律・中心方針・非主張)
(3) must-not-remain(現状診断の旧構造・旧挙動、except items the PRD explicitly leaves to another PRD).
Report in Japanese as three numbered lists. Do not read the tracking Issue or parent notes.
```

親は独立抽出レーンの結果を自分のリストと突合し、差分を解消してから統合判定する。

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
- 共通: `git diff --check`
- 共通 hidden / bidi scan: `rg -nP "[\x{200B}-\x{200F}\x{202A}-\x{202E}\x{2066}-\x{2069}]" <changed-files>`
- 共通 privacy / local-path scan: public / release surface と changed files に対して `rg -n "(\\/Users\\/|\\/home\\/|C:\\\\Users\\\\|Documents\\/|HelloLean|nakahata|private\\/internal|\\/private\\/internal|\\.codex|AlgebraicArchitectureTheoryV2)" <changed-files>` を目安に確認する。Tooling output contract では repo-local docs path を安定 ID に置き換える必要がないかも見る。

PRD がこれより狭い検証を指定している場合は、PRD 指定を優先する。PRD が要求していない広範な検証を、未達条件として扱わない。

## 報告形式

終了時は次の順で簡潔に報告する。

1. 総合判定: `達成済み`, `未達あり`, `未確認あり`, `PRD欠陥あり`, `範囲限定レビュー`
2. **アウトカム判定**: PRD の「## 問い」に現状が答えているか。
   AC scoreboard とは独立に判定し、根拠を書く
3. Scoreboard: `満たした / 未達 / 未確認 / PRD欠陥 / 範囲外` の件数
4. 条件別レビュー表: 条件 ID、PRD 文言の要約、判定、根拠、残リスク
5. Findings: 重大度順。未達・PRD欠陥・重要な未確認を先に出す。
   finding ゼロの観点は反証試行3件以上を明記する
6. 実行した検証: コマンドと結果
7. Coverage limits: 読んだ範囲、未確認範囲、実行できなかった検証
8. 次アクション案: 実装 Issue 化、PRD 修正相談、追加検証などの提案に留める

**監査コメントの投稿義務**: prd-loop の最終達成条件レビューとして実行された
場合、上記 1〜7 を tracking Issue へコメント投稿する(投稿は本 SKILL の
義務であり、外部の記録転記に依存しない)。単独起動の場合も、
対象 PRD に tracking Issue があれば同様に投稿する。
