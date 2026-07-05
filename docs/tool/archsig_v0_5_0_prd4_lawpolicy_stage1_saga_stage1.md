# ArchSig v0.5.0 PRD-4 — LawPolicy Stage 1 と SAGA Stage 1(最初の SAGA 計測)

対象は制度選択層の新形(law-policy 新形 + measurement-profile の独立 artifact 化 = LawPolicy 案4 の
Stage 1)と、SAGA 定理(第X部)の最初の現場計測(`archsig-repair-plan` + `ag.saga-descent` の
complete-support regime + `ag.cech-obstruction` 新形)。ロードマップ P7〜P8、v0.5.0 PRD 5 本の第 4 弾。
**前提: PRD-1〜3 の実装が受け入れ済みであること**(単一契約版数 / conclusionCode registry /
gate の boundaryKindOverrides / v1 語彙の不在)。

関連(設計の正本):

- [ArchSig v0.5.0 再設計ノート](../note/archsig_v0_5_0_redesign_note.md) — §3(SAGA 診断の階段)、
  §4(LawPolicy 案4 + 発展追随の拡張規律)、§8 裁定3(law-equation は law surface へ — Stage 2)・
  裁定4(repair-plan 統一)・裁定6(registry)・裁定10(互換ゼロ)
- [design_ag-measurement](../note/archsig_v0_5_0/design_ag-measurement.md) — §3.1(repair-plan)、
  §3.3.1(saga-descent)、§3.5(実行機構 3 条件)、§3.6 A1/A2、§3.8(翻訳規律)、§3.9(fixture)
- [design_lawpolicy](../note/archsig_v0_5_0/design_lawpolicy.md) — §3.4 案4(a)(c)、§6 Stage 1
- AAT 本文: 第X部 §1-§3(supplied / generated、descent 定理 3.4 / 3.5、例 2.6 / 3.6)、
  第IV部 §12(系12.3 / 定理12.4)、第VIII部(verdict discipline、定理5.2、原則5.3)

## 問い

**SAGA の supplied / generated 規律を artifact contract として実装できるか —
供給されたものだけを仮定し、生成されるものを入力から受け取らないか。**

第X部 §1「定理の結論に現れる構造を supplied certificate として受け取らない」を採否の判定規律にする。

- **(採用条件 — supplied 側)** 供給されるデータは、(i) 適合条件を**検査してから**使う
  (restriction-difference rule、δ¹∘δ⁰ = 0、complete-support の cross-field 検査、参照整合)、
  (ii) 検査で落とせないもの(列挙の完全性等)は assumption ledger に `assumed_by: author` で記録する
  (境界の一括払い)、(iii) 結論相当フィールドを持たない(anti-weakening hard error)。
  P7 も同じ問いの下にある: finiteBounds の profile 昇格は実装定数の supplied 化、
  basisLedger は evidence contract の宣言化である。
- **(採用条件 — generated 側)** 結論 token の発火条件は**定理の前提の検査**に束縛する。
  肯定的 descent は faithfulness 基盤(complete-support 宣言 = 定理3.5 regime)があるときだけ、
  `COVER_SHAPE_EXCLUDES_GLUING_OBSTRUCTION` は定理12.4 の 3 前提すべてが discharged_by_check の
  ときだけ。前提が欠けるときは `unmeasured` + boundary statement(沈黙)であり、エラーでも
  残タスクでもない。
- **(却下条件)** 前提を検査せずに結論を出す変更、結論相当フィールドを入力 schema に足す変更、
  faithfulness なしの肯定的 descent、law surface 本体の先取り(Stage 2 = 0.5.x)、
  互換機構の追加(裁定10)は、たとえ有益でも却下する。

## Core Thesis

理論側は 2026-07-03 に SAGA 全連鎖が Lean proved になったが、第X部に対応する計測は 1 つもない。
「repair が貼り合うか」は PR review・AI 生成パッチの検収で最も需要のある問いである。

Stage 1 は診断の階段の最初の 2 段を立てる:

```text
(A) 観測 archmap                        → residual 生値(既存 cech の新形が concrete に)
(B) + repair-plan(供給・検査済み)      → r ∈ B¹ の境界所属
    r ∉ B¹  ⇒ 貼り合わない             【無条件。定理3.4(i) の対偶】
    r ∈ B¹ ∧ complete-support 宣言     ⇒ 貼り合う【定理3.5: faithfulness が定理として成立】
```

この非対称 — **否定は無条件、肯定は宣言された regime の内側** — を出力語彙にそのまま写す。
層 C(additive H¹ の class)・層 D(比較)・層 E(law-equation)は 0.5.x の Stage 2 以降であり、
本 PRD では**商が構成されない段に class の語を使わない**(第X部 定義3.2 の語彙規律)。

## Design Principles

1. **supplied / generated の分界は schema で**: 供給欄(residual / complex / primitives /
   faithfulness 宣言)と生成物(境界所属・closure 診断・verdict)を別 artifact に置き、
   入力側に結論語 hard error(`check_repair_plan_no_conclusion_tokens`、archmap R3 と同型)。
2. **予約フィールドは fail-closed**: Stage 2 以降の欄(`lawSurfaceRef` / `policies[].profileRef` /
   repair-plan の `trueSheafCertificate` / `gluingData` / `comparison` / `grounding` /
   `faithfulness.mode: "supplied"`)は schema に定義するが、書かれたら「未対応の宣言」として
   明示エラーで fail する。黙って無視しない(暗黙の入力欠落・暗黙の受理をどちらも作らない)。
3. **二 run 構成が正式経路**: measured residual は前回 packet への参照(`--residual-packet`)で pin する。
   law-policy は run あたり単一 profile のまま(`policies[].profileRef` は予約のみ。
   単一 run 化は 0.5.x)。
4. **claim 境界**: 結論はすべて「選ばれた複体 / cover / 宣言された regime の内側」。repair synthesis・
   最小修復・extraction completeness は主張しない。hitting set の表示には第VIII部 原則5.3
   (組合せ的 repair target であって repair semantics ではない)を併記する。
5. **Rust / Lean 非対応**: fixture の数値ロックと Lean 構造体の語彙借用は便宜であり contract ではない。
   proved の帰属は witness の形ごとに書き分ける(circle nerve の Lean witness は 3 辺形)。
6. **モジュール規律**: SAGA ファミリは新モジュール(例 `src/ag/saga.rs`)に置き、
   既存 dispatch の if-else 連鎖に乗せない。

## 改修(本体)

### P7 群 — LawPolicy Stage 1(案4 の土台。方程式はまだ動かさない)

- **R1(law-policy 新形)** `basisLedger` 新設: `{ basisId, kind: repo-document | external-standard |
  registry, path, revision }`。`policies[].basis` は台帳内 `basisId` への解決必須(未解決は
  validation fail)。ArchSig が検査するのは台帳内解決のみで、**文書内容の意味検証・path 実在検査は
  しない**(evidence contract の宣言主義。`--check-basis-paths` は導入しない — 未決事項を「検査しない」で
  閉じる)。`lawSurfaceRef` と `policies[].profileRef` を予約フィールドとして定義(書かれたら fail-closed)。
- **R2(measurement-profile の独立 artifact 化)** 埋め込み `measurementProfiles[]` を廃止し、
  `--measurement-profile` で渡す独立ファイル + `measurementProfileRef` の id 一致検査に対称化する。
  profile schema に `finiteBounds` を昇格: 実装定数 7 種(MAX_SQUARE_FREE_WITNESS_VARIABLES 12 /
  MAX_COHERENCE_CONTEXTS 12 / MAX_TOR_WITNESS_VARIABLES 12 / MAX_BOUNDARY_RESIDUE_VARIABLES 16 /
  MAX_LAPLACIAN_CELLS 16 / MAX_PERIOD_CYCLES 16 / MAX_TRANSFER_TARGETS 16)と 1 対 1 の対応表で全数定義。
  **registry 所有の hard cap(現行定数値)を validation で強制し、profile は cap 以下への引き下げのみ
  宣言可**(`all_subsets` の 2^n 実体化があるため上限は資源制約であり author の自由ではない)。
  `witnessFamily` は現行のまま profile に残す(law surface への移設は Stage 2)。
  各フィールドと第VIII部 定義2.1 / 定義4.1 の対応表を docs/tool/law_policy.md 改訂版に置く。
- **R3(CLI の対称化、意図的 breaking)** `law-policy` サブコマンドの `--input` → `--law-policy` 改名、
  `analyze` / `law-policy` への `--measurement-profile` 追加、`measurement-profile` 単独検証
  サブコマンド新設。commands.md / README / law-policy-creater を同一 PR で改訂(裁定10:
  旧形の受理・変換・バックフィルはしない。law-policy-creater は新形の新規作成のみ)。
- **R4(catalog / fixture)** schema catalog への登録と lock fixture 更新。既存 AG fixture の
  law-policy / profile を新形に書き換える(旧形 fixture は残さない)。

### P8 群 — SAGA Stage 1

- **R5(repair-plan artifact)** `archsig-repair-plan/v0.5.0`(schema 全文は design_ag-measurement
  §3.1 が正): `residual`(kind: measured | supplied。measured は packetRef + invariantRef)、
  `complex`(charts / overlaps / tripleOverlaps / enumerationComplete)、`primitives[]`
  (overlap ごとの res_L / res_R と support)、`semanticProjection`(Λ = archmap atoms、
  K = subjects、π = subject-of-atom)、`faithfulness.mode`(Stage 1 の実装は `complete-support` と
  `none`。`supplied` は予約 = fail-closed)、`coefficient: f2-additive`。
  validator(hard error): 参照整合、restriction-difference rule(δ⁰ の supplied 条件、part_10:199)、
  δ¹∘δ⁰ = 0 と δ¹(r) = 0(triple があるとき)、**complete-support cross-field 検査**
  (mode = complete-support ⇒ 全 primitive の support.kind = complete。Lean
  `CompleteSupportBoundaryComplex` の `support_eq` は全 primitive に要求)、
  **measured residual の chart 束縛**(charts は archmap context 参照必須)、
  `deny_unknown_fields` + 結論語 hard error(`h1Zero` / `globalCoherent` / `glues` / `verdict` 等)。
  `enumerationComplete` は検証せず assumption ledger 行にする(`assumed_by: repair-plan author`)。
- **R6(CLI 統合)** `repair-plan` 単独検証サブコマンド(`--residual-packet` で参照解決 + cocycle 検査)、
  `analyze --repair-plan --residual-packet`。policy に `ag.saga-descent` があるのに repair-plan
  不供給のときは行を `not_computed`(reason: `repair_plan_not_supplied`)+ boundary
  `silence_by_design` とする(エラーにしない — 沈黙の手続き化)。
- **R7(`ag.saga-descent`、complete-support regime)** 計算: restriction-difference 検査 →
  supplied primitive 加群上の δ⁰g = r 可解性(F₂ 線形代数)→ 境界所属 → coverage / faithfulness の
  有限集合演算(補題2.5)→ alias witness 列挙(例2.6 / 3.6 型の生値)。
  verdict 行: `saga.residual-boundary-membership`(常時)/ `saga.global-coherence`
  (complete-support 宣言時は measured — 定理3.5 により faithfulness は仮定でなく定理。
  mode = none のときは `unmeasured` + `silence_by_design`「complete-support 宣言または
  faithfulness data〔Stage 2〕の供給で語れる」)。**residual-class 行は立てない**(層 C は語彙の外)。
  invariant: `boundaryMembership { inB1, witnessPrimitiveCombination, residualSupport }`
  (**class の語を使わない**)、`closureDiagnostics { residualComponentCovered,
  residualComponentFaithful, aliasWitnesses[] }`、`faithfulnessBasis`。
  aliasWitnesses は ArchMap 抽出精度(Λ/K 二層を潰さない)への計測フィードバックとして
  PRD-5 の SKILL に渡る(次元間 interface)。
- **R8(`ag.cech-obstruction` 新形)** concrete class 規律(第IV部 原則4.4): 代表 cocycle と
  class support(どの辺)を invariant で出す。`nerveShape { b1, oneSkeletonB1, capacityLowerBound,
  isForest, eulerCharacteristic }`(b1 = 面込み複体の Betti 数、oneSkeletonB1 と区別 — 系12.3 の読み)。
  `COVER_SHAPE_EXCLUDES_GLUING_OBSTRUCTION` の発火条件は定理12.4 の 3 前提
  (isForest ∧ tripleOverlaps 空 ∧ 全 restriction map の全射性検査 pass)を各
  `discharged_by_check` にしたときのみ。結論は選ばれた abelian 係数 sheaf に相対化し、
  non-abelian torsor / stacky descent / gerbe obstruction の非排除を boundary note 1 行で固定。
- **R9(`REPAIR_TARGETS_IDENTIFIED`)** 既存 `ag.square-free-repair` の実装済み invariant
  (`minimalForbiddenSupports` / `alexanderDualRepair.minimalHittingSets`)を参照する summary token の
  追加のみ。**版上げ・フィールドリネームはしない**(既存 fixture・CLI テスト・ArchView 投影を壊す
  利益がない)。一行文に原則5.3 の boundary を併記。
- **R10(翻訳規律の実装)** summary 生成コードに写像規則テーブルを持たせ、テストで固定する:
  (1) 主文は選ばれた profile 内側の肯定形 + theoremRef、
  (2) Stage 1 は law-check 行が存在しないため「law が守られている」文型を emit しない、
  (3) 非零は concrete support で名指す(層 B の invariant / token / summary に `class` 語彙を
  emit しない lint)、
  (4) 沈黙の boundary は「次に何を供給すれば語れるか」を 1 行で示す、
  (5) 「証明する」は theoremRef 付き定理帰属文のみ(tool の一人称は certified detection に留める)。
- **R11(registry / gate 接続)** conclusionCode registry(PRD-2 機構)へ
  `REPAIR_GLUES_WITHIN_SELECTED_COMPLEX` / `MEASURED_NONGLUING_RESIDUAL` /
  `COVER_SHAPE_EXCLUDES_GLUING_OBSTRUCTION` / `REPAIR_TARGETS_IDENTIFIED` を追加。
  `STRUCTURAL_VERDICT_EVALUATORS` へ `ag.saga-descent` を追加。
  SAGA 行(`silence_by_design` 付き非終端)を含む正常系 run が、gate-policy の
  `boundaryKindOverrides` で `pass_with_boundary` になる e2e を固定する。
- **R12(fixture と数値ロック)** proved 帰属を書き分けて lock する:
  (a) 境界所属の正例 / 負例(r ∈ B¹ / r ∉ B¹、complete-support regime — 定理3.4 / 3.5)、
  (b) 例2.6 / 3.6 型 alias 負例(component 水準 covered だが faithful でない →
  not GlobalCoherent。aliasWitnesses が生値で出る)、
  (c) appendix B.8 toy(Atom family → 3 chart → mismatch (1,0,0)、検出汎関数で H¹ 非零 —
  cech 新形の concrete support)、
  (d) I_Ob = ⟨pq, qr⟩ → hitting sets {q}, {p,r}(第VIII部 定理5.2、Lean proved — R9 の token 発火)。
- **R13(repair-plan-creater SKILL、最小形)** complete-support mode 限定の authoring SKILL を新設
  (既存 4 SKILL の書式慣行に従う。読んだ証拠 → 機械検証 → complete-first の型)。
  supplied faithfulness / comparison の authoring は Stage 2 で拡張する。

## Changed / Removed Fields

- **Added**: law-policy の basisLedger + 予約 2 欄、measurement-profile 独立 artifact
  (finiteBounds 込み)、archsig-repair-plan、`ag.saga-descent`、saga 系 conclusionCode 4 種、
  `repair-plan` / `measurement-profile` サブコマンド、repair-plan-creater SKILL。
- **Changed**: `ag.cech-obstruction`(concrete class support + nerveShape + 定理12.4 検査の追加。
  既存 verdict の意味は不変)、law-policy / analyze の CLI 引数(breaking)。
- **Not changed**: archmap の形状(SAGA に必要な観測は既存 v2 語彙の範囲 — semantic atom +
  subject + 生 section 値。alias の保持は authoring 規律であり schema 変更ではない)、
  measurement packet の 6 区画、`ag.square-free-repair` の invariant。

## Failure Contract

- 予約フィールドの使用・complete-support 不整合・結論語入り repair-plan・未解決 basis /
  measurementProfileRef 不一致・finiteBounds の cap 超過は validation fail(明示エラー)。
- repair-plan 不供給・faithfulness 不在は fail ではなく `not_computed` / `unmeasured` +
  `silence_by_design`(gate は boundaryKindOverrides で制度的に扱う)。

## Implementation Plan

各 PR の完了条件: cargo test(archsig / fieldsig)green、lean.yml green、`git diff --check` +
hidden Unicode scan、**PR 説明に「supplied 側 / generated 側どちらの規律の実装か」を 1 行**。

| PR | 内容 | 対応 R |
| --- | --- | --- |
| PR-1 | law-policy 新形 + basisLedger + 予約欄 + profile 独立化 + finiteBounds + CLI 改名 + catalog / fixture + law-policy-creater 同期 | R1-R4 |
| PR-2 | repair-plan schema + validator + `repair-plan` / `--residual-packet` | R5-R6 |
| PR-3 | `ag.saga-descent`(complete-support)+ saga モジュール新設 + assumption ledger + token 2 種 | R7, R11 前半 |
| PR-4 | `ag.cech-obstruction` 新形 + `COVER_SHAPE_EXCLUDES…` + `REPAIR_TARGETS_IDENTIFIED` | R8-R9 |
| PR-5 | 翻訳規律テーブル + class 語彙 lint + gate e2e + fixture 数値ロック仕上げ + repair-plan-creater SKILL | R10-R13 |

順序は PR-1 → PR-2 → PR-3 →(PR-4 は PR-2 以降で独立)→ PR-5。

## Acceptance Criteria

1. **anti-weakening(負系)**: 結論語(`h1Zero` / `globalCoherent` / `glues` 等)を含む repair-plan、
   および未知フィールドを含む入力が validation fail する。
2. **complete-support cross-check(負系)**: mode = complete-support で 1 つでも
   support.kind ≠ complete の primitive を含む repair-plan が fail する。
3. **前提なし発火の不在**: (a) faithfulness.mode = none の run で
   `REPAIR_GLUES_WITHIN_SELECTED_COMPLEX` が出ず、global-coherence が `unmeasured` +
   `silence_by_design`(供給すべきものを 1 行で示す)になる。(b) triple overlap が存在する、
   または restriction 全射性検査が落ちる fixture で `COVER_SHAPE_EXCLUDES…` が発火しない。
4. **無条件の否定**: r ∉ B¹ fixture で faithfulness の有無に関わらず
   `MEASURED_NONGLUING_RESIDUAL` + concrete support(どの overlap か)が出る(定理3.4(i))。
5. **alias 負例**: 例2.6 / 3.6 型 fixture で coverage = true / faithful = false /
   aliasWitnesses 非空 / not GlobalCoherent が同時に成立する。
6. **層 B の語彙規律**: boundary-membership 段の invariant / token / summary 文に `class` 語彙が
   現れない(lint テスト)。「証明する」が theoremRef なしで現れない(summary 生成テスト)。
7. **予約 fail-closed**: lawSurfaceRef / policies[].profileRef / trueSheafCertificate / gluingData /
   comparison / grounding / faithfulness = supplied を書いた入力が、それぞれ明示エラーで fail する。
8. **finiteBounds**: cap 超過の profile が fail し、cap 以下への引き下げが evaluator の実効上限に
   反映される(正負系)。
9. **basisLedger**: 未解決 basis が fail する。path の実在は検査されない(宣言主義のテスト固定)。
10. **assumption ledger**: 列挙完全性が `assumed_by: repair-plan author` として packet に現れる。
11. **gate 接続**: SAGA 行入りの正常系 run が boundaryKindOverrides 付き gate-policy で
    `PASS_WITHIN_GATE_POLICY`(pass_with_boundary 記録付き)になる e2e。
12. **数値ロック**: R12 の 4 fixture が期待値どおり(proved 帰属の注記込み)。決定論(byte 同一)維持。
13. **問いへの遡及**: 各 PR の説明に supplied / generated どちらの規律の実装かが 1 行で書かれている。

## Non-Goals

- law-equation-surface / holdsCriterion / defectSources / quotientSheafCondition の有効化 —
  Stage 2(0.5.x)。binding kind registry(発展追随の拡張規律の実装)も law surface と同時。
- 層 C(additive H¹ class)・supplied faithfulness data・true sheaf certificate — Stage 2(0.5.x)。
- `ag.saga-comparison` / 非零 class 転送 / `ag.saga-grounded`(10 結論 packet)— Stage 2〜3(0.5.x)。
- `ag.harmonic-debt` / `ag.refactor-transport` / compare の class-transport — 0.5.x。
- policy 行ごと profileRef の**有効化**(単一 run 多 profile)— 0.5.x(本 PRD は予約のみ)。
- conormal 係数(I_U/I_U²)— 理論側の進展待ち(v0.6.0 系)。受け皿も作らない(沈黙)。
- SAGA ビューの可視化 — 0.5.x ArchView マイルストーン(packet 側の invariant はここで揃う)。
- 互換機構の追加 — 裁定10 により恒久非目標。
