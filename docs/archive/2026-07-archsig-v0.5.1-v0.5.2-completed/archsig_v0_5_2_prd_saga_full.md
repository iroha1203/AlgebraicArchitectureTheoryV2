# ArchSig v0.5.2 PRD — SAGA 完全対応(診断階段 Stage 2 + Stage 3、O2 完結)

対象は SAGA 診断の階段の残り全部 = **Stage 2(層 C / D: supplied faithfulness・class 語彙・
saga-comparison)+ Stage 3(層 E: saga-grounded 10 結論 + harmonic-debt + refactor-transport +
compare の class-transport)**。目標アウトカム **O2「SAGA 等の理論を現場接続する」の完結**であり、
v0.5.2 のスコープはこれのみとする。設計正本が意図的に未決のまま残した supplied slot 4 種
(faithfulness data / gluing data / supplied Čech 係数 / law-equation witness = holdsCriterion)の
形状裁定も**本 PRD に含める**(ユーザー決定 2026-07-12: 補遺設計ノートは挟まず PRD 一本)。

**前提: v0.5.1(LawPolicy Stage 2)受け入れ済み** — law-equation-surface が方程式の唯一の
供給経路であり、witnessFamily は profile に存在せず、policy-bundle の componentFingerprints が
実装済みであること。v0.5.0 出荷済みの階段は層 B まで(repair-plan + `ag.saga-descent`
complete-support regime + gate boundaryKindOverrides + 層 B の class 語 lint)。

関連(設計の正本):

- [design_ag-measurement](../2026-07-archsig-v0.5.0-completed/design/design_ag-measurement.md)
  — §3.1(repair-plan フィールド表)、§3.3.1-3.3.3(saga evaluator 3 種)、§3.4(10 結論 packet)、
  §3.5(実行機構 3 条件・profileRef blocking 依存)、§3.6 S2/S3/A3/A4、§3.7(定理8.4/8.5/6.4 の
  guardrail 三層)、§3.8(翻訳規律 7 項)、§3.9(数値ロックと witness 帰属)、§5.1 Stage 2-3
- [design_lawpolicy](../2026-07-archsig-v0.5.0-completed/design/design_lawpolicy.md)
  — §3.4(b)(Stage 3 予約欄)、§7 未決事項 1 / 3(本 PRD が閉じる slot)
- [再設計ノート](../2026-07-archsig-v0.5.0-completed/archsig_v0_5_0_redesign_note.md)
  — §8 裁定3(SAGA 層 E データ = law-equation-surface)・裁定7(単一契約版数)・裁定10(互換ゼロ)、
  compare の class-transport 水準
- [v0.5.1 PRD](archsig_v0_5_1_prd_lawpolicy_stage2.md) — law surface の schema・予約欄・fingerprint
- AAT 本文: 第X部(定義3.1 / 定義3.2 語彙規律 / 定理3.4-3.5 / 定義4.2 / 補題4.5 / 定義4.6 /
  定義4.7 / 定理4.8 / 定義5.1 / 定理6.4 / 定義7.1 / 定理7.2-7.5 / 定理8.1-8.2 / 定理8.4-8.5 /
  例9.1-9.2)、第III部(定義11.3 / 定理11.4 / 系11.5)、第VIII部(定理7.3 refactor invariance /
  定理8.5-8.7 harmonic debt / 命題4.10)。SAGA 数学本文は第X部 + 第III部 §11 が canonical

## 問い

**SAGA の診断階段は上下両方向に閉じているか —
下(供給)から: 第X部の supplied 成分のすべてに artifact の置き場・validator・fixture があるか。
上(発火)から: どの結論も、その段の supplied データなしには発火しないか。**

「完全対応」の完全性と健全性を一つの判定規律に束ねる。供給側の判定は §R1 の
**supplied slot 台帳**で行い、発火側の判定は反例駆動で行う:

- **(供給側の採否)** slot 台帳の全行が「artifact の置き場 + validator + fixture」を持ち、
  空行がないこと。台帳にない supplied 成分に依存する結論行が 1 つでも出力されれば fail。
  逆に、置き場だけあって validator / fixture のない slot が残れば completion と呼ばない。
- **(発火側の反例 — 各 1 つでも残れば fail)**
  1. 商が構成されない run(層 C 未供給)の invariant / token / summary に class 語が現れる
     (第X部 定義3.2 の語彙規律)。
  2. holdsCriterion による defect 生値検査を経ずに law 依存肯定結論
     (`DISPLAYED_LAWS_HOLD_ON_SELECTED_CHARTS` / law-dependent conclusions)が発火する。
     interpretation 零・H^0 零からの premise 導出も同罪(系11.5: 消滅と同値なのは
     law の成立ではなく defect の ideal 所属)。
  3. comparison data の適合検査(定義7.1)なしに class の転送・同一視・「同じ障害の追跡」を語る
     (定理8.4 / 8.5: 比較可能性はデータである)。
  4. cost model の供給なしに repair 下界(`essentialRepairLowerBound`)行が立つ(系8.7)。
  5. refactor-morphism artifact なしに版間 verdict transport を語る(第VIII部 定理7.3)。
  6. 出力面(packet / summary / insight)に絶対 cohomology 表記(full sheaf 語)が現れる(定理8.4)。
- **(採用条件)** slot 台帳の行を埋める変更、発火反例 6 種をゼロにする変更、
  およびそのゼロを負系テストで固定する変更。
- **(却下条件)** 結論相当フィールドの supplied 化(comparison / certificate に商水準の対応や
  zero 保存の結論を書かせる)、前提検査なしの結論発火、H^1 零の law 証拠化(定理8.2)、
  細→粗方向の refinement 申告の受理(定理8.5 の反例で遮断)、Stage 4 の先取り
  (nullstellensatz / hilbert-interference / boundary-residue@2)、互換機構(裁定10)は、
  たとえ有益でも却下する。

## Core Thesis

理論側は SAGA 全連鎖(第X部 + 第III部 §11)が Lean proved であり、v0.5.0 は階段の層 B
(境界所属、complete-support regime)までを現場計測にした。残りの層 C(class)・層 D(比較)・
層 E(law-grounded 10 結論)と analytic 系(harmonic-debt / refactor-transport)は
すべて「supplied データがあるときだけ語れる」段であり、実装の本体は evaluator の計算よりも
**supplied slot の contract 設計**にある。だから本 PRD の中心は slot 台帳(R1)である:
第X部が要求する supplied 成分の全数を台帳化し、各行に置き場・検査・解禁される語彙を割り当て、
台帳の外に supplied 成分が残らないこと(供給側の閉包)と、台帳の行なしに結論が出ないこと
(発火側の閉包)を同じ表で判定する。

v0.5.0 設計からの継承裁定を 3 点固定する:

1. **層 E の受け口は law-equation-surface**(裁定3)。design_ag-measurement §3.2 の
   「profile の lawEquation ブロック」案は採らない。v0.5.1 が予約した `skeleton` /
   `defectSources` / `quotientSheafCondition` / `diagnosticCeiling` を有効化し、
   holdsCriterion は law surface 側に新設する(本 PRD の裁定、R5)。
2. **strict carve-out(design_ag-measurement §3.5)は実装しない**。strict 系フラグは
   v0.5.0 で全廃済みであり、「宣言済み沈黙を CI がどう扱うか」は gate-policy の
   boundaryKindOverrides が既に制度化している。carve-out の意図(silence_by_design を
   fail に丸めない)は gate 側の e2e で担保する(R11)。
3. **grounded residual と measured residual の分離**は evaluator と invariant の構造で守る
   (design_ag-measurement §3.4 要点 4)。定理7.5 経路の residual は構成的に δ⁰(primitive) なので
   その H^1 零は law の証拠ではない — この線が本 PRD で最も事故りやすい境界である。

## Design Principles

1. **語彙は段が解禁する**: 層 B = 境界所属の生値(class 語なし)、層 C = class 語、
   層 D = 転送の語、層 E = law の語。verdict 行の立て方は判別基準
   「選ばれていない語彙の行は立てない / 語彙の内の入力不足は `unmeasured` 行 + boundary statement」
   (design_ag-measurement §3.3 冒頭)に従う。
2. **supplied は検査してから使う、検査で落とせないものは assumption ledger へ**:
   comparison の両側逆・zero 保存・可換、faithfulness の 3 点適合、係数公理、gluing 適合、
   holdsCriterion の tie 整合は有限検査(落ちたら contract violation の明示 fail)。
   列挙完全性・global sheaf condition 等は `assumed_by: author` で台帳記録(一括払い)。
3. **comparison / certificate は結論を格納しない**: 写像水準のフィールドのみ定義し、
   商水準の対応・zero class・整合を書く欄を作らない(定義7.1 の schema 化)。
   deny_unknown_fields + 結論語 hard error は全新設 schema に既定で課す。
4. **law-dependent / law-independent の分割は packet の一次構造**(定理7.5 の
   statement-level dependency boundary)。theorem-level(`status: established`)と
   instance-level(`instanceReading`)を同じフィールドに潰さない。
5. **premise の判定源は holdsCriterion 生値検査のみ**。premise fail 時は law-dependent 結論を
   `not_established` にし、代わりに detector(系11.5 detector soundness)を発火する —
   沈黙ではなく certified detection。
6. **係数生成は square-free / F₂ Boolean クラス限定**。一般の ideal membership
   (Gröbner 基底級)は導入せず、既存 MAX_* と同型の有限上限を課す。クラス外は入力検証で語る。
7. **翻訳規律 7 項**(design_ag-measurement §3.8)を summary 生成コードの写像規則テーブルと
   テストで固定する。「証明する」は theoremRef 付き定理帰属文のみ。
8. **Rust / Lean 非対応**: フィールド名の Lean 鏡写し(`SemanticRepairGeneratedEndToEndSAGAPacket`)と
   fixture 数値ロックは便宜であり contract ではない。witness の形ごとに proved 帰属を書き分ける
   (circle nerve の Lean witness は 3 辺形。2 頂点形は本文対応の補助 fixture)。
9. **モジュール規律**: saga-comparison / saga-grounded / harmonic-debt / refactor-transport は
   SAGA モジュール群に置き、既存 dispatch の if-else 連鎖に追記しない。
10. **版数一斉更新**: 全 schema 文字列を `<name>/v0.5.2` に更新(裁定7)。受理は完全一致のみ。

## 改修(本体)

### 供給側 — slot 台帳と supplied slot の解禁

- **R1(supplied slot 台帳)** 第X部の supplied 成分の全数台帳を `docs/tool` に文書として新設し、
  実装の受け入れ判定表とする。各行 = supplied 成分 / 理論典拠 / 置き場 artifact / validator /
  解禁される語彙 / fixture。本 PRD 時点の全行:

| supplied 成分 | 典拠 | 置き場 | 検査 | 解禁される語彙 |
| --- | --- | --- | --- | --- |
| 観測(atoms / contexts / covers) | 第X部 (A) | archmap(既存) | R1-R3(既存) | 層 B の生値 |
| repair primitives(C⁰ / δ⁰ / supp) | 定義3.1 (B) | repair-plan(既存) | restriction-difference ほか(既存) | 境界所属 |
| faithfulness data(zero primitive / 述語 Q / faithfulness law) | 定義4.6 | repair-plan `faithfulness.mode: "supplied"`(解禁) | 3 点適合 + Q(r) 検査 | complete-support 以外の regime での肯定的大域整合 |
| triple + additive 係数 | 定義4.2 | repair-plan `complex.tripleOverlaps` + `coefficient`(`f2-additive` 標準 / supplied 形を解禁) | 係数公理(additive regime・δ¹∘δ⁰=0・δ¹(0)=0) | 層 C の class 語彙 |
| true sheaf certificate | 定義4.7 | repair-plan `trueSheafCertificate`(解禁) | cover membership 検査 + global sheaf condition は assumption 行 | 定理4.8 package 読み |
| gluing data | 第X部 定理7.3 | repair-plan `gluingData`(解禁) | 適合検査 | grounded global gluing package |
| comparison data(incidence bridge + h1 comparison) | 定義7.1 / 定理6.4 | repair-plan `comparison` + `h1-comparison-data/v0.5.2` | 両側逆・差の保存・zero 保存・微分可換・参照解決 | 層 D の転送 |
| law equation grounded surface(変数・Forb・skeleton・defect tie・holdsCriterion・quotient sheaf condition) | 定義5.1 / 定義11.3 | law-equation-surface(Stage 3 欄有効化 + holdsCriterion 新設) | 5 点組適合 + 単元 context 検査 | 層 E の 10 結論 |
| cost model(Lipschitz 定数 L + harmonic-resolution 要求) | 第VIII部 系8.7 | measurement-profile の analytic 宣言欄(新設) | 宣言検査 + assumption ledger 記録 | repair 下界行 |
| refactor morphism(site 射 + law / coefficient / witness 互換) | 第VIII部 定理7.3 | `refactor-morphism/v0.5.2`(新設) | 互換データ検査 | 版間 verdict transport |
| refinement data(粗→細) | 命題4.10 | `refinement-comparison/v0.5.2`(新設) | 粗→細方向検査(細→粗は schema が受けない) | compare の zero 引き継ぎ |

  design_lawpolicy §7 未決事項 1 / 3 の slot はこの台帳で全行閉じる。
  以後、置き場のない supplied 成分に依存する結論は「台帳に行を足してから」でなければ実装しない。
- **R2(supplied faithfulness、層 B→C の橋)** repair-plan の `faithfulness.mode: "supplied"` を
  解禁する。supplied ブロック = 定義4.6 の 3 点(zero primitive / residual support predicate Q /
  faithfulness law)。ArchSig は 3 点の参照整合と Q(r) を検査し、pass した run で
  `faithfulnessBasis: "supplied-data"` の下の肯定的大域整合(`REPAIR_GLUES_WITHIN_SELECTED_COMPLEX`)
  を解禁する。検査で落とせない部分は assumption ledger 行。
- **R3(層 C の解禁)** `trueSheafCertificate`(定義4.7)・`gluingData`(第X部 定理7.3)・
  supplied 係数(定義4.2 の公理検査)の予約を解除し、triple + additive 係数が揃った run で
  Z¹/B¹ の class 判定(補題4.5)を実装する。`saga.residual-class` verdict 行と
  `MEASURED_NONGLUING_RESIDUAL_CLASS` token、class 語彙のフィールド(`residualClassSupport` 等)は
  **この段でのみ** emit する(層 B のフィールド名 `residualSupport` は不変)。

### 層 D — 比較と転送

- **R4(`ag.saga-comparison`)** 入力 = 層 C までの全部 + `comparison` ブロック
  (`incidenceBridge.kind: chart-indexed | explicit`、`h1ComparisonData.kind: identity | explicit`)。
  chart-indexed は定理6.4 の構成的側で tool が incidence を生成(構成条件 = repair cover の
  添字集合が Čech cover の chart 集合と一致、満たさなければ explicit 要求 — no-go: 一様構成は
  存在しない)。identity は両辺が同一の正規化有限複体表示を持つときのみ。explicit は
  定義7.1 の適合条件(degree1 両側逆・差の保存 / degree2 zero 保存 / 微分可換)を有限検査し、
  落ちたら `COMPARISON_DATA_CONTRACT_VIOLATION` で fail。invariant は supplied
  (cochain 水準の写像)と generated(商水準の同型・zero-predicate equivalence・非零 class 転送 =
  定理7.2 / 7.4)の区別を構造で刻む。token `SAGA_COMPARISON_ESTABLISHED_UNDER_SUPPLIED_DATA`。
  comparison 不供給時は verdict 行を立てず `silence_by_design`
  (reason: `comparison_data_not_supplied`)1 行(エラーでも残タスクでもない)。
  explicit の `cochainMap` は `degreeZero` / `degreeOne` / `degreeTwo.basisMap` の有限基底写像表
  (chart・overlap・triple の対応と変数対応)と `degreeTwo.zeroImage` を供給し、ArchSig が5条件を表から再計算する。
  `degreeOneLeftInverse` などの宣言booleanは入力schemaに置かない。

### 層 E — law-grounded 10 結論

- **R5(law surface Stage 3 欄の有効化 + holdsCriterion)** v0.5.1 の予約欄を有効化する:
  `skeleton`(0-単体ごとの supportAtomRef + requiredLawId、analyze 時に参照解決)、
  `defectSources`(law ごとの coverRef + chartDefects の defectObservable = ArchMap 生値参照)、
  `quotientSheafCondition`(`single-context-theorem` は selected context poset の単元性を検査し
  pass なら `discharged-by-finite-model`〔例9.1、仮定が定理に変わる唯一の箇所〕、不成立は
  fail-closed。`assumed` は assumption ledger 行。`not-selected` は層 E 結論なし)、
  profile の `diagnosticCeiling`(要求上限の宣言。到達段が上限未満なら boundary statement)。
  **holdsCriterion は law surface の `defectSources[]` に新設する(本 PRD の裁定)**:
  law ごとの評価意味論(chart-local holds-defect tie、定義11.3)の宣言
  (例: `{ "kind": "defect-raw-value-zero", "zeroSense": "empty-witness-set" }`)。
  ArchSig は defect observable の**生値**に criterion を適用して premise
  `displayedRequiredLawsHold` を判定する。判定源はこの生値検査のみで、
  interpretation 零・H^0 検査 pass からは生成しない(系11.5)。assumption ledger に
  「premise は宣言された tie を介した operationalization」の 1 行を記録する。
- **R6(`ag.saga-grounded`、10 結論 packet)** 入力 = 層 D までの全部 + law surface の
  grounded surface(R5)への `grounding` 参照。計算: 定義5.1 の 5 点組適合検査 →
  係数 Q = O/I_Ob の生成(square-free / F₂ Boolean 限定 + 有限上限、原則6)→
  各 chart で holdsCriterion 生値検査(law-check)→ 生値を商に落とし interpretation を計算 →
  10 結論 packet の組立。packet(design_ag-measurement §3.4 の schema が正、契約版数は
  `archsig-saga-conclusions/v0.5.2`)は **lawDependent / lawIndependent の分割を一次構造**とし、
  theorem-level(`established` + theoremRef)と instance-level(`instanceReading`)を分離、
  premise fail 時は `detectorFindings`(`MEASURED_LAW_DEFECT_AT_CHART`、系11.5 detector
  soundness の certified detection)を発火する。lawIndependent 区画には
  「law の充足を仮定せずに従う。law 充足の証拠として読まない」(定理8.2)を焼き込み、
  `degreeZeroLawContribution`(定理8.1: law 意味論が複体に到達する地点は正確に次数 0)を刻む。
  token: `MEASURED_LAW_DEFECT_AT_CHART` / `DISPLAYED_LAWS_HOLD_ON_SELECTED_CHARTS`。
  **grounded residual(構成的 δ⁰)と measured residual(`ag.saga-descent`)は別 evaluator・
  別 invariant のまま分離する**(継承裁定 3)。

### analytic 系と compare

- **R7(`ag.harmonic-debt`)** 入力 = cover complex + profile 宣言の内積 / 重み + cost model
  (系8.7 の Lipschitz 定数 L + harmonic-resolution 要求。R1 台帳の profile analytic 欄)。
  出力: `harmonicDebtNorm`(analytic readings 区画。verdict 文に混ぜない)+ certified 文
  「local adjustment では ‖h(g)‖ 未満に下げられない」(定理8.6 のみで支持)。
  `essentialRepairLowerBound` は **cost model 供給時のみ**(assumption ledger に L /
  harmonic-resolution 要求を記録)。不供給 run では下界行を立てない(silence_by_design)。
  既存 `ag.sheaf-laplacian` の proxy ラベルは維持し、本 evaluator は faithful 版として別に立てる。
  norm の小ささは lawfulness ではない(第VIII部 定義3.3)を boundary に併記。
- **R8(`ag.refactor-transport` + compare の class-transport)**
  `refactor-morphism/v0.5.2` 新設(site 射 + law / coefficient / witness 互換データ。
  結論フィールドなし)。検査 pass 時のみ `VERDICT_PRESERVED_UNDER_DECLARED_REFACTOR`
  (第VIII部 定理7.3 の zero verdict 保存)。compare コマンドを class-transport 水準へ拡張:
  (i) identity comparison の自動採用は **正規化後の有限複体表示(context 集合・overlap・
  triple 構造)の同一性を fingerprint が witness するときのみ**(参照名一致のハッシュは
  設計段階で排除 — 定理8.5 違反の入力補完になるため)。v0.5.1 の componentFingerprints と
  siteCoverDigest をこの正規化表示の witness に拡張する。
  (ii) fingerprint 不一致 + `--refinement` なしのときは class の同一視・「同じ障害の追跡」・
  改善 / 悪化の語りを一切せず、`TWO_PROFILES_REPORTED_SEPARATELY` で並記のみ。
  (iii) `refinement-comparison/v0.5.2` は粗→細方向のみ受理(命題4.10。細→粗は schema 拒否)し、
  供給時は検査済み data の下で zero 引き継ぎだけを語る。
- **R9(`policies[].profileRef` の有効化)** design_ag-measurement §3.5 の blocking 依存を解消する:
  policy 行ごとの profileRef で単一 run 多 profile を可能にし、cech 系 profile が residual を
  計測し同一 packet に saga 区画を積む単一 run 構成を正式経路にする。同一 run pin の
  profile 適合規則 = residual を計測した profile と saga profile の site / cover の
  正規化表示一致(不一致は validation fail)。二 run 構成(`--residual-packet`)も引き続き有効。

### 横断 — 語彙・registry・版数・fixture・SKILL

- **R10(語彙 lint の全段化と翻訳テーブル拡張)** 出力 lint を CI に固定する:
  (a) full sheaf 語 — packet / summary / insight に絶対 cohomology 表記(`H^n(X, ·)` 型)を
  emit しない。出力は常に `coverRelativeH1` / 「選ばれた cover に相対的な」(定理8.4)。
  (b) 層 B run の class 語(既存 lint の維持)。
  (c) 「law が守られている」文型は law-check 行からのみ生成し、interpretation 零・H^0 零・
  H^1 零から生成しない(写像規則テーブルのテスト固定。定理8.1 / 8.2 / 系11.5)。
  summary の翻訳テーブルに §3.8 の新 token 行(class / comparison / law / harmonic / refactor)を
  追加し、Avoid 対句を skills(archsig-reader)に載せる。
- **R11(conclusionCode registry / gate 接続)** 新 token
  (`MEASURED_NONGLUING_RESIDUAL_CLASS` / `SAGA_COMPARISON_ESTABLISHED_UNDER_SUPPLIED_DATA` /
  `MEASURED_LAW_DEFECT_AT_CHART` / `DISPLAYED_LAWS_HOLD_ON_SELECTED_CHARTS` /
  `VERDICT_PRESERVED_UNDER_DECLARED_REFACTOR` / `TWO_PROFILES_REPORTED_SEPARATELY` /
  `COMPARISON_DATA_CONTRACT_VIOLATION`)を registry に登録。`STRUCTURAL_VERDICT_EVALUATORS` へ
  `ag.saga-comparison` / `ag.saga-grounded` を追加。silence_by_design 付き非終端行を含む
  正常系 run が boundaryKindOverrides 付き gate-policy で `pass_with_boundary` になる e2e を
  各段(comparison 不供給 / cost model 不供給 / ceiling 未達)で固定する(継承裁定 2)。
- **R12(版数一斉更新)** 全 schema 文字列を `<name>/v0.5.2` へ(新設: h1-comparison-data /
  refinement-comparison / refactor-morphism / archsig-saga-conclusions を含む)。
  catalog / lock fixture 改訂、v0.5.1 文字列の入力は全面拒否。
- **R13(fixture と数値ロック)** proved 帰属を書き分けて lock する(design_ag-measurement §3.9):
  (a) circle nerve **3 辺 Lean witness**(`circleSimplex` / `circleNext`、係数 Z/(2))—
  residual class 非零 + identity comparison 下で両側非零(転送発火)。
  (b) 2 頂点・逆向き 2 辺の本文 worked example(例9.2 / B.9)— 同現象の**補助 fixture**
  (Lean proved はこの形ではない、の帰属注記込み)。
  (c) lawful firing instance(単一 context、例9.1)— displayed laws hold ⇒ interpretation 零 ∧
  defect class 零 ∧ quotientSheafCondition = discharged-by-finite-model。
  (d) premise fail instance — detectorFindings 発火 + law-dependent `not_established` +
  lawIndependent は established のまま(分割の実測)。
  (e) 擬円周 cover / B.8 toy / alias 負例 / hitting sets {q},{p,r}(既存ロックの維持)。
  (f) harmonic debt explicit data 例(定理8.5-8.7)— cost model 有無の対 fixture。
  (g) refactor-transport e2e(morphism 供給で zero verdict 保存 / 不供給で transport なし)。
  決定論(同一入力 → byte 同一)維持。
- **R14(SKILL / docs / website 同期)** repair-plan-creater を supplied faithfulness /
  comparison / gluing / certificate の authoring に拡張(complete-first の型を維持、
  良悪対例集: 結論語入り comparison の悪例、細→粗 refinement の悪例)。law-policy-creater に
  Stage 3 欄(skeleton / defectSources / holdsCriterion / quotientSheafCondition)の authoring 節を
  追加。archsig-reader に Avoid 対句(R10)と診断階段の読み方、archsig-pr-reviewer に
  law-dep / law-indep の読み分けを追加。責務憲章・`docs/tool/law_policy.md`・
  `archsig_compare.md`・`archsig_gate_policy.md`・commands.md・README・website の
  ArchSig 製品マニュアル該当ルートを同一波で改訂。ArchView への interface は
  design_ag-measurement §3.10 の表(計測データ → 解放される幾何)を docs に残すのみ
  (描画実装は ArchView 波)。

## Changed / Removed Fields

- **Added**: repair-plan の supplied 解禁 4 欄(faithfulness supplied ブロック /
  trueSheafCertificate / gluingData / comparison)+ supplied 係数形、law surface の
  Stage 3 欄有効化 + `defectSources[].holdsCriterion`、profile の `diagnosticCeiling` 有効化 +
  analytic 宣言欄(内積 / 重み / costModel)、`h1-comparison-data` / `refinement-comparison` /
  `refactor-morphism` / `archsig-saga-conclusions`(いずれも v0.5.2)、
  `ag.saga-comparison` / `ag.saga-grounded` / `ag.harmonic-debt` / `ag.refactor-transport`、
  `policies[].profileRef` 有効化、conclusionCode 7 種、supplied slot 台帳文書。
- **Changed**: 全 schema 文字列 v0.5.2、`ag.saga-descent`(層 C 解禁: class 判定 + class 語彙
  フィールドの条件付き emit)、compare(class-transport 水準 + fingerprint 健全性要件)、
  summary 翻訳テーブル(新 token 行)。
- **Not changed**: archmap/v2 の schema 形状(SAGA に必要な観測は既存語彙の範囲。
  版数文字列のみ更新)、packet 6 区画、五値 verdict、層 B のフィールド名(`residualSupport`)、
  `ag.square-free-repair` の invariant、`ag.sheaf-laplacian` の proxy ラベル、
  gate の決定面(boundaryKindOverrides の機構は不変)。

## Failure Contract

- **fail-closed(明示エラー)**: comparison / faithfulness / 係数 / gluing / morphism /
  refinement の適合検査不合格(`COMPARISON_DATA_CONTRACT_VIOLATION` 等)、
  結論語入り supplied ブロック、細→粗 refinement、単元性不成立の single-context-theorem 宣言、
  係数生成クラス外の入力、profile 適合規則違反(単一 run pin)、未知フィールド、
  v0.5.1 版数文字列。
- **沈黙(boundary statement 付き非終端)**: comparison 不供給・cost model 不供給・
  faithfulness 不在・repair-plan 不供給・diagnosticCeiling 未達は fail ではなく
  `not_computed` / `unmeasured` + `silence_by_design`(次に何を供給すれば語れるかを 1 行)。
  gate は boundaryKindOverrides で制度的に扱う。
- 補完・推測・縮退は存在しない(fail-closed と沈黙の二分のみ)。

## Implementation Plan

各 PR の完了条件: `cargo test`(archsig / fieldsig)green、`git diff --check` +
hidden Unicode scan、**PR 説明に「供給側 / 発火側どちらの閉包を進めたか(+対応する台帳行 /
反例番号)」を 1 行**。

| PR | 内容 | 対応 R |
| --- | --- | --- |
| PR-1 | slot 台帳文書 + 版数一斉更新 + repair-plan supplied 4 欄解禁(faithfulness / certificate / gluing / 係数)+ 層 C class 解禁 | R1-R3, R12 |
| PR-2 | `ag.saga-comparison` + h1-comparison-data + 転送 invariant | R4 |
| PR-3 | law surface Stage 3 欄有効化 + holdsCriterion + diagnosticCeiling + profileRef 有効化 | R5, R9 |
| PR-4 | `ag.saga-grounded` 10 結論 packet + detector + 分割構造 | R6 |
| PR-5 | `ag.harmonic-debt`(cost model contract 込み) | R7 |
| PR-6 | `ag.refactor-transport` + compare class-transport + refinement-comparison | R8 |
| PR-7 | 語彙 lint 全段化 + 翻訳テーブル + registry / gate e2e | R10, R11 |
| PR-8 | fixture 数値ロック仕上げ + SKILL / docs / website 同期 | R13, R14 |

順序は PR-1 → PR-2 → PR-3 → PR-4 →(PR-5 / PR-6 は PR-1 以降で独立、PR-6 は PR-2 の後)→
PR-7 → PR-8。PR-4 は PR-2 と PR-3 の両方に依存する。

## Acceptance Criteria

1. **slot 台帳の完全性(供給側)**: R1 台帳の全行に artifact + validator + fixture が存在し、
   空行がない。台帳にない supplied 成分に依存する結論行が出力されない(監査 AC)。
2. **class 語彙の段束縛(反例 1)**: 層 C 未供給 run の invariant / token / summary に
   class 語が現れない(lint + 負系)。供給 run で `saga.residual-class` 行と
   `MEASURED_NONGLUING_RESIDUAL_CLASS` が発火する(正系)。
3. **law 依存肯定結論の witness 束縛(反例 2)**: `DISPLAYED_LAWS_HOLD_ON_SELECTED_CHARTS` と
   lawDependent conclusions が holdsCriterion 生値検査 pass の場合のみ発火し、
   interpretation 零・H^0 零から premise が導出されない(写像規則テスト)。premise fail 時に
   detectorFindings が発火し lawIndependent 区画は established のまま(R13(d) fixture)。
4. **転送のデータ束縛(反例 3)**: comparison 不供給 → silence_by_design、適合検査不合格 →
   `COMPARISON_DATA_CONTRACT_VIOLATION`、established のときのみ非零 class 転送。
   identity 自動採用は正規化複体表示の一致のみ(参照名だけ一致する負系 fixture で不採用)。
5. **下界の cost model 束縛(反例 4)**: cost model 不供給 run に `essentialRepairLowerBound` 行が
   立たず、供給 run でのみ assumption ledger 記録付きで立つ(対 fixture)。
6. **transport の morphism 束縛(反例 5)**: refactor-morphism なしの版間 transport なし。
   fingerprint 不一致 + refinement なしで `TWO_PROFILES_REPORTED_SEPARATELY`(class 同一視ゼロ)。
   細→粗 refinement が schema で拒否される(負系)。
7. **full sheaf 語 lint(反例 6)**: 全出力面に絶対 cohomology 表記が現れない(CI lint)。
8. **H^1 零の law 証拠化の不在**: grounded packet の lawIndependent note が保持され、
   summary に「H^1 零 ⇒ law 充足」型の文が生成されない(定理8.2 焼き込みテスト)。
9. **profileRef**: 単一 run 多 profile の e2e(cech residual 計測 + saga 区画が同一 packet)、
   profile 適合規則違反の fail(負系)。二 run 構成の継続動作。
10. **数値ロック**: R13 の全 fixture が期待値どおり(witness 帰属の注記込み: 3 辺形 = Lean proved、
    2 頂点形 = 本文仕様)。既存 5 系列(v0.5.1 AC7)の再現維持。決定論 byte 同一。
11. **版数統一**: catalog / lock fixture の全 schema 文字列が v0.5.2、v0.5.1 文字列の全面拒否。
12. **gate / registry**: 新 token 7 種の registry 登録、silence_by_design 付き正常系 run の
    `pass_with_boundary` e2e(comparison 不供給 / cost model 不供給 / ceiling 未達の 3 態)。
13. **SKILL / docs**: repair-plan-creater が supplied faithfulness / comparison を authoring し
    analyze が通る実行例、law-policy-creater の Stage 3 節、翻訳 Avoid 対句の reader 反映、
    憲章・compare / gate docs・commands.md・README・website 該当ルートが v0.5.2 実体と一致。
14. **問いへの遡及**: 各 PR の説明に、供給側 / 発火側どちらの閉包か(台帳行 / 反例番号)が
    1 行で書かれている。

## Non-Goals

- **Stage 4(second wave)**: `ag.nullstellensatz-certificate` / `ag.hilbert-interference` /
  boundary residue 拡張(`ag.boundary-residue` の版上げ)— 別波。
- **C 群**: stability / barcode / Wasserstein / hotspot(statement-only candidate、
  安定性定理なしの計測値は接続しない)、temporal(第IX部)— FieldSig / SFT 側スコープ。
  artifact に拡張点だけ残す。
- **conormal 係数(I_U/I_U²)・non-abelian H¹ / stacky descent(G-04 系)** — v0.6.0 予約。
  受け皿も作らない(沈黙)。
- **ArchView V-A〜C** — 可視化波として別(計測が主・可視化が従)。本 PRD は §3.10 の
  interface 表(計測 → 解放される幾何)を docs に残すまでで、描画は実装しない。
  v0.5.2 完了で V-C(SAGA ビュー)の計測前提が揃う。
- **repair synthesis・最小修復・extraction completeness の主張** — 恒久非主張
  (claim boundary。hitting set は組合せ的 repair target、原則5.3 併記)。
- **corpus M3 / 外部ドッグフーディング** — v0.5.2 完成後(ユーザー決定 2026-07-12:
  順序は v0.5.1 → v0.5.2 → ドッグフーディング。SAGA 込みの計測器を実戦投入する)。
- **互換機構・migrate** — 恒久非目標(裁定10 / 裁定12)。
