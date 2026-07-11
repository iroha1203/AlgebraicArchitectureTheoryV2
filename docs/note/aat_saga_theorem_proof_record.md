# SAGA 定理 — 証明の記録

- 対象 GOAL: `G-aat-quality-surface-06`(AAT Site-Sheaf-Cech H1 Grounding Theorem)
- 完了: 2026-07-03 JST、`target-theorem-proved`(ユーザー受理)
- 正式な statement / claim boundary: [research/goals/G-aat-quality-surface-06.md](../../research/goals/G-aat-quality-surface-06.md) の completed カード
- 証明状態の台帳: [research/reports/G-aat-quality-surface-06.md](../../research/reports/G-aat-quality-surface-06.md)、tracking Issue [#2636](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/2636)(closed as COMPLETED)
- 本ノートの役割: 証明の物語・構造・命名の記録。statement の正本ではない。

## 1. 名前

この定理を **SAGA 定理**(SAGA Grounding Theorem; *Sémantique Architecturale, Géométrie Algébrique*)と呼ぶ。

命名は Serre の GAGA(*Géométrie Algébrique et Géométrie Analytique*)比較定理の伝統に連なる。GAGA が代数幾何と解析幾何という二つの世界のコホモロジーの一致を確立したように、SAGA 定理は**アーキテクチャ意味論の世界**(semantic repair additive `H1 = Z1/B1`)と**代数幾何の世界**(atom-generated AAT site 上の cover-relative Cech `H1`)のコホモロジーの一致を確立する。同時に、352 サイクル・347 の no-go 定理・一度の査読 veto と再審を経て登り切った登攀の記録として、*saga*(叙事詩)の語義を担う。命名は 2026-07-03 のユーザー判断による。

## 2. 何が証明されたか

一言でいえば: **AAT のコホモロジーは AAT 自身の公理から生えている**。

Lean 上に、途切れのない一本の定理連鎖が立った:

```
Atom(第I部)
  → law = 方程式(第III部: violation 座標、witness ideal I_L、I_Ob = Σ I_L)
  → obstruction 係数 = 商 O/I_Ob(第IV部の意図の実現、restriction は Ideal.quotientMap で構成)
  → atom-generated coverage / Grothendieck topology / AATSite(第II部)
  → cover-relative Cech 複体と H1
  → semantic repair additive H1 = Z1/B1(G-05)
  → 両者の comparison と zero-predicate equivalence(G-06 = SAGA)
```

各矢印は supplied certificate ではなく theorem である。G-06 カードが primary rival として名指ししていた「形式化内部の ad hoc Cech package」— site/sheaf 基盤の隣に接ぎ木された専用の有限商 — は消滅し、semantic repair `H1` は一般基盤の selected instance として読めるようになった。

中心的な新規命題は、法の充足が幾何を動かすことを言う **restriction evaluator の定理化**である:

> required law が局所の displayed reading の上で成り立つならば、共通細分上で obstruction-sheaf の制限は一致する。

これは `Lawful ⟺ s*I_Ob = ⊥`(law の成立 ⟺ ideal の消滅)というヒルベルトの Nullstellensatz 型の対応を要石とし、商係数の restriction functoriality を通って Cech 面に降りる。付随して、detector soundness(非零 class は displayed required law の失敗を証明する)、非退化性(商は lawful / non-lawful な読みを実際に分離する)、非零 `H1` class の双方向転送(zero-predicate equivalence が非 boundary content 上で機能する)が定理として並ぶ。

## 3. 塔の中の位置

- **G-02**(QED): 有限 semantic repair-gluing descent 定理 — 局所修復が大域に貼り合うのは有限 obstruction が消えるとき、かつそのとき。
- **G-05**(QED): その obstruction が本物の `Z1/B1` 商 `H1` であること。
- **G-06 = SAGA**(QED): その `H1` が atom-generated site 上の law-generated 係数の cover-relative Cech `H1` であること — **塔の全階が同じ地盤の上にあることの証明**。

SAGA 以後、G-03(relation atom)と G-04(universal obstruction tower)は、ad hoc な有限商ではなく site / sheaf / cohomology の標準的な数学面の上で進められる。

## 4. 証明の物語 — 352 サイクルの構造

### 第 1 幕(Cycle 1–99): comparison DAG の構築

G-05 の additive `H1` と一般 cover-relative Cech `H1` の quotient レベルの比較(`semanticRepairAdditiveH1Class_to_coverRelativeH1` と逆写像、`semanticRepairAdditiveH1Zero_iff_coverRelativeH1Zero`)、cochain realization、面制限微分の対応網が完成。site/sheaf 側の proof-use(`AATSheafCondition` → descent → effective gluing)も接続された。

### 第 2 幕(Cycle 100–218): 封鎖の絨毯爆撃

claim boundary が硬化され(cover refinement / naturality と full sheaf cohomology 比較は completion 外の boundary theorem へ)、あらゆる逃げ道 — surface のみ、boundaryData、conclusion-side shortcut、certificate field への退避 — が PUnit/ZMod2 型の有限反例で個別に封鎖された。Cycle 162 で `target-blocked` 宣言。欠落は「selected semantic coefficient realization layer」と命名された。

### 第 3 幕(Cycle 219–296): generated 転換

任意 envelope に比較を作る路線を放棄し、係数・regime・Cech 複体を atom/law cover geometry から**生成する**路線へ転換。標準的な交代和微分と `d ∘ d = 0` が生成側で証明され、Cycle 296 で `arrowCompatibilityLaw ⟺ commonRestrictionRealization`(sheaf descent 経由)が確立。

### 第 4 幕(Cycle 296–347): 一点圧縮と法宇宙の限界

目標全体が一つの命題に圧縮された:

```
∃ display-preserving baseRestrictionSource
  ⟺ arrowCompatibilityLaw ⟺ commonRestrictionRealization
  ⟺ overlap restriction equality ⟺ sourceC0CechZero ⟺ residual-zero
  ⟺ displayedRequiredLawRestrictionEvaluator(lawful objects の下で)
```

そして Cycle 320–347 の no-go 定理群が、この一点が**現行語彙からは原理的に出ない**ことを証明した。原因は `Law.holds : ArchitectureObject → Prop` — law が不透明述語であり、interpret が自由フィールドである限り、law データは interpret を定義的に制約できない(`withDisplayedInterpretation_iff` が `rfl` で証明されてしまう)。これは失敗の記録ではなく、**理論が自分の語彙の限界を定理として確定させた**、Nullstellensatz 型の教訓である: 述語は方程式を決めない。係数なしにコホモロジーなし。

### 第 5 幕(Cycle 348–352): laws-as-equations

2026-07-02、ユーザーが入力語彙の拡張を決断した: **law は方程式である**。拡張は外部からの借用ではなく、canonical 数学本文の第 III 部(LawAlgebra: violation witness 座標、witness ideal、lawful locus、Correspondence)の再利用であり、形式化が本文の編集意図に追いついた形になった。

- **Cycle 348**(PR #2898): `SemanticLawEquationWitnessIdealCore/Geometry` — ring 値 observable presheaf + atom-indexed violation 座標 + 座標の restriction 互換。obstruction 係数を商 presheaf `O/I_Ob` として生成し(functoriality は `Ideal.quotientMap` + `map_localObstructionIdeal_le` で証明)、interpret を defect の商 class として生成。**evaluator が定理として落ちた**。GOAL カードの ambient ledger 改訂(ユーザー承認)。
- **Cycle 349**(PR #2899): 具体有限 instance での `quotientIsSheaf` 放電(FiniteModel singleton site 上では任意 presheaf が sheaf — `Precoverage.isSheaf_toGrothendieck_iff` 経由)と、非退化 witness(defect `1` の class ≠ 0、violation 座標の class = 0)。
- **Cycle 350**(PR #2900): end-to-end composition `lawEquation_constructs_groundedComparisonPacket` — 二本の証明 track を生成 cover 上で接合し、gate 層 `SelectedSemanticCoefficientDirectRealizationLayer` を inhabit。**final review は rejected**(下記)。
- **Cycle 351**(PR #2901): 査読 obligation 1/3 の放電 — degree-0 境界定理 2 本と、FiniteModel 上の具体 end-to-end bundle の構成・発火。
- **Cycle 352**(PR #2901): 査読 obligation 2 の放電 — selected 円 nerve(頂点 2・辺 2、係数 = law-equation 商)上で非零 residual class を構成し(非零性は Cycle 349 の witness に帰着)、zero-predicate equivalence の双方向非零転送を実証。

## 5. 査読の記録 — veto が定理を生んだ

`$math-lean-review` 型の 4 レーン敵対査読を 2 回実施した。

**Cycle 350 後(rejected)**: 数学レーン A が veto。(1) packet の `H1` 零 conjunct 群は `residual := K.d 0 primitive` の定義と零 base section により law と無関係に構成的に真であり、law 意味論の Cech 面への到達点は degree-0 消滅である。(2) end-to-end 仮定クラスの具体 instance が未構成。— この veto は正しく、G-05 の運用(reject を report に固定し次サイクルの義務にする)に従って 3 obligation が記録された。

**Cycle 352 後(accepted)**: veto を出したレーンによる再審は「2 つの veto は、前回査読自身が定めた救済 obligation の文言どおりに Lean 定理として解消された」と判定。特筆すべきは、veto への応答が主張の切り下げではなく**新しい定理**だったことである — 「law 意味論の寄与は degree-0 消滅である」という正の境界定理(`..._sourceC0_pointwise_zero`)と「grounded route conjunct 群は law 非依存である」という負の境界定理(`lawEquation_groundedRoute_isLawIndependent`)。理論はこの査読を通じて自分自身についての知識を一段深めた。

## 6. 主要 Lean 成果物

置き場所: `Formal/AG/Research/QualitySurface/`

- `SemanticRepairCechGrounding.lean` — 352 サイクルの本体(site/topology bridge、comparison、zero-predicate equivalence、boundary theorems、no-go 定理群、一点圧縮の等価類)
- `SemanticRepairLawEquationRealization.lean` — laws-as-equations 層(witness ideal、商係数生成、消滅定理、evaluator 定理化、detector soundness)
- `SemanticRepairLawEquationWitnessInstance.lean` — 具体有限 instance(sheaf 条件放電、非退化 witness)
- `SemanticRepairLawEquationGroundedPacket.lean` — end-to-end composition と gate 層 inhabit
- `SemanticRepairLawEquationEndToEndInstance.lean` — degree-0 境界定理、FiniteModel 上の発火 instance
- `SemanticRepairLawEquationNonzeroClassInstance.lean` — 円 nerve、非零 class 転送 packet

全宣言は標準公理(`propext`, `Classical.choice`, `Quot.sound` の部分集合)のみに依存し、`sorryAx` なし。

## 7. 境界 — 語らないこと

SAGA 定理は次に相対化されている(正本は GOAL カード): 有限/small atom-supported AAT site、selected cover、law-equation witness-ideal realization(ambient 入力語彙)、Lean で discharge された各種条件。次は**主張しない**: 任意 Grothendieck site への無条件一般化、full sheaf cohomology との無条件同一視(boundary theorem で遮断済み)、cover refinement / naturality の無条件版(反例で遮断済み)、extraction completeness、実コード全体の品質判定。

accepted final review packet に記録された boundary notes: 円 nerve は selected simplicial data であり atom-level 交叉からの生成は主張しない。円 comparison は identity comparison である。witness site は退化(singleton contexts)。lawful instance(零 class)と nonzero instance は別 witness であり混同しない。law 意味論の Cech 寄与は degree-0 消滅である(これ自体が定理)。いずれも optional hardening であって本 GOAL の義務ではない。

## 8. 開いた問い — G-04 へ

degree-0 境界定理が最も面白い未踏部を指している。現在の意味論では lawful な読みは商で零になる — 「law の充足」は `H0` 的に働き、`H1` の非自明な内容は被覆の幾何から来る。では**相異なる非零の lawful 読みが非自明に貼り合う**係数はどう作るか。第 IV 部に既に置かれている conormal `I/I²`(`ConDef_U`)がその自然な候補であり、これは G-04(nonabelian `H1`、`H2`、stacky descent、universality)の入口の問いと重なる。SAGA 定理は G-04 の地盤であると同時に、G-04 が何を問うべきかの精密化を残して閉じた。

## 9. 台帳参照

- PR: [#2898](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/2898)(C348)、[#2899](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/2899)(C349)、[#2900](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/2900)(C350 + rejected review)、[#2901](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/2901)(C351/352 + accepted review)、[#2902](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/2902)(completion processing)
- 完了台帳: `research/goals/G-aat-quality-surface-06.md`(completed カード)、`docs/aat/proof_obligations.md`(research target-theorem 台帳)
- Cycle 1–347 の詳細は `research/reports/G-aat-quality-surface-06.md` を正とする
