# AAT代数幾何版 Lean形式化 PRD-10: 第X部 Semantic Repair Descent と SAGA 比較定理(蒸留移植)

対象本文: [第X部 Semantic Repair Descent と SAGA 比較定理](algebraic_geometric_theory/part_10_semantic_repair_descent_saga.md)
(付録 [B.9 Law-Equation Coefficient and Circle Nerve Worked Example](algebraic_geometric_theory/appendix.md) を含む)

先行PRD:
[PRD-1 第I部](lean_ag_part_1_atoms_objects_laws_prd.md) /
[PRD-2 第II部](lean_ag_part_2_sites_sheaves_prd.md) /
[PRD-3 第III部](lean_ag_part_3_law_algebra_lawful_locus_prd.md) /
[PRD-4 第IV部](lean_ag_part_4_obstruction_cohomology_prd.md) /
[PRD-5 第V部](lean_ag_part_5_derived_law_geometry_repair_prd.md) /
[PRD-6 第VI部](lean_ag_part_6_singularity_monodromy_stack_prd.md) /
[PRD-7 第VII部](lean_ag_part_7_representation_periods_analysis_prd.md) /
[PRD-8 第VIII部](lean_ag_part_8_measurement_theory_prd.md) /
[PRD-9 第IX部](lean_ag_part_9_evolution_geometry_prd.md)

移植元 evidence(research 成果、正典ではない):
`Formal/AG/Research/QualitySurface/`(受理済み theorem package 群 = G-02 / G-05 / G-06、
およびそれらが import する QualitySurface 基盤ファイル。G-01 / G-04 は active な GOAL であり、
その evidence は移植スパインが依存する範囲でのみ参照する)、
[research/reports/G-aat-quality-surface-06.md](../../research/reports/G-aat-quality-surface-06.md)、
[SAGA 証明記録](../note/aat_saga_theorem_proof_record.md)

## 問い

研究サンドボックスで受理された SAGA 定理群(G-02 / G-05 / G-06)は、
研究 evidence としてではなく、**本体の塔の第10層**として立ち上がるか。
すなわち、第X部の supplied / generated 規律に忠実な形で、

```text
semantic projection (Λ, K, π)
  -> finite semantic repair-gluing complex 𝔎, descent(定理3.4)
  -> semantic repair additive H^1 = Z^1/B^1(定理4.8)
  -> generated coefficient Q = O / I_Ob(第III部 定理11.4)
  -> atom-generated site / Čech 橋(§6: 定理6.1、定義6.2–6.3、定理6.4–6.6)
  -> SAGA 比較 H^1_semantic ≅ H^1(𝒰, Q)(定理7.2/7.3)
  -> end-to-end 発火と非零 class 転送(定理7.4/7.5、例9.1/9.2)
```

の連鎖が、`Formal/AG` 本体(namespace `AAT.AG`、default build、no-sorry / no-axiom)
の中に、Research 由来の作業足場を持ち込まずに sorry なしで存在するか。

特に、次を機械検証できるか。

- 第X部の [Certified bounded inference] 6定理(3.4 / 4.8 / 7.2 / 7.3 / 7.5 / 8.1)が
  本体の定理として証明されていること。
- 本体 `Cohomology` / `Site` がデータ仮置きにしていた法則
  (標準 Čech 微分、`d∘d = 0`、cochain 比較からの `H^1` 同値)が、
  Research 側で証明済みの canonical 構成の吸収により**定理化**されること。
- 反例型境界定理(6.4 / 8.4 / 8.5)が、反例 witness の構成と否定命題の二段として
  本体に存在すること。

採否規律: 蒸留移植の対象は、(a) 第X部ラベルの処遇表で「定義」「証明」「例 theorem」と
指定された宣言、(b) それらが依存する移植スパイン(後述のホワイトリスト、
依存グラフで確定する)、(c) 重複統廃合(R1)で本体へ吸収される canonical 構成、
の三つに限る。Research の premise 順列 no-go 帯・iff 格子の中間ノード・
サイクル checkpoint 帯は移植しない。移植で statement を本文より弱める・強めることは
禁止する(anti-weakening は G-06 受理時の査読 lane と同じ規律)。実装中に、
移植スパインが本体の語彙で書き直せない、または第X部の主張と Research の
Lean statement が一致しないことが見つかった場合、それは本文・Research evidence・
本PRD のいずれかの欠陥であり、ループを停止して報告する。

## 中心方針

PRD-1〜9 の方針(塔を下から積む / 忠実性契約 / `Formal/AG` 実装 /
`axiom`・`admit`・`sorry`・`unsafe` 禁止 / Mathlib 二段橋 / 台帳統合 /
部番号付き台帳ラベル)を引き継ぐ。本PRDで新たに加わる方針が七つある。

**(1) これは新規形式化ではなく蒸留移植である。**

第X部の Lean 実体は `Formal/AG/Research/QualitySurface/` に受理済みで存在する
(sorry なし、標準公理のみ、G-02 / G-05 / G-06 として `target-theorem-proved`)。
本PRDの作業は「証明を書く」ことではなく、**約12.2万行の research evidence から
載荷経路上の宣言(実測で約60〜100宣言+その依存)だけを切り出し、本体の語彙・
規約で書き直す**ことである。`Formal.AG.Research` を本体から import することは
統合とみなさない(禁止)。`FormalAGResearch` lib を default build に載せることも
統合とみなさない(禁止)。

**(2) ホワイトリスト先行、依存グラフで切り出す。**

`SemanticRepairCechGrounding.lean`(50,184行)は namespace の多重再オープンと
Cycle 挿入により、行範囲でも時系列でも分割できない。移植は
「最終 package(定理7.3 = `trueSheafBoundaryRelationAdditive_coverRelativeH1Zero_effectiveGluing_package` 相当、
定理7.5 = `lawEquation_constructs_groundedComparisonPacket` 相当)から逆向きに辿った
宣言依存グラフ」を唯一の基準とする。本PRD末尾の移植スパイン初期リストを
出発点とし、ループの最初のタスクでこれを機械的に確定する(R0)。

**(3) no-go は二種類あり、扱いを分ける。**

- 本文の「Is Data」定理(6.4 / 8.4 / 8.5)と carrier 比較の非一様性に対応する
  **canonical no-go(代表6〜8本)は本文ラベルの実体であり、移植する**。
- premise 順列を1つずつ伸ばした再主張帯(約60〜70本)と `of_X_via_Y` 再入口
  変種(約30本)は**サイクル足場であり、移植しない**。

**(4) 重複統廃合は「本体のデータ仮置きフィールドの定理化」として行う。**

Research は本体の Čech / 被覆 / 有限 poset 型を再定義しておらず、本体型を
import して消費し、本体が structure フィールドとして仮置きしていた法則
(`differential`、`differential_comp`、cohomology 比較)の canonical instance を
**構成・証明**している。統合の本丸は名寄せではなく、この canonical 構成を
本体 `Site` / `Cohomology` へ吸収することである(R1)。吸収は**追加的宣言**
(新 structure + 変換 def + canonical instance + 定理)で行い、既存本体宣言の
シグネチャは凍結する。特に `finitePosetCoverRelativeCover`
(`Formal/AG/Cohomology/FinitePosetComparison.lean:22`)、
`FinitePosetAATSiteRegime`、`FinitePosetCechComplex`、
`CoverRelativeCechCover` / `CoverRelativeCechComplex` の型変更は Research 側
5万行に波及するため禁止する。完了条件として `lake build`(default)と
`lake build FormalAGResearch` の**両方**が green であることを課す。

**(5) supplied / generated を型設計に写像する。**

第X部は全主張を supplied(入力として与えられ適合条件で拘束されるデータ)と
generated(入力から構成され証明されるもの)の二語で規律する。Lean では
supplied = structure フィールド、generated = def / theorem として写像し、
docstring に本文ラベル(`X.定義3.1` 等)とともに supplied / generated の別を記す。
定理の結論に現れる構造を supplied certificate として受け取らない
(comparison data が結論を格納しない、という定義7.1 の規律を全層で維持する)。

**(6) law-grounded content の境界は docstring ではなく Lean 定理で維持する。**

定理7.5 の10結論のうち law に依存するのは正確に次数0の3結論
(displayed interpretation 実現 / restriction evaluator / 生成 0-cochain の Čech 零)
のみであり、`H^1` zero 結論を law-grounded descent として引用することは
定理8.2(`lawEquation_groundedRoute_isLawIndependent` 相当)が Lean の定理水準で
禁止している。移植後もこの二定理(8.1 / 8.2)を必ず本体に持ち、
台帳・docstring の記述をこの境界に従わせる。

**(7) 受理時の boundary notes を非主張として引き継ぐ。**

G-06 受理時の final review packet の boundary notes(identity comparison /
selected circle nerve / degenerate witness site / law-equation ambient rows)は、
移植後も claim boundary として台帳の非主張に記録する。これらの解消
(非恒等 comparison での転送、atom-generated な非零 instance 等)は本PRDの
義務ではなく、補強PRD(PRD-R)の任意 hardening 項目である。

## 背景

- 第X部本文(PR #2907)は 2026-07-04 に正典化されたが、対応する Lean は
  隔離 lib `FormalAGResearch` にのみ存在し、CI の default build に載っていない。
  本体台帳(`lean_theorem_index_ag_aat.md` / `proof_obligations_ag_aat.md`)には
  第X部の行が存在せず、第I〜IX部と異なり本文ラベル↔Lean 宣言の対応が追跡できない。
- G-06(SAGA)は 352 サイクル・約975宣言の登攀の成果だが、下流の受理ルートが
  実際に名前参照する宣言は細い柱(実測で約57+α)である。全量移植は5万行の
  足場を本体に持ち込むことになり、正典の可読性と保守性を毀損する。
- 本体 `Cohomology/CechComplex.lean` は `differential` と `differential_comp`
  (d∘d=0)をデータフィールドとして持ち、`FinitePosetComparisonTarget` /
  `FinitePosetCechComparisonData` は cohomology 比較写像までデータで要求する。
  Research 側にはこれらを標準交代和・自由 tuple nerve・cosimplicial 恒等式から
  **証明**する canonical 構成が完備している。この吸収は第X部の移植であると同時に、
  第IV部形式化の最大の弱点(査読耐性監査で優先度A)の解消でもある。
- 依存の向きは統合に整合的である: Research → 本体(`Site` / `LawAlgebra` /
  `Cohomology` / `Examples.FiniteModel`)の一方向 import のみで、循環はない。
- 第X部 §5 は第III部 定義11.3 / 定理11.4(laws-as-equations、witness ideal、
  生成商係数、restriction evaluator)に依存する。この Lean 実体
  (`SemanticRepairLawEquationRealization.lean`)も Research 側にのみ存在し、
  本文が [Certified bounded inference] を付す第III部の到達点が本体に不在という
  逆転が起きている。本PRDはこれを第III部の本体モジュールへ吸収する(R5)。

## アウトカム

本PRDの完了時点で、次が成り立つ。

1. `Formal/AG/SemanticRepair/` が新設され、第X部の全処遇対象ラベルが
   namespace `AAT.AG.SemanticRepair` の下に sorry なしで存在し、CI の
   default build でビルドされる。
2. [CBI] 6定理(3.4 / 4.8 / 7.2 / 7.3 / 7.5 / 8.1)が本体の定理として証明され、
   台帳で `X.定理N.M` ラベルから宣言単位に追跡できる。
3. 本体 `Site` / `Cohomology` に標準有限 poset Čech 複体の canonical 構成
   (標準交代和微分、d∘d=0 の証明、cover geometry からの end-to-end 生成)と
   「cochain 水準比較 ⇒ H^1 同値」の一般定理が存在し、データ仮置き版
   comparison interface が定理により充足可能になっている。
4. 例9.1(lawful firing)と例9.2(circle nerve 非零 class 転送)が
   `Formal/AG/Examples/` の example theorem として発火し、本体の
   `CoverRelativeCechComplex` に対する初の無条件非零 `H^1` class 実例を与える。
5. 第III部 定義11.3 / 定理11.4 の Lean 実体が `Formal/AG/LawAlgebra/` に存在し、
   第III部台帳に登録されている。
6. 両台帳に第X部セクションが新設され、「PRD-1〜9」表記が入口ファイルと
   分割台帳ヘッダの計4箇所で「PRD-1〜10」へ更新され、research 台帳に
   正典昇格の pointer が記録されている。
7. `Formal.AG.Research` は本体から import されないまま残り(evidence 凍結)、
   `lake build FormalAGResearch` も green を維持している。

## 第X部ラベルの処遇表

ギャップ分析はこの表を基準に行う。「証明」は sorry なしの theorem、
「定義」は structure / def としての形式化、「例 theorem」は具体 instance 上の
発火定理を要求する。「移植元」列は Research 側の対応宣言(参考情報であり、
名前・分割は本体規約に合わせて変えてよい。statement の弱化・強化は不可)。

| 本文ラベル | 処遇 | 移植元(Research)と備考 |
| --- | --- | --- |
| §1 supplied/generated 規律 | 対象外 | 型設計規約として中心方針(5)に反映。docstring 規約 |
| 定義2.1 Semantic Atom Projection | 定義(一般化) | `SemanticSupportProjectionKernel` の projection 語彙。Research は `K = BridgeComponent` 固定・組を束ねる structure なし。本体版は component vocabulary を型パラメータ化した組 `(Λ, K, π)` の structure として定義する(R2) |
| 定義2.2 Semantic Residual Atom | 定義(一般化) | `SemanticProjectedResidual` + cover datum。`HandoffCechCover` は Research 固有語彙なので、holonomy support `R(𝒰) ⊂ K` を持つ generic な有限 cover datum として再定義する(R2) |
| 定義2.3 Repair Support / Semantic Closure | 定義 | `SemanticRepairClosed`(R2) |
| 定義2.4 Coverage / Faithfulness | 定義 | `ResidualComponentCoveredSupport` / `ResidualComponentFaithfulSupport`(R2) |
| 補題2.5 Closure Decomposition | 証明 | `semanticRepairClosed_iff_residualComponentCovered_and_faithful`(R2) |
| 例2.6 Coverage Without Faithfulness | 例 theorem | t/s/o 3元 atom と alias projection の負例。`surfaceRepairSupport_componentCovered_not_faithful` 等(R2/R9) |
| 定義3.1 Finite Semantic Repair-Gluing Complex | 定義 | `FiniteSemanticRepairGluingComplex`。列挙の完全性はデータの一部、δ⁰ の restriction-difference 律は supplied 条件(R3) |
| 定義3.2 境界所属と GlobalCoherent | 定義 | `B1` / `ObstructionClassVanishes` / `GlobalSemanticRepairCoherent`。§3 では `H^1` を名乗らない(R3) |
| 定義3.3 Semantic Faithfulness Hypothesis | 定義 | `SemanticFaithfulnessHypotheses`(R3) |
| 定理3.4 Finite Semantic Repair-Gluing Descent [CBI] | 証明 | (i) 無条件 necessity + 対偶 / (ii)(iii) 仮説下。`globalRepairCoherent_forces_obstructionVanishes`、`no_globalRepairCoherent_of_nonzero_obstruction`、`globalRepairCoherent_of_obstructionVanishes`、`finiteSemanticRepairGluingDescent_iff`。(i) と (ii)(iii) の条件非対称を保つ(R3) |
| 定理3.5 Complete-Support Faithfulness | 証明 | `CompleteRepairSupportBoundaryComplex` + 仮説の定理化 + 族内無条件同値。正典放電経路は GluingComplex 直接版とし、AdequacyDischarge の certificate 経由は補助定理として移植可(R3) |
| 例3.6 Component Coverage Is Not Closure | 例 theorem | `selectedVisibleLocalWitnessComplex` + `obstructionNonzero` + `noGlobalRepairCoherent` + 可視局所整合の検証命題(R3/R9) |
| 定義4.1 Finite Repair Cover / Cover Nerve | 定義 | `SemanticRepairCover` + `toCoverNerve`(第IV部 定義12.1 の 2-骨格版)(R4) |
| 定義4.2 Čech 型係数データ | 定義 | `SemanticRepairCoverCechData(WithZero)` / `SemanticResidualCoefficientSheaf`。定義3.1 と異なり列挙完全性を要求しない。δ⁰/δ¹ は supplied(R4) |
| 定義4.3 Additive Regime | 定義 | `SemanticRepairAdditiveCechH1Data` / `SemanticRepairCoverH1BoundaryRelationAdditiveData`(R4) |
| 定義4.4 Semantic Repair Additive H^1 | 定義+証明 | additive `Z^1/B^1` 商。同値関係の反射・対称・推移と `[c]` の well-definedness は定義に付随する証明義務(R4) |
| 補題4.5 Quotient Zero Reading | 証明 | `semanticRepairAdditiveH1Zero_iff_boundary`(R4) |
| 定義4.6 Boundary-Relation Faithfulness Data | 定義 | `SemanticRepairCoverH1BoundaryRelationAbelianData`(z / Q / faithfulness law、大域選択子なし)(R4) |
| 定義4.7 True Sheaf Certificate | 定義 | `SemanticRepairCoverH1(BoundaryRelation)TrueSheafConditionCertificate`(cover membership + global sheaf condition)(R4) |
| 定理4.8 True Sheaf H^1 Semantic Repair-Gluing [CBI] | 証明 | 最終形は boundary-relation additive package(結論5「上位層は構成から自明」を外部仮定でなく構成から放電する経路)。torsor/higher/stack 消滅を外部仮定に取る旧経路は正対応ではない(R4) |
| 命題4.9 Finite Complex Shadow | 証明 | `SemanticRepairG02FiniteComparison` + `coverEnvelope_sheafH1Zero_iff_g02ObstructionVanishes`(R4) |
| 命題4.10 Refinement Pullback(片方向) | 証明 | `SemanticRepairCoverRefinement` + `RefinementComparison` + pullback 2定理。逆方向は定理8.5 が遮断(非主張)(R4) |
| §5 前文(第III部依存の宣言) | 定義+証明(第III部へ吸収) | `SemanticLawEquationWitnessIdealCore` / witness ideal 生成 / restriction 互換 / `Q = O ⧸ I_Ob` 生成 / functor 法則の証明 / evaluator 定理を `Formal/AG/LawAlgebra/` へ。台帳は第III部節(定義11.3 / 定理11.4)にも行を追加(R5) |
| 定義5.1 Law Equation Grounded Surface | 定義 | 5成分: (a) finite poset atom/law cover geometry(R1 で本体吸収)、(b) skeleton、(c) defect source(`LawEquationDefectSemanticAtomLawInputBoundarySource`)、(d) incidence bridge、(e) quotient sheaf condition。(e) の二相性(一般=supplied 仮定 / 例9.1 の class では定理)を型で保つ(R5) |
| 意味5.2 Coefficient Is Generated | 対象外(定理群として実現) | 実体は R5 の生成定理群(`obstructionQuotientCoefficient` の functor 法則、interpret の商 class 生成、`interpret_eq_zero_iff_defect_mem_obstructionIdeal`)。docstring と `X.定義5.1` 行の意味欄・Non-conclusions 段落で記録し、独立のラベル行は作らない |
| 定理6.1 Coverage Generation Bridge | 証明 | `atomGeneratedCoverage_generates_AATGrothendieckTopology` + topology 一致(R6) |
| 定義6.2 Selected Simplicial Čech Complex | 定義(既存本体 + R1(a) canonical 構成) | 本体 `CoverRelativeCechCover` / `CoverRelativeCechComplex` は微分と d∘d=0 をフィールド供給する器であり、本文の「微分 = 面への制限の交代和(generated)」の実体は R1(a) が吸収する標準交代和 canonical 構成(`standardFinitePosetCechComplex` 相当)が担う。台帳の `X.定義6.2` 行は両者を併せて引用する(R1/R6) |
| 定義6.3 Repair Cover Incidence Bridge | 定義 | `SemanticRepairCoverRelativeCoverBridge`(chart/overlap/triple → 0/1/2-単体の provenance)(R6) |
| 定理6.4 Incidence Is Data | 証明(反例+肯定の二段) | 否定半分 = 空 Index 反例の no-go 代表、肯定半分 = `CoverRelativeCechChartIndexedZeroCover` からの構成(R1/R6) |
| 定理6.5 Cover Nerve Provenance | 証明 | `coverNerve_typedComponent_adequacy`(R6) |
| 定理6.6 Descent Is Derived | 証明 | `aatSheafCondition_coverMembership_descent_effectiveGluing`(sheaf 条件 + cover membership → descent / gluing の導出)(R6) |
| 定義7.1 H^1 Comparison Data | 定義 | `SemanticRepairCoverRelativeH1Comparison`(+強形 `CochainRealization`)。結論を格納しない規律を維持(R7) |
| 定理7.2 SAGA 比較定理 [CBI] | 証明 | cocycle 対応 / coboundary 対応 / 商水準 H^1 同値(equiv は定理として構成)/ zero-predicate equivalence + package。一般形に有限性仮定を混入させない(R7) |
| 定理7.3 Grounded Global Gluing [CBI] | 証明 | 定理4.8 + 定理7.2 + gluing data から `GlobalCoherent ⇔ cover-relative residual H^1 zero` を含む結論束(R7) |
| 定理7.4 Nonzero Class Transfer | 証明 | zero-predicate equivalence の対偶 + circle instance での発火(R7/R9) |
| 定理7.5 Generated End-to-End Realization [CBI] | 証明 | `lawEquation_constructs_groundedComparisonPacket` 相当(10結論)。law 依存は結論1〜3のみという内部境界を statement 構造で保つ。基幹 route(Cycle 332)は蒸留・分解して移植(R7) |
| 原則7.6 SAGA Is Not AAT-GAGA | 対象外 | 命名と責務境界。docstring と台帳非主張に記録 |
| 定理8.1 Degree-Zero Law Contribution [CBI] | 証明 | `displayedRequiredLawsHoldOn_constructs_sourceC0_pointwise_zero`(各点零)+ Čech 零への微分の影(R8) |
| 定理8.2 Law-Independence of the Grounded Route | 証明 | `lawEquation_groundedRoute_isLawIndependent`(law 前提なしで結論4〜10を証明)(R8) |
| 意味8.3 Where Law Semantics Lives | 対象外 | 定理8.1/8.2 の帰結の読み。conormal 係数 `I_U/I_U²` の読みは本文の open question であり、台帳に future proof obligation として記録(形式化しない) |
| 定理8.4 Full Sheaf Comparison Is Data | 証明(データ+反例の二段) | 比較データ structure + データ相対化定理 + 空ターゲット反例(無条件比較の不存在)(R8) |
| 定理8.5 Refinement Naturality Is Data | 証明(データ+反例の二段) | refinement 比較 structure + データ相対化定理 + coarse 零 / fine 非零反例(R8) |
| 例9.1 Lawful Firing Instance | 例 theorem | 有限モデル site の全 presheaf sheaf 条件定理 + `quotientIsSheaf` の定理化 + end-to-end packet の発火。defect class 零は定理8.1 の帰結(R9) |
| 例9.2 Circle Nerve Nonzero Class | 例 theorem | circle nerve cover + 係数 `Q ≅ F₂`(witness ideal `(2) ⊂ ℤ`)+ `residual_not_coboundary`(1 ∉ (2) に帰着)+ 両側非零 + transfer packet(R9) |
| §10 結論 | 対象外 | まとめ。台帳には登録しない |

処遇表の付随規律:

- 「証明の読み」2箇所(定理3.4 直後 / 定理4.8 直後)は形式化対象外。証明方針の
  docstring として反映してよい。
- canonical no-go 代表(定理6.4 否定半分、carrier 比較非一様性の有限反例
  `PUnit`/`ZMod 2` 対、定理8.4/8.5 の反例、fail-closed 締め2本)は本文ラベルの
  実体として移植する。それ以外の no-go は移植しない。
- explicit 版 envelope(`cohomologous` 関係による `SemanticRepairSheafH1Envelope`
  経路)は本文 §4 に対応節を持たない。additive 版を正として移植し、explicit 版は
  移植しないか、必要な場合のみ補助定義として持つ(台帳には載せない)。

## 要求

### R0. 立ち上げ・移植スパイン確定・二重ビルド規律

- `Formal/AG/SemanticRepair/` を新設する。ファイル分割は本文の節構成に概ね
  対応させる。例: `Projection.lean`(§2)、`GluingComplex.lean`(§3)、
  `AdditiveH1.lean`(§4)、`CechBridge.lean`(§6)、`Comparison.lean`(§7)、
  `Boundary.lean`(§8)。§5 の係数生成は `Formal/AG/LawAlgebra/LawEquation.lean`
  (仮)へ、§9 は `Formal/AG/Examples/SemanticRepairPart10.lean` へ。
- namespace は `AAT.AG.SemanticRepair`(§5 吸収分は `AAT.AG.LawAlgebra` 配下)。
  `Formal.AG.Research.*` の namespace を本体に持ち込まない。
- `Formal/AG.lean` に新モジュールの import を追加し、CI の default build に載せる。
  `Formal.AG.Research` への import は追加しない。
- ループの最初のタスクとして、本PRD末尾の移植スパイン初期リストを起点に、
  受理ルートの宣言依存グラフを機械的に確定し(rg + import 追跡)、確定版
  ホワイトリストを tracking Issue に記録する。以後のギャップ分析はこの
  確定版を基準にする。
- 完了条件: 空でない最初のモジュールが CI でビルドされ merge されている。
  以後の全タスクで `lake build` と `lake build FormalAGResearch` の両方が green。

### R1. 重複統廃合 — 本体 Site / Cohomology への canonical 構成の吸収

Research が証明済みの canonical 構成を、本体のデータ仮置き interface の
充足定理として吸収する。既存本体宣言のシグネチャは凍結し、吸収は追加的宣言で行う。

- (a) **標準有限 poset Čech 複体**: canonical tuple nerve
  (`Fin (n+1) → Index` 型 simplex、`SimplexCategory` の coface 恒等式による
  face 作用)、標準交代和 differential、cosimplicial double-face cancellation
  による `d∘d = 0` の証明、cover geometry と obstruction sheaf だけから本体
  `FinitePosetCechComplex` / `CoverRelativeCechComplex` を end-to-end に生成する
  ルート(`standardFinitePosetCechComplex` / `atomLawOverlapCoverRelativeCechComplex`
  相当)を、`Formal/AG/Site/FinitePosetStandardComplex.lean`(仮)へ移植する。
  Research の `FinitePosetAtomLaw...Law` 系中間 record は畳み、最終構成と
  必要補題だけを残す。
- (b) **coefficient-free cover geometry**: `FinitePosetAtomLawCoverGeometry`
  (本体 `FinitePosetAATSiteRegime` から `coefficient` を外した一般化)と
  `toObstructionCoefficientRegime` 変換を本体 `Site` 側へ追加する。
  既存 `FinitePosetAATSiteRegime` は変更しない。
- (c) **cochain 比較 ⇒ H^1 同値の一般補題**: 「3-term additive complex 間の
  次数1往復 + 減法互換 + 微分互換 + 次数2 zero 保存」だけから商水準の
  `H^1` 同値・zero-predicate 同値を導出する一般定理を、semantic 語彙に依存しない
  形で `Formal/AG/Cohomology/` へ置く。既存のデータ仮置き版
  (`FinitePosetComparisonTarget` / `FinitePosetCechComparisonData` の
  cohomology フィールド群)には「この定理で充足できる」旨の構成 def を添える
  (deprecate はするが削除はしない)。
- (d) **chart-indexed zero cover**: `CoverRelativeCechZeroSimplexChartIncidence`
  と `CoverRelativeCechChartIndexedZeroCover`(0-単体 = chart 添字の definitional
  特殊化)+ 素の cover からは incidence が導出できないことの no-go 代表を
  本体 `Cohomology/CechComplex.lean` 近傍へ吸収する(定理6.4 の実体)。
- (e) **ObstructionSheaf の生成 constructor**: `AddCommGrpCat` 値 presheaf から
  `map_zero` / `map_add` を定理として得る constructor(`ofAddCommGrpValued` 相当)
  を本体 `Cohomology/ObstructionSheaf.lean` へ追加する。
- 完了条件: (a)–(e) が sorry なしで存在し、既存本体宣言のシグネチャ変更ゼロ、
  両ビルド green。

### R2. §2 semantic projection 層(定義2.1–2.4、補題2.5、例2.6)

- `(Λ, K, π)` を束ねる structure を、component vocabulary `K` を型パラメータと
  する generic な形で定義する(Research の `BridgeComponent` 固定を一般化)。
- 有限 cover datum(chart 族 / 遷移データ / holonomy support `R(𝒰) ⊂ K`)を
  generic に定義し、`Res(π,𝒰) = π⁻¹(R(𝒰))`、semantic closure、coverage、
  faithfulness の述語を移植する。residual は「生値であり判定ではない」ことを
  docstring に記す。
- 補題2.5(closed ⟺ covered ∧ faithful)を移植する。
- 例2.6 の負例(3元 atom、alias projection、`S = {t, s}`)を instance として
  移植し、covered ∧ ¬faithful ∧ ¬closed を証明する。
- 一般化により Research 側の証明が通らない場合は、その箇所を特定して
  ループを停止し報告する(本文は `K` を任意集合とするため、一般化の失敗は
  本文か evidence の欠陥である)。
- 完了条件: §2 の全ラベルが sorry なしで存在する。

### R3. §3 gluing complex と descent(定義3.1–3.3、定理3.4、定理3.5、例3.6)

- `FiniteSemanticRepairGluingComplex` を R2 の generic 語彙の上で移植する。
- 定理3.4 を (i) 無条件 / (ii)(iii) 仮説付きの構造を保って移植する。
  package 形(必要性・対偶・十分性・同値・bridge・witness 検証の束)は
  移植してよいが、台帳には (i)(ii)(iii) の別で登録する。
- 定理3.5 の complete-support 族と放電定理、および正例 instance を移植する。
- 例3.6 を移植し、「可視の局所整合はすべて成立するが `r ∉ B¹`」の検証命題を
  含める。
- 完了条件: 定理3.4(i) が無条件で、(ii)(iii) が `SemanticFaithfulnessHypotheses`
  下で証明され、定理3.5 が族内で仮説を放電している。

### R4. §4 additive H^1(定義4.1–4.7、補題4.5、定理4.8、命題4.9/4.10)

- `SemanticRepairCover`(有限列挙付き)と `toCoverNerve` を移植する。
- Čech 型係数データ・additive regime・additive `Z^1/B^1` 商を移植する。
  定義4.4 に付随する証明義務(同値関係の性質、well-definedness)を
  補題として明示する。
- 定義4.6(boundary-relation faithfulness data)と定義4.7(true sheaf
  certificate、global sheaf condition + cover membership)を移植する。
- 定理4.8 は boundary-relation additive package を正典として移植する。
  結論1(cover sheaf condition と descent の導出)、結論2(cocycle 性)、
  結論3(descent 同値)、結論4(quotient reading)、結論5(上位層の構成的
  放電)の5結論が本文の書き分けどおり statement に現れること。
  結論3が結論1からでなく faithfulness data と additive regime から導かれる
  という証明構造を docstring に記す。
- 命題4.9(§3 複体との shadow 一致)と命題4.10(refinement pullback 片方向)を
  移植する。
- 完了条件: 定理4.8 package が sorry なしで証明され、上位層(torsor / higher /
  stack)の消滅を外部仮定として受け取っていない。

### R5. §5 係数の生成 — 第III部 定義11.3 / 定理11.4 の本体化

- `SemanticLawEquationWitnessIdealCore`(observable presheaf、violation
  coordinates、restriction 互換、support / required law)を
  `Formal/AG/LawAlgebra/` へ移植する。既存 `ObstructionIdeal.lean` の
  `SelectedLawWitnessIdealFamily` / `localObstructionIdeal` 語彙に接続する。
- 生成定理群を移植する: `lawWitnessIdeal` の span 構成、
  `map_lawWitnessIdeal_le` / `map_obstructionIdeal_le`(restriction 互換)、
  `ObstructionQuotient = O ⧸ I_Ob` と `obstructionQuotientCoefficient`
  (functor 法則は証明)、interpret の商 class 生成、
  `interpret_eq_zero_iff_defect_mem_obstructionIdeal` 型の vanishing
  (ideal 所属としての読み、第III部 原則5.6 no-cancellation)、非退化側、
  検出器 soundness、restriction evaluator 定理、grounding packet。
- defect source(displayed local reading + chart-local law-defect tie。
  `interpret` フィールドを持たない)と、二相性を持つ
  `quotientIsSheaf`(一般 = supplied)を移植する。
- 台帳: 第III部節に `III.定義11.3` / `III.定理11.4` の行を追加し、第X部節の
  `X.定義5.1` 行から参照する(意味5.2 は独立行を作らず、同行の意味欄と
  Non-conclusions 段落で記録する)。
- Cycle 347 no-go(任意 support-only source への base-restriction 構成は不可、
  正の構成は law-equation 実現生成の source のみ)は claim boundary として
  台帳に記録する(no-go 定理自体の移植は canonical 代表1本まで)。
- 完了条件: 定理11.4 相当の生成定理群が本体で証明され、第III部台帳に
  登録されている。

### R6. §6 Atom-Generated Site と Čech 橋(定理6.1、定義6.3、定理6.4–6.6)

- 定理6.1: atom-generated admissible coverage の生成篩が `J_U` の cover であり
  topology が一致することの定理を移植する。
- 定義6.3: repair cover → cover-relative Čech cover の incidence bridge
  (provenance data)を移植する。
- 定理6.4: R1(d) の吸収と合わせ、否定半分(空 Index 反例)と肯定半分
  (chart-indexed cover からの構成)の二段で移植する。
- 定理6.5: cover nerve が overlap データの再記述であることの typed 一致定理。
- 定理6.6: sheaf 条件 + cover membership から per-cover descent・gluing・
  大域 section 一意存在が従う導出定理。
- 完了条件: §6 の全ラベルが sorry なしで存在する。

## Target Statements

定理7.5の有限性仮定を持たない経路について、入力と10結論の型を次で固定する。
実装との defeq 一致は
`Formal/AG/StatementContractsSemanticRepairPart10.lean` を通常 build surface から
elaborate して検査する。

```lean
structure LawEquationSemanticAtomInputBody (U : AtomCarrier.{x}) where
  Component : Type v
  project : U.Atom -> Component
  sourceTraceToken : U.Atom -> Bool

structure LawEquationWitnessIdealGeometryBody
    (semanticInput : LawEquationSemanticAtomInputBody.{v, x} Ulaw)
    (S : Site.AATSite.{x} Alaw) where
  toCore : LawAlgebra.SemanticLawEquationWitnessIdealCore.{x} S
  supportAtom_traceVisible :
    semanticInput.sourceTraceToken toCore.supportAtom = true
  quotientIsSheaf :
    Site.AATSheafCondition S toCore.obstructionQuotientPresheaf

structure FinitePosetLawEquationDefectSourceBody
    (semanticInput : LawEquationSemanticAtomInputBody.{v, x} Ulaw)
    (G : LawEquationWitnessIdealGeometryBody semanticInput Slaw)
    (geometry : Site.FinitePosetCoverGeometry Slaw) where
  LocalInput : geometry.cover.Index -> Type x
  input : (i : geometry.cover.Index) -> LocalInput i
  atomSupport :
    (i : geometry.cover.Index) -> LocalInput i -> List Ulaw.Atom
  atomSupport_traceVisible :
    forall (i : geometry.cover.Index) (localInput : LocalInput i),
      exists atom : Ulaw.Atom,
        atom ∈ atomSupport i localInput /\
          semanticInput.sourceTraceToken atom = true
  lawSupport :
    (i : geometry.cover.Index) -> LocalInput i -> List Slaw.lawUniverse.Index
  lawSupport_nonempty :
    forall i, exists lawIndex : Slaw.lawUniverse.Index,
      lawIndex ∈ lawSupport i (input i)
  lawSupport_required :
    forall i (lawIndex : Slaw.lawUniverse.Index),
      lawIndex ∈ lawSupport i (input i) -> Slaw.lawUniverse.Required lawIndex
  objectOfLocalInput :
    (i : geometry.cover.Index) -> LocalInput i -> ArchitectureObject Ulaw
  defect :
    (i : geometry.cover.Index) -> LocalInput i ->
      G.toCore.Observable
        (Site.ContextCategoryObject.of Slaw.contextPreorder
          (geometry.cover.patch i))
  holds_defect_mem :
    forall i (lawIndex : Slaw.lawUniverse.Index),
      lawIndex ∈ lawSupport i (input i) ->
        Slaw.lawUniverse.Required lawIndex ->
          (Slaw.lawUniverse.law lawIndex).holds
              (objectOfLocalInput i (input i)) ->
            defect i (input i) ∈
              G.toCore.lawWitnessIdeal
                (Site.ContextCategoryObject.of Slaw.contextPreorder
                  (geometry.cover.patch i)) lawIndex
```

10結論 packet は次の field 型を持つ。先頭3 field だけが
`DisplayedRequiredLawsHoldOn` に依存し、残る7 field は law 前提を受けない
補助定理で構成する。

```lean
structure LawEquationGroundedComparisonFiniteFreeConjunctsBody
    {semanticInput : LawEquationSemanticAtomInputBody.{v, x} Ulaw}
    {semanticCover :
      SemanticRepairCover.{x, v, w, x} semanticInput.toSemanticAtomProjection}
    {G : LawEquationWitnessIdealGeometryBody semanticInput Slaw}
    {geometry : Site.FinitePosetCoverGeometry Slaw}
    (D : FinitePosetLawEquationDefectSourceBody semanticInput G geometry)
    (surface :
      LawEquationGeneratedCurrentG06InputSurface
        semanticCover Slaw G.toCore.obstructionQuotientPresheaf
        (lawEquationCechComplex (G := G.toCore) G.quotientIsSheaf
          geometry.canonicalTupleCoverGeometryFromOverlap))
    (source :
      LawEquationBodyCechSource D.toLawEquationDefectSource
        (lawEquationCechComplex (G := G.toCore) G.quotientIsSheaf
          geometry.canonicalTupleCoverGeometryFromOverlap)) where
  displayedInterpretationRealization : source.DisplayedInterpretationRealization
  displayedRequiredLawRestrictionEvaluator :
    source.DisplayedRequiredLawRestrictionEvaluator
  sourceC0CechZero : source.SourceC0CechZero
  selectedRealizationLayer :
    Nonempty
      (LawEquationSelectedSemanticCoefficientFiniteFreeLayerBody D source surface
        (coverRelativeGeneratedBoundaryAdditiveH1Surface
          (lawEquationCechComplex (G := G.toCore) G.quotientIsSheaf
            geometry.canonicalTupleCoverGeometryFromOverlap)
          source.toPrimitive))
  degreewiseCarrierFaceEquations :
    DegreewiseCarrierDataAndExplicitFaceRestrictionEquationsBody
      (coverRelativeGeneratedBoundaryAdditiveH1Surface
        (lawEquationCechComplex (G := G.toCore) G.quotientIsSheaf
          geometry.canonicalTupleCoverGeometryFromOverlap)
        source.toPrimitive)
      (lawEquationCechComplex (G := G.toCore) G.quotientIsSheaf
        geometry.canonicalTupleCoverGeometryFromOverlap)
  cochainRealization :
    Nonempty
      (SemanticRepairCoverRelativeCochainRealization
        (coverRelativeGeneratedBoundaryAdditiveH1Surface
          (lawEquationCechComplex (G := G.toCore) G.quotientIsSheaf
            geometry.canonicalTupleCoverGeometryFromOverlap)
          source.toPrimitive)
        (lawEquationCechComplex (G := G.toCore) G.quotientIsSheaf
          geometry.canonicalTupleCoverGeometryFromOverlap))
  h1ComparisonPackage :
    Nonempty
      (SemanticRepairCoverRelativeH1Comparison.
        SemanticRepairAdditiveH1CoverRelativeH1ComparisonPackage
          (coverRelativeGeneratedBoundaryCochainRealization
            (lawEquationCechComplex (G := G.toCore) G.quotientIsSheaf
              geometry.canonicalTupleCoverGeometryFromOverlap)
            source.toPrimitive).toH1Comparison)
  residualBoundary :
    GeneratedResidualBoundarySurfaceBody
      (coverRelativeGeneratedBoundaryAdditiveH1Surface
        (lawEquationCechComplex (G := G.toCore) G.quotientIsSheaf
          geometry.canonicalTupleCoverGeometryFromOverlap)
        source.toPrimitive)
  semanticH1Zero :
    GeneratedSemanticH1ZeroBody
      (coverRelativeGeneratedBoundaryAdditiveH1Surface
        (lawEquationCechComplex (G := G.toCore) G.quotientIsSheaf
          geometry.canonicalTupleCoverGeometryFromOverlap)
        source.toPrimitive)
  additiveH1Zero :
    (coverRelativeGeneratedBoundaryAdditiveH1Surface
      (lawEquationCechComplex (G := G.toCore) G.quotientIsSheaf
        geometry.canonicalTupleCoverGeometryFromOverlap)
      source.toPrimitive).H1Zero
```

主定理と law 非依存補助定理の完全な signature は次で固定する。

```lean
theorem lawEquation_constructs_finiteFreeLawIndependentConjuncts
    (semanticInput : LawEquationSemanticAtomInputBody.{v, x} Ulaw)
    (semanticCover :
      SemanticRepairCover.{x, v, w, x} semanticInput.toSemanticAtomProjection)
    (G : LawEquationWitnessIdealGeometryBody semanticInput Slaw)
    (geometry : Site.FinitePosetCoverGeometry Slaw)
    (D : FinitePosetLawEquationDefectSourceBody semanticInput G geometry)
    (chartSimplex :
      semanticCover.CoverChart ->
        (lawEquationCoverRelativeCover (G := G.toCore) G.quotientIsSheaf
          geometry.canonicalTupleCoverGeometryFromOverlap).simplex 0)
    (overlapSimplex :
      (Sigma fun pair : semanticCover.CoverChart × semanticCover.CoverChart =>
        semanticCover.Overlap pair.1 pair.2) ->
          (lawEquationCoverRelativeCover (G := G.toCore) G.quotientIsSheaf
            geometry.canonicalTupleCoverGeometryFromOverlap).simplex 1)
    (tripleSimplex :
      (Sigma fun triple : semanticCover.CoverChart × semanticCover.CoverChart ×
        semanticCover.CoverChart =>
        semanticCover.TripleOverlap triple.1 triple.2.1 triple.2.2) ->
          (lawEquationCoverRelativeCover (G := G.toCore) G.quotientIsSheaf
            geometry.canonicalTupleCoverGeometryFromOverlap).simplex 2) :
    let K := lawEquationCechComplex (G := G.toCore) G.quotientIsSheaf
      geometry.canonicalTupleCoverGeometryFromOverlap
    let source := D.toLawEquationBodyCechSource
    let surface := lawEquationGeneratedCurrentG06InputSurfaceOfFinitePosetGeometry
      semanticCover geometry K chartSimplex overlapSimplex tripleSimplex G.quotientIsSheaf
    let additive := coverRelativeGeneratedBoundaryAdditiveH1Surface K source.toPrimitive
    let realization := coverRelativeGeneratedBoundaryCochainRealization K source.toPrimitive
    Nonempty (LawEquationSelectedSemanticCoefficientFiniteFreeLayerBody
      D source surface additive) /\
      DegreewiseCarrierDataAndExplicitFaceRestrictionEquationsBody additive K /\
      Nonempty (SemanticRepairCoverRelativeCochainRealization additive K) /\
      Nonempty
        (SemanticRepairCoverRelativeH1Comparison.
          SemanticRepairAdditiveH1CoverRelativeH1ComparisonPackage
            realization.toH1Comparison) /\
      GeneratedResidualBoundarySurfaceBody additive /\
      GeneratedSemanticH1ZeroBody additive /\
      additive.H1Zero

theorem lawEquation_constructs_groundedComparisonPacket_finiteFree
    (semanticInput : LawEquationSemanticAtomInputBody.{v, x} Ulaw)
    (semanticCover :
      SemanticRepairCover.{x, v, w, x} semanticInput.toSemanticAtomProjection)
    (G : LawEquationWitnessIdealGeometryBody semanticInput Slaw)
    (geometry : Site.FinitePosetCoverGeometry Slaw)
    (D : FinitePosetLawEquationDefectSourceBody semanticInput G geometry)
    (chartSimplex :
      semanticCover.CoverChart ->
        (lawEquationCoverRelativeCover (G := G.toCore) G.quotientIsSheaf
          geometry.canonicalTupleCoverGeometryFromOverlap).simplex 0)
    (overlapSimplex :
      (Sigma fun pair : semanticCover.CoverChart × semanticCover.CoverChart =>
        semanticCover.Overlap pair.1 pair.2) ->
          (lawEquationCoverRelativeCover (G := G.toCore) G.quotientIsSheaf
            geometry.canonicalTupleCoverGeometryFromOverlap).simplex 1)
    (tripleSimplex :
      (Sigma fun triple : semanticCover.CoverChart × semanticCover.CoverChart ×
        semanticCover.CoverChart =>
        semanticCover.TripleOverlap triple.1 triple.2.1 triple.2.2) ->
          (lawEquationCoverRelativeCover (G := G.toCore) G.quotientIsSheaf
            geometry.canonicalTupleCoverGeometryFromOverlap).simplex 2)
    (hholds : D.DisplayedRequiredLawsHoldOn) :
    let K := lawEquationCechComplex (G := G.toCore) G.quotientIsSheaf
      geometry.canonicalTupleCoverGeometryFromOverlap
    let source := D.toLawEquationBodyCechSource
    let surface := lawEquationGeneratedCurrentG06InputSurfaceOfFinitePosetGeometry
      semanticCover geometry K chartSimplex overlapSimplex tripleSimplex G.quotientIsSheaf
    Nonempty (LawEquationGroundedComparisonFiniteFreeConjunctsBody D surface source)
```

### R7. §7 SAGA 比較定理(定義7.1、定理7.2–7.5)

- `SemanticRepairCoverRelativeH1Comparison`(次数別往復・減法互換・微分互換・
  次数2 zero 保存のみ。結論フィールドなし)と強形 `CochainRealization`、
  `toH1Comparison` を移植する。
- 定理7.2: cocycle 移送、sameClass iff、商水準の両方向写像とその
  well-definedness、左右逆定理、`H^1` equiv、zero-predicate equivalence、
  package を移植する。**一般形に有限性の仮定を混入させない**(有限性は
  grounded surface と instance の側に属する)。
- 定理7.3: 定理7.2 + 定義4.6/4.7 + gluing data からの結論束
  (SheafConditionFor / Descent / 大域 section 一意存在 / package /
  `GlobalCoherent ⇔ CoverRelativeResidualH1Zero` / additive H^1 zero 同値 /
  上位層消滅)を移植する。
- 定理7.5: 生成入力面(生成 Čech complex / 生成商係数 / 生成篩 / supplied
  quotient sheaf condition / 導出 descent)の上での 10結論 packet を移植する。
  Cycle 332 の基幹 route 定理(約30連言の一括供給)は、そのまま持ち込まず
  本体の語彙で結論群を再編成して移植する(連言の分解・補題化は可、
  結論の削減は不可)。
- 定理7.4: 対偶定理と、R9 の circle instance での発火をもって完了とする。
- carrier 比較の非一様性反例(`PUnit`/`ZMod 2`)を canonical no-go として
  1組移植する(定義7.1 が material data であることの証拠)。
- 完了条件: [CBI] 3定理(7.2 / 7.3 / 7.5)が sorry なしで証明されている。

### R8. §8 境界定理(定理8.1、8.2、8.4、8.5)

- 定理8.1: law 充足 ⇒ 生成 0-cochain の各点零(pointwise 版)と、その微分の
  影としての Čech 零を移植する。
- 定理8.2: packet の law 非依存結論群を law 前提なしで証明する定理を移植する。
- 定理8.4 / 8.5: 比較データ structure(typed target)+ データ相対化定理 +
  反例(空ターゲット / coarse 零・fine 非零)の二段で移植する。
- fail-closed 締め(comparison provenance の明示要求)2本を canonical no-go
  として移植する。
- 意味8.3 の open question(conormal 係数の読み)は台帳の future proof
  obligation に登録し、形式化しない。
- 完了条件: §8 の4定理が sorry なしで存在する。

### R9. §9 有限 instance(例9.1、例9.2)

- `Formal/AG/Examples/SemanticRepairPart10.lean` に移植する:
  (a) 有限モデル site の生成篩 pullback 最大性と全 presheaf sheaf 条件定理、
  (b) 具体 law-equation core(Observable = `ℤ`、witness `2`、`I_Ob ⊆ (2)`、
  `1 ∉ I_Ob`、`[1] ≠ 0`、violation class 零)、
  (c) `quotientIsSheaf` を定理として放電した geometry(例9.1 の
  「仮定→定理」転化 witness)、
  (d) end-to-end packet の発火(例9.1)、
  (e) circle nerve cover / complex、residual、`residual_not_coboundary`、
  恒等 comparison、両側 `H^1` 非零、transfer packet(例9.2)。
- 例9.1 と例9.2 は別 witness であり、lawful 例の class 零は定理8.1 の帰結で
  あって欠陥ではないことを docstring に記す。
- 付録 B.9 の詳細計算のうち、例9.1/9.2 の発火に必要な範囲だけを対象とする
  (B.9 全体の形式化は要求しない)。
- 完了条件: 両 instance が sorry なしで発火し、例9.2 が本体
  `CoverRelativeCechComplex` の無条件非零 `H^1` class を与えている。

### R10. Research 側の凍結と足場の非移植

- `Formal/AG/Research/QualitySurface/` の既存ファイルは変更しない(evidence
  凍結)。削除・rename・本体からの re-export はいずれも本PRDの範囲外とする。
- 移植ホワイトリスト外の宣言(premise 順列 no-go 帯、`of_X_via_Y` 再入口
  変種、iff 格子中間ノード、checkpoint 帯)は本体へ持ち込まない。
- 本体化した宣言と Research の対応(Research 宣言名 → 本体宣言名)の対照表を
  tracking Issue に記録する(将来の Research 清掃の材料。清掃自体は別作業)。
- 完了条件: 本体(= `Formal/AG` 配下から `Formal/AG/Research/` と lib root
  `Formal/AG/Research.lean` を除いた範囲)に `Formal.AG.Research` への参照が
  存在しない(`rg 'AG\.Research' Formal/AG --glob '!Formal/AG/Research/**'
  --glob '!Formal/AG/Research.lean'` が no match)。

### R11. 台帳整備

- `lean_theorem_index_ag_aat.md` の末尾に第X部セクションを追加する。
  見出しは Part VIII/IX の流儀
  (`## AAT Algebraic-Geometric Part X Semantic Repair Descent (SAGA)`)、
  セクション前文として `Files:`(`Formal/AG/SemanticRepair/` 配下と R1/R5/R9 の
  新設ファイルの列挙)と Tracking Issue / R 番号別実装 Issue のリンク列を
  Part VIII/IX の流儀で置く。表は既存5列(本文ラベル / Lean 名 / 種別 / 意味 /
  Status)、本文ラベルは `X.定義2.1` / `X.定理3.4` / `X.定理7.2` 形式。
  セクション末尾に Non-conclusions 段落を置く。
- `proof_obligations_ag_aat.md` の末尾に第X部セクション
  (` Lean status` サフィックス付き見出し、同様の前文、3列表 + 締めの
  2列 status 表)を追加する。explicit non-goal 行に登録するのは**数学的
  non-goal に限る**: 任意 Grothendieck site への無条件一般化 /
  full sheaf cohomology との無条件同一視 / unbounded derived・infinity-stack・
  nonabelian・stacky universality / 無条件 refinement naturality、
  boundary notes 4項目(identity comparison / selected circle nerve /
  degenerate witness site / law-equation ambient rows)、および意味8.3 の
  conormal open question。G-06 claim boundary の tooling 側項目
  (raw source extraction completeness / ArchMap correctness / runtime
  extraction completeness / repair synthesis completeness / コード全体の
  品質判定)は research 台帳の Non-conclusions に記録済みであり、
  **本体台帳へ複製しない**(tooling 境界を AAT 正典台帳へ持ち込まない。
  必要な参照は research 台帳への pointer 1文に留める)。
- 第III部節に定義11.3 / 定理11.4 の行を追加する(R5)。
- 「PRD-1〜9」表記を「PRD-1〜10」へ更新する。対象は4箇所:
  入口ファイル `lean_theorem_index.md` / `proof_obligations.md` の分割台帳表、
  および分割台帳自身の冒頭 `lean_theorem_index_ag_aat.md` /
  `proof_obligations_ag_aat.md` の管理宣言文。
- research 台帳(`lean_theorem_index_research.md` / `proof_obligations_research.md`)
  の G-02 / G-05 / G-06 記載は残置し、各項に「第X部として本体へ正典化済み
  (PRD-10、対応表は tracking Issue)」の pointer 文を追加する。二重管理を
  避けるため、以後の更新は本体台帳側でのみ行う旨を明記する。
- 処遇表で「対象外」とした本文ラベルは独立のラベル行として登録しない。
  例外は次の三つの記録であり、いずれも独立行ではなく指定の場所に置く:
  意味8.3 の open question(future proof obligation 行)、意味5.2
  (`X.定義5.1` 行の意味欄 + Non-conclusions)、原則7.6(Non-conclusions
  段落に SAGA ≠ AAT-GAGA の1文)。
- 完了条件: 両台帳が最終実装と一致している。

## 非主張(claim boundary)

- 本PRDの全主張は、選ばれた chart・overlap・residual・係数・comparison data に
  相対化される。結論は固定された semantic repair geometry の内部でだけ読む。
- 任意の Grothendieck site への無条件一般化、full sheaf cohomology との無条件
  同一視、unbounded derived / infinity-stack / nonabelian / stacky universality
  は主張しない(定理8.4 / 8.5 が反例で遮断する)。cover refinement の自然性は
  明示的な refinement 比較データの下でのみ成立する。
- comparison data(定義7.1)は商の等式・zero class・大域整合・descent の結論を
  格納しない。`H^1` 同値と zero-predicate equivalence は商水準で証明される
  定理である。
- `quotientIsSheaf` は一般には supplied 仮定であり、単一 context 有限モデルの
  class 上でのみ定理である。一般 site での sheaf 条件 discharge を主張しない。
- law-grounded content は正確に次数0(定理8.1)であり、`H^1` zero 結論を
  law に根拠づけられた descent 内容として引用しない(定理8.2)。
- 定理3.4 の十分性・同値は semantic faithfulness hypothesis の下でのみ成立する。
  complete-support 族(定理3.5)の外では仮説は checkpoint のまま残る。
- §3 の障害消滅は境界所属であり、商 class と `H^1` の語は §4 以降にのみ使う。
  選ばれた cover に相対的な Čech 型商を `H^n(X,·)` と書くための追加条件は
  第IV部 定義3.3 の規律に従う。
- circle nerve(例9.2)は単元 cover 上の選ばれた simplicial データであり、
  chart 交叉から生成されたとは主張しない。例9.2 の comparison は定義的に
  等しい担体上の恒等 comparison であり、非恒等 comparison を通じた非零転送は
  演習されていない(一般定理自体は任意の comparison について証明される)。
  有限モデル witness site は退化(singleton contexts)している。
  law-equation surface の ambient 入力行(cover geometry / coefficient
  geometry / semantic site / pointwise atom-law choices 等)は supplied
  データであり、定理の結論に含めない。これら4項目は G-06 受理時の
  boundary notes であり、解消は PRD-R の任意 hardening 項目。
- SAGA は AAT-GAGA(第VIII部 定理12.3)ではない。SAGA の名は GAGA への言及で
  あり、Serre の定理の適用でも一般化でもない。
- tooling 境界に属する非主張(source extraction / ArchMap / runtime /
  repair synthesis / コード全体の品質)は research 台帳の Non-conclusions に
  記録済みであり、本体台帳・本体 docstring へ複製しない(R11)。
- 相異なる非零の lawful reading が非自明に貼り合う係数(conormal `I_U/I_U²`)の
  読みは本文の open question であり、本PRDは形式化しない。
- 本PRDは数学本文(`docs/aat/algebraic_geometric_theory/`)を変更しない。
  移植中に本文の欠陥が見つかった場合は停止して報告し、本文改訂はユーザー判断に
  委ねる。

## 完了条件(Acceptance Criteria)

- [ ] AC1. `Formal/AG/SemanticRepair` が新設され、CI の default `lake build` で
      ビルドされる。`Formal.AG.Research` への import が本体に存在しない(R0/R10)
- [ ] AC2. 移植スパインの確定版ホワイトリストが tracking Issue に記録され、
      以後のギャップ分析の基準になっている(R0)
- [ ] AC3. 標準有限 poset Čech 複体の canonical 構成(tuple nerve / 標準交代和 /
      d∘d=0 の証明 / end-to-end 生成ルート)が本体 Site/Cohomology に存在する(R1)
- [ ] AC4. cochain 比較 ⇒ H^1 同値の一般定理が semantic 語彙に依存しない形で
      本体 Cohomology に存在する(R1)
- [ ] AC5. R1 の吸収が既存本体宣言のシグネチャ変更ゼロで行われ、
      `lake build FormalAGResearch` が green を維持している(R0/R1)
- [ ] AC6. §2 の generic `(Λ, K, π)` 語彙と補題2.5、例2.6 が形式化されている(R2)
- [ ] AC7. 定理3.4 が (i) 無条件 / (ii)(iii) 仮説付きの構造で証明され、
      定理3.5 が complete-support 族で仮説を放電している(R3)
- [ ] AC8. 例3.6 が「可視局所整合の成立」と「r ∉ B¹ ∧ ¬GlobalCoherent」を
      同時に検証している(R3)
- [ ] AC9. 定理4.8 の boundary-relation additive package が、上位層消滅を
      外部仮定に取らずに証明されている(R4)
- [ ] AC10. 補題4.5、命題4.9、命題4.10 が証明されている(R4)
- [ ] AC11. 第III部 定義11.3 / 定理11.4 相当(witness ideal 生成、商係数生成、
      functor 法則、vanishing = ideal 所属、evaluator 定理)が
      `Formal/AG/LawAlgebra/` で証明されている(R5)
- [ ] AC12. 定理6.1 / 6.5 / 6.6 と、定理6.4 の反例+肯定二段が証明されている(R6)
- [ ] AC13. 定理7.2 の H^1 equiv と zero-predicate equivalence が、有限性仮定
      なしの一般形で証明されている(R7)
- [ ] AC14. 定理7.3 / 7.5 の package が証明され、7.5 の law 依存境界
      (結論1〜3のみ)が statement 構造に現れている(R7)
- [ ] AC15. 定理8.1 / 8.2 が証明され、8.4 / 8.5 がデータ+反例の二段で
      存在する(R8)
- [ ] AC16. 例9.1 が発火し、`quotientIsSheaf` が具体 instance 上で定理として
      放電されている(R9)
- [ ] AC17. 例9.2 が発火し、本体 `CoverRelativeCechComplex` の無条件非零
      `H^1` class(両側)と transfer packet が存在する(R9)
- [ ] AC18. `Formal/AG` 全体(Research 除く)に `axiom` / `admit` / `sorry` /
      `unsafe` が存在しない
- [ ] AC19. 両台帳に第X部セクション(前文 Files / Issue リンク付き)が追加され、
      「PRD-1〜9」表記が計4箇所(入口2 + 分割台帳ヘッダ2)で PRD-1〜10 に
      更新され、research 台帳に正典昇格 pointer が記録されている(R11)
- [ ] AC20. explicit non-goal 行が数学的 non-goal・boundary notes 4項目・
      意味8.3 open question に限って登録され、tooling 側項目が本体台帳に
      複製されていない(R11)

## 実行順序の指針

prd-loop のギャップ分析で対象を選ぶ際は、次の依存順を推奨する。

```text
R0 -> R1(a)(b) -> R1(c)(d)(e)
   -> R2 -> R3
   -> R4
   -> R5
   -> R6 -> R7
   -> R8 -> R9
   -> R10 -> R11
```

- R1 は以降の全レイヤの土台であり最初に閉じる(R1 単独でも第IV部形式化の
  データ仮置き問題を解消する価値がある)。
- R2/R3(§2–3、G-02 資産)は依存が浅く、generic 化の成否を早期に確認できる。
- R4(G-05 資産)は R2/R3 の語彙に依存する。
- R5(第III部吸収)は R4 と独立に進められるが、R7 の定理7.5 の前提になる。
- R7 は R1(c)・R4・R5・R6 が揃ってから着手する。
- R9 の instance は各レイヤが閉じるたびに増分追加してよい
  (例9.2 の circle 側は R1 + R5 + R7 の一部で発火可能)。

## 付録: 移植スパイン初期リスト(R0 で確定する)

以下は調査時点の逆引き(受理ルートが名前参照する宣言群)。グループ単位で示す。
確定は R0 の依存グラフ解析による。

- **A. SAGA 比較核**(`SemanticRepairCechGrounding.lean`):
  `SemanticRepairCoverRelativeCoverBridge`(L69)、
  `CarrierSpecificAdditiveComparisonData`(L613)+ 非一様性反例(L666/688/703)、
  `SemanticRepairCoverRelativeH1Comparison`(L720)/
  `SemanticRepairCoverRelativeCochainRealization`(L775)/ `toH1Comparison`(L952)、
  namespace `SemanticRepairCoverRelativeH1Comparison` 一式(L5046–5353:
  cocycle 移送、sameClass iff、H^1 両写像、逆元、equiv、zero iff、package)
- **B. 生成係数・envelope 鎖**: `CoverRelativeCechGeneratedSemanticCoefficient`
  (L7593)系、`CoverRelativeCechGeneratedCanonicalH1Envelope`(L8517)系、
  `FinitePosetAtomLawCoverGeometry`(L9474)+ regime 変換、
  `SemanticAtomLawAdditiveCoefficientGeometry`(L9836)、
  `atomLawOverlapStandardFinitePosetCechComplex`(L13222)/
  `atomLawOverlapCoverRelativeCechComplex`(L13257)、tuple nerve・face action・
  double-face cancellation(L11197–12949)
- **C. 入力境界 source の塔(受理ルートが通る階段のみ)**:
  `CoverRelativeCechFreeSemanticAtomLawInputBoundarySource`(L13712)〜
  `BaseRestriction...`(L14224)、`...InputBoundaryGeometry`(L20097)、
  基幹 route 定理(L40309、蒸留して分解)
- **D. law 意味論層**: `displayedRequiredLawsHoldOn`(L16825)、
  `commonRestrictionRealization`(L16873)、
  `displayedRequiredLawRestrictionEvaluator`(L18181)、
  `atomLawOverlap_sourceSectionFreeSkeleton_sourceC0(CechZero)`(L25375/25482)
- **E. 入力面・gate 層**: `CurrentG06InputSurface`(L4055)、
  `SelectedSemanticCoefficientDirectRealizationLayer`(L29686)、
  `DegreewiseCarrierDataAndDirectDifferentialLaws`(L6466)
- **F. 最終セクション**: presheaf restriction 零/加法(L43981/43992)、
  定理6.6(L44010)、定理8.4 系(L44029–44066)、定理8.5 系(L44083–44127)、
  最終 package(L44136/L44165)、fail-closed 締め(L50142/50165)
- **G. §6 土台**: 定理6.1(L38/52)、incidence(L69/109/134/158)、
  chart-indexed 肯定半分(L188/220/265/290)、定理6.5(L570)
- **G-02/G-05 資産**: `SemanticRepairGluingComplex.lean`(全体が §3 対応)、
  `SemanticRepairAdequacyDischarge.lean`(定理3.5 の certificate 経路、補助)、
  `SemanticRepairSheafH1.lean`(定義4.2–4.4 / 補題4.5 の additive 側)、
  `SemanticRepairTrueSheafH1.lean`(定義4.1/4.6/4.7、定理4.8、命題4.9/4.10)、
  §2 基盤(`SemanticSupportProjectionKernel.lean` /
  `SemanticResidualComponentFaithfulness.lean`)
- **LawEquation 5ファイル**(G-06 受理分): `Realization`(§5 / 定理11.4)、
  `WitnessInstance`(例9.1 site 定理 + 算術核)、`GroundedPacket`(定理7.5)、
  `EndToEndInstance`(定理8.1/8.2 + 例9.1 発火)、
  `NonzeroClassInstance`(定理7.4 + 例9.2)
