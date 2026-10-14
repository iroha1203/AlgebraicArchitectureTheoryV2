# G-137 証明記録

固定GOAL・設計・共通基準: `d6d19ba0b199d499e1aa0239b60d71c50aa4bee4`。
GOAL blob: `00278db46e595fbe30762a1bb969230f77828f4f`。
既存宣言の参照版: `f3ae0eab35186e2259fa030eb23fb4657180a868`。
追跡: [#5358](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5358)。

## 現 proof obligation

T0・A–Eを固定したまま進める。Cycle 1は
[PR #5360](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5360#issuecomment-6168427100)、
merge `7f6ba524fb2f8d18c5707563d442b74a10cb1d56` で受理済み。
Cycle 2はAの二段商同型、実cochain/H¹の恒等・合成、全Law・G-135診断接続の受理候補。
W0の全粗化安全性と、三角形全関係商の不安全性も同じSafeで構成した。
全GOALは `target-proof-checkpoint`。B–E、P_G・P_J・P_N、W1・W2の指定評価は未完了。
Formalへの蒸留は未実施。

## Cycle 1 selection

selectionは実装前に[開始コメント](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5358#issuecomment-6167942871)で固定した。

```yaml
ledger_type: target_cycle_result
goal: G-137-aat-safe-coarsening-order
cycle: 1
goal_blob_sha: 00278db46e595fbe30762a1bb969230f77828f4f
base_oid: 38178c6e86f4e8f353f7b05d7b6e9b7db7ac40e4
tracking_issue: 5358
report_path: research/reports/G-137-aat-safe-coarsening-order.md
selection:
  proof_state_ref: tracking Issueの未着手記録と開始コメント
  proof_dag_predecessors: [RI.TargetSupportedNerve, RI.TargetSupportedNerveMorphism, RI.comparisonFactor_unique, FRS.ofHereditary, ADC.comparisonComp, mathlib.Setoid]
  milestone: T0とAの原始商・因子化・原始比較の恒等と合成
  proof_obligations: [全分割対からの商readingと台と有向辺, 全Rの原始比較, 関係包含と可換二因子の同値, 任意R≤R'の比較, 原始直接比較と合成の全record等号, 恒等比較の全計算成分]
  exit_criteria: [任意Rの商生成, 原始端点と支持条件の放電, le_iff_factors, quotientMorphism_factorとfactorMorphism_comp, 恒等chartとedgeと空face, focused checkと全宣言公理監査]
  selection_reason: B以後の全分割対分類が使う商と実比較の原始入力を生成する
  expected_result_type: proof-obligation-discharged
  lean_targets: [PrimitiveInput.lean, QuotientNerve.lean, Factorization.lean, PrimitiveExamples.lean]
  risks: [逆向き辺の誤併合, 元商写像を忘れた同一視, 結論の入力fieldへの移動, 原辺台の像とK1商台の混同]
  unchecked: [正式PR査読]
```

## 宣言と条項の対応

namespaceは `AAT.AG.SafeCoarseningOrder`。cycle scaffoldはない。
各行の公開API、structureの生成宣言、instance chainも受理対象とする。

| 条項 | ファイル・実宣言 | 入力・構成と使用先 |
| --- | --- | --- |
| T0 原始表 | `PrimitiveInput`, `PrimitiveInput.reading`, `Edge`, `nerve`, `supported`, `mem_edgeSupport`, `edge_endpoints_ne` | 全射q、対角を含まない辺、非空台だけを保持。既存reading・K1 nerveに接続。S/T/Vの有限非空条件は固定T0であり、汎用補助APIは条件を使わない場合より一般の型でも成立する。 |
| T0 全粗化と順序 | `Coarsening` | mathlibの全 `Setoid T × Setoid V`。関係包含の積complete lattice。安全性による入力候補の削減をしない。 |
| 任意Rの商 | `quotientReading`, `quotientSupport`, `quotientSupport_mk`, `quotientSupport_nonempty`, `quotientEdge`, `QuotientEdge`, `quotientNerve`, `quotientSupported`, `mem_quotient_edgeSupport` | chart fiber内の合併の像とK1交差、有向順序対の存在から全商を生成。平行辺の生成証拠はProp。 |
| fineから商への原始比較 | `quotient_coarser`, `quotient_factor`, `quotientEdgeMap`, `quotientEdgeMap_eq_none`, `quotientEdgeMap_eq_some`, `quotientMorphism`, `quotientComparison` | target商写像をcanonical factorと同定し、chart・部分edge・空faceと全支持条件を放電。G-134へ同じ比較を埋め込む。 |
| 因子化の必要十分 | `Coarsening.factor`, `factor_mk`, `factor_unique`, `le_iff_factor`, `le_iff_factors`, `factor_refl`, `factor_comp` | 元T/Vからの商写像と可換な二因子の存在を関係包含と同値にする。二因子の一意性と恒等・合成も証明。 |
| 全R≤R'の原始比較 | `factor_coarser`, `factor_comparisonFactor`, `factor_support`, `factorEdgeMap`, `factorEdgeMap_eq_none`, `factorEdgeMap_eq_some`, `factorMorphism` | 包含からtarget/chart因子と原始部分セル像を生成。台輸送と空面条件を入力表から放電。 |
| 全record合成と恒等 | `quotientEdgeMap_factor`, `morphism_ext`, `quotientMorphism_factor`, `factorEdgeMap_comp`, `factorMorphism_comp`, `factorMorphism_refl_chart`, `factorMorphism_refl_edge` | 直接辺像はOption.bindと一致。chart/edge/faceの全計算成分を照合して既存G-133比較合成と全record等号を示す。face成分は空型。 |
| 発火と対角除外 | `w0`, `w0Edge`, `w0_top_edge_none`, `w0_bot_edge_not_none`, `primitive_no_diagonal` | W0の原始表で全関係による縮約と恒等分割での保持を同時に評価。対角を含む表がT0に入らないことを示す。W0のH¹・安全順序・定数Law評価は後続。 |

## 前提・構成と再利用

| 前提 | 分類 | 出所・使用先・状態 |
| --- | --- | --- |
| S/T/Vの有限非空性、全射q、対角除外、有向辺、非空台、空面 | ambient-boundary / 本文由来 | T0。セルの有限性、reading、非空商台、原始nerveを生成。W0では全条件を構成。 |
| 任意の分割対R、R≤R' | ambient-boundary / 本文由来 | T0・A。mathlib Setoidの全関係と包含。因子と部分セル像を生成。 |
| 商reading・商台・商辺・原始比較と支持輸送 | discharge-required / 放電済み候補 | 上表のquotient/factor producer。比較同型・rank・安全元一覧を入力に置いていない。 |
| 原始因子化の逆方向と恒等・合成 | discharge-required / 放電済み候補 | le_iff_factors、全record合成、恒等成分。実cochain/H¹への接続は後続義務。 |
| 二段商の同型、全Law同値とG-135、B–E | discharge-required / 未完了 | 本cycleの受理主張に含めない。全GOALの未完了として保持。 |

既存宣言の関連5 sourceは参照版とbaseで差分なし。
`RI.TargetSupportedNerve` の全有限セル・K1台・空面端点条件、
`TargetSupportedNerveMorphism` の部分セル像・支持輸送を実型で確認した。
`comparisonFactor_unique` はreading全射から一意性を示し、今回の標準商因子へ適用する。
`FRS.ofHereditary` は同じchart/edge/faceをincidence比較に埋め込む。
`ADC.comparisonComp` はchart合成とedge/faceのOption.bindを持ち、今回の原始直接比較と等しい。
受理記録は[G-133 PR #5269](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5269#issuecomment-6007700344)と
[G-134 PR #5287](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5287#issuecomment-6030258596)。
G-135/G-136の[Research完了](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5290#issuecomment-6078348119)・
[完了同期](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5321#issuecomment-6117232196)は確認済み。
その同じ実H¹と有限判定、W3比較への接続は後続cycleで行う。
Lean v4.28.0、mathlib `8f9d9cff6bd728b17a24e163c9402775d9e6a365`のSetoid complete latticeと標準商APIを用いる。

## Cycle 1 result proposal

```yaml
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: 全Rの原始商、分割包含と二可換因子の同値、原始比較生成と全record恒等・合成
  exit_criteria_status: [全4sourceの個別検証, le_iff_factors, quotientMorphism_factor, factorMorphism_comp, 恒等成分評価, W0縮約と保持]
  split_reason: none
  completion_candidate: no
  lean_artifacts: [PrimitiveInput.lean, QuotientNerve.lean, Factorization.lean, PrimitiveExamples.lean]
  evidence: [宣言と条項の対応表]
  claim_mapping:
    theorem_names: [le_iff_factors, quotientMorphism_factor, factorMorphism_comp, factorMorphism_refl_chart, factorMorphism_refl_edge]
    source_labels: [T0, A 原始商と因子化と原始比較]
    conjuncts: [上記対応表]
    undischarged_assumptions: []
    acceptance_point: 任意分割対と任意包含からの全原始比較を生成し全計算成分を照合
    port_status: unported
audits:
  premise_delta:
    discharged: [商非空台, 原始比較の全incidenceと支持条件, 関係包含と因子化, 原始恒等と合成]
    remaining: [Aの二段商同型と実比較とLawとG-135接続, B–E]
  certificate_provenance:
    discharged: [quotientMorphismとfactorMorphismを元表から生成, w0の原始表]
    unresolved: []
  proof_use:
    used: [q全射→商全射とcanonical factor一意性, 元非空台→全商非空台, 分割包含→target/chart因子, 原始辺存在→商辺, 原始端点→全record合成]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [個別focusedと公理監査はPR証跡に固定]
  blocking_findings: [標準PR独立査読前]
  next_obligation: Aの二段商同型と実cochain/H¹とLaw/G-135接続
```

正式受理、固定head、review evidence、CI、mergeと次義務はPR監査とtracking Issueに記録する。
Research検証はこの到達点の個別sourceと単一監査fileに限定する。
本体・Researchの全体build、Research aggregate検証、Formal移植は実施しない。

## Cycle 2 selection

実装前に[Cycle 1同期とCycle 2開始](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5358#issuecomment-6168457656)で固定した。

```yaml
ledger_type: target_cycle_result
goal: G-137-aat-safe-coarsening-order
cycle: 2
goal_blob_sha: 00278db46e595fbe30762a1bb969230f77828f4f
base_oid: 7f6ba524fb2f8d18c5707563d442b74a10cb1d56
tracking_issue: 5358
report_path: research/reports/G-137-aat-safe-coarsening-order.md
selection:
  proof_state_ref: Cycle 1受理・merge同期コメント
  proof_dag_predecessors: [Cycle 1原始比較, ADC.aSubnerveComparisonHom_comp, FRS.ofHereditary_aSubnerveComparisonHom, RI.uniformInvariance_iff_allNonemptyASubnerveH1Bijective, ACF.coefficient_zeroDefect_iff, ACF.allAPreservationDecision_eq_true_iff]
  milestone: Aの二段商同型と同じ実cochain/H¹・全Law・G-135診断への接続
  proof_obligations: [二段商の全原始同型, 元T/V商写像との可換性, 原始直接比較から実HomとH¹の合成, 空A, 全adequate Law必要十分, 同じJ/係数/fiber/有限判定, 非空虚なSafeの成立と不成立]
  exit_criteria: [iteratedIsoと辺全単射と支持保存, 原始商とsupported recordの一致, 実cochain/H¹の恒等・合成, safe_iff_laws, safe_iff_zeroDefectとsafe_iff_coefficientとsafe_iff_decision, w0_safeとtriangle_top_not_safe, 対象focusedと全宣言公理監査]
  selection_reason: 固定全分割対を既存実核・余核と全Lawへ戻しB–Eの安全性判定を可能にする
  expected_result_type: proof-obligation-discharged
  lean_targets: [PrimitiveIsomorphism.lean, IteratedQuotient.lean, GeneratedComparison.lean, UniformSafety.lean, SimpleEdgeHomology.lean, SafetyInstances.lean]
  risks: [二段商を直接商から定義する経路, 忘却後だけの同型, 次元一致の代用, Law値型への有限性追加, 空Aを落とすこと, 係数条件の省略]
  unchecked: [正式PR査読]
```

## Cycle 2 条項・実宣言・前提使用

| 条項 | ファイル・宣言 | 構成・proof-use |
| --- | --- | --- |
| 全S/T/Vを保存する原始同型 | `PrimitiveIsomorphism` の `PrimitiveIso`, `refl`, `trans`, `symm`, `edgeEquiv`, `edgeEquiv_left/right`, `ext`, `trans_symm`, `symm_trans` | 入力条件は全単射と原始q/有向辺/台の保存だけ。辺の全単射と逆・合成はこのデータから生成。Cの実cochain共役・安全作用は後続。 |
| 同じ商表の再生成 | `quotientInput`, `quotientInput_reading/support/edge/nerve/supported` | Cycle 1と同じ商表からprimitive inputを作り、全nerve・supported recordを独立生成と等号で接続。有限instanceを保持。 |
| 二段商と直接商 | `Coarsening.factor_surjective`, `factorKernel`, `iteratedEquiv`, `iteratedEquiv_mk`, `PrimitiveInput.iteratedRelation`, `iterated_support`, `iterated_edge`, `iteratedIso`, `iteratedIso_target_mk/chart_mk` | 初段表へ商式を再適用。標準因子の核を次段分割とし、商第一同型定理からtarget/chart全単射、辺と台の保存を両方向で証明。元T/Vの二段商写像と可換。 |
| 元の恒等商同型 | `Coarsening.botEquiv`, `botEquiv_apply`, `PrimitiveInput.botIso` | 元集合から等号関係商への全単射と、元q/辺/台の全保存を生成。 |
| 同じ旧・新実比較 | `quotient_actualHom_old`, `quotient_actualH1_old` | G-134 hereditary埋め込みと旧比較の全Hom・同じH¹商写像の一致。 |
| 実恒等 | `factorMorphism_refl`, `identity_subset_preimage`, `factor_cochain_refl`, `factor_h1_refl` | Cycle 1原始全成分から旧identityMorphismと同定。canonical逆像を元Aに輸送し、全三次数Hom・実H¹は恒等。 |
| 実合成 | `quotient_cochain_comp`, `quotient_h1_comp`, `factor_cochain_comp`, `factor_h1_comp` | 原始全record等号→G-133同じHom合成→実H¹。最粗Aの中間逆像を使う。任意同次元同型による代用なし。 |
| 全Aと全Law | `Safe`, `empty_h1_subsingleton`, `empty_comparison_bijective`, `safe_iff_laws` | SafeはG-134実H¹全単射。G-107全adequate Law族との同値を埋め込み一致で接続し、空Aは零H¹として追加。粗adequacyから細adequacyをG-133で導出。Law値型全体の有限instanceは要求しない。発生ラベルは既存全Lawのまま。 |
| 同じ診断と入力生成判定 | `safe_iff_zeroDefect`, `safe_iff_coefficient`, `safe_iff_decision` | 実H¹の全単射、同じJ零、同じunitH1全単射とconnectingTau単射、原始有理行列からの全A判定を必要十分で接続。G-135のpure特殊化を使用せず、係数条件も保持。 |
| 成立例 | `subset_d0_surjective_of_single_edge`, `quotient_edges_subsingleton`, `safe_of_single_edge`, `w0_edges_subsingleton`, `w0_safe` | 一辺以下という一般方向条件から、任意Aの実d0全射をpotentialで生成。W0では一辺条件を原始表から放電し、全粗化の実比較が全単射。 |
| 不成立例と原始類 | `Triangle.input`, `fullComplex`, `fullChart`, `fullEdge`, `period`, `period_boundary`, `cycle`, `classOf`, `periodH1`, `periodH1_classOf`, `spike`, `period_spike`, `spike_class_nonzero`, `top_edges_empty`, `top_h1_subsingleton`, `triangle_top_not_safe` | 有向三角形の同じ元辺和、指定一辺1のcochain、既存d0像による商を使う。periodは原d0で零、spikeで1、同じ実H¹類は非零。全関係商のH¹は零なので実比較は非全射。 |
| 原始同型の発火・不成立 | `triangleEdgeless`, `triangle_not_iso_edgeless`, `triangle_bot_iso` | 三角形の恒等商同型は元表から生成。同じ台で辺だけが空の表との原始同型は有向辺保存の矛盾で排除。 |

### material premiseと再利用

T0・Aの原始表、任意分割対と包含は本文由来。`PrimitiveIso`の全単射と原始保存は一般同型の
direction-hypothesisで、二段商/恒等商と発火例では全fieldを生成する。
実H¹同型、安全性、rankを同型fieldへ入れない。`Subsingleton Edge`と異端点は一辺以下の
一般補題のdirection-hypothesisであり、W0では元表と商辺producerから放電する。
全Law方向の粗adequacyはカードの量化域、細adequacyは `adequate_of_coarser` で放電する。
新たな未申告前提を入力として保持しない。

G-133/G-134はCycle 1の受理refと同じsource版を継続使用。
`ADC.SubsetComposition` の全Hom型輸送と実H¹合成、`ADC.ComparisonLaws` と
G-107 `UniformityInstancePairs` の恒等成分を、実引数と同じ複体で確認した。
G-107の全Law還元は [PR #3994受理監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/3994#issuecomment-5279154319)
とG-107 reportの完了記録を参照し、同じ量化と実引数に適用する。
G-135は [Research完了記録](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5290#issuecomment-6078348119)
と [PR #5318](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5318#issuecomment-6078269788)
で受理済み。`coefficient_zeroDefect_iff`、`allAPreservationDecision_eq_true_iff`、
`h1_subsingleton_of_d0_surjective` の現在statement・必要定義・適用を読んだ。
前二者は同じ原始部分比較とAの実H¹に適用し、後者はW0の同じ実d0全射に適用する。
受理predecessorの内部履歴を再帰的に再認定せず、使用源の版・必要定義・今回の適用・受理refまで確認する。

### Cycle 2 result proposal

```yaml
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: 二段/直接商と恒等商の全原始同型、同じ実Hom/H¹の恒等・合成、全Law/J/係数/fiber/有限診断への必要十分、Safeの正負発火
  exit_criteria_status: [上記対応表の全構成・必要十分・実評価, 個別focusedと全宣言公理監査はPRに証跡固定]
  split_reason: none
  completion_candidate: no
  lean_artifacts: [PrimitiveIsomorphism.lean, IteratedQuotient.lean, GeneratedComparison.lean, UniformSafety.lean, SimpleEdgeHomology.lean, SafetyInstances.lean]
  evidence: [Cycle 2条項対応表]
  claim_mapping:
    theorem_names: [iteratedIso, quotientInput_supported, factor_cochain_refl, quotient_h1_comp, factor_h1_comp, safe_iff_laws, safe_iff_coefficient, safe_iff_decision, w0_safe, triangle_top_not_safe]
    source_labels: [A, T0 Safe, E W0の全A安全性]
    conjuncts: [Cycle 2対応表]
    undischarged_assumptions: []
    acceptance_point: 任意分割対と任意包含の独立生成を同じ実比較と全Law/診断へ接続
    port_status: unported
audits:
  premise_delta:
    discharged: [二段と直接商の原始保存, 恒等商保存, 実恒等・合成, 空A, 全Law還元, 同じJ/係数/fiber/有限判定, W0一辺条件, 三角形非零実類]
    remaining: [B–E, Cの全同型作用と実共役, 全GOAL最終監査]
  certificate_provenance:
    discharged: [iteratedIsoとbotIsoの全field, w0_safeの原始表, 三角形periodと指定spike]
    unresolved: []
  proof_use:
    used: [初段商表→再商→二段iso, 商全射→標準全単射, 原始全record等号→実Hom/H¹, 空辺型→空A零, 粗adequacy→細adequacy, 原有理比較→同じJ, W0辺単一性→potential→d0全射, 三角形d0のperiod零→同じ非零H¹類→非全射]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [PRに固定する対象focusedと累積個別公理ログ]
  blocking_findings: [標準PR独立査読前]
  next_obligation: Bの全有限分類とCの全同型輸送・自然選択
```
