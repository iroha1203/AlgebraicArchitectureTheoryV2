# G-137 証明記録

固定GOAL・設計・共通基準: `d6d19ba0b199d499e1aa0239b60d71c50aa4bee4`。
GOAL blob: `00278db46e595fbe30762a1bb969230f77828f4f`。
既存宣言の参照版: `f3ae0eab35186e2259fa030eb23fb4657180a868`。
追跡: [#5358](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5358)。

## 現 proof obligation

T0・A–Eを固定したまま進める。Cycle 1は
[PR #5360](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5360#issuecomment-6168427100)、
merge `7f6ba524fb2f8d18c5707563d442b74a10cb1d56` で受理済み。
Cycle 2は[PR #5361](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5361#issuecomment-6169485942)、
merge `f0ae3485d72fe4218e4afb448536d7ed65b74296` で受理済み。
Aの二段商同型、実cochain/H¹の恒等・合成、全Law・G-135診断接続を完了した。
W0の全粗化安全性と、三角形全関係商の不安全性も同じSafeで構成した。
Cycle 3は[PR #5362](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5362#issuecomment-6171574304)、
merge `7ab0d926988dc32f13d26252bdaa664e813b66fe` で受理済み。
Bの全有限分類、最大元/join判定、各不安全元の実cochain失敗出力を構成した。
三角形の二Safe粗化について全共通上界を排除した。
Cycle 4は[PR #5363](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5363#issuecomment-6172559576)、
merge `f253296cb1c1155ad6161c8601775dfcb05c2995` で受理済み。
Cの全原始同型による順序・実cochain/H¹輸送とSafe/Max作用を構成した。
Cycle 5は[PR #5364](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5364#issuecomment-6174995908)、
merge `8c2e3478d7781ea944cb7eabaa83f258c2c815fc` で受理済み。
B固定極大判定、C全Aut・自然選択iffと選択独立、Dの三一様主張の不成立と一般相互含意を確定した。
Cycle 6は[PR #5365](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5365#issuecomment-6176661031)、
merge `e09218510ed44defbf4a22dd90c0cac294ef30b8` で受理済み。
EのW0全候補/定数LawとW3の元比較同定/全A/同じhidden類を完了した。
Cycle 7は[PR #5366](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5366#issuecomment-6178686416)、
merge `7cc9e6509e40867309a864c61c5c2bf81779fce0` で受理済み。
E W1の全三十分割対/同じ実比較/全Max/全Aut/自然選択を確定した。
Cycle 8は[PR #5367](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5367)、
merge `8d323b16c468a60ba387a1cee4c88b1acf63a8aa` で受理済み。
固定T0・A–Eの全構成・判定群は Researchで `target-theorem-proved`。
[同head正式完了判定](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5367#issuecomment-6180099392)は、
標準PR受入後の別fresh数学2・Lean2全票とroot統合が正確に `No major findings`、全15gate pass、中心未確認なしを記録する。
以下のcycle selection/result/auditsと完了候補の記述は各固定headでの履歴であり、正式最終判定はこの参照へ固定する。
Formalへの蒸留は未実施、`unported (Research-proved)`。

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

## Cycle 3 selection

[Cycle 2同期とCycle 3開始](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5358#issuecomment-6169532688)で実装前に固定。
merge後main CI成功は[追記](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5358#issuecomment-6169638532)に固定した。

```yaml
ledger_type: target_cycle_result
goal: G-137-aat-safe-coarsening-order
cycle: 3
goal_blob_sha: 00278db46e595fbe30762a1bb969230f77828f4f
base_oid: f0ae3485d72fe4218e4afb448536d7ed65b74296
tracking_issue: 5358
report_path: research/reports/G-137-aat-safe-coarsening-order.md
selection:
  proof_state_ref: Cycle 2受理とmerge同期
  proof_dag_predecessors: [Cycle 2.botIso, Cycle 2.safe_iff_decision, G135実有理診断, RI.CochainEquiv.h1Equiv, mathlib有限半順序]
  milestone: Bの全粗化・全安全元・全極大元と最大元/joinの有限分類
  proof_obligations: [全同値関係対の有限列挙, 原始同型の実cochain生成と恒等商Safe, 安全/極大一覧の正しさと完全性, 各安全元上の極大元, 最大元と唯一極大と安全共通上界条件の同値, 最大元/joinの原始判定と正負証拠, 各不安全元の実kernelまたはcoker失敗証拠]
  exit_criteria: [全関係表列挙と完全性, 恒等商の同じ実H1全単射, 全安全/極大のmem iff, 有限極大存在と最大元同値, greatest/join判定の正負出力, 全共通上界排除, 原始比較からの失敗Aと実非零商類/汎関数, focusedと全宣言公理監査]
  selection_reason: Bの全候補を尽くしDの最大元/join反証を実比較へ戻す
  expected_result_type: proof-obligation-discharged
  lean_targets: [IsomorphismCochains.lean, IdentitySafety.lean, FiniteClassification.lean, FailureCertificates.lean, FiniteDecisions.lean]
  risks: [Safeの上方閉性を仮定すること, join失敗だけで全共通上界を排除すること, 形式的EMを具体失敗証拠へ読み替えること, 同次元同型による恒等比較代用, 有限一覧を入力fieldに置くこと]
  unchecked: [正式PR査読]
```

Bの固定極大元判定はCの全自己同型作用を生成する後続到達点で扱い、固定要求から削除しない。

## Cycle 3 条項・実宣言・前提使用

| 固定条項 | ファイル・宣言 | 構成・使用先 |
| --- | --- | --- |
| 恒等粗化の同じ実安全性 | `IsomorphismCochains` の `subsetChart/Edge/FaceEquiv`, `subsetCochainEquiv`, 逆Hom次数評価API、`IdentitySafety.bot_preimage`, `safe_bot` | 全原始同型のq/有向辺/K1台保存から選択セルと全三次数同型を生成。恒等商ではbotIsoを適用し、原始商比較と逆生成Homの全record一致を証明して同じH¹へ降ろす。Cの全同型作用・共役図式は後続。 |
| 全原始分割対 | `FiniteClassification.relationTable`, `relationOK`, `fromRelationTable`, `allSetoids`, `mem_allSetoids`, `setoidFintype`, `allCoarsenings`, `mem_allCoarsenings` | 全有限順序対表の冪集合、反射/対称/推移の有限検査から全同値関係と全独立分割対を尽くす。安全元一覧を入力として受け取らない。 |
| 全安全/極大一覧 | `safeCoarsenings`, `mem_safeCoarsenings`, `maximalCoarsenings`, `mem_maximalCoarsenings`, `exists_maximal_above`, `safeCoarsenings_nonempty`, `maximalCoarsenings_nonempty` | 全分割対をG-135同じ全A有理判定でfilterし、包含について全極大元をfilter。soundness/completenessは同じSafeへの必要十分。恒等Safeと有限半順序から非空・各Safe上の極大元を生成。Safeの上方/下方単調性を仮定しない。 |
| 最大元の有限特徴づけ | `greatest_iff_unique_maximal`, `greatest_iff_safe_upper_bounds`, `greatest_iff_card_one`, `no_greatest_witness`, `greatest_of_join_closed` | 最大元・唯一極大・全安全対の安全共通上界を有限性から同値にし、最大元負では全共通上界排除を得る。join閉性は安全な共通上界を与える方向だけを使う。 |
| 同じ実cochainへの失敗証拠 | `FailureCertificates.allCycles`, `cochainClass`, 公開評価/全射/d0零/自然性、`KernelFailure`, `CokerFailure`, 両生成定理と `failure_exists`, `class_nonzero`, `annihilate_sum`, `not_injective`, `not_surjective` | 原面なし条件→全cycle→既存の実H¹商。核の非零類から粗代表元・細potential・粗d0像で零/元で1の有理汎関数を構成。literal余核から細cycleと細d0像+粗cycle比較像で零/元で1の汎関数を構成。次元差だけを証拠にしない。 |
| 全不安全元の領域と証拠 | `FiniteDecisions.failureRegions`, `mem_failureRegions`, `failureRegions_nonempty`, `primitive_kernel_zero_iff`, `RegionFailure`, `regionFailure_exists`, `UnsafeWitness`, `unsafeWitness`, `unsafeWitness_region_mem`, `UnsafeWitness.not_safe` | 全有限部分領域を原始有理kernelへ通す。各Setも有限表で尽くされる。同じ計算Jの核成分で核/余核分岐を選び、原面型が空であることを放電してcochain証拠を生成。生成領域は失敗一覧に所属し、証拠から実不安全性を再検証できる。 |
| 最大元の入力ごとの正負判定 | `greatestDecision`, `greatestDecision_eq_true`, `GreatestWitness`, `greatestWitness`, `NoGreatestWitness`, `noGreatestWitness_exists`, `noGreatestWitness` | 全極大一覧のcard=1を有限Boolで判定。正なら原始分割対と全Safeに対する最大性。負なら二Safe元・全共通上界Wの排除と、各Wの個別失敗領域/実cochain証拠を生成。同じ失敗Aを全Wに仮定しない。 |
| joinの入力ごとの正負判定 | `joinDecision`, `joinDecision_eq_true`, `JoinFailure`, `joinFailure_exists`, `joinFailure` | 全分割対の全順序対を有限kernelへ通し、両Safeの場合に同じjoinの安全性を判定。負出力は元二Safe分割とそのjoinの実失敗証拠。 |
| 原始正負発火 | `FiniteDecisionInstances` のW0最大元/全極大一覧/最大元Bool/joinBool/空失敗一覧、三角形top Bool false/非空失敗一覧/実UnsafeWitness、`CertificateInstances` | 指定W0では全関係が最大元で全極大一覧はsingleton、両Boolはtrue。原始三角形topの同じ安全判定はfalseで実cochain証拠を出力。証拠構造の正負instanceを実入力から生成し、一般核/余核APIは同じ非零三角形複体の零/恒等Homでも正負確認する。零HomはT0粗化反例の代替にしない。 |
| 原始最大元/join負の発火 | `TriangleCuts.cutMap`, `cut`, 元/商セルと全分類、`cutHom`, 全評価API、`cutLift`, `cutPotential`, `cutCoarsePotential`, `cut_surjective/injective_representatives`, `cutHom_bijective`, `cut_full_bijective`, `cut_safe`、`TriangleCounterexamples.common_upper_bound_top`, `common_upper_bounds_unsafe`, `cut_join_top`, `no_greatest`, 両Bool false、指定/有限生成負出力 | 元3辺を保持する同じ三角形で、iとi+1を合併しi+2を分ける粗化を生成。残る二逆向きセルを別に保持。元cochainと細potential/粗potentialの正逆liftで同じ実H¹比較を全Aで全単射と証明。cut0/cut1の全共通上界をtarget/chartの全関係と証明し、同じtop不安全性から全排除。最大元とjoinの両有限負producerが原始入力で発火。Dの全一様主張とCの全固定点排除は後続である。 |

### 前提・provenance・proof-use

T0の有限原始S/T/V、全射q、有向非対角辺、非空台、空面、ℚは本文由来。
汎用補助は使わない有限/非空条件を要求しない形で一般化し、全T0への適用を保持する。
全関係表の列挙にはT/Vの有限性、既存全A判定にはSの有限性を使用する。
原始同型の三全単射/q/辺/台保存は一般方向仮定で、恒等商ではCycle 2のbotIsoが全fieldを放電する。
Safe非空は仮定でなく `safe_bot` から生成し、有限性から極大元を得る。
一般最大元同値の非空条件も入力適用では恒等から放電する。

面なし条件、非全単射/非単射/非全射は一般certificate生成定理の方向仮定。
入力適用では元Empty面を使ってd1零を証明し、全Aの原始有理判定から失敗を導出する。
核/余核branchは計算されたJ核成分で決める。代表元/potential/正規化汎関数は同じ実線形商から生成される。
証拠出力structureには証明済みの結論を格納するが、producerは原始表→有限一覧→同じ実射→商代表元を通り、
期待rank/安全一覧/失敗certificateを入力に置かない。非計算的選択はこれらの証明済み有限/線形構成に用いる。
未評価の排中律だけを入力ごとの判定に使っていない。

三角形の指定原始辺/台と有理period非零はCycle 2受理済み。
今回のcut支持・辺・部分像・全原始表は同じ入力から生成する。原始元辺への全射と全商二辺分類を証明し、
実pullbackの0/1/2成分・canonical全A逆像transportを保持して実H¹へ接続する。
cut0/cut1の安全性を前提として受け取らず、元cochain/potentialの正逆liftから放電する。
全上界W排除は関係包含の反射/対称/推移で行い、join失敗からの推論にはしない。

再利用はCycle 1–2の受理refs、G-107の `CochainEquiv.toHom_h1Map_bijective`、
G-133の全Hom型輸送・`h1Map_mk_eq_zero_iff`・`h1_mk_mem_range_iff`、
G-135の `primitiveDiagnostic_eq_blockDefect`・全A Bool・実rank/核/余核接続。
固定参照版と現在の必要定義/statement/適用を照合し、受理predecessorの内部全履歴は再認定しない。
mathlibの有限順序の極大存在、Setoid、Finset冪集合、有限次元双対分離、実線形核/商を固定版で使用する。

### Cycle 3 result proposal

```yaml
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: 全有限関係/安全/極大一覧、恒等実安全性、最大元の三特徴づけ、最大元/join有限正負判定、全不安全元の実cochain失敗出力、原始正負発火
  exit_criteria_status: [上記全一般構成と必要十分, 恒等商とW0正例, 三角形二Safe粗化の全共通上界排除と同じjoin失敗, 個別検証と累積全宣言公理はPR証跡へ固定]
  split_reason: none
  completion_candidate: no
  lean_artifacts: [IsomorphismCochains.lean, IdentitySafety.lean, FiniteClassification.lean, FailureCertificates.lean, FiniteDecisions.lean, FiniteDecisionInstances.lean, TriangleCuts.lean, TriangleCounterexamples.lean, CertificateInstances.lean]
  evidence: [Cycle 3条項対応表]
  claim_mapping:
    theorem_names: [safe_bot, mem_allCoarsenings, mem_safeCoarsenings, mem_maximalCoarsenings, exists_maximal_above, greatest_iff_unique_maximal, greatest_iff_safe_upper_bounds, greatestDecision_eq_true, joinDecision_eq_true, regionFailure_exists, cut_safe, common_upper_bound_top]
    source_labels: [B全有限分類と最大元/join, C実cochain同型生成, D対応負証拠の基礎, E W0部分評価]
    conjuncts: [Cycle 3対応表]
    undischarged_assumptions: []
    acceptance_point: 全原始候補の有限判定と同じ実cochain証拠付き正負出力を生成し具体的原始入力で発火
    port_status: unported
audits:
  premise_delta:
    discharged: [恒等実比較全単射, 全関係/部分領域有限列挙, Safe非空, 全極大存在, 全共通上界排除, 実核/余核代表元と汎関数, 三角形cut安全性]
    remaining: [B固定極大判定, C全作用/実共役/自然選択, D全一様主張と接続, E全指定評価, 全GOAL最終監査]
  certificate_provenance:
    discharged: [元表→全有限表→同じ実有理Bool→実H1核/余核→元cochain/potential/dual, 三角形指定二粗化の全原始生成]
    unresolved: []
  proof_use:
    used: [原始同型→全セル/実cochain→恒等商Safe, 全関係表→全分割対→全A判定→Safe/Max一覧, 恒等Safe→有限極大→最大元同値, 実非全単射→同じ商非零類→cochainと汎関数, 原三角形cochain→cutLiftとpotential→実全単射, 二cut包含→全関係上界→同じtop失敗]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [PRに固定する対象個別検証と累積個別公理ログ]
  blocking_findings: [標準PR独立査読前]
  next_obligation: Cの全原始同型作用・実共役・全固定極大元と自然選択
```

当初の5 lean_targetsに対し、有限判定と証拠構造の正負発火のため4つの従属証拠moduleを追加した。
終了条件・固定GOAL/設計は変更せず、三角形cutの実比較と全上界排除を今回の一般出力へ通した。
新9sourceと同じreport/manifestだけが書込対象で、Formal蒸留・全体buildは未実施。


## Cycle 4 selection

実装前の[Cycle3同期・Cycle4選定](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5358#issuecomment-6171616652)に固定。
Cycle3 main CI成功と対象11file一致は[main確認](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5358#issuecomment-6171727657)。

```yaml
ledger_type: target_cycle_result
result:
  goal_id: G-137
  milestone: Cの全原始同型による実比較輸送
  proof_obligation: 全S/T/V同型から順序・商入力・全cochainと同じH1を輸送しSafe/Maxを保存反映
  lean_targets: [CoarseningTransport.lean, IsomorphismComparison.lean, SafeIsomorphism.lean, IsomorphismActionInstances.lean]
  exit_criteria: [元商写像を保つ順序と商入力同型, 全0/1/2比較図式と実H1共役, 恒等合成, 全AとSafe/Max両方向, 原始作用発火, 個別Leanと全宣言公理, 独立数学2Lean2とroot受入CImain同期]
  expected_result_type: proof-obligation-discharged
  completion_candidate: no
```

### Cycle 4 条項・実宣言・前提使用

| 選定条項 | 実宣言 | 入力からの生成・前提使用・証拠 |
| --- | --- | --- |
| 全分割対の包含順序輸送 | `transportSetoid`, `transportSetoid_rel`, `PrimitiveIso.coarseningOrderIso`, target/chart関係API | 逆全単射のSetoid.comapから両包含を保つ順序同型。target/chartは独立な全Setoidの積。安全性を入力せず、軌道同一視なし。 |
| 恒等・合成・逆の全順序同型 | `coarseningOrderIso_refl`, `coarseningOrderIso_trans`, `coarseningOrderIso_symm` | 全OrderIso recordのext等号。元関係への二段逆像は同じ原始合成と一致。忘却後の部分fieldだけの等号にしない。 |
| 元商写像を保つ商入力同型 | `transportQuotient`, `quotientTarget/Chart`, 各mk評価、`quotient_edge_iff`, `quotient_support_iff`, `quotientIso`, source/target/chart API | sourceは同じ元source全単射、read_commは元q可換性を商写像に適用。辺は非対角と原辺存在を両方向に輸送、台は同じfiber合併の像を輸送。全fieldを元表から生成。 |
| 有向部分辺像の自然性 | `quotientEdgeMap_naturality` | 内部辺は同じ関係輸送で両側none。残る辺は元商写像の可換性と両端一意性でsame-direction同じ商辺にする。逆向き辺を併合しない。 |
| 独立商supportedと実cochain同型 | `quotientSubsetChart/EdgeEquiv`, 各val、`quotientSubsetEquiv`, 逆f0/f1評価 | quotientInputを独立quotientSupportedへ全record同定する受理C2のFintypeを保持。受理C3の原始セル同型→非依存関数再添字→元d0/d1互換を適用し、期待H¹同型を入力しない。 |
| canonical逆像と同じ全Hom | `canonical_preimage`, `reindexedMapsTo`, `reindexedComparisonHom`, `reindexedComparisonHom_eq_transport` | 元商target写像の可換性から全Set等号を生成。細subsetの再表示は旧生成Homを複体全体で等号transportしたものと証明し、比較を別射へ置換しない。 |
| 全0/1/2自然性と同じH¹共役 | `comparison_cochain_square`, `comparison_h1_square`, `comparison_actual_h1_square` | f0は元商chart可換性、f1はnone/some部分辺自然性、f2は元Empty。全Hom等号を既存H¹商の合成へ降ろし、G134 incidence埋め込みを同じ実射へ戻す。 |
| 全A全単射、Safe、Maxと最大性の両方向 | `comparison_bijective_iff`, `safe_iff`, `maximal_forward`, `maximal_iff`, `greatest_forward`, `greatest_iff` | 生成cochain同型の実H¹逆を両側で用いる。同じH¹写像の共役と全Hom等号transportから全単射iff。商target全単射の逆像で全Aを尽くす。全安全元の包含をOrderIsoで保存反映し極大/最大へ接続。 |
| 原始作用の正負発火 | `w0_top_fixed`, `w0_top_maximal`, `Triangle.rotationChart`, `rotation`, `rotation_ne_refl`, `rotation_cut`, `rotation_moves_cut0`, `rotation_cut0_safe`, `identity_cut0_fixed`, `rotation_top_not_safe` | W0の同じ最大元は全Aut固定。三角形回転のq/E/台を元表から放電。全cutの関係輸送を評価し、指定Safe cut0が動くことを示す。恒等作用は固定、同じ不安全topは共役で不安全のまま。 |

material premiseはT0の有限/原始q・非対角辺・非空台と、一般原始同型の全S/T/V全単射・q/辺/台保存。
前者は原始幾何、後者は一般同型の方向条件である。商入力同型と三角形回転の適用では全fieldを原始表から放電する。
cochain/H¹同型は原始同型からの出力であり、Safeや期待rankをfieldへ加えない。
商target/chart全単射は元商写像を保持し、元source全単射は商read_commに使用する。
微分/比較は既存実複体、H¹は元cycleのd0像による商である。

新規部分は全分割対のOrderIso、商入力の全同型、部分辺の自然性、全Hom/H¹共役、Safe/Max作用、原始回転の実作用。
受理C1/C2の原始商と同型、C3のセル再添字/H¹生成・恒等安全性・三角形cut証明を再利用する。
G107実H¹同型、G133実Hom合成/等号transport、G134同じincidence埋め込み、G135診断保存の既存接続を使用する。
現在の型・必要定義・実引数・proof-useと受理refを独立査読で照合し、既存内部全履歴の再認定はしない。

### Cycle 4 result proposal

```yaml
ledger_type: target_cycle_result
result:
  goal_id: G-137
  result_type: proof-obligation-discharged
  completion_candidate: no
  overall_goal_status: target-proof-checkpoint
  formal_port_status: unported
  status: proposed
  evidence: [Cycle4条項対応表]
  validation_refs: [PRに固定する対象個別Leanと累積個別公理]
  remaining: [B固定極大有限判定, C全Aut分類と固定点自然選択iffと同型選択独立, D三一様主張と接続, E全指定W0W1W2W3評価, 全GOAL最終独立監査]
```

Researchの対象個別sourceと単一focusedだけを検証する。Research全体build/aggregate/全file elaboration、
Formal移植・本体全体buildはこのcycleで実施しない。


## Cycle 5 selection・結果提案

実装前の[Cycle4同期・Cycle5選定](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5358#issuecomment-6172660268)で固定した。
Cycle4の[main CI確認](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5358#issuecomment-6172817239)まで完了済み。

```yaml
ledger_type: target_cycle_result
goal: G-137
cycle: 5
goal_blob_sha: 00278db46e595fbe30762a1bb969230f77828f4f
base_oid: f253296cb1c1155ad6161c8601775dfcb05c2995
tracking_issue: 5358
report_path: research/reports/G-137-aat-safe-coarsening-order.md
selection:
  proof_state_ref: Issue5358 comment6172660268
  proof_dag_predecessors: [C1 PR5360 comment6168427100, C2 PR5361 comment6169485942, C3 PR5362 comment6171574304, C4 PR5363 comment6172559576]
  milestone: B固定極大判定・C全Autと自然選択iff・D三一様主張の決着
  proof_obligations: [全S/T/V原始Aut列挙, 全固定極大表と正負出力, 全T0 groupoidと同型類全体の自然選択iff, 全同型選択独立, 全三一様主張と相互含意, 原始全Max固定点排除と各負結果]
  exit_criteria: [上記一般構成・両方向・全量化, 原始正負producer発火, D各側確定, 対象個別Leanと全宣言公理, 独立数学2Lean2標準PR査読, root受入・exact-head CI・main同期]
  selection_reason: 受理C4の全実同型作用から固定点・自然選択と一様主張へ直接接続する
  expected_result_type: proof-obligation-discharged
  lean_targets: [FiniteIsomorphisms.lean, FixedMaximalDecision.lean, FinitePrimitiveModel.lean, NaturalMaximalSelection.lean, TriangleMaximalClassification.lean, UniformDecisions.lean, FixedSelectionInstances.lean]
  risks: [全Autを特定生成元へ縮小しない, 全Max固定点排除, 自然選択の出力はRそのもの, 同型選択独立, 全T0量化, 同じ実比較への接続, EMだけで決着しない]
  unchecked: [PR独立査読・root受入・CIは作成後に固定する]
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: 全原始Aut有限表と固定極大判定を生成し全groupoid自然選択iffを閉じた。三角形全分割・全Safe・全Max分類から全固定点を排除しP_G/P_J/P_Nを各原始証拠で反証、相互含意は一般構成で証明
  exit_criteria_status: [一般構成・両方向と原始正負はsourceへ固定, 対象個別Leanと累積個別公理はPR検証証跡へ固定, 独立査読・root受入・CIはPR gateで判定]
  split_reason: none
  completion_candidate: no
  lean_artifacts: [上記新7source]
  evidence: [下記Cycle5条項対応表とspine declaration list]
  claim_mapping:
    theorem_names: [mem_allPrimitiveIsos, mem_fixedMaximalCoarsenings, fixedMaximalDecision_eq_true, naturalSelection_iff_fixed, naturalSelection_iff_decision, transport_independent, Triangle.maximal_iff_cut, Triangle.rotation_moves_all_maximal, P_J_implies_P_G, P_G_implies_P_N, not_P_G, not_P_J, not_P_N]
    source_labels: [GOAL B固定極大有限判定, GOAL C全同型自然選択, GOAL D一様主張]
    conjuncts: [下記Cycle5条項対応表]
    undischarged_assumptions: []
    acceptance_point: 原始全Aut有限生成と実作用、同型類全入力と全射への選択独立、全Max排除・元比較負証拠を接続し全一様主張の具体的側を確定
    port_status: unported
audits:
  premise_delta:
    discharged: [全Aut原始保存field, 有限正負出力全field, 固定元からの全自然性, 三角形全候補と全Max移動, 全T0原始モデルの埋め込み]
    remaining: [E全指定評価と全GOAL最終査読]
  certificate_provenance:
    discharged: [FixedMaximalWitnessとNoFixedMaximalWitnessは原始有限表から生成, NaturalMaximalSelectionは同じ固定分割の全原始輸送から生成, D反例は元三角形と受理C3/C4同じ実比較・作用]
    unresolved: []
  proof_use:
    used: [有限全Equiv表とq/辺/台保存, 全Maxと全Aut, OrderIso恒等合成逆, Safe/Max保存反映, 固定性と原始逆同型, 全共通上界排除とjoin実失敗, 全Max回転移動]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [PRに固定する新7source個別Lean・公式単一focused・全累積宣言個別公理・共通scan]
  blocking_findings: []
  next_obligation: Eの同じW0/W1/W2/W3全指定評価と全GOAL最終監査
```

### Cycle 5 条項・実宣言・入力生成の対応

| 固定要求 | 実宣言・spine | 原始入力・前提使用・必要な全方向 |
| --- | --- | --- |
| 全S/T/V原始同型の有限生成 | `IsoTable`, `isoTableOK`, `isoTableOK_iff`, `fromIsoTable`, `allPrimitiveIsos`, `mem_allPrimitiveIsos` | 元の全Equiv三表の積をq/有向辺/台保存だけでfilter。全fieldを検査から生成し、任意原始Isoの三表を戻して完全性。特定chart回転や安全性で候補を減らさない。 |
| 全Aut・軌道・安定化集合 | `PrimitiveInput.allAut`, `mem_allAut`, `orbit`, `mem_orbit`, `stabilizer`, `mem_stabilizer`, `stabilizer_identity/composition/inverse`, `orbit_maximal`, `fixed_iff_orbit_singleton` | 同じ全原始自己同型表に同じ受理C4 OrderIsoを作用させる。安定化の全原始恒等/合成/逆閉性、軌道の全Max保存と全固定性iffを証明する。 |
| 固定極大判定と正負出力 | `fixedMaximalCoarsenings`, `mem_fixedMaximalCoarsenings`, `fixedMaximalDecision`, `fixedMaximalDecision_eq_true`, `FixedMaximalWitness`, `fixedMaximalWitness_exists`, `fixedMaximalWitness`, `NoFixedMaximalWitness`, `noFixedMaximalWitness_exists`, `noFixedMaximalWitness` | 全Maxを全Aut固定検査に通す。正は同じ元RとMax/全固定証拠。負は全Maxの各Rに全原始表内の移動Autを生成。各証拠のdecision_true/decision_not_true/fixed_emptyで同じ有限判定を再検証する。 |
| 全T0と全原始同型のgroupoid | `FinitePrimitiveModel`, `ofInput`, `ofInput_input`, `primitiveGroupoid`, `hom_eq`, `identity_eq`, `composition_eq` | 全非空有限S/T/V型と原始入力を束ねる。任意T0 inputを埋め込める。Homは元PrimitiveIsoそのもの、恒等/合成/逆と全法則を元record extから生成。H¹/安全性fieldを射に追加しない。 |
| 同型類全体・全射への自然選択 | `IsoClass`, `base`, `isoTo`, `NaturalMaximalSelection`, `selectionFromFixed`, `selectionFromFixed_select`, `selection_fixed` | Mと同型な全T0入力を対象とし、その間の全原始Isoを自然性で量化。Rそのものを同じOrderIsoで輸送しMax保存から極大性を生成。自然性は原始合成と固定性から導く。 |
| 同型選択独立と必要十分 | `transport_independent`, `selectionFromFixed_base`, `naturalSelection_iff_fixed`, `naturalSelection_iff_decision`, `selectionFromDecision`, `selectionFromDecision_base` | 任意α/βについてαとβ逆の合成を元Autとして固定性を使用、輸送後Rが一致。逆は自然性をMの全Autへ適用。元入力で同じRを返し、orbit選択に置換しない。 |
| 原始全候補/Safe/Max分類 | `Triangle.three_rel_ext`, `classify_chart`, `classify_coarsening`, `safe_iff_bottom_or_cut`, `cut_neighbor_iff`, `cut_le_iff`, `cut_maximal`, `maximal_iff_cut`, `safeCoarsenings_eq`, `maximalCoarsenings_eq`, `maximal_card_three` | 三chart全同値関係を反射・対称・推移から五分割に尽くす。受理C3の同じcut比較Safeとtop実失敗から全Safe四元、全Max三cutを導出する。予想一覧を入力しない。 |
| 全固定点排除と負producer発火 | `Triangle.rotation_moves_cut`, `rotation_moves_all_maximal`, `cut0_orbit`, `fixedMaximalCoarsenings_empty`, `fixedMaximalDecision_false`, `specifiedNoFixedOutput`, `generatedNoFixedOutput` | 全Max三cutを受理C4原始回転が全て動かす。全Aut表内の同じ回転から全Max負出力を明示生成し、同じfalseから一般producerも発火。単一非自明軌道だけで打ち切らない。 |
| 全一様主張と一般接続 | `GlobalNaturalMaximalChoice`, `P_G`, `P_J`, `P_N`, `globalFromGreatest`, `globalFromGreatest_select`, `P_J_implies_P_G`, `P_G_implies_P_N` | 全T0束で量化。join閉性から有限非空安全poset最大元、全最大元から同じ元分割を選び全原始同型の最大性保存・一意性で自然性。反証済み主張の矛盾消去だけで含意を証明しない。 |
| 各一様主張の原始負の側 | `triangleModel`, `triangleModel_input`, `not_P_G`, `not_P_J`, `not_P_N` | P_Gは受理C3二Safe元の全共通上界排除、P_Jは同じcut対/join/top実失敗、P_Nは全Max回転移動と全groupoid自然性の矛盾。三つとも不成立の側を確定する。 |
| 固定極大・自然選択の原始正負と検証 | `w0_fixedMaximalCoarsenings`, `w0_fixedMaximalDecision_true`, `w0SpecifiedFixedOutput`, `w0GeneratedFixedOutput`, 各mem/eq_top/decision、`w0_top_orbit/stabilizer`, `w0_no_negative_fixed_output`, `triangle_no_positive_fixed_output`, `triangleGeneratedNoFixed_moves`, `w0Model`, `w0NaturalSelection`, `w0SpecifiedNaturalSelection`, 各base/exists、`triangle_no_natural_selection`, `w0_identity_isoTableOK`, `triangle_edgeless_isoTable_not_ok` | W0同じ最大topが全Aut固定で表はsingleton。正の指定/一般producerと全同型類自然選択が発火、負証拠は不存在。三角形は正証拠不存在・一般全Max負出力発火・同型類全入力自然選択不存在。 |

### Material premise・provenance・field-content

全finite/nonempty S/T/V・q全射・非対角有向辺・非空台・K1・Empty面・ℚは固定T0原始幾何。
一般PrimitiveIsoの三全単射とq/辺/台保存はCの方向条件であり、全有限同型表と具体回転の適用では原始表から放電する。
一般固定元からの自然選択producerのMax/全固定性は必要十分の方向条件。有限正出力とW0では元有限表・同じ実比較から生成する。
負の有限producerのfalseは方向条件、三角形の全Max分類と元回転移動が具体適用で放電する。
`P_G`/`P_J`を仮定する相互含意は固定Dが要求する条件付きの一般構成であり、三つの成立判定とは区別する。

`FixedMaximalWitness`のR/Max/fixed、`NoFixedMaximalWitness`の全Max移動、自然選択のselect/maximal/naturalは出力fieldである。
各producerが全有限原始表・同じOrderIso/Safe/Maxから全fieldを生成し、構造を受け取るだけの証明にしない。
前提の使用は、三全単射→原始保存検査→全Iso、全Max/Aut→固定表、原始合成/逆＋固定性→選択独立、Max保存→全出力極大、
原始全分類/受理cut実比較→全Max、受理回転実作用→全固定点排除、全共通上界排除/同じjoin実失敗→各一様否定、で追跡する。
`not_P_G`は全共通上界Wを排除する `Triangle.common_upper_bounds_unsafe` / `Triangle.noGreatestOutput`、
`not_P_J`は同じ原始joinの `Triangle.joinFailureOutput` とその実cochain失敗へ接続する受理C3依存を保つ。
`not_P_N`は一つの移動元だけでなく `maximal_iff_cut` と `rotation_moves_all_maximal` を必要とする。

### 再利用・新規部分・検証範囲

新規は全原始同型表、固定極大有限判定と全正負出力、全T0の実groupoid、全同型類自然選択iff/選択独立、
三角形の全候補/Safe/Max/固定点分類、全一様主張と一般接続・原始反証である。
受理C1–C4の同じ原始商/Safe/Max/実Hom/H¹/OrderIso/回転を再利用する。
G107の実H¹同型、G133の元比較合成、G134の同じincidence比較、G135の同じ有理判定は既存接続を維持し、
G136 Width入力のhidden/fiber接続はEの未完義務として残す。
必要な現在型・定義・実引数/proof-use・source版・受理refを独立査読で照合し、内部全履歴の再認定はしない。
対象新7sourceの個別Lean、公理・placeholder/hiddenBiDi/privacy/語彙/import方向/manifestをPRで固定する。
Research全体build/aggregate/全file検証、Formal移植・本体全体buildは実施しない。
E全指定W0/W1/W2/W3評価と別final packetによる全GOAL最終独立4査読は未完として保持する。


品質基準の新述語instanceペアは、`isoTableOK`をW0恒等三表の成立と三角形→辺なし表の不成立で示す。
固定極大の正/負証拠と同型類上の自然選択はW0/三角形で両側を示す。
`P_G/P_J/P_N`は全T0にわたる一様命題であり、原始反証により成立instanceは存在しない。
`GlobalNaturalMaximalChoice`も全Max固定点排除から不存在である。この理由を定義所有moduleに記載し、
条件付き相互含意の一般producerを具体的な成立判定と混ぜない。


## Cycle 6：W0全評価とW3の同じ実比較・hidden回帰

実装前selectionは[Issue5358 comment6175074020](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5358#issuecomment-6175074020)。
原始表は固定EのW0/W3そのもの。W3 minus=falseは全交互閉路、plus=trueはa₀だけ除去する。
W1/W2の未検証候補を本cycleの成功例として扱わない。

```yaml
ledger_type: target_cycle_result
goal: G-137-aat-safe-coarsening-order
cycle: 6
goal_blob_sha: 00278db46e595fbe30762a1bb969230f77828f4f
base_oid: 8c2e3478d7781ea944cb7eabaa83f258c2c815fc
tracking_issue: 5358
report_path: research/reports/G-137-aat-safe-coarsening-order.md
selection:
  proof_state_ref: Issue5358/comment6175074020
  proof_dag_predecessors: [受理C1-C5, G107全Law/実H1, G133全Homtransport, G134同じ原始比較, G135同じ実診断, G136指定Widthセル/比較/hidden/fiber]
  milestone: Eの指定W0とW3を同じ原始商/実比較/全A/全Law/有限判定へ通し全要求を閉じる
  proof_obligations:
    - W0一つの定数Lawと発生label/全値block/全候補全A実J/実Law射
    - W0同じ最大元とjoin閉性と全Aut固定の有限正出力
    - W3旧v/wおよびa/bと新T0端点対の全単射/非対角/元K1支持一致
    - 指定Rの元target/chart商写像とZMod2/Unitおよび旧reading/全台/空辺の同定
    - 新m_R部分セル像/全三次数u_R/元H1射を旧comparison2false/trueとactualMapへ可換同定
    - 全plusAと全properminusAのJ零およびfullminusJ(0,1)
    - 同じ指定Rの全候補/Safe表と有理全A判定の正負一致
    - 新literal余核の同じMV類を旧非零hidden類と係数/fiberRestrictionH1へ接続
  exit_criteria: [上記全指定構成/全比較/全A/同じ類/有限判定のLean証明, 全material premise放電, 個別Lean/全宣言公理/共通scan, 独立数学2Lean2標準PR監査/root受入/exact-head CI/main同期]
  selection_reason: 一般A-Dから指定支持依存入力への実比較/hidden接続gapを閉じる
  expected_result_type: proof-obligation-discharged
  lean_targets: [W0Evaluation.lean, W3Input.lean, W3Comparison.lean, W3Evaluation.lean]
  risks: [minus/plus反転, 旧セルを根拠なくsimple辺へ置換, 実商写像/逆像/全Hom忘却, 同次元H1による代用, hidden類交換, rank/J/Safe入力化, 既存全幅成果を新規計上]
  unchecked: []
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: W0全候補の同じ定数Law保存と有限正出力、W3旧元セル/比較の新原始商同定から全A診断/同じliteral余核類とfiber項を接続
  exit_criteria_status:
    - 原始W0/W3と全要求のsource証拠を下表へ固定
    - 個別対象Lean/公式単一focused/累積個別公理/共通scanをPRに固定
    - 標準PR独立4査読/root受入/CI/main同期はPR作成後に確定
  split_reason: none
  completion_candidate: no
  lean_artifacts: [W0Evaluation.lean, W3Input.lean, W3Comparison.lean, W3Evaluation.lean]
  evidence: [W0全実J/定数Law比較/同じ最大元固定元, W3元セルEquiv/全cochain図式/actualH1図式, W3全A診断/正負finite表, W3同じhidden/fiber]
  claim_mapping:
    theorem_names: [W0Evaluation.all_actual_defects, law_bijective, law_defect, greatestOutput_top, fixedOutput_top, W3.edgeEquiv, factor_region, cochain_square, actual_h1_square, actual_h1_square_direct, actual_defect, plus_safe, proper_actual_defects, full_actual_defect, minus_not_safe, plus_decision_true, minus_decision_false, gluing_hidden_same, gluing_hidden_nonzero, coefficient_hidden_same]
    source_labels: [GOAL E W0, GOAL E W3, witnesses W0/W3, T0/A-Cの同じ経路]
    conjuncts: [元W0定数Lawと全候補保存, 元W3T0入力/商同定, 全m/u/T図式, 全A/J/finite判定, 同じliteralhidden類/fiber接続]
    undischarged_assumptions: []
    acceptance_point: 入力data/元セルと受理先行定理から選定E二例の全構成と評価を生成
    port_status: unported
audits:
  premise_delta:
    discharged: [元T0原始表, W0全adequacy/値block/同じ実Law全単射, W3元セル全単射/台/商/部分像, canonical全A輸送と同じ実比較, 全有限正負, 同じhidden類とfiber]
    remaining: [E W1/W2全指定評価, 別final packet全GOAL最終独立4査読]
  certificate_provenance:
    discharged: [元W0Law/全候補/同じtrueの最大固定正出力, 元W3セル生成fine/coarse同型と比較図式, 元Width.gluingOldClassの逆セル輸送と同じ実余核]
    unresolved: []
  proof_use:
    used: [旧左端/右端/台から新辺/選択セル, 全商台と元mkから粗同型, 全d0/d1と実部分像から全Hom図式, H1図式から実核/余核同型, 旧plus/proper/fullから全A判定, 同じ旧非零hiddenとcoefficient_hidden_same]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [PRに固定する新4source個別Lean/公式単一focused/全累積個別公理/共通scan]
  blocking_findings: []
  next_obligation: W1/W2全指定候補の実比較/全分割/全A/Law/全Max全Aut/全上界評価
```

### 条項・元入力・実宣言対応

以下のW0宣言は `AAT.AG.SafeCoarseningOrder.W0Evaluation`、W3宣言は `AAT.AG.SafeCoarseningOrder.W3`。

| 固定要求 | 宣言とspine | 元データと必要な全方向/使用 |
| --- | --- | --- |
| W0定数Law、発生label、値block | `constantLaw`, `constant_eval`, `constant_adequate`, `constantLabel`, `constantLabelsUnique`, `constant_labels_card`, `constant_fiber` | Unit Sourceで一つのUnit値Lawを構成。全商readingへ定数値をdescend、同じ値block=全target、label1個。値型有限性を一般Law条件へ追加しない。 |
| W0全候補・全A・実Law保存 | `all_actual_defects`, `lawMap`, `lawMap_eq`, `law_bijective`, `law_defect`, `safeCoarsenings_eq_all`, `all_decision_true` | 受理単一有向辺の元H¹比較Safeを全R/空含む全Aで使う。同じ生成Law射を全Law iffから全単射/J零へ戻す。全候補表から除外しない。 |
| W0有限B正出力・最大・join・全固定 | `greatestOutput`, `greatestOutput_top`, `join_closure`, `fixedOutput`, `fixedOutput_top`, `top_fixed` | 同じtrueから一般producerを発火。全安全元の最大topと全原始Aut固定を再検証。受理C3/C5の同じ元出力と一致。 |
| W3同じ旧原始表をT0へ構成 | `Point`, `Chart`, `old_left`, `input`, `input_edge_iff`, `input_support`, `edgeEquiv`, `edgeEquiv_left/right` | q=id、vᵢ/wᵢの元台、false全a/b、trueだけa₀除去。旧辺名=左端なので端点対全単射、Boolの端点相違で非対角。K1交差を保持。 |
| W3指定商と元写像 | `coarsening`, `coarsening_target_iff`, `coarsening_chart_rel`, `targetEquiv`, `targetEquiv_mk`, `chartEquiv`, `quotient_support_all`, `quotient_chart_eq`, `quotient_no_edge`, `region`, `mem_region`, `factor_region`, `reading_comm`, `morphism_chart_comm`, `morphism_edge_comm`, `quotient_edge_none` | R=(ker fst,top)。元target商mkをZMod2のfstへ、元chart商mkをUnitへ同定。全台を元vᵢ台から生成、全内部辺none、旧mの元部分像と一致。 |
| W3全三次数支持複体同型 | `fineChartEquiv/EdgeEquiv/FaceEquiv`, `fineCochainEquiv`, `coarseChartEquiv/EdgeEquiv/FaceEquiv`, `coarseCochainEquiv` | 任意元領域Bの選択セル、K1とd0/d1から関数再添字の実同型を生成。期待rank/H¹同型fieldを入力しない。 |
| W3新旧同じ実比較と全Hom/H1 | `new_maps_to`, `old_maps_to`, `newHom`, `oldHom`, 各f0/f1 API、fine/coarse評価API、`newHom_eq_transport`, `oldHom_eq_transport`, `cochain_square`, `reindexed_h1_square`, `actual_h1_square` | 両canonical因子逆像を元領域へ等号transport。全f0/f1/f2可換図式を元商chart/内部辺noneから証明。全Homから同じH¹写像図式へ降ろす。 |
| W3同じ実核/余核/Jの同定 | `reindexedKernelEquiv`, `reindexedCokernelEquiv`, `reindexed_defect`, `actual_defect`, `actualFineCochainEquiv`, `actual_h1_square_direct`, `actualCokernelEquiv`, `actualCokernelEquiv_mk` | 全Hom図式と元H¹同型から実核/literal余核を輸送。canonical射も同じcell生成同型で可換。直接式のcoarse零は旧coarse_H1_zeroの実商を使用、全cochain図式を数値零に置換しない。 |
| W3全plus/properminus/fullminus | `plus_defect`, `proper_defect`, `full_defect`, `region_surjective`, `plus_safe`, `proper_actual_defects`, `full_actual_defect`, `minus_not_safe` | 同じ旧actualMapの既受理三診断を接続。targetEquivの全画像/逆像で商targetの全Aを尽くし、proper/fullを保存。空Aを除外しない。 |
| W3同じ有限入力の正負 | `candidate_mem_all`, `plus_mem_safe`, `minus_not_mem_safe`, `plus_decision_true`, `minus_decision_false` | 指定同じRを全分割対に入力。plus全A保存、minus同じfull失敗から全安全表/同じ有理全A判定が一致する。 |
| W3同じMV hidden非零/fiber | `gluingRegion`, `gluingFineClass`, `gluingHiddenClass`, `gluing_fine_same`, `gluingHiddenClass_eq_mk`, `old_hiddenClass_eq_mk`, `gluing_hidden_same`, `gluing_hidden_nonzero`, `coefficient_hidden_same` | 元G136 gluingOldClassを元セルfine同型の逆で移し、新literal余核へ入れる。実余核同型が同じ旧hidden類へ戻す。旧非零性と同じ係数列/fiberRestrictionH1の同じ元に接続。 |

### Material premise・再利用と検証範囲

T0有限非空S/T/V・全射q・非対角有向単純E・非空支持・K1/Empty/ℚは固定入力幾何。
具体W0/W3は定義と既存有限/非空instanceから全条件を放電する。一般領域X/Bやproper条件は評価の方向条件。
全A適用では `region_surjective` が任意商領域を生成し、proper条件も元全単射の画像/逆像から導出する。
W0のLaw adequacyは元定数評価から、全候補保存は元単一辺実比較から、最大/固定出力は同じfinite trueから放電。
W3の同型fieldは元セル全単射とK1・実d0/d1から、領域MapsToは同じcanonical因子から放電する。
JやSafe/hidden非零を構成recordの入力fieldへ移さない。`gluingFineClass`は指定旧MV類の同じセル同型による逆輸送であり、
J=(0,1)から任意の同次元類を選ぶ構成ではない。`gluing_hidden_same` と `coefficient_hidden_same` が元代表の使用先を固定する。
新Prop述語/certificate構造は追加していない。plusの指定R保存、minusの同じR失敗が具体正負回帰である。

新規はW0定数Lawの元全候補評価、W3指定原始表のT0接続・実商/全Hom/H1同定・有限判定/同じhidden類の接続。
G136の `Width.plus_defect/proper_defect/full_defect/gluing_hidden_nonzero/coefficient_hidden_same` のn=2を再利用する。
source参照は固定既存版 `f3ae0eab35186e2259fa030eb23fb4657180a868`、G136受理PR5336とtracking Issue5321の
[完了記録](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5321#issuecomment-6117232196)。
使用する現在型・必要定義・実引数/proof-use・関連変更を監査する。既存全有限幅分離・同じ局所大域同値は新規成果に数えない。
受理C1-C5/G107/G133/G134/G135の同じ原始商/実比較/Law/有限表/実輸送を維持する。

新4source個別Lean、公式単一focused、累積対象宣言の全個別公理照会と共通scanをPRコメントへ固定する。
Research full/aggregate/全module/全file検証、Formalへの蒸留・本体全体buildは未実施。
W1/W2の全指定評価、別final packetでの全GOAL最終独立4査読と完了同期は未完として保持する。

### Cycle6 初回査読後の品質修正

初回の独立数学2/Lean2は中心finding0・Minor issues。全4報告をrootが全文読了し、
[数学票](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5365#issuecomment-6176133121)と
[Lean票](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5365#issuecomment-6176223618)へ記録した。
`constant_fiber`は既存`mem_labelValueFiber`、W3の非対角性は`Width.right_apply`、
商chart逆写像の領域条件は`mem_region`を使う。
定理名`joinClosure/newMapsTo/oldMapsTo`を`join_closure/new_maps_to/old_maps_to`へ改め、
全使用sourceとreport対応を同じPRで更新した。数理statement・原始表・選定要求・premise statusは維持する。
定理名とdefinition内proofの変更により直接対応の資格を使わず、修正headで独立4票の正式査読を再実行する。

## Cycle 7：指定W1の全分割・実比較・全自己同型

実装前selectionは[Issue5358 comment6176740665](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5358#issuecomment-6176740665)。
指定S=T=Bool/q=id、V=ZMod4、i→i+1四辺、全chart台、Empty面、ℚを維持する。
原始restricted-growth色表の全15分割とtarget全二分割を尽くす。結果は予想を入力せず、実部分辺像・period・全関係包含から生成した。

個別Lean証拠による結果は全30候補、全Safe24、全Max7、FixMax1。
指定四Riは全AでJ零・安全だが極大ではない。
全Maxはtargettopの全二block分割、全Aut固定元は交互分割 `{0,2}|{1,3}` のみ。
最大元とjoin閉性は不成立。二安全元 `{0,1,2}|{3}` / `{0,1,3}|{2}` の全共通上界はtopだけであり、
同じ実full比較の指定spike/periodが余核1を証明する。全固定極大の正出力と全同型類自然選択は成立する。
これらをDの一様主張へ読み替えず、受理済みDの原始三角形反証と区別する。

```yaml
ledger_type: target_cycle_result
goal: G-137-aat-safe-coarsening-order
cycle: 7
goal_blob_sha: 00278db46e595fbe30762a1bb969230f77828f4f
base_oid: e09218510ed44defbf4a22dd90c0cac294ef30b8
tracking_issue: 5358
report_path: research/reports/G-137-aat-safe-coarsening-order.md
selection:
  proof_state_ref: Issue5358/comment6176740665
  proof_dag_predecessors: [受理C1-C6, G133実Hom/同署名/全Law加法, G135同じ有理全A判定, G136周期potential]
  milestone: E W1全指定原始入力/全分割対/全A実比較/Law/period/全Max/全Aut/自然選択と有限出力の確定
  proof_obligations:
    - Bool/id/ZMod4有向四辺/全台/Empty/ℚのT0生成
    - 元既存H1のperiodと指定辺0→1spike非零
    - 元部分辺像/全pullback値/正periodから実比較全射liftとrankを構成
    - 全商d0核を定数関数へ同定し全A実核余核/J/Safeを評価
    - target二分割/chart全15表と指定Riの実比較/安全性/極大性を尽くす
    - 全Max/全共通上界/最大元とjoin判定の正負有限出力
    - 元回転とBool交換の作用/全有向原始Aut/全FixMax
    - 元二Law発生labelと各値block/同じ実Law欠損/重複度
    - 同じ全A有理判定と全Safe/Max/fixed/自然選択producer
  exit_criteria: [上記W1全指定要求の入力生成Lean証拠, 全material premise放電, 個別Lean/累積全個別公理/共通scan, 標準PR独立数学2Lean2/root受入/exact-head CI/main同期]
  selection_reason: Eの未完全分割・対称性を持つ同じ指定W1の実評価gapを閉じる
  expected_result_type: proof-obligation-discharged
  lean_targets: [CycleHomology.lean, CycleQuotientHomology.lean, CycleSubsetEvaluation.lean, CycleSubsetRank.lean, CycleLaws.lean, W1Partitions.lean, W1Evaluation.lean, W1Classification.lean, W1SpecifiedCuts.lean, W1Symmetry.lean, W1FiniteResults.lean, W1NaturalSelection.lean, W1LawEvaluation.lean, W1FiniteEvaluation.lean]
  risks: [同次元射置換, 逆向き辺併合, target分割除外, 指定Riを全Maxと仮定, 一軌道だけの固定点排除, 無向反射混入, Lawlabel重複消去, 未評価有限表の存在だけ]
  unchecked: []
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: 元periodと実pullbackから全30候補/全A診断、全Safe24/Max7/FixMax1と全上界負証拠/自然選択正証拠を生成
  exit_criteria_status:
    - 指定全W1の原始表/商mk/実比較/全A/Law/全Max全Aut/全上界/有限出力を下表へ対応
    - 対象個別Lean/累積全個別公理/共通scanを固定head PRへ公開する
    - 標準4査読/root受入/CI/main同期はPR後に確定
  split_reason: none
  completion_candidate: no
  lean_artifacts: [上記全14sourceのspine/API/有限witness]
  evidence: [元period/spike/実全射lift, 元商d0核/実J/同署名図式, 全原始分割分類と全Aut分類, 全上界排除/実余核証拠, 全label Law比較/同じ有限出力/全同型類自然選択]
  claim_mapping:
    theorem_names: [Cycle.periodH1_bijective, spike_nonzero, coarse_H1_euler, fullHom_h1_surjective, actual_full_defect, all_a_defect, actual_nonempty_rank, safe_iff_edges_eq_charts, separatingMap_defect, constantMap_defect, W1.classify_chart, candidate_defect, candidate_safe_classification, maximal_iff_binary, maximal_card_seven, specifiedCut_relation, specifiedCut_defect, specifiedCut_rank, specifiedCut_safe, specifiedCut_not_maximal, aut_classification, rotation_candidate, boolSwap_candidate, fixed_maximal_iff, fixedMaximalDecision_true, common_upper_bounds_top, no_greatest, specified_join_defect, topCokerFailure, top_cokernel_spike_nonzero, generatedNaturalSelection_base, candidate_decision, safeCoarsenings_eq]
    source_labels: [固定GOAL E W1, witnesses W1項目1-4, T0/A-Cの同じ経路]
    conjuncts: [元Bool/id有向閉路, 全独立分割対/全商mk/部分像, 全A実rank核余核J, 指定Ri正負, 全Max/全上界, 全Aut/全固定点, 全label実Law/period, 同じ有限出力/自然選択]
    undischarged_assumptions: []
    acceptance_point: 原始有限表と元period/受理先行定理からW1の全指定評価を生成
    port_status: unported
audits:
  premise_delta:
    discharged: [元T0条件, period商同型/指定非零, 元商d0核/実pullback全射rank, 全A同署名比較, 全分割完全性/全Max, 全Aut完全性/全固定元, 全共通上界排除/同じ非零余核, Lawadequacy/全発生label/値block/実比較, 全有限正負と全同型類自然選択]
    remaining: [E W2全指定評価, 別全GOAL最終独立4査読/完了同期]
  certificate_provenance:
    discharged: [元色表/商mk可換全単射, 元閉路spike/period/積分, 全有限関係包含/作用, literal余核と同じcochain分離汎関数, 全Aut固定元から自然選択, 実比較から同じ判定true/false]
    unresolved: []
  proof_use:
    used: [原始辺値→period/積分→元H1, 商元辺部分像→正period→実全射lift, 全台→同署名全cochain図式→全A, 全関係表→全Safe/Max/上界, 全有向辺保存→Auttranslation→全固定点, 原始Law値→adequacy/label→実Law直和欠損, 同じfinite結果→B/Cproducer]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [PRに固定する14source個別Lean/公式単一focused/累積全個別公理/共通scan]
  blocking_findings: []
  next_obligation: E W2同じ六角形の全候補/全上界/全A実rank核余核J/全Law/periodと別全GOAL最終監査
```

### 全条項と受理spine候補

namespace `AAT.AG.SafeCoarseningOrder.Cycle` / `.W1`。下表の全定義/API/instanceと公開generated宣言は同じ個別公理監査へ含める。cycle scaffoldはない。

| 固定要求 | module/実spine宣言 | 元構成と使用先 |
| --- | --- | --- |
| 指定T0閉路・元period/spike | `CycleHomology`: input/edge/support/read API, fullChart/fullEdge, period/period_apply/period_boundary, extended/extended_apply/potential/potential_apply/differential_potential, classOf/periodH1/periodH1_bijective/fullH1Equiv, spike/period_spike/spike_nonzero | 元有向辺からperiodを生成。G136累積積分へa辺値/b辺零で接続し、同じ実d0の原始関数を生成。元H1商への全射/単射と指定spikeを証明してから次元1を導く。 |
| 全原始商の元cell/rank/実核余核 | `CycleQuotientHomology`: quotient_support_all, coarseChart/Edge/Equiv, coarseKernelEquiv/coarse_H1_euler, fullHom/fullHom_eq_old/fullHom_edge_none/some, coarseSpike/coarse_edge_has_original/period_coarseSpike_pos/fullHom_h1_surjective/fullHom_h1_rank/fullHom_defect/actual_full_defect | 元商全台からK1セルを生成。実d0核は巡回全点から定数。実部分像の指定商辺spikeを引き戻し、正periodにより同じ実H1の全射liftを構成する。元全射を先に証明し、セル数をrank代用の入力にしない。 |
| 空含む全A、実図式/rank/Safe | `CycleSubsetEvaluation/Rank`: support_family_all/alpha_nonempty/actual_nonempty_defect_eq_full/actual_empty_defect/all_a_defect/coarse_edges_ge_charts/safe_iff_edges_eq_charts/actual_full_rank/actual_nonempty_rank | 元全支持・商mk全射が六種類の全名付きセルを選択する。G133同署名の全cochain比較図式から同じ実核余核/rankを輸送。非空領域一致を仮定しない。 |
| 全Law/発生label/値block/実比較 | `CycleLaws`: separatingLaw/Label/LabelEquiv/labels_card/labels_ne/adequate/fiber_mk/fiber/fibers_same_signature, constantLaw/Label/LabelsUnique/adequate/fiber/labels_card, separatingMap/constantMap/各defect; `W1LawEvaluation`各全候補/指定Ri/全charttop defect/bijective | 非定数は元Bool値を返し二label、bottom値blockは元mk singleton。定数は任意商へdescend、一label/全target。元G133 Law比較直和欠損の全label和で二重度を保持し、同じH1射を評価する。 |
| chart全15分割・元mk可換全単射 | `W1Partitions`: partitionMap/partition/partition_relation_iff/four_rel_ext/classify_chart, numClasses/colorValue/surjective/chartEquiv/chartEquiv_mk/chart_card | 原始色表の核を生成し、六関係の全場合と反射対称推移から全Setoidを尽くす。元発生色への商mk可換全単射でchart数を評価する。期待安全性を関係へ入れない。 |
| 有向商辺・全30候補・全A実J | `W1Evaluation`: input/candidate/colorEdge/ColorEdge/edgeEquiv/numEdges/color_edge_card/quotient_edge_card/quotientEdge/candidate_defect/candidate_safe_classification/top_H1_subsingleton/top_full_defect/top_nonempty_defect/top_not_safe | 元色の異端点有向順序対を全四原辺から生成。逆向きは保持。元商辺全単射で辺数を数え、既証明の実rankへ戻す。top以外の非空J=(辺数-chart数,0)、top非空J=(0,1)、空J=(0,0)。 |
| 全Safe/全Maxとtarget二表 | `W1Classification`: classify_target/classify_coarsening/partition_le_iff/binary_le_iff/binary_above/binary_maximal/maximal_iff_binary/partition_injective/binaryIndices/maximalCoarsenings_eq/maximal_card_seven; `W1FiniteEvaluation`: targetChoice/targetChoice_false/targetChoice_true/parameterCandidatesEquiv/allCoarsenings_card_thirty/safeParameters/safeCoarsenings_eq/card | 全二target表を保持。全安全元の上に二block元を原始有限包含で構成し、全Maxをtargettopの七二block表に尽くす。全候補30/Safe24を元全単射・有限表完全性で評価。 |
| 指定四Ri・全A実比較/極大性 | `W1SpecifiedCuts`: cutIndex/specifiedCut/specifiedCut_chart_iff/specifiedCut_relation/cut_cell_counts/specifiedCut_defect/specifiedCut_rank/specifiedCut_safe/specifiedCut_not_maximal/specifiedSpike_period/specifiedSpike_nonzero | 元隣接二元だけの併合を関係式で証明。全A J零、非空実rank1、Safeは成立。全Max分類がtargettopを要求するためtargetbottomの指定Riは非極大。 |
| 全Aut・回転/Bool交換と全FixMax | `W1Symmetry`: automorphism/aut_source_eq_target/aut_chart_step/aut_chart_apply/aut_classification/bool_equiv_cases, rotation/rotationIndex/rotation_candidate/boolSwap/boolSwap_candidate, alternating_fixed/rotation_fixed_binary_iff/fixed_maximal_iff/fixedMaximalCoarsenings_eq/decision_true/specifiedFixedOutput/generatedFixedOutput | 有向辺保存→chart一段差1→全translation、q=id→source=target、Bool全単射二表。全Autを覆い、回転は他六Maxを全て動かし交互分割を全Autが固定。FixMaxは元交互Rのsingletonで、軌道へ置換しない。 |
| 全共通上界・最大元/join負出力 | `W1FiniteResults`: partition_zero_top/candidate_zero_top/common_upper_bounds_top/common_upper_bounds_unsafe/noGreatestOutput/no_greatest/greatestDecision_false/generatedNoGreatestOutput/specified_join_top/defect/topCokerFailure/top_cokernel_spike_nonzero/joinDecision_false/generatedJoinFailure | 指定二安全元1/2の全上界の元関係をtopへ強制。実full J=(0,1)、同じspike/periodで明示cochain証拠とliteral余核非零。全上界排除と同じfalseから一般Bproducerを発火。 |
| 自然選択・有限判定同じ出力 | `W1NaturalSelection`: model/model_input/specifiedNaturalSelection/generatedNaturalSelection/各base/natural_selection_exists/transport_choice_independent; `W1FiniteEvaluation`: candidate_decision/specifiedCut_decision_true/mem_safeCoarsenings_candidate/mem_maximalCoarsenings_iff/mem_fixedMaximalCoarsenings_iff | 元全固定極大と同じtrueから全同型類全原始同型の自然R選択を生成し、元入力で同じ交互Rを返す。同型選択独立を再適用。元全A有理判定が全分割の実評価と一致。 |

### Material premise・provenance・proof-use

T0有限非空S/T/V、全射id、有向非対角辺、全支持/K1、Empty面、ℚは固定入力。補助閉路familyはn≥2でこれらを原始表から放電し、W1はn=4を指定する。
任意R/P/Q/Aと原始色indexは量化入力。一般rank補題の元商辺e・非空Aは方向条件だが、W1の全top以外候補では原始色辺からeを生成し、空Aは別に零比較を証明する。
全charttopは実空辺から粗H1零を生成する。原始cell数は実d0核構成と実pullback全射liftの後でJ/rankへ使用する。
Lawadequacyは元定数値またはbottom商への明示liftから、発生labelは元source点から構成する。実Law欠損は同じ元比較の全label直和へ戻す。
全Max・全固定性・判定true/false・自然選択compatibilityを入力fieldに置かず、全原始分割/有向Aut/実比較から生成する。
全上界排除はjoin失敗だけに依存せず、二元包含が全原始関係をtopへ強制する。余核証拠は同じ指定spikeとperiodで生成する。

各前提の使用は、元辺値→積分→H1商、部分辺像→正period→実全射lift、商d0核→Euler/J、原始支持→同署名全Hom→全A、
全関係包含→全Max/全上界、全有向保存→Aut分類→全FixMax、元Law値→label/adequacy→実Law直和、有限結果→B/C出力、と追跡する。
同じ署名を持つ異なるLawlabelは二つの実直和成分として残す。
新述語colorEdgeの正/負は元恒等色表0→1の実在と全chart合併の対角除外で確認する。

### 再利用・新規部分・範囲

新規は元閉路periodを指定T0へ接続する一般補助、全商の同じ実rank/全A、原始全分割分類、W1全指定評価/全Aut/全Max/FixMax/全上界/自然選択の具体発火である。
受理C1-C6の商生成/実比較/Safe/全有限表/全作用/自然選択を再利用する。
G133同署名の全cochain比較図式と実核余核/range輸送、全Law直和欠損を再利用し、G135の同じ全A有理判定へ戻す。
G136 `Width.difference_potential` の一般nを、元a辺値/b辺零の同じcochainに適用する。既存全幅成果は新規計上しない。
固定既存版f3aeおよびG133/G135/G136受理refから現在必要な定義・statement・実引数/proof-useを追跡し、内部全履歴の再認定へ広げない。

新14sourceは上記全W1到達点の従属証拠/APIであり、途中分割はない。spineは上表、足場なし。
Research全体/aggregate/全module/全file検証、Formal移植/本体全体buildは未実施。
E W2の全指定評価と別final packet全GOAL最終4査読/完了同期は未完として保持する。


### Cycle7 初回査読の直接対応

初回固定headは `510f883a91d6b202ac559ca43a80e6bfd599fee6`。
独立数学2・Lean2の全報告をrootが全文読了し、中心finding 0、非中心3件を一括修正した。
[数学全文](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5366#issuecomment-6178340514)、
[Lean全文](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5366#issuecomment-6178343198)に元票を固定する。

数学A F1は `W1.targetChoice_false/true` を追加し、全候補全射性の利用側を値評価APIへ変更した。
LeanA F1は既存 `Width.left_apply/right_apply` と名指しされた自身の基本評価
`Cycle.extended_apply/potential_apply` を利用する証明内部修正である。
LeanA F2は定義所有 `UniformInvariance/ASubnerveReduction.lean` に
`AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.targetSubsetComparisonHom_f1_apply`
を追加し、元none/some評価を同じ次数1 projection API経由へ変更した。
この所有API追加は新たな数学claimや別比較の構成ではなく、同じ既存Homと実pullbackの等式である。

査読済みstatement、def/instance本体・値、入力・仮定、import方向、既存宣言、台帳statusを保持する。
追加5宣言は指摘が名指しした基本評価APIだけであり、個別公理監査へ全件含める。
直接対応資格と各指摘の解消は修正後の独立単一確認およびroot受入で別に確定する。
E W2、別全GOAL最終4査読、完了同期は未完のまま保持する。


## Cycle 8：指定W2の実比較と全共通上界、全GOAL完了候補

実装前selectionは[Issue5358 comment6178766622](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5358#issuecomment-6178766622)。
S=T=Bool、q=id、a=0,b=1,c=2,d=3,e=4,f=5をZMod6へ符号化し、元六有向辺・全支持・Empty面・ℚを保持する。
Racはa/cだけ、Rdfはd/fだけのchart合併でtarget等号関係。真のT0 joinは両二対合併である。
元商mkを保つchart/有向辺全単射を作り、受理C7の同じ実pullbackの正period・全射lift/全A比較図式へ接続する。

非空Aの同じ実rankは各指定合併/joinで1。指定二併合はそれぞれ核1・余核0、joinは核2・余核0であり、全て不安全。
空Aではrank/J零。指定二元は安全対join反例の前件を満たさない。
全共通上界はtarget二表×join四chartの全十五分割の引き戻し、合計30個である。
同じ実比較について安全なものは全七二block表×target二表、合計14個。
具体的上界はchart `{a,b,c}|{d,e,f}`、target等号関係であり安全。全共通上界の不存在候補は成立しない。
これを全W2粗化が30個であるという主張へ読み替えない。全W2粗化はBの全同値関係対一覧が保持する。

元非定数Lawの二発生labelを保持した実比較のJは指定二合併(2,0)、join(4,0)。
全target分割で元定数Law一labelの同じchart比較はそれぞれ(1,0)、(2,0)。
同じ署名のlabelを消去せず、元値blockとgeneratedComparisonH1Mapの全label直和欠損へ戻す。
元a→bだけ1の指定cochainは同じ六辺period=1、同じ既存H1商で非零。
指定合併/joinの実核は生成した粗cochain・細potential・正規化分離汎関数と同じH1商の非零類へ戻す。
Dの三一様主張の反証は受理三角形のままであり、不成立のW2候補へ差し替えない。

```yaml
ledger_type: target_cycle_result
goal: G-137-aat-safe-coarsening-order
cycle: 8
goal_blob_sha: 00278db46e595fbe30762a1bb969230f77828f4f
base_oid: 7cc9e6509e40867309a864c61c5c2bf81779fce0
tracking_issue: 5358
report_path: research/reports/G-137-aat-safe-coarsening-order.md
selection:
  proof_state_ref: Issue5358/comment6178766622
  proof_dag_predecessors: [受理C1-C7, G133同署名実比較/全Law直和, G135同じ有限全A有理判定, G136period積分]
  milestone: E W2の指定六角形・二併合・join・全共通上界の同じ実評価を確定し、全GOAL完了候補を監査する
  proof_obligations:
    - Bool/idとa..fの同じ六有向辺/全支持/Empty/ℚからT0入力を生成
    - Rac/Rdfの指定二点だけ合併と元商mk可換chart/有向辺全単射
    - 同じ元period/spike非零、実部分辺像と既証明実全射liftから全A rank/核余核/J/Safeを評価
    - T0 joinを原始関係包含/生成で確定し同じjoin実比較を全A評価
    - 任意共通上界のtarget分割二表とchart合併表を完全分類し、安全上界があれば元Rそのものを明示
    - 指定Law二発生label/singleton値blockと定数Law一label/全block、同じ実Law比較/重複度/指定periodを接続
    - 同じ一般Bの全候補/全Safe有限表・全A有理判定へ具体評価を戻し、候補が成立しない場合も固定データの結果として記録
    - 累積T0/A-D/E W0-W3と全premiseを最終mappingへ照合し、別finalpacket全GOALfresh数学2Lean2/root最終受入を実施
  exit_criteria: [W2全固定要求の入力生成Lean証拠, 全material premise放電, 個別Lean/累積全個別公理/共通scan, 標準PR独立数学2Lean2/root受入/exact-head CI, 別全GOAL最終4査読/root照合, merge/main/完了同期]
  selection_reason: Eの最後の指定六角形の全A実比較と全共通上界gapを閉じ、累積全GOAL判定へ進む
  expected_result_type: proof-obligation-discharged
  lean_targets: [W2Input.lean, W2SpecifiedEvaluation.lean, W2UpperBounds.lean, W2LawEvaluation.lean, W2FiniteEvaluation.lean]
  risks: [候補予想を入力する, 逆向き商辺併合, 実rankを次元だけで置換, 全共通上界のtarget分割除外, join不安全だけから最大元不存在, 同署名label重複消去, 既受理C1-C7票を別全GOAL最終票へ代用]
  unchecked: []
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: 指定二合併/joinの全A実rankと核余核を確定し、全三十共通上界/十四安全上界を完全分類、同じLaw/period/有限判定へ接続
  exit_criteria_status:
    - W2の全指定数学構成・実比較・全上界・Lawを下表へ対応
    - 個別Lean/全個別公理/共通scanを固定headのPRへ公開
    - 標準独立4査読/root受入/CIの後に同head別finalpacketを生成し、全GOAL最終fresh4査読を実施
    - merge/main/完了同期は全gate通過後に確定
  split_reason: none
  completion_candidate: yes
  lean_artifacts: [新5sourceの全spine/API/原始有限witness, 受理C1-C7累積spine]
  evidence: [元六有向辺/二点合併関係, 元商mk可換chart/edge全単射, 同じ実全射rank/全A核余核, 全上界関係復元/全分割完全性, 元cochain/potential/汎関数, 同じLaw実直和欠損/元period, 同じB有限一覧/全A有理判定]
  claim_mapping:
    theorem_names: [W2.ac_specified_relation, df_specified_relation, specified_join, specifiedSpike_nonzero, fold_defect, fold_rank, fold_empty_rank, fold_not_safe, fold_not_maximal, foldKernelFailure, fold_kernel_class_nonzero, compressed_reconstruct, classify_upper, upperCandidate_defect, upperCandidate_safe_classification, joined_defect, joined_rank, joinedKernelFailure, joined_kernel_class_nonzero, safe_common_upper_classification, safe_common_upper_exists, separating_fold_defect, constant_fold_defect, separating_joined_defect, constant_joined_defect, commonUpperBounds_eq, commonUpperBounds_card, safeCommonUpperBounds_eq, safeCommonUpperBounds_card, upperCandidate_decision]
    source_labels: [固定GOAL E W2, witnesses W2全評価表, 同じT0/A-C経路, 全GOAL completion criteria1-3]
    conjuncts: [元六角形と指定合併, 真のjoin/全A実rank核余核J, 全共通上界/具体安全上界, 元Lawと全label重複度/値block, 元period非零, 同じ有限出力, 累積全GOAL最終監査]
    undischarged_assumptions: []
    acceptance_point: 元原始表と受理C1-C7の同じ実比較から全指定W2評価を生成
    port_status: unported
audits:
  premise_delta:
    discharged: [指定T0原始条件, 元二点合併/真のjoin, 商mk可換chart/有向辺同定, 実pullback全射rankと全A核余核, 任意上界の全十五分割復元/全target保持, 元Lawadequacy/label/値block/実直和比較, 元period非零, 同じ全A有理判定/全候補・全安全一覧]
    remaining: [標準PR4査読/root受入/CI, 別全GOAL最終4査読/root最終照合, merge/main/完了同期]
  certificate_provenance:
    discharged: [元有限色表/商mk両逆, 同じ実pullback正period/全射lift, 同じ実H1核から元cochain/potential/分離dual, 元sectionとjoin関係から任意上界復元, 元Law発生値から全label直和, 元実Safe分類から有限true-false]
    unresolved: []
  proof_use:
    used: [元六辺/二点合併→商mk可換セル全単射→実rank核余核, 元全台→同署名全Hom→全A, 原始包含/section→全上界完全性→安全十四, 同じ実非単射→元核cochain証拠, 原始Law値→adequacy/label/値block→全実直和欠損, 元実分類→同じB一覧/有限判定]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [固定head PRに公開する新5source個別Lean/公式単一focused/累積全個別公理/共通scan]
  blocking_findings: []
  next_obligation: 標準PR/root受入と同headCI、別finalpacket全GOAL最終4査読/root再照合、merge/main/完了同期
```

### W2 要求・実spine・生成経路

namespace `AAT.AG.SafeCoarseningOrder.W2`。全定義/API/instanceと公開generated宣言を公理監査へ含める。足場はない。

| 固定要求 | source / 実宣言 | 元構成・使用先 |
| --- | --- | --- |
| 同じ六角形、指定二点合併、真のjoin、period | W2Input: input/read/support/edge API, acMap/dfMap/joinMap, ac/df/joined, ac_specified_relation/df_specified_relation, specified_join, specifiedSpike_period/nonzero | 元六辺、元二点合併の核関係、原始包含と反射でjoinを証明。元a→bだけ1を同じC7 period/H1へ適用。 |
| 元指定商セルと全A実比較 | W2SpecifiedEvaluation: foldCandidate/fold_false/true/relation, foldChartEquiv/mk/card, foldEdge/FoldEdge/foldEdgeEquiv/card/実商辺, fold_defect/rank/empty_rank/not_safe/not_maximal | 元五色全射とmathlib核商全単射、元有向順序対を生成。両逆/mkを保持して商セル数を数えた後、実pullback全射liftとd0核へ戻す。各非空J=(1,0)、rank1。 |
| 同じ実核cochainと非零H1 | W2SpecifiedEvaluation: fold_not_injective/foldKernelFailure/fold_kernel_class_nonzero; W2UpperBounds: joined_not_injective/joinedKernelFailure/joined_kernel_class_nonzero | 元実Jの核1/2から同じ射の非単射を導き、受理C3 producerで実粗cochain・細potential・d0を消す正規化汎関数を生成。literal元H1類非零を保持。 |
| 全共通上界の完全性と実診断 | W2UpperBounds: compressed/reconstruct, upperCandidate/classify_upper, upperColor/ChartEquiv/edgeEquiv/cards, upperCandidate_defect/rank/safe_classification, joined_eq_upper_candidate/defect/rank, safe_common_upper_classification/exists | joinMapの全射sectionから任意上界関係を全四点へ復元。全十五分割/任意Pを引き戻し、元商mk・向き保持で実Jを評価。安全上界を七二blockに尽くし、具体{abc}|{def}を示す。 |
| 元Law・値block・重複度 | W2LawEvaluation: separating_fold_defect/constant_fold_defect/separating_joined_defect/constant_joined_defect; 受理CycleLawsのLabelEquiv/labels_card/fiber/adequacy | 非定数は元Bool値/二label/等号商mk singleton値block。定数は全target商へ降下/一label/全値block。両labelを同署名でも保持し、同じgeneratedLaw射の全label欠損和へ戻す。 |
| 同じ全候補/全安全表と有限結果 | W2FiniteEvaluation: upper_parameter_injective/complete, commonUpperBounds/eq/card, safeCommonUpperBounds/eq/card, fold_decision_false/joined_decision_false/upperCandidate_decision/specified_upper_decision_true | Bの全関係対一覧と同じ全A有理判定を再利用。元関係両包含のfilterを全30表に同定し、安全14表を全実Safeに同定。全W2候補を30に縮めない。 |

### Material premise・provenance・proof-use

指定有限非空S/T/V、id全射、非対角有向辺、全支持/K1/Empty/ℚはT0入力幾何で、n6と元原始表から放電する。
一般閉路実rankの商辺存在・非空Aは方向条件、指定合併と全非top上界では原始有向色辺から放電し、空Aは別の零比較。
全chart合併は元空辺と零粗H1から同じ実余核1を生成する。
各色表の全射/商mk両逆/辺同定、join関係包含、全上界復元は新規構成義務であり、元有限表とsection/rightInverseから証明する。
元実比較全射・rank・全A共役は受理C7の同じn6/R/A/元実商辺に適用し、期待次元を入力しない。
核失敗recordは結論を保持する出力だが、そのx/y/functional/normalized/annihilateは同じ実H1核と受理C3の元代表・dualから生成する。
粗Lawadequacyは元非定数値の等号商降下または元定数値の任意商降下で構成し、細adequacyは一般Aから導出。
原始全発生labelと同じ値blockが全実直和比較へ使われる。任意target分割を共通上界表から除外しない。

C7の数学spineが新規n6適用の材料であるため、その現在statement/必要定義/実引数と受理PR5366/comment6178686416を確認する。
既存G133/G135/G136、C1-C6の再利用は現在必要source版/ref・proof-useまで確認し、受理履歴全体の再認定へ広げない。
source5はW2到達点の従属証拠/APIであり、途中分割はない。
Researchfull/aggregate/全module/全fileloop、Formal移植/本体全体buildは未実施。Formalunported。

### 累積全GOAL完了候補の対応

| 固定条項 | 累積実証拠と受理段階 | 完了候補で照合する強さ |
| --- | --- | --- |
| T0 | C1 PrimitiveInput/QuotientNerve、C2 GeneratedComparison/UniformSafety | 全有限非空原始入力、任意独立同値関係対、元商規則、実canonical逆像の全A比較。 |
| A | C1 Factorization、C2 IteratedQuotient/UniformSafety、C3 IsomorphismCochains/IdentitySafety | 関係包含 iff 元二商因子化、二段/direct mk可換同型、全Hom/H1恒等合成、全粗adequateLaw、同じJ/G135係数fiberiff。 |
| B | C3 FiniteClassification/FiniteDecisions/FailureCertificates、C5 FixedMaximalDecision | 全候補/Safe/Max完全性、各Safeの上にMax、最大元 iff 唯一Max iff 全安全対安全上界、最大/join/固定の全正負出力と各実cochain失敗。 |
| C | C4 CoarseningTransport/IsomorphismComparison/SafeIsomorphism、C5 FiniteIsomorphisms/FinitePrimitiveModel/NaturalMaximalSelection | 全S/T/V原始Iso、順序/元mk/全cochain/H1共役、全Safe/Max/Aut/FixMax、全同型類/全Iso自然R選択 iff 固定Max、任意同型選択独立。 |
| D | C5 UniformDecisions、C3/C5元Triangle全分類/全上界/全Max作用 | PG/PJ/PNすべて不成立。元T0三角形から二Safeの全上界排除/実join失敗/全Max固定点不存在→全groupoid自然選択不存在。非空虚なPJ⇒PG⇒PNを一般構成で証明。 |
| E W0 | C6 W0Evaluation、C2 W0全安全 | 元Unit/id/一辺/全台/一定数Law、全R全A実J零、同じB最大/join/全Aut固定の正出力。 |
| E W1 | C7全Cycle/W1 source | 元四有向辺/全30分割、各Ri全A実比較、安全/非極大、全Safe24/Max7/FixMax1、全上界負証拠、全Aut作用/自然選択、同じLaw/period/有限出力。 |
| E W2 | C8新5source | 元六有向辺/指定二点合併/真のjoin、全A実rank/J/核証拠、全共通上界30/安全14/具体安全上界、同じLaw/period/有限結果。候補予想を採用しない。 |
| E W3 | C6 W3Input/Comparison/Evaluation | 元G136 false全a/b・truea0除去、元支持、R=(ker fst,top)、mk可換同定/三次数d0d1/全Hom/H1、plus全A/properminus/fullminus、同じMV hiddenとG135 fiber類。 |
| 完了条件2-3 | 全53対象sourceと所有API/manifest、本report、Issue/PR固定証跡と別finalpacket | 全spine/API/instanceと前提生成/use対応、全個別公理/placeholder/共通scan、標準PRと別最終4/root全gate、merge/main/完了同期を独立に確定。 |

この表は最終判定ではない。標準PR受入・同headCIの後に別finalpacketをPRコメントへ固定し、fresh数学2Lean2が固定GOAL/設計/累積実体の全条項を照合する。
全4票とroot最終統合が正確にNo major findings、全gate pass、unchecked中心項目なしとなるまでtarget-theorem-provedを出さない。


## 全GOALの正式完了証跡

- 証明head: `a2c4603604d8c5cc3565c89e18a7d598d1d4b959`。
- [標準PR受入・同headCI](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5367#issuecomment-6179726904)。
- [別全GOAL最終packet](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5367#issuecomment-6179792760)。
- [最終数学2全文](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5367#issuecomment-6180076376)、
  [最終Lean2全文](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5367#issuecomment-6180078784)。
- [root全gate・全material premise・正式completion ledger](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5367#issuecomment-6180099392)。
- 全1,122公開宣言の個別公理は標準3公理のみ。元宣言・query・result・compiler originの全順序と全54source/blob対応を照合済み。
- 固定数学仕様・設計・共通基準は証明loop中不変。Dの三一様主張はすべて不成立、Eの候補判定は同じ指定データの結果として確定した。
- Researchの証明義務・中心未確認・blockerは空。Formal蒸留と全Formalbuildは未実施。
  Research全体・aggregate・全module・全file loopのbuildはhard ruleに従い実施していない。
- merge後のmain検証と完了状態同期の実行記録はtracking Issue #5358へ置く。IssueはOPENを保持する。
