# G-138 — 指定補正の持ち上げ障害と全解

## 固定入力と証拠の範囲

一次仕様はcommit `80f680adfd5c3271dff1e0ff0ddba3fb17b16558`の
[GOAL](../goals/G-138-aat-specified-repair-lifting.md)と参照設計4文書。
適用する共通基準も同commitであり、[固定記録](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/6191#issuecomment-6634148509)で解決する。
GOAL blobは`64dd19a5f4959437649748306100bd023b4f029e`。
実行・査読・mergeの記録は[tracking Issue #6191](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/6191)に置く。

## 証明対象と宣言の対応

[AdditiveCone.lean](../lean/ResearchLean/AG/SpecifiedRepairLifting/AdditiveCone.lean)の
namespaceは`AAT.AG.SpecifiedRepairLifting`。一般錐の座標APIは可換環R上で構成し、
非負複体への主定理は整数加群を用いる。任意アーベル群は標準整数作用を持つため、
自由性・有限性・無捩れ性を仮定していない。

| 固定条項 | 宣言 | 内容 |
| --- | --- | --- |
| T0・Aの全次数成分 | `coneCoordinateEquiv`、`coneCoordinateEquiv_d`、`coneCoordinateEquiv_d_apply` | 標準mappingConeのtarget/source座標と微分の符号 |
| T0の零延長 | `zeroExtension`、`zeroExtensionMap`、`zeroExtensionEquiv_d`、`zeroExtensionEquiv_map`、`zeroExtension_isZero` | 全非負次数の元の群・射・微分を保ち、負次数を零にする |
| T0のcohomology保存 | `zeroExtensionHomologyIso`、`zeroExtensionHomologyIso_class`、`zeroExtensionHomologyIso_naturality` | 標準Hⁿ・cycleの類・誘導比較との可換性 |
| Aの指定類 | `specifiedRepresentative`、`specifiedRepresentative_closed`、`specifiedCycle`、`specifiedObstruction` | 同じz,bから(b,−z)を作り標準H⁰へ送る |
| Aの零性と証人 | `specifiedObstruction_zero_iff_boundary`、`specifiedObstruction_zero_iff_lift` | 実微分の像と厳密な二等式の両方向 |
| Aの相互復元 | `coneMinusOneEquiv`、`cone_boundary_iff`、`boundaryWitnessEquiv` | 次数−1≃C⁰、微分証人と実Liftの両逆 |
| Aの元の非負入力 | `NonnegativeLift`、`zeroExtensionLiftEquiv`、`zeroExtension_closed`、`zeroExtension_compatible`、`nonnegativeObstruction`、`nonnegativeObstruction_zero_iff_lift` | 元の全適合z,bについて障害零性と補正存在の同値 |
| Cへの補助API | `coneCoordinateEquiv_map` | 標準平方からの錐写像の成分式。C全体の完了を意味しない |
| 非空虚性 | `integerZeroDifferential`、`identity_lift_nonempty`、`zero_comparison_no_lift`、`zero_comparison_compatible`、`zero_comparison_obstruction_ne_zero` | 同じ原始整数複体上の非空解と空解・非零障害。指定Wの代替ではない |

## 前提の生成と使用

| 前提 | 分類 | 出所と使用 |
| --- | --- | --- |
| 非負整数加群複体C,D、cochain写像f | ambient-boundary／本文由来 | T0。標準零延長・錐・解の二等式に使用 |
| d¹z=0、d⁰b=f¹z | ambient-boundary／本文由来 | T0。`zeroExtension_closed/compatible`から`specifiedRepresentative_closed`へ接続 |
| 一般整数次数版のD⁻¹のSubsingleton | direction-hypothesis／適用時放電済み | `zeroExtension_isZero`と`ModuleCat.subsingleton_of_isZero`で生成し、主定理の外部入力に残さない |
| 標準錐座標・homology同型 | discharge-required／構成済み | mathlibのinl/inr/fst/sndと`moduleCatHomologyIso`。追加のexactness証明書を受け取らない |
| 元の補正a₀ | Aでは入力にしない | B・Dの既存補正との比較は別の証明義務 |

`Lift`と`NonnegativeLift`は元のcochain二等式のsubtypeである。
`specifiedObstruction`は独立な標準錐のkernel/range商を標準homology同型の逆で送った元であり、
持ち上げ存在の真偽から定義していない。`boundaryWitnessEquiv`と`zeroExtensionLiftEquiv`の合成が
零性の実微分証人と元の補正を相互に復元する。

## 再利用・接続・新規証明

- 再利用: Lean v4.28.0、mathlib `8f9d9cff6bd728b17a24e163c9402775d9e6a365`の
  `HomologicalComplex.extend/extendMap/extendHomologyIso`、標準mappingCone、
  `ShortComplex.moduleCatHomologyIso`、submodule quotientとLinearEquiv。
- 接続: 標準錐の成分と微分、標準H⁰の零性と実微分の像、元の非負複体の各次数・Hⁿ・比較。
- 新規証明: 指定(b,−z)、厳密Lift、零性同値、証人の両逆、非負入力への適用。
  G-133の`ConeCoordinates`の証明方針を一般化したが、有理係数の既存定理を整数群の証拠にはしていない。

依存DAGは、零延長→標準錐座標→指定閉元→標準H⁰→微分証人→Lift→元の非負Lift。
G-125の実比較は下のD節でこのDAGへ接続する。整数消去とFormalへの移植は未実施。

## 残る固定証明義務

Dの同じ実Čech比較とreadingはcycle 5の独立査読待ち。
Eの整数全入力の停止算法・商での全解、指定W1–W6は未完了。
これらをAの一般定理や非空虚性例で完了扱いしない。

## Cycle 1 ledger

```yaml
ledger_type: target_cycle_result
goal: G-138-aat-specified-repair-lifting
cycle: 1
goal_blob_sha: 64dd19a5f4959437649748306100bd023b4f029e
base_oid: be98dfcf12f5a879e1fa4f8b094bdc2827a11510
tracking_issue: 6191
report_path: research/reports/G-138-aat-specified-repair-lifting.md
selection:
  proof_state_ref: '#6191 / issuecomment-6635062308'
  proof_dag_predecessors: [固定mathlibの零延長・標準錐・標準homology]
  milestone: T0・Aの一般非負入力から標準錐障害と厳密Liftの両方向対応
  proof_obligations: [全次数零延長, 標準錐座標, 指定閉元, 標準H⁰, 零性同値, 証人復元]
  exit_criteria: [全適合z,b, 自由性等の追加仮定なし, 標準錐への同定, 両方向と証人復元, focused検証と公理監査]
  selection_reason: B–Eへ共通に用いる指定持ち上げの判定を構成する
  expected_result_type: proof-obligation-discharged
  lean_targets: [ResearchLean/AG/SpecifiedRepairLifting/AdditiveCone.lean]
  risks: [錐の符号, 負次数切断, a₀の暗黙要求, 商の一致への弱化]
  unchecked: [独立レビュー]
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: 上記宣言対応表のT0・Aを構成
  exit_criteria_status: [上記宣言対応表およびPRのfocused検証結果へ対応]
  split_reason: none
  completion_candidate: no
  lean_artifacts: [ResearchLean/AG/SpecifiedRepairLifting/AdditiveCone.lean]
  evidence: [nonnegativeObstruction_zero_iff_lift, boundaryWitnessEquiv, zeroExtensionLiftEquiv]
  claim_mapping:
    theorem_names: [nonnegativeObstruction_zero_iff_lift, boundaryWitnessEquiv]
    source_labels: [T0, A]
    conjuncts: [上記宣言対応表]
    undischarged_assumptions: []
    acceptance_point: 選定したT0・Aの到達点。正式受理は固定headの独立レビューによる
    port_status: unported
audits:
  premise_delta:
    discharged: [D⁻¹の零性, 指定閉元, 零性証人と解の相互復元]
    remaining: [B–EとWの構成義務]
  certificate_provenance:
    discharged: [標準零延長, 標準錐, 入力z,bからの指定閉元]
    unresolved: []
  proof_use:
    used: [hzとhbは指定閉元の閉性, 負次数零性は元の補正復元]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [PR記載のfocused検証と全宣言公理監査]
  blocking_findings: [独立レビュー未実施]
  next_obligation: Bのkφと余核障害・短完全列・全解の分類
```


## Bの全解分類

[LiftTorsor.lean](../lean/ResearchLean/AG/SpecifiedRepairLifting/LiftTorsor.lean)は元の非負複体の
`NonnegativeLift`を直接用いる。cycle 1の依存宣言はcommit
`2e13b143c28a0a06db9c879ef08eb38e9943828f`、
[独立4査読と受理判定](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/6195#issuecomment-6635534502)
で解決する。CIとmergeの状態はtracking Issueに記録する。

| Bの要求 | 宣言 | 生成経路 |
| --- | --- | --- |
| kφ | `zeroCycles`、`cycleComparison`、`cycleComparison_apply` | 元のd⁰のAddMonoidHom kernelとφ⁰の制限。cochain性から閉性を生成 |
| ker kφ | `CorrectionKernel`、`correctionKernel_d/f` | 同じkの実AddSubgroup kernel |
| 実解への作用と差 | `addKernel`、`liftDifference`、`addKernel_difference`、`difference_addKernel` | 元C⁰の加法・差から二等式を再証明 |
| AddTorsor | `liftAddTorsor`、`lift_vadd_val`、`lift_vsub_val` | 非空な実Liftだけに既存mathlib構造を与え、元cochainで評価 |
| 全解・作用元の一意性 | `kernelEquivLift`、`kernelEquivLift_val`、`existsUnique_addKernel` | a*+hとa−a*の両逆 |
| 元補正から指定補正へ | `residualCycle`、`residualCycle_val`、`lift_of_cycleComparison_surjective` | b−φa₀の閉性を生成し、kの全射性から補正を構成 |
| 全射性の同値 | `cycleComparison_surjective_iff` | 全ての閉z・元補正存在・適合bを量化。逆方向はz=0と任意Z⁰D |
| 単射性の同値 | `lift_subsingleton_of_injective`、`cycleComparison_injective_iff` | 解の差が核に入る。逆方向はz=0の実fiber |
| 非空fiberの一意性 | `correctionKernel_subsingleton_iff`、`nonempty_lift_unique_iff_kernel_zero` | 実解を基点とした全解同値と実kernel=⊥ |
| 非空虚性 | `integerZeroLift`、`integer_difference_action`、`integer_two_lifts_ne`、`integer_difference_ne_zero`、`integer_identity_cycle_injective`、`integer_identity_unique` | 同じ整数複体の零比較で二つの異なる解と非零の実作用、恒等比較で一意な補正 |

前提はC,D,fがT0由来、z,bとその適合条件が本文由来。`hs`や`hi`はBの同値の
方向仮定であり、逆方向も証明する。a₀とその補正等式はBで許された方向仮定。
`liftAddTorsor`のNonemptyと`kernelEquivLift`の基点a*はBで明示された条件。
これらをAの外部入力へ追加していない。cycle・kernel・実作用・実差・両逆は構成義務として
元の射の加法性とcochain性から生成する。

全射性・単射性同値で量化したhzやhbが各方向で直接必要とは限らない。
全射性の十分方向ではa₀の存在からzの閉性が従い、単射性の十分方向はすべての実fiberに
成立する。より強い補助定理を用いながら、主定理では固定targetの全量化域を保持している。
余核の類と標準錐短完全列への接続、指定Wの評価は別の未完義務として残る。

## Cycle 2 ledger

```yaml
ledger_type: target_cycle_result
goal: G-138-aat-specified-repair-lifting
cycle: 2
goal_blob_sha: 64dd19a5f4959437649748306100bd023b4f029e
base_oid: 2e13b143c28a0a06db9c879ef08eb38e9943828f
tracking_issue: 6191
report_path: research/reports/G-138-aat-specified-repair-lifting.md
selection:
  proof_state_ref: '#6191 / issuecomment-6635545238'
  proof_dag_predecessors: [cycle1のNonnegativeLift, mathlibのAddTorsorとAddSubgroup]
  milestone: Bの実Liftへの核の作用と全解・一意性の分類
  proof_obligations: [kの制限, 実kernel, 作用と差, AddTorsor, 基点による両逆, 全射単射同値, 非空fiberの一意性]
  exit_criteria: [全適合入力の量化, 非空のときだけAddTorsor, 実作用と両逆, 全射単射の両方向, 非空虚性, focused検証と公理監査]
  selection_reason: Aの実Liftを分類し、Bの短完全列とD・Eの全解に接続する
  expected_result_type: proof-obligation-discharged
  lean_targets: [ResearchLean/AG/SpecifiedRepairLifting/LiftTorsor.lean]
  risks: [空fiberで一意性を誤判定, kの全射性を像へ限定, パラメータ表示と補正の混同]
  unchecked: [独立レビュー, 先行PRのCIとmerge]
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: Bの全解分類表の宣言を構成
  exit_criteria_status: [上記対応表とPR記載のfocused検証]
  split_reason: none
  completion_candidate: no
  lean_artifacts: [ResearchLean/AG/SpecifiedRepairLifting/LiftTorsor.lean]
  evidence: [kernelEquivLift, liftAddTorsor, cycleComparison_surjective_iff, cycleComparison_injective_iff, nonempty_lift_unique_iff_kernel_zero]
  claim_mapping:
    theorem_names: [上記Bの全解分類表]
    source_labels: [B]
    conjuncts: [kの核による実作用, 全解同値, 全射単射条件, 非空fiberの一意性]
    undischarged_assumptions: []
    acceptance_point: 選定したBの全解分類。余核・短完全列とGOAL全体は未完了
    port_status: unported
audits:
  premise_delta:
    discharged: [kの閉性, 核の作用, 解の差, AddTorsor則, 残差の閉性, 全条件の逆方向]
    remaining: [Bの余核と短完全列, C–E, W]
  certificate_provenance:
    discharged: [元d⁰のkernel, 実φ⁰の制限, 元cochainの加法と差]
    unresolved: []
  proof_use:
    used: [cochain性はkと残差の閉性, 基点は全解同値, 非空性はAddTorsor]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [PR記載のfocused検証と全宣言公理監査]
  blocking_findings: [独立レビュー未実施, 先行PRのCI未完了]
  next_obligation: Bの余核障害の選択独立性と標準錐の実短完全列
```


## Bの余核と標準短完全列

[ResidualExact.lean](../lean/ResearchLean/AG/SpecifiedRepairLifting/ResidualExact.lean)は、
cycle 2の同じ実kの余核と、cycle 1の同じ標準錐H⁰を接続する。
依存headは`34272bb80b993e6c56cbc85c078bb3595befa2bd`、
[cycle 2の独立査読と受理](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/6196#issuecomment-6635869161)
を参照する。cycle 1はPR #6195、cycle 2はPR #6196でmerge済み。実行状態はtracking Issueに残す。

| 固定Bの要求 | 宣言 | 実体 |
| --- | --- | --- |
| 実kの余核 | `CorrectionCokernel`、`residualClass` | Z⁰D / im kと実b−fa₀の類 |
| 選択独立性と零性 | `residualClass_independent`、`residualClass_zero_iff_lift` | 任意二補正の差cycleを生成。残差の前像から同じ指定bの補正を復元 |
| 標準homologyのAPI | `moduleCycleClass`、`moduleDescClass`、`moduleCycleClass_naturality` | mathlibの実ker/range商と標準homology同型、全cycleの類・降下・標準誘導射 |
| jの構成と単射性 | `zeroCycleToCone`、`cokernelPreinclusion`、`cokernelInclusion`、`cokernelInclusion_injective` | (b,0)の標準類。前写像の核が同じim kであることから降下 |
| pの構成 | `nonnegativeConeCoordinateEquiv`、`coneCycleProjection`、`coneProjection`、`coneKernelProjection` | 標準錐cycleの元C¹成分を元の標準H¹Cへ送り、実H¹fのkernelへ制限 |
| pの全射性 | `coneKernelProjection_surjective` | 任意のkernel類の実cycleと、像が実微分である証人から錐類を復元 |
| 中間の完全性 | `coneProjection_zero_iff`、`cokernel_kernel_exact` | pで零ならsource成分の実補正を取り、target成分を調整してjの前像を構成 |
| 同じ短完全列 | `correction_short_exact` | 同じj,pのinjective・Function.Exact・surjective |
| 二つの指定評価式 | `cokernelInclusion_residual`、`coneProjection_obstruction` | j([b−fa₀])=oφ(z,b)、p(oφ(z,b))=−[z]を元の代表元で証明 |
| 非空虚性 | `integer_oneClass_ne_zero`、`integer_projection_nonzero`、`integer_residual_inclusion_nonzero` | 同じ整数零比較でj,p双方が非零の類を保持。指定Wの代替ではない |

新しいmaterial premiseは追加しない。C,D,f,z,bと適合性はT0、a₀とその補正等式は
Bの残差表示にだけ必要な方向仮定。j,p、kernelへの所属、完全性、全射性は原始複体から
構成する。`moduleDescClass`は補助APIとして実微分を零にする証明を受け取るが、
その唯一の本体適用では`coneCycleProjectionClass_boundary`が標準錐と元のd⁰から生成する。
`moduleCycleClass_naturality`は別の比較写像を定義せず、標準`ShortComplex.homologyMap`
との可換性を証明する。pの終域は元の`HomologicalComplex.homologyMap f 1`の実kernel。
零延長のH¹同型を通じてT0のH¹と一致する。

選択・証人の存在を用いるhomology構成であり、Eの計算可能なproducerとは区別する。
cycle 3時点ではCの平方全体での自然性、Dの実比較とEの整数算法は未接続であった。

## Cycle 3 ledger

```yaml
ledger_type: target_cycle_result
goal: G-138-aat-specified-repair-lifting
cycle: 3
goal_blob_sha: 64dd19a5f4959437649748306100bd023b4f029e
base_oid: 34272bb80b993e6c56cbc85c078bb3595befa2bd
tracking_issue: 6191
report_path: research/reports/G-138-aat-specified-repair-lifting.md
selection:
  proof_state_ref: '#6191 / issuecomment-6635880829'
  proof_dag_predecessors: [cycle1の標準錐と零性, cycle2の実kと残差cycle, mathlibの標準homology]
  milestone: Bの余核障害と同じ標準錐の短完全列
  proof_obligations: [余核, 選択独立性, jとpの構成, 単射全射中間完全性, 二つの指定評価式]
  exit_criteria: [同じ標準錐と標準H¹比較, 全適合入力, 原始射からの構成, 両評価式, 非空虚性, focused検証と公理監査]
  selection_reason: Aの障害とBの残差を同じ類に接続し、CとDの自然性へ進む
  expected_result_type: proof-obligation-discharged
  lean_targets: [ResearchLean/AG/SpecifiedRepairLifting/ResidualExact.lean]
  risks: [標準H¹を別商で置換, pの符号, a₀の存在をAへ追加, exactnessを外部入力化]
  unchecked: [独立レビュー]
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: Bの余核と標準短完全列の対応表を構成
  exit_criteria_status: [上記対応表とPR記載のfocused検証]
  split_reason: none
  completion_candidate: no
  lean_artifacts: [ResearchLean/AG/SpecifiedRepairLifting/ResidualExact.lean]
  evidence: [correction_short_exact, cokernelInclusion_residual, coneProjection_obstruction, residualClass_independent]
  claim_mapping:
    theorem_names: [上記Bの余核と標準短完全列の対応表]
    source_labels: [B]
    conjuncts: [余核障害, 選択独立性, 同じjとpの短完全列, 同じ指定類への評価]
    undischarged_assumptions: []
    acceptance_point: 選定したBの余核と短完全列。C–EとWは未完了
    port_status: unported
audits:
  premise_delta:
    discharged: [商への降下, 標準類の自然性, pのkernel所属, jの単射性, pの全射性, 中間完全性, 両指定評価式]
    remaining: [C–E, W]
  certificate_provenance:
    discharged: [実kの像商, 標準錐cycleの座標, 実H¹比較, 元d⁰の像からの復元]
    unresolved: []
  proof_use:
    used: [cochain性は閉性とH¹比較, a₀は残差表示のみ, 元のcycleと微分証人はexactnessの復元]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [PR記載のfocused検証と全宣言公理監査]
  blocking_findings: [独立レビュー未実施]
  next_obligation: Cの実平方に沿った障害・余核・短完全列・全解作用の自然性
```


## Cの平方自然性と同型

[SquareNaturality.lean](../lean/ResearchLean/AG/SpecifiedRepairLifting/SquareNaturality.lean)は
任意cochain平方の元の成分を使う。依存はcycle 3のhead
`d6a7111271bfab58a82e3682a90e9778c52ca25a`、
[独立査読・直接対応・受理](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/6197#issuecomment-6636378313)
を参照する。PR #6197はmerge済み。

| 固定Cの要求 | 宣言 | 実体 |
| --- | --- | --- |
| 適合入力と実Liftの輸送 | `square_component`、`square_closed`、`square_compatible`、`squareLiftMap` | 元のα⁰で補正を送り、両方の厳密等式を保持 |
| kの核・余核 | `zeroCyclesMap`、`cycleComparison_square`、`squareKernelMap`、`squareCokernelMap` | 実cycleの制限と同じ像商への降下 |
| 標準錐と障害 | `zeroExtension_square`、`squareConeMap`、`squareConeMap_coordinates`、`squareObstructionMap`、`obstruction_naturality` | mathlibのmappingCone.mapとhomologyMap。座標は同じβ⁰,α¹ |
| j,pと可換 | `cokernelInclusion_naturality`、`coneProjection_naturality`、`squareH1KernelMap`、`coneKernelProjection_naturality` | 余核・標準H⁰・元の標準H¹kernelの同じ写像 |
| 作用・差・残差 | `squareLiftMap_addKernel`、`squareLiftMap_difference`、`square_correction`、`residualClass_naturality` | 元cochainの加法・差、輸送したa₀による同じ残差 |
| 恒等・合成 | `squareLiftMap_id/comp`、`squareKernelMap_id/comp`、`squareCokernelMap_id/comp`、`squareConeMap_id/comp`、`squareObstructionMap_id/comp`、`squareH1KernelMap_id/comp` | 全ての輸送に同じcochain平方の恒等と合成を適用 |
| 同型時の両方向 | `square_inverse_comm`、`squareLiftEquiv`、`squareKernelEquiv`、`squareCokernelEquiv`、`squareConeIso`、`squareObstructionEquiv`、`squareH1KernelEquiv` | 元のcochain逆射から逆輸送を生成し両逆を証明 |
| 同型時の作用と零性 | `squareLiftEquiv_addKernel`、`obstruction_zero_iff_of_iso`、`lift_nonempty_iff_of_iso` | 同じ補正の同値と作用の対応、障害零性と持ち上げ存在の両方向 |
| 一般平方の保存のみ | `obstruction_zero_preserved`、`integer_square_nonreflection` | 非同型平方では非零障害が零に送られる実整数例を保持 |
| 非自明な同型輸送 | `integerNegationIso`、`integer_negation_lift` | 元整数複体の符号反転で補正1を−1へ送る |

平方可換性はCが許す入力であり、同型は両方向主張だけの方向仮定。
零延長の平方、実核・余核の所属と降下、標準障害の輸送、逆平方と両逆は構成する。
自然性・逆向きの証明書を外部引数として受け取らない。
`he`は元のcochain平方の可換性で、零延長、核・余核、障害、実Liftに使用する。
同型のinverseは同じcochain同型の実逆射である。
一般平方での反映やLift全射は主張しない。下のD節では既存readingからこの入力平方を生成する。
整数例はCの非空虚性であり、W1–W6の代替ではない。

## Cycle 4 ledger

```yaml
ledger_type: target_cycle_result
goal: G-138-aat-specified-repair-lifting
cycle: 4
goal_blob_sha: 64dd19a5f4959437649748306100bd023b4f029e
base_oid: d6a7111271bfab58a82e3682a90e9778c52ca25a
tracking_issue: 6191
report_path: research/reports/G-138-aat-specified-repair-lifting.md
selection:
  proof_state_ref: '#6191 / issuecomment-6636382253'
  proof_dag_predecessors: [cycle1の標準錐, cycle2の実Liftとkernel作用, cycle3の余核とj,p]
  milestone: Cの一般平方自然性・恒等合成・同型輸送
  proof_obligations: [実Lift輸送, 核余核輸送, 標準錐障害輸送, jとpの自然性, 作用差残差, 恒等合成, 同型の両逆]
  exit_criteria: [任意cochain平方, 同じ実成分と標準誘導射, 一般平方で保存のみ, 同型時の両方向, 非空虚性, focused検証と公理監査]
  selection_reason: 一般理論の表示変更を閉じ、Dの実readingとEの表示変更へ接続する
  expected_result_type: proof-obligation-discharged
  lean_targets: [ResearchLean/AG/SpecifiedRepairLifting/SquareNaturality.lean]
  risks: [一般平方へ同型条件を追加, 零性反映の過大主張, 自然性certificateの入力化, 元補正の厳密一致を喪失]
  unchecked: [独立レビュー]
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: 上記Cの平方自然性と同型の対応表を構成
  exit_criteria_status: [上記対応表とPR記載のfocused検証]
  split_reason: none
  completion_candidate: no
  lean_artifacts: [ResearchLean/AG/SpecifiedRepairLifting/SquareNaturality.lean]
  evidence: [obstruction_naturality, cokernelInclusion_naturality, coneKernelProjection_naturality, squareLiftEquiv_addKernel]
  claim_mapping:
    theorem_names: [上記Cの対応表]
    source_labels: [C]
    conjuncts: [全実対象の輸送と自然性, 恒等合成, 同型時の両逆]
    undischarged_assumptions: []
    acceptance_point: 固定Cの一般理論。D–EとWは未完了
    port_status: unported
audits:
  premise_delta:
    discharged: [零延長平方, 核余核の誘導射, 標準錐との座標一致, jとpの自然性, 逆平方と両逆]
    remaining: [D–E, W]
  certificate_provenance:
    discharged: [元cochain成分, 標準mappingCone.map, 標準homologyMap, 元の同型逆射]
    unresolved: []
  proof_use:
    used: [平方可換性は実Liftと核余核と障害, 同型逆射は両方向だけ]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [PR記載のfocused検証と全宣言公理監査]
  blocking_findings: [独立レビュー未実施]
  next_obligation: DのG-125実比較と元のH¹・readingへの接続
```


## Dの同じ実 Čech 比較と reading への接続

cycle 4 の受理は [PR #6198監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/6198#issuecomment-6636742470)、merge `d4a8d6b34ae7a1c69f395f7ddcf24dc8afb9ab5c`。
G-125 の使用版は同じ commit の `ObstructionDiagnosticBridge` の元宣言。
[PR #4825受理](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4825#issuecomment-5746968898)と
[完了査読](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4825#issuecomment-5747017083)を再利用資格の参照とする。
使用する `FaceEmptyCechNormalization`、`ActualCechH1Comparison`、`SpecifiedAffineObstruction`、
`SpecifiedClassReflection`、`ActualCechReadingComparison` はそのmerge `964c3bab958fed4ccbd2a7f977ea7f42f9b7b242` から変更なし。
今回の適用は元の型・定義・証明から照合し、既存の合否のみを適用の証拠にしない。

| 固定Dの要求 | 新規宣言と元の実体 |
| --- | --- |
| 元の全次数 Čech 群と微分 | `cechObject`、`cechDifferential`、`cechNative`、`cechNativeEquiv`、`cechNative_d`。一般 `CoverRelativeCechComplex` の全次数を保存し、切断しない。`cechNativeEquiv_apply` が評価を保持し、`actualCechHigher_zero` が元の空なsimplex添字から高次零性を証明 |
| 独立診断複体の忘却と零延長 | `diagnosticObject`、`diagnosticDifferential`、`diagnosticNative`。元の `ThreeCochainComplex ℚ` の加法群と二微分。`diagnosticNativeEquiv0/1/2` と `diagnosticNative_higher_zero` が元群同定と次数外零性を与える |
| 元の二つの H¹ 商 | `cechCycleEquiv`、`cechH1Map`、`cechH1Equiv` と `diagnosticCycleEquiv`、`diagnosticH1Map`、`diagnosticH1Equiv`。全cycle・boundaryの代表を保つ単射全射から両方向の群同型を生成 |
| 同じ実比較 | `actualComparisonDegree`、`actualComparisonDegree_comm`、`actualComparison`、`actualComparison_f`。既存 `actualCechCoefficientCochainMap` のf0/f1/f2をそのまま使用 |
| 元の H¹ 比較との図式 | `actualComparison_h1`。全ての元のAdditiveCechH1類について既存 `actualCechDiagnosticH1Map` と標準homologyMapが可換 |
| 任意の元データと指定補正 | `actualMismatch_closed`、`actualMismatch_compatible`、`ActualLift`、`actualLift_equations`、`actualLiftOfEquations`、`actualObstruction_zero_iff`。適合した任意bの元cochain二等式を保持し、反映条件を課さない |
| A/Bの同じ障害・作用 | `actualLiftKernelEquiv`、`actualLiftKernelEquiv_val`、`actualLift_unique_iff`、`actualClass_native`、`actualObstruction_projection`、`actualResidual_inclusion`、`actualResidual_zero_iff`。実核の加法作用・一意性、pの−actualClass、jの同じ残差を接続 |
| 元状態の更新 | `actualLift_update`。元の `adjustLocalState (-a)` の actualMismatch が零になる |
| 床補正の条件付き使用 | `integralCorrection_is_correction` が元G-125定理からa₀を生成。`integralCorrection_residual_value` と `integralCorrection_residual_obstruction` が同じ実φ⁰の差を余核へ送りjで指定障害に一致させる |
| reading射の同じ成分 | `actualReadingDegree`、`actualReadingMap` と `diagnosticMapDegree`、`diagnosticNativeMap`。既存actualCechPullback0/1とgeneratedComparisonHomを使用し、全次数条件を生成 |
| 元の reading H¹ 射 | `actualReadingMap_h1`、`diagnosticNativeMap_h1`。元のactualCechRefinementH1Mapと生成診断H¹射が同じ代表で標準射と可換 |
| Cの平方と元データ輸送 | `actualCoefficient0_reading`、`actualReading_square`、`actualReadingData_mismatch`、`actualReading_compatible`。平方を入力せず元の座標自然性から生成 |
| 同じ指定補正と解・障害 | `actualReadingLift`、`actualReadingLift_val`、`actualReading_obstruction`、`actualReading_residual`。元データのtransition/localStateを独立にpullbackし、指定bも元generatedPullback0で送る |

Bの実AddTorsor、差、短完全列、残差独立性は同じ `actualComparison` に対する受理済み一般定理
`liftAddTorsor`、`liftDifference`、`correction_short_exact`、`residualClass_independent` を適用する。
新しい余核や障害を定義し直さない。`actualReading_residual` は輸送した元補正と新しい側で選び直した任意補正の残差を同定するので、床補正自体の厳密自然性を仮定しない。Cのkernel/cokernel/j/p/作用自然性も生成した同じ
`actualReading_square` に適用される。一般readingで零性の反映や解の全射は追加しない。

元 Čech の整数係数を有理化せず、診断の有理群の加法構造だけを忘却する。
全次数群の直接同定と元のH¹商の同型は別々に構成している。
実comparisonの次数2も保持し、face-emptyによる高次群の一意性を次数外の射にだけ使う。
`actualObstruction` は標準錐の同じ(b,−actualMismatch)であり、元補正a₀を入力しない。

Material premise: P・cover・adequate laws・元局所データとreading morphismはDが許すambient入力。
指定bの診断補正式はT0の適合条件で、`actualMismatch_compatible` が実比較の適合性を生成する。
CommonLabelChartSupport/ReflectionConditionは床補正節だけのdirection-hypothesis。
元のa₀の補正式はこの節では入力せず `integralCorrection_is_correction` で放電する。
cochain可換性・二つのH¹比較・reading平方・輸送した適合条件は全てdischarge-requiredとして生成済み。
自然性・障害零性・指定補正一致を供給する外部certificateは追加しない。

再利用はG-125の全実群・比較・floor・reading、A/B/Cの標準錐・作用・自然性。
接続は整数加群への忘却、全次数とH¹の同定、実比較の標準射化。
新規証明はH¹図式、任意指定bへのA/B適用、−a更新、床残差、元reading平方と指定障害/解の輸送。
Eの整数producer、W1–W6の同時成立と評価は未完了であり、Dの一般適用で代替しない。
Formal未移植。Dの新規宣言は以下が全spineで、使い捨てscaffoldはない。

- `ActualCechComplex`: `cechObject`, `cechDifferential`, `cechDifferential_square`, `cechNative`, `cechNativeEquiv`, `cechNativeEquiv_apply`, `cechNative_d`, `cechCycleEquiv`, `cechCycleClass`, `cechCycleClass_boundary`, `cechH1Map`, `cechH1Map_mk`, `cechH1Map_injective`, `cechH1Map_surjective`, `cechH1Equiv`, `diagnosticObject`, `diagnosticDifferential`, `diagnosticDifferential_square`, `diagnosticNative`, `diagnosticNativeEquiv0`, `diagnosticNativeEquiv1`, `diagnosticNativeEquiv2`, `diagnosticNative_higher_zero`, `diagnosticNative_d`, `diagnosticCycleEquiv`, `diagnosticCycleClass`, `diagnosticCycleClass_boundary`, `diagnosticH1Map`, `diagnosticH1Map_mk`, `diagnosticH1Map_injective`, `diagnosticH1Map_surjective`, `diagnosticH1Equiv`, `actualCechHigher_zero`, `actualComparisonDegree`, `actualComparisonDegree_comm`, `actualComparison`, `actualComparison_f`, `actualComparison_h1`。

- `ActualCechLifting`: `actualMismatch_closed`, `actualMismatch_compatible`, `ActualLift`, `actualLift_equations`, `actualLiftOfEquations`, `actualObstruction`, `actualObstruction_eq_nonnegativeObstruction`, `actualObstruction_zero_iff`, `actualLift_update`, `actualLiftKernelEquiv`, `actualLiftKernelEquiv_val`, `actualLift_unique_iff`, `actualClass_native`, `actualObstruction_projection`, `actualResidual`, `actualResidual_eq_residualClass`, `actualResidual_inclusion`, `actualResidual_zero_iff`, `integralCorrection_is_correction`, `integralCorrection_residual_value`, `integralCorrection_residual_obstruction`。

- `ActualCechReading`: `diagnosticMapDegree`, `diagnosticMapDegree_comm`, `diagnosticNativeMap`, `diagnosticNativeMap_h1`, `actualReadingDegree`, `actualCechDifferential_succ`, `actualReadingDegree_comm`, `actualReadingMap`, `actualReadingMap_h1`, `actualCoefficient0_reading`, `actualReading_square`, `actualReadingData`, `actualReadingData_mismatch`, `actualReading_compatible`, `actualReadingLift`, `actualReadingLift_val`, `actualReading_obstruction`, `actualReading_residual`。


## Cycle 5 ledger

```yaml
ledger_type: target_cycle_result
goal: G-138-aat-specified-repair-lifting
cycle: 5
goal_blob_sha: 64dd19a5f4959437649748306100bd023b4f029e
base_oid: d4a8d6b34ae7a1c69f395f7ddcf24dc8afb9ab5c
tracking_issue: 6191
report_path: research/reports/G-138-aat-specified-repair-lifting.md
selection:
  proof_state_ref: '#6191 / issuecomment-6636773067'
  proof_dag_predecessors: [G-125の実比較と床補正とreading, cycle1-4のA/B/C]
  milestone: Dの同じ実Čech比較・指定補正・元readingへの接続
  proof_obligations: [全次数と微分の同定, 元の二つのH¹商と実比較, A/Bの任意指定補正への適用, 負の補正による更新, 床残差, 元readingからのC平方と輸送]
  exit_criteria: [同じ全入力と係数, 同じ実比較とH¹写像, 反映条件を床節だけに限定, 元cochainの厳密一致, 全次数reading平方, focused検証と公理監査]
  selection_reason: 一般A/B/Cを元G-125に接続し固定Dの構成義務を閉じる
  expected_result_type: proof-obligation-discharged
  lean_targets: [ActualCechComplex.lean, ActualCechLifting.lean, ActualCechReading.lean]
  risks: [元係数の有理化, 次数切断, H¹だけへの置換, 反映条件の漏出, 平方certificateの入力化]
  unchecked: [独立レビュー]
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: 上記Dの全対応表とspine
  exit_criteria_status: [元全次数と元商の同定, 同じ比較の可換図式, 任意指定補正の障害と解, 床残差と負の更新, 元reading平方からの輸送, PR記載のfocused検証]
  split_reason: none
  completion_candidate: no
  lean_artifacts: [ActualCechComplex.lean, ActualCechLifting.lean, ActualCechReading.lean]
  evidence: [actualComparison_h1, actualObstruction_zero_iff, actualLift_update, integralCorrection_residual_obstruction, actualReading_square, actualReading_obstruction]
  claim_mapping:
    theorem_names: [上記Dの全spine]
    source_labels: [D]
    conjuncts: [元複体とH¹の接続, 元の指定補正へのA/B, 床残差, 元readingへのC]
    undischarged_assumptions: []
    acceptance_point: 固定Dの同じ全入力への接続。EとWは未完了
    port_status: unported
audits:
  premise_delta:
    discharged: [元複体則から標準複体, 商同型, 実比較のcochain条件, mismatch閉性と適合性, 条件付き床補正, 元reading平方]
    remaining: [E, W]
  certificate_provenance:
    discharged: [元の全次数群と二微分, 元actualCechCoefficientCochainMap, 元integralCorrection, 元actualCechPullbackとgeneratedComparisonHom]
    unresolved: []
  proof_use:
    used: [adequacyは元診断構成, face-emptyは元高次群と閉性, reflectionとcommon-labelは床補正だけ, reading条件は元pullback可換性]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [PR記載の3ファイルfocused検証と77名前付き宣言と生成含む83宣言の公理監査]
  blocking_findings: [独立レビュー未実施]
  next_obligation: Eの有限表示整数producerとW1–W6
```


Dの最終focused検証は3ファイルともexit 0、警告なし。
`ActualCechComplex` と `ActualCechLifting` は同じ単一ファイルの依存oleanを出力して検証し、
`ActualCechReading` は `lake env lean ResearchLean/AG/SpecifiedRepairLifting/ActualCechReading.lean` で検証した。
77名前付き宣言の全printと生成含む83宣言の監査は標準公理のみ。
ログSHA256は順に `7f6881c10af3a1e05f4be0a0676e45cfe77ab69d64405e62051f69efbb47ca6a`、
`6adfc760a2997459255088fdd0e3f8a4df36a458c30e75946e0dedd1bcc41ef5`、
`6b4402d25127822b9da2ae24bd86024b73fe2409da84e6dba6d11698b8247aba`。
検証に必要なG-125依存2モジュールだけのtargeted buildもexit 0。
Research全体・aggregate・全ファイルelaborationは実施していない。


## Eの原始整数行列solver

Dの受理は [PR #6199監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/6199#issuecomment-6637595621)、merge `6b3dd2c583b41b50371dfa74f99e59cbf6e71fac`。

cycle 6 は実装前の [selection](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/6191#issuecomment-6637411229) の到達点を扱う。
任意の自然数m,n（零を含む）、任意の整数行列Aと右辺bから、元整数方程式Ax=bを解く。
これはEの基礎算法部分であり、有限表示群の商へのdecode、補助変数除去、同じ実CorrectionKernelとA/B/Cへの接続、W2–W5評価は後続義務として残す。

`IntegerElimination` の `produce A` は原始Aだけから整数変換表を生成する。
直接対角候補と有限燃料のEuclid型候補を検査し、不合格なら符号化された有限整数表を構成的に探索する。
全入力での停止は `exists_valid` のSmith像基底の存在と `Encodable.choose` の探索定理から得る。
Smith形・基底・変換行列は外部から渡さない。存在証明内のClassical.choiceは実行部から消去される。
Euclid型候補単体の完全性・計算量の上界・実用的効率は主張せず、有限燃料が尽きても完全な探索に進む。

| 到達点の要求 | 証拠 |
| --- | --- |
| 有限検査可能な整数変換 | `Valid` の二つの逆行列等式、UA=diag(d)V、AB=U⁻¹diag(d)、dの零行におけるVの零性。全成分の整数等式で決定 |
| 全原始入力から生成・停止 | `exists_valid` が像のSmith基底とその原像から表の存在を構成。`produce` は実行可能な候補検査と構成的探索。`produce_valid` は全入力でValidを放電 |
| 特解と完全性 | `solve_solution`、`solve_complete`。整除時の特解B((Ub)/d)は元Ax=bを厳密に満たす |
| 不能証拠 | `failureRow_spec`、`solve_failure`、`solve_no_solution`、`solve_failure_kind`。返した行の不整除または零行の非零右辺が元解不存在を証明 |
| 実整数kernelの有限表示 | K=I−BV、`kernelMatrix_killed`、`kernelMatrix_fixed`。`producedKernelEquiv` はZ^n/im(BV)と実ker(A)の同型、`producedKernelEquiv_mk` は代表をKtへ送る |
| 同じ全解と一意性 | `solve_all_solutions` は返した特解xについてAx'=b iff ∃t,x'=x+Kt。`unique_correct` は計算可能な判定と元の存在一意性の同値 |

再利用はmathlibの自由加群のSmith像基底、有限関数の符号化、構成的探索、商の第一同型定理。
接続は元の行列成分と有限表の等式。新規証明は全表条件の存在、原始入力producer、整除による元解復元、実核の商表示、全解と一意性。
`Valid` は補助定理で入力されるが、公開producer経路では `produce_valid` が必ず生成する。
原始A,bに追加の可解性、階数、対角形、非零次元、有限探索範囲の仮定はない。
計算可能性はdefのLean検査と実行でも確認し、非計算的な宣言は二つの商同型だけ。
公理依存のClassical.choiceは存在・商の証明にも現れるが、実行時のデータ選択に使われない。

実行例10件は全てtrue: 0×0、scalar 2の可解/不能、非対角rank1の変換・可解・不能、0×2、2×0、負係数の一意解、rank1の非一意解。
これらをGOAL指定W2–W5の代替と数えない。元整数解の一意性と商での補正の一意性も混同しない。
Formal未移植。以下55名前付き宣言が全spine（探索候補の内部構成を含む）、使い捨てscaffoldなし。

`Vec`, `Mat`, `matrixEncodable`, `Data`, `dataEquiv`, `dataEncodable`, `Valid`, `validDecidable`, `transformed`, `Divisible`, `divisibleDecidable`, `particular`, `solution_divisible`, `particular_correct`, `divisible_iff_solution`, `no_solution_of_not_dvd`, `kernelMatrix`, `kernelMatrix_killed`, `kernelMatrix_fixed`, `kernelMatrix_apply`, `kernelParam`, `kernelParam_val`, `kernelParam_surjective`, `kernelParam_ker`, `kernelPresentationEquiv`, `kernelPresentationEquiv_mk`, `all_solutions`, `exists_valid`, `diagonalCandidate`, `State`, `initialState`, `swapRows`, `swapCols`, `reduceRow`, `reduceCol`, `diagonalize`, `stateCandidate`, `euclideanCandidate`, `produce`, `produce_valid`, `failingRows_nonempty`, `failureRow`, `failureRow_spec`, `solve`, `solve_solution`, `solve_failure`, `solve_no_solution`, `solve_failure_kind`, `solve_complete`, `producedKernelEquiv`, `producedKernelEquiv_mk`, `solve_all_solutions`, `unique_solution_iff`, `unique`, `unique_correct`。

focused検証は `lake env lean -o .lake/build/lib/lean/ResearchLean/AG/SpecifiedRepairLifting/IntegerElimination.olean ResearchLean/AG/SpecifiedRepairLifting/IntegerElimination.lean`、exit 0、警告なし。
55名前付き宣言の全printと生成含む88宣言のnamespace監査は標準公理のみ。
ログSHA256: `2bba603c6872abc96ef9f0ef43a0211aa51ec0a28f9448c2a743918dd09d6513`。
Research全体・aggregate・全ファイルelaborationは実施していない。

## Cycle 6 ledger

```yaml
ledger_type: target_cycle_result
goal: G-138-aat-specified-repair-lifting
cycle: 6
goal_blob_sha: 64dd19a5f4959437649748306100bd023b4f029e
base_oid: 6b3dd2c583b41b50371dfa74f99e59cbf6e71fac
tracking_issue: 6191
report_path: research/reports/G-138-aat-specified-repair-lifting.md
selection:
  proof_state_ref: '#6191 / issuecomment-6637411229'
  proof_dag_predecessors: [固定Eの整数表示, mathlibのSmith像基底と構成的探索]
  milestone: Eの原始整数行列からの停止solverと実整数kernelの有限表示
  proof_obligations: [全入力からの変換生成, 停止と有限検査, 整除判定と特解, 不能証拠, 実kernelの有限表示, 全解復元]
  exit_criteria: [全m,nと全整数A,b, 外部対角形なし, producer停止正当性完全性, 整除違反と零行矛盾, 特解と全kernel復元, focused検証と公理監査]
  selection_reason: 商の持ち上げ問題へ接続する前に原始整数入力からの算法を閉じる
  expected_result_type: proof-obligation-discharged
  lean_targets: [IntegerElimination.lean]
  risks: [実行部の非計算的choice, 外部certificateだけ, 補助未知数と実補正の混同, 有限探索の過大表示]
  unchecked: [独立レビュー]
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: 原始行列だけから停止solver・不能証拠・特解・実kernel有限表示・全解を構成
  exit_criteria_status: [上記対応表とfocused検証]
  split_reason: none
  completion_candidate: no
  lean_artifacts: [IntegerElimination.lean]
  evidence: [produce_valid, solve_complete, solve_failure_kind, producedKernelEquiv, solve_all_solutions, unique_correct]
  claim_mapping:
    theorem_names: [上記55名前付き全spine]
    source_labels: [Eの原始整数算法]
    conjuncts: [全原始入力の停止と有限検査, 特解と不能証拠, 実整数kernel有限表示, 全整数解復元]
    undischarged_assumptions: []
    acceptance_point: E基礎算法の選定到達点。E全体とWは未完了
    port_status: unported
audits:
  premise_delta:
    discharged: [Validは全Aからproduce_valid, 探索停止は全Aのexists_valid, 整除は実行判定, kernel関係はkernelParam_ker]
    remaining: [Eの商decodeと補助変数除去と実CorrectionKernel接続, 表示不変性, W]
  certificate_provenance:
    discharged: [原始Aからproduce, 原始bから特解またはfailureRow, 原始Aからkernel行列と関係行列]
    unresolved: []
  proof_use:
    used: [逆行列は元解復元, UAとABは整除とkernel, 零対角行はkernel固定, Smith像基底は全域探索停止だけ]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [上記focused検証と全宣言公理監査]
  blocking_findings: [独立レビュー未実施]
  next_obligation: 有限表示群の元関係からのdecodeと実補正kernelおよびA/B/C接続とW
```
