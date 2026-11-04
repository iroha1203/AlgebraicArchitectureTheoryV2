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
`zero_data_not_valid` は一次元全零変換表の不成立例を提供する。これらをGOAL指定W2–W5の代替と数えない。元整数解の一意性と商での補正の一意性も混同しない。
Formal未移植。以下56名前付き宣言が全spine（探索候補の内部構成を含む）、使い捨てscaffoldなし。

`Vec`, `Mat`, `matrixEncodable`, `Data`, `dataEquiv`, `dataEncodable`, `Valid`, `validDecidable`, `transformed`, `Divisible`, `divisibleDecidable`, `particular`, `solution_divisible`, `particular_correct`, `divisible_iff_solution`, `no_solution_of_not_dvd`, `kernelMatrix`, `kernelMatrix_killed`, `kernelMatrix_fixed`, `kernelMatrix_apply`, `kernelParam`, `kernelParam_val`, `kernelParam_surjective`, `kernelParam_ker`, `kernelPresentationEquiv`, `kernelPresentationEquiv_mk`, `all_solutions`, `exists_valid`, `diagonalCandidate`, `State`, `initialState`, `swapRows`, `swapCols`, `reduceRow`, `reduceCol`, `diagonalize`, `stateCandidate`, `euclideanCandidate`, `produce`, `produce_valid`, `failingRows_nonempty`, `failureRow`, `failureRow_spec`, `solve`, `solve_solution`, `solve_failure`, `solve_no_solution`, `solve_failure_kind`, `solve_complete`, `producedKernelEquiv`, `producedKernelEquiv_mk`, `solve_all_solutions`, `unique_solution_iff`, `unique`, `unique_correct`, `zero_data_not_valid`。

focused検証は `lake env lean -o .lake/build/lib/lean/ResearchLean/AG/SpecifiedRepairLifting/IntegerElimination.olean ResearchLean/AG/SpecifiedRepairLifting/IntegerElimination.lean`、exit 0、警告なし。
56名前付き宣言の全printと生成含む89宣言のnamespace監査は標準公理のみ。
ログSHA256: `10feb22f4e359f4cabb4cdfff6708a5cf7ff38d4f3da5345ded61238d46d18aa`。
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
    theorem_names: [上記56名前付き全spine]
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


## Eの有限表示群上の逆像と実kernel

cycle 6受理は [PR #6200監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/6200#issuecomment-6638150317)、merge `cef7b278f190ea485e34f782c3cb18bf098e7e30`。
`IntegerElimination` はこの受理版から変更なし。cycle 7は実装前の
[selection](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/6191#issuecomment-6637990516)の到達点を扱う。

任意の有限表示P=(n,r,R)、Q=(m,s,S)、原始整数行列Aについて、元群をP=Z^n/imR、Q=Z^m/imSとして保持する。
`MapValid` はARの全列がimSに入ることを原始solverの整除で有限検査する。
`mapValid_iff` が検査と商射条件の必要十分性、`map` と `map_class` が同じ商射の構成・代表評価を与える。
`class_zero_iff` と `class_eq_iff` は元関係を法とする商等号を元整数証人へ両方向に戻す。
有限性やtorsionの消去は追加せず、零個の生成元・関係も許す。

| 到達点の要求 | 宣言・構成 |
| --- | --- |
| 原始関係保存を有限検査 | `MapValid`、`mapValidDecidable`、`relation_preserved`、`mapValid_iff` |
| 同じ元商群と射 | `Presentation`、`relationSpace`、`Group`、`quotientClass`、`class_surjective`、`class_eq_iff`、`map_class` |
| 指定逆像と整数系の両方向 | `equationMatrix` は[A,−S]、`equationMatrix_mulVec`、`map_class_eq_iff`、`fiber_nonempty_iff` |
| 原始入力から特解・不能証拠 | `solvePresented`、`solvePresented_solution`、`solvePresented_no_solution`、`solvePresented_complete`、`solvePresented_failure_kind` |
| 実商kernelの全生成 | 拡大行列MのK=I−BVの前半行G=`generatorMatrix`。`generatorMatrix_killed`と`generatorMatrix_surjective`が元商射kernelとの一致を証明 |
| パラメータの全関係 | 二つ目の原始整数系[G,−R]の整数核を前半へ射影した `relationMatrix`。`relationMatrix_range` がその像とt↦[Gt]のkernelの両方向一致を証明 |
| 計算した有限表示と実kernel | `kernelPresentation`、`kernelParam_ker`、`kernelEquiv`、`kernelEquiv_class`。自由パラメータを計算した全関係で割り、元商射の実kernelへ同型 |
| 全商解と作用 | `all_solutions`、`Fiber`、`fiberEquiv`、`fiberEquiv_class`。指定逆像aから生成核表示の全類をa+[Gt]へ送る両方向同値 |
| 元商解の一意性 | `kernelZero_correct`、`unique_fiber_iff`、`uniquePresented_correct`。全G列の元関係membershipで実kernel零性を判定し、可解性と組み合わせる |
| 代表変更 | `solvePresented_rep_independent`、`uniquePresented_rep_independent`。同じ終域元の代表が変わっても存在判定と一意性は同じ |

補助未知数uと元代表xの変動は、自由パラメータのまま全解の異なる元と数えない。
実kernel表示の関係を二つ目の原始整数solverから生成するので、整数系の核が非零でも商解が一意になる場合を正しく扱う。
`fiberEquiv` の逆は元商解の差を実kernelへ戻してから生成表示の同型の逆を適用する。
表示の等号は字面の整数代表ではなく、入力が定める元群の等号である。

再利用は受理済み原始整数solverと実整数kernel、mathlibの商と第一同型定理。
接続は入力関係行列と商等号、整数系への関係証人の追加。
新規証明は全商逆像の双方向還元、実商kernelへの射影の全射性、二つ目の系による全関係、全解同値と正しい一意性。
Material premiseは全自然数と整数表がambient入力、MapValidが有限検査条件。
その内容を供給証明としてだけ扱わず、決定可能な全列検査と商射条件の同値を証明する。
kernel全射・関係・表示同型・不能性は入力証明fieldに置かず、全て原始solverの証明から生成する。

focused検証と実行9件は全て成功: Z/4→Z/2の関係保存、逆方向の不成立、Z/4の零性/非零性、2倍の不能/可解/非一意、恒等射の一意、零表示の一意、自由整数群から零写像の非一意。
これらを指定W全要件の証明と数えない。
このcycleは一般有限表示射の逆像までであり、Eの六群の複体・cochain・T0全検査、同じA/B/CとCorrectionKernelへの接続、表示同型によるC輸送、指定Wと最終累積査読は未完了。
Formal未移植。全spineは次の59名前付き宣言で、使い捨てscaffoldなし。

`join`, `first`, `second`, `first_join`, `second_join`, `join_parts`, `beside`, `beside_mulVec`, `firstMap`, `Presentation`, `relationSpace`, `Group`, `quotientClass`, `class_surjective`, `class_zero_iff`, `class_eq_iff`, `isZero`, `isZero_correct`, `MapValid`, `mapValidDecidable`, `relation_preserved`, `map`, `map_class`, `equationMatrix`, `equationMatrix_mulVec`, `map_class_eq_iff`, `fiber_nonempty_iff`, `solvePresented`, `solvePresented_solution`, `solvePresented_failure`, `solvePresented_no_solution`, `solvePresented_complete`, `topRows`, `topRows_mulVec`, `generatorMatrix`, `generatorMatrix_killed`, `generatorMatrix_surjective`, `kernelParam`, `kernelParam_val`, `kernelParam_surjective`, `relationMatrix`, `relationMatrix_range`, `kernelPresentation`, `kernelParam_ker`, `kernelEquiv`, `kernelEquiv_class`, `all_solutions`, `kernelZero`, `kernelZero_correct`, `Fiber`, `fiberEquiv`, `fiberEquiv_class`, `unique_fiber_iff`, `uniquePresented`, `uniquePresented_correct`, `solvePresented_failure_kind`, `mapValid_iff`, `solvePresented_rep_independent`, `uniquePresented_rep_independent`。

検証は `lake env lean -o .lake/build/lib/lean/ResearchLean/AG/SpecifiedRepairLifting/PresentedGroups.olean ResearchLean/AG/SpecifiedRepairLifting/PresentedGroups.lean`、exit0警告なし。
全59名前付きprintと生成含む74宣言のnamespace監査は標準公理のみ。
ログSHA256: `68a2eefecca04aa4279f03cfa01c3c3f437489f2483f7a6c179e12976079f77f`。Research全体・aggregate・全file elaborationは実施していない。

## Cycle 7 ledger

```yaml
ledger_type: target_cycle_result
goal: G-138-aat-specified-repair-lifting
cycle: 7
goal_blob_sha: 64dd19a5f4959437649748306100bd023b4f029e
base_oid: cef7b278f190ea485e34f782c3cb18bf098e7e30
tracking_issue: 6191
report_path: research/reports/G-138-aat-specified-repair-lifting.md
selection:
  proof_state_ref: '#6191 / issuecomment-6637990516'
  proof_dag_predecessors: [cycle6原始整数solverと実整数核]
  milestone: 有限表示群上の射・指定逆像・実商kernelの有限表示と全解
  proof_obligations: [関係保存の有限検査, 元商射decode, 商等号と整数証人, 特解と不能証拠, 実商kernelの全生成と全関係, 全商解同値, 元商解一意性]
  exit_criteria: [全原始表示とtorsion零次元, 関係検査と商射条件の両方向, 元商逆像の正当性完全性, 補助変数を除いた実kernel表示, 全解と一意性, focusedと公理検証]
  selection_reason: 整数solverを実補正の属する商群に接続し補助自由度を除く
  expected_result_type: proof-obligation-discharged
  lean_targets: [PresentedGroups.lean]
  risks: [関係保存の外部証明化, 補助自由度の偽非一意性, torsion零表示除外, 元商元と代表の混同]
  unchecked: [独立レビュー]
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: 全有限表示射から実商kernel有限表示と全逆像分類を構成
  exit_criteria_status: [上記全対応表とfocused検証]
  split_reason: none
  completion_candidate: no
  lean_artifacts: [PresentedGroups.lean]
  evidence: [mapValid_iff, solvePresented_complete, relationMatrix_range, kernelEquiv, fiberEquiv, uniquePresented_correct]
  claim_mapping:
    theorem_names: [上記59名前付き全spine]
    source_labels: [Eの有限表示群のdecodeと全商解]
    conjuncts: [商射の有限検査, 指定逆像還元, 実商kernel表示, 特解と全解と一意性]
    undischarged_assumptions: []
    acceptance_point: 一般有限表示射の選定到達点。六群とA/B/C接続とWは後続義務
    port_status: unported
audits:
  premise_delta:
    discharged: [商射条件は全列検査, 原始系の可解性はproducer, 実kernel全射と関係は二つの原始系, 元商一意性は全生成列の関係membership]
    remaining: [E六群と複体cochainT0全検査, A/B/C接続, 表示変更, W]
  certificate_provenance:
    discharged: [原始関係行列, equationMatrix, generatorMatrix, relationMatrix, kernelPresentation]
    unresolved: []
  proof_use:
    used: [MapValidは商射構成, 商等号は関係証人, 元整数核固定は全商kernel生成, 二つ目の原始系は全パラメータ関係, 実kernelは全解と一意性]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [上記focused検証と全宣言公理監査]
  blocking_findings: [独立レビュー未実施]
  next_obligation: Eの六群・複体・cochain・T0の有限検査とA/B/C接続およびW
```


## Eの六群の有限検査と同じA・B・Cへの接続

cycle7受理は [PR #6201監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/6201#issuecomment-6638430528)、merge `70fe77f9aa445cb8975bd5e2177555f2e6f1ed41`。
`PresentedGroups` と `IntegerElimination` は受理版から変更なし。
cycle8は実装前の [selection](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/6191#issuecomment-6638351351) の到達点を扱う。
A/B/Cの再利用sourceは同じbaseの `AdditiveCone`、`LiftTorsor`、`ResidualExact`、`SquareNaturality`。
各受理参照は本reportのcycle1–4に固定したPR #6195–6198の監査であり、今回それらを変更しない。

`ComplexData` は各三群の原始表示と二つの微分行列、`ComparisonData` は三つの原始比較行列だけを持つ。
`ZeroColumns` は原始整数solverで関係像membershipを全列検査する。
`ComplexValid` は両微分の関係保存とd¹d⁰、`ComparisonValid` は三成分の関係保存と両cochain則を検査する。
`InputValid` はそれらにzの閉性・bの適合性を加える。全て決定可能で、`checkInput` と `checkedSolve` が実行入口になる。
不正な入力は `none`、正しい入力は同じ `finiteSolve` の特解または矛盾行を返す。

| 固定Eと設計の要求 | 同じ対象へのLean接続 |
| --- | --- |
| 六群・微分・比較・z,bの全有限検査 | `zeroColumns_iff`、`ComplexValid`、`ComparisonValid`、`InputValid`、`checkInput_correct`、`checkedSolve_reject_iff/some_iff` |
| 元の三群と二微分、次数二の保持 | `nativeObject`、`nativeDifferential`、`differential_square`、`native`、`nativeEquiv0/1/2`、`native_d0_class/d1_class`。三次以降だけ `native_higher_zero` |
| 同じ比較とT0の生成 | `comparisonDegree_comm`、`comparison`、`comparison_apply0/1/2`、`input_closed`、`input_compatible` |
| 二式を束ねる元群の直積 | `product` は元関係のブロック対角、`productEquiv` と `productEquiv_class` は二つの元商との同型。`above_valid/map` が同じ二射を束ねる |
| 固定設計の拡大整数系 | `jointMatrix`、`jointValue`、`finiteEquation_first/second` がd_C x−R_C u、φ⁰x−R_D vを元原始成分で評価 |
| 同じ実Lift | `joint_equation` は二つの元群での厳密等号。`liftFiberEquiv` の両逆と `liftFiberEquiv_val` は元C⁰の補正を保持 |
| 空非空・特解・不能証拠 | `finiteSolve_complete`、`decodedSolution/val`、`finiteSolve_no_solution/failure_kind`。元の実Liftへ両方向、不能行は同じ原始系の整除違反または零行矛盾 |
| A/Bの同じ障害 | `finiteSolve_obstruction` は標準錐の同じoの零性と計算判定の同値。元補正a₀がある場合だけ `finiteSolve_residual` が同じBの余核残差へ同定 |
| 同じ実CorrectionKernel | `joint_zero`、`jointKernelEquiv/val`、`correctionPresentation`、`computedKernelEquiv/class`。計算した有限表示とBの実核の群同型、元C⁰の代表評価を保持 |
| 全解と同じ作用 | `computedLiftEquiv` は生成表示からBの `kernelEquivLift` へ合成。`computedLiftEquiv_class` は元C⁰のa*+[Gt]、実Lift全体への両方向同値 |
| 補正自体の一意性 | `finiteUnique_correct`、`finiteUnique_lift`、`finiteUnique_kernel`。存在一意性、非空かつSubsingleton、非空時の同じ実kernel零性が一致 |
| 表示変更の原始順逆行列 | `IsoData` は順逆の原始三行列だけ。`InverseValid`、`IsoValid` が全関係・cochain・両合成恒等を検査、`comparison_inverse` と `nativeIso` がCの実cochain同型を生成 |
| 原始平方と輸送先入力 | `SquareValid`、`native_square`、`transported_input`。全三成分の平方を検査し、輸送した原始代表のT0も生成。一般平方に同型条件を追加しない |
| Cの同じ解・作用・障害の同値 | `representationLiftEquiv/val`、`finiteSolve_representation`、`finiteUnique_representation`、`representationKernelEquiv/comm`、`representation_action`、`representation_obstruction` |

同型は有限表示群そのものの同型であり、原始生成元の個数が等しいことや自由群行列の可逆性を要求しない。
順逆の合成を元関係を法として検査するため、冗長生成元・関係を含む表示変更も対象になる。
輸送後の特解や出力基底の字面一致は主張せず、元Liftと実kernelと作用の同値をCの同じ射で得る。
一般平方の可換性と入力条件の生成は同型を仮定しない。存在・一意性の反映を使う節だけ原始両逆を検査する。

再利用はcycle6–7の原始solver・実商kernel・全商解、A/Bの標準錐・余核・実核作用、Cの同型平方輸送。
接続は六群を同じ整数加群へdecodeし、二式を元商直積へ束ね、実Lift/CorrectionKernelへ同定すること。
新規証明は全有限検査からの複体/比較/T0/両逆/平方の生成と、同じA/B/Cへの全結果の一致。
複体・cochain・閉性・適合性・両逆・平方は入力structureの証明fieldへ置かない。
各Validは有限原始検査そのもの。`checkedSolve` はこの検査を先行し、成立時にdecodeする。
a₀は余核残差の条件付き記述だけ、特解は非空全解分類だけの方向仮定である。

対象5ファイルのfocused検証は全てexit0警告なし。全115名前付き宣言（主spine108、検査用data7）をprintと機械突合し、生成含む162宣言のnamespace監査は標準公理のみ。
`FiniteValidation` の23実行は全てtrue。関係保存・複体則・二つのcochain則・閉性・適合性・逆条件・同型条件・平方条件の正負、原始solverと存在一意性、checkedSolveの受理/拒否を検査した。
非零d¹とtorsionを持つ入力、零表示を含む。これらだけで指定W1–W6を達成したとは扱わない。

主spineは最初の4moduleの次の宣言群。`FiniteValidation` の7宣言は原始検査用scaffoldで、主証明の入力には使わない。

- `PresentedComplex`: `ZeroColumns`, `zeroColumnsDecidable`, `zeroColumns_iff`, `zeroColumns_sub_iff`, `ComplexData`, `ComplexValid`, `complexValidDecidable`, `differential_square`, `nativeObject`, `nativeDifferential`, `nativeDifferential_square`, `native`, `native_d`, `nativeEquiv0`, `nativeEquiv1`, `nativeEquiv2`, `ComparisonData`, `ComparisonValid`, `comparisonValidDecidable`, `comparisonDegree`, `comparisonDegree_comm`, `comparison`, `comparison_f`, `InputValid`, `inputValidDecidable`, `checkInput`, `checkInput_correct`, `input_closed`, `input_compatible`, `native_d0_class`, `native_d1_class`, `comparison_apply0`, `comparison_apply1`, `comparison_apply2`, `native_higher_zero`。

- `PresentedProduct`: `secondMap`, `blockMatrix`, `blockMatrix_first`, `blockMatrix_second`, `product`, `pairClass`, `pairClass_apply`, `pairClass_relations`, `productMap`, `productMap_class`, `productMap_zero`, `productMap_injective`, `productMap_surjective`, `productEquiv`, `productEquiv_class`, `above`, `above_first`, `above_second`, `above_valid`, `above_map`。

- `FiniteLifting`: `jointMatrix`, `jointValue`, `joint_valid`, `joint_equation`, `liftFiberEquiv`, `liftFiberEquiv_val`, `joint_zero`, `jointKernelEquiv`, `jointKernelEquiv_val`, `correctionPresentation`, `computedKernelEquiv`, `computedKernelEquiv_class`, `finiteSolve`, `decodedSolution`, `decodedSolution_val`, `finiteSolve_complete`, `finiteSolve_obstruction`, `computedLiftEquiv`, `computedLiftEquiv_class`, `finiteUnique`, `finiteUnique_correct`, `finiteSolve_no_solution`, `finiteSolve_failure_kind`, `finiteUnique_lift`, `finiteUnique_kernel`, `finiteEquation_first`, `finiteEquation_second`, `checkedSolve`, `checkedSolve_valid`, `checkedSolve_reject_iff`, `checkedSolve_some_iff`, `finiteSolve_residual`。

- `FiniteRepresentation`: `InverseValid`, `inverseValidDecidable`, `comparison_inverse`, `IsoData`, `IsoValid`, `isoValidDecidable`, `nativeIso`, `nativeIso_hom`, `SquareValid`, `squareValidDecidable`, `native_square`, `transported_input`, `representationLiftEquiv`, `finiteSolve_representation`, `finiteUnique_representation`, `representationKernelEquiv`, `representationLiftEquiv_val`, `representationKernelEquiv_comm`, `representationLiftEquiv_eq_squareLiftEquiv`, `representation_action`, `representation_obstruction`。

- `FiniteValidation`: `free`, `cyclic`, `torsionComplex`, `identityData`, `zeroData`, `firstComplex`, `secondComplex`。

Focusedコマンドは各対象について `lake env lean ResearchLean/AG/SpecifiedRepairLifting/<module>.lean`。
依存として使う最初の4moduleは同じfocusedコマンドに対象moduleの `.olean` 出力だけを付けた。
対象は上記5fileに限定し、Research全体・aggregate・全file elaborationは実施していない。
各ログSHA256:

- `PresentedComplex`: `dbe7ab50952fa1c2a979ab13c938a36462033d82b54916e3d1e56db510f19d88`。
- `PresentedProduct`: `0faacf681c0ee5d87771a392e881302b5e5c8393b00148fa8d4a00159fc11125`。
- `FiniteLifting`: `48a7badd39cba38ca78aea38e07a5018ab2e3da42bdaa9f40053d8cbeda7ed37`。
- `FiniteRepresentation`: `b590aba5534b0bea407ababdf224d57d15179b46a115217cb4ba5caaf8852f8e`。
- `FiniteValidation`: `195ff29954b9e5bf4f411def5da63b23c70b0c0ae20700ce9a8543e7a774880b`。

Eの選定到達点は一般の全有限表示入力で閉じたが、指定Wの同時成立・W2–W5のE評価、最終累積4本査読は未完了。
Formal未移植、G-138完了候補ではない。

初回レビュー後、定理名を `jointValid → joint_valid`、`jointEquation → joint_equation`、`jointZero → joint_zero`、`nativeSquare → native_square`、`transportedInput → transported_input` と変更した。statementと証明内容は同じ。
`representationLiftEquiv_eq_squareLiftEquiv` を公開APIとして追加し、作用の証明はこのAPI経由でCの作用保存を使う。公開定義の直接展開を除去した。

## Cycle 8 ledger

```yaml
ledger_type: target_cycle_result
goal: G-138-aat-specified-repair-lifting
cycle: 8
goal_blob_sha: 64dd19a5f4959437649748306100bd023b4f029e
base_oid: 70fe77f9aa445cb8975bd5e2177555f2e6f1ed41
tracking_issue: 6191
report_path: research/reports/G-138-aat-specified-repair-lifting.md
selection:
  proof_state_ref: '#6191 / issuecomment-6638351351'
  proof_dag_predecessors: [cycle6原始整数solver, cycle7実商kernelと全解, A/B/Cの一般理論]
  milestone: 六群の全有限検査と同じA/B/CのLift障害核作用への接続
  proof_obligations: [全関係複体cochainT0検査, 同じ複体比較へのdecode, 実Liftと直積表示Fiberの同値, 実CorrectionKernelと計算表示同型, 全解と一意性, 表示同型のC輸送]
  exit_criteria: [全原始表示と非零d1とtorsion零表示, 検査から全構造則生成, 指定補正の元群一致, 特解不能証拠全解核作用の一致, 表示同型時のC対応, focused全公理監査]
  selection_reason: Eの算法をA/B/Cの同じ数学対象へ接続して一般有限表示部分を閉じる
  expected_result_type: proof-obligation-discharged
  lean_targets: [PresentedComplex.lean, PresentedProduct.lean, FiniteLifting.lean, FiniteRepresentation.lean, FiniteValidation.lean]
  risks: [検査の外部証明化, d1切捨て, cochain一方向漏れ, 補助関係と実補正の混同, 一般平方からの無条件反映]
  unchecked: [独立レビュー]
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: 全原始有限表示入力の検査と復元結果を同じA/B/Cへ接続
  exit_criteria_status: [上記全対応表と全focused検証]
  split_reason: none
  completion_candidate: no
  lean_artifacts: [上記5module]
  evidence: [checkedSolve_some_iff, liftFiberEquiv, computedKernelEquiv, finiteSolve_obstruction, finiteSolve_residual, computedLiftEquiv, finiteUnique_kernel, representation_action, representation_obstruction]
  claim_mapping:
    theorem_names: [上記主spine108宣言と検査用7宣言]
    source_labels: [E, EからA/B/Cへの接続, 設計の整数系と表示変更]
    conjuncts: [全有限検査とdecode, 同じLiftと障害, 実kernel表示と作用, 全解一意性, 表示同型輸送]
    undischarged_assumptions: []
    acceptance_point: Eの一般部分。指定Wは後続義務
    port_status: unported
audits:
  premise_delta:
    discharged: [複体比較T0は全有限検査, 直積同型は元関係, 実核同型は同じ二式, 順逆と平方は全三成分の有限検査]
    remaining: [指定W1–W6とW2–W5評価, 最終累積査読]
  certificate_provenance:
    discharged: [原始六群と二微分と三比較, 元関係のブロック対角, jointMatrix, correctionPresentation, nativeIsoとnative_square]
    unresolved: []
  proof_use:
    used: [関係保存は商射, 複体cochain検査は全次数構造則, 閉性適合性はA障害, 同時二式は実核, 実核は全解作用一意性, 両逆はCの反映, 平方は輸送]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [上記5focused検証と全宣言公理監査と23原始評価]
  blocking_findings: [独立レビュー未実施]
  next_obligation: 固定W1–W6の同時成立とW2–W5のE評価
```


## 固定W2・W5・W6の同時成立

cycle8は [PR #6202監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/6202#issuecomment-6639122077) で受理、merge `7da633678a71252824374a88bca80b721abe98d1`。
cycle9は実装前の [selection](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/6191#issuecomment-6638835889) に従う。
`FreeWitnesses.lean` は設計のW2・W5・W6を同じ原始整数表から生成し、Eの商群を `freeEquiv` で元の整数座標へ同定する。
原始表と一般A/B/Eの対象を別々に置かず、`native` と `comparison` から同じ実Liftを作る。

| 固定要求 | 同じ入力のLean証拠 |
| --- | --- |
| W2のC⁰=Z³、D⁰=Z²、差分微分、射影比較、z=1,b=(0,1) | `w2C/w2D/w2Comparison` の原始表、`w2_input_valid` の全検査、`w2Map` |
| W2全解と整数wの両逆 | `w2Lift`、`w2Lift_coordinates`、`w2_lift_coordinates`、`w2LiftEquiv`。元C⁰の全解は厳密に(0,1,w) |
| W2実核と作用、異なる解 | `w2KernelEquiv` は実CorrectionKernelとの群同型、`w2KernelEquiv_coordinates` は(0,0,w)、`w2_action` はwへの加算、`w2_distinct` |
| W2同じA/B障害 | `w2_obstruction_zero`、`w2_residual_zero` は同じ比較と入力の標準錐・余核類 |
| W2のE出力と全解作用 | `w2_decoded_coordinates`、`w2ComputedKernelEquiv`、`w2_computed_action`。計算した実核表示から同じ整数wへ同型、出力作用も同じ加算 |
| W5の非零d¹と唯一Lift | `w5C/w5Comparison/w5_input_valid`、`w5Lift`、`w5_unique`、`w5_not_closed`、`w5_d1_ne_zero`。z=(1,0),b=1で唯一の補正1、(0,1)は閉じない |
| W5のA/BおよびE評価 | `w5_obstruction_zero`、`w5_residual_zero`、`w5_correction_kernel_zero`。`w5_decoded_eq` はE特解が同じ1、`w5_checked_reject` は不適合表の実行入口拒否 |
| W6の同じ実補正の一意性 | `w6C/w6Comparison/w6_input_valid`、`w6Lift/w6_unique`。`w6_obstruction_zero/residual_zero`、`w6_correction_kernel_zero` は同じA/B |
| W6実C⁰への非単射表示 | `w6Rho` は整数座標の和、`integerClassEquiv` で元C⁰へ同定した `w6CorrectionRho` が実射。`w6_parameter_iff` が同じ補正1のfiberを同定 |
| W6全fiber・全核・異なる表示 | `w6ActualParameterEquiv/val` は全整数nと実fiberの両逆で(n,1−n)、`w6ActualKernelEquiv/val` は実kerρとZの群同型で(n,−n)、`w6_actual_parameters_distinct`。座標側の両逆・非単射性も保持 |

W6ではBの実補正作用核が零である一方、実C⁰を値域とするρの核はZと同型である。
表示射の値域を新しい代用品に変えず、同じ一意補正の逆像を分類した。
W2の全解証明は全整数を量化して両逆を証明し、有限実行だけで無限全解を主張していない。
W5では非零d¹の評価を元複体で証明し、bad zの拒否を計算とtheoremの双方で保持する。

再利用はcycle1–4の一般A/B、cycle6–8の原始有限表示検査と同じLift/kernelへの接続。
接続は関係なし商を元整数座標へ同定する `freeEquiv` と、一整数商の `integerClassEquiv`。
新規証明は固定表の全条件、全Liftと核の座標分類、非零d¹、同じ実表示射のfiberと核、計算出力の一致。
対象外の一般群を自由群へ縮小せず、自由群なのは今回指定された三つの入力だけである。

全69名前付き宣言は以下の主spine（補助API含む）。別scaffoldなし。

`freePresentation`, `free_relations`, `freeEquiv`, `freeEquiv_class`, `free_class_eq_iff`, `w2C`, `w2D`, `w2Comparison`, `w2_input_valid`, `w2Map`, `W2Lift`, `w2Lift`, `w2Lift_coordinates`, `w2_lift_coordinates`, `w2LiftEquiv`, `w2_distinct`, `w2KernelEquiv`, `w2KernelEquiv_coordinates`, `w2_action`, `w2_residual_zero`, `w2_decoded_coordinates`, `w2ComputedKernelEquiv`, `w5C`, `w5Comparison`, `w5_input_valid`, `w5Map`, `W5Lift`, `w5_map_apply`, `w5Lift`, `w5_unique`, `w5_not_closed`, `w5_d1_ne_zero`, `w5_obstruction_zero`, `w6C`, `w6Comparison`, `w6_input_valid`, `w6Map`, `W6Lift`, `w6_map_apply`, `w6Lift`, `w6_unique`, `w6Rho`, `w6Rho_apply`, `W6Parameters`, `w6Parameter`, `w6Parameter_val`, `w6ParameterEquiv`, `w6_parameters_distinct`, `w6ParameterKernelEquiv`, `w6_rho_not_injective`, `integerClassEquiv`, `integerClassEquiv_apply`, `w6CorrectionRho`, `w6CorrectionRho_apply`, `w6_parameter_iff`, `w6ActualParameterEquiv`, `w6ActualKernelEquiv`, `w2_computed_action`, `w2_obstruction_zero`, `w5_residual_zero`, `w6_obstruction_zero`, `w6_residual_zero`, `w6_correction_kernel_zero`, `w5_correction_kernel_zero`, `w6ActualParameterEquiv_val`, `w6ActualKernelEquiv_val`, `w6_actual_parameters_distinct`, `w5_decoded_eq`, `w5_checked_reject`。

`lake env lean ResearchLean/AG/SpecifiedRepairLifting/FreeWitnesses.lean` はexit0警告なし。
全69宣言のsource・printを機械突合し、namespaceの69宣言も標準公理のみ。
ログSHA256 `deb6f9c5099f0b6d68bb68e875327307a9f1a97ef27360eac5401da72f5f33aa`。
7評価は全true（W2入力受理・成功・非一意、W5入力受理・bad z拒否・成功・一意）。
Research全体buildなし。既存依存は受理baseから変更なし。
W1（実G-125実現を含む）、W3、W4と最終累積査読は未完。G-138完了候補ではない。

## Cycle 9 ledger

```yaml
ledger_type: target_cycle_result
goal: G-138-aat-specified-repair-lifting
cycle: 9
goal_blob_sha: 64dd19a5f4959437649748306100bd023b4f029e
base_oid: 7da633678a71252824374a88bca80b721abe98d1
tracking_issue: 6191
report_path: research/reports/G-138-aat-specified-repair-lifting.md
selection:
  proof_state_ref: '#6191 / issuecomment-6638835889'
  proof_dag_predecessors: [一般A/B, cycle8の同じA/B/E接続]
  milestone: 固定W2・W5・W6の自由整数入力における全解と実核作用および補正と表示の一意性の差
  proof_obligations: [W2全解と実核と作用と残差, W2のE一致, W5唯一解と非零d1と非閉性とE受理拒否, W6唯一補正と実rhoのfiber核全対応]
  exit_criteria: [固定表から全入力条件, 同じA/Bへの適用, W2全w両逆と加法作用と異なる解, W5非零d1と障害零とE評価, W6実C0のrhoと全fiber核と異なる表示, focused全公理監査]
  selection_reason: 一般理論と算法を指定された同じ非退化入力へ適用する義務を縮める
  expected_result_type: proof-obligation-discharged
  lean_targets: [FreeWitnesses.lean]
  risks: [自由代表と元群の同定漏れ, E評価だけの全解主張, 補正と表示の一意性混同, d1未発火]
  unchecked: [独立レビュー]
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: W2とW5とW6の全指定条件を同じ入力から証明
  exit_criteria_status: [上記対応表とfocused全公理監査]
  split_reason: none
  completion_candidate: no
  lean_artifacts: [FreeWitnesses.lean]
  evidence: [w2LiftEquiv, w2KernelEquiv, w2_action, w2_computed_action, w5_unique, w5_not_closed, w5_checked_reject, w6_unique, w6ActualParameterEquiv, w6ActualKernelEquiv]
  claim_mapping:
    theorem_names: [上記69宣言]
    source_labels: [W2, W5, W6]
    conjuncts: [全解実核作用と計算結果, 非零次微分と唯一解, 補正と表示の一意性の差]
    undischarged_assumptions: []
    acceptance_point: 固定三入力の全要求の同時成立
    port_status: unported
audits:
  premise_delta:
    discharged: [固定原始表の全検査, 自由商と整数座標の同定, 同じ実Liftと核の全元分類, 実rhoの全fiber核]
    remaining: [W1実G125実現含む, W3, W4, 最終累積査読]
  certificate_provenance:
    discharged: [w2入力表, w5入力表, w6入力表, 原始表からnativeとcomparison, 同じrho]
    unresolved: []
  proof_use:
    used: [原始検査は複体比較T0, 自由商同型は座標全解, 実核差は作用, 同じBは残差と一意性, Eの実核表示は計算作用同定]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [focused exit0, 全69公理監査, 7評価true]
  blocking_findings: [独立レビュー未実施]
  next_obligation: W3とW4のtorsion不能非一意性および元修復不能の標準障害とE評価
```


## 固定W3・W4のtorsionと元修復不能

cycle9は [PR #6203監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/6203#issuecomment-6639362403) で受理、merge `343ba1850e364e215ab2906987706070ff7d79b8`。
cycle10は実装前の [selection](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/6191#issuecomment-6639291374) に従う。
一般A/B/Eと固定GOALは変更せず、W3・W4の同じ原始整数表から条件と結論を生成する。

| 固定要求 | 同じ対象のLean証拠 |
| --- | --- |
| W3のC⁰=D⁰=Z/4、比較2倍、正次数零 | `cyclicPresentation 4` は一生成元・関係[4]、`w3C/w3Comparison` の原始表。`cyclic_relations` は剰余射の実核が関係像と一致、`cyclicEquiv/class` は同じ元商とZMod4を両方向に同定 |
| W3全入力のT0と厳密Lift | `w3_input_one/two`、`w3_map_coordinates`、`w3_lift_iff`。元群の二式は同じ剰余で2a=bと同値 |
| b=1の不能と非零障害 | `w3_one_no_lift`、`w3_obstruction_one_ne_zero`。同じBの余核は `w3CokernelEquiv` でZ/2、`w3_residual_one_coordinates/ne_zero` は同じ残差が非零元1 |
| b=2の全Lift={1,3} | `w3LiftOne/Three`、`w3_lifts_distinct`、`w3_all_lifts`。同じA/Bの障害は `w3_obstruction_two_zero/residual_two_zero` |
| 実核{0,2}≅Z/2と自由推移作用 | `w3KernelEquiv/coordinates`、`w3_kernel_coordinates`、`w3_action_one`、`w3AllSolutions/apply/zero/one`。Bの実kernel作用から全解との両逆を生成 |
| 同じ原始Eの両結果 | `w3_algorithm_distinguishes`、`w3_solver_failure/divisibility_certificate`、`w3_decoded_two`、`w3ComputedKernelEquiv`、`w3_computed_action`。b=1は非零対角への整除違反、b=2の出力は同じ二解で核作用も一致 |
| rankや有理化では差を再現できない | `w3_four_smul`、`w3_rank_zero`、`w3_rationalization_zero` は元群の4-torsion・整数rank零・実TensorProductの全元零。`w3_rational_map_zero` と `w3_rational_diagnostic_loses_decision` は有理値の全射影がb1,b2を同一視する一方、実Liftの有無は異なることを示す |
| W4のC⁰=0,C¹=Z,D=0,z=1,b=0 | `w4C/w4D/w4Comparison/w4_input_valid` は固定表からT0を生成。`w4_no_repair/no_lift` は元修復も実Liftも不存在 |
| W4の標準H⁰Cone≅Z | `w4CycleCoordinate` は標準錐の元座標のsource成分、`w4_class_injective` は実C⁰零から標準類写像の単射性を得る。`w4ConeEquiv/class` は標準homologyと整数群の両方向群同型 |
| W4の同じo=-1とp(o)非零 | `w4_obstruction_coordinates/ne_zero`、`w4_oneClass_ne_zero`、`w4_projection_obstruction/ne_zero`。標準障害の整数座標は-1、同じBのpは元標準H¹の-[z]へ送り非零 |
| W4のE不能証拠 | `w4_solver_failure`、`w4_zero_row_certificate`。原始算法の実出力は行0、対角零かつ変換右辺非零 |

再利用はAの標準錐、Bの標準cycle類・射影・実kernel作用、Eの入力生成・復元・核表示、cycle9の自由商同型。
接続は巡回原始商とZModの同型、およびW4の標準錐cycle座標から標準homologyを経由する整数同型。
新規証明は固定torsion入力の不能・全二解・実核/余核・作用と有理化、および元修復不能入力の標準障害とEの零行証拠。
有限ZModでの判定を元商へ戻す両方向同型を明示し、元群を自由群へ置換しない。
W4の標準錐・H¹・pは既存A/Bそのもので、独自障害群を定義して一致義務を消していない。
元修復a₀はW3の残差で0を構成し、W4のA適用では存在を要求しない。

全103名前付き宣言が主spine（補助API含む）。別scaffoldなし。

- `TorsionWitness` 71宣言: `cyclicPresentation`, `residueLinear`, `residueLinear_apply`, `cyclic_relations`, `cyclicMap`, `cyclicMap_class`, `cyclicMap_injective`, `cyclicMap_surjective`, `cyclicEquiv`, `cyclicEquiv_class`, `w3C`, `w3Comparison`, `w3_input_one`, `w3_input_two`, `w3Map`, `W3Lift`, `w3_d_apply`, `w3_map_coordinates`, `w3_lift_iff`, `w3_one_no_lift`, `w3LiftOne`, `w3LiftThree`, `w3_lifts_distinct`, `w3_all_lifts`, `w3_d_zero`, `w3CyclesEquiv`, `w3CyclesEquiv_apply`, `w3CyclesEquiv_symm_coordinates`, `w3_cycle_comparison`, `evenEmbed`, `evenEmbed_injective`, `evenEmbed_range`, `w3KernelHom`, `w3KernelHom_coordinates`, `w3KernelHom_injective`, `w3KernelHom_surjective`, `w3KernelEquiv`, `w3KernelEquiv_coordinates`, `w3_action_one`, `w3AllSolutions`, `parity4`, `parity4_zero_iff`, `parity4_surjective`, `w3Parity`, `w3Parity_apply`, `w3_comparison_range`, `w3Parity_surjective`, `w3CokernelEquiv`, `w3CokernelEquiv_class`, `w3_obstruction_one_ne_zero`, `w3_obstruction_two_zero`, `w3CokernelEquiv_residual`, `w3_residual_one_coordinates`, `w3_residual_one_ne_zero`, `w3_residual_two_zero`, `w3_four_smul`, `w3_rational_map_zero`, `w3_algorithm_distinguishes`, `w3_decoded_two`, `w3ComputedKernelEquiv`, `w3_rank_zero`, `w3_rationalization_zero`, `w3_rational_diagnostic_loses_decision`, `w3_computed_action`, `w3_kernel_coordinates`, `w3AllSolutions_apply`, `w3AllSolutions_zero`, `w3AllSolutions_one`, `w3FailureRow`, `w3_solver_failure`, `w3_divisibility_certificate`。
- `NoRepairWitness` 32宣言: `w4C`, `w4D`, `w4Comparison`, `w4_input_valid`, `w4Map`, `w4_source_zero`, `w4_target_zero`, `w4_d_zero`, `w4_z_ne_zero`, `w4_no_repair`, `w4_no_lift`, `W4Cone`, `W4Cycles`, `w4CycleCoordinate`, `w4CycleCoordinate_apply`, `w4CycleCoordinate_injective`, `w4_closed`, `w4_compatible`, `w4CycleCoordinate_surjective`, `w4_class_injective`, `w4ConeEquiv`, `w4ConeEquiv_class`, `w4Obstruction`, `w4Obstruction_class`, `w4_obstruction_coordinates`, `w4_obstruction_ne_zero`, `w4_oneClass_ne_zero`, `w4_projection_obstruction`, `w4_projection_ne_zero`, `w4FailureRow`, `w4_solver_failure`, `w4_zero_row_certificate`。

対象それぞれの `lake env lean ResearchLean/AG/SpecifiedRepairLifting/<module>.lean` はexit0警告なし。
103名前付き宣言のsource/printを突合し、namespaceの103宣言も標準公理のみ。
6評価全true（W3不能・成功・非一意、W4入力受理・不能・非一意判定）。
ログSHA256はTorsionWitness `b0b6ef0e1e6a219c15112909540dce272e260fea457edcea0ecb93f1c282d22a`、NoRepairWitness `d9c262bc17e654075669c478b1bf75a7e671242f7e4e5d8c48e2eccd1c22376f`。
必要なmathlibのDimension.Torsion.FiniteとTensorProduct.Basicだけをtargeted buildした。Research全体buildなし。
既存A/B/Eとcycle9の受理済みsourceはbaseから変更なし。
W1（実G-125実現を含む）と最終累積4本は未完。Formal未移植、G-138完了候補ではない。

## Cycle 10 ledger

```yaml
ledger_type: target_cycle_result
goal: G-138-aat-specified-repair-lifting
cycle: 10
goal_blob_sha: 64dd19a5f4959437649748306100bd023b4f029e
base_oid: 343ba1850e364e215ab2906987706070ff7d79b8
tracking_issue: 6191
report_path: research/reports/G-138-aat-specified-repair-lifting.md
selection:
  proof_state_ref: '#6191 / issuecomment-6639291374'
  proof_dag_predecessors: [A標準錐, B実核余核射影, E有限表示, cycle9自由商同型]
  milestone: 固定W3のtorsionとW4の元修復不能を同じA/B/Eで評価
  proof_obligations: [W3不能と余核Z2障害, W3全二解と実核Z2作用, W3同じEとrank有理化, W4T0と元修復不能, W4標準H0ConeZとo符号とp非零, W4E零行証拠]
  exit_criteria: [両固定表で全条件同時成立, 一般A/Bとの同定, E同じ原始表で評価, focused全公理監査]
  selection_reason: torsionを保持する算法とa0不要の一般障害を指定例で検証する
  expected_result_type: proof-obligation-discharged
  lean_targets: [TorsionWitness.lean, NoRepairWitness.lean]
  risks: [torsion自由群化, 類障害と原始失敗の分離, 全二解未証明, 標準錐H1の代用品, 隠れa0前提]
  unchecked: [独立レビュー]
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: W3とW4の全指定条件を同じ入力から証明
  exit_criteria_status: [上記対応表とfocused全公理監査]
  split_reason: none
  completion_candidate: no
  lean_artifacts: [TorsionWitness.lean, NoRepairWitness.lean]
  evidence: [w3_all_lifts, w3KernelEquiv, w3CokernelEquiv, w3_residual_one_coordinates, w3_rationalization_zero, w3_algorithm_distinguishes, w4_no_repair, w4ConeEquiv, w4_obstruction_coordinates, w4_projection_ne_zero, w4_zero_row_certificate]
  claim_mapping:
    theorem_names: [上記103宣言]
    source_labels: [W3, W4]
    conjuncts: [torsion不能非一意性と核余核, rank有理化の情報損失, 元修復不能と標準錐符号, E同じ不能証拠]
    undischarged_assumptions: []
    acceptance_point: 固定二入力の全要求の同時成立
    port_status: unported
audits:
  premise_delta:
    discharged: [原始表の全検査, 巡回商同型, 実核余核の全元分類, W4標準homology同型, 原始不能行の証拠]
    remaining: [W1実G125実現含む, 最終累積査読]
  certificate_provenance:
    discharged: [関係4と比較2の原始表, W4零次零と一次Zの表, 同じ整数solverの返す行]
    unresolved: []
  proof_use:
    used: [原始検査はnative比較T0, 巡回同型は厳密Lift分類, 実kernelは作用, parity実核は余核同型, W4C0零は標準類単射, 同じ錐座標は符号, Eの原始行は不能]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [2focused exit0, 全103公理監査, 6評価true]
  blocking_findings: [独立レビュー未実施]
  next_obligation: W1の整数有理差と実G125三点構成および最終累積査読
```
