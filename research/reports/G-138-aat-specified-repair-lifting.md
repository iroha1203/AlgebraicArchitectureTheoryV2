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
G-125の実比較・整数消去はこのDAGへ未接続。Formalへの移植も未実施。

## 残る固定証明義務

Bの短完全列・余核類・選択独立性、Cの全自然性・同型、
Dの同じ実Čech比較とreading、Eの整数全入力の停止算法・商での全解、指定W1–W6は未完了。
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
