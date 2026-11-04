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

Bの短完全列・余核類・選択独立性・AddTorsor・全射単射の全量化、Cの全自然性・同型、
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
