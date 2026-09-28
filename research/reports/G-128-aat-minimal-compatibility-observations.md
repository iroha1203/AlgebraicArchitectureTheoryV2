# G-128 — 適合性を決定する最小観測集合

- 一次仕様: [`G-128-aat-minimal-compatibility-observations.md`](../goals/G-128-aat-minimal-compatibility-observations.md)
- tracking Issue: [#5075](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5075)
- 固定 GOAL・共通基準 commit: `4cb492c98c88ec876f91ea3acc6cc9b6904a5ea1`
- 固定 GOAL blob: `e50d778b5b0592a79c1b12506a6c04fe71a6c147`

この report は固定 target と Lean 宣言、前提の出所・使用先を対応させる。
査読・CI・merge の実行記録は tracking Issue と PR に置く。

## A–E の宣言対応

| 条項 | 宣言・証拠 | 状態 |
| --- | --- | --- |
| A: 観測と点安定化群 | `PointObservation.observe`, `pointStabilizer`, `observe_eq_iff` | 証明済み |
| A1: 適合性判定 | `Sufficient`, `exists_predicate_iff_sufficient` | 証明済み |
| A2: 最小観測数 | `minObservations`, `minObservations_eq_top_iff`, `minObservations_attained`, `minObservations_eq_zero_iff`, `sufficient_bot_iff_injective` | 証明済み |
| A: G-120 の同じ観測 | `singletonTableEquiv`, `singletonPredicateEquiv`, `hom_observe_one`, `hom_tableEquiv_observe`, `hom_predicate_apply`, `hom_pointStabilizer_one`, `hom_predicate_iff_original`, `hom_predicate_iff_kernel` | 証明済み |
| B: 適応的問い合わせ | — | 未証明 |
| C: 有限構成・greedy・延長 | — | 未実装 |
| D: 独立系の合成・単調性 | — | 未証明 |
| E: 名前付き操作と固定例 | — | 未実装 |

Aの `Group G`、`MulAction G X`、`Gamma : Subgroup G` は固定targetの入力である。
`Sufficient` は結論ではなく点安定化群から定義し、`exists_predicate_iff_sufficient`
が任意の有限集合について両方向を証明する。`minObservations` は十分な有限集合の
濃度の `ℕ∞` 下限であり、集合が存在しない場合は `∞` になる。
`hom_pointStabilizer_one` は G-120 の実際の kernel と一致し、
`hom_observe_one` はその観測値を同じ `O g` として評価する。
`singletonTableEquiv` と `singletonPredicateEquiv` は表・述語を双方向へ移し、
`hom_predicate_apply` が任意の述語と変更で判定値の一致を与える。

## 指定した有限例

G-127完了条件2の一頂点・二ループ例からの群同型、二つの作用と
`∞`・`1`・`2` の最小値、B・Cの手続き出力は未構成。

## Cycle 1 selection / proposed result

```yaml
ledger_type: target_cycle_result
goal: G-128-aat-minimal-compatibility-observations
cycle: 1
goal_blob_sha: e50d778b5b0592a79c1b12506a6c04fe71a6c147
base_oid: e1fe6859b047faeb142277a19cf56eb82968d217
tracking_issue: 5075
report_path: research/reports/G-128-aat-minimal-compatibility-observations.md
selection:
  proof_state_ref: Issue #5075 initial proof state
  proof_dag_predecessors: [G-120 ObservationKernel.exists_observation_predicate_iff_ker_le]
  milestone: Aの任意群作用における観測判定・最小数・G-120特殊化
  proof_obligations: [点安定化群とfiber同値, A1両方向, A2の∞と達成値, 0と単射性, G-120の同じ観測]
  exit_criteria: [全A条項のLean宣言, focused check, 公理監査]
  selection_reason: B–Dの共通の観測と最小数を固定する
  expected_result_type: proof-obligation-discharged
  lean_targets: [ResearchLean/AG/MinimalCompatibilityObservations/PointObservation.lean]
  risks: [群の正規性や作用の忠実性の隠れた仮定, 空集合, ℕ∞の∞]
  unchecked: [B, C, D, E, 指定した有限例]
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: Aの観測fiber・判定・最小値・G-120特殊化を同じ作用から証明
  exit_criteria_status: [Aの宣言を追加, focused check成功, 標準公理のみ]
  split_reason: none
  completion_candidate: no
  lean_artifacts: [PointObservation.lean]
  evidence: [observe_eq_iff, exists_predicate_iff_sufficient, minObservations_eq_top_iff, minObservations_attained, minObservations_eq_zero_iff, sufficient_bot_iff_injective, singletonTableEquiv, singletonPredicateEquiv, hom_predicate_apply, hom_predicate_iff_original, hom_predicate_iff_kernel]
  claim_mapping:
    theorem_names: [observe_eq_iff, exists_predicate_iff_sufficient, minObservations_eq_zero_iff, hom_predicate_iff_original]
    source_labels: [A1, A2, G-120特殊化]
    conjuncts: [観測fiber, 両方向の適合判定, 最小値と∞, 同じ観測のkernel]
    undischarged_assumptions: []
    acceptance_point: Aの任意作用とG-120特殊化を元の群と作用の入力だけから導出
    port_status: unported
audits:
  premise_delta:
    discharged: [点安定化群と判定の同値, 最小値の存在と∞の分岐]
    remaining: [B, C, D, E, 指定した有限例]
  certificate_provenance:
    discharged: [観測表と点安定化群を入力作用から定義]
    unresolved: []
  proof_use:
    used: [observe_eq_iff in exists_predicate_iff_sufficient, singletonTableEquiv in singletonPredicateEquiv, hom_tableEquiv_observe in hom_predicate_apply, hom_predicate_apply in hom_predicate_iff_original, G-120 kernel theorem in hom_predicate_iff_kernel]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [focused checkと公理監査はPRに記録]
  blocking_findings: []
  next_obligation: Bの決定的適応問い合わせと最悪時最適性
```
