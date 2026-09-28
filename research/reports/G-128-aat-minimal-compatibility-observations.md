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
| A: 観測と点安定化群 | `observe`, `pointStabilizer`, `observe_eq_iff` | 証明済み |
| A1: 適合性判定 | `Sufficient`, `exists_predicate_iff_sufficient` | 証明済み |
| A2: 最小観測数 | `minObservations`, `minObservations_eq_top_iff`, `minObservations_attained`, `minObservations_eq_zero_iff`, `sufficient_bot_iff_injective` | 証明済み |
| A: G-120 の同じ観測 | `singletonTableEquiv`, `singletonPredicateEquiv`, `hom_observe_one`, `hom_tableEquiv_observe`, `hom_predicate_apply`, `hom_pointStabilizer_one`, `hom_predicate_iff_original`, `hom_predicate_iff_kernel` | 証明済み |
| B: 履歴依存手続きと恒等元での下限 | `QueryRun`, `QueryRun.deterministic`, `QueryRun.replay_identity`, `identity_queries_sufficient`, `minObservations_le_identity_queries`, `no_correct_procedure_of_minObservations_top` | 下限の証明済み。B1の上限・等号は未証明 |
| C: 指定観測表の延長 | `FiniteExtension.findExtension`, `findExtension_some`, `findExtension_none_iff`, `findCompatibleExtension`, `findCompatibleExtension_some`, `findCompatibleExtension_none_iff`, `classify_correct` | 証明済み |
| C: 最小集合・判定不能・greedy | — | 未実装 |
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

Cの指定観測表の延長は、G-127の `ExplicitEnumeration G` と元の作用から
`scan` で実行する。`tableMatches` は有限な `B` 上の等号を決定し、
`findExtension` と `findCompatibleExtension` はそれぞれ周囲の変更と
適合する変更を返す。`some` の場合は同じ元の作用による観測表との一致を示し、
`none` の場合は全候補の不存在を示す。`classify_correct` は十分な `B` について
未知の変更の観測表だけから適合性を判定する。`B` の有限性、変更の完全列挙、
`X` の等号判定、`Gamma` の所属判定は有限表の入力条件である。

Bの `QueryRun` は履歴だけから次の点または結果を選ぶ手続きに対し、
未知の変更が入力される箇所を回答 `g • x` に限定する。再問い合わせも
`ask` の適用と質問列の一要素として数える。`QueryRun.deterministic` は
同じ手続き・変更・履歴から終了結果と質問列が一意であることを示す。
`QueryRun.replay_identity` は恒等元実行の質問をすべて固定する変更について
同じ実行を構成する。`identity_queries_sufficient` は正答性からこの質問集合が
十分であることを示し、`minObservations_le_identity_queries` が最小数の
問い合わせ回数下限を与える。`no_correct_procedure_of_minObservations_top` は
最小数が∞なら停止して正答する手続きが存在しないことを示す。
各手続きの最悪時最大値、固定観測集合からの上限手続き、B1の等号は未構成。

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

## Cycle 2 selection / proposed result

```yaml
ledger_type: target_cycle_result
goal: G-128-aat-minimal-compatibility-observations
cycle: 2
goal_blob_sha: e50d778b5b0592a79c1b12506a6c04fe71a6c147
base_oid: 713b9c23f7d101f45da140c18b4b9c2a69ebab81
tracking_issue: 5075
report_path: research/reports/G-128-aat-minimal-compatibility-observations.md
selection:
  proof_state_ref: Issue #5075 cycle 1 accepted state
  proof_dag_predecessors: [PointObservation.observe, PointObservation.exists_predicate_iff_sufficient, ProtocolHolonomy.ExplicitEnumeration]
  milestone: Cの任意指定観測表に対する実現可能性・適合延長とBで使用する正確なclassifier
  proof_obligations: [有限表走査の停止, someでの同一候補の正確性, noneでの全候補不存在, 十分集合でのclassifier正答性]
  exit_criteria: [二種の実行可能なOption探索, 双方のsome/none証明, classifierの正答定理, focused checkと公理監査]
  selection_reason: Bの固定質問列が返す表を正確に分類する依存構成を先に放電
  expected_result_type: proof-obligation-discharged
  lean_targets: [ResearchLean/AG/MinimalCompatibilityObservations/FiniteExtension.lean]
  risks: [有限表からの計算可能性, none分岐の全候補量化, supplied certificateへの逃避]
  unchecked: [B, Cの最小集合・判定不能・greedy, D, E, 指定した有限例]
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: 元の作用表から任意の観測表を探索し、実現可能性と適合延長をそれぞれ判定
  exit_criteria_status: [二種のOption探索を定義, some/noneとclassifierを証明, focused checkと公理監査成功]
  split_reason: none
  completion_candidate: no
  lean_artifacts: [FiniteExtension.lean]
  evidence: [tableMatches_iff, scan_some, scan_none_iff, findExtension_some, findExtension_none_iff, findExtension_isSome_iff, findCompatibleExtension_some, findCompatibleExtension_none_iff, findCompatibleExtension_isSome_iff, classify_correct]
  claim_mapping:
    theorem_names: [findExtension_some, findExtension_none_iff, findCompatibleExtension_some, findCompatibleExtension_none_iff, classify_correct]
    source_labels: [C 指定された観測表の延長, B 固定集合による上限]
    conjuncts: [任意の表の実現可能性, 適合する延長, someの実際の元, noneの全候補不存在, 十分集合での判定]
    undischarged_assumptions: []
    acceptance_point: 完全な変更列挙と決定可能な入力表から両方向の正確性を証明
    port_status: unported
audits:
  premise_delta:
    discharged: [観測表の二つの延長探索とその正確性]
    remaining: [B, Cの最小集合・判定不能・greedy, D, E, 指定した有限例]
  certificate_provenance:
    discharged: [Optionのsome値は入力変更列からscanが選ぶ]
    unresolved: []
  proof_use:
    used: [ExplicitEnumeration.complete in none証明, scan_some in some証明, observe_eq_iff in classify_correct]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [単一file focused checkとnamespace公理監査をPRに記録]
  blocking_findings: []
  next_obligation: Bの決定的手続きと最悪時問い合わせ数
```

## Cycle 3 selection / proposed result

```yaml
ledger_type: target_cycle_result
goal: G-128-aat-minimal-compatibility-observations
cycle: 3
goal_blob_sha: e50d778b5b0592a79c1b12506a6c04fe71a6c147
base_oid: 89018f656b4ff55a3babfd1a2ad646500f2ca23b
tracking_issue: 5075
report_path: research/reports/G-128-aat-minimal-compatibility-observations.md
selection:
  proof_state_ref: Issue #5075 cycle 2 accepted state
  proof_dag_predecessors: [PointObservation.minObservations, PointObservation.observe_eq_iff, FiniteExtension.classify_correct]
  milestone: B1の適応的問い合わせ最適性
  proof_obligations: [履歴依存手続きの定義, 実行の決定性, 恒等元実行の再現, 全正答手続きの下限, 最悪時最大値, 固定集合からの上限, B1の等号]
  exit_criteria: [全Gについて停止する手続きの最悪時回数を定義, 下限と上限の同じ最小数への接続, 固定最小集合による達成]
  selection_reason: Aの最小数とCのclassifierをB1へ接続する
  expected_result_type: proof-checkpoint
  lean_targets: [ResearchLean/AG/MinimalCompatibilityObservations/AdaptiveLowerBound.lean]
  risks: [適応性を固定質問へ弱める危険, 恒等元実行の再現, 重複質問の費用, 上限手続きの計算可能性]
  unchecked: [最悪時最大値, B1上限・等号, C最小集合・判定不能・greedy, D, E, 指定例]
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: 決定的な履歴手続きと実行の一意性を定義・証明し、恒等元実行から全適応手続きの下限と∞時の不存在を証明
  exit_criteria_status: [履歴モデルと下限は証明済み, 最悪時最大値と上限・等号は未証明]
  split_reason: 恒等元実行からの下限と∞時の不存在は独立に再利用できる定理であり、固定質問手続きの構成前に査読する
  completion_candidate: no
  lean_artifacts: [AdaptiveLowerBound.lean]
  evidence: [QueryRun.deterministic, QueryRun.replay_identity, identity_queries_sufficient, minObservations_le_identity_queries, no_correct_procedure_of_minObservations_top]
  claim_mapping:
    theorem_names: [QueryRun.replay_identity, identity_queries_sufficient, minObservations_le_identity_queries, no_correct_procedure_of_minObservations_top]
    source_labels: [B 恒等元での実行による下限]
    conjuncts: [同じ履歴と結果の再現, 質問点集合の十分性, minObservations≤質問回数, ∞なら正答手続きなし]
    undischarged_assumptions: [B1の上限・最悪時最大値]
    acceptance_point: Bの下限部分を全決定的履歴手続きについて証明したcheckpoint
    port_status: unported
audits:
  premise_delta:
    discharged: [恒等元質問の再現, 全正答手続きの下限, ∞の場合の不存在]
    remaining: [最悪時最大値, 固定集合の上限, B1の等号, Cの残り, D, E, 指定例]
  certificate_provenance:
    discharged: [質問集合は恒等元の実行から生成]
    unresolved: []
  proof_use:
    used: [正答性 in identity_queries_sufficient, 再現補題 in identity_queries_sufficient, Aの最小値 in minObservations_le_identity_queries]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [単一file focused checkとnamespace公理監査をPRに記録]
  blocking_findings: []
  next_obligation: 最悪時最大値と固定観測集合からの上限手続き
```
