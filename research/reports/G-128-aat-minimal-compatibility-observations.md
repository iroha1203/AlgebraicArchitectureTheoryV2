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
| B: 適応的問い合わせの最適値 | `QueryRun`, `QueryRun.deterministic`, `QueryRun.replay_identity`, `identity_queries_sufficient`, `worstQueries`, `worstQueries_attained`, `optimalQueries`, `finiteFixedProcedure`, `finiteFixedProcedure_executable_optimal`, `optimalQueries_eq_minObservations` | B1、有限群の最悪時最大値、有限表の固定集合による達成を証明済み |
| C: 指定観測表の延長 | `FiniteExtension.findExtension`, `findExtension_some`, `findExtension_none_iff`, `findCompatibleExtension`, `findCompatibleExtension_some`, `findCompatibleExtension_none_iff`, `classify_correct` | 証明済み |
| C: 最小集合と判定不能の証拠 | `candidateSets`, `minimumObservation`, `minimumObservation_card`, `findIncompatibleFixer`, `minimumOrWitness`, `minimumOrWitness_correct`, `minimumOrWitness_invisible`, `minimumOrWitness_optimalProcedure` | 入力列挙からの全探索、実際の最小集合または不適合な全点固定元、A・Bとの対応を証明済み |
| C: 集合被覆 | `incompatibleSet`, `detectedSet`, `sufficient_iff_cover` | 入力有限表の不適合元と点ごとの検出集合から、十分性と被覆の同値を証明済み |
| C: greedyの選択・停止・正確性 | `newCoverage`, `greedyPick`, `greedyPick_spec`, `greedyAux`, `greedyAux_correct`, `greedyObservationSet`, `greedyObservationSet_correct`, `greedyObservation_empty` | 入力順の最大新規被覆点を選び、成功時の十分集合・失敗時の不適合全点固定元を証明済み |
| C1: 調和数近似保証 | — | 未証明 |
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
`worstQueries` は全実行の回数の上限、`optimalQueries` は全正答手続きの最小値である。
`worstQueries_attained` は有限な `G` と全変更での停止を使い、上限が実際の実行の
最大値であることを示す。`fixedProcedure` は有限集合の各点を一回ずつ質問し、
得た履歴と一致する適合変更が存在するかで判定する。
`finiteFixedProcedure` は同じ終端判定を入力の `ExplicitEnumeration G` に対する
停止する `scan` で計算し、`finiteFixedProcedure_eq_fixed` が両者の完全一致を示す。
`finitePoints` は入力の `ExplicitEnumeration X` から最小集合の点を重複なしで列挙し、
長さが集合の濃度と一致する。`finiteFixedProcedure_executable_optimal` はこの
点列と変更列挙を使う全変更で停止・正答する手続きが `b_Γ` 回を達成することを示す。
`optimalQueries_eq_minObservations` はB1の両方向を結ぶ。最小集合自体を入力表から
全探索で計算する構成は `minimumObservation` に置く。`minimumOrWitness_optimalProcedure`
はその同じ出力集合をBの実行可能な固定質問手続きへ渡す。

Cの `candidateSets` は入力点列の全 sublist を集合に変換する。重複した列挙からも
任意の有限 `B` が現れることを `mem_candidateSets` が示す。`sufficientBool` は入力の
変更列挙から作った有限量化で点安定化群の包含を決定し、`minimumObservation`
はその真となる候補を `argmin` で選ぶ。`some B` なら同じ `B` が十分で全候補より
濃度が小さく、`B.card=b_Γ` となる。`none` なら十分な有限集合は存在しない。
`findIncompatibleFixer` は全点を固定する不適合な元を変更列挙から走査し、
`minimumOrWitness` の失敗枝で実際にその元を返す。恒等元と同じ全点観測で
適合性が異なること、`b_Γ=D_Γ=∞` を同じ出力に対して証明する。
調和数保証は後続のC義務である。
`incompatibleSet` は不適合変更全体、`detectedSet x` は点 `x` で動く不適合変更を
入力変更表から構成する。`sufficient_iff_cover` は任意の有限 `B` について、
元の `Sufficient Gamma B` と `B` の検出集合の和集合が全不適合変更に等しいことを
双方向に証明する。greedy法とC1はこの同じ被覆族を使う。
`greedyPick` は残る不適合元の新規被覆数を最大にする点を入力の点列から選び、
同数ならその列で最初に現れた点を保つ。`greedyAux` は正の新規被覆のたびに
残集合を真に縮める有限再帰であり、十分な燃料を初期 `U.card` から与える。
`greedyObservationSet_correct` は実際の出力集合が十分か、返した元が不適合で
全点を固定し `b_Γ=D_Γ=∞` を証明する。`U=∅` の場合は空集合を返す。
返す集合の濃度に対する調和数上界C1は残る。

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

## Cycle 4 selection / proposed result

```yaml
ledger_type: target_cycle_result
goal: G-128-aat-minimal-compatibility-observations
cycle: 4
goal_blob_sha: e50d778b5b0592a79c1b12506a6c04fe71a6c147
base_oid: c01539c1e98ba0af7000803a82d1ecdca9dd1dbb
tracking_issue: 5075
report_path: research/reports/G-128-aat-minimal-compatibility-observations.md
selection:
  proof_state_ref: Issue #5075 cycle 3 accepted state
  proof_dag_predecessors: [AdaptiveLowerBound.minObservations_le_identity_queries, PointObservation.minObservations_attained]
  milestone: B1の最悪時最適性と固定集合による達成
  proof_obligations: [最悪時回数, 正答手続きの最適値, 固定質問手続きの停止・正答・回数, B1の等号]
  exit_criteria: [B1の同じ群作用での等号, 有限値を達成する固定集合と手続き, focused checkと公理監査]
  selection_reason: cycle 3で証明した適応下限に固定集合からの上界を接続する
  expected_result_type: proof-obligation-discharged
  lean_targets: [ResearchLean/AG/MinimalCompatibilityObservations/QueryOptimum.lean]
  risks: [全変更に対する正答, 重複質問の回数, 有限表での計算可能性, 最悪時最大値]
  unchecked: [C最小集合・判定不能・greedy, D, E, 指定例]
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: 全決定的手続きの最悪時回数と最適値を定義し、有限群での最大値と有限表の固定質問手続きの停止・正答からB1と達成を証明
  exit_criteria_status: [B1と達成の宣言を追加, focused checkと公理監査成功]
  split_reason: none
  completion_candidate: no
  lean_artifacts: [QueryOptimum.lean]
  evidence: [minObservations_le_optimalQueries, worstQueries_attained, fixedProcedure_run, fixedAnswer_correct, fixedProcedure_correct, finiteFixedProcedure_eq_fixed, finitePoints_length, finiteFixedProcedure_executable_optimal, optimalQueries_eq_minObservations]
  claim_mapping:
    theorem_names: [worstQueries_attained, finiteFixedProcedure_executable_optimal, optimalQueries_eq_minObservations]
    source_labels: [B1, B 有限値での達成]
    conjuncts: [全変更の停止・正答, 重複を数える最悪時回数, 下限, 上界, 等号, 固定集合での達成]
    undischarged_assumptions: []
    acceptance_point: 一般の作用のままB1を証明し、有限値の固定集合が最適値を達成
    port_status: unported
audits:
  premise_delta:
    discharged: [全手続きの最悪時下限, 固定手続きの停止・正答・上界, B1]
    remaining: [Cの残り, D, E, 指定例]
  certificate_provenance:
    discharged: [達成集合はAのminObservations_attainedから選択]
    unresolved: []
  proof_use:
    used: [cycle 3のidentity下限, Aの十分集合と最小値達成, QueryRun.deterministic]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [単一file focused checkとnamespace公理監査をPRに記録]
  blocking_findings: []
  next_obligation: Cの有限表からの最小集合・判定不能の元・greedy構成
```

## Cycle 5 selection / proposed result

```yaml
ledger_type: target_cycle_result
goal: G-128-aat-minimal-compatibility-observations
cycle: 5
goal_blob_sha: e50d778b5b0592a79c1b12506a6c04fe71a6c147
base_oid: 7bf21af3eb4a0fe75460fb97d61de5dd6c3f5f6c
tracking_issue: 5075
report_path: research/reports/G-128-aat-minimal-compatibility-observations.md
selection:
  proof_state_ref: Issue #5075 cycle 4 accepted state
  proof_dag_predecessors: [PointObservation.minObservations_attained, QueryOptimum.finiteFixedProcedure, FiniteExtension.scan]
  milestone: Cの有限表からの最小観測集合または判定不能の実際の元
  proof_obligations: [全有限集合の実行可能な列挙, 十分性の決定, 最小濃度, 失敗時の全点固定不適合元, AとBへの対応]
  exit_criteria: [二分岐の停止する関数, 返した同じ集合・元の正確性, focused checkと公理監査]
  selection_reason: Bの有限表手続きに入力表から構成した最小集合を渡し、Cの判定不能を実元で証明する
  expected_result_type: proof-obligation-discharged
  lean_targets: [ResearchLean/AG/MinimalCompatibilityObservations/FiniteMinimum.lean]
  risks: [重複した入力列挙, 空点集合, Cの失敗枝に結論相当の証書を渡す危険]
  unchecked: [C集合被覆・greedy・C1, D, E, 指定例]
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: 入力列から全候補を探索し最小集合または全点を固定する不適合元を返し、その同じ値から分類とBの最適手続きを導出
  exit_criteria_status: [二分岐のOptionとSum探索, 最小濃度・失敗元の証明, focused checkと公理監査成功]
  split_reason: none
  completion_candidate: no
  lean_artifacts: [FiniteMinimum.lean]
  evidence: [mem_candidateSets, sufficientBool_iff, minimumObservation_some, minimumObservation_none_iff, minimumObservation_card, findIncompatibleFixer_some, no_sufficient_iff_incompatible_fixer, minimumOrWitness_correct, minimumOrWitness_classifier, minimumOrWitness_optimalProcedure, minimumOrWitness_invisible]
  claim_mapping:
    theorem_names: [minimumOrWitness_correct, minimumOrWitness_optimalProcedure, minimumOrWitness_invisible]
    source_labels: [C 最小集合と判定不能の証拠, B 有限表からの最適手続き]
    conjuncts: [候補の完全性, 返した集合の最小性, 返した元の不適合性と全点固定, bとDの∞, 同じ集合による分類と最適質問]
    undischarged_assumptions: []
    acceptance_point: 実際の有限表関数の両分岐から元の群作用・適合群の結論を取得
    port_status: unported
audits:
  premise_delta:
    discharged: [Cの最小集合と判定不能の元, 有限表からBの最適手続きへの接続]
    remaining: [Cの集合被覆とgreedy・C1, D, E, 指定例]
  certificate_provenance:
    discharged: [最小集合は入力点列のsublistsからargminで選択, 判定不能元は入力変更列からscanで選択]
    unresolved: []
  proof_use:
    used: [AのSufficientとminObservations, BのfiniteFixedProcedure, FiniteExtension.scan, G-127のExplicitEnumeration]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [単一file focused checkとnamespace公理監査をPRに記録]
  blocking_findings: []
  next_obligation: Cの集合被覆・greedy・調和数近似保証
```

## Cycle 6 selection / proposed result

```yaml
ledger_type: target_cycle_result
goal: G-128-aat-minimal-compatibility-observations
cycle: 6
goal_blob_sha: e50d778b5b0592a79c1b12506a6c04fe71a6c147
base_oid: fb8a968b2ac59f07506793bd17a346bd975ba100
tracking_issue: 5075
report_path: research/reports/G-128-aat-minimal-compatibility-observations.md
selection:
  proof_state_ref: Issue #5075 cycle 5 accepted state
  proof_dag_predecessors: [PointObservation.Sufficient, ProtocolHolonomy.ExplicitEnumeration.toFintype]
  milestone: Cの元の作用表に対する集合被覆対応
  proof_obligations: [Uの構成, 点ごとの検出集合, 十分性と被覆の両方向]
  exit_criteria: [同じGamma・作用からUとS_xを定義, 全Bについて被覆との同値, focused checkと公理監査]
  selection_reason: greedyが最大新規被覆点を選ぶ前に、最適化対象と元の適合性判定の一致を固定する
  expected_result_type: proof-checkpoint
  lean_targets: [ResearchLean/AG/MinimalCompatibilityObservations/FiniteCover.lean]
  risks: [S_xがUの外に出る誤り, 被覆の片方向だけの証明, 結論相当のcover仮定]
  unchecked: [C greedy・C1, D, E, 指定例]
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: 入力表からUとS_xを構成し、任意のBについて十分性と和集合による被覆が同値と証明
  exit_criteria_status: [UとS_xを定義, 被覆同値を証明, focused checkと公理監査成功]
  split_reason: set-coverの双方向同値はgreedyの証明で独立に再利用される中心補題なので選択規則の実装前に査読する
  completion_candidate: no
  lean_artifacts: [FiniteCover.lean]
  evidence: [mem_incompatibleSet, mem_detectedSet, cover_subset_incompatible, sufficient_iff_cover]
  claim_mapping:
    theorem_names: [sufficient_iff_cover]
    source_labels: [C 集合被覆]
    conjuncts: [Uは全不適合変更, S_xは動く不適合変更, 任意Bの十分性と被覆の双方向]
    undischarged_assumptions: []
    acceptance_point: AとCの元の適合性判定を同じ有限表のset-cover条件へ結ぶ
    port_status: unported
audits:
  premise_delta:
    discharged: [Cの集合被覆対応]
    remaining: [C greedy・C1, D, E, 指定例]
  certificate_provenance:
    discharged: [UとS_xは入力のGammaと作用から定義]
    unresolved: []
  proof_use:
    used: [PointObservation.Sufficient, G-127のExplicitEnumeration]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [単一file focused checkとnamespace公理監査をPRに記録]
  blocking_findings: []
  next_obligation: Cのgreedy実行関数と調和数近似保証
```

## Cycle 7 selection / proposed result

```yaml
ledger_type: target_cycle_result
goal: G-128-aat-minimal-compatibility-observations
cycle: 7
goal_blob_sha: e50d778b5b0592a79c1b12506a6c04fe71a6c147
base_oid: b5711070186a0822e3e00a8590e6cc44fd8e5135
tracking_issue: 5075
report_path: research/reports/G-128-aat-minimal-compatibility-observations.md
selection:
  proof_state_ref: Issue #5075 cycle 6 accepted state
  proof_dag_predecessors: [FiniteCover.incompatibleSet, FiniteCover.detectedSet, FiniteCover.sufficient_iff_cover, FiniteMinimum.findIncompatibleFixer]
  milestone: Cの入力順greedy実行関数と成功・失敗の正確性
  proof_obligations: [最大新規被覆と同数時入力順, 停止, 成功時の十分集合, 失敗時の全点固定不適合元, U空の場合]
  exit_criteria: [実行可能なgreedy関数, 実際の同じ出力の正確性, focused checkと公理監査]
  selection_reason: C1の調和数点数保証を適用する対象の実行関数と選択規則を先に固定する
  expected_result_type: proof-checkpoint
  lean_targets: [ResearchLean/AG/MinimalCompatibilityObservations/GreedySelection.lean]
  risks: [燃料不足への逃避, 零利得で不正なfallback, 全探索をgreedyから呼ぶ逃避, 同数処理]
  unchecked: [C1, D, E, 指定例]
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: 入力点列の最大新規被覆選択と有界再帰を構成し、出力集合の十分性または実際の不適合全点固定元を証明
  exit_criteria_status: [選択規則と同数時入力順を証明, 初期U.card燃料で成功・失敗の正確性を証明, focused checkと公理監査成功]
  split_reason: C1の量的保証は同じgreedy関数の点数に対する別の帰納証明であり、実行関数と正確性を固定してから監査する
  completion_candidate: no
  lean_artifacts: [GreedySelection.lean]
  evidence: [greedyPick_spec, greedyPick_zero_fixer, greedyFallback_correct, greedyAux_correct, greedyObservationSet_correct, greedyObservation_empty]
  claim_mapping:
    theorem_names: [greedyPick_spec, greedyAux_correct, greedyObservationSet_correct]
    source_labels: [C greedy選択・停止・正確性]
    conjuncts: [最大新規被覆, 入力順tie, 残集合の減少, 成功時被覆, 失敗時元, U空で空集合]
    undischarged_assumptions: [C1調和数近似保証]
    acceptance_point: 元の有限表から実行する同じgreedy出力をCの判定条件へ結ぶcheckpoint
    port_status: unported
audits:
  premise_delta:
    discharged: [C greedyの実行と正確性]
    remaining: [C1, D, E, 指定例]
  certificate_provenance:
    discharged: [最大利得点は入力点列からargmax, 失敗元は入力変更列からscan]
    unresolved: []
  proof_use:
    used: [FiniteCoverのUとS_x, sufficient_iff_cover, FiniteMinimum.findIncompatibleFixer, List.argmaxの最大・tie定理]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [単一file focused checkとnamespace公理監査をPRに記録]
  blocking_findings: []
  next_obligation: 同じgreedyObservationSet出力のC1調和数近似保証
```
