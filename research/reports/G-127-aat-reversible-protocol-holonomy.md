# G-127 — 可逆操作のholonomyと持ち上げ

- 一次仕様: [`G-127-aat-reversible-protocol-holonomy.md`](../goals/G-127-aat-reversible-protocol-holonomy.md)
- tracking Issue: [#4981](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/4981)
- 固定 GOAL・共通基準・既存宣言 commit: `b80cb54dcc7ab5e2cd3316727e23d968490f2345`
- 固定 GOAL blob: `86ed6948771755a19db802e01e42dbd00a8f9abf`
- proof state: `target-proof-checkpoint`

この report は固定 GOAL の条項と Lean 証拠の対応を示す。実行・レビュー履歴は
tracking Issue と PR に置く。

## 宣言と条項

| 条項 | Lean 宣言 | 対応と残る義務 |
| --- | --- | --- |
| A の可変 fiber と辺作用 | `ReversibleData.Fiber`, `ReversibleData.edgeEquiv` | 任意のグラフ上の型と可逆辺作用。有限性と `Π,H` は未接続 |
| A1 の持ち上げ | `ReversibleData.Lift`, `ReversibleData.renamedEdgeEquiv` | 元の名前付き辺作用と改名後の辺作用を全状態で結ぶ等式。`Lift` の存在は入力しない |
| A の全状態写像 | `ReversibleData.Lift.stateEquiv`, `stateEquiv_observation`, `stateEquiv_injective` | 各 fiber の全単射から `Σ_v F(v)` 上の全単射を構成し、観測と忠実性を証明。逆方向の対応は未構成 |
| A2 の実際の変更群 | `ReversibleData.NamedExecution`, `StateChange`, `ChangeGroup`, `ChangeGroup.projection` | 名前付き実行関係を保つ全状態の全単射を合成・逆で群にし、指定可視部分群 `H` への射影を構成。`Lift` との同定は未構成 |

## 前提・構成の状態

`Q` と可変 `F(v),T_e` は A の入力。`Lift` の `fiber` は分類対象の要素であり、
`edge_naturality` は A1 そのもの。`stateEquiv` はこの入力から生成する。
`renamedEdgeEquiv` の型変換は `FixedFGraphAutomorphism.source_rename` と
`target_rename` の証明だけを使用する。

A の有限性・`Π`・`H` の入力条件、全状態写像による操作保存の明示定理と
逆方向の対応、A2 の `Lift` との群同定と式(A2)、B の道とholonomy、C の持ち上げ分類・完全列・torsor、
D の表示変更と意味論、E の有限手続き、二つの固定例は未完了である。
現在の宣言を固定targetの完了証拠として扱わない。

## Cycle 1 selection / proposed result

```yaml
ledger_type: target_cycle_result
goal: G-127-aat-reversible-protocol-holonomy
cycle: 1
goal_blob_sha: 86ed6948771755a19db802e01e42dbd00a8f9abf
base_oid: 005f379f301a4aa58ea5dcf5a1cb32519cf35fd3
tracking_issue: 4981
report_path: research/reports/G-127-aat-reversible-protocol-holonomy.md
selection:
  proof_state_ref: Issue #4981 initial proof state
  proof_dag_predecessors: [FixedFDirectedMultigraph, FixedFGraphAutomorphism]
  proof_obligation: Construct A1 over varying fibers and its total state change
  selection_reason: Supplies the named-edge square and state map used by A2 through D
  expected_result_type: proof-checkpoint
  lean_targets: [ResearchLean/AG/ProtocolHolonomy/Basic.lean]
  risks: [dependent endpoint transports, state-map faithfulness, absent A2 group]
  unchecked: [finite input, Pi equations, H congruence preservation, operation preservation on total states, reverse state-map correspondence, A2 through E, finite examples]
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: The A1 solution type is defined and maps injectively to total state equivalences over a fixed visible automorphism
  completion_candidate: no
  lean_artifacts: [ReversibleData.Lift, ReversibleData.Lift.stateEquiv]
  evidence: [ReversibleData.Lift.stateEquiv_observation, ReversibleData.Lift.stateEquiv_injective]
  claim_mapping:
    theorem_names: [ReversibleData.Lift.stateEquiv_injective]
    source_labels: [A1, A total state change]
    conjuncts: [named-edge square in Lift.edge_naturality, state equivalence in stateEquiv]
    undischarged_assumptions: [finite input, Pi equations, H congruence preservation]
    acceptance_point: Varying fibers, edge actions and the A1 solution type are defined; a fixed-visible total-state map is constructed injectively
    port_status: unported
audits:
  premise_delta:
    discharged: [state equivalence generated from each fiber equivalence]
    remaining: [finite input, Pi equations, H congruence preservation, explicit operation preservation on total states, reverse state-map correspondence, A2 through E, fixed examples]
  certificate_provenance:
    discharged: [stateEquiv from Lift.fiber and graph vertex equivalence]
    unresolved: [finite input and protocol semantics]
  proof_use:
    used: [Lift.fiber in stateEquiv, graph endpoint laws in renamedEdgeEquiv]
    unused: [Lift.edge_naturality in the state-map construction]
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [focused Lean check and axiom audit to be recorded in PR]
  blocking_findings: []
  next_obligation: Construct A2 group law and projection from actual state maps
```

## Cycle 2 selection / proposed result

```yaml
ledger_type: target_cycle_result
goal: G-127-aat-reversible-protocol-holonomy
cycle: 2
goal_blob_sha: 86ed6948771755a19db802e01e42dbd00a8f9abf
base_oid: 749cb99abb084072ddbbdc883eaade1e46e46d6a
tracking_issue: 4981
report_path: research/reports/G-127-aat-reversible-protocol-holonomy.md
selection:
  proof_state_ref: Issue #4981 Cycle 1 proof state and Basic.lean
  proof_dag_predecessors: [ReversibleData, ReversibleData.Lift, FixedFGraphAutomorphism]
  proof_obligation: Construct actual operation-preserving change group and visible projection
  selection_reason: Gives A2 a concrete total-state group without assuming lift existence or projection surjectivity
  expected_result_type: proof-checkpoint
  lean_targets: [ResearchLean/AG/ProtocolHolonomy/ChangeGroup.lean]
  risks: [equivalence with Lift, reverse preservation, H membership, operation relation]
  unchecked: [Lift-to-StateChange equivalence, fiber formula A2, finite and Pi input, B through E, fixed examples]
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: Actual total-state operation-preserving changes form a group with visible projection into H
  completion_candidate: no
  lean_artifacts: [ReversibleData.NamedExecution, ReversibleData.StateChange, ReversibleData.ChangeGroup]
  evidence: [StateChange group instance, StateChange.projection, ChangeGroup.projection]
  claim_mapping:
    theorem_names: [StateChange.pair_injective, ChangeGroup.projection_apply]
    source_labels: [A named-operation preservation, A2 group and projection]
    conjuncts: [actual total-state equivalence, visible observation, named-execution preservation, group composition and inverse, visible homomorphism]
    undischarged_assumptions: [finite input, Pi equations, H congruence preservation]
    acceptance_point: A direct actual-change group is constructed; identification with Lift and the A2 fiber formula remain open
    port_status: unported
audits:
  premise_delta:
    discharged: [group closure of actual named-execution preserving changes, projection into selected H]
    remaining: [Lift correspondence, A2 fiber formula, finite input, Pi equations, H congruence preservation, B through E, fixed examples]
  certificate_provenance:
    discharged: [group operation from actual total-state and graph equivalences, named relation from edgeEquiv]
    unresolved: [Lift correspondence]
  proof_use:
    used: [named relation in closure and inverse, observation in closure and inverse]
    unused: [Lift.edge_naturality in this independent group construction]
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [focused Lean check and axiom audit to be recorded in PR]
  blocking_findings: []
  next_obligation: Identify Lift with the fixed-visible state-change fiber and prove A2 component formula
```
