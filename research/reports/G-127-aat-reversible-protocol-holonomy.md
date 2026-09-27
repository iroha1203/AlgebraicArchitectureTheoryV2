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
| A の全状態写像 | `ReversibleData.Lift.stateEquiv`, `stateEquiv_observation`, `stateEquiv_injective` | 各 fiber の全単射から `Σ_v F(v)` 上の全単射を構成し、観測と固定可視変更での単射性を証明 |
| A2 の実際の変更群 | `ReversibleData.NamedExecution`, `StateChange`, `ChangeGroup`, `ChangeGroup.projection` | 名前付き実行関係を保つ全状態の全単射を合成・逆で群にし、指定可視部分群 `H` への射影を構成 |
| A1 と A2 の実変更への対応 | `Lift.maps_namedExecution`, `Lift.preserves_namedExecution`, `StateChange.toLift`, `liftEquivStateChangeOver`, `liftPairMulEquivChangeGroup`, `liftPair_mul_fiber_apply`, `liftPairProjection` | 各 fiber の A1 と名前付き実行保存を同定し、固定可視変更と全対の群を実変更に対応させ、(A2) の評価式と射影を証明 |
| B の符号付き道と輸送 | `TypedEdge`, `SignedPath`, `ReversibleData.signedEdgeEquiv`, `ReversibleData.transport`, `transport_comp`, `transport_reverse` | 元の辺名を持つ有向辺と逆向き通過の道を構成し、辺作用の逆・道の連結・反転に対する輸送を証明。根・木・holonomy は未構成 |
| A の有限入力・経路等式・可視群 | `PositivePath`, `PathEquations`, `PathEquations.Congruent`, `FiniteProtocolInput`, `FiniteProtocolInput.preserves_congruence`, `PathEquations.preservesCongruence_iff_generators`, `FiniteProtocolInput.visible_preserves_congruence` | 有限の頂点・元の辺名・fiber・生成等式、等式を満たす辺作用と合同を保つ `H` を同じ入力に保持。生成等式から作用の全合同保存を証明し、`H` の生成条件と全合同保存を同値化。実行圏との同定と E の表は未構成 |

`PathEquations.lean` の一頂点二ループ例では、`a=空道` から生成した合同は
`a` と空道を結ぶが `b` と空道を結ばない。辺名の交換は生成等式と
合同全体のどちらも保たず、恒等変更はどちらも保つ。

## 前提・構成の状態

`Q` と可変 `F(v),T_e`、有限性、`Π`、`H` は A の入力。`Lift` の `fiber` は分類対象の要素であり、
`edge_naturality` は A1 そのもの。`stateEquiv` はこの入力から生成する。
`renamedEdgeEquiv` の型変換は `FixedFGraphAutomorphism.source_rename` と
`target_rename` の証明だけを使用する。

B の根・木とholonomy、C の持ち上げ分類・完全列・torsor、
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

## Cycle 3 selection / proposed result

```yaml
ledger_type: target_cycle_result
goal: G-127-aat-reversible-protocol-holonomy
cycle: 3
goal_blob_sha: 86ed6948771755a19db802e01e42dbd00a8f9abf
base_oid: 271bce5ca699e105b0317bfe2f8bc7b3b439fffb
tracking_issue: 4981
report_path: research/reports/G-127-aat-reversible-protocol-holonomy.md
selection:
  proof_state_ref: Issue #4981 Cycle 2 proof state and Basic/ChangeGroup declarations
  proof_dag_predecessors: [ReversibleData.Lift, ReversibleData.StateChange, ReversibleData.ChangeGroup]
  proof_obligation: Identify Lift with actual state changes and prove pair group formula A2
  selection_reason: Closes the bridge between A1's independently defined solution type and A2's actual state-change group
  expected_result_type: proof-obligation-discharged
  lean_targets: [ResearchLean/AG/ProtocolHolonomy/LiftBridge.lean]
  risks: [dependent fiber extraction, reverse operation preservation, group transport, hidden conditionality]
  unchecked: [finite input, Pi equations, H congruence preservation, B through E, fixed examples]
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: A1 solutions and actual changes are equivalent at fixed visible renaming; pair group is isomorphic to actual changes and has formula A2
  completion_candidate: no
  lean_artifacts: [LiftBridge.lean]
  evidence: [Lift.preserves_namedExecution, StateChange.fiberEquiv_naturality, liftEquivStateChangeOver, liftPairMulEquivChangeGroup, liftPair_mul_fiber_apply, liftPairProjection]
  claim_mapping:
    theorem_names: [liftEquivStateChangeOver, liftPairMulEquivChangeGroup, liftPair_mul_fiber_apply, liftPairProjection]
    source_labels: [A1, A2, A total state change]
    conjuncts: [actual named-operation preservation, fiberwise recovery, both inverse laws, group correspondence, pair multiplication formula, visible group projection]
    undischarged_assumptions: [finite input, Pi equations, H congruence preservation]
    acceptance_point: The selected A1-to-A2 group bridge is proved on arbitrary reversible edge data; the full fixed input and B-E remain open
    port_status: unported
audits:
  premise_delta:
    discharged: [Lift-StateChange correspondence, pair group correspondence, A2 component formula]
    remaining: [finite input, Pi equations, H congruence preservation, B through E, fixed examples]
  certificate_provenance:
    discharged: [fiber equivalences recovered from actual total-state equivalence and observation, inverse law from proved equivalences]
    unresolved: [finite protocol semantics]
  proof_use:
    used: [Lift.edge_naturality in operation preservation, StateChange.preserves in recovered naturality, group multiplication in A2 formula]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [focused Lean check and axiom audit to be recorded in PR]
  blocking_findings: []
  next_obligation: Integrate finite Q/F, path equations Pi, and congruence-preserving H into the primitive input
```

## Cycle 4 selection / proposed result

```yaml
ledger_type: target_cycle_result
goal: G-127-aat-reversible-protocol-holonomy
cycle: 4
goal_blob_sha: 86ed6948771755a19db802e01e42dbd00a8f9abf
base_oid: 18c13b179afe277fbaeae4e431f5b97b762e6787
tracking_issue: 4981
report_path: research/reports/G-127-aat-reversible-protocol-holonomy.md
selection:
  proof_state_ref: Issue #4981 Cycle 3 proof state and Basic/LiftBridge declarations
  proof_dag_predecessors: [ReversibleData.edgeEquiv, FixedFDirectedMultigraph]
  proof_obligation: Construct signed named paths and prove composition and reversal of transport
  selection_reason: Supplies the path action used by equations, holonomy and root-lift classification
  expected_result_type: proof-checkpoint
  lean_targets: [ResearchLean/AG/ProtocolHolonomy/Transport.lean]
  risks: [dependent endpoint casts, inverse-edge action, path composition]
  unchecked: [finite input, Pi equations, H congruence preservation, B root/tree and holonomy, C through E, fixed examples]
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: Signed named paths act by fiber equivalences; composition and path reversal agree with equivalence composition and inversion
  completion_candidate: no
  lean_artifacts: [TypedEdge, SignedPath, ReversibleData.transport]
  evidence: [ReversibleData.transport_positive, ReversibleData.transport_negative, ReversibleData.transport_comp, ReversibleData.transport_reverse]
  claim_mapping:
    theorem_names: [ReversibleData.transport_comp, ReversibleData.transport_reverse]
    source_labels: [B signed path transport]
    conjuncts: [named edge with typed endpoints, inverse edge action, path composition, reversed path action]
    undischarged_assumptions: [finite input, Pi equations, H congruence preservation]
    acceptance_point: Signed path transport is established for arbitrary reversible edge data; root/tree and holonomy remain open
    port_status: unported
audits:
  premise_delta:
    discharged: [transport action of positive and negative named edges, composition and reversal of paths]
    remaining: [finite input, Pi equations, H congruence preservation, B root/tree and holonomy, C through E, fixed examples]
  certificate_provenance:
    discharged: [signed paths from the original named graph, inverse transport from edgeEquiv]
    unresolved: [finite protocol semantics]
  proof_use:
    used: [edgeEquiv in signedEdgeEquiv, signedEdgeEquiv in transport, transport in composition and reverse laws]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [focused Lean check and axiom audit to be recorded in PR]
  blocking_findings: []
  next_obligation: Connect finite path equations Pi and H congruence preservation to primitive data
```

## Cycle 5 selection / proposed result

```yaml
ledger_type: target_cycle_result
goal: G-127-aat-reversible-protocol-holonomy
cycle: 5
goal_blob_sha: 86ed6948771755a19db802e01e42dbd00a8f9abf
base_oid: 184f198712782355040ad24e43f284db81ffe95c
tracking_issue: 4981
report_path: research/reports/G-127-aat-reversible-protocol-holonomy.md
selection:
  proof_state_ref: Issue #4981 Cycle 4 proof state and Transport.lean
  proof_dag_predecessors: [ReversibleData, PositivePath, ReversibleData.transport]
  proof_obligation: Connect finite Q/F, directed path equations and congruence-preserving H to primitive data
  selection_reason: This is the complete A-side input required by the remaining holonomy, semantics and finite construction
  expected_result_type: proof-checkpoint
  lean_targets: [ResearchLean/AG/ProtocolHolonomy/PathEquations.lean]
  risks: [directed versus signed paths, congruence closure, equation action, H renaming]
  unchecked: [quotient execution category correspondence, B root/tree and holonomy, C through E, fixed examples]
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: Finite protocol input contains named graph, finite fibers, finite parallel path equations, equation-respecting edge action and a subgroup preserving the generated congruence
  completion_candidate: no
  lean_artifacts: [PathEquations, PathEquations.Congruent, FiniteProtocolInput]
  evidence: [ReversibleData.positiveTransport_comp, FiniteProtocolInput.preserves_congruence, PathEquations.preservesCongruence_iff_generators, FiniteProtocolInput.visible_preserves_congruence]
  claim_mapping:
    theorem_names: [FiniteProtocolInput.preserves_congruence, PathEquations.preservesCongruence_iff_generators, FiniteProtocolInput.visible_preserves_congruence]
    source_labels: [A primitive input and generated path congruence]
    conjuncts: [finite vertices/edges/fibers/equation indices, original directed named paths, equation action, generated congruence, H preservation]
    undischarged_assumptions: [equationsHold and H preservation are GOAL A input conditions, not consequences of arbitrary edge actions]
    acceptance_point: A-side finite primitive input is packaged with generated congruence and proved closure laws; quotient semantics and B-E remain open
    port_status: unported
audits:
  premise_delta:
    discharged: [positive-path action extends to generated congruence from input equation laws, H generator criterion equivalent to full congruence preservation]
    remaining: [execution quotient correspondence, B root/tree and holonomy, C through E, fixed examples]
  certificate_provenance:
    discharged: [all path action from primitive edgeEquiv, full congruence closure by inductive generation]
    unresolved: [execution category adapter, finite tables]
  proof_use:
    used: [edgeEquiv through transport in positive path action, satisfies in congruence proof, renaming_preserves in visible congruence proof]
    unused: [finiteVertex, finiteEdge, finiteFiber in the path-congruence proofs]
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [focused Lean check and axiom audit to be recorded in PR]
  blocking_findings: []
  next_obligation: Build root and spanning path infrastructure for B
```
