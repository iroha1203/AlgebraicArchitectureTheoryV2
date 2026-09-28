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
| A の可変 fiber と辺作用 | `ReversibleData.Fiber`, `ReversibleData.edgeEquiv` | 任意のグラフ上の型と可逆辺作用。`FiniteProtocolInput` はこれを `data` とし、有限の `Π` と `H` を別fieldに保持する |
| A1 の持ち上げ | `ReversibleData.Lift`, `ReversibleData.renamedEdgeEquiv` | 元の名前付き辺作用と改名後の辺作用を全状態で結ぶ等式。`Lift` の存在は入力しない |
| A の全状態写像 | `ReversibleData.Lift.stateEquiv`, `stateEquiv_observation`, `stateEquiv_injective` | 各 fiber の全単射から `Σ_v F(v)` 上の全単射を構成し、観測と固定可視変更での単射性を証明 |
| A2 の実際の変更群 | `ReversibleData.NamedExecution`, `StateChange`, `ChangeGroup`, `ChangeGroup.projection` | 名前付き実行関係を保つ全状態の全単射を合成・逆で群にし、指定可視部分群 `H` への射影を構成 |
| A1 と A2 の実変更への対応 | `Lift.maps_namedExecution`, `Lift.preserves_namedExecution`, `StateChange.toLift`, `liftEquivStateChangeOver`, `liftPairMulEquivChangeGroup`, `liftPair_mul_fiber_apply`, `liftPairProjection` | 各 fiber の A1 と名前付き実行保存を同定し、固定可視変更と全対の群を実変更に対応させ、(A2) の評価式と射影を証明 |
| B の符号付き道と輸送 | `TypedEdge`, `SignedPath`, `ReversibleData.signedEdgeEquiv`, `ReversibleData.transport`, `transport_comp`, `transport_reverse` | 元の辺名を持つ有向辺と逆向き通過の道を構成し、辺作用の逆・道の連結・反転に対する輸送を証明。根道との接続は下行 |
| A の有限入力・経路等式・可視群 | `PositivePath`, `PathEquations`, `PathEquations.Congruent`, `FiniteProtocolInput`, `FiniteProtocolInput.preserves_congruence`, `PathEquations.preservesCongruence_iff_generators`, `FiniteProtocolInput.visible_preserves_congruence` | 有限の頂点・元の辺名・fiber・生成等式、等式を満たす辺作用と合同を保つ `H` を同じ入力に保持。生成等式から作用の全合同保存を証明し、`H` の生成条件と全合同保存を同値化。実行圏との同定と E の表は未構成 |
| B の成分と根道 | `SignedReachable`, `signedReachable_iff_undirected`, `component_eq_iff_signedReachable`, `RootedPaths`, `rootedPathsOfRoots`, `chooseRootedPaths` | 元の名前付き辺の正逆道の存在と既存の無向成分を同定。各成分の任意の根選択から根道を構成し、根自身への道を空道に固定。有限表の全域森とholonomyは未構成 |

`PathEquations.lean` の一頂点二ループ例では、`a=空道` から生成した合同は
`a` と空道を結ぶが `b` と空道を結ばない。辺名の交換は生成等式と
合同全体のどちらも保たず、恒等変更はどちらも保つ。
`RootedPaths.lean` の無辺二頂点例では同一点間に空道があり、異なる
二頂点間には符号付き道がない。`RootedPaths` 自体は任意のグラフで
`chooseRootedPaths` が構成するため、不成立例は存在しない。

## 前提・構成の状態

`Q` と可変 `F(v),T_e`、有限性、`Π`、`H` は A の入力。`Lift` の `fiber` は分類対象の要素であり、
`edge_naturality` は A1 そのもの。`stateEquiv` はこの入力から生成する。
`renamedEdgeEquiv` の型変換は `FixedFGraphAutomorphism.source_rename` と
`target_rename` の証明だけを使用する。

B の有限表の全域森とholonomy、C の持ち上げ分類・完全列・torsor、
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
    undischarged_assumptions: [satisfies and renaming_preserves are GOAL A input conditions, not consequences of arbitrary edge actions]
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

## Cycle 6 selection / proposed result

```yaml
ledger_type: target_cycle_result
goal: G-127-aat-reversible-protocol-holonomy
cycle: 6
goal_blob_sha: 86ed6948771755a19db802e01e42dbd00a8f9abf
base_oid: 376a9055d659287823d14c876ef9c6e8da92acb4
tracking_issue: 4981
report_path: research/reports/G-127-aat-reversible-protocol-holonomy.md
selection:
  proof_state_ref: Issue #4981 Cycle 5 proof state and Transport/PathEquations
  proof_dag_predecessors: [SignedPath, FixedFUndirectedReachable, FixedFComponent]
  proof_obligation: Relate signed named paths to graph components and construct paths from arbitrary component roots
  selection_reason: Supplies the root path family used in B1/B2 and C1/C2 without assuming connectedness
  expected_result_type: proof-checkpoint
  lean_targets: [ResearchLean/AG/ProtocolHolonomy/RootedPaths.lean]
  risks: [EqvGen equivalence direction, empty graph, root self-path normalization, noncomputable versus E algorithm]
  unchecked: [finite spanning forest, B holonomy/centralizer, C through E, fixed examples]
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: Signed path existence is equivalent to original undirected reachability and component equality; root paths exist for any selected root per component
  completion_candidate: no
  lean_artifacts: [SignedReachable, RootedPaths, rootedPathsOfRoots, chooseRootedPaths]
  evidence: [signedReachable_iff_undirected, component_eq_iff_signedReachable, pathFromRoot_self]
  claim_mapping:
    theorem_names: [signedReachable_iff_undirected, component_eq_iff_signedReachable, pathFromRoot_self]
    source_labels: [B undirected components and root paths]
    conjuncts: [original named positive and negative steps, reachability equivalence, arbitrary component roots, empty root path]
    undischarged_assumptions: [B specialization to paths from any chosen spanning forest, E terminating finite-table spanning-forest construction]
    acceptance_point: Root paths can be constructed for every component and arbitrary chosen root; tree-generated paths and holonomy remain open
    port_status: unported
audits:
  premise_delta:
    discharged: [signed-reachability to component equivalence, arbitrary-root path existence and self normalization]
    remaining: [finite spanning forest, B holonomy and centralizer, C through E, fixed examples]
  certificate_provenance:
    discharged: [root paths from EqvGen reachability and signed-path equivalence]
    unresolved: [finite-table spanning forest]
  proof_use:
    used: [original named edge in signed path forward/backward cases, component quotient in root path selection]
    unused: [finite input in structural reachability result]
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [focused Lean check and axiom audit to be recorded in PR]
  blocking_findings: []
  next_obligation: Construct edge-loop holonomy and prove it equals all rooted-loop transports
```

## Cycle 7 selection / proposed result

```yaml
ledger_type: target_cycle_result
goal: G-127-aat-reversible-protocol-holonomy
cycle: 7
goal_blob_sha: 86ed6948771755a19db802e01e42dbd00a8f9abf
base_oid: 38a1bfb1ef3c3c07b8f2ae55caf3f7780e7523fe
tracking_issue: 4981
report_path: research/reports/G-127-aat-reversible-protocol-holonomy.md
selection:
  proof_state_ref: Issue #4981 Cycle 6 proof state and RootedPaths/Transport
  proof_dag_predecessors: [RootedPaths, SignedPath, ReversibleData.transport]
  proof_obligation: Construct B1 edge-loop monodromies from the original named table and identify their generated subgroup with all rooted-loop transports
  selection_reason: Directly discharges the holonomy-generation calculation needed by B2 and C1
  expected_result_type: proof-checkpoint
  lean_targets: [ResearchLean/AG/ProtocolHolonomy/HolonomyGenerators.lean]
  risks: [inverse traversal, multiplication order, quotient component indexing, arbitrary root-path choices]
  unchecked: [B spanning-tree specialization and centralizer classification, C through E, fixed examples]
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: Each original edge gives an actual signed root loop whose transport is P_target inverse composed with T_edge and P_source; its generated subgroup equals the subgroup whose members are exactly transports of all root loops
  completion_candidate: no
  lean_artifacts: [RootedPaths.edgeLoopAt, ReversibleData.edgeMonodromyAt, ReversibleData.holonomy, ReversibleData.rootedLoopTransportGroup]
  evidence: [ReversibleData.transport_edgeLoopAt, ReversibleData.normalizedTransport_edge_mem, ReversibleData.normalizedTransport_mem_holonomy, ReversibleData.holonomy_eq_rootedLoopTransportGroup]
  claim_mapping:
    theorem_names: [ReversibleData.transport_edgeLoopAt, ReversibleData.holonomy_eq_rootedLoopTransportGroup]
    source_labels: [B1 edge monodromy and equality with all root-loop transports]
    conjuncts: [original named edge, positive and negative traversal, root-to-endpoint paths, table-derived monodromy, both subgroup inclusions, actual loop-transport carrier]
    undischarged_assumptions: [B specialization to paths from any chosen spanning tree, E terminating finite-table spanning-forest construction]
    acceptance_point: B1 holds for any RootedPaths choice; the fixed target still requires the spanning-tree route and B2 through E
    port_status: unported
audits:
  premise_delta:
    discharged: [named edge loop transport identity, each signed path normalized into table holonomy, rooted-loop equality]
    remaining: [B chosen-tree specialization and centralizer, C through E, fixed examples]
  certificate_provenance:
    discharged: [holonomy generators from original edgeEquiv and selected root paths, loop group from actual signed path transport]
    unresolved: [finite-table spanning forest]
  proof_use:
    used: [edgeEquiv through transport, original edge names through typed signed steps, positive and negative path induction]
    unused: [finite input and Π because the structural B1 identity does not require them]
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [focused Lean check and axiom audit to be recorded in PR]
  blocking_findings: []
  next_obligation: Prove B2 vertical changes are exactly the product of holonomy centralizers, then connect arbitrary chosen spanning trees
```

## Cycle 8 selection / proposed result

```yaml
ledger_type: target_cycle_result
goal: G-127-aat-reversible-protocol-holonomy
cycle: 8
goal_blob_sha: 86ed6948771755a19db802e01e42dbd00a8f9abf
base_oid: 873db15063655c09006eacb72473961d006d5059
tracking_issue: 4981
report_path: research/reports/G-127-aat-reversible-protocol-holonomy.md
selection:
  proof_state_ref: Issue #4981 Cycle 7 proof state and HolonomyGenerators/LiftBridge
  proof_dag_predecessors: [ReversibleData.Lift, ReversibleData.transport, ReversibleData.holonomy, ReversibleData.StateChange]
  proof_obligation: Construct B2 group isomorphism from actual vertical A1 lifts to the product of holonomy centralizers
  selection_reason: Closes the principal B classification and supplies the vertical group for C's exact sequence and torsor
  expected_result_type: proof-checkpoint
  lean_targets: [ResearchLean/AG/ProtocolHolonomy/VerticalCentralizer.lean]
  risks: [inverse path naturality, centralizer multiplication order, dependent component indexing, group-law provenance]
  unchecked: [B spanning-tree specialization, C through E, fixed examples]
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: A vertical A1 lift commutes with all signed transports; root evaluation lands in the holonomy centralizers and is invertible by the conjugation formula at every vertex; the correspondence is a group isomorphism under actual state-change composition
  completion_candidate: no
  lean_artifacts: [ReversibleData.RootCentralizers, ReversibleData.reconstructedFiber, ReversibleData.VerticalStateGroup, ReversibleData.verticalRootMulEquiv]
  evidence: [ReversibleData.vertical_transport_naturality, ReversibleData.vertical_root_mem_centralizer, ReversibleData.reconstructed_edge_naturality, ReversibleData.verticalRootEquiv, ReversibleData.vertical_mul_fiber_apply, ReversibleData.verticalRootMulEquiv]
  claim_mapping:
    theorem_names: [ReversibleData.verticalRootEquiv, ReversibleData.verticalRootMulEquiv]
    source_labels: [B2 root evaluation and inverse P_v a_j P_v inverse]
    conjuncts: [all components, named-edge A1, root centralizer of B1 holonomy, inverse reconstruction, both inverse laws, actual group composition]
    undischarged_assumptions: [B specialization to paths from any chosen spanning tree, E terminating finite-table spanning-forest construction]
    acceptance_point: B2 holds for every RootedPaths family built from the original component relation; arbitrary-tree specialization and later clauses remain open
    port_status: unported
audits:
  premise_delta:
    discharged: [vertical path naturality, centralizer membership, root reconstruction A1, root evaluation inverse laws, group compatibility]
    remaining: [B chosen-tree specialization, C through E, fixed examples]
  certificate_provenance:
    discharged: [centralizers from B1 original edge table, reconstructed vertical lift from centralizing root values]
    unresolved: [finite-table spanning forest]
  proof_use:
    used: [A1 edge_naturality in path naturality, holonomy generator membership in reconstruction, actual StateChange group in vertical group law]
    unused: [finite input and Π because B2's structural classification works for arbitrary reversible named operations]
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [focused Lean check and axiom audit to be recorded in PR]
  blocking_findings: []
  next_obligation: Connect every chosen spanning tree to RootedPaths and then construct C1/C2 lift criterion
```

## Cycle 9 selection / proposed result

```yaml
ledger_type: target_cycle_result
goal: G-127-aat-reversible-protocol-holonomy
cycle: 9
goal_blob_sha: 86ed6948771755a19db802e01e42dbd00a8f9abf
base_oid: b854968d4ec27f1204bbd86d84f645872545dc33
tracking_issue: 4981
report_path: research/reports/G-127-aat-reversible-protocol-holonomy.md
selection:
  proof_state_ref: Issue #4981 Cycle 8 proof state and RootedPaths/HolonomyGenerators/VerticalCentralizer
  proof_dag_predecessors: [SignedPath, FixedFComponent, RootedPaths, B1, B2]
  proof_obligation: Connect original named-edge spanning trees and unique root paths to the RootedPaths family used by B1/B2
  selection_reason: Discharges the chosen-root/tree route left open by structural B1/B2 calculations
  expected_result_type: proof-checkpoint
  lean_targets: [ResearchLean/AG/ProtocolHolonomy/SpanningTrees.lean]
  risks: [parallel edge identity, reverse edge identity, empty components, path uniqueness, arbitrary undirected tree orientation]
  unchecked: [undirected-tree to outward-arborescence orientation bridge, E terminating finite-table forest, C through E, fixed examples]
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: Each original component becomes a signed named-edge quiver; every chosen outward named spanning arborescence has unique root paths and maps to RootedPaths; a geodesic named arborescence exists from any chosen root
  completion_candidate: no
  lean_artifacts: [ComponentVertex, NamedSpanningTree, NamedSpanningForest, geodesicNamedSpanningTree, chooseNamedSpanningForest]
  evidence: [component_rootedConnected, NamedSpanningTree.rootPath_unique, geodesicNamedSpanningTree_root, NamedSpanningForest.toRootedPaths]
  claim_mapping:
    theorem_names: [NamedSpanningTree.rootPath_unique, NamedSpanningForest.toRootedPaths, geodesicNamedSpanningTree_root]
    source_labels: [B chosen roots and spanning trees with unique paths]
    conjuncts: [original positive and negative named passages, existing undirected component, chosen root, unique path in an outward selected tree, empty self path, arbitrary chosen outward arborescence]
    undischarged_assumptions: [formal orientation bridge from an arbitrary undirected named spanning tree to the outward arborescence representation, E terminating finite-table forest]
    acceptance_point: B1/B2 can use the unique paths of any selected NamedSpanningForest; the full arbitrary-undirected-tree reading remains to be connected formally
    port_status: unported
audits:
  premise_delta:
    discharged: [component rooted connectedness from original signed paths, chosen outward tree unique-path-to-RootedPaths construction, geodesic tree existence from any root]
    remaining: [arbitrary undirected spanning-tree orientation bridge, E terminating construction, C through E, fixed examples]
  certificate_provenance:
    discharged: [component reachability from existing quotient, geodesic tree from Mathlib shortest paths, arbitrary chosen outward tree root path from Arborescence.uniquePath]
    unresolved: [finite-table forest]
  proof_use:
    used: [original named signed edges in component quiver and tree path map, component reachability in RootedConnected, uniquePath in toRootedPaths]
    unused: [finite input and Π because structural tree existence uses choice and shortest-path selection]
  structure_field_escape: none-found-for-chosen-tree-reading
  route_integrity: pass-for-chosen-outward-arborescences
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [focused Lean check and axiom audit to be recorded in PR]
  blocking_findings: []
  next_obligation: Formalize orientation of every undirected named spanning tree into an outward arborescence; then construct C1/C2
```

## Cycle 10 selection / proposed result

```yaml
ledger_type: target_cycle_result
goal: G-127-aat-reversible-protocol-holonomy
cycle: 10
goal_blob_sha: 86ed6948771755a19db802e01e42dbd00a8f9abf
base_oid: e3d2585c1da654318fb8dde2f87777f64edc905f
tracking_issue: 4981
report_path: research/reports/G-127-aat-reversible-protocol-holonomy.md
selection:
  proof_state_ref: Issue #4981 Cycle 9 proof state and SpanningTrees/LiftBridge/Transport
  proof_dag_predecessors: [Lift.edge_naturality, SignedPath, transport, RootedPaths.edgeLoopAt]
  proof_obligation: Derive the C1 root equations and root-value uniqueness from every actual A1 lift
  selection_reason: C1 forward implication is the first direct link from actual changes to the root solution space; the arbitrary undirected tree orientation bridge requires a separate named-simple-path development
  expected_result_type: proof-checkpoint
  lean_targets: [ResearchLean/AG/ProtocolHolonomy/LiftRootCondition.lean]
  risks: [inverse passage naturality, cast coherence, path composition direction, root indexing]
  unchecked: [C2 converse construction, arbitrary undirected named spanning tree bridge, A execution quotient, C3, D, E, fixed examples]
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: Every A1 lift is natural on all signed original named paths; its root values satisfy the C1 equations on every original edge loop and determine every fiber equivalence uniquely
  completion_candidate: no
  lean_artifacts: [renameSignedEdge, renameSigned, ReversibleData.RootSolutions, ReversibleData.Lift.toRootSolutions, ReversibleData.Lift.eq_of_root_fiber_eq]
  evidence: [ReversibleData.Lift.signed_edge_naturality, ReversibleData.Lift.signed_path_naturality, ReversibleData.Lift.toRootSolutions, ReversibleData.Lift.eq_of_root_fiber_eq]
  claim_mapping:
    theorem_names: [ReversibleData.Lift.toRootSolutions, ReversibleData.Lift.eq_of_root_fiber_eq]
    source_labels: [C1 forward implication, C2 root evaluation injectivity]
    conjuncts: [original positive edge names, inverse edge passages, all signed paths, every component root, all original edge loops, uniqueness of a lift from root values]
    undischarged_assumptions: [constructing a lift from each C1 solution, arbitrary undirected tree orientation bridge, terminating finite-table decision procedure]
    acceptance_point: C1 is necessary for an actual lift and root evaluation is injective; surjectivity and the full C1/C2 bijection remain open
    port_status: unported
audits:
  premise_delta:
    discharged: [A1 edge square extends to signed paths, necessary C1 equations, root-value uniqueness]
    remaining: [C2 sufficiency and inverse laws, undirected-tree bridge, A quotient semantics, C3 through E, fixed examples]
  certificate_provenance:
    discharged: [RootSolutions is populated from each actual Lift by root evaluation]
    unresolved: [existence of Lift from an arbitrary RootSolutions value]
  proof_use:
    used: [A1 edge_naturality in positive passage case, inverse equivalence in negative case, path induction, root loops, root paths]
    unused: [finite input and path equations because this C1 direction applies to arbitrary reversible named operations]
  structure_field_escape: none-found-for-the-necessary-condition
  route_integrity: pass-for-C1-forward
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [focused Lean check and axiom audit to be recorded in PR]
  blocking_findings: []
  next_obligation: Construct the inverse from any C1 RootSolutions using C2 and prove the full bijection
```

## Cycle 11 selection / proposed result

```yaml
ledger_type: target_cycle_result
goal: G-127-aat-reversible-protocol-holonomy
cycle: 11
goal_blob_sha: 86ed6948771755a19db802e01e42dbd00a8f9abf
base_oid: 15c65c63b10d8055b7188deb06698809b1f12efd
tracking_issue: 4981
report_path: research/reports/G-127-aat-reversible-protocol-holonomy.md
selection:
  proof_state_ref: Issue #4981 Cycle 10 proof state and LiftRootCondition
  proof_dag_predecessors: [RootSolutions, signed_path_naturality, Lift.eq_of_root_fiber_eq, RootedPaths.edgeLoopAt]
  proof_obligation: Construct C2 from every C1 root solution, prove A1 on all original named edges, and close both inverse laws
  selection_reason: Completes the C1/C2 classification needed to characterize the visible lift image in C3
  expected_result_type: proof-checkpoint
  lean_targets: [ResearchLean/AG/ProtocolHolonomy/LiftRootReconstruction.lean]
  risks: [transport composition order, named inverse passages, dependent root indexing, target root distinct from chosen root]
  unchecked: [arbitrary undirected named spanning-tree bridge, A execution quotient, C3, D, E, fixed examples]
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: Renaming respects signed path composition and reversal; C2 reconstructs every vertex fiber from a C1 root solution; the root loop equations imply all A1 original-edge squares; root evaluation and reconstruction form an equivalence
  completion_candidate: no
  lean_artifacts: [renameSigned_comp, renameSigned_reverse, ReversibleData.RootSolutions.reconstructedFiber, ReversibleData.RootSolutions.toLift, ReversibleData.liftEquivRootSolutions]
  evidence: [ReversibleData.RootSolutions.reconstructed_edge_naturality, ReversibleData.RootSolutions.reconstructedFiber_root, ReversibleData.RootSolutions.toLift_toRootSolutions, ReversibleData.Lift.toRootSolutions_toLift]
  claim_mapping:
    theorem_names: [ReversibleData.liftEquivRootSolutions]
    source_labels: [C1 C2 full root-solution lift classification]
    conjuncts: [all components, each original named edge loop, arbitrary visible graph automorphism, target fiber at g of selected root, C2 vertex formula, A1 for every named edge, both inverse laws]
    undischarged_assumptions: [arbitrary undirected named-tree orientation bridge, terminating finite-table C1 solver]
    acceptance_point: For any RootedPaths family from original signed named edges, C1 root solutions are equivalent to actual A1 lifts; C3 image and torsor remain open
    port_status: unported
audits:
  premise_delta:
    discharged: [C1 sufficiency, C2 formula, A1 preservation, both inverses]
    remaining: [undirected-tree bridge, A execution quotient, C3, D, E, fixed examples]
  certificate_provenance:
    discharged: [every RootSolutions value yields a genuine Lift through root equation calculations]
    unresolved: [finite-table decision and explicit witness]
  proof_use:
    used: [C1 edge_holonomy in square_of_root_equation, original edgeEquiv and renamedEdgeEquiv, signed path composition/reversal, root path normalization, accepted Cycle 10 injectivity]
    unused: [finite input and path equations because this structural classification applies to any reversible named operation table]
  structure_field_escape: none-found-for-C1-C2
  route_integrity: pass-for-rooted-paths
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [focused Lean check and axiom audit to be recorded in PR]
  blocking_findings: []
  next_obligation: Define H_lift as the actual projection image and prove C3 with the fiber torsor
```

## Cycle 12 selection / proposed result

```yaml
ledger_type: target_cycle_result
goal: G-127-aat-reversible-protocol-holonomy
cycle: 12
goal_blob_sha: 86ed6948771755a19db802e01e42dbd00a8f9abf
base_oid: 778b1c3864d7b00e2a2947c5b74ba75b4997a9fc
tracking_issue: 4981
report_path: research/reports/G-127-aat-reversible-protocol-holonomy.md
selection:
  proof_state_ref: Issue #4981 Cycle 11 proof state and liftEquivRootSolutions
  proof_dag_predecessors: [ChangeGroup.projection, liftEquivStateChangeOver, liftMulEquivVerticalStateGroup, liftEquivRootSolutions]
  proof_obligation: Identify H_lift with the actual projection image and prove C3's short exact sequence with the original vertical lift group
  selection_reason: Establishes the visible-image and exactness clauses before the fiber torsor action
  expected_result_type: proof-checkpoint
  lean_targets: [ResearchLean/AG/ProtocolHolonomy/LiftableVisible.lean]
  risks: [dependent visible subgroup membership, kernel identification, group law compatibility, exactness direction]
  unchecked: [C3 right torsor on every lift fiber, arbitrary undirected named-tree bridge, A execution quotient, D, E, fixed examples]
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: H_lift is the range of the actual visible projection and membership is equivalent to nonempty actual Lift and nonempty C1 RootSolutions; projection restricted to H_lift is surjective; its kernel is group-isomorphic to the original vertical A1 lift group, yielding C3 short exactness
  completion_candidate: no
  lean_artifacts: [ReversibleData.LiftableVisible, ReversibleData.projectionToLiftable, ReversibleData.verticalLiftEquivLiftableKernel, ReversibleData.verticalLiftInclusion]
  evidence: [ReversibleData.mem_liftableVisible_iff_lift, ReversibleData.mem_liftableVisible_iff_rootSolutions, ReversibleData.projectionToLiftable_surjective, ReversibleData.projectionToLiftable_ker, ReversibleData.liftable_shortExact]
  claim_mapping:
    theorem_names: [ReversibleData.mem_liftableVisible_iff_rootSolutions, ReversibleData.liftable_shortExact]
    source_labels: [C3 H_lift definition and short exact sequence]
    conjuncts: [actual H subgroup, actual projection image, C1 solution equivalence, vertical Aut_Q(F), actual A_F, injective inclusion, exactness at A_F, surjectivity to H_lift]
    undischarged_assumptions: [right-kernel free and transitive action on each Lift_F(u), arbitrary undirected named-tree orientation bridge, finite decision procedure]
    acceptance_point: C3 image and exactness hold for the actual change group; the torsor clause remains open
    port_status: unported
audits:
  premise_delta:
    discharged: [H_lift subgroup from actual image, C1 membership iff liftability, vertical kernel identification, C3 exactness]
    remaining: [C3 torsor, undirected-tree bridge, A quotient semantics, D, E, fixed examples]
  certificate_provenance:
    discharged: [C1 solution to actual lift via Cycle 11, kernel iso from actual total-state changes]
    unresolved: [finite-table solver and fiber torsor identification]
  proof_use:
    used: [C1/C2 equivalence in visible image theorem, actual StateChange and ChangeGroup projection, vertical Lift group iso, literal kernel inclusion]
    unused: [finite input and Π because image/exactness are structural group statements]
  structure_field_escape: none-found
  route_integrity: pass-for-image-and-exactness
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [focused Lean check and axiom audit to be recorded in PR]
  blocking_findings: []
  next_obligation: Prove right action of Aut_Q(F) on each Lift_F(u) is free and transitive with fiber formula
```

## Cycle 13 selection / proposed result

```yaml
ledger_type: target_cycle_result
goal: G-127-aat-reversible-protocol-holonomy
cycle: 13
goal_blob_sha: 86ed6948771755a19db802e01e42dbd00a8f9abf
base_oid: 83f009a5ca6e0ef733b0613b3e15b9dfc6c59654
tracking_issue: 4981
report_path: research/reports/G-127-aat-reversible-protocol-holonomy.md
selection:
  proof_state_ref: Issue #4981 Cycle 12 proof state and liftable_shortExact
  proof_dag_predecessors: [liftEquivStateChangeOver, verticalLiftEquivLiftableKernel, projectionToLiftable, liftable_shortExact]
  proof_obligation: Prove the C3 right Aut_Q(F) action on every Lift_F(u) is free and transitive and has the specified fiber formula
  selection_reason: Closes the torsor clause after the actual image and short exact sequence
  expected_result_type: proof-checkpoint
  lean_targets: [ResearchLean/AG/ProtocolHolonomy/LiftFiberTorsor.lean]
  risks: [right versus left action order, opposite kernel group, actual change group fiber versus original Lift fiber, dependent fiber formula]
  unchecked: [arbitrary undirected named-tree bridge, A execution quotient, D, E, fixed examples]
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: Literal right multiplication by the actual projection kernel acts freely and transitively on every actual projection fiber; the fiber is equivalent to the original Lift type; transporting the action through the accepted vertical group isomorphism gives a right Aut_Q(F) action with identity/composition laws, unique displacement, and the requested vertexwise formula
  completion_candidate: no
  lean_artifacts: [ReversibleData.LiftableFiber, ReversibleData.liftEquivLiftableFiber, ReversibleData.liftRightAction, ReversibleData.verticalRightAction]
  evidence: [ReversibleData.liftableFiber_action_free, ReversibleData.liftableFiber_action_transitive, ReversibleData.liftRightAction_one, ReversibleData.liftRightAction_mul, ReversibleData.verticalRightAction_one, ReversibleData.verticalRightAction_mul, ReversibleData.verticalRightAction_existsUnique, ReversibleData.verticalRightAction_fiber_apply, ReversibleData.verticalRightAction_displacement_fiber]
  claim_mapping:
    theorem_names: [ReversibleData.verticalRightAction_existsUnique, ReversibleData.verticalRightAction_fiber_apply]
    source_labels: [C3 right torsor and formula]
    conjuncts: [every liftable visible u, original Lift_F(u), original vertical Aut_Q(F), right action law, free and transitive, unique vertical displacement, each vertex/state formula φ_v after α_v]
    undischarged_assumptions: [arbitrary undirected named-tree bridge, A execution quotient, terminating finite-table solver]
    acceptance_point: C1/C2 and all C3 structural clauses hold using original changes; GOAL still requires A completion, B tree bridge, D, E, and fixed examples
    port_status: unported
audits:
  premise_delta:
    discharged: [C3 right action, free and transitive law, fiber formula]
    remaining: [undirected-tree bridge, A quotient semantics, D, E, fixed examples]
  certificate_provenance:
    discharged: [fiber action from literal actual ChangeGroup product, vertical input from original Lift 1 via group iso]
    unresolved: [finite-table witness and solver]
  proof_use:
    used: [actual projection fiber, actual kernel, C3 kernel iso, StateChange multiplication, A2 fiber formula]
    unused: [finite input and path equations because torsor is structural]
  structure_field_escape: none-found
  route_integrity: pass-for-actual-fiber
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [focused Lean check and axiom audit to be recorded in PR]
  blocking_findings: []
  next_obligation: Prove arbitrary undirected named spanning-tree orientation bridge or A execution quotient semantics
```

## Cycle 14 selection / proposed result

```yaml
ledger_type: target_cycle_result
goal: G-127-aat-reversible-protocol-holonomy
cycle: 14
goal_blob_sha: 86ed6948771755a19db802e01e42dbd00a8f9abf
base_oid: e4204a39aa9c52dccf1265ebaa14c21b3660ab84
tracking_issue: 4981
report_path: research/reports/G-127-aat-reversible-protocol-holonomy.md
selection:
  proof_state_ref: Issue #4981 Cycle 13 and the accepted B2/C1-C2 declarations
  proof_dag_predecessors: [verticalRootMulEquiv, liftEquivRootSolutions, vertical_transport_naturality, Lift.signed_path_naturality]
  proof_obligation: Construct coherent root and chosen-path coordinate changes with the actual conjugation formulas in D
  selection_reason: The same original vertical changes and lifts underlie all B2 and C1 presentations; making the transition maps explicit reduces the D compatibility proof distance
  expected_result_type: proof-checkpoint
  lean_targets: [ResearchLean/AG/ProtocolHolonomy/ChoiceChange.lean]
  risks: [conjugation direction, renamed target path, preservation of original A1 family, arbitrary root and tree choices]
  unchecked: [holonomy subgroup conjugacy, A2/projection/kernel/torsor compatibility, undirected-tree bridge, A quotient semantics, D identity specialization, E, fixed examples]
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: For any two RootedPaths choices, the B2 group coordinates and C1 solution coordinates are changed through the original A1 changes; direct and successive transitions coincide, reconstruction yields the identical original fiber family, and each new root value obeys the actual old-to-new transport conjugation formula
  completion_candidate: no
  lean_artifacts: [ReversibleData.verticalChoiceChange, ReversibleData.liftChoiceChange, ReversibleData.oldRootToNewRoot]
  evidence: [ReversibleData.verticalChoiceChange_comp, ReversibleData.liftChoiceChange_comp, ReversibleData.verticalChoiceChange_reconstruct, ReversibleData.liftChoiceChange_reconstruct, ReversibleData.verticalChoiceChange_root_formula, ReversibleData.liftChoiceChange_root_formula]
  claim_mapping:
    theorem_names: [ReversibleData.verticalChoiceChange_root_formula, ReversibleData.liftChoiceChange_root_formula]
    source_labels: [D root and tree change]
    conjuncts: [arbitrary normalized root/path choices, original named signed path between roots, vertical transport conjugation, renamed lift transport formula, coherent successive changes, unchanged original fiber maps]
    undischarged_assumptions: [holonomy subgroup conjugacy, arbitrary undirected named-tree bridge, remaining D compatibilities, A quotient semantics, E finite construction and two fixed examples]
    acceptance_point: A genuine D coordinate-change construction and formulas are proved; the full D clause and G-127 completion remain open
    port_status: unported
audits:
  premise_delta:
    discharged: [coordinate transitions for arbitrary RootedPaths choices and explicit root transport formulas]
    remaining: [holonomy conjugacy, A2/projection/kernel/torsor compatibility, semantic and identity-specialization clauses, E and examples]
  certificate_provenance:
    discharged: [choice changes derived from original Lift and vertical group, path transport derived from original named edges]
    unresolved: [arbitrary undirected-tree orientation bridge and E executable forest]
  proof_use:
    used: [B2 group equivalence, C1/C2 lift equivalence, actual signed-path naturality]
    unused: [finite equations and H because coordinate changes apply to each original lift]
  structure_field_escape: none-found
  route_integrity: pass-for-rooted-paths
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [focused Lean check and axiom audit to be recorded in PR]
  blocking_findings: []
  next_obligation: Construct A execution quotient realization from the original finite input and then finish D compatibility and conjugacy
```

## Cycle 15 selection / proposed result

```yaml
ledger_type: target_cycle_result
goal: G-127-aat-reversible-protocol-holonomy
cycle: 15
goal_blob_sha: 86ed6948771755a19db802e01e42dbd00a8f9abf
base_oid: 72ab35169118d26af5e2d9ade015fbde41d31a44
tracking_issue: 4981
report_path: research/reports/G-127-aat-reversible-protocol-holonomy.md
selection:
  proof_state_ref: Issue #4981 Cycle 14 and PathEquations primitive input
  proof_dag_predecessors: [FiniteProtocolInput.satisfies, ReversibleData.positiveTransport, ProtocolSchema.pathFunctorOfEdgeAction, ProtocolRealization]
  proof_obligation: Construct the independent quotient execution realization from every original finite reversible protocol input, preserving all named edges and original positive-path actions
  selection_reason: Discharges the construction half of D's independent semantics from the exact A input without restricting the vertex, edge, or fiber universes
  expected_result_type: proof-checkpoint
  lean_targets: [ResearchLean/AG/ProtocolHolonomy/ProtocolConnection.lean]
  risks: [three universe levels, original edge names through ULift, relation descent from original Pi, one-point observation, quotient path readback]
  unchecked: [visible rename descent and A1 natural-isomorphism correspondence, D other clauses, undirected-tree bridge, E, fixed examples]
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: The original finite vertices, named edges, equation indices, and fibers are embedded via ULift; the original edge actions generate a free-path functor, original Pi validity proves quotient descent, and a ProtocolRealization with singleton observation is constructed; original named-edge and every original positive-path action are read back exactly
  completion_candidate: no
  lean_artifacts: [FiniteProtocolInput.schema, FiniteProtocolInput.pathFunctor, FiniteProtocolInput.executionFunctor, FiniteProtocolInput.singletonObservation, FiniteProtocolInput.realization]
  evidence: [FiniteProtocolInput.pathFunctor_map_up, FiniteProtocolInput.pathFunctor_relation, FiniteProtocolInput.realization_edgeAction_down, FiniteProtocolInput.realization_pathAction_down]
  claim_mapping:
    theorem_names: [FiniteProtocolInput.realization, FiniteProtocolInput.realization_edgeAction_down, FiniteProtocolInput.realization_pathAction_down]
    source_labels: [A primitive input, D independent protocol semantics]
    conjuncts: [arbitrary three-universe original finite input, exact original named edges, exact original Pi, quotient execution category, finite state carriers, singleton observation, original edge and directed-path actions]
    undischarged_assumptions: [visible-renaming quotient descent, natural-isomorphism correspondence, D remaining clauses, E algorithm, fixed examples]
    acceptance_point: The execution realization is built from the primitive input, while the change/natural-isomorphism correspondence and full target remain open
    port_status: unported
audits:
  premise_delta:
    discharged: [D realization construction and original edge/path action readback]
    remaining: [visible renaming and natural isomorphism, root/tree bridge and D compatibilities, E, fixed examples]
  certificate_provenance:
    discharged: [schema and functor constructed from P rather than supplied, relation proof from P.satisfies, observation from actual singleton]
    unresolved: [visible rename and executable finite tables]
  proof_use:
    used: [P.finiteVertex, P.finiteEdge, P.finiteFiber, P.equations, P.satisfies, P.data.edgeEquiv, quotient lift]
    unused: [P.H and renaming_preserves because no visible change is constructed in this cycle]
  structure_field_escape: none-found
  route_integrity: pass-for-original-execution-realization
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [focused Lean check and 16-declaration standard axiom audit to be recorded in PR]
  blocking_findings: []
  next_obligation: Descend each selected visible renaming through Pi and identify A1 lifts with natural isomorphisms of the independent realization
```

## Cycle 16 selection / proposed result

```yaml
ledger_type: target_cycle_result
goal: G-127-aat-reversible-protocol-holonomy
cycle: 16
goal_blob_sha: 86ed6948771755a19db802e01e42dbd00a8f9abf
base_oid: 4ec1cab76d5d19767edd8e2cb06bf68bc35afdb5
tracking_issue: 4981
report_path: research/reports/G-127-aat-reversible-protocol-holonomy.md
selection:
  proof_state_ref: Issue #4981 Cycle 15 quotient realization and PathEquations visible congruence preservation
  proof_dag_predecessors: [FiniteProtocolInput.schema, PathEquations.Congruent, FiniteProtocolInput.visible_preserves_congruence, ProtocolSchema.ExecutionCategory]
  proof_obligation: Descend every selected visible graph automorphism from its original named-edge action to the quotient execution category
  selection_reason: Uses the remaining H congruence-preservation input in the independent semantic bridge and enables the subsequent A1-natural-isomorphism equivalence
  expected_result_type: proof-checkpoint
  lean_targets: [ResearchLean/AG/ProtocolHolonomy/VisibleRename.lean]
  risks: [equation congruence versus quotient relation, endpoint-dependent names, path composition, actual use of H membership]
  unchecked: [visible functor inverse/composition laws, A1-natural-isomorphism equivalence, D other clauses, undirected-tree bridge, E, fixed examples]
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: Every original generated congruence consequence is sound in the independent quotient; H membership supplies preservation of its generating equations, constructing a rename functor on all quotient executions; its map on any original path is precisely the original named-edge rename
  completion_candidate: no
  lean_artifacts: [FiniteProtocolInput.renamePrefunctor, FiniteProtocolInput.renamePathFunctor, FiniteProtocolInput.renameExecutionFunctor]
  evidence: [FiniteProtocolInput.congruent_sound, FiniteProtocolInput.renamePath_up, FiniteProtocolInput.renamePathFunctor_relation, FiniteProtocolInput.renameExecutionFunctor_map_up]
  claim_mapping:
    theorem_names: [FiniteProtocolInput.renameExecutionFunctor, FiniteProtocolInput.renameExecutionFunctor_map_up]
    source_labels: [A congruence-preserving H, D visible execution renaming]
    conjuncts: [every g in original H, original vertex and named-edge maps, generated Pi congruence, quotient descent, all original positive-path rename evaluation]
    undischarged_assumptions: [functor group laws and equivalence, A1 natural-isomorphism correspondence, D other clauses, E and fixed examples]
    acceptance_point: The visible rename genuinely descends from the original H condition, but the full D semantics and G-127 completion remain open
    port_status: unported
audits:
  premise_delta:
    discharged: [H congruence-preservation used for quotient rename descent]
    remaining: [rename functor inverse/composition, A1 natural isomorphism, D other clauses, E and examples]
  certificate_provenance:
    discharged: [rename functor from original graph maps; relation preservation from P.renaming_preserves via generated congruence soundness]
    unresolved: [independent natural-isomorphism correspondence and finite solver]
  proof_use:
    used: [P.H membership, P.renaming_preserves, original vertex and edge actions, original Pi and quotient soundness]
    unused: [P.data.edgeEquiv because quotient rename is a schema-side construction]
  structure_field_escape: none-found
  route_integrity: pass-for-quotient-rename
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [focused Lean check and nine-declaration standard axiom audit to be recorded in PR]
  blocking_findings: []
  next_obligation: Identify original A1 lifts with natural isomorphisms from realization to its visible rename, including all quotient-path naturality
```

## Cycle 17 selection / proposed result

```yaml
ledger_type: target_cycle_result
goal: G-127-aat-reversible-protocol-holonomy
cycle: 17
goal_blob_sha: 86ed6948771755a19db802e01e42dbd00a8f9abf
base_oid: f647644febc1a9b843f7ff0e2ba1cf8542ad3b2f
tracking_issue: 4981
report_path: research/reports/G-127-aat-reversible-protocol-holonomy.md
selection:
  proof_state_ref: Issue #4981 Cycle 16 quotient rename and Cycle 15 independent realization
  proof_dag_predecessors: [FiniteProtocolInput.realization, FiniteProtocolInput.renameExecutionFunctor, ReversibleData.Lift, ProtocolRealization.ext, ProtocolRealization.res]
  proof_obligation: Construct and invert the correspondence between every original A1 lift and natural isomorphisms from the independent realization to its quotient-execution rename
  selection_reason: Closes the central D semantic comparison without accepting any completed natural transformation as input to the forward direction
  expected_result_type: proof-checkpoint
  lean_targets: [ResearchLean/AG/ProtocolHolonomy/NaturalIsomorphism.lean]
  risks: [inverse edge square, all quotient-execution naturality, dependent vertex fibers, actual observation, two inverse laws]
  unchecked: [semantic compatibility with A2/projection/kernel/torsor, rename functor group laws, D other clauses, undirected-tree bridge, E, fixed examples]
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: Each original A1 lift yields generator maps in both directions, a full observation-preserving natural isomorphism on the quotient execution category, and an inverse restriction from any such semantic isomorphism; both inverse laws retain the original vertex equivalences and full natural transformations
  completion_candidate: no
  lean_artifacts: [FiniteProtocolInput.renamedRealization, FiniteProtocolInput.liftGeneratorMap, FiniteProtocolInput.liftInverseGeneratorMap, FiniteProtocolInput.liftIso, FiniteProtocolInput.isoToLift, FiniteProtocolInput.liftEquivSemanticIso]
  evidence: [FiniteProtocolInput.renamed_edgeAction_down, FiniteProtocolInput.isoToLift_liftIso, FiniteProtocolInput.liftIso_isoToLift, ProtocolRealization.ext]
  claim_mapping:
    theorem_names: [FiniteProtocolInput.liftEquivSemanticIso]
    source_labels: [D independent semantics correspondence]
    conjuncts: [every selected g in original H, original A1 Lift, original quotient execution realization, actual renamed realization, vertexwise map preservation, all quotient-path naturality, observation preservation, both inverse laws]
    undischarged_assumptions: [semantic A2/projection/kernel/torsor compatibility, rename functor group laws, D other clauses, E, fixed examples]
    acceptance_point: D's bidirectional lift/natural-isomorphism comparison is proved; its cross-fiber compatibility and the full G-127 target remain open
    port_status: unported
audits:
  premise_delta:
    discharged: [A1 to semantic natural isomorphism and reverse restriction, all quotient-path naturality]
    remaining: [semantic group and torsor compatibility, D other clauses, E and fixed examples]
  certificate_provenance:
    discharged: [forward semantic isomorphism from original Lift A1, inverse map from actual isomorphism components and inverse laws]
    unresolved: [finite-table witness and executable solver]
  proof_use:
    used: [A1 named-edge condition, inverse A1 square, ProtocolRealization.ext path and quotient induction, semantic isomorphism laws, singleton observation]
    unused: [B/C holonomy because semantic equivalence is constructed directly from A]
  structure_field_escape: none-found
  route_integrity: pass-for-semantic-isomorphism
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [focused Lean check and eleven-declaration standard axiom audit to be recorded in PR]
  blocking_findings: []
  next_obligation: Prove semantic A2 composition, projection, kernel, and fiber/torsor compatibility using the bidirectional correspondence
```

## Cycle 18 selection / proposed result

```yaml
ledger_type: target_cycle_result
goal: G-127-aat-reversible-protocol-holonomy
cycle: 18
goal_blob_sha: 86ed6948771755a19db802e01e42dbd00a8f9abf
base_oid: 9e75f32b3f993e700c12257f951e6c12cc5a7797
tracking_issue: 4981
report_path: research/reports/G-127-aat-reversible-protocol-holonomy.md
selection:
  proof_state_ref: Issue #4981 Cycle 14 root coordinates and accepted B1 root-loop group equality
  proof_dag_predecessors: [holonomy_eq_rootedLoopTransportGroup, transport_comp, transport_reverse, oldRootToNewRoot]
  proof_obligation: Prove that changing component roots conjugates the complete table-generated holonomy subgroups by original named-path transport
  selection_reason: Closes the remaining holonomy-group assertion of D root change rather than only changing centralizer and C1 coordinates
  expected_result_type: proof-checkpoint
  lean_targets: [ResearchLean/AG/ProtocolHolonomy/HolonomyChoice.lean]
  risks: [group multiplication orientation, different root fiber types, both membership directions, arbitrary signed named connecting path]
  unchecked: [arbitrary undirected-tree bridge, D semantic and identity compatibilities, E, fixed examples]
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: Transport along any original signed named path between chosen roots induces a permutation-group isomorphism; its conjugation maps table-generated holonomy membership equivalently in both directions, including the path used in the D coordinate change
  completion_candidate: no
  lean_artifacts: [ReversibleData.permutationConjugation, ReversibleData.rootLoopTransport_conjugate_mem]
  evidence: [ReversibleData.holonomy_change_iff, ReversibleData.holonomy_choice_iff]
  claim_mapping:
    theorem_names: [ReversibleData.holonomy_change_iff, ReversibleData.holonomy_choice_iff]
    source_labels: [D root and tree change, B1 original table holonomy]
    conjuncts: [arbitrary two rooted-path choices, any signed named root-to-root path, original operation transport, full table-generated holonomy on both root fibers, conjugation in both directions]
    undischarged_assumptions: [arbitrary undirected named-tree bridge, D semantic and identity compatibility, E and fixed examples]
    acceptance_point: D's holonomy conjugacy follows from accepted B1 equality and original named-path transport; G-127 remains incomplete
    port_status: unported
audits:
  premise_delta:
    discharged: [holonomy subgroup conjugacy for any chosen roots]
    remaining: [undirected-tree bridge, D semantic and identity compatibility, E and fixed examples]
  certificate_provenance:
    discharged: [conjugating equivalence from original D.transport of named path; subgroup equality from B1]
    unresolved: [E finite table construction]
  proof_use:
    used: [B1 equality with all rooted signed-loop transports, actual path reversal and composition, both root choices]
    unused: [Pi/H because holonomy concerns original reversible operation tables]
  structure_field_escape: none-found
  route_integrity: pass-for-rooted-paths
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [focused Lean check and four-declaration standard axiom audit to be recorded in PR]
  blocking_findings: []
  next_obligation: Prove remaining D semantic composition and torsor compatibility or arbitrary undirected named-tree orientation bridge
```

## Cycle 19 selection / proposed result

```yaml
ledger_type: target_cycle_result
goal: G-127-aat-reversible-protocol-holonomy
cycle: 19
goal_blob_sha: 86ed6948771755a19db802e01e42dbd00a8f9abf
base_oid: 9bafc64b23312a09684d140ec7adc24a1aba0960
tracking_issue: 4981
report_path: research/reports/G-127-aat-reversible-protocol-holonomy.md
selection:
  proof_state_ref: Issue #4981 Cycles 14 and 18 choice changes and Cycle 12 original vertical right action
  proof_dag_predecessors: [liftChoiceChange_reconstruct, verticalChoiceChange_reconstruct, verticalRightAction_fiber_apply, RootSolutions.toLift_toRootSolutions]
  proof_obligation: Prove that changing roots and trees preserves the original right torsor action on C1 lift coordinates, with the actual root-fiber composition formula
  selection_reason: Connects D root-change coordinates to C's literal group action instead of only preserving individual lifts
  expected_result_type: proof-checkpoint
  lean_targets: [ResearchLean/AG/ProtocolHolonomy/ChoiceTorsor.lean]
  risks: [right-action composition order, root-value evaluation, action provenance through the original state-change group, arbitrary roots]
  unchecked: [D A2/projection/kernel and semantic compatibility, identity specialization, arbitrary undirected-tree bridge, E, fixed examples]
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: C1 root solutions inherit the original right action by actual vertical A1 lifts; its root value is phi_root composed after alpha_root, and arbitrary coordinate change preserves the action while changing centralizer coordinates
  completion_candidate: no
  lean_artifacts: [ReversibleData.rootRightAction, ReversibleData.rootRightAction_rootFiber]
  evidence: [ReversibleData.liftChoiceChange_rootRightAction]
  claim_mapping:
    theorem_names: [ReversibleData.rootRightAction_rootFiber, ReversibleData.liftChoiceChange_rootRightAction]
    source_labels: [C3 right torsor, D root and tree choice compatibility]
    conjuncts: [original liftable visible g, original right action via actual change group, arbitrary rooted choices, changed B2/C1 coordinates, root-fiber right composition]
    undischarged_assumptions: [remaining D A2/projection/kernel and semantic compatibility, identity specialization, arbitrary undirected named-tree bridge, E and fixed examples]
    acceptance_point: The original right action and D coordinate change commute for every liftable g; full G-127 remains incomplete
    port_status: unported
audits:
  premise_delta:
    discharged: [D root-coordinate compatibility with the original C3 right action]
    remaining: [D other compatibilities and specialization, undirected-tree bridge, E and fixed examples]
  certificate_provenance:
    discharged: [root solutions reconstruct an original A1 lift; centralizers reconstruct an original vertical lift; action is the original right group action]
    unresolved: [E finite table construction]
  proof_use:
    used: [C1/C2 reconstruction equivalence, B2 vertical reconstruction, literal verticalRightAction, both choice-change reconstruction equalities]
    unused: [Pi because this action clause concerns original A1 data]
  structure_field_escape: none-found
  route_integrity: pass-for-rooted-paths
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [focused Lean check and three-declaration standard axiom audit to be recorded in PR]
  blocking_findings: []
  next_obligation: Prove D A2/projection/kernel compatibility with presentation changes or semantic isomorphism composition
```

## Cycle 20 selection / proposed result

```yaml
ledger_type: target_cycle_result
goal: G-127-aat-reversible-protocol-holonomy
cycle: 20
goal_blob_sha: 86ed6948771755a19db802e01e42dbd00a8f9abf
base_oid: 9d5d82f685618ee45c9d3b15f044c0efc564d9a0
tracking_issue: 4981
report_path: research/reports/G-127-aat-reversible-protocol-holonomy.md
selection:
  proof_state_ref: Issue #4981 Cycles 14 and 19 root-coordinate changes and A2 original pair group
  proof_dag_predecessors: [liftPairMulEquivChangeGroup, liftPair_mul_fiber_apply, liftEquivRootSolutions, liftChoiceChange, verticalChoiceChange]
  proof_obligation: Preserve the original A2 group law, visible projection, and literal kernel under arbitrary changes of C1 root coordinates
  selection_reason: Connects coordinate changes to the complete original change group and projection, extending the prior individual-lift and right-action compatibility
  expected_result_type: proof-checkpoint
  lean_targets: [ResearchLean/AG/ProtocolHolonomy/ChoiceGroup.lean]
  risks: [dependent visible fiber, transported group provenance, projection/kernel equality, agreement with earlier C1 choice map]
  unchecked: [explicit root-coordinate A2 point formula, D semantic composition, identity specialization, arbitrary undirected-tree bridge, E, fixed examples]
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: Root-pair coordinates are group-isomorphic to the original A2 lift-pair group; changing arbitrary roots is a group isomorphism whose fiber map is the prior C1 change, and it preserves visible projection and actual kernel membership
  completion_candidate: no
  lean_artifacts: [ReversibleData.RootPair, ReversibleData.liftPairEquivRootPair, ReversibleData.liftPairMulEquivRootPair, ReversibleData.rootPairProjection]
  evidence: [ReversibleData.rootPairChoiceChange, ReversibleData.rootPairChoiceChange_projection, ReversibleData.rootPairChoiceChange_fiber, ReversibleData.rootPairChoiceChange_mem_ker_iff]
  claim_mapping:
    theorem_names: [ReversibleData.liftPairMulEquivRootPair, ReversibleData.rootPairChoiceChange_projection, ReversibleData.rootPairChoiceChange_mem_ker_iff]
    source_labels: [A2 original pair group, D root and tree choice compatibility]
    conjuncts: [original H and A1 lift pairs, actual A2 group law, all C1 root solutions, arbitrary rooted choices, original visible projection, literal projection kernel, changed fiber value]
    undischarged_assumptions: [explicit coordinate A2 point formula, remaining D semantic/identity compatibility, undirected named-tree bridge, E and fixed examples]
    acceptance_point: Group/projection/kernel compatibility of D root presentations follows through the original A2 group, but remaining D/E/example obligations keep G-127 incomplete
    port_status: unported
audits:
  premise_delta:
    discharged: [D root-choice group law, projection, and kernel compatibility]
    remaining: [explicit root-coordinate A2 point formula, D semantic/identity compatibility, undirected-tree bridge, E and fixed examples]
  certificate_provenance:
    discharged: [root solution reconstruction into original A1 lift; original A2 group law from actual state-change composition]
    unresolved: [E finite table construction]
  proof_use:
    used: [C1/C2 lift equivalence, original LiftPair group, original projection, prior choice changes]
    unused: [Pi because the group-coordinate clause concerns original A1 data]
  structure_field_escape: none-found
  route_integrity: pass-for-rooted-paths
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [focused Lean check and seven-declaration standard axiom audit to be recorded in PR]
  blocking_findings: []
  next_obligation: Prove the explicit root-coordinate A2 evaluation formula or semantic isomorphism composition
```

## Cycle 21 selection / proposed result

```yaml
ledger_type: target_cycle_result
goal: G-127-aat-reversible-protocol-holonomy
cycle: 21
goal_blob_sha: 86ed6948771755a19db802e01e42dbd00a8f9abf
base_oid: c84b90104690271c41960c9219be36a1329aca2c
tracking_issue: 4981
report_path: research/reports/G-127-aat-reversible-protocol-holonomy.md
selection:
  proof_state_ref: Issue #4981 Cycle 20 group isomorphism and original A2 fiber law
  proof_dag_predecessors: [liftPair_mul_fiber_apply, liftPairEquivRootPair, RootSolutions.reconstructedFiber_root]
  proof_obligation: Compute the actual A2 multiplication of two arbitrary C1 root pairs at each component root, including the moved-vertex index
  selection_reason: Supplies the pointwise formula explicitly left open by Cycle 20 and prevents a transported group isomorphism from replacing the original fiber evaluation
  expected_result_type: proof-checkpoint
  lean_targets: [ResearchLean/AG/ProtocolHolonomy/ChoiceGroupFormula.lean]
  risks: [dependent target fiber, composition order, selected-root reconstruction, conflating root values with full lift]
  unchecked: [D semantic composition and identity specialization, arbitrary undirected-tree bridge, E, fixed examples]
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: At every original component root, multiplication of arbitrary C1 root pairs evaluates as the first reconstructed lift at the vertex moved by the second visible change, applied to the second root value, exactly the original A2 equation
  completion_candidate: no
  lean_artifacts: [ReversibleData.rootPair_mul_rootFiber]
  evidence: [ReversibleData.liftPair_mul_fiber_apply, ReversibleData.RootSolutions.reconstructedFiber_root]
  claim_mapping:
    theorem_names: [ReversibleData.rootPair_mul_rootFiber]
    source_labels: [A2, D root and tree change composition compatibility]
    conjuncts: [arbitrary two visible changes and C1 solutions, every component root and root fiber element, original shifted vertex, actual A2 composition]
    undischarged_assumptions: [D semantic composition and identity specialization, arbitrary undirected named-tree bridge, E and fixed examples]
    acceptance_point: Actual A2's dependent root evaluation is explicit for the accepted RootPair group, while full G-127 remains incomplete
    port_status: unported
audits:
  premise_delta:
    discharged: [D explicit A2 root-coordinate point formula]
    remaining: [D semantic/identity compatibility, undirected-tree bridge, E and fixed examples]
  certificate_provenance:
    discharged: [original LiftPair multiplication from StateChange, root values from C1/C2 reconstruction]
    unresolved: [E finite table construction]
  proof_use:
    used: [original A2 dependent fiber formula, C1/C2 reconstructed root equation, Cycle 20 root group definition]
    unused: [Pi because the group-coordinate clause concerns original A1 data]
  structure_field_escape: none-found
  route_integrity: pass-for-rooted-paths
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [focused Lean check and one-declaration standard axiom audit to be recorded in PR]
  blocking_findings: []
  next_obligation: Prove D semantic isomorphism composition and projection/kernel/fiber compatibility
```

## Cycle 22 selection / proposed result

```yaml
ledger_type: target_cycle_result
goal: G-127-aat-reversible-protocol-holonomy
cycle: 22
goal_blob_sha: 86ed6948771755a19db802e01e42dbd00a8f9abf
base_oid: f92d494c77528d4f6a1b922f0e95056d0b68903c
tracking_issue: 4981
report_path: research/reports/G-127-aat-reversible-protocol-holonomy.md
selection:
  proof_state_ref: Issue #4981 Cycle 16 quotient rename and Cycle 17 semantic natural isomorphism
  proof_dag_predecessors: [FiniteProtocolInput.renameExecutionFunctor, FiniteProtocolInput.renamePathFunctor_relation, FixedFGraphAutomorphism group law]
  proof_obligation: Prove that the original H action on the complete independent quotient execution category respects identity, composition, and inverse visible renaming
  selection_reason: Supplies the actual semantic reindexing group laws needed to compare the A2 composition of original lifts with composed semantic natural isomorphisms
  expected_result_type: proof-checkpoint
  lean_targets: [ResearchLean/AG/ProtocolHolonomy/RenameComposition.lean]
  risks: [functor composition order, quotient morphisms beyond generators, named edge preservation, inverse membership in H]
  unchecked: [D semantic natural-isomorphism A2/projection/kernel/fiber compatibility, identity specialization, arbitrary undirected-tree bridge, E, fixed examples]
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: The quotient execution rename functors generated from the original named graph action satisfy exact composition and identity laws on every quotient morphism; inverse visible changes give two-sided inverse functors
  completion_candidate: no
  lean_artifacts: [renameTypedEdge_mul, renamePositive_mul, FiniteProtocolInput.renamePath_mul, FiniteProtocolInput.renamePath_one]
  evidence: [FiniteProtocolInput.renameExecutionFunctor_mul, FiniteProtocolInput.renameExecutionFunctor_one, FiniteProtocolInput.renameExecutionFunctor_inv_right, FiniteProtocolInput.renameExecutionFunctor_inv_left]
  claim_mapping:
    theorem_names: [FiniteProtocolInput.renameExecutionFunctor_mul, FiniteProtocolInput.renameExecutionFunctor_one, FiniteProtocolInput.renameExecutionFunctor_inv_right, FiniteProtocolInput.renameExecutionFunctor_inv_left]
    source_labels: [D independent semantics reindexing and composition]
    conjuncts: [original H automorphisms, original vertex and named edge actions, congruence-preserving quotient descent, every quotient execution, product order, identity and both inverse laws]
    undischarged_assumptions: [D semantic natural-isomorphism composition/projection/kernel/fiber, identity specialization, arbitrary undirected named-tree bridge, E and fixed examples]
    acceptance_point: Reindexing is proved as a genuine quotient-execution group action; natural-isomorphism compatibility and full G-127 remain open
    port_status: unported
audits:
  premise_delta:
    discharged: [D semantic execution reindexing group laws on the full quotient]
    remaining: [D natural-isomorphism group/fiber compatibility and identity specialization, undirected-tree bridge, E and fixed examples]
  certificate_provenance:
    discharged: [renaming from original vertex and named-edge automorphisms; quotient descent from original H congruence-preservation]
    unresolved: [E finite table construction]
  proof_use:
    used: [original graph automorphism product, named edge and path rename, quotient induction on every execution, previous congruence preservation]
    unused: [fiber operation values because reindexing concerns execution names]
  structure_field_escape: none-found
  route_integrity: pass-for-quotient-execution-reindexing
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [focused Lean check and nine-declaration standard axiom audit to be recorded in PR]
  blocking_findings: []
  next_obligation: Prove D semantic natural-isomorphism composition using this reindexing law and the original A2 lift law
```

## Cycle 23 selection / proposed result

```yaml
ledger_type: target_cycle_result
goal: G-127-aat-reversible-protocol-holonomy
cycle: 23
goal_blob_sha: 86ed6948771755a19db802e01e42dbd00a8f9abf
base_oid: 3dd337b66796cc111e1eaeb7eac37dd53c7193fd
tracking_issue: 4981
report_path: research/reports/G-127-aat-reversible-protocol-holonomy.md
selection:
  proof_state_ref: Issue #4981 Cycles 17 and 22 semantic natural isomorphisms and quotient rename group law
  proof_dag_predecessors: [FiniteProtocolInput.liftIso, FiniteProtocolInput.renameExecutionFunctor_mul, ReversibleData.Lift.comp_fiber_apply]
  proof_obligation: Show the independently constructed semantic natural isomorphism of an original A2 product equals the reindexed composite of the two original semantic natural isomorphisms on every quotient execution
  selection_reason: Connects D's semantic correspondence to the original A2 composition beyond vertex generator maps
  expected_result_type: proof-checkpoint
  lean_targets: [ResearchLean/AG/ProtocolHolonomy/SemanticComposition.lean]
  risks: [reindexing order, functor target equality, natural transformation on all quotient objects, dependent moved vertex]
  unchecked: [D semantic projection/kernel/fiber action compatibility, identity specialization, arbitrary undirected-tree bridge, E, fixed examples]
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: The semantic target of a product equals iterated quotient rename, and the full natural transformation from the original A2 lift is exactly the composite of the second semantic lift with the first semantic lift whiskered by the second visible rename
  completion_candidate: no
  lean_artifacts: [FiniteProtocolInput.renamedFunctor_mul, FiniteProtocolInput.liftIsoSemanticComposite]
  evidence: [FiniteProtocolInput.liftIso_comp_vertex, FiniteProtocolInput.liftIsoSemanticComposite_eq]
  claim_mapping:
    theorem_names: [FiniteProtocolInput.liftIsoSemanticComposite_eq]
    source_labels: [A2, D independent semantic correspondence and composition]
    conjuncts: [original input P and H, arbitrary two visible changes and A1 lifts, actual quotient-execution reindexing, full natural transformations, original A2 fiber law, all quotient-path naturality]
    undischarged_assumptions: [D semantic projection/kernel/fiber compatibility, identity specialization, arbitrary undirected named-tree bridge, E and fixed examples]
    acceptance_point: Semantic natural-isomorphism composition is equal to the original A2 lift image as a full natural transformation; full G-127 remains incomplete
    port_status: unported
audits:
  premise_delta:
    discharged: [D semantic correspondence respects original A2 composition on all quotient executions]
    remaining: [D semantic projection/kernel/fiber and identity specialization, undirected-tree bridge, E and fixed examples]
  certificate_provenance:
    discharged: [semantic isomorphisms from original A1 lifts; quotient rename product from original H; A2 product from actual state changes]
    unresolved: [E finite table construction]
  proof_use:
    used: [original A2 dependent fiber formula, genuine semantic natural isomorphisms, quotient rename group law, functor whiskering and natural-transformation equality]
    unused: [B/C because semantic A2 correspondence follows directly from original A]
  structure_field_escape: none-found
  route_integrity: pass-for-semantic-A2
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [focused Lean check and four-declaration standard axiom audit to be recorded in PR]
  blocking_findings: []
  next_obligation: Prove D semantic projection/kernel/each-fiber right-action compatibility
```

## Cycle 24 selection / proposed result

```yaml
ledger_type: target_cycle_result
goal: G-127-aat-reversible-protocol-holonomy
cycle: 24
goal_blob_sha: 86ed6948771755a19db802e01e42dbd00a8f9abf
base_oid: f941a7a6da72a66a788d44eea31fdeb2665a4e23
tracking_issue: 4981
report_path: research/reports/G-127-aat-reversible-protocol-holonomy.md
selection:
  proof_state_ref: Issue #4981 Cycles 17 and 23 full semantic natural isomorphism equivalence and A2 composition
  proof_dag_predecessors: [FiniteProtocolInput.liftEquivSemanticIso, FiniteProtocolInput.liftIsoSemanticComposite_eq, ReversibleData.liftPairMulEquivChangeGroup, ReversibleData.liftPairProjection]
  proof_obligation: Identify the complete group of original visible changes paired with independent semantic natural isomorphisms, including its original visible projection and literal kernel
  selection_reason: Connects semantic A2 composition to the original change-group projection and kernel rather than leaving the semantic correspondence fiberwise only
  expected_result_type: proof-checkpoint
  lean_targets: [ResearchLean/AG/ProtocolHolonomy/SemanticGroup.lean]
  risks: [dependent renamed target, supplied semantic group law, original projection preservation, kernel substitution]
  unchecked: [semantic each-fiber right torsor action, D identity specialization, arbitrary undirected-tree bridge, E, fixed examples]
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: Original A1 lift pairs and full independent semantic isomorphism pairs are group-isomorphic; multiplication of arbitrary semantic pairs has the actual reindexed natural-isomorphism composite as hom; the semantic projection is the original visible projection, and its literal kernel membership is exactly original identity-visible pair membership
  completion_candidate: no
  lean_artifacts: [FiniteProtocolInput.SemanticIsoPair, FiniteProtocolInput.liftPairEquivSemanticPair, FiniteProtocolInput.liftPairMulEquivSemanticPair, FiniteProtocolInput.semanticPairProjection]
  evidence: [FiniteProtocolInput.semanticPair_mul_toNatTrans, FiniteProtocolInput.semanticPair_mul_composite, FiniteProtocolInput.semanticPairProjection_apply, FiniteProtocolInput.semanticPair_mem_ker_iff, FiniteProtocolInput.liftPairEquivSemanticPair_mem_ker_iff]
  claim_mapping:
    theorem_names: [FiniteProtocolInput.liftPairMulEquivSemanticPair, FiniteProtocolInput.semanticPair_mul_composite, FiniteProtocolInput.liftPairEquivSemanticPair_mem_ker_iff]
    source_labels: [A2, C3 original projection and kernel, D independent semantic projection/kernel compatibility]
    conjuncts: [original H and all its A1 lifts, full semantic isomorphisms, original actual A2 group, reindexed natural-isomorphism composite on arbitrary semantic pairs, original visible projection, literal projection kernel, bidirectional correspondence]
    undischarged_assumptions: [semantic fiber right-action compatibility, D identity specialization, arbitrary undirected named-tree bridge, E and fixed examples]
    acceptance_point: The semantic group/projection/kernel all descend from and return to the original A1/A2 change group; G-127 remains incomplete
    port_status: unported
audits:
  premise_delta:
    discharged: [D semantic group and reindexed composition, visible projection, and literal kernel compatibility]
    remaining: [D semantic each-fiber right action and identity specialization, undirected-tree bridge, E and fixed examples]
  certificate_provenance:
    discharged: [semantic isomorphisms from original A1 lifts and inverse by vertex restriction; group law from original StateChange group]
    unresolved: [E finite table construction]
  proof_use:
    used: [Cycle 17 semantic iso equivalence, original LiftPair group and projection, Cycle 23 semantic A2 natural-transformation composition]
    unused: [B/C because semantic correspondence follows directly from original A]
  structure_field_escape: none-found
  route_integrity: pass-for-semantic-group
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [focused Lean check and eight-declaration standard axiom audit to be recorded in PR]
  blocking_findings: []
  next_obligation: Prove semantic each-fiber right torsor action compatibility
```

## Cycle 25 selection / proposed result

```yaml
ledger_type: target_cycle_result
goal: G-127-aat-reversible-protocol-holonomy
cycle: 25
goal_blob_sha: 86ed6948771755a19db802e01e42dbd00a8f9abf
base_oid: 2a207e26c
tracking_issue: 4981
report_path: research/reports/G-127-aat-reversible-protocol-holonomy.md
selection:
  proof_state_ref: Issue #4981 Cycle 24 original A2 semantic group/composition checkpoint
  proof_dag_predecessors: [FiniteProtocolInput.liftEquivSemanticIso, FiniteProtocolInput.semanticPair_mul_composite, ReversibleData.verticalRightAction_existsUnique, ReversibleData.verticalRightAction_fiber_apply]
  proof_obligation: Preserve C3's original right vertical torsor action on every D semantic isomorphism fiber, including its pointwise fiber formula
  selection_reason: Completes the remaining semantic action compatibility of D using the original vertical group and all actual natural isomorphisms
  expected_result_type: proof-checkpoint
  lean_targets: [ResearchLean/AG/ProtocolHolonomy/SemanticFiberTorsor.lean]
  risks: [replacing original vertical group, selected iso rather than whole fiber, reversing right action, merely transported formula]
  unchecked: [D identity specialization, arbitrary undirected named-tree bridge, E, fixed examples]
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: Every liftable visible semantic isomorphism fiber carries the original vertical group's free transitive right action, and each vertex component is literal right composition of the original fiber maps
  completion_candidate: no
  lean_artifacts: [FiniteProtocolInput.semanticVerticalRightAction]
  evidence: [FiniteProtocolInput.semanticVerticalRightAction_one, FiniteProtocolInput.semanticVerticalRightAction_mul, FiniteProtocolInput.semanticVerticalRightAction_free, FiniteProtocolInput.semanticVerticalRightAction_transitive, FiniteProtocolInput.semanticVerticalRightAction_fiber_apply]
  claim_mapping:
    theorem_names: [FiniteProtocolInput.semanticVerticalRightAction_free, FiniteProtocolInput.semanticVerticalRightAction_transitive, FiniteProtocolInput.semanticVerticalRightAction_fiber_apply]
    source_labels: [C3 original right action, D independent semantic each-fiber action compatibility]
    conjuncts: [original vertical group, every liftable visible fiber, all semantic isomorphisms, right action laws, free and transitive, literal pointwise fiber formula]
    undischarged_assumptions: [D identity specialization, arbitrary undirected named-tree bridge, E and fixed examples]
    acceptance_point: D semantic action is a genuine right torsor with C3's same original vertical maps; G-127 remains incomplete
    port_status: unported
audits:
  premise_delta:
    discharged: [D semantic each-fiber right action compatibility]
    remaining: [D identity specialization, undirected-tree bridge, E and fixed examples]
  certificate_provenance:
    discharged: [all semantic isomorphisms from independent quotient realization and inverse by vertex restriction, original vertical group through C3 actual state-change kernel]
    unresolved: [E finite table construction]
  proof_use:
    used: [Cycle 17 full semantic iso equivalence, C3 original vertical right action and torsor]
    unused: [Cycle 24 semantic group presentation and B/C coordinates because semantic fiber action follows directly from original A1 and C3]
  structure_field_escape: none-found
  route_integrity: pass-for-semantic-action
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [focused Lean check and six-declaration standard axiom audit to be recorded in PR]
```

## Cycle 26 selection / proposed result

```yaml
ledger_type: target_cycle_result
goal: G-127-aat-reversible-protocol-holonomy
cycle: 26
goal_blob_sha: 86ed6948771755a19db802e01e42dbd00a8f9abf
base_oid: 0df72d2f3
tracking_issue: 4981
report_path: research/reports/G-127-aat-reversible-protocol-holonomy.md
selection:
  proof_state_ref: Issue #4981 Cycle 25 completed D semantic fiber-action checkpoint
  proof_dag_predecessors: [ReversibleData.transport, ReversibleData.transport_edgeLoopAt, ReversibleData.holonomy_eq_rootedLoopTransportGroup]
  proof_obligation: For the original A-side identity-operation data with arbitrary named graph and common fiber K, all signed transports and B1 holonomy are trivial for every root choice
  selection_reason: Establishes the starting calculation of D's arbitrary identity-operation specialization directly on the original named input
  expected_result_type: proof-checkpoint
  lean_targets: [ResearchLean/AG/ProtocolHolonomy/IdentityTransport.lean]
  risks: [assuming holonomy trivial as input, omitting reverse named passages, fixing a special graph or root]
  unchecked: [D identity H_lift, component classification, section, FixedF/G-124 comparison, arbitrary undirected named-tree bridge, E, fixed examples]
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: Identity operations on any original named graph have identity signed-path transport, identity B1 edge generators, and bottom holonomy for every root-path choice
  completion_candidate: no
  lean_artifacts: [identityReversibleData]
  evidence: [identity_signedEdgeEquiv, identity_transport, identity_edgeMonodromyAt, identity_holonomy]
  claim_mapping:
    theorem_names: [identity_transport, identity_edgeMonodromyAt, identity_holonomy]
    source_labels: [D arbitrary identity-operation specialization, B1 original named-edge monodromy]
    conjuncts: [original edge names, both signed orientations, all signed paths, every component and root choice, actual holonomy subgroup]
    undischarged_assumptions: [D identity H_lift/component/section/FixedF/G-124, arbitrary undirected named-tree bridge, E and fixed examples]
    acceptance_point: The identity specialization calculates transport and holonomy from edge actions rather than supplying either as a premise; G-127 remains incomplete
    port_status: unported
audits:
  premise_delta:
    discharged: [D identity signed transports and holonomy triviality]
    remaining: [D identity H_lift and group classification, section and FixedF/G-124 comparison, undirected-tree bridge, E and fixed examples]
  certificate_provenance:
    discharged: [identity edgeEquiv on the original named graph, induction on signed paths, B1 actual named-loop transport]
    unresolved: [E finite table construction]
  proof_use:
    used: [A-side reversible primitive data, signed transport recursion, B1 named-loop and holonomy equality]
    unused: [semantic presentation because this calculation is on the original A input]
  structure_field_escape: none-found
  route_integrity: pass-for-identity-transport
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [focused Lean check and five-declaration standard axiom audit to be recorded in PR]
```

## Cycle 49 selection / proposed result

```yaml
ledger_type: target_cycle_result
goal: G-127-aat-reversible-protocol-holonomy
cycle: 49
goal_blob_sha: 86ed6948771755a19db802e01e42dbd00a8f9abf
base_oid: 7b68a4fdb977dc5455a2f15641867a904d16a5b8
tracking_issue: 4981
report_path: research/reports/G-127-aat-reversible-protocol-holonomy.md
selection:
  proof_state_ref: Issue #4981 Cycle 48 conditional B2 search with supplied component equality
  proof_dag_predecessors: [fixedFDirectedEdgeStep, FixedFUndirectedReachable, fixedFComponentSetoid, ExplicitEnumeration.toFintype]
  proof_obligation: Derive a terminating equality decision for the original component quotient from explicit original vertex and edge tables, including loops and parallel edges
  selection_reason: Removes a runtime premise of Cycle 48 and supplies the component membership test needed by B2 and forest construction
  expected_result_type: proof-obligation-discharged
  lean_targets: [ResearchLean/AG/ProtocolHolonomy/FiniteComponents.lean]
  risks: [replacing original component relation, losing loops/parallel names in the source, noncomputable equality oracle, failure on empty graph]
  unchecked: [input-generated executable named forest/root paths, all-component B2 assembly, H_lift/torsor finite output, fixed examples]
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: A finite simple adjacency from original edge endpoints has reachability exactly equal to the existing EqvGen component relation; bounded walks and explicit vertex/edge enumerations compute decidable equality on the original quotient
  completion_candidate: no
  lean_artifacts: [finiteReachabilityGraph, finiteReachable_iff_original, finiteAdjDecidable, finiteComponentDecidableEq]
  evidence: [finiteReachable_iff_original, finiteComponentDecidableEq, executable connected and disconnected Bool evaluations]
  claim_mapping:
    theorem_names: [finiteReachable_iff_original, finiteComponentDecidableEq]
    source_labels: [E original finite graph component construction]
    conjuncts: [original endpoint relation, symmetric closure, finite bounded-walk decision, original quotient equality]
    undischarged_assumptions: [explicit vertex/edge lists and their GOAL E equality decisions are inputs; finite named forest paths remain]
    acceptance_point: Input-generated decidable equality on the exact original component quotient, not yet a named forest/root-path algorithm
    port_status: unported
audits:
  premise_delta:
    discharged: [component equality decision from original finite vertex/edge tables]
    remaining: [executable named forest/root paths, all-component B2/E construction and examples]
  certificate_provenance:
    discharged: [finite adjacency searches original edge list; bounded-walk theorem supplies reachability decision; equivalence to existing EqvGen transports decision to quotient]
    unresolved: [named edge and signed path witnesses for executable root paths]
  proof_use:
    used: [explicit vertex and edge enumerations, original fixedFDirectedEdgeStep, both directions of reachability equivalence, Quotient.decidableEq]
    unused: [B2/C1 solvers are downstream users; no root paths constructed here]
  structure_field_escape: none-found
  route_integrity: pass-for-original-component-equality
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [focused Lean check and four-declaration standard axiom audit to be recorded in PR; #eval connected true and disconnected false]
```

## Cycle 50 selection / proposed result

```yaml
ledger_type: target_cycle_result
goal: G-127-aat-reversible-protocol-holonomy
cycle: 50
goal_blob_sha: 86ed6948771755a19db802e01e42dbd00a8f9abf
base_oid: 9380bfb4d3326b35d111a0ee10b39ea2c3bfbbb9
tracking_issue: 4981
report_path: research/reports/G-127-aat-reversible-protocol-holonomy.md
selection:
  proof_state_ref: Issue #4981 Cycle 49 input-generated original component decision and open executable named root paths
  proof_dag_predecessors: [finiteReachabilityGraph, finiteReachable_iff_original, SignedPath, ExplicitEnumeration.complete]
  proof_obligation: Resolve each bounded-walk adjacency into an original named edge and signed orientation by finite edge-list search, then compute a SignedPath for any finite graph walk
  selection_reason: Supplies name-preserving executable path conversion needed after bounded-walk selection and before constructing roots/forest
  expected_result_type: proof-obligation-discharged
  lean_targets: [ResearchLean/AG/ProtocolHolonomy/FiniteNamedWalks.lean]
  risks: [Classical.choose extraction of edge name, collapsed parallel names, missing reverse orientation, proof-only recursor that cannot execute]
  unchecked: [finite bounded-walk selection from roots, executable named forest and root paths, all-component B2/E assembly, H_lift/torsor output, fixed examples]
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: Every adjacency of the finite simple reachability graph is resolved by an explicit scan of the original named edge list; structurally recursive walk conversion concatenates these signed passages into the exact original SignedPath type
  completion_candidate: no
  lean_artifacts: [signedStepCandidate, signedEdgeOfAdj, signedPathOfFiniteWalk]
  evidence: [signedStepCandidate_ne_none_of_pos, signedStepCandidate_ne_none_of_neg, signedEdgeOfAdj, executable forward/reverse one-edge Bool evaluations]
  claim_mapping:
    theorem_names: [signedEdgeOfAdj, signedPathOfFiniteWalk]
    source_labels: [B original signed named paths, E finite named path construction]
    conjuncts: [original edge-list witness, positive and negative traversal, names retained in SignedPath, total computed conversion]
    undischarged_assumptions: [complete finite edge list and decidable vertex equality are GOAL E input; bounded root walk/forest construction remains]
    acceptance_point: Computable name-preserving conversion from finite graph walk to original signed path, not yet root path or spanning forest generation
    port_status: unported
audits:
  premise_delta:
    discharged: [original named-edge resolution and executable signed path conversion for a supplied finite graph walk]
    remaining: [select bounded root walks and a consistent named spanning forest, all-component E assembly and examples]
  certificate_provenance:
    discharged: [adjacency forces an original edge witness; complete edge list and findSome search compute an actual named edge, including inverse traversal]
    unresolved: [runtime selection of the finite walk and common tree paths]
  proof_use:
    used: [both adjacency orientations, explicit edge enumeration completeness, structural walk recursion, original SignedPath constructors]
    unused: [component decision supplies future reachability test but is not needed for converting a supplied walk]
  structure_field_escape: none-found
  route_integrity: pass-for-original-named-path-conversion
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [focused Lean check and five-declaration standard axiom audit to be recorded in PR; #eval forward and reverse length one, plus selected original edge false with forward and reverse tags]
```

## Cycle 51 selection / proposed result

```yaml
ledger_type: target_cycle_result
goal: G-127-aat-reversible-protocol-holonomy
cycle: 51
goal_blob_sha: 86ed6948771755a19db802e01e42dbd00a8f9abf
base_oid: 0e8f38cb1e8a1dfa6b9a8dfc4eac36f19485dc14
tracking_issue: 4981
report_path: research/reports/G-127-aat-reversible-protocol-holonomy.md
selection:
  proof_state_ref: Issue #4981 Cycle 50 finite-walk-to-original-named-path conversion and open bounded walk selection
  proof_dag_predecessors: [finiteComponentDecidableEq, finiteReachable_iff_original, signedPathOfFiniteWalk, SimpleGraph.Reachable.elim_path]
  proof_obligation: From complete original finite vertex and edge lists, terminate with a named SignedPath for connected endpoints and none for disconnected endpoints, using bounded explicit walk enumeration
  selection_reason: Removes the supplied-walk premise of Cycle 50 and provides pairwise executable original named paths needed for rooted paths and forest construction
  expected_result_type: proof-obligation-discharged
  lean_targets: [ResearchLean/AG/ProtocolHolonomy/FiniteNamedPaths.lean]
  risks: [noncomputable Finset.toList or Classical.choose path selection, incomplete walk bound, decidability supplied by an oracle, untyped or unnamed output]
  unchecked: [consistent named spanning forest and RootedPaths from pairwise paths, all-component B2/E assembly, H_lift/torsor output, fixed examples]
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: Structural List recursion enumerates every walk of a fixed length from explicit vertex/edge tables; a simple path has length below the vertex count, so bounded walk enumeration contains one whenever the original component relation holds; the first list path converts to original SignedPath, while component equality decides none exactly on disconnected endpoints
  completion_candidate: no
  lean_artifacts: [finiteWalksExact, finiteBoundedWalks, finiteNamedPathOfReachable, findFiniteNamedPath]
  evidence: [mem_finiteWalksExact, findFiniteNamedPath_isSome_iff, executable connected some one-step and disconnected none evaluations]
  claim_mapping:
    theorem_names: [mem_finiteWalksExact, finiteNamedPathOfReachable, findFiniteNamedPath_isSome_iff]
    source_labels: [B original signed named paths, E finite graph path construction]
    conjuncts: [finite vertex/edge enumeration, complete fixed-length walks, bounded reachable witness, named signed output, success and failure exactness]
    undischarged_assumptions: [GOAL E explicit finite tables and equality decisions are inputs; consistent named spanning forest and component roots remain]
    acceptance_point: Pairwise input-generated named path decision is exact; it does not yet select a common tree or root for each component
    port_status: unported
audits:
  premise_delta:
    discharged: [bounded finite walk selection and pairwise original named SignedPath decision]
    remaining: [input-generated genuine named spanning forest and RootedPaths, all-component E assembly and examples]
  certificate_provenance:
    discharged: [all walks enumerated from explicit vertex and original adjacency tables, finite path-length bound from Mathlib, returned edge names selected by Cycle 50 list scan]
    unresolved: [common root/tree selection and selected-edge acyclicity]
  proof_use:
    used: [component decision from Cycle 49, complete finiteWalksExact, simple path bound, original signedPathOfFiniteWalk]
    unused: [supplied RootedPaths from earlier B/C modules; pairwise paths need later forest organization]
  structure_field_escape: none-found
  route_integrity: pass-for-pairwise-original-named-path-decision
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [focused Lean check and six-declaration standard axiom audit to be recorded in PR; #eval connected true and some one-step, disconnected false]
```

## Cycle 52 selection / proposed result

```yaml
ledger_type: target_cycle_result
goal: G-127-aat-reversible-protocol-holonomy
cycle: 52
goal_blob_sha: 86ed6948771755a19db802e01e42dbd00a8f9abf
base_oid: a9db1b8d031b5def80a5fe8c0659516f8c83d99a
tracking_issue: 4981
report_path: research/reports/G-127-aat-reversible-protocol-holonomy.md
selection:
  proof_state_ref: Issue #4981 Cycle 51 pairwise input-generated named path decision and open RootedPaths provenance
  proof_dag_predecessors: [finiteComponentDecidableEq, finiteNamedPathOfReachable, RootedPaths, ReversibleData.findRootLift_isSome_iff]
  proof_obligation: From original finite vertex/edge tables, choose one root per original component and normalized original named paths to all vertices, then run the simultaneous C1 lift decision without supplied root paths
  selection_reason: Removes the supplied RootedPaths premise from the C1 procedure, directly shrinking E's input-generated construction gap
  expected_result_type: proof-checkpoint
  lean_targets: [ResearchLean/AG/ProtocolHolonomy/FiniteRootedPaths.lean]
  risks: [Quotient.out used as runtime root, disconnected or empty graph failure, nonempty path oracle, claiming a spanning forest from arbitrary pairwise paths]
  unchecked: [genuine named spanning forest and proof that root paths use its selected edges, all-component B2/E assembly, H_lift/torsor output, fixed examples]
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: First matching original vertex in each component is selected from the explicit list; bounded pairwise path search supplies normalized root paths, yielding actual RootedPaths. The C1 finite root search now runs on that input-generated data and succeeds exactly when an original Lift exists
  completion_candidate: no
  lean_artifacts: [finiteRootForComponent, finitePathFromRoot, finiteRootedPaths, ReversibleData.findFiniteRootLift]
  evidence: [finitePathFromRoot_self, ReversibleData.findFiniteRootLift_isSome_iff, executable root false/path length one/C1 search true evaluations]
  claim_mapping:
    theorem_names: [finiteRootedPaths, ReversibleData.findFiniteRootLift_isSome_iff]
    source_labels: [B chosen roots and original named paths, C1/C2, E input-generated finite lift decision]
    conjuncts: [all original components including disconnected/empty graph, root representative from finite list, named path from same tables, root nil normalization, C1 decision exact for original A1]
    undischarged_assumptions: [GOAL E explicit finite tables/equality decisions are inputs; genuine named spanning forest and all-component B2/E output remain]
    acceptance_point: Input-generated RootedPaths and C1 lift decision are exact, but chosen paths have not been organized into one named spanning forest as GOAL B/E demand
    port_status: unported
audits:
  premise_delta:
    discharged: [finite component roots and original named RootedPaths from original tables, C1 solver's formerly supplied-root premise]
    remaining: [genuine finite named spanning forest, all-component B2 and H_lift/torsor output, fixed examples]
  certificate_provenance:
    discharged: [filtered explicit vertex list computes roots; Cycle 51 bounded path search computes root paths; Cycle 47 C1 search consumes this exact RootedPaths]
    unresolved: [selected-edge tree structure and acyclicity for the same paths]
  proof_use:
    used: [input-generated component decision, complete vertex list, normalized finite named path, original findRootLift_isSome_iff]
    unused: [UndirectedNamedSpanningForest predicate remains an independent forest proof obligation]
  structure_field_escape: none-found-for-generated-RootedPaths
  route_integrity: pass-for-input-generated-C1-route-without-forest
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [focused Lean check and six-declaration standard axiom audit to be recorded in PR; #eval root false, path length one, C1 search true]
```

## Cycle 53 selection / proposed result

```yaml
ledger_type: target_cycle_result
goal: G-127-aat-reversible-protocol-holonomy
cycle: 53
goal_blob_sha: 86ed6948771755a19db802e01e42dbd00a8f9abf
base_oid: 23db4aa08dae7340c01153d70c3cc9c001da78b9
tracking_issue: 4981
report_path: research/reports/G-127-aat-reversible-protocol-holonomy.md
selection:
  proof_state_ref: Issue #4981 Cycle 52 input-generated C1 decision and open finite visible-image computation
  proof_dag_predecessors: [ReversibleData.findFiniteRootLift_isSome_iff, ReversibleData.mem_liftableVisible_iff_lift, ExplicitEnumeration]
  proof_obligation: Enumerate exactly H_lift from a complete finite list of original visible changes by running the input-generated simultaneous C1 decision for every member, retaining a genuine A1 lift on success
  selection_reason: Extends the exact per-visible-change finite C1 solver to the actual C3 image without a supplied liftability predicate or certificate
  expected_result_type: proof-checkpoint
  lean_targets: [ResearchLean/AG/ProtocolHolonomy/FiniteLiftableVisible.lean]
  risks: [assuming the selected list already contains only liftable changes, testing only sample changes, confusing existence with a section, claiming all lifts from one witness]
  unchecked: [genuine named spanning forest, all-component B2 assembly, full torsor output, fixed examples]
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: Filter the complete original H list by the input-generated C1 search; list membership is equivalent to the original projection range H_lift, and each accepted member has a returned original A1 lift
  completion_candidate: no
  lean_artifacts: [ReversibleData.finiteLiftableVisible]
  evidence: [ReversibleData.mem_finiteLiftableVisible_iff, ReversibleData.finiteLiftableVisible_lift_iff]
  claim_mapping:
    theorem_names: [ReversibleData.mem_finiteLiftableVisible_iff, ReversibleData.finiteLiftableVisible_lift_iff]
    source_labels: [C1/C3 visible image and E finite H_lift decision]
    conjuncts: [every original H element via explicit complete list, simultaneous C1 computation, exact original projection image, actual A1 witness on success]
    undischarged_assumptions: [the GOAL E finite visible list and original finite graph/fiber tables are inputs; no forest or all-lift output is claimed]
    acceptance_point: Exact finite enumeration of H_lift through the original C1 route, conditional only on E's stipulated finite input tables; full E remains open
    port_status: unported
audits:
  premise_delta:
    discharged: [complete finite visible-image scan and exact C3 subgroup membership decision]
    remaining: [genuine finite named spanning forest, all-component B2 and torsor output, fixed examples]
  certificate_provenance:
    discharged: [every visible candidate is drawn from the supplied complete H table; input-generated named roots feed the C1 search; accepted results carry original A1 lifts]
    unresolved: [forest structure for the chosen paths]
  proof_use:
    used: [complete H enumeration, findFiniteRootLift_isSome_iff, actual mem_liftableVisible_iff_lift]
    unused: [direct A1 search and a supplied H_lift certificate]
  structure_field_escape: none-found-for-finite-visible-scan
  route_integrity: pass-for-C1-to-original-H_lift
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [focused Lean check and three-declaration standard axiom audit to be recorded in PR]
```

## Cycle 54 selection / proposed result

```yaml
ledger_type: target_cycle_result
goal: G-127-aat-reversible-protocol-holonomy
cycle: 54
goal_blob_sha: 86ed6948771755a19db802e01e42dbd00a8f9abf
base_oid: 88404f86ae7d4e50de3f6c338c51d81356e8e753
tracking_issue: 4981
report_path: research/reports/G-127-aat-reversible-protocol-holonomy.md
selection:
  proof_state_ref: Issue #4981 Cycle 48 per-component finite B2 centralizer list, Cycle 49 component decision, Cycle 52 generated roots
  proof_dag_predecessors: [finiteRootCentralizers, centralizer_mem_finiteRootCentralizers, finiteComponentDecidableEq, finiteRootedPaths, verticalRootEquiv]
  proof_obligation: From original finite graph/fiber tables, enumerate all original components, take the exhaustive B2 centralizer list at each root, and reconstruct every actual vertical A1 lift from the dependent product
  selection_reason: Closes the all-component assembly and connects finite B2 centralizers with original vertical changes rather than leaving separate component lists
  expected_result_type: proof-checkpoint
  lean_targets: [ResearchLean/AG/ProtocolHolonomy/FiniteVerticalLifts.lean]
  risks: [assuming a supplied component enumeration, omitting disconnected or empty components, mapping centralizer tuples without original A1 reconstruction, claiming all nonvertical lifts]
  unchecked: [genuine named spanning forest, all-lifts torsor output, fixed examples]
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: The complete vertex list maps onto the original component quotient; componentwise finite B2 centralizers form a complete dependent-product enumeration, and B2 reconstruction maps that list onto every original A1 vertical lift
  completion_candidate: no
  lean_artifacts: [finiteComponentEnumeration, ReversibleData.finiteRootCentralizerFamilies, ReversibleData.finiteVerticalLifts]
  evidence: [finiteComponentEnumeration.complete, ReversibleData.finiteRootCentralizerFamilies.complete, ReversibleData.finiteVerticalLifts.complete]
  claim_mapping:
    theorem_names: [finiteComponentEnumeration, ReversibleData.finiteRootCentralizerFamilies, ReversibleData.finiteVerticalLifts]
    source_labels: [B2 all-component centralizer product and E finite vertical reconstruction]
    conjuncts: [original component quotient, every component including disconnected and empty graph, each named-edge B1 centralizer condition, actual B2 inverse, complete original vertical A1 lift list]
    undischarged_assumptions: [E explicit finite tables/equality decisions are inputs; generated root paths are not yet proven to form a named forest]
    acceptance_point: Complete finite B2 tuple and original vertical-lift enumeration from finite tables, without claiming the full nonvertical fiber or all E
    port_status: unported
audits:
  premise_delta:
    discharged: [all-component assembly of finite B2 centralizers and vertical A1 lift output]
    remaining: [genuine finite named spanning forest, all-lifts torsor output, fixed examples]
  certificate_provenance:
    discharged: [component indices generated from complete original vertex list; each centralizer generated from original named edge/fiber tables; RootedPaths generated from same graph tables; original Lift reconstructed through reviewed B2 equivalence]
    unresolved: [tree structure of generated root paths]
  proof_use:
    used: [Quotient.out only in list-completeness proof, finiteComponentDecidableEq at runtime, complete componentwise centralizer lists, verticalRootEvaluation/reconstructVertical inverse]
    unused: [noncomputable verticalRootMulEquiv group structure is not used to generate the list]
  structure_field_escape: none-found-for-vertical-list
  route_integrity: pass-for-B2-to-original-vertical-lifts
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [focused Lean check and three-declaration standard axiom audit to be recorded in PR]
```

## Cycle 55 selection / proposed result

```yaml
ledger_type: target_cycle_result
goal: G-127-aat-reversible-protocol-holonomy
cycle: 55
goal_blob_sha: 86ed6948771755a19db802e01e42dbd00a8f9abf
base_oid: cfd99e31b47413c0e1714423760dfbfcc03d243f
tracking_issue: 4981
report_path: research/reports/G-127-aat-reversible-protocol-holonomy.md
selection:
  proof_state_ref: Issue #4981 Cycle 53 exact H_lift and one C1 lift, Cycle 54 complete finite B2 vertical lift list, original C3 torsor
  proof_dag_predecessors: [findFiniteRootLift_isSome_iff, finiteVerticalLifts, verticalRightAction_transitive, verticalRightAction_fiber_apply]
  proof_obligation: For any original visible automorphism, compute the entire original A1 lift fiber by composing one input-generated C1 lift on the right with all finite B2 vertical lifts; prove the empty output exactly means no lift
  selection_reason: Connects the C1 existence route, B2 finite enumeration, and C3 torsor into E's full output for each visible change
  expected_result_type: proof-checkpoint
  lean_targets: [ResearchLean/AG/ProtocolHolonomy/FiniteAllLifts.lean]
  risks: [using noncomputable group action as the runtime enumerator, only returning one lift, mismatching A2 right action order, failing negative branch, claiming forest construction]
  unchecked: [genuine named spanning forest, two fixed examples, final cumulative A-E completion audit]
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: Pointwise right composition is defined constructively on the original A1 Lift and proved equal to the C3 right action; finite C1/B2 lists yield every original lift, and output is empty exactly when the original lift fiber is empty
  completion_candidate: no
  lean_artifacts: [ReversibleData.composeVertical, ReversibleData.finiteAllLifts]
  evidence: [ReversibleData.composeVertical_eq_rightAction, ReversibleData.mem_finiteAllLifts, ReversibleData.finiteAllLifts_eq_nil_iff]
  claim_mapping:
    theorem_names: [ReversibleData.composeVertical_eq_rightAction, ReversibleData.mem_finiteAllLifts, ReversibleData.finiteAllLifts_eq_nil_iff]
    source_labels: [A1/A2 pointwise composition, B2 vertical output, C3 right torsor, E full finite visible fiber]
    conjuncts: [original named-edge A1 equations, right order phi_v after alpha_v, C1 witness, every B2 vertical change, all original lifts, exact negative branch]
    undischarged_assumptions: [only GOAL E finite input tables/equality decisions; forest structure is not claimed]
    acceptance_point: Exact finite original A1 lift-fiber output via C1/B2/C3, while the named forest and fixed examples still prevent G-127 completion
    port_status: unported
audits:
  premise_delta:
    discharged: [full finite fiber enumeration and negative answer for every original visible change]
    remaining: [genuine finite original named forest and both fixed examples]
  certificate_provenance:
    discharged: [base lift computed by original simultaneous C1 search; every vertical lift generated by finite original B2 centralizer tables; final value built by pointwise A1 composition]
    unresolved: [tree structure of generated root paths]
  proof_use:
    used: [C1 isSome equivalence for negative branch, B2 vertical list completeness, C3 torsor transitivity, pointwise right-action equality]
    unused: [noncomputable C3 action is used only in proof of completeness, not in runtime output]
  structure_field_escape: none-found-for-full-fiber-list
  route_integrity: pass-for-C1-B2-C3-to-original-A1-output
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [focused Lean check and five-declaration standard axiom audit to be recorded in PR]
```

## Cycle 56 selection / proposed result

```yaml
ledger_type: target_cycle_result
goal: G-127-aat-reversible-protocol-holonomy
cycle: 56
goal_blob_sha: 86ed6948771755a19db802e01e42dbd00a8f9abf
base_oid: b55e8d7e2ecd74606c70d83d8969fcef845fbc3b
tracking_issue: 4981
report_path: research/reports/G-127-aat-reversible-protocol-holonomy.md
selection:
  proof_state_ref: Issue #4981 Cycle 55 full finite lift-fiber output and remaining genuine named-forest construction
  proof_dag_predecessors: [finiteReachabilityGraph, finiteReachable_iff_original, ExplicitEnumeration.toFintype]
  proof_obligation: For any finite subset of original named edges, compute exactly its undirected reachability relation and prove selecting the whole original edge table recovers the original component relation
  selection_reason: Supplies an executable exact selected-edge connectivity predicate for finite forest search and bridge testing without replacing the original graph quotient
  expected_result_type: proof-checkpoint
  lean_targets: [ResearchLean/AG/ProtocolHolonomy/FiniteSelectedConnectivity.lean]
  risks: [forgetting original edge names, identifying parallel edges in selection, loop or disconnected corner case, claiming a forest before bridge proof]
  unchecked: [candidate search and minimal selected-edge proof, genuine forest/root paths, fixed examples]
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: Selected named-edge reachability is exactly the equivalence closure of selected original directed steps, decidable by bounded walks over explicit finite vertex and selected-edge tables; selecting every original name reproduces the original undirected component relation
  completion_candidate: no
  lean_artifacts: [selectedNamedStep, SelectedNamedReachable, selectedReachabilityGraph, selectedReachableDecidable, allNamedEdges]
  evidence: [selectedReachable_iff_named, allNamedEdges_reachable_iff_original, selected-edge connected true/empty false evaluations]
  claim_mapping:
    theorem_names: [selectedReachable_iff_named, selectedReachableDecidable, allNamedEdges_reachable_iff_original]
    source_labels: [E finite named forest selected-edge connectivity]
    conjuncts: [original selected edge names, both orientations, loops, parallel edges, finite stopping decision, agreement with original components at full selection]
    undischarged_assumptions: [E finite original vertex/edge tables and equality decisions only; no forest or bridge is claimed]
    acceptance_point: Exact executable selected-edge connectivity test, not a completed spanning forest
    port_status: unported
audits:
  premise_delta:
    discharged: [finite exact connectivity decision for every selected original named-edge set]
    remaining: [finite candidate search, selected-edge bridge and connectedness proof, actual named forest/tree paths, fixed examples]
  certificate_provenance:
    discharged: [selection is a Finset of original Q.Edge names; adjacency and bounded walk derive only from those names; complete edge table recovers the original relation]
    unresolved: [forest selection and bridge proof]
  proof_use:
    used: [every selected original named edge in adjacency, finite vertex list for bounded reachability, original fixedFDirectedEdgeStep for full-set comparison]
    unused: [no supplied forest or external connectivity certificate]
  structure_field_escape: none-found-for-selected-reachability
  route_integrity: pass-for-original-selected-edge-decision
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [focused Lean check, eight-declaration standard axiom audit, selected true/empty false evaluations to be recorded in PR]
```

## Cycle 57 selection / proposed result

```yaml
ledger_type: target_cycle_result
goal: G-127-aat-reversible-protocol-holonomy
cycle: 57
goal_blob_sha: 86ed6948771755a19db802e01e42dbd00a8f9abf
base_oid: 9b3ee46438cca1fa45702056c4cd617ff735c2b9
tracking_issue: 4981
report_path: research/reports/G-127-aat-reversible-protocol-holonomy.md
selection:
  proof_state_ref: Issue #4981 Cycle 56 exact finite selected-edge connectivity decision and open forest selection
  proof_dag_predecessors: [selectedReachableDecidable, allNamedEdges_reachable_iff_original, ExplicitEnumeration.toFintype]
  proof_obligation: From complete finite original vertex/edge tables, execute a terminating edge-name deletion search whose output remains a subset of the original names and connects every original undirected component
  selection_reason: Produces an actual input-generated spanning edge selection before proving irredundancy/bridge and tree paths
  expected_result_type: proof-checkpoint
  lean_targets: [ResearchLean/AG/ProtocolHolonomy/FiniteSpanningSelection.lean]
  risks: [using noncomputable connectivity choice, deleting a necessary named edge, treating parallel names as one, claiming acyclicity or bridge without proof]
  unchecked: [retained-edge irredundancy/bridge, actual named forest and root paths, fixed examples]
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: A structurally recursive deletion over the original edge-name list removes each name only if the exact finite selected-edge decision proves all original component connections survive; the output uses only original names and spans each original component
  completion_candidate: no
  lean_artifacts: [SpansOriginalComponents, pruneNamedEdges, finiteSpanningEdgeSelection]
  evidence: [pruneNamedEdges_spans, pruneNamedEdges_subset, finiteSpanningEdgeSelection_originalReachable, parallel-edge-plus-loop evaluation yielding one selected edge and loop false]
  claim_mapping:
    theorem_names: [finiteSpanningEdgeSelection_subset, finiteSpanningEdgeSelection_spans, finiteSpanningEdgeSelection_originalReachable]
    source_labels: [E input-generated finite named spanning selection]
    conjuncts: [complete original name list, terminating deletion, exact connectivity decision at every step, all original components, subset of original edge names]
    undischarged_assumptions: [GOAL E finite tables and equality decisions only; retained edges are not yet proved bridges]
    acceptance_point: Input-generated connected spanning named-edge subset, not yet a genuine undirected named spanning forest
    port_status: unported
audits:
  premise_delta:
    discharged: [finite input-generated spanning named-edge selection with original component connectedness]
    remaining: [irredundancy and bridge proof, forest structure and selected tree paths, fixed examples]
  certificate_provenance:
    discharged: [runtime deletion uses only exact Cycle 56 finite connectivity decision and original edge list; no supplied spanning certificate]
    unresolved: [edge-minimality and bridge condition]
  proof_use:
    used: [all original edge names, selected-edge finite decision, all-edge-to-original component relation, recursive spanning preservation and subset proofs]
    unused: [no noncomputable tree/group action in runtime selection]
  structure_field_escape: none-found-for-connected-selection
  route_integrity: pass-for-input-generated-original-edge-selection
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [focused Lean check, ten explicit #print axioms and namespace standard-axiom assertion to be recorded in PR; parallel-edge-plus-loop #eval card one and loop false]
```

## Cycle 58 selection / proposed result

```yaml
ledger_type: target_cycle_result
goal: G-127-aat-reversible-protocol-holonomy
cycle: 58
goal_blob_sha: 86ed6948771755a19db802e01e42dbd00a8f9abf
base_oid: 76819256b39ec04c59e9e33832e9a0eaf1d50d07
tracking_issue: 4981
report_path: research/reports/G-127-aat-reversible-protocol-holonomy.md
selection:
  proof_state_ref: Issue #4981 Cycle 57 input-generated spanning named-edge selection and open retained-edge irredundancy
  proof_dag_predecessors: [selectedNamedStep, SelectedNamedReachable, SpansOriginalComponents, pruneNamedEdges_subset, finiteSpanningEdgeSelection_subset]
  proof_obligation: Prove that every original edge name retained by the finite deletion algorithm is individually necessary for spanning every original component
  selection_reason: Supplies the edge-minimality proof needed to derive the literal undirected named-tree bridge property
  expected_result_type: proof-checkpoint
  lean_targets: [ResearchLean/AG/ProtocolHolonomy/FiniteIrredundantSelection.lean]
  risks: [assuming monotonicity without proof, losing a retained edge when handling duplicates, proving only local-stage failure rather than final failure, claiming bridge before rerouting proof]
  unchecked: [selected-edge endpoint bridge implication, selected named-path connectivity and actual forest/root paths, fixed examples]
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: Selected reachability and all-component spanning are monotone in the selected original-name set; induction over the deletion algorithm shows that if a processed name survives to the final set, removing it from that final set cannot span the original components
  completion_candidate: no
  lean_artifacts: [selectedNamedReachable_mono, spansOriginalComponents_mono, pruneNamedEdges_irredundant]
  evidence: [finiteSpanningEdgeSelection_irredundant]
  claim_mapping:
    theorem_names: [pruneNamedEdges_irredundant, finiteSpanningEdgeSelection_irredundant]
    source_labels: [E finite named-forest edge-minimality]
    conjuncts: [every retained original name, duplicate name-list entries, final output rather than temporary stage, deletion of exact name, loss of original all-component spanning]
    undischarged_assumptions: [GOAL E finite original tables and equality decisions only; no bridge or tree path is claimed]
    acceptance_point: Every retained edge is essential to spanning, with literal bridge conversion still open
    port_status: unported
audits:
  premise_delta:
    discharged: [final retained-edge irredundancy of actual finite output]
    remaining: [endpoint bridge condition, actual named forest and selected tree paths, fixed examples]
  certificate_provenance:
    discharged: [all reachability and spanning conditions derive from original selected names and the Cycle 56 decision; no supplied minimality certificate]
    unresolved: [conversion from failure of all-component spanning to failure of an endpoint path after removing the edge]
  proof_use:
    used: [EqvGen monotonicity, Finset erase subset, Cycle 57 pruning branch decision, complete original edge-name list]
    unused: [no noncomputable forest object or bridge premise]
  structure_field_escape: none-found-for-irredundancy
  route_integrity: pass-for-pruning-to-final-edge-necessity
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [focused Lean check, four #print axioms and namespace standard-axiom assertion to be recorded in PR]
```

## Cycle 59 selection / proposed result

```yaml
ledger_type: target_cycle_result
goal: G-127-aat-reversible-protocol-holonomy
cycle: 59
goal_blob_sha: 86ed6948771755a19db802e01e42dbd00a8f9abf
base_oid: 18d3a3443
tracking_issue: 4981
report_path: research/reports/G-127-aat-reversible-protocol-holonomy.md
selection:
  proof_state_ref: Issue #4981 Cycle 58 retained original edge names are individually necessary for all-component spanning
  proof_dag_predecessors: [SelectedNamedReachable, UsesNamedEdges, finiteSpanningEdgeSelection_spans, finiteSpanningEdgeSelection_irredundant]
  proof_obligation: Convert edge irredundancy into the literal named-path bridge property required by the fixed undirected spanning-tree field
  selection_reason: Closes the exact retained-edge bridge condition while preserving original edge names and signed orientations
  expected_result_type: proof-checkpoint
  lean_targets: [ResearchLean/AG/ProtocolHolonomy/FiniteSelectionBridge.lean]
  risks: [using unnamed graph reachability, treating the selected set as an assumed tree, missing backward traversals, proving only a weak endpoint relation]
  unchecked: [actual componentwise forest construction and selected tree paths, terminating forest-root path output, fixed examples]
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: An alternate endpoint route reroutes every selected EqvGen connection around the erased edge; actual signed paths using the remaining original names induce that alternate route; irredundancy therefore excludes the literal signed-path bridge counterexample for every retained name
  completion_candidate: no
  lean_artifacts: [selectedNamedReachable_erase_of_endpoints, usesNamedEdges_selectedReachable]
  evidence: [finiteSpanningEdgeSelection_bridge]
  claim_mapping:
    theorem_names: [selectedNamedReachable_erase_of_endpoints, usesNamedEdges_selectedReachable, finiteSpanningEdgeSelection_bridge]
    source_labels: [E original named-edge bridge condition]
    conjuncts: [actual retained original name, its original source and target, all signed paths through remaining names, both edge orientations, failure of alternate path]
    undischarged_assumptions: [GOAL E explicit finite original tables and equality decisions; componentwise forest and root paths still open]
    acceptance_point: Literal bridge proposition for the generated selected edge set; no forest object or path constructor yet
    port_status: unported
audits:
  premise_delta:
    discharged: [exact retained-edge bridge condition in original signed paths]
    remaining: [actual named forest and selected tree paths, terminating root-path computation, fixed examples]
  certificate_provenance:
    discharged: [bridge derives from input-generated pruning, selected-name reachability, and original signed path edge names; no supplied tree certificate]
    unresolved: [construction of componentwise forest fields and executable selected paths]
  proof_use:
    used: [all-component spanning, final retained-edge irredundancy, EqvGen closure, signed path induction for forward and backward original edges]
    unused: [no supplied forest, root path, or noncomputable choice in the bridge theorem]
  structure_field_escape: none-found-for-bridge-proposition
  route_integrity: pass-for-selected-original-names-to-literal-bridge
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [focused Lean check, three #print axioms and namespace standard-axiom assertion to be recorded in PR]
```

## Cycle 60 selection / proposed result

```yaml
ledger_type: target_cycle_result
goal: G-127-aat-reversible-protocol-holonomy
cycle: 60
goal_blob_sha: 86ed6948771755a19db802e01e42dbd00a8f9abf
base_oid: 7da80a72a
tracking_issue: 4981
report_path: research/reports/G-127-aat-reversible-protocol-holonomy.md
selection:
  proof_state_ref: Issue #4981 Cycle 59 exact bridge property and open actual selected path construction
  proof_dag_predecessors: [SelectedNamedReachable, UsesNamedEdges, signedComp, signedReverse, usesNamedEdges_selectedReachable]
  proof_obligation: Show that selected original-name reachability produces an actual signed path all of whose edges retain those original names
  selection_reason: Supplies the connected field of the finite generated named forest without assuming a selected path certificate
  expected_result_type: proof-checkpoint
  lean_targets: [ResearchLean/AG/ProtocolHolonomy/SelectedNamedPaths.lean]
  risks: [only proving one direction, losing original names on path reversal, requiring an assumed tree or path]
  unchecked: [componentwise forest fields, terminating selected root-path computation, fixed examples]
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: A selected original edge step becomes a one-edge signed path; path concatenation and reversal preserve the exact original names; induction on the selected equivalence closure yields an actual selected signed path and the converse follows from the prior signed-path conversion
  completion_candidate: no
  lean_artifacts: [usesNamedEdges_single, usesNamedEdges_comp, usesNamedEdges_reverse]
  evidence: [selectedNamedReachable_iff_usesNamedEdges]
  claim_mapping:
    theorem_names: [selectedNamedReachable_iff_usesNamedEdges]
    source_labels: [E named spanning forest connectivity]
    conjuncts: [selected original edge names, signed forward and reverse paths, reflexive symmetric transitive closure, both implications]
    undischarged_assumptions: [forest packaging and executable selected path choice remain open]
    acceptance_point: Existence of an actual selected signed path exactly when selected-name reachability holds
    port_status: unported
audits:
  premise_delta:
    discharged: [selected-reachability-to-actual-selected-path equivalence]
    remaining: [componentwise named forest, terminating selected root paths, fixed examples]
  certificate_provenance:
    discharged: [path existence follows by induction on original selected-edge steps with no supplied forest or path certificate]
    unresolved: [computable extraction of a selected path from finite tables]
  proof_use:
    used: [original typed edge names, reverse signed edge, concatenation, selected EqvGen induction]
    unused: [no noncomputable tree choice or arbitrary graph-edge quotient]
  structure_field_escape: none-found-for-path-existence
  route_integrity: pass-for-selected-reachability-to-original-named-paths
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [focused Lean check, four #print axioms and namespace standard-axiom assertion to be recorded in PR]
```

## Cycle 61 selection / proposed result

```yaml
ledger_type: target_cycle_result
goal: G-127-aat-reversible-protocol-holonomy
cycle: 61
goal_blob_sha: 86ed6948771755a19db802e01e42dbd00a8f9abf
base_oid: 71cf2ec4a
tracking_issue: 4981
report_path: research/reports/G-127-aat-reversible-protocol-holonomy.md
selection:
  proof_state_ref: Issue #4981 Cycle 60 actual selected signed-path existence, Cycle 59 bridge, and open forest structure
  proof_dag_predecessors: [finiteSpanningEdgeSelection_originalReachable, finiteSpanningEdgeSelection_bridge, selectedNamedReachable_iff_usesNamedEdges, UndirectedNamedSpanningForest]
  proof_obligation: Construct the actual named spanning forest from the generated selected original edge set on every original component
  selection_reason: Packages component restriction, selected-path connectivity, and exact bridge into the fixed B/E forest structure
  expected_result_type: proof-checkpoint
  lean_targets: [ResearchLean/AG/ProtocolHolonomy/FiniteNamedForest.lean]
  risks: [selected edges from other components leaking into a tree, non-original edge names, supplied tree certificate, noncomputable path choice passed off as E procedure]
  unchecked: [terminating selected root-path computation, fixed examples]
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: The finite original-name selection restricted by source component yields the actual UndirectedNamedSpanningForest; every selected signed path from that component stays within it, and the exact bridge theorem supplies its bridge field
  completion_candidate: no
  lean_artifacts: [usesNamedEdges_mono, usesNamedEdges_restrictComponent]
  evidence: [finiteNamedSpanningForest]
  claim_mapping:
    theorem_names: [finiteNamedSpanningForest]
    source_labels: [B original named spanning forest, E finite table forest construction]
    conjuncts: [every original component, original selected edge names, within, connected via actual SignedPath, bridge excluding alternate same-name route]
    undischarged_assumptions: [explicit finite original vertex and edge tables and equality decisions; executable selected root-path selection still open]
    acceptance_point: Actual forest structure generated from finite tables with connected and bridge proofs; no terminating selected path output claimed
    port_status: unported
audits:
  premise_delta:
    discharged: [componentwise original named forest structure]
    remaining: [terminating selected root-path computation, fixed examples]
  certificate_provenance:
    discharged: [forest derived from input-generated edge selection and proved reachability and bridge; no supplied forest/tree certificate]
    unresolved: [finite computational extraction of selected tree root paths]
  proof_use:
    used: [component equality, original selected path equivalence, signed path component restriction, generated bridge theorem]
    unused: [no assumed tree or arbitrary spanning certificate]
  structure_field_escape: none-found-for-forest
  route_integrity: pass-for-generated-original-names-to-intrinsic-forest
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [focused Lean check, three #print axioms and namespace standard-axiom assertion to be recorded in PR]
```

## Cycle 62 selection / proposed result

```yaml
ledger_type: target_cycle_result
goal: G-127-aat-reversible-protocol-holonomy
cycle: 62
goal_blob_sha: 86ed6948771755a19db802e01e42dbd00a8f9abf
base_oid: 6c7e65545
tracking_issue: 4981
report_path: research/reports/G-127-aat-reversible-protocol-holonomy.md
selection:
  proof_state_ref: Issue #4981 Cycle 61 actual generated forest and open executable selected root paths
  proof_dag_predecessors: [selectedReachabilityGraph, signedToPath, UsesNamedEdges, usesNamedEdges_single, usesNamedEdges_comp]
  proof_obligation: Resolve each finite selected-graph adjacency and walk into an executable original named signed passage with selection proof
  selection_reason: Gives the computational edge and walk conversion needed before bounded selected path search
  expected_result_type: proof-checkpoint
  lean_targets: [ResearchLean/AG/ProtocolHolonomy/FiniteSelectedWalks.lean]
  risks: [using noncomputable Finset.toList, accepting unselected original edge, losing edge name or reverse orientation, treating walk conversion as complete root algorithm]
  unchecked: [bounded selected path search, terminating selected root-path construction, fixed examples]
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: Scan the explicit original edge list with a selected-membership test to compute a typed forward or reverse signed passage for each selected adjacency; recursively concatenate these passages for a finite graph walk while retaining a UsesNamedEdges proof
  completion_candidate: no
  lean_artifacts: [selectedSignedStepCandidate, selectedSignedStepCandidate_ne_none_of_pos, selectedSignedStepCandidate_ne_none_of_neg, selectedSignedEdgeOfAdj]
  evidence: [selectedSignedPathOfWalk]
  claim_mapping:
    theorem_names: [selectedSignedEdgeOfAdj, selectedSignedPathOfWalk]
    source_labels: [E selected original named path computation]
    conjuncts: [explicit original edge list, actual selected names, positive and negative passage, terminating list scan and walk recursion, selected-edge proof]
    undischarged_assumptions: [selected adjacency or finite walk is supplied; bounded generation and root-level selection remain open]
    acceptance_point: Computable translation of a finite selected graph walk to an actual original signed path with selected-name certificate
    port_status: unported
audits:
  premise_delta:
    discharged: [computable selected adjacency and walk translation]
    remaining: [bounded selected path generation, executable selected root paths, fixed examples]
  certificate_provenance:
    discharged: [selected membership tested against computed original-name set; scan uses explicit original edge values and adjacency proof only to eliminate impossible empty result]
    unresolved: [production of the selected walk from finite tables]
  proof_use:
    used: [original edge list completeness, selected adjacency witness, forward and reverse typed edges, signed path composition]
    unused: [no noncomputable Finset.toList or supplied tree-path certificate]
  structure_field_escape: none-found-for-walk-translation
  route_integrity: pass-for-selected-adjacency-to-original-named-walk
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [focused Lean check, five #print axioms and namespace standard-axiom assertion to be recorded in PR]
```

## Cycle 63 selection / proposed result

```yaml
ledger_type: target_cycle_result
goal: G-127-aat-reversible-protocol-holonomy
cycle: 63
goal_blob_sha: 86ed6948771755a19db802e01e42dbd00a8f9abf
base_oid: dd5bf0e1e
tracking_issue: 4981
report_path: research/reports/G-127-aat-reversible-protocol-holonomy.md
selection:
  proof_state_ref: Issue #4981 Cycle 62 executable selected-walk translation and open bounded selected walk search
  proof_dag_predecessors: [selectedReachable_iff_named, selectedAdjDecidable, selectedSignedPathOfWalk, ExplicitEnumeration.toFintype]
  proof_obligation: Compute a selected original named path for every selected-reachable pair from bounded finite graph-walk enumeration
  selection_reason: Supplies executable selected path choice needed for component roots and E forest-root output
  expected_result_type: proof-checkpoint
  lean_targets: [ResearchLean/AG/ProtocolHolonomy/FiniteSelectedPaths.lean]
  risks: [assuming unbounded search terminates, choosing a path by Classical.choice, returning a path outside selected original names, asserting root normalization prematurely]
  unchecked: [input-generated normalized root paths and E integration, fixed examples]
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: Enumerate selected walks by length using explicit vertex values and decidable selected adjacency; every concrete walk occurs at its length; simple paths lie below the finite vertex count, so a reachable pair gives a nonempty bounded list whose head translates to an actual selected original named signed path
  completion_candidate: no
  lean_artifacts: [finiteSelectedWalksExact, mem_finiteSelectedWalksExact, finiteSelectedBoundedWalks]
  evidence: [finiteSelectedNamedPathOfReachable]
  claim_mapping:
    theorem_names: [finiteSelectedNamedPathOfReachable]
    source_labels: [E terminating original named selected-path construction]
    conjuncts: [explicit finite vertex and edge tables, selected edge set, bounded walk enumeration, list-head choice, original selected SignedPath and name proof]
    undischarged_assumptions: [selected reachability proof; finite root selection and normalized family of root paths still open]
    acceptance_point: Terminating selected path computation conditional only on an established selected-reachable pair
    port_status: unported
audits:
  premise_delta:
    discharged: [bounded selected path generation and executable selected named path selection]
    remaining: [normalized roots and selected root paths from finite tables, fixed examples]
  certificate_provenance:
    discharged: [walk list is generated from explicit vertex values and selected adjacency; original names resolved by explicit edge list; reachability proof only eliminates impossible empty list]
    unresolved: [root-level combination with component equality and forest]
  proof_use:
    used: [simple path length bound, finite enumeration completeness, selected adjacency decision, Cycle 62 walk translator]
    unused: [no unbounded search or noncomputable selected path choice]
  structure_field_escape: none-found-for-selected-path-procedure
  route_integrity: pass-for-bounded-selected-walk-to-original-named-path
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [focused Lean check, four #print axioms, namespace standard-axiom assertion, one #eval length-1 smoke to be recorded in PR]
```

## Cycle 64 selection / proposed result

```yaml
ledger_type: target_cycle_result
goal: G-127-aat-reversible-protocol-holonomy
cycle: 64
goal_blob_sha: 86ed6948771755a19db802e01e42dbd00a8f9abf
base_oid: 7adba59dd
tracking_issue: 4981
report_path: research/reports/G-127-aat-reversible-protocol-holonomy.md
selection:
  proof_state_ref: Issue #4981 Cycle 63 terminating selected path search and open normalized root-path family
  proof_dag_predecessors: [finiteRootForComponent, finiteSpanningEdgeSelection_originalReachable, finiteSelectedNamedPathOfReachable, usesNamedEdges_restrictComponent, finiteNamedSpanningForest]
  proof_obligation: Compute normalized root-to-vertex paths inside the generated original named forest for every finite original component
  selection_reason: Supplies the exact B/C RootedPaths input from finite tables and proves its paths stay in the same E forest
  expected_result_type: proof-checkpoint
  lean_targets: [ResearchLean/AG/ProtocolHolonomy/FiniteSelectedRootedPaths.lean]
  risks: [noncomputable choice of roots or paths, failing root-path normalization, a path leaving its component tree, claiming all E integration or examples]
  unchecked: [B2/C1/E decision integration with these selected root paths, fixed examples]
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: The first vertex in each component is chosen from the explicit input list; for other vertices the bounded selected path search computes an original named path and component restriction proves it stays in the generated tree; the root itself receives the empty path, yielding RootedPaths and a forest-membership theorem
  completion_candidate: no
  lean_artifacts: [finiteSelectedPathFromRoot, finiteSelectedPathFromRoot_self, finiteSelectedRootedPaths]
  evidence: [finiteSelectedRootedPaths_path_usesForest]
  claim_mapping:
    theorem_names: [finiteSelectedRootedPaths, finiteSelectedRootedPaths_path_usesForest]
    source_labels: [B root paths in named spanning forest, E finite root and tree path construction]
    conjuncts: [all original components, input-generated roots, selected original names, actual SignedPath, empty path at each root, same generated forest]
    undischarged_assumptions: [finite original tables and equality decisions; B2/C1/E end-to-end use and fixed examples still open]
    acceptance_point: Terminating normalized rooted-path family whose paths lie in the input-generated named forest
    port_status: unported
audits:
  premise_delta:
    discharged: [finite-table selected roots and normalized selected root paths]
    remaining: [B2/C1/E integration using selected rooted paths, fixed examples]
  certificate_provenance:
    discharged: [component representatives from finite vertex list; selected paths from bounded search and original edge scan; no supplied roots, tree, or path certificate]
    unresolved: [end-to-end finite procedure and example evaluations]
  proof_use:
    used: [original component equality, generated selected reachability, finite selected path search, component restriction, RootedPaths.path_root]
    unused: [no noncomputable forest.toRootedPaths choice]
  structure_field_escape: none-found-for-rooted-path-family
  route_integrity: pass-for-generated-forest-to-finite-root-paths
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [focused Lean check, four #print axioms, namespace standard-axiom assertion, one #eval length-1 smoke to be recorded in PR]
```

## Cycle 65 selection / proposed result

```yaml
ledger_type: target_cycle_result
goal: G-127-aat-reversible-protocol-holonomy
cycle: 65
goal_blob_sha: 86ed6948771755a19db802e01e42dbd00a8f9abf
base_oid: 4bd57d077
tracking_issue: 4981
report_path: research/reports/G-127-aat-reversible-protocol-holonomy.md
selection:
  proof_state_ref: Issue #4981 Cycle 64 finite-table forest roots and selected paths, with B2 list still using the older rooted family
  proof_dag_predecessors: [finiteSelectedRootedPaths, finiteRootCentralizers, centralizer_mem_finiteRootCentralizers, finiteComponentEnumeration, reconstructVertical_evaluation]
  proof_obligation: Enumerate exact B2 centralizer tuples and every original vertical A1 lift using the input-generated selected forest root paths
  selection_reason: Connects the newly constructed B/E forest directly to B2 and the vertical kernel of C/E
  expected_result_type: proof-checkpoint
  lean_targets: [ResearchLean/AG/ProtocolHolonomy/FiniteSelectedVerticalLifts.lean]
  risks: [centralizer tested for a different root family, incomplete component enumeration, supplied B2 certificate, claiming visible-lift search before C1 integration]
  unchecked: [C1 and full E visible-lift/all-lift integration with selected forest, fixed examples]
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: Dependent products of exact finite B2 root-centralizer lists over every original component, using the selected forest rooted paths, reconstruct every actual original vertical A1 lift and include each such lift
  completion_candidate: no
  lean_artifacts: [ReversibleData.finiteSelectedRootCentralizerFamilies]
  evidence: [ReversibleData.finiteSelectedVerticalLifts]
  claim_mapping:
    theorem_names: [ReversibleData.finiteSelectedRootCentralizerFamilies, ReversibleData.finiteSelectedVerticalLifts]
    source_labels: [B2 component holonomy centralizers, C vertical kernel, E finite B2 enumeration]
    conjuncts: [same generated selected root paths, all original components, every named-edge generator in the centralizer test, exact vertical lift enumeration]
    undischarged_assumptions: [GOAL E explicit finite tables and equality decisions; C1 visible branch and fixed examples still open]
    acceptance_point: Exact B2 tuple and original vertical A1 lists tied to the input-generated named forest
    port_status: unported
audits:
  premise_delta:
    discharged: [selected-forest-root B2 enumeration and vertical kernel reconstruction]
    remaining: [selected-root C1 and all visible lift integration, fixed examples]
  certificate_provenance:
    discharged: [component values from original vertex list, root fiber tables from explicit input, B2 tests every original named edge, no supplied centralizer tuple]
    unresolved: [visible change search and full E result]
  proof_use:
    used: [same finiteSelectedRootedPaths in B2 list and reconstruction, finite component completeness, centralizer list completeness, vertical evaluation equivalence]
    unused: [no supplied forest or centralizer certificate]
  structure_field_escape: none-found-for-B2-vertical-list
  route_integrity: pass-for-selected-forest-to-original-vertical-kernel
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [focused Lean check, two #print axioms and namespace standard-axiom assertion to be recorded in PR]
```

## Cycle 66 selection / proposed result

```yaml
ledger_type: target_cycle_result
goal: G-127-aat-reversible-protocol-holonomy
cycle: 66
goal_blob_sha: 86ed6948771755a19db802e01e42dbd00a8f9abf
base_oid: 56cd8e9f2
tracking_issue: 4981
report_path: research/reports/G-127-aat-reversible-protocol-holonomy.md
selection:
  proof_state_ref: Issue #4981 Cycle 65 selected-forest B2/vertical enumeration and open C1 visible branch
  proof_dag_predecessors: [finiteSelectedRootedPaths, ReversibleData.findRootLift_isSome_iff, ReversibleData.findRootLift_isSome_iff_rootSolutions, ReversibleData.mem_liftableVisible_iff_lift]
  proof_obligation: Run the original simultaneous C1 search with selected-forest root paths and scan finite visible H to compute exactly the original H_lift
  selection_reason: Connects the same finite generated forest to C1 and the actual original visible image
  expected_result_type: proof-checkpoint
  lean_targets: [ResearchLean/AG/ProtocolHolonomy/FiniteSelectedLiftability.lean]
  risks: [checking a different root family, changing the original A1 lift fiber, assuming a successful lift as input, scanning only a candidate subset of H]
  unchecked: [all A1 lifts via selected-forest B2 torsor, fixed examples]
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: The exact C1 search is instantiated with finiteSelectedRootedPaths; success is equivalent both to original A1 Lift nonemptiness and genuine C1 RootSolutions nonemptiness; filtering the complete visible table returns exactly LiftableVisible H and a successful original lift
  completion_candidate: no
  lean_artifacts: [ReversibleData.findSelectedRootLift, ReversibleData.findSelectedRootLift_isSome_iff, ReversibleData.findSelectedRootLift_isSome_iff_rootSolutions, ReversibleData.finiteSelectedLiftableVisible]
  evidence: [ReversibleData.mem_finiteSelectedLiftableVisible_iff, ReversibleData.finiteSelectedLiftableVisible_lift_iff]
  claim_mapping:
    theorem_names: [ReversibleData.findSelectedRootLift_isSome_iff, ReversibleData.findSelectedRootLift_isSome_iff_rootSolutions, ReversibleData.mem_finiteSelectedLiftableVisible_iff]
    source_labels: [C1 simultaneous lift condition, E original H_lift decision]
    conjuncts: [same selected forest roots, full finite original edge and fiber tables, exact success/nonexistence, complete finite H scan, original A1 lift fiber]
    undischarged_assumptions: [GOAL E explicit finite tables and complete H enumeration; all-lift torsor output and fixed examples still open]
    acceptance_point: Exact selected-forest C1 decision and original liftable visible image list
    port_status: unported
audits:
  premise_delta:
    discharged: [selected-root C1 decision and finite original H_lift scan]
    remaining: [selected-root all-lift enumeration via B2/C3, fixed examples]
  certificate_provenance:
    discharged: [root paths generated from finite original tables; C1 candidates generated from finite fiber tables; H elements from complete supplied visible table; no successful lift certificate]
    unresolved: [complete all-lift list and fixed examples]
  proof_use:
    used: [same finiteSelectedRootedPaths in C1 and root solutions, complete H enumeration, original LiftableVisible characterization]
    unused: [no supplied root or C1 solution]
  structure_field_escape: none-found-for-C1-H-lift-list
  route_integrity: pass-for-selected-forest-to-original-visible-image
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [focused Lean check, six #print axioms and namespace standard-axiom assertion to be recorded in PR]
```

## Cycle 67 selection / proposed result

```yaml
ledger_type: target_cycle_result
goal: G-127-aat-reversible-protocol-holonomy
cycle: 67
goal_blob_sha: 86ed6948771755a19db802e01e42dbd00a8f9abf
base_oid: 5243ed7c5
tracking_issue: 4981
report_path: research/reports/G-127-aat-reversible-protocol-holonomy.md
selection:
  proof_state_ref: Issue #4981 Cycle 65 selected-root B2 vertical list and Cycle 66 selected-root C1/H_lift search
  proof_dag_predecessors: [ReversibleData.findSelectedRootLift_isSome_iff, ReversibleData.finiteSelectedVerticalLifts, ReversibleData.composeVertical_eq_rightAction, ReversibleData.verticalRightAction_transitive]
  proof_obligation: Recover every original A1 lift over each visible change by combining the selected-forest C1 output with all B2 vertical lifts via the original C3 torsor
  selection_reason: Completes the selected-forest E fiber output and exact negative branch before the fixed examples
  expected_result_type: proof-checkpoint
  lean_targets: [ResearchLean/AG/ProtocolHolonomy/FiniteSelectedAllLifts.lean]
  risks: [composing in the wrong action order, missing an original vertical lift, claiming empty list without lift nonexistence, introducing a supplied torsor certificate]
  unchecked: [the two fixed examples and cumulative A-E completion audit]
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: For a visible change the selected-forest C1 search returns either no lift or one original A1 lift; the successful branch composes that lift on the right with the complete selected-forest B2 vertical list; C3 transitivity proves every original Lift g appears, and the output is empty exactly when the original Lift g is empty
  completion_candidate: no
  lean_artifacts: [ReversibleData.finiteSelectedAllLifts]
  evidence: [ReversibleData.mem_finiteSelectedAllLifts, ReversibleData.finiteSelectedAllLifts_eq_nil_iff]
  claim_mapping:
    theorem_names: [ReversibleData.mem_finiteSelectedAllLifts, ReversibleData.finiteSelectedAllLifts_eq_nil_iff]
    source_labels: [C3 original right torsor, E all-lifts finite output and negative decision]
    conjuncts: [same selected forest in C1 and B2, original A1 Lift g, actual C3 right composition, exhaustive list, empty iff nonexistent]
    undischarged_assumptions: [GOAL E explicit finite tables and equality decisions; fixed examples and final cumulative audit remain]
    acceptance_point: Exact all-original-lifts output from the input-generated named forest for every visible change
    port_status: unported
audits:
  premise_delta:
    discharged: [selected-forest C1/B2/C3 all-lift output and negative branch]
    remaining: [two fixed examples, final A-E matching and completion audit]
  certificate_provenance:
    discharged: [C1 output generated from finite tables; vertical list from all original component B2 tables; C3 transitivity proves completeness; no supplied lift or torsor certificate]
    unresolved: [concrete finite example data and evaluations]
  proof_use:
    used: [selected C1 success equivalence, selected B2 vertical completeness, original composeVertical/rightAction equality, original torsor transitivity]
    unused: [no external choice of a reference lift]
  structure_field_escape: none-found-for-all-lifts-output
  route_integrity: pass-for-selected-forest-C1-B2-C3-to-original-Lift-fiber
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [focused Lean check, three #print axioms and namespace standard-axiom assertion to be recorded in PR]
```

## Cycle 68 selection / proposed result

```yaml
ledger_type: target_cycle_result
goal: G-127-aat-reversible-protocol-holonomy
cycle: 68
goal_blob_sha: 86ed6948771755a19db802e01e42dbd00a8f9abf
base_oid: 3a3af457d
tracking_issue: 4981
report_path: research/reports/G-127-aat-reversible-protocol-holonomy.md
selection:
  proof_state_ref: Issue #4981 Cycle 67 complete selected-forest E output and open fixed nonliftable example
  proof_dag_predecessors: [ReversibleData.Lift.edge_naturality, ReversibleData.findSelectedRootLift_isSome_iff]
  proof_obligation: Instantiate the exact one-vertex two-named-loop input and prove the name-swap has no original A1 lift and the E decision returns none
  selection_reason: Begins fixed completion condition 2 with the original input and an actual negative lift proof
  expected_result_type: proof-checkpoint
  lean_targets: [ResearchLean/AG/ProtocolHolonomy/OneVertexTwoLoops.lean]
  risks: [identifying distinct loop names, changing identity or swap edge action, deriving only a C1 failure without original A1 nonexistence, treating a smoke as a proof]
  unchecked: [fixed example 2 holonomy and B2 centralizer classification, H=C2 and H_lift trivial, full fixed example 3]
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: Define precisely one PUnit vertex, two Bool loop names, two-point Bool fiber, identity action on false and transposition on true, and visible edge-name transposition; original A1 naturality at false forces a fixed point of the transposition and is impossible; the selected-forest C1 search therefore returns none and an executable smoke evaluates false
  completion_candidate: no
  lean_artifacts: [oneLoopGraph, oneLoopData, oneLoopSwap, oneLoopVertices, oneLoopEdges, oneLoopFibers]
  evidence: [oneLoopSwap_noLift, oneLoopSwap_finiteSelected_none]
  claim_mapping:
    theorem_names: [oneLoopSwap_noLift, oneLoopSwap_finiteSelected_none]
    source_labels: [completion condition 2 original A1 nonliftability, E negative decision]
    conjuncts: [one original vertex, two distinct named loops, id and transposition edge actions, visible name swap, original Lift is empty, E returns none]
    undischarged_assumptions: [holonomy equality, B2 centralizer and H_lift classification, second fixed example]
    acceptance_point: Original A1 nonliftability and E negative result for exact first-example primitive graph and edge actions
    port_status: unported
audits:
  premise_delta:
    discharged: [fixed first-example data and original name-swap nonliftability with exact E negative result]
    remaining: [first-example holonomy/B2/H classification, full second example]
  certificate_provenance:
    discharged: [A1 contradiction uses actual false-loop equation at a concrete Bool state; finite decision uses the same explicit vertex edge fiber tables]
    unresolved: [first-example H and holonomy classification]
  proof_use:
    used: [original edge_naturality at false, Equiv.swap no fixed Bool point, selected C1 success equivalence]
    unused: [no supplied failed-search certificate or abstract nonliftability premise]
  structure_field_escape: none-found-for-original-A1-negative-example
  route_integrity: pass-for-fixed-input-to-A1-and-E-negative
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [focused Lean check, five #print axioms, namespace standard-axiom assertion, #eval false to be recorded in PR]
```

## Cycle 69 selection / proposed result

```yaml
ledger_type: target_cycle_result
goal: G-127-aat-reversible-protocol-holonomy
cycle: 69
goal_blob_sha: 86ed6948771755a19db802e01e42dbd00a8f9abf
base_oid: 7452526b6
tracking_issue: 4981
report_path: research/reports/G-127-aat-reversible-protocol-holonomy.md
selection:
  proof_state_ref: Issue #4981 Cycle 68 original nonliftability and E negative result
  proof_dag_predecessors: [oneLoopGraph, oneLoopData, oneLoopSwap, PathEquations, FiniteProtocolInput]
  proof_obligation: Fix the first example's empty Pi and full finite primitive input with the original edge actions and visible group
  selection_reason: The remaining B through E example claims must refer to one actual A-side input
  expected_result_type: proof-checkpoint
  lean_targets: [ResearchLean/AG/ProtocolHolonomy/OneVertexTwoLoopsInput.lean]
  risks: [vacuous Pi confused with absent input, changing the original fiber actions, asserting H=C2 without proof]
  unchecked: [H=C2, both holonomy groups C2, B2 centralizer, H_lift trivial, second fixed example]
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: Instantiate empty authored equations and finite vertex edge fiber witnesses; use the exact original one-loop data and the full visible graph automorphism subgroup with vacuous equation preservation
  completion_candidate: no
  lean_artifacts: [oneLoopEmptyEquations, oneLoopInput]
  evidence: [oneLoopSwap_mem_H, oneLoopInput_no_equations]
  claim_mapping:
    theorem_names: [oneLoopSwap_mem_H, oneLoopInput_no_equations]
    source_labels: [completion condition 2 primitive input and empty Pi]
    conjuncts: [same original Q and edge actions, no authored path equations, finite fibers, swap in H]
    undischarged_assumptions: [H=C2, holonomy, B2, H_lift, second fixed example]
    acceptance_point: First example is an actual FiniteProtocolInput with the original data and empty path equations
    port_status: unported
audits:
  premise_delta:
    discharged: [first-example finite primitive input and empty Pi]
    remaining: [first-example group and holonomy classification, second fixed example]
  certificate_provenance:
    discharged: [finite instances reduce definitionally to PUnit and Bool; empty equation type reduces to PEmpty]
    unresolved: [H=C2 and holonomy classification]
  proof_use:
    used: [PathEquations and FiniteProtocolInput original fields]
    unused: [no external finite or congruence certificate]
  structure_field_escape: none-found-for-first-example-A-input
  route_integrity: pass-for-first-example-primitive-input
  target_fitting: none-found
  vacuity: only-the-specified-empty-Pi
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [focused Lean check, four #print axioms and namespace standard-axiom assertion to be recorded in PR]
```

## Cycle 70 selection / proposed result

```yaml
ledger_type: target_cycle_result
goal: G-127-aat-reversible-protocol-holonomy
cycle: 70
goal_blob_sha: 86ed6948771755a19db802e01e42dbd00a8f9abf
base_oid: 3ea25f23e
tracking_issue: 4981
report_path: research/reports/G-127-aat-reversible-protocol-holonomy.md
selection:
  proof_state_ref: Issue #4981 Cycle 69 first fixed primitive input and empty Pi
  proof_dag_predecessors: [oneLoopInput, oneLoopSwap, FixedFGraphAutomorphism.ext]
  proof_obligation: Identify the first fixed example's actual visible H as C2
  selection_reason: Its later H_lift and projection claims require the exact visible group
  expected_result_type: proof-checkpoint
  lean_targets: [ResearchLean/AG/ProtocolHolonomy/OneVertexTwoLoopsVisibleGroup.lean]
  risks: [merely exhibiting an order-two element, omitting other graph automorphisms, confusing graph automorphism multiplication with an invented group]
  unchecked: [both holonomy groups C2, B2 centralizer, H_lift trivial, second fixed example]
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: Every actual visible graph automorphism is identity or the named-loop swap; its full H is group-isomorphic to permutations of Bool, has cardinality two, and is cyclic
  completion_candidate: no
  lean_artifacts: [oneLoopGraphAutOfPerm, oneLoopHEquivPermBool]
  evidence: [oneLoop_visible_eq_one_or_swap, oneLoopSwap_ne_one, oneLoop_H_exact, oneLoop_H_card_two, oneLoop_H_isCyclic]
  claim_mapping:
    theorem_names: [oneLoopHEquivPermBool, oneLoop_H_card_two, oneLoop_H_isCyclic]
    source_labels: [completion condition 2 H=C2]
    conjuncts: [actual full graph automorphism group, two elements, cyclic group structure]
    undischarged_assumptions: [both holonomy groups, B2, H_lift, second fixed example]
    acceptance_point: Same first-example input H is a cyclic group of order two with explicit graph-action classification
    port_status: unported
audits:
  premise_delta:
    discharged: [first-example visible H=C2]
    remaining: [first-example holonomy and vertical/liftable classification, second fixed example]
  certificate_provenance:
    discharged: [PUnit vertex extensionality, two-valued edge equivalence injectivity, actual group multiplication]
    unresolved: [holonomy and H_lift calculations]
  proof_use:
    used: [graph automorphism extensionality, actual edge-equivalence multiplication, explicit Bool permutation group equivalence]
    unused: [no H-cardinality axiom or supplied enumeration certificate]
  structure_field_escape: none-found-for-visible-group
  route_integrity: pass-for-first-example-H
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [focused Lean check, seven #print axioms and namespace standard-axiom assertion to be recorded in PR]
```

## Cycle 71 selection / proposed result

```yaml
ledger_type: target_cycle_result
goal: G-127-aat-reversible-protocol-holonomy
cycle: 71
goal_blob_sha: 86ed6948771755a19db802e01e42dbd00a8f9abf
base_oid: 10e53b43c
tracking_issue: 4981
report_path: research/reports/G-127-aat-reversible-protocol-holonomy.md
selection:
  proof_state_ref: Issue #4981 Cycle 70 actual visible H=C2
  proof_dag_predecessors: [oneLoopInput, oneLoopRootedPaths, ReversibleData.edgeMonodromyAt, ReversibleData.holonomy, FiniteProtocolInput.renamedRealization]
  proof_obligation: Calculate original and name-exchanged holonomy groups for the exact first fixed input and connect the exchanged table to the renamed realization
  selection_reason: GOAL condition 2 requires both holonomy groups to be C2 despite no lift of the swap
  expected_result_type: proof-checkpoint
  lean_targets: [ResearchLean/AG/ProtocolHolonomy/OneVertexTwoLoopsHolonomy.lean]
  risks: [inventing a disconnected renamed table, computing only abstract isomorphic groups, confusing edge names, omitting actual B1 generated subgroup]
  unchecked: [B2 centralizer, H_lift trivial, second fixed example]
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: Use the unique vertex's empty root paths; original true edge and renamed false edge each generate the full Bool permutation group; both actual B1 subgroups have cardinality two and are cyclic; the renamed table agrees with the independently constructed renamed realization on each original named edge
  completion_candidate: no
  lean_artifacts: [oneLoopRootedPaths, oneLoopRenamedData, oneLoopComponent]
  evidence: [oneLoop_renamed_semantic_edge, oneLoop_original_monodromy, oneLoop_renamed_monodromy, oneLoop_original_holonomy_top, oneLoop_renamed_holonomy_top, oneLoop_original_holonomy_card_two, oneLoop_renamed_holonomy_card_two, oneLoop_original_holonomy_isCyclic, oneLoop_renamed_holonomy_isCyclic]
  claim_mapping:
    theorem_names: [oneLoop_original_holonomy_top, oneLoop_renamed_holonomy_top, oneLoop_original_holonomy_card_two, oneLoop_renamed_holonomy_card_two]
    source_labels: [completion condition 2 original and renamed holonomy C2]
    conjuncts: [same original graph, same chosen root paths, original id and swap generators, actual name-swapped realization action, both cyclic order-two holonomy groups]
    undischarged_assumptions: [B2 centralizer, H_lift, second fixed example]
    acceptance_point: Both specified first-example holonomy groups are the full two-point permutation group, linked to actual edge semantics
    port_status: unported
audits:
  premise_delta:
    discharged: [original and renamed first-example holonomy C2]
    remaining: [first-example B2 and H_lift, second fixed example]
  certificate_provenance:
    discharged: [original named-edge B1 generators and renamed realization edge action]
    unresolved: [vertical centralizer and H_lift]
  proof_use:
    used: [actual B1 holonomy closure, original named edges, Bool permutation exhaustion, semantic renamed edge theorem]
    unused: [no supplied holonomy equality premise]
  structure_field_escape: none-found-for-holonomy
  route_integrity: pass-for-first-example-B1-and-renamed-semantics
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [focused Lean check, eleven #print axioms and namespace standard-axiom assertion to be recorded in PR]
```

## Cycle 72 selection / proposed result

```yaml
ledger_type: target_cycle_result
goal: G-127-aat-reversible-protocol-holonomy
cycle: 72
goal_blob_sha: 86ed6948771755a19db802e01e42dbd00a8f9abf
base_oid: a7369cec7
tracking_issue: 4981
report_path: research/reports/G-127-aat-reversible-protocol-holonomy.md
selection:
  proof_state_ref: Issue #4981 Cycle 71 both original and renamed holonomy C2
  proof_dag_predecessors: [oneLoopData, oneLoopRootedPaths, oneLoop_original_holonomy_top, ReversibleData.verticalRootMulEquiv]
  proof_obligation: Apply actual B2 vertical-group isomorphism and calculate every holonomy centralizer in the first fixed example
  selection_reason: GOAL condition 2 requires B2 to apply to the same primitive input as the negative lift proof
  expected_result_type: proof-checkpoint
  lean_targets: [ResearchLean/AG/ProtocolHolonomy/OneVertexTwoLoopsCentralizer.lean]
  risks: [using a newly defined vertical group, assuming one component without proof, only calculating one root, deriving commutativity from an unproved H]
  unchecked: [H_lift trivial, second fixed example]
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: Prove the original graph has exactly one component; its actual B1 holonomy centralizer is the full two-point permutation group at every root; instantiate B2 as an isomorphism from the actual vertical A1 group with its A2 law to the product of those centralizers
  completion_candidate: no
  lean_artifacts: [oneLoopB2]
  evidence: [oneLoop_component_unique, oneLoop_holonomy_centralizer_top, oneLoop_holonomy_centralizer_top_every, oneLoopB2]
  claim_mapping:
    theorem_names: [oneLoop_holonomy_centralizer_top_every, oneLoopB2]
    source_labels: [completion condition 2 B2 centralizer display]
    conjuncts: [unique component, full holonomy centralizer, actual vertical A1 group and A2 multiplication, root evaluation isomorphism]
    undischarged_assumptions: [H_lift trivial, second fixed example]
    acceptance_point: B2 is specialized to the exact first-example input and its centralizer is calculated
    port_status: unported
audits:
  premise_delta:
    discharged: [first-example B2 centralizer and vertical-group display]
    remaining: [first-example H_lift and second fixed example]
  certificate_provenance:
    discharged: [actual B1 holonomy, quotient-component uniqueness, cyclic order-two permutation commutativity, generic B2 proof]
    unresolved: [H_lift classification]
  proof_use:
    used: [original holonomy equality, two-point permutation group cardinal, actual verticalRootMulEquiv]
    unused: [no supplied vertical-classification certificate]
  structure_field_escape: none-found-for-B2
  route_integrity: pass-for-first-example-B2
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [focused Lean check, four #print axioms and namespace standard-axiom assertion to be recorded in PR]
```

## Cycle 73 selection / proposed result

```yaml
ledger_type: target_cycle_result
goal: G-127-aat-reversible-protocol-holonomy
cycle: 73
goal_blob_sha: 86ed6948771755a19db802e01e42dbd00a8f9abf
base_oid: b99c388d6
tracking_issue: 4981
report_path: research/reports/G-127-aat-reversible-protocol-holonomy.md
selection:
  proof_state_ref: Issue #4981 Cycle 72 first-example B2 centralizer
  proof_dag_predecessors: [oneLoop_H_exact, oneLoopSwap_noLift, ReversibleData.LiftableVisible, ReversibleData.mem_liftableVisible_iff_lift]
  proof_obligation: Prove the actual visible projection image H_lift is the identity subgroup in the first fixed example
  selection_reason: This closes the remaining subgroup classification in fixed completion condition 2
  expected_result_type: proof-checkpoint
  lean_targets: [ResearchLean/AG/ProtocolHolonomy/OneVertexTwoLoopsLiftable.lean]
  risks: [claiming only swap nonliftability without exhausting H, defining a replacement image, assuming identity has a lift]
  unchecked: [second fixed example, final cumulative A-E audit]
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: The actual H has only identity and the original name swap; the swap has no A1 lift and the identity belongs to the projection image by the group unit, so the actual H_lift subgroup equals bottom
  completion_candidate: no
  lean_artifacts: [oneLoop_H_lift_eq_bot]
  evidence: [oneLoop_H_lift_eq_bot]
  claim_mapping:
    theorem_names: [oneLoop_H_lift_eq_bot]
    source_labels: [completion condition 2 H_lift={1}]
    conjuncts: [actual A2 projection range, exhaustive H=C2 classification, swap nonliftability, identity membership]
    undischarged_assumptions: [second fixed example, final cumulative audit]
    acceptance_point: First fixed example's H_lift is exactly the identity subgroup
    port_status: unported
audits:
  premise_delta:
    discharged: [first fixed example H_lift={1}]
    remaining: [second fixed example and cumulative A-E completion]
  certificate_provenance:
    discharged: [actual projection range definition, original A1 nonliftability at named false edge, group-unit membership]
    unresolved: [second fixed example]
  proof_use:
    used: [actual mem_liftableVisible_iff_lift, H identity-or-swap classification, original swap noLift]
    unused: [no assumed subgroup image certificate]
  structure_field_escape: none-found-for-first-example-H-lift
  route_integrity: pass-for-first-example-C3-image
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [focused Lean check, one #print axioms and namespace standard-axiom assertion to be recorded in PR]
```

## Cycle 74 selection / proposed result

```yaml
ledger_type: target_cycle_result
goal: G-127-aat-reversible-protocol-holonomy
cycle: 74
goal_blob_sha: 86ed6948771755a19db802e01e42dbd00a8f9abf
base_oid: 08c3faf02
tracking_issue: 4981
report_path: research/reports/G-127-aat-reversible-protocol-holonomy.md
selection:
  proof_state_ref: Issue #4981 first fixed example complete through Cycle 73 and second fixed example open
  proof_dag_predecessors: [ReversibleData.Lift, PathEquations, FiniteProtocolInput]
  proof_obligation: Instantiate the exact second fixed primitive input and exhibit an original A1 lift of its simultaneous vertex/name exchange
  selection_reason: The required C4 extension must be built from this specific two-vertex/two-opposite-edge input
  expected_result_type: proof-checkpoint
  lean_targets: [ResearchLean/AG/ProtocolHolonomy/TwoVertexOppositeEdges.lean]
  risks: [misorienting the named edges, changing id or transposition actions, replacing the original A1 square by a certificate, assuming C4 prematurely]
  unchecked: [second-example H=C2, Aut_Q(F)=C2, A_F=C4, projection quotient, both swap lifts order four, no section, E output and C torsor]
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: Define Bool vertices and original Bool edge names with false:0-to-1 and true:1-to-0; set false edge action to identity and true to the Bool swap; define the simultaneous visible exchange and its actual A1 lift with identity fiber at 0 and swap fiber at 1; package the same data with empty Pi and full visible H into a finite protocol input
  completion_candidate: no
  lean_artifacts: [twoVertexGraph, twoVertexData, twoVertexSwap, twoVertexSwapLift, twoVertexEmptyEquations, twoVertexInput]
  evidence: [twoVertexSwap_mem_H, twoVertexInput_no_equations, twoVertexSwapLift.edge_naturality]
  claim_mapping:
    theorem_names: [twoVertexSwapLift, twoVertexSwap_mem_H, twoVertexInput_no_equations]
    source_labels: [completion condition 3 exact primitive input and existence of a swap lift]
    conjuncts: [two opposite original named edges, Bool fibers, id and transposition actions, simultaneous vertex/name exchange, empty Pi, finite witnesses, original A1 lift]
    undischarged_assumptions: [H=C2, vertical and total group classifications, quotient and section, E and torsor]
    acceptance_point: Exact second-example primitive input and one original A1 lift exist in Lean
    port_status: unported
audits:
  premise_delta:
    discharged: [second-example finite primitive input and explicit swap lift]
    remaining: [second-example group extension, E and torsor classification]
  certificate_provenance:
    discharged: [edge naturality proved directly by cases on both original names and both fiber states]
    unresolved: [group and finite output calculations]
  proof_use:
    used: [actual ReversibleData.Lift A1 edge square, original named edge actions]
    unused: [no assumed swap-lift certificate]
  structure_field_escape: none-found-for-second-example-input
  route_integrity: pass-for-second-example-A1
  target_fitting: none-found
  vacuity: only-the-specified-empty-Pi
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [focused Lean check, eight #print axioms and namespace standard-axiom assertion to be recorded in PR]
```

## Cycle 75 selection / proposed result

```yaml
ledger_type: target_cycle_result
goal: G-127-aat-reversible-protocol-holonomy
cycle: 75
goal_blob_sha: 86ed6948771755a19db802e01e42dbd00a8f9abf
base_oid: 8b64c529f
tracking_issue: 4981
report_path: research/reports/G-127-aat-reversible-protocol-holonomy.md
selection:
  proof_state_ref: Issue #4981 Cycle 74 second fixed input and original swap lift
  proof_dag_predecessors: [twoVertexGraph, twoVertexSwap, twoVertexInput, FixedFGraphAutomorphism.ext]
  proof_obligation: Identify the actual full visible group H of the second fixed example as C2
  selection_reason: The specified C4 extension and projection require exactly the visible simultaneous vertex/name exchange
  expected_result_type: proof-checkpoint
  lean_targets: [ResearchLean/AG/ProtocolHolonomy/TwoVertexVisibleGroup.lean]
  risks: [showing only one order-two element, omitting additional graph automorphisms, treating vertex and edge permutations independently, invented multiplication]
  unchecked: [Aut_Q(F)=C2, A_F=C4, quotient projection, two order-four swap lifts, no section, E and torsor]
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: Every actual graph automorphism has identical vertex and original edge-name permutations; these are identity or simultaneous swap; H is group-isomorphic to permutations of Bool, has cardinality two, and is cyclic
  completion_candidate: no
  lean_artifacts: [twoVertexGraphAutOfPerm, twoVertexHEquivPermBool]
  evidence: [twoVertex_vertex_eq_edge, twoVertex_visible_eq_one_or_swap, twoVertexSwap_ne_one, twoVertex_H_exact, twoVertex_H_card_two, twoVertex_H_isCyclic]
  claim_mapping:
    theorem_names: [twoVertexHEquivPermBool, twoVertex_H_card_two, twoVertex_H_isCyclic]
    source_labels: [completion condition 3 H=C2]
    conjuncts: [actual full graph automorphism group, simultaneous vertex and edge action, two elements, cyclic group]
    undischarged_assumptions: [vertical and total group classifications, quotient and section, E and torsor]
    acceptance_point: Second-example H is the actual simultaneous exchange group C2
    port_status: unported
audits:
  premise_delta:
    discharged: [second-example H=C2]
    remaining: [second-example C4 extension and decision/torsor output]
  certificate_provenance:
    discharged: [original source labels force vertex=edge permutation, Bool permutation exhaustion, actual graph group law]
    unresolved: [vertical and total group calculations]
  proof_use:
    used: [source_rename for all original edge names, graph automorphism extensionality, genuine multiplication]
    unused: [no assumed H enumeration]
  structure_field_escape: none-found-for-visible-H
  route_integrity: pass-for-second-example-visible-group
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [focused Lean check, eight #print axioms and namespace standard-axiom assertion to be recorded in PR]
```

## Cycle 76 selection / proposed result

```yaml
ledger_type: target_cycle_result
goal: G-127-aat-reversible-protocol-holonomy
cycle: 76
goal_blob_sha: 86ed6948771755a19db802e01e42dbd00a8f9abf
base_oid: e65d454b0
tracking_issue: 4981
report_path: research/reports/G-127-aat-reversible-protocol-holonomy.md
selection:
  proof_state_ref: Issue #4981 Cycle 75 second-example actual visible H=C2
  proof_dag_predecessors: [twoVertexData, ReversibleData.Lift, ReversibleData.vertical_mul_fiber_apply]
  proof_obligation: Identify the actual identity-visible A1 group Aut_Q(F) of the second fixed example as C2
  selection_reason: The specified C4 extension's kernel must be the actual A2 vertical group
  expected_result_type: proof-checkpoint
  lean_targets: [ResearchLean/AG/ProtocolHolonomy/TwoVertexVerticalGroup.lean]
  risks: [classifying merely one fiber without naturality, defining a replacement group, unproved commutation with the transposition edge, assumed cardinality]
  unchecked: [A_F=C4, projection quotient, both swap lifts order four, no section, E and torsor]
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: The original identity edge forces equal fiber permutations at vertices 0 and 1 for every vertical A1 lift; every Bool permutation gives an original vertical A1 lift; evaluation at vertex 0 is a group isomorphism using actual A2 multiplication; the group has cardinality two and is cyclic
  completion_candidate: no
  lean_artifacts: [twoVertexVerticalOfPerm, twoVertexVerticalEquivPermBool, twoVertexVerticalSwap]
  evidence: [twoVertex_vertical_fibers_eq, twoVertex_vertical_card_two, twoVertex_vertical_isCyclic]
  claim_mapping:
    theorem_names: [twoVertexVerticalEquivPermBool, twoVertex_vertical_card_two, twoVertex_vertical_isCyclic]
    source_labels: [completion condition 3 Aut_Q(F)=C2]
    conjuncts: [original A1 vertical lifts, both vertex fiber maps, actual A2 law, group isomorphism to Bool permutations, cyclic order two]
    undischarged_assumptions: [total group C4 and quotient, both swap lifts order four, no section, E and torsor]
    acceptance_point: Actual second-example vertical A1 group is C2 with its A2-derived multiplication
    port_status: unported
audits:
  premise_delta:
    discharged: [second-example Aut_Q(F)=C2]
    remaining: [second-example total extension and finite/torsor output]
  certificate_provenance:
    discharged: [original identity edge square, direct Bool permutation commutation with the transposition edge, generic A2 vertical product formula]
    unresolved: [total group]
  proof_use:
    used: [original edge naturality for both edge names, A2 vertical product theorem]
    unused: [no supplied vertical classification premise]
  structure_field_escape: none-found-for-vertical-group
  route_integrity: pass-for-second-example-kernel
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [focused Lean check, six #print axioms and namespace standard-axiom assertion to be recorded in PR]
```

## Cycle 77 selection / proposed result

```yaml
ledger_type: target_cycle_result
goal: G-127-aat-reversible-protocol-holonomy
cycle: 77
goal_blob_sha: 86ed6948771755a19db802e01e42dbd00a8f9abf
base_oid: 6eeaf01ea
tracking_issue: 4981
report_path: research/reports/G-127-aat-reversible-protocol-holonomy.md
selection:
  proof_state_ref: Issue #4981 Cycle 76 actual vertical Aut_Q(F)=C2
  proof_dag_predecessors: [twoVertexSwapLift, twoVertexVerticalSwap, ReversibleData.ChangeGroup, ReversibleData.Lift.toStateChange]
  proof_obligation: Calculate the order of an actual A2 change lying above the second example's visible swap
  selection_reason: A fourth-order swap lift is the structural generator required for the C4 extension and non-splitting proof
  expected_result_type: proof-checkpoint
  lean_targets: [ResearchLean/AG/ProtocolHolonomy/TwoVertexCycle.lean]
  risks: [calculating only a fiberwise candidate, ignoring actual A2 multiplication, asserting order four from a smoke, failing to distinguish square from identity]
  unchecked: [entire A_F=C4, quotient projection, second swap lift order four, no section, E and torsor]
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: Embed the original swap lift and nontrivial vertical lift in the actual ChangeGroup; the swap lift's square is the nontrivial vertical change, whose square is identity; the swap lift is not identity and has exact order four
  completion_candidate: no
  lean_artifacts: [twoVertexCycleChange, twoVertexVerticalChange]
  evidence: [twoVertexCycleChange_sq, twoVertexVerticalChange_sq, twoVertexCycleChange_ne_one, twoVertexVerticalChange_ne_one, twoVertexCycleChange_pow_four, twoVertexCycleChange_order_four]
  claim_mapping:
    theorem_names: [twoVertexCycleChange_sq, twoVertexCycleChange_order_four]
    source_labels: [completion condition 3 one order-four swap lift]
    conjuncts: [actual original swap A1 lift, actual A2 ChangeGroup multiplication, nontrivial square, exact order four]
    undischarged_assumptions: [total group exhaustiveness and C4, second swap lift order four, quotient and no section, E and torsor]
    acceptance_point: The explicit original swap lift has exact order four in the actual A2 change group
    port_status: unported
audits:
  premise_delta:
    discharged: [one actual swap lift has order four]
    remaining: [total C4 classification, second lift, projection/section, E and torsor]
  certificate_provenance:
    discharged: [actual StateChange fields and multiplication, state equivalence evaluated on every Bool vertex/state, original A1 lift]
    unresolved: [group exhaustiveness]
  proof_use:
    used: [actual ChangeGroup subtype, StateChange.ext, state permutation on all four states, orderOf_eq_iff]
    unused: [no supplied order certificate]
  structure_field_escape: none-found-for-order-four-generator
  route_integrity: pass-for-second-example-generator
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [focused Lean check, five #print axioms and namespace standard-axiom assertion to be recorded in PR]
```

## Cycle 78 selection / proposed result

```yaml
ledger_type: target_cycle_result
goal: G-127-aat-reversible-protocol-holonomy
cycle: 78
goal_blob_sha: 86ed6948771755a19db802e01e42dbd00a8f9abf
base_oid: 0dce93d3d
tracking_issue: 4981
report_path: research/reports/G-127-aat-reversible-protocol-holonomy.md
selection:
  proof_state_ref: Issue #4981 Cycle 77 one actual order-four swap lift
  proof_dag_predecessors: [twoVertexSwapLift, twoVertexData.Lift.edge_naturality, twoVertex_H_exact]
  proof_obligation: Exhaust the original A1 lift fiber above the second example's visible swap
  selection_reason: The fixed target requires both swap lifts and their subsequent order and E/torsor classification
  expected_result_type: proof-checkpoint
  lean_targets: [ResearchLean/AG/ProtocolHolonomy/TwoVertexSwapFiber.lean]
  risks: [finding a second candidate without exhaustiveness, assuming commutation for arbitrary fiber maps, using a changed edge table]
  unchecked: [A_F=C4, second swap lift order four, quotient projection, no section, E and torsor]
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: The original false-edge A1 square uniquely determines the vertex-1 fiber map from any Bool permutation at vertex 0; both Bool choices satisfy the true-edge square; the actual Lift fiber is equivalent to Bool permutations, has cardinality two, and its explicit second lift differs from the first
  completion_candidate: no
  lean_artifacts: [twoVertexSwapLiftOfPerm, twoVertexSwapFiberEquivPermBool, twoVertexSecondSwapLift]
  evidence: [twoVertex_swap_fiber_true, twoVertex_swap_fiber_card_two, twoVertex_second_swap_ne_first]
  claim_mapping:
    theorem_names: [twoVertexSwapFiberEquivPermBool, twoVertex_swap_fiber_card_two, twoVertex_second_swap_ne_first]
    source_labels: [completion condition 3 the two original lifts above the visible swap]
    conjuncts: [same original A1 fiber, complete two-element classification, concrete distinct second lift]
    undischarged_assumptions: [total C4 and quotient, second lift order four, no section, E and torsor]
    acceptance_point: Exactly two original A1 lifts exist over the visible swap
    port_status: unported
audits:
  premise_delta:
    discharged: [two original swap lifts and exhaustiveness]
    remaining: [their full group/quotient and E/torsor claims]
  certificate_provenance:
    discharged: [original false and true edge A1 equations, exhaustive Bool permutation classification]
    unresolved: [total group and second lift order]
  proof_use:
    used: [original A1 edge_naturality at false, direct true-edge naturality, Lift.ext]
    unused: [no supplied two-element fiber certificate]
  structure_field_escape: none-found-for-swap-fiber
  route_integrity: pass-for-second-example-C1-fiber
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [focused Lean check, six #print axioms and namespace standard-axiom assertion to be recorded in PR]
```

## Cycle 79 selection / proposed result

```yaml
ledger_type: target_cycle_result
goal: G-127-aat-reversible-protocol-holonomy
cycle: 79
goal_blob_sha: 86ed6948771755a19db802e01e42dbd00a8f9abf
base_oid: f9d433c8a
tracking_issue: 4981
report_path: research/reports/G-127-aat-reversible-protocol-holonomy.md
selection:
  proof_state_ref: Issue #4981 Cycle 78 exactly two original swap lifts
  proof_dag_predecessors: [twoVertex_H_exact, twoVertex_vertical_card_two, ReversibleData.verticalLiftEquivLiftableKernel, twoVertexCycleChange_order_four]
  proof_obligation: Prove the actual second-example A2 change group is cyclic of order four and identify it with C4
  selection_reason: Fixed condition 3 requires the total group, not merely one order-four element
  expected_result_type: proof-checkpoint
  lean_targets: [ResearchLean/AG/ProtocolHolonomy/TwoVertexTotalGroup.lean]
  risks: [assuming total cardinality from one element, using an abstract substitute extension, failing actual projection surjectivity, forgetting kernel provenance]
  unchecked: [projection quotient compatibility, second swap lift order four, no section, E and torsor]
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: The actual ChangeGroup projection reaches both visible elements, its kernel has cardinality two by the actual vertical A1 group isomorphism, and its range has cardinality two; subgroup index gives total cardinality four; the already proved order-four swap change generates the entire actual group; a cyclic-four group isomorphism is constructed
  completion_candidate: no
  lean_artifacts: [twoVertexProjection, twoVertexC4]
  evidence: [twoVertex_projection_surjective, twoVertex_projection_kernel_card_two, twoVertex_projection_range_card_two, twoVertex_changeGroup_card_four, twoVertexCycleChange_generates, twoVertex_changeGroup_isCyclic]
  claim_mapping:
    theorem_names: [twoVertex_changeGroup_card_four, twoVertexCycleChange_generates, twoVertexC4]
    source_labels: [completion condition 3 A_F=C4]
    conjuncts: [actual A2 ChangeGroup, actual visible projection, actual vertical kernel, four elements, chosen original swap lift generates all, group isomorphism with C4]
    undischarged_assumptions: [quotient compatibility, second swap lift order four, no section, E and torsor]
    acceptance_point: The specified total A_F is cyclic of order four
    port_status: unported
audits:
  premise_delta:
    discharged: [second-example A_F=C4]
    remaining: [projection quotient, second lift and nonsplitting, E and torsor]
  certificate_provenance:
    discharged: [actual ChangeGroup.projection kernel/range, original swap lift, vertical A1 equivalence, subgroup cardinal-index theorem]
    unresolved: [quotient compatibility]
  proof_use:
    used: [actual projection surjectivity, verticalLiftEquivLiftableKernel, group index/cardinality, order-four chosen generator]
    unused: [no supplied total-group cardinality certificate]
  structure_field_escape: none-found-for-total-group
  route_integrity: pass-for-second-example-C4
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [focused Lean check, seven #print axioms and namespace standard-axiom assertion to be recorded in PR]
```

## Cycle 27 selection / proposed result

```yaml
ledger_type: target_cycle_result
goal: G-127-aat-reversible-protocol-holonomy
cycle: 27
goal_blob_sha: 86ed6948771755a19db802e01e42dbd00a8f9abf
base_oid: 53aaadaeb
tracking_issue: 4981
report_path: research/reports/G-127-aat-reversible-protocol-holonomy.md
selection:
  proof_state_ref: Issue #4981 Cycle 26 identity transport and holonomy checkpoint
  proof_dag_predecessors: [identity_transport, ReversibleData.mem_liftableVisible_iff_lift, ReversibleData.Lift.toStateChange]
  proof_obligation: Construct arbitrary finite identity-operation A input with its original path equations and admissible H, prove every visible change lifts and H_lift equals H
  selection_reason: Connects identity transport calculation to the original C3 visible image without replacing equations or selecting a restricted subgroup
  expected_result_type: proof-checkpoint
  lean_targets: [ResearchLean/AG/ProtocolHolonomy/IdentityLiftability.lean]
  risks: [changing Π or H, assuming equation satisfaction, imposing nonempty K, replacing original H_lift]
  unchecked: [D identity component classification and section/split sequence/torsor, FixedF/G-124 comparison, arbitrary undirected named-tree bridge, E, fixed examples]
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: For arbitrary finite Q and K, arbitrary authored equations and H satisfying A's renaming condition, identity edge actions satisfy every equation; the original LiftableVisible subgroup is top in H because every visible element has its literal identity-fiber A1 lift
  completion_candidate: no
  lean_artifacts: [identityFiniteProtocolInput, identityLift]
  evidence: [identity_liftableVisible_eq_top, identityFiniteProtocolInput_liftableVisible_eq_top]
  claim_mapping:
    theorem_names: [identityFiniteProtocolInput, identityLift, identityFiniteProtocolInput_liftableVisible_eq_top]
    source_labels: [A original finite input, A1 lifts, C3 original visible projection image, D identity H_lift]
    conjuncts: [arbitrary finite named graph Q, arbitrary finite common K including empty, arbitrary A-admissible equations and H, original identity named operations, all visible changes have A1 lifts, original H_lift equals H]
    undischarged_assumptions: [D identity component classification/section/FixedF/G-124, arbitrary undirected named-tree bridge, E and fixed examples]
    acceptance_point: Identity operations satisfy the original finite A contract and give H_lift=H on the actual change-group projection; G-127 remains incomplete
    port_status: unported
audits:
  premise_delta:
    discharged: [D identity finite A input and H_lift=H]
    remaining: [D identity component classification and group section/split/FixedF/G-124, undirected-tree bridge, E and fixed examples]
  certificate_provenance:
    discharged: [equation truth from all-path identity transport, A1 identity fiber lifts, original projection-range definition of LiftableVisible]
    unresolved: [E finite table construction]
  proof_use:
    used: [Cycle 26 identity transport, A finite input contract, original C3 liftable-visible characterization]
    unused: [semantic realization because H_lift is the original C3 image]
  structure_field_escape: none-found
  route_integrity: pass-for-identity-liftability
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [focused Lean check and four-declaration standard axiom audit to be recorded in PR]
```

## Cycle 28 selection / proposed result

```yaml
ledger_type: target_cycle_result
goal: G-127-aat-reversible-protocol-holonomy
cycle: 28
goal_blob_sha: 86ed6948771755a19db802e01e42dbd00a8f9abf
base_oid: be8a4383c
tracking_issue: 4981
report_path: research/reports/G-127-aat-reversible-protocol-holonomy.md
selection:
  proof_state_ref: Issue #4981 Cycle 27 arbitrary identity input and H_lift=H
  proof_dag_predecessors: [identityLift, ReversibleData.Lift.toStateChange, ReversibleData.ChangeGroup.projection]
  proof_obligation: Construct an actual homomorphic identity-hidden section of the original visible projection for the arbitrary identity-operation system
  selection_reason: Turns the proven H_lift=H into the D split-extension map without replacing the original state-change group
  expected_result_type: proof-checkpoint
  lean_targets: [ResearchLean/AG/ProtocolHolonomy/IdentitySection.lean]
  risks: [section as arbitrary choice only, fake extension, wrong composition order, losing original edge names]
  unchecked: [D identity component classification and explicit split exact sequence/torsor, FixedF/G-124 comparison, arbitrary undirected named-tree bridge, E, fixed examples]
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: The literal identity-fiber state changes define a monoid homomorphism from the supplied H into the original actual operation-preserving ChangeGroup H, with state map (v,x) to (g v,x), and the original visible projection composed with this section is identity
  completion_candidate: no
  lean_artifacts: [identityChange, identitySection]
  evidence: [identityChange_state_apply, identitySection_rightInverse]
  claim_mapping:
    theorem_names: [identitySection, identitySection_rightInverse]
    source_labels: [A2 original actual change group, C3 original projection, D identity-hidden section]
    conjuncts: [arbitrary original H, original named-operation preserving state changes, literal identity hidden map, composition preservation, original visible projection right inverse]
    undischarged_assumptions: [D identity component classification/split exact sequence/torsor/FixedF/G-124, arbitrary undirected named-tree bridge, E and fixed examples]
    acceptance_point: The identity system has an actual group-homomorphic section of the original visible projection; G-127 remains incomplete
    port_status: unported
audits:
  premise_delta:
    discharged: [D identity-hidden section of original visible projection]
    remaining: [D identity component classification and explicit split exact sequence/torsor/FixedF/G-124, undirected-tree bridge, E and fixed examples]
  certificate_provenance:
    discharged: [A1 identity lift to actual state change, state-change group composition, original projection]
    unresolved: [E finite table construction]
  proof_use:
    used: [Cycle 27 identity lift, original Lift-to-StateChange bridge, original ChangeGroup projection]
    unused: [abstract group extension and chosen section]
  structure_field_escape: none-found
  route_integrity: pass-for-identity-section
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [focused Lean check and four-declaration standard axiom audit to be recorded in PR]
```

## Cycle 29 selection / proposed result

```yaml
ledger_type: target_cycle_result
goal: G-127-aat-reversible-protocol-holonomy
cycle: 29
goal_blob_sha: 86ed6948771755a19db802e01e42dbd00a8f9abf
base_oid: ef68153f7
tracking_issue: 4981
report_path: research/reports/G-127-aat-reversible-protocol-holonomy.md
selection:
  proof_state_ref: Issue #4981 Cycle 28 original identity-hidden section
  proof_dag_predecessors: [identityReversibleData, ReversibleData.Lift.edge_naturality, FixedFEdgeConstantPermutationFamily.equivComponentPermutationFamilies]
  proof_obligation: Classify all original vertical A1 lifts in the identity-operation system by one hidden permutation per original undirected graph component, preserving their actual vertexwise maps
  selection_reason: Connects D identity specialization to the existing FixedF component quotient without replacing the original vertical group
  expected_result_type: proof-checkpoint
  lean_targets: [ResearchLean/AG/ProtocolHolonomy/IdentityComponents.lean]
  risks: [classifying a replacement edge-constant input instead of actual A1 lifts, losing named-edge square, fixing component representatives, claiming group law from a type equivalence]
  unchecked: [D identity group-law correspondence and explicit split exact sequence/torsor, FixedF/G-124 comparison, arbitrary undirected named-tree bridge, E, fixed examples]
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: The full original vertical A1 lift type is equivalent to the existing edge-constant family and then to one permutation per undirected component; evaluation at a vertex reads exactly the original fiber equivalence
  completion_candidate: no
  lean_artifacts: [identityVerticalToEdgeConstant, identityEdgeConstantToVertical, identityVerticalEquivEdgeConstant, identityVerticalEquivComponents]
  evidence: [identityVerticalEquivComponents_apply]
  claim_mapping:
    theorem_names: [identityVerticalEquivComponents, identityVerticalEquivComponents_apply]
    source_labels: [C3 original vertical group carrier, D identity component-permutation classification]
    conjuncts: [all original vertical A1 lifts, original named-edge square, generated undirected component quotient, one permutation per component, same vertex maps]
    undischarged_assumptions: [identity group-law correspondence and split exact sequence/torsor/FixedF/G-124, arbitrary undirected named-tree bridge, E and fixed examples]
    acceptance_point: Identity vertical lifts have the stated component-permutation classification as a type equivalence, with group compatibility still explicit as a remaining obligation; G-127 remains incomplete
    port_status: unported
audits:
  premise_delta:
    discharged: [D identity vertical carrier and pointwise component classification]
    remaining: [D identity group-law correspondence and split exact sequence/torsor/FixedF/G-124, undirected-tree bridge, E and fixed examples]
  certificate_provenance:
    discharged: [A1 named-edge square gives edge constancy, inverse edge-constant family gives A1, existing original component quotient]
    unresolved: [E finite table construction]
  proof_use:
    used: [original A1 vertical lifts, FixedF component classification equivalence]
    unused: [section because this is the vertical kernel carrier]
  structure_field_escape: none-found
  route_integrity: pass-for-identity-component-carrier
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [focused Lean check and five-declaration standard axiom audit to be recorded in PR]
```

## Cycle 30 selection / proposed result

```yaml
ledger_type: target_cycle_result
goal: G-127-aat-reversible-protocol-holonomy
cycle: 30
goal_blob_sha: 86ed6948771755a19db802e01e42dbd00a8f9abf
base_oid: 65ca73d75
tracking_issue: 4981
report_path: research/reports/G-127-aat-reversible-protocol-holonomy.md
selection:
  proof_state_ref: Issue #4981 Cycle 29 original vertical carrier/component equivalence
  proof_dag_predecessors: [identityVerticalEquivComponents, ReversibleData.vertical_mul_fiber_apply]
  proof_obligation: Show the original identity-operation vertical group is isomorphic as a group to component-indexed hidden permutation families
  selection_reason: Discharges the group-law part of D's component permutation classification from the actual A2 state-change product
  expected_result_type: proof-checkpoint
  lean_targets: [ResearchLean/AG/ProtocolHolonomy/IdentityComponentGroup.lean]
  risks: [pointwise carrier equivalence without multiplication, replacement vertical group, wrong A2 composition order]
  unchecked: [D identity explicit split exact sequence/torsor and FixedF/G-124 comparison, arbitrary undirected named-tree bridge, E, fixed examples]
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: The full original vertical A1 lift group, whose law is actual total-state composition, is group-isomorphic to the component-indexed permutation product, reading the original fiber equivalence at every vertex
  completion_candidate: no
  lean_artifacts: [identityVerticalMulEquivComponents]
  evidence: [identityVerticalMulEquivComponents_apply]
  claim_mapping:
    theorem_names: [identityVerticalMulEquivComponents, identityVerticalMulEquivComponents_apply]
    source_labels: [A2 actual composition, C3 original vertical group, D identity component permutation group]
    conjuncts: [all original vertical A1 lifts, actual StateChange-derived group law, original undirected component quotient, pointwise permutation multiplication, original vertex maps]
    undischarged_assumptions: [D identity explicit split exact sequence/torsor/FixedF/G-124, arbitrary undirected named-tree bridge, E and fixed examples]
    acceptance_point: Identity vertical group is the component permutation group with actual A2 multiplication; G-127 remains incomplete
    port_status: unported
audits:
  premise_delta:
    discharged: [D identity vertical component group law]
    remaining: [D identity explicit split exact sequence/torsor/FixedF/G-124, undirected-tree bridge, E and fixed examples]
  certificate_provenance:
    discharged: [Cycle 29 full original vertical carrier equivalence, original actual vertical multiplication formula]
    unresolved: [E finite table construction]
  proof_use:
    used: [Cycle 29 original A1/component equivalence, actual StateChange-derived vertical multiplication]
    unused: [abstract group law on a replacement carrier]
  structure_field_escape: none-found
  route_integrity: pass-for-identity-component-group
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [focused Lean check and two-declaration standard axiom audit to be recorded in PR]
```

## Cycle 31 selection / proposed result

```yaml
ledger_type: target_cycle_result
goal: G-127-aat-reversible-protocol-holonomy
cycle: 31
goal_blob_sha: 86ed6948771755a19db802e01e42dbd00a8f9abf
base_oid: 4d293036e
tracking_issue: 4981
report_path: research/reports/G-127-aat-reversible-protocol-holonomy.md
selection:
  proof_state_ref: Issue #4981 Cycles 27–30 identity H_lift, section, component group
  proof_dag_predecessors: [ReversibleData.verticalLiftEquivLiftableKernel, ReversibleData.projectionToLiftable_ker, identitySection_rightInverse]
  proof_obligation: Exhibit the original identity-operation A1 vertical group, actual change group, and full supplied visible H as a split short exact sequence
  selection_reason: Makes D's exactness and split explicit on the original projection rather than the restricted liftable-visible presentation
  expected_result_type: proof-checkpoint
  lean_targets: [ResearchLean/AG/ProtocolHolonomy/IdentitySplitExact.lean]
  risks: [codomain only H_lift, substitute kernel, abstract split without actual section]
  unchecked: [D identity fiber torsor and FixedF/G-124 comparison, arbitrary undirected named-tree bridge, E, fixed examples]
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: Original vertical A1 lifts include into actual identity-operation ChangeGroup H; their image is exactly the original visible projection kernel, that projection is surjective onto full H, and the literal identity-hidden section is a group-homomorphic right inverse
  completion_candidate: no
  lean_artifacts: [identity_shortExact]
  evidence: [identity_shortExact_section]
  claim_mapping:
    theorem_names: [identity_shortExact, identity_shortExact_section]
    source_labels: [C3 original exact sequence, D identity split exact sequence]
    conjuncts: [original A1 vertical group, original actual named-operation change group, full supplied H, literal kernel, injectivity, surjectivity, homomorphic identity-hidden section]
    undischarged_assumptions: [D identity fiber torsor/FixedF/G-124, arbitrary undirected named-tree bridge, E and fixed examples]
    acceptance_point: The original identity-operation C3 sequence is exact and split over H, with actual maps; G-127 remains incomplete
    port_status: unported
audits:
  premise_delta:
    discharged: [D identity split short exact sequence]
    remaining: [D identity fiber torsor/FixedF/G-124, undirected-tree bridge, E and fixed examples]
  certificate_provenance:
    discharged: [original C3 vertical inclusion and kernel equivalence, original projection kernel equality, Cycle 28 literal identity-hidden section]
    unresolved: [E finite table construction]
  proof_use:
    used: [original C3 vertical inclusion and kernel equivalence, original projection, Cycle 28 actual section]
    unused: [abstract replacement extension]
  structure_field_escape: none-found
  route_integrity: pass-for-identity-split-sequence
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [focused Lean check and two-declaration standard axiom audit to be recorded in PR]
```

## Cycle 32 selection / proposed result

```yaml
ledger_type: target_cycle_result
goal: G-127-aat-reversible-protocol-holonomy
cycle: 32
goal_blob_sha: 86ed6948771755a19db802e01e42dbd00a8f9abf
base_oid: 62de92438
tracking_issue: 4981
report_path: research/reports/G-127-aat-reversible-protocol-holonomy.md
selection:
  proof_state_ref: Issue #4981 Cycles 27 and 31 identity H_lift=H and split sequence
  proof_dag_predecessors: [identityLift, ReversibleData.mem_liftableVisible_iff_lift, ReversibleData.verticalRightAction_existsUnique, ReversibleData.verticalRightAction_fiber_apply]
  proof_obligation: State the original C3 right torsor on every A1 lift fiber over every supplied g∈H in the identity-operation system, preserving the actual pointwise formula
  selection_reason: Turns the arbitrary liftable-visible torsor into the D identity specialization over all H using explicit original identity lifts
  expected_result_type: proof-checkpoint
  lean_targets: [ResearchLean/AG/ProtocolHolonomy/IdentityFiberTorsor.lean]
  risks: [restricting to a chosen fiber/visible element, replacing original vertical group, mere existential without action law, wrong composition order]
  unchecked: [D identity FixedF/G-124 comparison, arbitrary undirected named-tree bridge, E, fixed examples]
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: Every original g∈H is liftable by an explicit identity-fiber A1 lift; on its whole original A1 lift fiber the original vertical group has a right action with unit and multiplication laws, unique displacement between any two lifts, and literal vertex formula φ_v(α_v x)
  completion_candidate: no
  lean_artifacts: [identityLiftableVisible, identityRightAction]
  evidence: [identityRightAction_one, identityRightAction_mul, identityRightAction_existsUnique, identityRightAction_fiber_apply]
  claim_mapping:
    theorem_names: [identityRightAction_existsUnique, identityRightAction_fiber_apply]
    source_labels: [C3 original right torsor, D identity each-fiber torsor]
    conjuncts: [all supplied H elements, all A1 lifts over each visible element, original vertical A1 group, right action law, free/transitive unique displacement, original vertexwise composition]
    undischarged_assumptions: [D identity FixedF/G-124 comparison, arbitrary undirected named-tree bridge, E and fixed examples]
    acceptance_point: Identity-operation original C3 right torsor is available on every visible H-fiber, with the same maps and action law; G-127 remains incomplete
    port_status: unported
audits:
  premise_delta:
    discharged: [D identity each-fiber right torsor]
    remaining: [D identity FixedF/G-124, undirected-tree bridge, E and fixed examples]
  certificate_provenance:
    discharged: [Cycle 27 explicit identity lift for each H element, original C3 actual vertical right action and unique displacement]
    unresolved: [E finite table construction]
  proof_use:
    used: [Cycle 27 original identity A1 lift, original C3 vertical right action and torsor]
    unused: [replacement component-group action; Cycle 30 group equivalence is a separate identification]
  structure_field_escape: none-found
  route_integrity: pass-for-identity-fiber-torsor
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [focused Lean check and six-declaration standard axiom audit to be recorded in PR]
```

## Cycle 33 selection / proposed result

```yaml
ledger_type: target_cycle_result
goal: G-127-aat-reversible-protocol-holonomy
cycle: 33
goal_blob_sha: 86ed6948771755a19db802e01e42dbd00a8f9abf
base_oid: 42a61f494
tracking_issue: 4981
report_path: research/reports/G-127-aat-reversible-protocol-holonomy.md
selection:
  proof_state_ref: Issue #4981 Cycles 27–32 identity A input, group, split sequence, torsor
  proof_dag_predecessors: [ReversibleData.StateChange.toLift, ReversibleData.Lift.toStateChange, FixedFProtocolGroupConnection.ProtocolChangeGroup]
  proof_obligation: Give a direct bidirectional carrier correspondence between the original identity-operation actual change group and the existing independent FixedF protocol change group, retaining the original visible name rename and state map
  selection_reason: Starts D's Π-empty FixedF comparison using the two real groups rather than an abstract replacement extension
  expected_result_type: proof-checkpoint
  lean_targets: [ResearchLean/AG/ProtocolHolonomy/IdentityProtocolCarrier.lean]
  risks: [dropping original named edge squares, identifying only selected changes, claiming group compatibility before proof, changing universe/input]
  unchecked: [D FixedF group/projection/section/kernel/fiber action and G-124 comparison, arbitrary undirected named-tree bridge, E, fixed examples]
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: In the finite no-equation FixedF universe, every original actual identity-operation change and every independent FixedF ProtocolChangeGroup element correspond in both directions; visible automorphism including edge rename is identical, and protocol state adapters evaluate the original total-state map at every vertex and hidden state
  completion_candidate: no
  lean_artifacts: [identityChangeToProtocol, identityProtocolToChange, identityChangeEquivProtocol]
  evidence: [identityChangeEquivProtocol_visible, identityChangeEquivProtocol_state]
  claim_mapping:
    theorem_names: [identityChangeEquivProtocol, identityChangeEquivProtocol_visible, identityChangeEquivProtocol_state]
    source_labels: [D Π-empty existing FixedF protocol change group carrier]
    conjuncts: [original actual identity-operation ChangeGroup H, independent FixedF ProtocolChangeGroup H, all named-edge squares, original graph automorphism and edge names, same total-state map, both inverse directions]
    undischarged_assumptions: [D FixedF group/projection/section/kernel/fiber action and G-124, arbitrary undirected named-tree bridge, E and fixed examples]
    acceptance_point: The full two-input carrier correspondence is fixed without claiming its group law yet; G-127 remains incomplete
    port_status: unported
audits:
  premise_delta:
    discharged: [D identity/FixedF full carrier, visible and total-state readback]
    remaining: [D FixedF group/projection/section/kernel/fiber action and G-124, undirected-tree bridge, E and fixed examples]
  certificate_provenance:
    discharged: [actual StateChange.toLift and A1 Lift.toStateChange, independent protocol named-edge naturality]
    unresolved: [E finite table construction]
  proof_use:
    used: [original A1/actual StateChange equivalence, existing FixedF independent protocol group definition]
    unused: [abstract extension or selected subgroup]
  structure_field_escape: none-found
  route_integrity: pass-for-fixedf-carrier
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [focused Lean check and five-declaration standard axiom audit to be recorded in PR]
```

## Cycle 34 selection / proposed result

```yaml
ledger_type: target_cycle_result
goal: G-127-aat-reversible-protocol-holonomy
cycle: 34
goal_blob_sha: 86ed6948771755a19db802e01e42dbd00a8f9abf
base_oid: 58d30e2aa
tracking_issue: 4981
report_path: research/reports/G-127-aat-reversible-protocol-holonomy.md
selection:
  proof_state_ref: Issue #4981 Cycle 33 direct carrier correspondence
  proof_dag_predecessors: [identityChangeEquivProtocol, ReversibleData.Lift.comp_fiber_apply, ReversibleData.StateChange.toStateChange_toLift]
  proof_obligation: Prove the direct correspondence preserves the actual group product, including the original visible named-edge automorphism
  selection_reason: Completes the first group-level step of D's Π-empty FixedF comparison on the two original groups
  expected_result_type: proof-checkpoint
  lean_targets: [ResearchLean/AG/ProtocolHolonomy/IdentityProtocolGroup.lean]
  risks: [transported replacement group law, omission of visible edge rename, reversal of fiber composition order]
  unchecked: [D projection/section/kernel/fiber action and G-124 comparison, arbitrary undirected named-tree bridge, E, fixed examples]
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: The original actual identity-operation ChangeGroup H is group-isomorphic to the independent FixedF ProtocolChangeGroup H; multiplication follows the original A2 total-state composition and retains the full supplied visible H element
  completion_candidate: no
  lean_artifacts: [identityChangeMulEquivProtocol]
  evidence: [identityChangeMulEquivProtocol_visible]
  claim_mapping:
    theorem_names: [identityChangeMulEquivProtocol, identityChangeMulEquivProtocol_visible]
    source_labels: [D Π-empty existing FixedF protocol group law]
    conjuncts: [all original actual changes, independent FixedF protocol group, original multiplication, original visible vertex and named-edge automorphism]
    undischarged_assumptions: [D projection/section/kernel/fiber action and G-124, arbitrary undirected named-tree bridge, E and fixed examples]
    acceptance_point: Direct original-to-protocol group isomorphism is established; G-127 remains incomplete
    port_status: unported
audits:
  premise_delta:
    discharged: [D identity/FixedF direct group isomorphism]
    remaining: [D projection/section/kernel/fiber action and G-124, undirected-tree bridge, E and fixed examples]
  certificate_provenance:
    discharged: [Cycle 33 direct carrier equivalence, actual A2 lift composition formula]
    unresolved: [E finite table construction]
  proof_use:
    used: [original StateChange group multiplication, original A1 Lift bridge, independent FixedF protocol multiplication]
    unused: [replacement transported group structure]
  structure_field_escape: none-found
  route_integrity: pass-for-fixedf-group-law
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [focused Lean check and two-declaration standard axiom audit to be recorded in PR]
```

## Cycle 35 selection / proposed result

```yaml
ledger_type: target_cycle_result
goal: G-127-aat-reversible-protocol-holonomy
cycle: 35
goal_blob_sha: 86ed6948771755a19db802e01e42dbd00a8f9abf
base_oid: 3033ee9c6
tracking_issue: 4981
report_path: research/reports/G-127-aat-reversible-protocol-holonomy.md
selection:
  proof_state_ref: Issue #4981 Cycle 34 direct original-to-protocol group isomorphism
  proof_dag_predecessors: [identityChangeMulEquivProtocol, identitySection, ProtocolChangeGroup.projection, ProtocolChangeGroup.canonicalSection]
  proof_obligation: Show the group isomorphism preserves the two original visible projections and maps the actual identity-hidden section to the independently defined protocol canonical section
  selection_reason: Verifies the original structure maps rather than inferring them from an uninspected abstract group equivalence
  expected_result_type: proof-checkpoint
  lean_targets: [ResearchLean/AG/ProtocolHolonomy/IdentityProtocolCompatibility.lean]
  risks: [projection equality only on vertices, section of a replacement group, loss of named operation rename]
  unchecked: [D kernel/fiber action and G-124 comparison, arbitrary undirected named-tree bridge, E, fixed examples]
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: Both visible projections literally return the same original H element, and the actual identity-hidden section over every g∈H maps to the existing independent protocol canonical section
  completion_candidate: no
  lean_artifacts: [identityProtocol_projection, identityProtocol_section]
  evidence: [identityProtocol_projection, identityProtocol_section]
  claim_mapping:
    theorem_names: [identityProtocol_projection, identityProtocol_section]
    source_labels: [D Π-empty FixedF projection and section compatibility]
    conjuncts: [original actual projection, independent protocol projection, all supplied H elements and named-edge renames, actual identity-hidden section, independent canonical section]
    undischarged_assumptions: [D kernel/fiber action and G-124, arbitrary undirected named-tree bridge, E and fixed examples]
    acceptance_point: Original-to-protocol projection and section compatibility is proved; G-127 remains incomplete
    port_status: unported
audits:
  premise_delta:
    discharged: [D identity/FixedF projection and section compatibility]
    remaining: [D kernel/fiber action and G-124, undirected-tree bridge, E and fixed examples]
  certificate_provenance:
    discharged: [Cycle 34 direct group isomorphism, actual identitySection, independent ProtocolChangeGroup.canonicalSection]
    unresolved: [E finite table construction]
  proof_use:
    used: [both independently defined projection maps and section maps]
    unused: [replacement extension or chosen visible generator]
  structure_field_escape: none-found
  route_integrity: pass-for-fixedf-projection-section
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [focused Lean check and two-declaration standard axiom audit to be recorded in PR]
```

## Cycle 36 selection / proposed result

```yaml
ledger_type: target_cycle_result
goal: G-127-aat-reversible-protocol-holonomy
cycle: 36
goal_blob_sha: 86ed6948771755a19db802e01e42dbd00a8f9abf
base_oid: f06179695
tracking_issue: 4981
report_path: research/reports/G-127-aat-reversible-protocol-holonomy.md
selection:
  proof_state_ref: Issue #4981 Cycles 34–35 direct group and projection compatibility
  proof_dag_predecessors: [identityChangeMulEquivProtocol, identityProtocol_projection]
  proof_obligation: Restrict the direct original-to-protocol isomorphism to the literal kernels of the independently defined visible projections
  selection_reason: Fixes D's kernel comparison at the original group level before comparing the original vertical inclusion and every fiber action
  expected_result_type: proof-checkpoint
  lean_targets: [ResearchLean/AG/ProtocolHolonomy/IdentityProtocolKernel.lean]
  risks: [replacing the original kernel by an abstract subgroup, only set-level correspondence, projection from a different H]
  unchecked: [D vertical inclusion/fiber action and G-124 comparison, arbitrary undirected named-tree bridge, E, fixed examples]
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: The direct group isomorphism restricts to a group isomorphism of literal projection kernels, with membership proved by equality of the two original H-valued projections
  completion_candidate: no
  lean_artifacts: [identityProtocolKernelMulEquiv]
  evidence: [identityProtocolKernelMulEquiv]
  claim_mapping:
    theorem_names: [identityProtocolKernelMulEquiv]
    source_labels: [D Π-empty FixedF literal kernel comparison]
    conjuncts: [original actual projection kernel, independent protocol projection kernel, group law, all elements in both directions]
    undischarged_assumptions: [D vertical inclusion/fiber action and G-124, arbitrary undirected named-tree bridge, E and fixed examples]
    acceptance_point: Direct literal kernel correspondence is proved; G-127 remains incomplete
    port_status: unported
audits:
  premise_delta:
    discharged: [D identity/FixedF literal projection kernel isomorphism]
    remaining: [D vertical inclusion/fiber action and G-124, undirected-tree bridge, E and fixed examples]
  certificate_provenance:
    discharged: [Cycle 34 group isomorphism, Cycle 35 H-valued projection compatibility]
    unresolved: [E finite table construction]
  proof_use:
    used: [literal MonoidHom.ker on both independently defined projection homomorphisms]
    unused: [abstract replacement kernel]
  structure_field_escape: none-found
  route_integrity: pass-for-fixedf-literal-kernel
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [focused Lean check and one-declaration standard axiom audit to be recorded in PR]
```

## Cycle 37 selection / proposed result

```yaml
ledger_type: target_cycle_result
goal: G-127-aat-reversible-protocol-holonomy
cycle: 37
goal_blob_sha: 86ed6948771755a19db802e01e42dbd00a8f9abf
base_oid: 978076fd9
tracking_issue: 4981
report_path: research/reports/G-127-aat-reversible-protocol-holonomy.md
selection:
  proof_state_ref: Issue #4981 Cycles 31 and 36 original split kernel and direct protocol kernel equivalence
  proof_dag_predecessors: [ReversibleData.verticalLiftInclusion, ReversibleData.verticalLiftEquivLiftableKernel, identityProtocolKernelMulEquiv]
  proof_obligation: Map each original vertical A1 lift into the literal independent protocol kernel and preserve its pointwise fiber map and multiplication
  selection_reason: Connects the original C3 vertical group itself to D's FixedF protocol kernel rather than only comparing projection kernels abstractly
  expected_result_type: proof-checkpoint
  lean_targets: [ResearchLean/AG/ProtocolHolonomy/IdentityProtocolVertical.lean]
  risks: [replacing the original C3 vertical group, losing pointwise maps, assuming injectivity or surjectivity without proof]
  unchecked: [D vertical-kernel equivalence/fiber action and G-124 comparison, arbitrary undirected named-tree bridge, E, fixed examples]
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: The original vertical A1 inclusion followed by direct literal-kernel equivalence is a group homomorphism into the independent FixedF protocol kernel, and its vertexwise state maps equal the original A1 fiber maps pointwise
  completion_candidate: no
  lean_artifacts: [identityVerticalToProtocolKernel]
  evidence: [identityVerticalToProtocolKernel_fiber]
  claim_mapping:
    theorem_names: [identityVerticalToProtocolKernel, identityVerticalToProtocolKernel_fiber]
    source_labels: [D original vertical group to FixedF protocol kernel]
    conjuncts: [original C3 vertical A1 group, original actual inclusion, independent literal protocol kernel, group homomorphism, every vertex and hidden state map]
    undischarged_assumptions: [D vertical-kernel equivalence/fiber action and G-124, arbitrary undirected named-tree bridge, E and fixed examples]
    acceptance_point: Original vertical group map and pointwise readback are fixed; G-127 remains incomplete
    port_status: unported
audits:
  premise_delta:
    discharged: [D original vertical inclusion to independent protocol kernel with pointwise readback]
    remaining: [D vertical-kernel equivalence/fiber action and G-124, undirected-tree bridge, E and fixed examples]
  certificate_provenance:
    discharged: [original C3 verticalLiftInclusion, Cycle 36 direct literal-kernel equivalence]
    unresolved: [E finite table construction]
  proof_use:
    used: [original verticalLiftEquivLiftableKernel membership, original C3 inclusion, direct independent protocol kernel equivalence]
    unused: [replacement vertical group or chosen generator]
  structure_field_escape: none-found
  route_integrity: pass-for-fixedf-original-vertical-map
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [focused Lean check and two-declaration standard axiom audit to be recorded in PR]
```

## Cycle 38 selection / proposed result

```yaml
ledger_type: target_cycle_result
goal: G-127-aat-reversible-protocol-holonomy
cycle: 38
goal_blob_sha: 86ed6948771755a19db802e01e42dbd00a8f9abf
base_oid: f26b47d21
tracking_issue: 4981
report_path: research/reports/G-127-aat-reversible-protocol-holonomy.md
selection:
  proof_state_ref: Issue #4981 Cycle 37 original vertical homomorphism and pointwise readback
  proof_dag_predecessors: [identityVerticalToProtocolKernel, ReversibleData.verticalLiftEquivLiftableKernel, ReversibleData.projectionToLiftable_ker, identityProtocolKernelMulEquiv]
  proof_obligation: Prove the original vertical A1 group maps bijectively onto the independent FixedF protocol projection kernel
  selection_reason: Completes D's identity-kernel group identification with a genuine inverse from the original C3 kernel theorem
  expected_result_type: proof-checkpoint
  lean_targets: [ResearchLean/AG/ProtocolHolonomy/IdentityProtocolVertical.lean]
  risks: [assuming surjectivity from the section, identifying the wrong projection kernel, loss of original fiber readback]
  unchecked: [D fiber action and G-124 comparison, arbitrary undirected named-tree bridge, E, fixed examples]
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: The original vertical A1 group is group-isomorphic to the literal independent protocol kernel; injectivity and surjectivity factor through the original C3 vertical-to-actual-kernel equivalence and the direct original-to-protocol kernel equivalence, retaining Cycle 37 pointwise readback
  completion_candidate: no
  lean_artifacts: [identityVerticalProtocolKernelMulEquiv]
  evidence: [identityVerticalProtocolKernelMulEquiv, identityVerticalToProtocolKernel_fiber]
  claim_mapping:
    theorem_names: [identityVerticalProtocolKernelMulEquiv, identityVerticalToProtocolKernel_fiber]
    source_labels: [D Π-empty original vertical group and independent FixedF protocol kernel]
    conjuncts: [original C3 vertical A1 group, independent protocol literal kernel, group multiplication, both inverse directions, original pointwise fiber maps]
    undischarged_assumptions: [D fiber action and G-124, arbitrary undirected named-tree bridge, E and fixed examples]
    acceptance_point: Full original vertical-to-protocol kernel group equivalence is proved; G-127 remains incomplete
    port_status: unported
audits:
  premise_delta:
    discharged: [D identity FixedF original vertical-to-protocol kernel equivalence]
    remaining: [D fiber action and G-124, undirected-tree bridge, E and fixed examples]
  certificate_provenance:
    discharged: [original C3 verticalLiftEquivLiftableKernel, equality of original actual kernels, Cycle 36 direct protocol kernel equivalence]
    unresolved: [E finite table construction]
  proof_use:
    used: [actual original C3 kernel isomorphism, literal protocol kernel isomorphism, Cycle 37 homomorphism]
    unused: [section-based surjectivity or abstract replacement group]
  structure_field_escape: none-found
  route_integrity: pass-for-fixedf-vertical-kernel-equivalence
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [focused Lean check and three-declaration standard axiom audit to be recorded in PR]
```

## Cycle 39 selection / proposed result

```yaml
ledger_type: target_cycle_result
goal: G-127-aat-reversible-protocol-holonomy
cycle: 39
goal_blob_sha: 86ed6948771755a19db802e01e42dbd00a8f9abf
base_oid: b838a03cb
tracking_issue: 4981
report_path: research/reports/G-127-aat-reversible-protocol-holonomy.md
selection:
  proof_state_ref: Issue #4981 Cycles 25, 32, 36–38 original and independent right actions and kernel isomorphism
  proof_dag_predecessors: [identityRightAction, identityVerticalProtocolKernelMulEquiv, ProtocolChangeGroup.projectionFiberSMul, identityChangeMulEquivProtocol]
  proof_obligation: Compare the original C3 right vertical action on every identity-operation A1 lift fiber with the independent FixedF protocol right literal-kernel action
  selection_reason: Finishes the pointwise action-compatibility clause of D's Π-empty FixedF comparison on the actual original lifts and independently defined projection fibers
  expected_result_type: proof-checkpoint
  lean_targets: [ResearchLean/AG/ProtocolHolonomy/IdentityProtocolFiberAction.lean]
  risks: [using a selected fiber only, switching left/right composition, replacing literal kernel, dropping named-edge visible action]
  unchecked: [D full fiber equivalence and G-124 comparison, arbitrary undirected named-tree bridge, E, fixed examples]
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: Every original A1 lift over every g∈H maps to the independent literal protocol projection fiber, and the original vertical right action equals the protocol kernel right action under the original-to-protocol vertical group equivalence; equality is at the full protocol element and uses the original vertexwise fiber composition formula
  completion_candidate: no
  lean_artifacts: [identityLiftToProtocolFiber]
  evidence: [identityLiftToProtocolFiber_action]
  claim_mapping:
    theorem_names: [identityLiftToProtocolFiber, identityLiftToProtocolFiber_action]
    source_labels: [D Π-empty FixedF every-fiber right action]
    conjuncts: [every supplied g∈H, all original A1 lifts over g, independent literal projection fiber, original vertical A1 group, independent literal kernel, right action, each vertex/state map, full visible automorphism]
    undischarged_assumptions: [D full fiber equivalence and G-124, arbitrary undirected named-tree bridge, E and fixed examples]
    acceptance_point: Original and independent FixedF right actions coincide on the direct lift-to-protocol fiber map; G-127 remains incomplete
    port_status: unported
audits:
  premise_delta:
    discharged: [D identity FixedF right-action compatibility]
    remaining: [D full fiber equivalence and G-124, undirected-tree bridge, E and fixed examples]
  certificate_provenance:
    discharged: [original C3 right action, original-to-independent group and vertical-kernel equivalences, independent literal kernel action]
    unresolved: [E finite table construction]
  proof_use:
    used: [original identityRightAction, original verticalRightAction_fiber_apply, independent ProjectionFiber action, direct group and kernel maps]
    unused: [selected basepoint or replacement action]
  structure_field_escape: none-found
  route_integrity: pass-for-fixedf-fiber-action
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [focused Lean check and two-declaration standard axiom audit to be recorded in PR]
```

## Cycle 40 selection / proposed result

```yaml
ledger_type: target_cycle_result
goal: G-127-aat-reversible-protocol-holonomy
cycle: 40
goal_blob_sha: 86ed6948771755a19db802e01e42dbd00a8f9abf
base_oid: a599d56a0
tracking_issue: 4981
report_path: research/reports/G-127-aat-reversible-protocol-holonomy.md
selection:
  proof_state_ref: Issue #4981 Cycle 39 direct action-compatibility map on every original A1 lift fiber
  proof_dag_predecessors: [identityLiftToProtocolFiber, identityProtocolToChange, ReversibleData.StateChange.toLift, ReversibleData.Lift.toStateChange]
  proof_obligation: Prove the direct original lift-to-protocol map is a full equivalence on every literal visible projection fiber, retaining each vertexwise state map
  selection_reason: Ensures D's every-fiber action comparison is on complete original and independent fibers, not only a selected subcarrier
  expected_result_type: proof-checkpoint
  lean_targets: [ResearchLean/AG/ProtocolHolonomy/IdentityProtocolFiberEquiv.lean]
  risks: [replacing the original fiber by a selected lift, forgetting original named edges, one-way map presented as equivalence, hidden cast changing state maps]
  unchecked: [D G-124 representative comparison, arbitrary undirected named-tree bridge, E, fixed examples]
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: For every supplied g∈H, all original A1 lifts and all independent FixedF protocol changes in the literal projection fiber correspond in both directions; the visible automorphism and every vertex/state map are retained, and Cycle 39 right-action compatibility holds on the whole fibers
  completion_candidate: no
  lean_artifacts: [identityLiftEquivProtocolFiber]
  evidence: [identityLiftEquivProtocolFiber_state, identityLiftToProtocolFiber_action]
  claim_mapping:
    theorem_names: [identityLiftEquivProtocolFiber, identityLiftEquivProtocolFiber_state, identityLiftToProtocolFiber_action]
    source_labels: [D Π-empty FixedF all projection fibers and right actions]
    conjuncts: [every g∈H, all original A1 lifts, literal independent protocol projection fiber, both inverse directions, full named-edge visible automorphism, all vertexwise state maps, original/protocol right action]
    undischarged_assumptions: [D G-124 representative comparison, arbitrary undirected named-tree bridge, E and fixed examples]
    acceptance_point: Original-to-independent FixedF group/projection/section/kernel/each-fiber action comparison is established; G-127 remains incomplete
    port_status: unported
audits:
  premise_delta:
    discharged: [D identity FixedF all-fiber equivalence]
    remaining: [D G-124 comparison, undirected-tree bridge, E and fixed examples]
  certificate_provenance:
    discharged: [Cycle 33 direct carrier equivalence, original A1 Lift/StateChange bridge, Cycle 39 action compatibility]
    unresolved: [E finite table construction]
  proof_use:
    used: [original-to-independent protocol carrier conversion in both directions, literal ProjectionFiber, original A1 lift and actual state-change inverse laws]
    unused: [selected basepoint or replacement fiber]
  structure_field_escape: none-found
  route_integrity: pass-for-fixedf-all-fibers
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [focused Lean check and two-declaration standard axiom audit to be recorded in PR]
```

## Cycle 41 selection / proposed result

```yaml
ledger_type: target_cycle_result
goal: G-127-aat-reversible-protocol-holonomy
cycle: 41
goal_blob_sha: 86ed6948771755a19db802e01e42dbd00a8f9abf
base_oid: f9ca04d94
tracking_issue: 4981
report_path: research/reports/G-127-aat-reversible-protocol-holonomy.md
selection:
  proof_state_ref: Issue #4981 Cycle 40 complete FixedF protocol comparison; G-124 D/E determining representative API
  proof_dag_predecessors: [identityReversibleData, FixedFFollowingStateChange.preservingEquivEdgeConstantFamilies, FinitePermutationReadingCriteria.readAt]
  proof_obligation: Construct a direct all-visible bridge between original identity-operation A1 lifts and G-124 actual operation-preserving following changes, preserving every vertex reading
  selection_reason: G-124 representative determining and C2 extension cannot be compared merely by juxtaposing their theorems without matching their actual carriers and readAt maps
  expected_result_type: proof-checkpoint
  lean_targets: [ResearchLean/AG/ProtocolHolonomy/IdentityG124Bridge.lean]
  risks: [vertical-identity-only bridge, replacing actual preserving changes with an abstract family, dropping named-edge squares, assuming readAt equality]
  unchecked: [D G-124 representative B2/C2 extension comparison, arbitrary undirected named-tree bridge, E, fixed examples]
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: For every fixed visible graph automorphism g, the original identity-operation A1 lifts and G-124 actual named-operation-preserving following changes are equivalent through the same edge-constant family; G-124 readAt at every vertex equals the original A1 fiber permutation
  completion_candidate: no
  lean_artifacts: [identityLiftEquivG124Family, identityLiftEquivG124Preserving]
  evidence: [identityG124_readAt]
  claim_mapping:
    theorem_names: [identityLiftEquivG124Preserving, identityG124_readAt]
    source_labels: [D G-124 actual preserving-change comparison input]
    conjuncts: [arbitrary original visible graph automorphism, all original A1 lifts, all G-124 actual preserving changes, named-edge naturality, both inverse directions, every vertex readAt and original fiber map]
    undischarged_assumptions: [D G-124 representative B2/C2 extension comparison, arbitrary undirected named-tree bridge, E and fixed examples]
    acceptance_point: The two actual carriers and their vertex readings coincide; representative extension/C2 equality remains; G-127 remains incomplete
    port_status: unported
audits:
  premise_delta:
    discharged: [D G-124 actual preserving-change carrier and readAt bridge]
    remaining: [D G-124 representative B2/C2 extension, undirected-tree bridge, E and fixed examples]
  certificate_provenance:
    discharged: [original A1 named-edge squares and G-124 preservingEquivEdgeConstantFamilies]
    unresolved: [E finite table construction]
  proof_use:
    used: [actual G-124 PreservingChange, original A1 Lift, source-owned edge-constant family, G-124 readAt]
    unused: [replacement group or selected representative]
  structure_field_escape: none-found
  route_integrity: pass-for-g124-carrier-reading
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [focused Lean check and five-declaration standard axiom audit to be recorded in PR]
```

## Cycle 42 selection / proposed result

```yaml
ledger_type: target_cycle_result
goal: G-127-aat-reversible-protocol-holonomy
cycle: 42
goal_blob_sha: 86ed6948771755a19db802e01e42dbd00a8f9abf
base_oid: 590f17280
tracking_issue: 4981
report_path: research/reports/G-127-aat-reversible-protocol-holonomy.md
selection:
  proof_state_ref: Issue #4981 Cycle 41 G-124 actual preserving-change and readAt bridge
  proof_dag_predecessors: [InducedComponent.representative, CSFixedFDetermining.protocolRepresentativeSet, rootedPathsOfRoots, ReversibleData.verticalRootMulEquiv, identityG124_readAt]
  proof_obligation: Identify G-124's exact determining representative vertices with B2 roots and show their readings agree on each original vertical A1 lift
  selection_reason: Moves the G-124/B2 comparison from carrier coincidence to the actual selected representative/root values
  expected_result_type: proof-checkpoint
  lean_targets: [ResearchLean/AG/ProtocolHolonomy/IdentityG124Representatives.lean]
  risks: [using a different representative choice, claiming all-vertex extension from root equality alone, conflating finite-table runtime with noncomputable structural roots]
  unchecked: [D G-124 determining extension/C2 comparison, arbitrary undirected named-tree bridge, E, fixed examples]
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: A RootedPaths choice uses exactly G-124's InducedComponent.representative for each component; every root lies in G-124's finite protocolRepresentativeSet, and B2 verticalRootMulEquiv reads exactly G-124 readAt on the corresponding actual preserving change at that representative
  completion_candidate: no
  lean_artifacts: [g124RepresentativeRootedPaths]
  evidence: [g124_root_mem_representativeSet, identityG124_B2_representative_reading]
  claim_mapping:
    theorem_names: [g124RepresentativeRootedPaths, g124_root_mem_representativeSet, identityG124_B2_representative_reading]
    source_labels: [D G-124 determining representatives match B2 identity roots]
    conjuncts: [same original component quotient, exact G-124 chosen representative and finite set, B2 root centralizer coordinate, actual G-124 readAt, original A1 fiber]
    undischarged_assumptions: [D G-124 determining extension/C2, arbitrary undirected named-tree bridge, E and fixed examples]
    acceptance_point: G-124 and B2 share literal selected root values; all-vertex extension/C2 equality remains; G-127 remains incomplete
    port_status: unported
audits:
  premise_delta:
    discharged: [D G-124 chosen representative and B2 root reading comparison]
    remaining: [D G-124 determining extension/C2, undirected-tree bridge, E and fixed examples]
  certificate_provenance:
    discharged: [G-124 InducedComponent.representative and protocolRepresentativeSet, Cycle 41 actual readAt equality, B2 original root evaluation]
    unresolved: [E finite table construction]
  proof_use:
    used: [original G-124 representative choice, original finite representative set, original B2 verticalRootMulEquiv, actual G-124 readAt]
    unused: [new representative choice or executable forest claim]
  structure_field_escape: none-found
  route_integrity: pass-for-g124-b2-representatives
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [focused Lean check and three-declaration standard axiom audit to be recorded in PR]
```

## Cycle 43 selection / proposed result

```yaml
ledger_type: target_cycle_result
goal: G-127-aat-reversible-protocol-holonomy
cycle: 43
goal_blob_sha: 86ed6948771755a19db802e01e42dbd00a8f9abf
base_oid: 303ee2642
tracking_issue: 4981
report_path: research/reports/G-127-aat-reversible-protocol-holonomy.md
selection:
  proof_state_ref: Issue #4981 Cycles 41–42 actual G-124 carrier/readAt and matching representative roots
  proof_dag_predecessors: [identity_transport, ReversibleData.RootSolutions.reconstructedFiber, FixedFFollowingStateChange.preservingEquivComponentPermutationFamilies, FinitePermutationReadingCriteria.readAt]
  proof_obligation: Prove identity-operation C2 reconstruction from every component-root family agrees at every vertex with G-124's actual preserving-change extension from the same component family
  selection_reason: Discharges the all-vertex extension formula rather than only root-value agreement
  expected_result_type: proof-checkpoint
  lean_targets: [ResearchLean/AG/ProtocolHolonomy/IdentityG124Extension.lean]
  risks: [using a different source component quotient, assuming C1 instead of proving it, treating classical roots as E runtime, only checking representatives]
  unchecked: [D G-124 determining predicate synchronization, arbitrary undirected named-tree bridge, E, fixed examples]
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: Every component permutation family satisfies the original C1 edge-loop equations for identity operations; C2 reconstructs α(component(v)) at every vertex, and G-124's actual preserving change reconstructed through the accepted component classification has the identical readAt value at every vertex
  completion_candidate: no
  lean_artifacts: [identityComponentRootSolutions]
  evidence: [identity_C2_component_extension, identity_G124_C2_extension_agree]
  claim_mapping:
    theorem_names: [identityComponentRootSolutions, identity_C2_component_extension, identity_G124_C2_extension_agree]
    source_labels: [D G-124 representative extension equals C2 identity specialization]
    conjuncts: [original C1 root equations, original signed transport, original C2 reconstruction, original full component quotient, actual G-124 preserving change, all vertices and hidden permutations]
    undischarged_assumptions: [D G-124 determining predicate synchronization, arbitrary undirected named-tree bridge, E and fixed examples]
    acceptance_point: All-vertex extension formulas agree on the same component family; G-124 determining theorem synchronization remains; G-127 remains incomplete
    port_status: unported
audits:
  premise_delta:
    discharged: [D identity C2 and actual G-124 all-vertex extension equality]
    remaining: [D G-124 determining predicate synchronization, undirected-tree bridge, E and fixed examples]
  certificate_provenance:
    discharged: [Cycle 26 identity transport on all signed paths, original C1 RootSolutions condition, G-124 accepted component-family classification]
    unresolved: [E finite table construction]
  proof_use:
    used: [identity transport on original and renamed paths, original RootSolutions.reconstructedFiber, G-124 actual PreservingChange classification and readAt]
    unused: [replacement extension or selected representative only]
  structure_field_escape: none-found
  route_integrity: pass-for-g124-c2-all-vertices
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [focused Lean check and four-declaration standard axiom audit to be recorded in PR]
```

## Cycle 44 selection / proposed result

```yaml
ledger_type: target_cycle_result
goal: G-127-aat-reversible-protocol-holonomy
cycle: 44
goal_blob_sha: 86ed6948771755a19db802e01e42dbd00a8f9abf
base_oid: a4d2f7df3
tracking_issue: 4981
report_path: research/reports/G-127-aat-reversible-protocol-holonomy.md
selection:
  proof_state_ref: Issue #4981 Cycles 41–43 G-124 actual carrier, representative root values and all-vertex C2 extension comparison
  proof_dag_predecessors: [CSFixedFDetermining.protocol_representatives_determining, identityLiftEquivG124Preserving, identityG124_readAt]
  proof_obligation: Transport G-124's exact determining predicate, including separation and coherent table extension, to original identity-operation A1 lifts on the same finite representative set
  selection_reason: Closes the accepted G-124 D/E representative theorem comparison rather than relying on equal example values alone
  expected_result_type: proof-checkpoint
  lean_targets: [ResearchLean/AG/ProtocolHolonomy/IdentityG124Determining.lean]
  risks: [omitting extension or coherence, adding Nontrivial K to B2/C2, using a different selected finite set, replacing original lifts with abstract families]
  unchecked: [arbitrary undirected named-tree bridge, E, fixed examples]
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: On exactly G-124's finite protocolRepresentativeSet, original A1 lift vertex readings have the same FiniteReading.Determining property as accepted G-124 actual preserving changes: injective restriction and extension of every accepted EdgeCoherent table; Nontrivial K appears only in this accepted determining statement
  completion_candidate: no
  lean_artifacts: [identityLift_representatives_determining]
  evidence: [identityLift_representatives_determining, identityG124_readAt, identity_G124_C2_extension_agree]
  claim_mapping:
    theorem_names: [identityLift_representatives_determining, identityG124_B2_representative_reading, identity_G124_C2_extension_agree]
    source_labels: [D G-124 D/E representative reading and extension agree with B2/C2 identity specialization]
    conjuncts: [same actual preserving changes and original A1 lifts, exact selected representative Finset, actual readAt equals original fiber, B2 root coordinate, G-124 separation, coherent table extension, C2/G-124 all-vertex equality]
    undischarged_assumptions: [arbitrary undirected named-tree bridge, E and fixed examples]
    acceptance_point: D G-124 representative comparison is established across Cycles 41–44; G-127 remains incomplete
    port_status: unported
audits:
  premise_delta:
    discharged: [D G-124 determining representatives versus B2/C2 identity comparison]
    remaining: [undirected-tree bridge, E and fixed examples]
  certificate_provenance:
    discharged: [accepted G-124 determining theorem with its original Nontrivial K restriction, Cycle 41 actual carrier/readAt bridge, Cycles 42–43 root and extension formulas]
    unresolved: [E finite table construction]
  proof_use:
    used: [both halves of G-124 FiniteReading.Determining, same finite representative set and EdgeCoherent predicate, original A1 Lift via direct equivalence]
    unused: [new weaker determining predicate or extra Nontrivial K in B2/C2]
  structure_field_escape: none-found
  route_integrity: pass-for-g124-determining-comparison
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [focused Lean check and one-declaration standard axiom audit to be recorded in PR]
```

## Cycle 45 selection / proposed result

```yaml
ledger_type: target_cycle_result
goal: G-127-aat-reversible-protocol-holonomy
cycle: 45
goal_blob_sha: 86ed6948771755a19db802e01e42dbd00a8f9abf
base_oid: f9555bd1c
tracking_issue: 4981
report_path: research/reports/G-127-aat-reversible-protocol-holonomy.md
selection:
  proof_state_ref: Issue #4981 Cycle 44 closure of G-124 identity comparison; SpanningTrees.lean outward arborescence only
  proof_dag_predecessors: [RootedPaths, SpanningTrees, B1/B2/C1 root-path theorems]
  proof_obligation: Supply arbitrary undirected named-edge tree selections and arbitrary roots to the original B/C rooted-path API while retaining original edge names and signs
  selection_reason: Removes the oriented-arborescence restriction on structural B/C inputs without modifying their statements
  expected_result_type: proof-checkpoint
  lean_targets: [ResearchLean/AG/ProtocolHolonomy/UndirectedNamedTrees.lean]
  risks: [mistaking outward arborescence for undirected tree, losing parallel edge names, assuming chosen paths are executable, hiding the connectedness or acyclicity requirement]
  unchecked: [constructing such a forest from every finite table, executable E, two fixed examples]
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: An intrinsic undirected tree selects original edge names, requires within-component connectivity and every selected edge to be a bridge, and yields RootedPaths for any roots with every root path using only selected signed named edges
  completion_candidate: no
  lean_artifacts: [UsesNamedEdges, UndirectedNamedSpanningTree, UndirectedNamedSpanningForest.toRootedPaths]
  evidence: [UndirectedNamedSpanningTree.pathFromRoot_usesEdges, UndirectedNamedSpanningForest.toRootedPaths_path_usesEdges]
  claim_mapping:
    theorem_names: [UndirectedNamedSpanningForest.toRootedPaths, UndirectedNamedSpanningForest.toRootedPaths_path_usesEdges]
    source_labels: [B arbitrary roots and undirected named spanning trees, D choice change]
    conjuncts: [original named edges and orientation-sensitive signed passages, independent edge selection, arbitrary component roots, normalized empty root path, selected-edge provenance]
    undischarged_assumptions: [finite-table construction and proof of forest existence, E decision procedure, fixed examples]
    acceptance_point: Every genuine undirected named forest supplies B/C input; existence and executable construction remain open
    port_status: unported
audits:
  premise_delta:
    discharged: [arbitrary undirected named forest and arbitrary roots map to original B/C root-path data]
    remaining: [input-generated forest existence and executable E, fixed examples]
  certificate_provenance:
    discharged: [conversion of a supplied selected-edge path witness to RootedPaths while preserving original Q.Edge names]
    unresolved: [forest connectivity witness and executable finite-table forest constructor from the original graph input]
  proof_use:
    used: [tree connectedness, selected-edge witness, normalized root path]
    unused: [bridge condition is part of the intrinsic tree predicate and not needed for B/C path theorems]
  structure_field_escape: none-found
  route_integrity: pass-for-undirected-tree-to-rooted-paths
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [focused Lean check and four-declaration standard axiom audit to be recorded in PR]
```

## Cycle 46 selection / proposed result

```yaml
ledger_type: target_cycle_result
goal: G-127-aat-reversible-protocol-holonomy
cycle: 46
goal_blob_sha: 86ed6948771755a19db802e01e42dbd00a8f9abf
base_oid: 5bc7f3039
tracking_issue: 4981
report_path: research/reports/G-127-aat-reversible-protocol-holonomy.md
selection:
  proof_state_ref: Issue #4981 Cycle 45 structural undirected-tree bridge and open E computation
  proof_dag_predecessors: [ReversibleData.Lift, ReversibleData.Lift.edge_naturality]
  proof_obligation: From explicit finite enumerations and equality decisions, decide existence of an original A1 Lift for any visible graph automorphism and return one genuine lift or a proof of nonexistence
  selection_reason: Establishes a terminating exact original-Lift decision baseline and a reusable table candidate enumeration for the B/C-derived E procedure and fixed examples
  expected_result_type: proof-checkpoint
  lean_targets: [ResearchLean/AG/ProtocolHolonomy/FiniteDirectDecision.lean]
  risks: [using Classical.choice or Fintype.ofFinite in executable search, testing only injectivity, deciding a wrapper instead of original Lift, silently assuming root/forest input]
  unchecked: [finite forest construction, B1/B2/C1-derived E decision, H_lift enumeration and torsor reconstruction, both fixed examples]
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: Explicit vertex/edge/fiber lists generate all forward/inverse vertex table families by terminating List.pi and List.product; the executable search checks both inverse laws and every original A1 named-edge square, returns a genuine Lift, and a none result excludes every original Lift
  completion_candidate: no
  lean_artifacts: [ExplicitEnumeration.pi, ReversibleData.allCandidateMaps, ReversibleData.findDirectLift]
  evidence: [ReversibleData.findDirectLift_none, ReversibleData.findDirectLift_isSome_iff, executable one-vertex zero-edge Bool evaluation]
  claim_mapping:
    theorem_names: [ExplicitEnumeration.pi, ReversibleData.findDirectLift_none, ReversibleData.findDirectLift_isSome_iff]
    source_labels: [E original Lift soundness and completeness baseline]
    conjuncts: [explicit finite input, total candidate enumeration, A1 validity, positive lift and negative nonexistence]
    undischarged_assumptions: [finite forest construction and B/C-derived E procedure, fixed examples]
    acceptance_point: Complete direct A1 finite decision baseline on explicit input lists; B/C-derived algorithm and forest construction remain required for G-127 E
    port_status: unported
audits:
  premise_delta:
    discharged: [explicit candidate generation, original A1 table decision with both directions of existence]
    remaining: [finite forest construction, B1/B2/C1-derived E route, H_lift enumeration and torsor connection, fixed examples]
  certificate_provenance:
    discharged: [allCandidateMaps from explicit vertex and fiber lists, ValidCandidate inverse and edge checks, direct construction of original Lift]
    unresolved: [same solver applied through input-generated B/C data]
  proof_use:
    used: [every supplied enumeration completeness proof in List.pi, finite quantified inverse and edge checks, original A1 Lift fields]
    unused: [no forest or RootSolutions input is consumed by this direct baseline]
  structure_field_escape: none-found-for-direct-A1-baseline
  route_integrity: pass-for-direct-A1-baseline-only
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [focused Lean check and ten-declaration standard axiom audit to be recorded in PR; #eval direct one-vertex Bool search true]
```

## Cycle 47 selection / proposed result

```yaml
ledger_type: target_cycle_result
goal: G-127-aat-reversible-protocol-holonomy
cycle: 47
goal_blob_sha: 86ed6948771755a19db802e01e42dbd00a8f9abf
base_oid: c03375e79
tracking_issue: 4981
report_path: research/reports/G-127-aat-reversible-protocol-holonomy.md
selection:
  proof_state_ref: Issue #4981 Cycle 46 executable direct A1 baseline, original C1/C2 equivalence, open B/C finite route
  proof_dag_predecessors: [ExplicitEnumeration.pi, ReversibleData.allCandidateMaps, ReversibleData.liftEquivRootSolutions]
  proof_obligation: For supplied original RootedPaths and explicit finite tables, decide the simultaneous C1 condition from named edge loops, reconstruct a genuine original Lift by C2, and prove none exactly excludes original lifts
  selection_reason: Connects explicit finite enumeration to the required C1/C2 route rather than merely reusing direct A1 decision
  expected_result_type: proof-checkpoint
  lean_targets: [ResearchLean/AG/ProtocolHolonomy/FiniteRootDecision.lean]
  risks: [testing only a subset of named edges, hidden quotient-component enumeration, using direct A1 test instead of C1, putting C1 in supplied certificate, nonexecutable root path choice]
  unchecked: [input-generated executable named forest/RootedPaths, B1/B2 finite centralizer enumeration, H_lift/torsor connection, fixed examples]
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: On supplied RootedPaths, explicit finite lists enumerate candidate tables and test both inverse laws plus the simultaneous pointwise C1 equation for every original named edge loop; a passing table gives actual RootSolutions and its C2 lift, while a negative answer excludes all original lifts and all C1 root solutions
  completion_candidate: no
  lean_artifacts: [ReversibleData.ValidRootCandidate, ReversibleData.rootSolutionsOfValidCandidate, ReversibleData.findRootLift]
  evidence: [ReversibleData.validRootCandidate_of_lift, ReversibleData.findRootLift_none, ReversibleData.findRootLift_isSome_iff, ReversibleData.findRootLift_isSome_iff_rootSolutions]
  claim_mapping:
    theorem_names: [ReversibleData.rootSolutionsOfValidCandidate, ReversibleData.findRootLift_none, ReversibleData.findRootLift_isSome_iff_rootSolutions]
    source_labels: [C1/C2 and E finite simultaneous root test]
    conjuncts: [all original named edges, simultaneous root values, C1 pointwise test, C2 original Lift, both decision directions]
    undischarged_assumptions: [executable root/forest construction from input, B1/B2 centralizer enumeration, H_lift and examples]
    acceptance_point: C1/C2 finite procedure on supplied RootedPaths is exact for original Lift and RootSolutions; input-generated executable roots/forest and B1/B2 remain required
    port_status: unported
audits:
  premise_delta:
    discharged: [simultaneous finite C1 test and C2 reconstruction for supplied original root paths]
    remaining: [E input-generated forest, B1/B2 centralizer enumeration, H_lift/torsor connection and examples]
  certificate_provenance:
    discharged: [all candidate tables from explicit lists, C1 check computed for every original named edge, RootSolutions and original Lift constructed on success]
    unresolved: [runtime root paths from finite named forest]
  proof_use:
    used: [every original named edge loop C1 test, both inverse laws, original RootSolutions.toLift C2, Lift-to-C1 converse]
    unused: [direct A1 validity test is not called by this C1 search]
  structure_field_escape: none-found-for-conditional-root-solver
  route_integrity: pass-for-supplied-root-paths-only
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [focused Lean check and seven-declaration standard axiom audit to be recorded in PR; #eval zero-edge Bool true; #eval two named-loop C1 positive true and negative false]
```

## Cycle 48 selection / proposed result

```yaml
ledger_type: target_cycle_result
goal: G-127-aat-reversible-protocol-holonomy
cycle: 48
goal_blob_sha: 86ed6948771755a19db802e01e42dbd00a8f9abf
base_oid: 70563f4bb981df2b236a727057e1bff981cf058d
tracking_issue: 4981
report_path: research/reports/G-127-aat-reversible-protocol-holonomy.md
selection:
  proof_state_ref: Issue #4981 Cycle 47 supplied-root C1 procedure and open finite B2/forest construction
  proof_dag_predecessors: [ExplicitEnumeration.pi, ReversibleData.edgeMonodromyAt, ReversibleData.holonomy, ReversibleData.verticalRootMulEquiv]
  proof_obligation: From explicit finite edge/root-fiber tables and supplied root paths/component equality, enumerate precisely the root permutations centralizing all original named-edge B1 generators in one component
  selection_reason: Closes the componentwise finite B2 centralizer enumeration before combining components and constructing input-generated forest/component decisions
  expected_result_type: proof-checkpoint
  lean_targets: [ResearchLean/AG/ProtocolHolonomy/FiniteCentralizerDecision.lean]
  risks: [testing an unnamed or incomplete edge set, supplied centralizer certificate, noncomputable component test hidden in runtime, claiming all-component E from one-component list]
  unchecked: [input-generated named forest and component equality decision, combination of all component centralizer lists, H_lift/torsor output, fixed examples]
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: Candidate forward/inverse root tables are completely enumerated; finite validity tests both inverse laws and commutation with every original named edge whose source belongs to the component; each passing table constructs an element of the actual B2 centralizer and every such element occurs in the resulting list
  completion_candidate: no
  lean_artifacts: [ReversibleData.ValidCentralizerCandidate, ReversibleData.finiteRootCentralizers]
  evidence: [ReversibleData.centralizerOfValidCandidate, ReversibleData.validCentralizerCandidate_of_mem, ReversibleData.centralizer_mem_finiteRootCentralizers]
  claim_mapping:
    theorem_names: [ReversibleData.centralizerOfValidCandidate, ReversibleData.centralizer_mem_finiteRootCentralizers]
    source_labels: [B1 named-edge generators, B2 component centralizer, E finite enumeration]
    conjuncts: [original named-edge monodromy, both inverse laws, generator commutation, centralizer soundness and exhaustive membership]
    undischarged_assumptions: [supplied RootedPaths, supplied DecidableEq on original component quotient, all-component and full E procedure]
    acceptance_point: Exact componentwise centralizer list conditional on supplied root paths/component equality; not a full input-generated E algorithm
    port_status: unported
audits:
  premise_delta:
    discharged: [finite root-permutation enumeration and B1-generator centralizer check for one chosen component]
    remaining: [finite named forest/component decision, all-component B2 assembly, E H_lift/torsor and examples]
  certificate_provenance:
    discharged: [candidate tables generated from explicit root-fiber values, original edgeMonodromyAt computed from named edge actions, B2 membership derived via centralizer_closure]
    unresolved: [runtime production of RootedPaths and decidable original component equality]
  proof_use:
    used: [all root-fiber table candidates, each named edge in component, both inverse laws, holonomy closure equality, original B2 centralizer]
    unused: [verticalRootMulEquiv is a later all-component connection; finiteRootLift C1 search is independent]
  structure_field_escape: none-found-for-conditional-component-list
  route_integrity: pass-for-B1-generator-to-B2-component-list
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [focused Lean check and five-declaration standard axiom audit to be recorded in PR]
```
