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
