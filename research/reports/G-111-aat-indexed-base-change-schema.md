# G-111 — indexed base-change calculus と coherent diagnostic assembly

- 一次仕様: [`research/goals/G-111-aat-indexed-base-change-schema.md`](../goals/G-111-aat-indexed-base-change-schema.md)
- tracking Issue: [#4158](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/4158)
- target theorem: Indexed Base-Change Calculus and Coherent Diagnostic Assembly Classification Theorem
- proof state: `active / Cycle 17 K4 component comparison candidate`
- completion candidate: `no`

旧カードに対する PR #4161 / #4162 は棄却済みであり、改訂後 target の
checkpoint または predecessor evidence として使用しない。

## 2026-08-26 human-approved target revision

Cycle 7 は、等しい source path と二つの independently validated square
だけから target path equality を一様生成する旧 K1.5 conjunct を有限反例
で否定した。人間裁定により、Gr4 の責務を次の三面へ分離した。

1. 全 base 射・全可換 square 上の pointwise indexed calculus(O1–O2)は
   Cycle 4–6 の reviewed artifact を保持する。
2. incidence-independent (d1)–(d6) は、診断語彙を含まない
   `IndexedBaseDiagram` / `IndexedBaseDiagramHom` が与える coherent
   diagram morphism 全域で、declared base relation に相対して assembly
   する。target `twoCellBase` はこの direction hypothesis の canonical
   realizationであり、raw family からの生成成果とは数えない。
3. arbitrary raw square family の自動 assembly は主張せず、一様持上げ
   可能性と `Epi` の必要十分性、vertexwise-epi producer、非 epi
   coherent 正例、Cycle 7 non-liftable 負例として分類する。

この改訂は Cycle 7 の反証を消去しない。旧 target は
`target-refuted` のまま履歴に残り、その有限反例は改訂 target の必須
負枝へ移る。Cycle 10 の F0 は diagnostic import を持たない base diagram /
hom と path-naturality API を、Cycle 11 の K2 はその上の coherent
diagnostic assembly をそれぞれ確定した。Cycle 12 は生成済み target
interpretation、endpoint group homomorphism、relation-relative data を
(d1)--(d3) の定理面へ固定した。Cycle 13 は同じ endpoint action で
source reselection を写す K3 (d4) を確定した。K3 (d5)--(d6) は Cycle 14
で確定し、Cycle 15 は同じ named cell 上で非自明性と (d4)--(d6) の発火を
固定する diagnostic witness を確定した。現在の proof obligation は K4
C0--C3 であり、Cycle 16 はまず walking-arrow restriction による C0 と
C3 の mate-level core を G-110 の実 route へ接続する。
raw-family classification は
(i) 一頂点・全 right legs の local uniform liftability iff `Epi`、
(ii) finite family support 上の vertexwise-epi sufficiency producer、
(iii) coherent domain の非 epi positive、(iv) Cycle 7 negative に分ける。
fixed-family の偶発的 liftability iff `Epi` は主張しない。nontrivial
(d4)–(d6) witness は別の named cell / connected subdiagram で構成し、
非 epi positive の因果的 diagnostic 発火とは表示しない。

## Cycle ledger

### Cycle 10 — diagnostic-free indexed base diagram and hom

```yaml
ledger_type: target_cycle_result
goal: G-111-aat-indexed-base-change-schema
cycle: 10
goal_blob_sha: 6541ee426482d09b8be4c91b2a268a6a7c3f9a0b
goal_sha256: cd372006a408707a262c24b81b590760ffb50ccc76f46f8ed80845cd60b7b3e4
base_oid: e28231e28569826a22221e3cdc351bb7cdbbfb46
pr: 4171
reviewed_head: 2791e02700af990ccdfaa2aa130b1739009ffae6
merge_oid: 613606daba3fde34e650e5370bf1ae9907c19282
tracking_issue: 4158
selection:
  proof_state_ref: "Issue #4158 accepted card revision / report F0"
  proof_dag_predecessors:
    - "Cycle 4-6 pointwise indexed calculus"
    - "G-109 CorePseudofunctor base category API"
  proof_obligation: >-
    Construct F0: a finite diagnostic-free base 0/1/2-cell shape,
    IndexedBaseDiagram, and IndexedBaseDiagramHom with vertex indices,
    generated commutative edge squares, all-path naturality, declared-cell
    path naturality, identity, composition, and category laws. No package,
    comparator, defect, reselection, coherence, or vanishing field may occur.
  selection_reason: >-
    This is the first unimplemented node in the fixed proof strategy and the
    input category required by K2-K5 and G-113.
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/IndexedBaseSquareGeometry.lean
    - ResearchLean/AG/DoctrineFiberProduct/IndexedBaseDiagram.lean
  risks:
    - diagnostic vocabulary enters through an import or structure field
    - path naturality is accepted as authored hom data instead of generated
    - declared target relation is credited as raw-family generation
    - identity or composition laws close only because hom data is proof-only
  unchecked:
    - K2 coherent diagnostic assembly
    - K3 (d1)-(d6)
    - K4 C0-C3
    - K5 raw-family producer and finite witnesses
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: >-
    IndexedBaseShape and IndexedBaseTwoShape give the finite authored base
    geometry. IndexedBaseDiagram assigns only extraction instances, generating
    base arrows, and declared base relations. IndexedBaseDiagramHom assigns
    only vertex indices and generating-edge squares. path_naturality is proved
    by induction. horizontalPathSquare and verticalPathSquare invoke the actual
    provenance-retaining paste operations; their side-comparison theorems connect
    pasted squares to appended paths and composite homs. The Category instance
    proves the identity, composition, and associativity laws.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/IndexedBaseSquareGeometry.lean
    - ResearchLean/AG/DoctrineFiberProduct/IndexedBaseDiagram.lean
  evidence:
    - IndexedBasePath.eval_append
    - IndexedBaseDiagram.path_append
    - IndexedBaseDiagram.relation_path
    - IndexedBaseDiagramHom.edgeSquare
    - IndexedBaseDiagramHom.path_naturality
    - IndexedBaseDiagramHom.pathSquare
    - IndexedBaseDiagramHom.horizontalPathSquare
    - IndexedBaseDiagramHom.horizontalPathSquare_top
    - IndexedBaseDiagramHom.horizontalPathSquare_bottom
    - IndexedBaseDiagramHom.horizontalPathSquare_route
    - IndexedBaseDiagramHom.twoCell_left_naturality
    - IndexedBaseDiagramHom.twoCell_right_naturality
    - IndexedBaseDiagramHom.twoCell_naturality
    - IndexedBaseDiagramHom.twoCell_target_relation
    - IndexedBaseDiagramHom.id
    - IndexedBaseDiagramHom.comp
    - IndexedBaseDiagramHom.verticalPathSquare
    - IndexedBaseDiagramHom.verticalPathSquare_left
    - IndexedBaseDiagramHom.verticalPathSquare_right
    - IndexedBaseDiagramHom.verticalPathSquare_route
    - indexedBaseDiagramCategory
  claim_mapping:
    theorem_names:
      - IndexedBaseDiagramHom.path_naturality
      - IndexedBaseDiagramHom.twoCell_naturality
      - indexedBaseDiagramCategory
    source_labels:
      - "G-111 target theorem (c)"
      - "G-111 target proof strategy F0"
    conjuncts:
      - "finite diagnostic-free base geometry -> IndexedBaseShape / IndexedBaseTwoShape"
      - "diagram vertices, edges, declared relations -> IndexedBaseDiagram"
      - "vertex indices and edge squares -> IndexedBaseDiagramHom / edgeSquare"
      - "path and declared-cell naturality -> generated theorems"
      - "horizontal and vertical pasting -> actual paste constructions plus side comparison theorems"
      - "identity, composition, category laws -> indexedBaseDiagramCategory"
    undischarged_assumptions:
      - "declared base relations remain the fixed direction hypothesis"
    acceptance_point: >-
      F0 is discharged if fixed-head review confirms the module is
      diagnostic-free, path naturality is generated, and the category API has
      no conclusion-side field escape.
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "diagnostic-free diagram category typing and path-naturality API"
    remaining:
      - "coherent diagnostic assembly and (d1)-(d6)"
      - "C0-C3"
      - "raw-family producer and positive/diagnostic witnesses"
  certificate_provenance:
    discharged:
      - "edge squares are generated from hom.naturality"
      - "all-path naturality is generated by induction from edge squares"
    unresolved:
      - "later target diagnostic certificates"
  proof_use:
    used:
      - "each generating-edge naturality proof in path_naturality"
      - "source declared relation in twoCell_naturality"
      - "target declared relation in twoCell_target_relation"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "focused lake env lean IndexedBaseSquareGeometry.lean: pass"
    - "targeted lake build IndexedBaseSquareGeometry: pass"
    - "focused lake env lean IndexedBaseChangeRaw.lean after geometry split: pass"
    - "focused lake env lean IndexedBaseDiagram.lean: pass"
    - "namespace axiom audit: 125 declarations, standard axioms only"
  initial_review_findings:
    - "horizontal path-square pasting lacked an actual paste construction"
    - "vertical path-square provenance used sequential comp instead of pasteVertical"
    - "IndexedBaseDiagram imported the package-level raw syntax module"
    - "the target declared relation had no explicit proof-use theorem"
  correction:
    - "split IndexedBaseSquareGeometry from IndexedBaseChangeRaw"
    - "add horizontalPathSquare with top, bottom, left, right, and route theorems"
    - "use verticalPaste with composite-side and route theorems"
    - "add twoCell_target_relation"
  blocking_findings: []
  next_obligation: "K2 connect the generated diagram hom action to coherent diagnostic assembly"
```

### Cycle 11 — coherent indexed diagnostic assembly

```yaml
ledger_type: target_cycle_result
goal: G-111-aat-indexed-base-change-schema
cycle: 11
goal_blob_sha: 6541ee426482d09b8be4c91b2a268a6a7c3f9a0b
goal_sha256: cd372006a408707a262c24b81b590760ffb50ccc76f46f8ed80845cd60b7b3e4
base_oid: 613606daba3fde34e650e5370bf1ae9907c19282
pr: 4172
reviewed_head: 198ecbcd55903f16dbb1e1b595a82c8128df07ca
merge_oid: 27b9f34611476fb9e5012f89a05fb1f1267d9ea2
tracking_issue: 4158
selection:
  proof_state_ref: "Issue #4158 Cycle 10 merged / K2 selected"
  proof_dag_predecessors:
    - "Cycle 10 diagnostic-free diagram category"
    - "Cycle 4-6 pointwise indexed action and square-total map"
  proof_obligation: >-
    Construct K2 coherent diagnostic assembly over a previously fixed
    IndexedBaseDiagramHom. Accept only ordinary source packages, source edge
    lifts and their local qualification, and source comparators. Generate the
    target packages, edge lifts, strong qualifications, target declared-cell
    base equation, and target comparators from the same pointwise action.
  selection_reason: >-
    K2 is the first open successor of the merged F0 category and supplies the
    target data on which K3 states (d1)-(d6).
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/IndexedDiagnosticAssembly.lean
  risks:
    - source packages are collapsed into one common fiber
    - target data is accepted through a structure field
    - edge transport does not use the generating commutative square
    - target two-cell base equality is credited as raw-family generation
  unchecked:
    - K3 (d1)-(d6), including reselection, coherence, and vanishing
    - K4 C0-C3
    - K5 raw-family classification and witnesses
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: >-
    IndexedDiagnosticInterpretation fixes ordinary source diagnostic data over
    a diagnostic-free source diagram without a common-fiber incidence premise.
    transportedPackage uses the vertex index action; transportedEdgeLift uses
    the corresponding validated generating square; strong qualification is
    preserved by indexedSquareTotalMap_isStronglyCocartesian. Source and target
    path lifts lie over their fixed diagram paths. transportedTwoCellBase uses
    the target declared relation, while transportedComparator is generated by
    the endpoint group action.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/IndexedDiagnosticAssembly.lean
  evidence:
    - IndexedDiagnosticInterpretation.pathLift_isHomLift
    - IndexedDiagnosticInterpretation.twoCellBase
    - IndexedBaseDiagramHom.vertexIndex
    - IndexedBaseDiagramHom.validatedEdgeSquare
    - IndexedBaseDiagramHom.transportedPackage
    - IndexedBaseDiagramHom.transportedEdgeLift
    - IndexedBaseDiagramHom.transportedEdgeLift_isHomLift
    - IndexedBaseDiagramHom.transportedEdgeLift_isStronglyCocartesian
    - IndexedBaseDiagramHom.transportedPathLift_isHomLift
    - IndexedBaseDiagramHom.transportedTwoCellBase
    - IndexedBaseDiagramHom.transportedComparator
  claim_mapping:
    source_labels:
      - "G-111 target theorem (d) K2"
      - "G-111 target proof strategy K2"
    conjuncts:
      - "ordinary source diagnostic interpretation -> IndexedDiagnosticInterpretation"
      - "vertexwise generated target packages -> transportedPackage"
      - "squarewise generated target lifts and qualification -> transportedEdgeLift"
      - "declared target relation realization -> transportedTwoCellBase"
      - "generated target comparator -> transportedComparator"
    undischarged_assumptions:
      - "source edge lifts and their strong qualification are ordinary source input"
      - "source comparator is ordinary source input"
      - "declared source and target base relations remain direction hypotheses"
    acceptance_point: >-
      K2 is discharged if fixed-head review confirms that all target diagnostic
      values are generated, no common-fiber incidence premise remains, and the
      target two-cell base equation is credited only to the declared relation.
audits:
  premise_delta:
    discharged:
      - "incidence-independent target package/edge/comparator assembly"
    remaining:
      - "K3 (d1)-(d6) theorem family"
      - "K4 C0-C3"
      - "K5 classification and witnesses"
  certificate_provenance:
    discharged:
      - "target edge qualification from indexedSquareTotalMap_isStronglyCocartesian"
      - "target comparator from coreFiberFunctorPackageAutHom"
    direction_hypothesis:
      - "source and target declared base relations"
  proof_use:
    used:
      - "hom.app at every transported package"
      - "hom.naturality at every validatedEdgeSquare"
      - "source edgeStrong at every transportedEdgeLift qualification"
      - "E.relation_path in transportedTwoCellBase"
      - "source comparator in transportedComparator"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  validation_refs:
    - "focused lake env lean IndexedDiagnosticAssembly.lean: pass"
    - "namespace axiom audit: 34 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "K3 state and prove (d1)-(d6) over the generated assembly"
```

### Cycle 12 — target interpretation, endpoint action, and relation-relative data

```yaml
ledger_type: target_cycle_result
goal: G-111-aat-indexed-base-change-schema
cycle: 12
goal_blob_sha: 6541ee426482d09b8be4c91b2a268a6a7c3f9a0b
goal_sha256: cd372006a408707a262c24b81b590760ffb50ccc76f46f8ed80845cd60b7b3e4
base_oid: 27b9f34611476fb9e5012f89a05fb1f1267d9ea2
pr: 4173
reviewed_head: 372fecd3c93b7eb62bde19e98d05d78d456f8132
merge_oid: 7995ea0f53687bd958cd57dda2255f4580db7c23
tracking_issue: 4158
selection:
  proof_state_ref: "Issue #4158 Cycle 11 merged / K3 selected"
  proof_dag_predecessors:
    - "Cycle 10 diagnostic-free diagram category"
    - "Cycle 11 coherent indexed diagnostic assembly"
  proof_obligation: >-
    Discharge K3 (d1)-(d3): package the generated K2 outputs as the target
    interpretation, expose the actual endpoint group homomorphism, and state
    the generated comparator, target relation-relative two-cell equation, and
    edge qualification on that interpretation.
  selection_reason: >-
    These are the first three K3 clauses and form the input surface required
    by mapped reselection and the later coherence and vanishing clauses.
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/IndexedDiagnosticCovariance.lean
  risks:
    - the target interpretation is accepted as input rather than generated
    - endpoint action is exposed only as a function, not a MonoidHom
    - target relation is misreported as generated from raw squares
    - d4-d6 are implicitly credited by the d1-d3 packaging
  unchecked:
    - "K3 (d4) mapped reselection"
    - "K3 (d5) coherence preservation"
    - "K3 (d6) vanishing preservation"
    - "K4 C0-C3"
    - "K5 raw-family classification and witnesses"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: >-
    transportedInterpretation constructs the target interpretation directly
    from the Cycle 11 package, edge-lift, qualification, and comparator
    outputs. endpointAction exposes the vertexwise MonoidHom and its identity
    and multiplication laws. The comparator equation, target declared-cell
    base equation, and strong edge qualification are theorem outputs on the
    generated interpretation.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/IndexedDiagnosticCovariance.lean
  evidence:
    - IndexedBaseDiagramHom.transportedInterpretation
    - IndexedBaseDiagramHom.transportedInterpretation_package
    - IndexedBaseDiagramHom.transportedInterpretation_edgeLift
    - IndexedBaseDiagramHom.endpointAction
    - IndexedBaseDiagramHom.endpointAction_one
    - IndexedBaseDiagramHom.endpointAction_mul
    - IndexedBaseDiagramHom.transportedInterpretation_comparator
    - IndexedBaseDiagramHom.transportedInterpretation_pathLift
    - IndexedBaseDiagramHom.transportedInterpretation_twoCellBase
    - IndexedBaseDiagramHom.transportedInterpretation_edgeStrong
  claim_mapping:
    source_labels:
      - "G-111 target theorem (d1)-(d3)"
      - "G-111 target proof strategy K3"
    conjuncts:
      - "(d1) generated target interpretation -> transportedInterpretation"
      - "(d2) endpoint group homomorphism -> endpointAction"
      - "(d3) comparator and relation-relative target data -> theorem family"
    undischarged_assumptions:
      - "source diagnostic interpretation remains ordinary input"
      - "target declared relations remain fixed direction hypotheses"
    acceptance_point: >-
      The cycle is discharged if fixed-head review confirms that the target
      interpretation and endpoint action are generated, d3 proof-uses the K2
      outputs and target relation, and no d4-d6 claim is smuggled into this
      layer.
audits:
  premise_delta:
    discharged:
      - "K3 (d1) generated target diagnostic interpretation"
      - "K3 (d2) endpoint group homomorphism"
      - "K3 (d3) relation-relative target theorem surface"
    remaining:
      - "K3 (d4)-(d6)"
      - "K4 C0-C3"
      - "K5 classification and witnesses"
  certificate_provenance:
    discharged:
      - "target interpretation fields are generated by Cycle 11 outputs"
      - "endpoint action is coreFiberFunctorPackageAutHom"
      - "target edge qualification is the transported K2 theorem"
    direction_hypothesis:
      - "target declared base relation used by transportedInterpretation_twoCellBase"
  proof_use:
    used:
      - "Cycle 11 transportedPackage and transportedEdgeLift"
      - "Cycle 11 transportedEdgeLift_isStronglyCocartesian"
      - "Cycle 11 transportedComparator"
      - "target interpretation twoCellBase, hence the target declared relation"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  validation_refs:
    - "focused lake env lean IndexedDiagnosticCovariance.lean: pass"
    - "namespace axiom audit: 12 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "K3 (d4) mapped reselection, followed by (d5)-(d6) preservation"
```

### Cycle 13 — mapped indexed edge reselection

```yaml
ledger_type: target_cycle_result
goal: G-111-aat-indexed-base-change-schema
cycle: 13
goal_blob_sha: 6541ee426482d09b8be4c91b2a268a6a7c3f9a0b
goal_sha256: cd372006a408707a262c24b81b590760ffb50ccc76f46f8ed80845cd60b7b3e4
base_oid: 7995ea0f53687bd958cd57dda2255f4580db7c23
pr: 4174
reviewed_head: 8f1f2c11960a5f5e0f8e4dfda065946e6a8e1fc8
merge_oid: 040927ef0633433f5a730ec4a43c3cb837fed993
tracking_issue: 4158
selection:
  proof_state_ref: "Issue #4158 Cycle 12 merged / K3 d4 selected"
  proof_dag_predecessors:
    - "Cycle 11 coherent indexed diagnostic assembly"
    - "Cycle 12 generated target interpretation and endpoint action"
  proof_obligation: >-
    Discharge K3 (d4): define edgewise source reselection over an arbitrary
    indexed diagnostic interpretation and map it pointwise through the same
    generated endpoint MonoidHom used by d2 and the target comparator.
  selection_reason: >-
    Mapped reselection is the next open K3 clause and the explicit coordinate
    required before coherence and vanishing preservation can be stated.
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/IndexedDiagnosticReselection.lean
  risks:
    - target reselection is accepted as a theorem argument or structure field
    - a second action unrelated to endpointAction is introduced
    - a common-source-fiber incidence premise is added
    - d5 or d6 is credited from group laws alone
  unchecked:
    - "K3 (d5) coherence preservation"
    - "K3 (d6) vanishing preservation"
    - "K4 C0-C3"
    - "K5 raw-family classification and witnesses"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: >-
    IndexedEdgeReselection is ordinary source-side edgewise automorphism data.
    transportedReselection generates the target coordinate by applying the d2
    endpointAction at every edge target. The identity and multiplication laws
    are inherited from that actual MonoidHom. No package incidence equality,
    target reselection field, coherence, or vanishing certificate is added.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/IndexedDiagnosticReselection.lean
  evidence:
    - IndexedEdgeReselection
    - IndexedBaseDiagramHom.transportedReselection
    - IndexedBaseDiagramHom.transportedReselection_apply
    - IndexedBaseDiagramHom.transportedReselection_one
    - IndexedBaseDiagramHom.transportedReselection_mul
  claim_mapping:
    source_labels:
      - "G-111 target theorem (d4)"
      - "G-111 target proof strategy K3"
    conjuncts:
      - "ordinary source edge reselection -> IndexedEdgeReselection"
      - "generated target reselection -> transportedReselection"
      - "same endpoint action and group laws -> one/mul theorems"
    undischarged_assumptions:
      - "source edge reselection is ordinary source-side input"
    acceptance_point: >-
      The cycle is discharged if fixed-head review confirms that every target
      coordinate is generated by the d2 endpointAction, the group laws are
      proof outputs, and no incidence premise or d5-d6 conclusion is added.
audits:
  premise_delta:
    discharged:
      - "K3 (d4) mapped reselection"
    remaining:
      - "K3 (d5)-(d6)"
      - "K4 C0-C3"
      - "K5 classification and witnesses"
  certificate_provenance:
    discharged:
      - "each target edge coordinate is endpointAction applied to source reselection"
    unresolved:
      - "path coherence and vanishing preservation"
  proof_use:
    used:
      - "Cycle 12 endpointAction at every target vertex"
      - "source reselection at every indexed edge"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  validation_refs:
    - "focused lake env lean IndexedDiagnosticReselection.lean: pass"
    - "namespace axiom audit: 5 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "K3 (d5) coherence preservation, followed by (d6) vanishing preservation"
```

### Cycle 14 — indexed coherence and obstruction-vanishing preservation

```yaml
ledger_type: target_cycle_result
goal: G-111-aat-indexed-base-change-schema
cycle: 14
goal_blob_sha: 6541ee426482d09b8be4c91b2a268a6a7c3f9a0b
goal_sha256: cd372006a408707a262c24b81b590760ffb50ccc76f46f8ed80845cd60b7b3e4
base_oid: 040927ef0633433f5a730ec4a43c3cb837fed993
pr: 4175
reviewed_head: 6fd8c062a0cdeaeb5dad63953e7afa0bf2576ec0
merge_oid: e71dd442911b50d7e30c2b2d3851ea8d0500f06b
tracking_issue: 4158
selection:
  proof_state_ref: "Issue #4158 Cycle 13 merged / K3 d5-d6 selected"
  proof_dag_predecessors:
    - "Cycle 12 generated target interpretation and endpoint action"
    - "Cycle 13 mapped indexed edge reselection"
    - "G-106 independent raw-defect orbit and coherentizability equivalence"
  proof_obligation: >-
    Discharge K3 (d5)-(d6) without common-fiber incidence. Prove edge and path
    naturality for the mapped reselection using the generated square action and
    canonical vertex lifts; consume source coherence to generate target
    coherence. Embed the unchanged finite 2-skeleton into the existing
    independent obstruction presentation, consume source orbit vanishing, and
    generate target orbit vanishing.
  selection_reason: >-
    These are the remaining K3 clauses and the only route from mapped edge
    coordinates to the actual two-cell equations and independent obstruction.
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/IndexedDiagnosticCoherence.lean
    - ResearchLean/AG/DoctrineFiberProduct/IndexedDiagnosticVanishing.lean
  risks:
    - coherence is renamed rather than expressed as a path equality
    - source coherence or source vanishing is accepted but not used
    - all packages are forced into one common source fiber
    - target coherence, reselection, or vanishing is accepted as input
    - indexed vanishing is defined to be coherentizability instead of using the independent orbit
  unchecked:
    - "nontrivial named (d4)-(d6) witness"
    - "K4 C0-C3"
    - "K5 raw-family classification and witnesses"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: >-
    IndexedCoherentAt is the authored package-level equality between the two
    reselected path lifts. Canonical vertex lifts intertwine source and target
    reselected edges by indexedUniversalSquareEdgeLaw and endpoint
    automorphisms by indexedUniversalEdgeLaw; path induction and strongly
    cocartesian uniqueness transport the source equation to the target.
    The finite 2-skeleton adapter retains the same vertices, edges, packages,
    lifts, cells, and comparators and adds no 3-cell. The existing independent
    raw-defect orbit is converted to coherentizability by the proved G-106
    equivalence, mapped by d5, and converted back to target orbit vanishing.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/IndexedDiagnosticCoherence.lean
    - ResearchLean/AG/DoctrineFiberProduct/IndexedDiagnosticVanishing.lean
  evidence:
    - IndexedDiagnosticInterpretation.reselectedEdgeLift
    - IndexedDiagnosticInterpretation.reselectedPathLift
    - IndexedDiagnosticInterpretation.IndexedCoherentAt
    - IndexedBaseDiagramHom.diagnosticVertexLift_endpointAction_naturality
    - IndexedBaseDiagramHom.diagnosticVertexLift_reselectedEdge_naturality
    - IndexedBaseDiagramHom.diagnosticVertexLift_reselectedPath_naturality
    - IndexedBaseDiagramHom.indexedCoherentAt_transport
    - IndexedDiagnosticInterpretation.toAdmissibleTransportData
    - IndexedDiagnosticInterpretation.indexedCoherentAt_iff_adaptedCoherentAt
    - IndexedBaseDiagramHom.indexedTransportObstructionVanishes_transport
  claim_mapping:
    source_labels:
      - "G-111 target theorem (d5)-(d6)"
      - "G-111 target proof strategy K3"
    conjuncts:
      - "source coherent reselection -> generated target coherent reselection"
      - "independent source obstruction-orbit vanishing -> target orbit vanishing"
    undischarged_assumptions:
      - "source coherence is the d5 direction hypothesis"
      - "source obstruction vanishing is the d6 direction hypothesis"
    acceptance_point: >-
      The cycle is discharged if fixed-head review confirms the actual path
      equations, source-hypothesis proof-use, independent orbit provenance,
      and absence of common-fiber incidence or target certificate inputs.
audits:
  premise_delta:
    discharged:
      - "K3 (d5) coherence preservation"
      - "K3 (d6) obstruction-vanishing preservation"
    remaining:
      - "nontrivial named (d4)-(d6) witness"
      - "K4 C0-C3"
      - "K5 classification and witnesses"
  certificate_provenance:
    discharged:
      - "target coherence is generated from source coherence by vertex-lift naturality"
      - "target vanishing is generated through the independent raw-defect orbit equivalence"
    unresolved:
      - "nontrivial witness and later classification outputs"
  proof_use:
    used:
      - "source IndexedCoherentAt equation in indexedCoherentAt_transport"
      - "source TransportObstructionVanishes in indexedTransportObstructionVanishes_transport"
      - "Cycle 13 transportedReselection in both outputs"
      - "target declared relation to align the two target HomLift bases"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  validation_refs:
    - "focused lake env lean IndexedDiagnosticCoherence.lean: pass"
    - "coherence namespace axiom audit: 14 declarations, standard axioms only"
    - "focused lake env lean IndexedDiagnosticVanishing.lean: pass"
    - "vanishing namespace axiom audit: 10 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "construct the named nontrivial (d4)-(d6) witness, then K4 C0-C3"
```

### Cycle 15 — named nontrivial indexed diagnostic witness

```yaml
ledger_type: target_cycle_result
goal: G-111-aat-indexed-base-change-schema
cycle: 15
goal_blob_sha: 6541ee426482d09b8be4c91b2a268a6a7c3f9a0b
goal_sha256: cd372006a408707a262c24b81b590760ffb50ccc76f46f8ed80845cd60b7b3e4
base_oid: e71dd442911b50d7e30c2b2d3851ea8d0500f06b
pr: 4176
reviewed_head: fc541e7511cc8b5d69cf63dda75b99711b253426
merge_oid: aa7aa88db246c487220efb7627dbd323aa671893
tracking_issue: 4158
selection:
  proof_state_ref: "Issue #4158 Cycle 14 merged / named witness selected"
  proof_dag_predecessors:
    - "Cycle 13 mapped indexed edge reselection"
    - "Cycle 14 indexed coherence and obstruction-vanishing preservation"
    - "G-106 finite adjacent-swap package witness"
  proof_obligation: >-
    Construct the separate named diagnostic witness required by target clause
    (g): one connected declared cell with syntactically distinct boundary
    paths, nonidentity participating source action, initial raw defect, and
    source reselection; prove that the generated endpoint action has a
    nonidentity concrete image and that the same cell fires (d4)-(d6).
  selection_reason: >-
    This is the last witness obligation attached directly to K3 and must be
    fixed before the independent K4 pasting laws are selected.
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/IndexedDiagnosticCovarianceWitnesses.lean
  risks:
    - source or target nonidentity is asserted without a concrete component
    - the source reselection does not satisfy the named cell equation
    - d5 or d6 is quoted on a different interpretation or cell
    - the witness is misreported as the K5 non-epi coherent positive
  unchecked:
    - "K4 C0-C3"
    - "K5 raw-family classification and witnesses"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: >-
    The indexed single disk fixes one named face with left and right generating
    paths. Identity base edges carry the finite three-axis support package;
    the authored comparator and right-edge reselection use the adjacent swap
    constructed on that source package in this cycle. The initial canonical
    comparator is identity, hence the
    initial raw defect is the nonidentity swap. Every participating vertex
    index is the reviewed finite nonidentity Atom transport. Functor naturality
    proves that the generated endpoint image of the same swap is nonidentity.
    On the concrete `componentC` family component, the generated transport
    image contains the component while the canonical identity-action image
    does not. The source face equation is proved directly, and the Cycle 14
    transport theorems generate target coherence and independent obstruction
    vanishing for this same interpretation.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/IndexedDiagnosticCovarianceWitnesses.lean
  evidence:
    - indexedCovariance_participatingAction_nonidentity
    - indexedCovariance_paths_ne
    - indexedCovariance_initialRawDefect_ne_one
    - indexedCovarianceSourceReselection_ne_one
    - indexedCovariance_generatedAction_image_ne_one
    - indexedCovariance_generatedAction_componentC_mem
    - indexedCovariance_identityAction_componentC_not_mem
    - indexedCovariance_generatedAction_ne_identityAction
    - indexedCovariance_targetReselection_right_ne_one
    - indexedCovarianceSourceReselection_coherent
    - indexedCovariance_target_coherent
    - indexedCovariance_target_obstruction_vanishes
    - indexedDiagnosticCovariance_nonvacuous
  claim_mapping:
    source_labels:
      - "G-111 target theorem (g)"
      - "G-111 target proof strategy K3 witness portfolio"
    conjuncts:
      - "named connected cell with syntactically distinct paths"
      - "nonidentity participating Atom action"
      - "nonidentity initial raw defect and source reselection"
      - "nonidentity generated endpoint image and mapped reselection"
      - "generated action and identity action differ on componentC membership"
      - "same witness fires d5 coherence and d6 obstruction vanishing"
    undischarged_assumptions:
      - "none beyond the fixed finite source package and canonical finite transport"
    acceptance_point: >-
      The cycle is discharged if fixed-head review confirms concrete
      nonidentity, same-cell route integrity, source-equation proof, independent
      obstruction provenance, and separation from the K5 non-epi witness.
audits:
  premise_delta:
    discharged:
      - "named nontrivial (d4)-(d6) witness"
    remaining:
      - "K4 C0-C3"
      - "K5 classification and witnesses"
  certificate_provenance:
    discharged:
      - "source coherence is a direct package-total path equation"
      - "target coherence and vanishing are generated by Cycle 14 theorems"
      - "nonidentity is observed on the adjacent-swap axis component"
      - "generated-versus-identity action difference is observed on componentC membership"
    unresolved:
      - "K4 and K5 outputs"
  proof_use:
    used:
      - "finiteWitnessTransportHom_atomEquiv_ne_refl for the participating action"
      - "diagnosticVertexLift_endpointAction_naturality for generated nonidentity"
      - "finiteTransportAtomEquiv_dependsAB for the concrete componentC image"
      - "indexedCoherentAt_transport for target coherence"
      - "indexedTransportObstructionVanishes_transport for target vanishing"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  validation_refs:
    - "focused lake env lean IndexedDiagnosticCovarianceWitnesses.lean: pass"
    - "targeted lake build ResearchLean.AG.DoctrineFiberProduct.IndexedDiagnosticCovarianceWitnesses: pass"
    - "namespace axiom audit: 51 declarations, standard axioms only"
  initial_review_findings:
    - >-
      The first candidate used identity vertex indices, so it did not witness
      the separately required nonidentity participating action.
    - >-
      Nonidentity of the image of a source swap did not compare the generated
      package image with the canonical identity-action image on a concrete
      component.
  correction:
    - "replace identity indices with the finite nonidentity Atom transport"
    - "prove generated endpoint nonidentity through vertex-lift naturality"
    - "separate generated and identity-action package families by componentC membership"
  final_review:
    exact_head: fc541e7511cc8b5d69cf63dda75b99711b253426
    lanes:
      - "Lean A: No findings"
      - "Lean B: No findings"
      - "mathematical target fitting A: No findings"
      - "mathematical route integrity B: No findings"
    direct_correction_rerun: "4/4 pass after report provenance and PR-body validation sync"
  blocking_findings: []
  next_obligation: "K4 C0-C3 indexed diagnostic pasting coherence"
```

### Cycle 16 — indexed BC restriction comparison and mate core

```yaml
ledger_type: target_cycle_result
goal: G-111-aat-indexed-base-change-schema
cycle: 16
goal_blob_sha: 6541ee426482d09b8be4c91b2a268a6a7c3f9a0b
goal_sha256: cd372006a408707a262c24b81b590760ffb50ccc76f46f8ed80845cd60b7b3e4
base_oid: aa7aa88db246c487220efb7627dbd323aa671893
pr: 4177
reviewed_head: 47625134b3e2e9911c6eead6229fd04d21a5f5dc
merge_oid: 0c1f9ee1f8c96ed175ad4ac4ead5d6d0d5ea3ec4
tracking_issue: 4158
report_path: research/reports/G-111-aat-indexed-base-change-schema.md
selection:
  proof_state_ref: "Issue #4158 Cycle 15 merged / K4 C0-C3 selected"
  proof_dag_predecessors:
    - "Cycle 10 diagnostic-free indexed base diagram and hom"
    - "Cycle 11 coherent indexed diagnostic assembly"
    - "G-110 reviewed covariant square comparison and Beck--Chevalley mate"
  proof_obligation: >-
    Establish the K4 restriction spine without inventing a southwest-to-
    northeast base arrow. Represent a pointed BC square as a walking-arrow
    IndexedBaseDiagramHom from its left column to its right column; prove that
    the generated indexed covariant square is the reviewed G-110 comparison,
    that its direct and via-base routes are the actual G-110 routes, and that
    taking the canonical mate recovers the actual G-110 Beck--Chevalley mate.
  selection_reason: >-
    This supplies C0 and the mate-level core of C3 before package, edge,
    two-cell, comparator, endpoint, reselection, and component-triangle
    adapters are compared.
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/IndexedBCRestrictionComparison.lean
  risks:
    - a fictitious southwest-to-northeast base arrow is introduced
    - the indexed square is merely renamed instead of identified with G-110
    - the mate has different direct or via-base routes
    - the cycle is reported as all of K4 rather than C0 and the mate core
  unchecked:
    - "K4 C1 package, edge, two-cell, and comparator compatibility"
    - "K4 C2 endpoint, reselection, edge, and path compatibility"
    - "K4 C3 component-level triangle"
    - "K5 raw-family classification and witnesses"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: >-
    The two-vertex walking-arrow source and target diagrams retain the left and
    right columns of the pointed square. The diagram-hom components are its top
    and bottom arrows, and the unique naturality equation consumes the authored
    square commutativity. The resulting indexed square action is identified
    with bcCoreTransportSquareIso through its semantic provenance theorem.
    The selected reindex-and-top and bottom-and-reindex routes are the actual
    G-110 direct and via-base functors, and the canonical mate is identified
    with coreBeckChevalleyMate.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/IndexedBCRestrictionComparison.lean
  evidence:
    - indexedBCRestrictionSourceDiagram
    - indexedBCRestrictionTargetDiagram
    - indexedBCRestrictionDiagramHom
    - indexedBCRestriction_squareAction_eq_semantic
    - indexedBCRestriction_squareAction_eq_g110
    - indexedBCRestrictionDirectFunctor
    - indexedBCRestrictionViaBaseFunctor
    - indexedBCRestrictionDirectFunctor_eq_g110
    - indexedBCRestrictionViaBaseFunctor_eq_g110
    - indexedBCRestrictionMate
    - indexedBCRestrictionMate_eq_g110
  claim_mapping:
    theorem_names:
      - indexedBCRestriction_squareAction_eq_g110
      - indexedBCRestrictionDirectFunctor_eq_g110
      - indexedBCRestrictionViaBaseFunctor_eq_g110
      - indexedBCRestrictionMate_eq_g110
    source_labels:
      - "G-111 target theorem K4 C0"
      - "G-111 target theorem K4 C3 mate-level core"
    conjuncts:
      - "pointed BC square -> walking-arrow IndexedBaseDiagramHom"
      - "indexed covariant square action -> reviewed G-110 square comparison"
      - "indexed restriction routes -> actual G-110 direct and via-base routes"
      - "canonical mate -> actual G-110 Beck--Chevalley mate"
    undischarged_assumptions:
      - "G-110 pointed BC presentation and its reviewed semantic provenance"
    acceptance_point: >-
      The cycle is discharged if fixed-head review confirms that the walking-
      arrow morphism uses the authored square equation, the square and mate are
      the actual G-110 constructions, and no C1, C2, or full-C3 claim is made.
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "K4 C0 indexed restriction square comparison"
      - "K4 C3 mate-level core"
    remaining:
      - "K4 C1 package, edge, two-cell, and comparator compatibility"
      - "K4 C2 endpoint, reselection, edge, and path compatibility"
      - "K4 C3 component-level triangle"
      - "K5 raw-family classification and witnesses"
  certificate_provenance:
    discharged:
      - "square action is generated from IndexedBaseDiagramHom naturality"
      - "G-110 identification uses the reviewed semantic provenance theorem"
      - "the mate is generated by the canonical adjunction mate equivalence"
    unresolved:
      - "diagnostic component-level adapters and triangle"
  proof_use:
    used:
      - "the authored BC square commutativity in diagram-hom naturality"
      - "bcProvenanceCoreTransportSquareIso_eq_semantic in the G-110 comparison"
      - "bcLeftAdjunction and bcRightAdjunction in the canonical mate"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "focused lake env lean IndexedBCRestrictionComparison.lean: pass"
    - "targeted lake build ResearchLean.AG.DoctrineFiberProduct.IndexedBCRestrictionComparison: pass"
    - "namespace axiom audit: 46 declarations, standard axioms only"
  final_review:
    exact_head: 47625134b3e2e9911c6eead6229fd04d21a5f5dc
    lanes:
      - "Lean A: No major findings"
      - "Lean B: No major findings"
      - "mathematical target fitting A: No major findings"
      - "mathematical route integrity B: No major findings"
  blocking_findings: []
  next_obligation: "K4 C1 and C2 adapters, then the full C3 component triangle"
```

### Cycle 17 — indexed diagnostic restriction components and triangle

```yaml
ledger_type: target_cycle_result
goal: G-111-aat-indexed-base-change-schema
cycle: 17
goal_blob_sha: 6541ee426482d09b8be4c91b2a268a6a7c3f9a0b
goal_sha256: cd372006a408707a262c24b81b590760ffb50ccc76f46f8ed80845cd60b7b3e4
base_oid: 0c1f9ee1f8c96ed175ad4ac4ead5d6d0d5ea3ec4
pr: 4178
tracking_issue: 4158
report_path: research/reports/G-111-aat-indexed-base-change-schema.md
selection:
  proof_state_ref: "Issue #4158 Cycle 16 merged / remaining K4 components selected"
  proof_dag_predecessors:
    - "Cycle 16 indexed restriction square, direct/via routes, and mate core"
    - "Cycle 11-14 indexed assembly, reselection, and coherence APIs"
    - "G-110 reviewed fiberwise diagnostic natural-isomorphism compatibility"
  proof_obligation: >-
    Discharge the remaining K4 C1, C2, and full C3 component triangle. Adapt
    arbitrary indexed 2-skeleton diagnostic data to constant fiber diagrams;
    compare actual indexed top/bottom assembly with the G-110 fiberwise maps;
    retain left/right reindexing as external reviewed factors; generate
    package, edge, two-cell, comparator, endpoint, reselection, and edge/path
    comparisons; and prove the indexed-to-direct, indexed-to-via, G-110
    comparison triangle on every package component.
  selection_reason: >-
    These are all remaining K4 layers after Cycle 16 fixed the square and mate
    spine. Closing them leaves K5 as the sole theorem-level obligation family.
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/IndexedBCDiagnosticCompatibility.lean
  risks:
    - the walking-arrow shape is incorrectly used as diagnostic geometry
    - a selected reindexing is represented as a covariant indexed base arrow
    - edge equality is asserted definitionally instead of by lift uniqueness
    - G-110 compatibility is merely renamed without actual indexed K2 proof-use
    - the component triangle restates only functor equality and omits the mate
  unchecked:
    - "K5 raw-family classification and finite witnesses"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: >-
    An arbitrary indexed 2-skeleton is interpreted constantly in one core
    fiber, and fiberwise diagnostic data is converted without changing its
    package, edge, or comparator. Constant indexed transport agrees with
    fiberwise transport on packages and comparators definitionally, on edges
    by strongly-cocartesian uniqueness, and on paths by induction. The direct
    route applies left reindexing externally and top transport through the
    indexed assembly; the via route performs actual indexed bottom transport,
    recovers its constant-fiber datum by the reviewed incidence bridge, and
    only then applies external right reindexing. Their C1 components are identified with the
    actual G-110 functors. The indexed mate generates the complete diagnostic
    natural-isomorphism compatibility package, including mapped reselection and
    reselected edge/path naturality. The component triangle explicitly uses the
    G-110 mate between the two Cycle 16 equality sides.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/IndexedBCDiagnosticCompatibility.lean
  evidence:
    - indexedConstantDiagram
    - indexedConstantDiagramHom
    - FiberwiseAdmissibleTransportData.toIndexedInterpretation
    - indexedConstantTransport_package
    - indexedConstantTransport_edge
    - indexedConstantTransport_comparator
    - indexedConstantTransport_path
    - indexedConstantTransport_endpointAction
    - indexedConstantTransport_reselection
    - indexedConstantTransport_reselectedEdge
    - indexedConstantTransport_reselectedPath
    - IndexedDiagnosticInterpretation.toFiberwiseOfConstant
    - indexedBCBottomInterpretation
    - indexedBCBottomFiberwise_eq_map
    - indexedBCDirectInterpretation
    - indexedBCViaBaseInterpretation
    - indexedBCDirect_package_eq_g110
    - indexedBCViaBase_package_eq_g110
    - indexedBCDirect_edge_eq_g110
    - indexedBCViaBase_edge_eq_g110
    - indexedBCDirect_comparator_eq_g110
    - indexedBCViaBase_comparator_eq_g110
    - indexedBCDirect_path_eq_g110
    - indexedBCViaBase_path_eq_g110
    - indexedBCDirect_twoCellBase_iff_g110
    - indexedBCViaBase_twoCellBase_iff_g110
    - indexedBCDirect_endpointAction_eq_g110
    - indexedBCViaBase_endpointAction_eq_g110
    - indexedBCDirect_K3_endpointAction_eq_g110
    - indexedBCViaBase_K3_endpointAction_eq_g110
    - indexedBCDirectTransportedReselection_eq_g110
    - indexedBCViaBaseTransportedReselection_eq_g110
    - indexedBCDirect_reselectedEdge_eq_g110
    - indexedBCViaBase_reselectedEdge_eq_g110
    - indexedBCDirect_reselectedPath_eq_g110
    - indexedBCViaBase_reselectedPath_eq_g110
    - indexedBCRestrictionDiagnosticCompatibility
    - indexedBCRestriction_mappedReselection_naturality
    - indexedBCRestriction_reselectedEdge_naturality
    - indexedBCRestriction_reselectedPath_naturality
    - indexedBCRestriction_comparison_triangle_app
  claim_mapping:
    theorem_names:
      - indexedBCDirect_package_eq_g110
      - indexedBCDirect_edge_eq_g110
      - indexedBCDirect_comparator_eq_g110
      - indexedBCDirect_twoCellBase_iff_g110
      - indexedBCViaBase_package_eq_g110
      - indexedBCViaBase_edge_eq_g110
      - indexedBCViaBase_comparator_eq_g110
      - indexedBCViaBase_twoCellBase_iff_g110
      - indexedBCRestrictionDiagnosticCompatibility
      - indexedBCRestriction_comparison_triangle_app
    source_labels:
      - "G-111 target theorem K4 C1"
      - "G-111 target theorem K4 C2"
      - "G-111 target theorem K4 C3"
    conjuncts:
      - "C1 package, edge, two-cell base, comparator -> staged indexed/G-110 comparison"
      - "C2 endpoint, mapped reselection, reselected edge/path -> mate naturality package"
      - "C3 indexed-to-direct, indexed-to-via, G-110 comparison -> package-component triangle"
    undischarged_assumptions:
      - "G-110 BCPresentation and reviewed selected reindexing factors"
      - "source fiberwise diagnostic data on the indexed 2-skeleton"
    acceptance_point: >-
      K4 is discharged if fixed-head review confirms actual indexed K2 use,
      external reindex factor integrity, component coverage, and a genuine
      mate component triangle without claiming K5.
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "K4 C1 package, edge, two-cell base, and comparator compatibility"
      - "K4 C2 endpoint, reselection, edge, and path compatibility"
      - "K4 C3 component triangle"
    remaining:
      - "K5 raw-family classification and finite witnesses"
  certificate_provenance:
    discharged:
      - "indexed target edges are generated by indexedSquareTotalMap"
      - "edge comparison uses the universal square-edge law and lift uniqueness"
      - "cross-route compatibility is generated from the indexed mate"
      - "component triangle uses the reviewed G-110 mate"
    unresolved:
      - "K5 producer and positive/negative finite witnesses"
  proof_use:
    used:
      - "indexed K2 transportedInterpretation on top and bottom factors"
      - "Cycle 16 direct/via functor and mate equalities"
      - "G-110 functor composition and natural-isomorphism compatibility"
    unused: []
  structure_field_escape: none-found
  route_integrity: pending-fixed-head-rereview
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "focused lake env lean IndexedBCDiagnosticCompatibility.lean: pass"
    - "targeted lake build ResearchLean.AG.DoctrineFiberProduct.IndexedBCDiagnosticCompatibility: pass"
    - "namespace axiom audit: 56 declarations, standard axioms only"
  correction_history:
    - reviewed_head: 7eaae7a8b50cc4c61d63c4af7ccdf245d6d6e5b2
      findings:
        - "via route bypassed actual indexed bottom transport"
        - "two-cell pair did not compare corresponding paths"
        - "native indexed K3 endpoint, reselection, edge, and path APIs were not connected"
        - "triangle statement did not name its three canonical isomorphism components"
      resolution: >-
        Rebuilt the via route from the actual bottom transported interpretation,
        replaced paired truths by path equality and equation equivalence, added
        native K3-to-G-110 component bridges, and stated the triangle through
        the three named canonical isomorphisms.
  blocking_findings: []
  next_obligation: "K5 local epi iff, finite-support producer, non-epi coherent positive, and Cycle 7 negative"
```

### Cycle 3 — rejected

```yaml
ledger_type: target_cycle_result
goal: G-111-aat-indexed-base-change-schema
cycle: 3
goal_blob_sha: 01c3f96149f0e2c1298a8cfd6acc80f16bb52cfa
goal_sha256: 8383135d79d612accba04c76a3b4f96daa17e69e7fbe72474fed4428d5efd248
base_oid: 58bc52a3a4d5acee234e6cbe00108224faa5773f
pr: 4164
reviewed_head: 45e2b936775520d23fd73617616ab898cd2f59de
result:
  result_type: rejected
  checkpoint: target-proof-checkpoint
  review_verdict: "3 Reject / 1 Accept"
  merged: no
  blocking_findings:
    - "comp / pasteVertical generated comparisons remained definitionally equal; route was an inert tag"
    - "public action structure accepted an arbitrary comparison field"
    - "universal edge law quantified only identity-base vertical fiber morphisms"
    - "3-cell alias did not select two generated routes"
    - "typed-term WellFormed views were equivalent to True"
  retained_evidence:
    - "full arrow/square leaf domain elaborated"
    - "horizontal/vertical component-route formulas elaborated"
    - "canonical G-109 action/lift provenance"
```

### Cycle 5 — generated transport coherence と canonical lift compatibility

```yaml
ledger_type: target_cycle_result
goal: G-111-aat-indexed-base-change-schema
cycle: 5
goal_blob_sha: 01c3f96149f0e2c1298a8cfd6acc80f16bb52cfa
goal_sha256: 8383135d79d612accba04c76a3b4f96daa17e69e7fbe72474fed4428d5efd248
base_oid: e08c82663ce0f63a173528b06625ca1849a52da2
tracking_issue: 4158
pr: 4166
selection:
  proof_obligation: >-
    Discharge the (a)-soundness/K0 coherence API and the linked K1(b1)
    canonical-lift compatibility for the Cycle 4 validated raw schema: prove
    the generated identity and composition comparisons at the total-lift
    level, prove that every recursively generated square action identifies
    the two canonical iterated lifts, and derive horizontal, vertical, and
    comp-versus-paste 3-cell equalities rather than accepting them as authored
    data. The shared evidence is recorded once and mapped to both obligations.
  expected_result_type: proof-obligation-discharged
  risks:
    - pasting equality follows only from definitional reduction
    - comparison equality is postulated or supplied by the caller
    - proof bypasses the canonical strongly cocartesian lift
  unchecked:
    - K1(b2) strongly cocartesian preservation
    - K1.5-K5 transported-data adapter, restriction, covariance, and witnesses
result:
  proposed_result_type: proof-obligation-discharged
  completion_candidate: no
  proof_obligation_delta: >-
    Identity and composition comparisons now have total-lift factorization
    theorems. A structural induction over the decoded square term proves that
    leaf, identity, comp, horizontal paste, and vertical paste actions all
    identify the corresponding canonical iterated lifts. Strongly
    cocartesian uniqueness then proves the horizontal outer-route equality,
    vertical outer-route equality, and the actual comp-versus-pasteVertical
    3-cell equality. These theorems discharge the (a)-soundness/K0 API and,
    without being counted a second time, the K1(b1) canonical-lift
    compatibility obligation at the underlying total-morphism level.
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/IndexedBaseChangeRaw.lean
  evidence:
    - indexedFiberIdentityComparison_hom_fac
    - indexedFiberCompositionComparison_hom_fac
    - indexedSquareOuterComparison_hom_fac
    - indexedSquareTermAction_hom_fac
    - indexedHorizontalPastingCoherence
    - indexedVerticalPastingCoherence
    - indexedThreeCellCoherence
  premise_delta:
    discharged:
      - K0 generated identity/composition coherence
      - K0 horizontal and vertical outer-versus-component route equality
      - K0 comp-versus-pasteVertical 3-cell equality
      - K1(b1) canonical lift compatibility and id/comp/paste coherence
    remaining:
      - K1(b2) strongly cocartesian preservation
      - K1.5-K5 material premises
  certificate_provenance:
    discharged:
      - comparisons are generated by the G-109 unitor, compositor, and square action
      - route equality is derived from canonical lift factorization and uniqueness
    unresolved:
      - K1(b2), K1.5-K5 theorem and witness certificates
  proof_use:
    used:
      - coreFiberUnitorApp_hom_fac
      - coreFiberCompositorApp_hom_fac
      - coreFiberTransportMap_fac
      - coreFiberLift_eqCast_fac
      - coreFiberIteratedLift_isStronglyCocartesian
      - Functor.IsStronglyCocartesian.ext
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  validation_refs:
    - "focused single-file check: pass"
    - "targeted module build: pass"
    - "namespace audit: 295 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "K1(b2) prove strongly cocartesian preservation, then K1.5 construct the morphism-indexed transported-data adapter"
audits:
  initial_review:
    exact_head: 8c9e6ee1363acd8659507734e30fc0614a647bd0
    verdict: "3 Accept / 1 Reject"
    central_finding:
      - >-
        The report counted all total-lift factorization and paste coherence as
        K0 while leaving K1(b1) canonical lift compatibility wholly pending,
        creating a proof-DAG mismatch and double-counting risk.
    correction:
      - >-
        Split the claim mapping between (a)-soundness/K0 and K1(b1), mark
        K1(b1) discharged by the same evidence without duplicate credit, and
        retain K1(b2) plus K1.5-K5 as the exact remaining obligations.
  rerun:
    exact_head: f90a1e2a4132504e73f0af7c59650942e4652fa8
    verdict: "4 Accept / 0 Reject; No major findings"
    blocking_findings: []
```

### Cycle 6 — square transport preserves strongly cocartesian morphisms

```yaml
ledger_type: target_cycle_result
goal: G-111-aat-indexed-base-change-schema
cycle: 6
goal_blob_sha: 01c3f96149f0e2c1298a8cfd6acc80f16bb52cfa
goal_sha256: 8383135d79d612accba04c76a3b4f96daa17e69e7fbe72474fed4428d5efd248
base_oid: 200401e9c2f6ca9adb29bb4e0c946ed49ba32aa8
tracking_issue: 4158
pr: 4167
selection:
  proof_obligation: >-
    Discharge K1(b2): for every validated commutative square and every
    strongly cocartesian total morphism over its left edge, prove that the
    square-generated total morphism is strongly cocartesian over the right
    edge. This preservation theorem must use the same Cycle 4 producer and
    may not be replaced by the strongness of a single canonical lift.
  expected_result_type: proof-obligation-discharged
  risks:
    - restating canonical-lift existence instead of preservation
    - accepting target strongness as an input certificate
    - defining a separate action that bypasses indexedSquareTotalMap
  unchecked:
    - K1.5-K5 transported-data adapter, restriction, covariance, and witnesses
result:
  proposed_result_type: proof-obligation-discharged
  completion_candidate: no
  proof_obligation_delta: >-
    indexedSquareTotalMap_isStronglyCocartesian consumes a strongly
    cocartesian left-edge total morphism, composes it with the canonical
    bottom lift, rewrites the resulting strong composite through the universal
    square-edge law and square commutativity, and cancels the canonical top
    lift by IsStronglyCocartesian.of_comp. The conclusion is strongness of the
    exact indexedSquareTotalMap output over the right edge.
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/IndexedBaseChangeRaw.lean
  evidence:
    - indexedSquareTotalMap_isStronglyCocartesian
    - indexedUniversalSquareEdgeLaw
    - indexedSquareTotalMap_isHomLift
  premise_delta:
    discharged:
      - K1(b2) strongly cocartesian preservation
    remaining:
      - K1.5-K5 material premises
  certificate_provenance:
    discharged:
      - target strongness is derived from the source direction hypothesis and the generated square map
    unresolved:
      - K1.5-K5 theorem and witness certificates
  proof_use:
    used:
      - indexedUniversalSquareEdgeLaw
      - coreFiberLift_isStronglyCocartesian
      - Functor.IsStronglyCocartesian.comp
      - Functor.IsStronglyCocartesian.of_comp
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  validation_refs:
    - "focused single-file check: pass"
    - "targeted module build: pass"
    - "namespace audit: 296 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "K1.5 construct the morphism-indexed transported-data adapter"
audits:
  initial_review:
    exact_head: 0040adab3b2926f4c206ba5e85d0f3862ed90494
    verdict: "4 Accept / 0 Reject; No major findings"
    blocking_findings: []
```

### Cycle 7 — K1.5 two-cell base-congruence no-go

```yaml
ledger_type: target_cycle_result
goal: G-111-aat-indexed-base-change-schema
cycle: 7
goal_blob_sha: 01c3f96149f0e2c1298a8cfd6acc80f16bb52cfa
goal_sha256: 8383135d79d612accba04c76a3b4f96daa17e69e7fbe72474fed4428d5efd248
base_oid: d552c4b57c12b523cb2f94dc093b892f60abfdd8
tracking_issue: 4158
selection:
  proof_obligation: >-
    Construct K1.5, the morphism-indexed adapter from the Cycle 4 generated
    action to the G-110 DiagnosticPackageTotalAction interface, and then use
    that same output in K2. In particular, determine whether source two-cell
    base equalities generate the target twoCellBase field without accepting
    target diagnostic data or a target equality certificate from the caller.
  expected_result_type: proof-obligation-discharged-or-formal-stop
  risks:
    - supplying target twoCellBase as authored adapter input
    - silently cancelling a non-epimorphic vertex transport index
    - restricting the full ExtInst_U domain to epimorphic indices
result:
  proposed_result_type: target-refuted
  completion_candidate: no
  proof_obligation_delta: >-
    Pasting validated edge squares transports a source equality only to an
    equality after precomposition by the vertex index. The generic theorem
    indexedTargetBaseCongruenceAt_iff_epi identifies unrestricted cancellation
    with Epi. More decisively, the target-scoped witness duplicates every
    source of the reviewed finite doctrine by a Boolean tag. The false-tag
    inclusion is a valid ExtInst arrow. Target identity and constant-tag
    endomorphisms are distinct but agree after that inclusion. They form two
    actual ValidatedIndexedBaseSquare leaves over the same source identity
    edge. finiteTwoLoopPresentation and finiteTwoLoopSourceData provide one
    finite two-loop presentation with an admissible source two-cell whose path
    bases are equal. IndexedValidatedTwoCellBaseGeneration states the exact
    full-domain bridge from an equal source-path pair plus its two validated
    squares to the target path-base equality, and
    finiteValidatedSquares_refute_twoCellBaseGeneration proves its negation.
    Thus the fixed full-domain K1.5/K2 target twoCellBase conjunct has a
    concrete counterexample.
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/IndexedBaseChangeTwoCellNoGo.lean
  evidence:
    - indexedTargetBaseCongruenceAt_iff_epi
    - finiteOneToTwo_comp_identity_eq_constant
    - finiteTwoSourceIdentity_ne_constant
    - finiteOneToTwoIndex_not_epi
    - finiteOneToTwo_no_targetBaseCongruence
    - indexedTargetBaseCongruenceAt_identity
    - finiteDuplicateIndex_comp_identity_eq_constant
    - finiteDuplicateIdentity_ne_constant
    - finiteDuplicateIdentitySquare
    - finiteDuplicateConstantSquare
    - finiteTwoLoopPresentation
    - finiteTwoLoopSourceData
    - finiteTwoLoopValidatedSquare
    - IndexedValidatedTwoCellBaseGeneration
    - finiteValidatedSquares_refute_twoCellBaseGeneration
  premise_delta:
    discharged: []
    candidate_route_only:
      - >-
        Existing APIs suggest component mappings for vertex packages, edge
        maps, edge strongness, and endpoint comparators; no assembled adapter
        is constructed or discharged in this cycle.
    remaining:
      - K1.5 target twoCellBase generation and complete transported-data adapter
      - K2 arbitrary-source target transported data
      - K3 C0-C3 restriction comparison
      - K4 d1-d6 full-domain covariance
      - K5 named nonvacuity and proper-extension witnesses
  certificate_provenance:
    rejected_inputs:
      - caller-supplied target twoCellBase
      - caller-supplied global base action or base-congruence certificate
    rejected_repairs:
      - >-
        Requiring every index to be epi removes the finite witness but weakens
        the fixed full ExtInst_U domain.
      - >-
        Replacing arbitrary validated right-edge squares by images of a global
        endofunctor changes the fixed all-square meaning; it is a possible new
        target, not a same-semantics signature repair.
  proof_use:
    used:
      - CategoryTheory.epi_iff_forall_injective
      - cancel_epi
      - ExtInstHom.ext
      - ExactDoctrineHom.ext
      - typedPresentationToSemantic
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  validation_refs:
    - "focused single-file check: pass"
    - "targeted module build: pass"
    - "namespace audit: 31 declarations, standard axioms only"
  blocking_findings: []
  stop_condition: >-
    target-refuted: one admissible finite source two-cell and two actual F0
    validated square leaves have equal source path bases but distinct target
    path bases. Epi restriction or globally generated right edges would change
    the fixed target. Any replacement target is reserved to the human owner.
audits:
  initial_review:
    exact_head: 377145efb4956445414a8283c88e38e7b38713d4
    verdict: "0 Accept / 4 Reject"
    central_findings:
      - >-
        The first artifact proved only a generic non-epi cancellation
        obstruction and did not connect it to finite admissible source data,
        actual F0 validated squares, or the K1.5/K2 target bridge.
      - >-
        The goal-defect classification assumed without proof that a global
        base action preserved the same all-square semantics; if the fixed
        bridge is refuted, the failure policy instead requires target-refuted.
      - >-
        Component API mappings were described as constructible without an
        assembled Lean adapter.
    correction:
      - >-
        Add a satisfying identity-index instance, a duplicated-source finite
        doctrine, two explicit validated square leaves, a one-vertex/two-loop
        presentation with admissible source data, and the exact target
        twoCellBase generation law plus its refutation.
      - >-
        Reclassify the stop as target-refuted and mark component mappings as an
        unassembled candidate route rather than discharged output.
  rerun:
    exact_head: c1b50f467f8734543d7270d17e88ca5bba293a83
    verdict: "4 Accept / 0 Reject; No major findings"
    blocking_findings: []
```

### Cycle 4 — validated raw input と term-indexed generated action

```yaml
ledger_type: target_cycle_result
goal: G-111-aat-indexed-base-change-schema
cycle: 4
goal_blob_sha: 01c3f96149f0e2c1298a8cfd6acc80f16bb52cfa
goal_sha256: 8383135d79d612accba04c76a3b4f96daa17e69e7fbe72474fed4428d5efd248
base_oid: 58bc52a3a4d5acee234e6cbe00108224faa5773f
tracking_issue: 4158
report_path: research/reports/G-111-aat-indexed-base-change-schema.md
selection:
  proof_state_ref: "Issue #4158: Cycle 3 rejected; Cycle 4 schema reselection"
  proof_dag_predecessors:
    - "G-110 PR #4153 final head a1471483, merge 315a2537"
    - "G-109 CorePseudofunctor canonical lift/functor/compositor/unitor API"
  proof_obligation: >-
    Reselect F0 so that decoder compatibility has positive and negative raw
    instances, every public producer consumes validated input, pasted terms are
    sent to recursive componentwise comparison routes rather than an inert tag,
    the square universal law quantifies arbitrary package-total morphisms, and
    the theorem-level 3-cell type names the actual comp and paste routes.
  expected_result_type: proof-obligation-discharged
  risks:
    - validated input is bypassed by a public caller-supplied action field
    - comp and pasteVertical generated comparisons are definitionally equal
    - square universal law silently restricts to identity-base fiber morphisms
    - 3-cell equality accepts arbitrary comparison inputs
  unchecked:
    - K0 identity/composition and horizontal/vertical outer-route coherence proofs
    - K1-K5 cocartesian compatibility, restriction, covariance, and witnesses
result:
  proposed_result_type: proof-obligation-discharged
  completion_candidate: no
  proof_obligation_delta: >-
    IndexedBaseHomInput and IndexedBaseSquareInput are recursive partial raw
    syntax. Their decoders fail on missing arrow leaves or missing square
    commutativity witnesses, yielding decidable positive and negative trees.
    Validated artifacts retain the successfully decoded typed term and its
    decoder equation. Public fiber/total/square producers consume those
    validated artifacts.
    The square action is a definition with no caller-supplied comparison field:
    comp selects the canonical outer route, while horizontal/vertical paste
    recursively select componentwise routes. The comp/pasteVertical equality is
    no longer definitional and is the concrete theorem-level 3-cell obligation.
    IndexedUniversalSquareEdgeLaw quantifies every raw commutative square and
    every package-total morphism lying over its left edge, with its factorization
    theorem proved by strong cocartesian universality; a separate public theorem
    records that the generated morphism lies over the square's right edge.
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/IndexedBaseChangeRaw.lean
  evidence:
    - IndexedBaseHomInput.WellFormed
    - IndexedBaseHomInput.ofTerm_wellFormed
    - IndexedBaseHomInput.missing_not_wellFormed
    - IndexedBaseSquareInput.WellFormed
    - IndexedBaseSquareInput.ofTerm_wellFormed
    - IndexedBaseSquareInput.missing_not_wellFormed
    - ValidatedIndexedBaseHom
    - ValidatedIndexedBaseSquare
    - indexedFiberAction
    - indexedTotalLift
    - indexedUniversalEdgeLaw
    - indexedSquareTotalMap
    - indexedSquareTotalMap_isHomLift
    - indexedUniversalSquareEdgeLaw
    - indexedSquareTermAction
    - indexedSquareTermAction_pasteHorizontal
    - indexedSquareTermAction_pasteVertical
    - IndexedHorizontalPastingCoherenceType
    - IndexedVerticalPastingCoherenceType
    - IndexedThreeCellCoherenceType
  claim_mapping:
    source_labels:
      - "target theorem (a): raw generator / indexed action / soundness type spine"
      - "target theorem stated scope: F0 universe and producer contract"
    conjuncts:
      - "all base arrows and commutative squares -> typed leaf terms -> positive validated inputs"
      - "raw trees with a missing arrow or commutativity leaf -> explicit negative instances"
      - "arrow fiber/total action -> validated input + G-109 canonical producer"
      - "all square/package-total edges -> indexedSquareTotalMap + indexedUniversalSquareEdgeLaw"
      - "horizontal/vertical paste -> recursive componentwise generated comparison"
      - "3-cell choice -> equality of actual comp and pasteVertical generated routes"
    undischarged_assumptions:
      - K0 coherence theorem bundle
      - K1-K5 material premises
    acceptance_point: >-
      F0 fixes the diagnostic-free schema signature and allowable generated
      producers. It does not claim K0, later conjuncts, or GOAL completion.
    port_status: unported
audits:
  initial_review:
    exact_head: e621df12e6c8240c9a382372f20b641e4c51d8f1
    verdict: "4 Reject / 0 Accept"
    central_findings:
      - "typed-term Option wrappers did not validate a recursive raw payload"
      - "public raw/decoded square comparison helpers bypassed validated recursive action"
      - "square-total output lacked a public right-edge IsHomLift theorem"
    correction:
      - "replace whole-term Option wrappers by recursive partial raw trees"
      - "store decoder success equation and decoded term in validated artifacts"
      - "make raw outer helpers private and require validated children in public component routes"
      - "publish indexedSquareTotalMap_isHomLift"
  premise_delta:
    discharged:
      - "decidable decoder compatibility with positive and negative raw instances"
      - "validated-input boundary for every public arrow/square action producer"
      - "universal arrow and square/package-total edge-law signatures"
      - "theorem-level concrete comp/paste 3-cell signature"
    remaining:
      - "K0-K5 material premises"
  certificate_provenance:
    discharged:
      - "fiber/total/square outputs are definitions from G-109 and category iso primitives"
      - "no public structure field accepts an action comparison"
    unresolved:
      - "K0 outer-vs-component route equality proofs"
  proof_use:
    used:
      - "coreFiberTransportFunctor/coreFiberLift in validated arrow action"
      - "IsStronglyCocartesian.map/fac in arbitrary square-total transport law"
      - "child square actions, compositors, whiskering, and associators in paste routes"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: >-
    Recursive raw decoder inputs have concrete successful trees and failed
    trees with missing leaves. Every actual arrow and commutative square remains
    representable through ofTerm.
    The comp/paste equality is not definitional and remains an explicit K0 law.
  validation_refs:
    - "focused single-file check: pass"
    - "targeted module build: pass"
    - "namespace audit after initial-review correction: 288 declarations, standard axioms only"
    - "negative focused refutation: comp/pasteVertical generated comparison equality is not rfl"
    - "diff, Unicode, placeholder, prohibited vocabulary, privacy, import-direction, manifest, and umbrella scans: pass"
  allowable_producers:
    - "validated arrow fiber action: indexedFiberAction"
    - "validated arrow total lift: indexedTotalLift"
    - "validated square-total map: indexedSquareTotalMap"
    - "validated recursive square comparison: indexedSquareTermAction"
    - "validated outer square comparison: indexedSquareOuterComparison"
    - "validated child horizontal/vertical component routes"
    - "canonical identity/composition comparisons"
  blocking_findings: []
  next_obligation: "K0 prove identity/composition and horizontal/vertical outer-route coherence"
```
