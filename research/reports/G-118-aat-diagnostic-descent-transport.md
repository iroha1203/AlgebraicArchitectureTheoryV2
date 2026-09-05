# G-118 — Qualified Comparison Transport and Diagnostic Information Loss

一次仕様は
[`research/goals/G-118-aat-diagnostic-descent-transport.md`](../goals/G-118-aat-diagnostic-descent-transport.md)
である。本 report は固定 target A–D の proof obligation、Lean 宣言、入力 provenance、
proof-use、査読結果を cycle ごとに記録する。

## Proof state

- fixed base: `42cec580bbe8b748360abaa17145cb4af3be0be0`
- tracking Issue: #4367
- completed obligations: F0 typing、A comparison stabilizer API、B1 generated-image / actual input-map classification、B2 fixed comparison decisions、C1 complete-geometry presentation transport、C2 actual edge reselection、C3 generated base-transport preservation and reflection
- current obligation: D coefficient nonfactorization and transport
- pending obligations: D、C1/C2/C3 closure、completion audit
- current target state: Cycle 8 implementation candidate の `target-proof-checkpoint`
- next obligation: D coefficient nonfactorization at the fixed datum

## Cycle 1 — F0 fixed source-map typing

```yaml
ledger_type: target_cycle_result
goal: G-118-aat-diagnostic-descent-transport
cycle: 1
goal_blob_sha: 641f3255062d2578ef070cbb77c019cc28c3febf
base_oid: 42cec580bbe8b748360abaa17145cb4af3be0be0
tracking_issue: 4367
report_path: research/reports/G-118-aat-diagnostic-descent-transport.md
selection:
  proof_state_ref: "Issue #4367 initial proof state: F0 pending; A--D unproved"
  proof_dag_predecessors:
    - "G-115 reviewed geometry declarations fixed by the GOAL source map"
    - "G-117 target-refuted record; no G-117 conclusion is imported as a proof premise"
  proof_obligation: "F0: elaborate the fixed source-map declarations at the exact universes, endpoint geometries, and variance required by G-118"
  selection_reason: "F0 is the unique next action in Issue #4367 and fixes the types consumed by every later A--D declaration without selecting a proof branch."
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - research/lean/ResearchLean/AG/DoctrineFiberProduct/QualifiedComparisonTransportTyping.lean
    - AAT.AG.DoctrineFiberProduct.QualifiedComparisonTransportTyping
  risks:
    - "source and target endpoint order for GeometryTotalHom.comp"
    - "source automorphism homomorphisms landing in different generated geometry groups"
    - "canonical-authored versus generated exact isomorphism direction"
    - "UpperDecisionWitness.solution and upperDecisionSolution definitional alignment"
  unchecked:
    - "all A--D theorem conclusions and material-premise discharge"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "The fixed G-115 source declarations now elaborate together at the G-118 universe, endpoint, relational-composite, coefficient, normalization, and decision-witness types; no A--D conclusion is claimed."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/DoctrineFiberProduct/QualifiedComparisonTransportTyping.lean
  evidence:
    - "focused elaboration of QualifiedComparisonTransportTyping.lean"
  claim_mapping:
    theorem_names: []
    source_labels:
      - "target proof strategy F0 typing"
      - "fixed source map"
    conjuncts:
      - "B1/C3 source automorphism maps -> two bundled MonoidHom examples"
      - "B1/C3 comparison typing -> mate, GeomReadHom, paired-composite, and both route-factorization examples"
      - "C1 endpoint changes -> two exact geometry Iso, conjugation, four coefficient identity, solution equivalence, and normalization examples"
      - "B2/D fixed datum -> solution/component equality and typed positive/negative decision-witness examples"
      - "D route qualification -> generatedPulledIdentityComparator_coefficient_id example"
    undischarged_assumptions:
      - "all discharge-required rows in the target material premise ledger"
    acceptance_point: "F0 discharges only the selected type-alignment obligation and does not discharge an A--D material premise."
    port_status: not-applicable
audits:
  premise_delta:
    discharged: []
    remaining:
      - "all target material premise ledger discharge-required rows"
  certificate_provenance:
    discharged: []
    unresolved:
      - "B2 decisions, C transport witnesses, and D nonfactorization"
  proof_use:
    used: []
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "cd research/lean && lake env lean ResearchLean/AG/DoctrineFiberProduct/QualifiedComparisonTransportTyping.lean; exit 0"
    - "F0 explicit examples cover both source MonoidHom targets, GeomReadHom/GeometryTotalHom mate direction, the B1/C3 paired composite, both fac theorems, both endpoint isomorphisms and conjugations, four endpoint coefficient identities, solution equivalence and normalizations, generated pulled identity coefficient, fixed solution equality, and four positive/negative witnesses"
    - "git diff --check; exit 0"
    - "hidden/BiDi and axiom/admit/sorry/unsafe scans on the F0 file; no matches"
    - "PR #4370 fixed head 6ae5be2c07a366cbe8042d60d551832dcec008eb; CI 7/7 pass"
    - "four independent fixed-head lanes: all No major findings"
    - "review audit: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4370#issuecomment-5549375449"
    - "acceptance regression: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4370#issuecomment-5549375572"
    - "merged by PR #4370 at b537678d24b16f88f709dc32356e6a409cebd4ee"
  blocking_findings: []
  next_obligation: "A: construct the comparison stabilizer, both projections/kernels, and nonempty-fiber torsor actions"
```

### F0 acceptance spine

F0 の scaffold は新しい certificate、solution、intertwining field を導入しない。B1/C3 の
二つの source 群準同型と比較合成、generated mate と `GeomReadHom`、両 route の factorization、
C1 の正方向 exact endpoint isomorphism・共役・係数恒等・solution normalization、固定 decision
datum の solution 同一性と正負宣言を既存名のまま型検査する。従ってこの cycle の claim は
型整合だけで、A–D の分類・決定・移送・非因子化はすべて未証明である。

## Cycle 2 — A comparison stabilizer and fibers

```yaml
ledger_type: target_cycle_result
goal: G-118-aat-diagnostic-descent-transport
cycle: 2
goal_blob_sha: 641f3255062d2578ef070cbb77c019cc28c3febf
base_oid: b537678d24b16f88f709dc32356e6a409cebd4ee
tracking_issue: 4367
report_path: research/reports/G-118-aat-diagnostic-descent-transport.md
selection:
  proof_state_ref: "Cycle 1 accepted F0; A is the unique next obligation"
  proof_dag_predecessors:
    - "F0 fixed endpoint, variance, composition, and conjugation types"
    - "CompositeFiberAut.conjugationMulEquiv"
  proof_obligation: "A: construct Gamma_c, both projections, their images and kernels, both nonempty-fiber torsors, and the isomorphic-comparison graph classification"
  selection_reason: "A is the reusable general API required by every B/C/D classification statement."
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - research/lean/ResearchLean/AG/DoctrineFiberProduct/QualifiedComparisonStabilizer.lean
    - AAT.AG.DoctrineFiberProduct.qualifiedComparisonSubgroup
    - AAT.AG.DoctrineFiberProduct.qualifiedComparisonIsoGraphMulEquiv
  risks:
    - "Aut multiplication reverses the displayed categorical hom composition"
    - "left stabilizer action must be proved closed on the actual lift fiber"
    - "projection kernels must identify with endpoint stabilizers rather than a renamed membership predicate"
    - "chosen fiber coordinates must remain separate from the choice-free action theorem"
  unchecked:
    - "all concrete B1/B2, C1/C2/C3, and D obligations"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "The arbitrary-comparison group, projections, projection image criteria, kernel equivalences, choice-free simply-transitive actions, chosen-point coordinates, and the isomorphic-comparison conjugation graph are constructed without new assumptions."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/DoctrineFiberProduct/QualifiedComparisonStabilizer.lean
  claim_mapping:
    theorem_names:
      - qualifiedComparisonSubgroup
      - qualifiedComparisonSourceProjection
      - qualifiedComparisonTargetProjection
      - qualifiedComparisonTargetStabilizer
      - qualifiedComparisonSourceStabilizer
      - mem_qualifiedComparisonSubgroup
      - mem_qualifiedComparisonTargetStabilizer
      - mem_qualifiedComparisonSourceStabilizer
      - QualifiedComparisonTargetLift
      - QualifiedComparisonSourceLift
      - qualifiedComparisonTargetLiftAction
      - qualifiedComparisonTargetLiftSMul
      - qualifiedComparisonTargetLiftMulAction
      - qualifiedComparisonTargetLiftAction_free
      - qualifiedComparisonTargetLiftAction_transitive
      - qualifiedComparisonSourceProjectionKernelMulEquiv
      - qualifiedComparisonTargetProjectionKernelMulEquiv
      - qualifiedComparisonTargetLift_existsUnique
      - qualifiedComparisonTargetLiftEquiv
      - qualifiedComparisonSourceLiftAction
      - qualifiedComparisonSourceLiftSMul
      - qualifiedComparisonSourceLiftMulAction
      - qualifiedComparisonSourceLiftAction_free
      - qualifiedComparisonSourceLiftAction_transitive
      - qualifiedComparisonSourceLift_existsUnique
      - qualifiedComparisonSourceLiftEquiv
      - mem_qualifiedComparisonSourceProjection_range_iff
      - mem_qualifiedComparisonTargetProjection_range_iff
      - qualifiedComparisonIsoGraphMulEquiv
      - qualifiedComparisonIsoSourceProjectionMulEquiv
      - qualifiedComparisonIsoTargetProjectionMulEquiv
      - qualifiedComparisonIsoSourceProjectionMulEquiv_apply
      - qualifiedComparisonIsoTargetProjectionMulEquiv_apply
      - qualifiedComparisonIsoSourceProjection_surjective
      - qualifiedComparisonIsoTargetProjection_surjective
      - qualifiedComparisonTargetStabilizer_eq_bot_of_iso
      - qualifiedComparisonSourceStabilizer_eq_bot_of_iso
    source_labels:
      - "target theorem (A)"
    conjuncts:
      - "Gamma_c group and projections -> qualifiedComparisonSubgroup and the two projection MonoidHom declarations"
      - "projection images -> the two mem_projection_range_iff theorems"
      - "projection kernels -> two kernel MulEquiv declarations to the actual endpoint stabilizers"
      - "nonempty fibers -> named MulAction instances, free/transitive/existsUnique theorems, and chosen-origin Equiv declarations"
      - "isomorphic comparison -> conjugation graph MulEquiv, both projection MulEquiv declarations, surjectivity, and trivial stabilizers"
    undischarged_assumptions:
      - "all B/C/D material-premise rows"
    acceptance_point: "A is general in arbitrary U,G,H,c and uses an Iso only in the explicitly conditional graph branch."
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "A comparison group, images/kernels, fiber actions, and conditional isomorphic graph"
    remaining:
      - "B actual-map classification and fixed decisions"
      - "C transport/reflection/coherence"
      - "D coefficient observation and nonfactorization"
  certificate_provenance:
    discharged:
      - "the Iso branch consumes the actual Iso and CompositeFiberAut.conjugationMulEquiv"
    unresolved:
      - "all named B2/C/D decisions"
  proof_use:
    used:
      - "CompositeFiberAut.conjugationMulEquiv and conjugationMulEquiv_hom in the graph classification"
      - "actual comparison equations in subgroup closure, fiber actions, kernel identifications, and graph recovery"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "cd research/lean && lake env lean ResearchLean/AG/DoctrineFiberProduct/QualifiedComparisonStabilizer.lean; exit 0"
    - "module terminal axiom audit: 37 declarations, standard axioms only"
    - "PR #4371 revised fixed head 9befcdf2b38e487e53b3e7dc4afd9d616bf3e3cc; CI 7/7 pass"
    - "four fresh independent revised fixed-head lanes: all No major findings"
    - "review audit: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4371#issuecomment-5549563800"
    - "acceptance regression: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4371#issuecomment-5549563970"
    - "merged by PR #4371 at 073636cf15f5ec3b4fc139f9a21a3e70e05fce98"
  blocking_findings: []
  next_obligation: "B1: connect generated endpoint maps to Gamma and classify J_i by actual geometry input maps"
```

## Cycle 3 — B1 generated-image residual classification

```yaml
ledger_type: target_cycle_result
goal: G-118-aat-diagnostic-descent-transport
cycle: 3
goal_blob_sha: 641f3255062d2578ef070cbb77c019cc28c3febf
base_oid: 073636cf15f5ec3b4fc139f9a21a3e70e05fce98
tracking_issue: 4367
report_path: research/reports/G-118-aat-diagnostic-descent-transport.md
selection:
  proof_state_ref: "Cycles 1--2 accepted F0 and A; B1 is the next fixed-target obligation"
  proof_dag_predecessors:
    - "Cycle 2 qualifiedComparisonSubgroup, target stabilizer, and target-lift action"
    - "generated base/pulled route factorizations and generated mate triangle"
    - "the two fixed generated CompositeFiberAut MonoidHom declarations"
  proof_obligation: "B1a: prove every generated diagonal pair lies in Gamma and classify all generated pairs by the residual source subgroup J_i and its right cosets"
  selection_reason: "This derives the algebraic generated-image half of B1 directly from the actual route legs and leaves the larger literal input-map characterization as the next named sub-obligation rather than hiding it."
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - research/lean/ResearchLean/AG/DoctrineFiberProduct/QualifiedComparisonGeneratedClassification.lean
    - AAT.AG.DoctrineFiberProduct.UpperGeometryCompatibleProblemInputData.generatedCompatibleUpperGeometryMateAt_automorphism_intertwining
    - AAT.AG.DoctrineFiberProduct.UpperGeometryCompatibleProblemInputData.generatedQualifiedComparisonRelation_iff_exists_kernel_factor
  risks:
    - "GeometryTotalHom.comp and CompositeFiberAut multiplication use the established categorical order"
    - "the generated diagonal must be derived from both actual route factorizations, not assumed as a certificate"
    - "a source preimage subgroup must not be confused with a proof that each Geometry input map is fixed"
  unchecked:
    - "B1b literal core, atomEquiv, objectMap, equation, operation, invariant, axis, coordinate, coefficient, support, axis-image, and observable-image characterization"
    - "all B2/C/D obligations"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "For every I, i, and source automorphism, the actual generated route factorizations and mate triangle imply generated endpoint intertwining. The generated comparison relation is then equivalent to target-stabilizer membership of the generated pulled-image difference, to membership of pulledChange * baseChange^-1 in the actual pulled preimage subgroup, and to a residual factor pulledChange = j * baseChange. A named fixed-datum negative instance establishes nonvacuity."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/DoctrineFiberProduct/QualifiedComparisonGeneratedClassification.lean
  claim_mapping:
    theorem_names:
      - generatedCompatibleUpperGeometryMateAt_automorphism_intertwining
      - GeneratedQualifiedComparisonRelation
      - generatedQualifiedComparisonRelation_diagonal
      - generatedPulledComparisonKernel
      - generatedQualifiedComparisonRelation_iff_difference_mem
      - generatedQualifiedComparisonRelation_iff_target_stabilizer_image
      - generatedQualifiedComparisonRelation_iff_exists_kernel_factor
      - UpperDecisionWitness.generatedQualifiedComparisonRelation_base_identity_not
    source_labels:
      - "target theorem (B1), generated-image and residual-coset clauses"
    conjuncts:
      - "every generated diagonal pair lies in Gamma -> generatedCompatibleUpperGeometryMateAt_automorphism_intertwining and generatedQualifiedComparisonRelation_diagonal"
      - "J_i is the pulled generated-map preimage of K_Y(c_i) -> generatedPulledComparisonKernel"
      - "R_i(a,d) iff the generated pulled-image difference belongs to K_Y(c_i) -> generatedQualifiedComparisonRelation_iff_target_stabilizer_image"
      - "R_i(a,d) iff d*a^-1 belongs to J_i -> generatedQualifiedComparisonRelation_iff_difference_mem"
      - "R_i(a,d) iff d=j*a for a residual j in J_i -> generatedQualifiedComparisonRelation_iff_exists_kernel_factor"
      - "the new relation has a concrete failing pair -> UpperDecisionWitness.generatedQualifiedComparisonRelation_base_identity_not"
    undischarged_assumptions:
      - "B1b literal actual input-map characterization"
      - "all B2/C/D material-premise rows"
    acceptance_point: "The arbitrary-source intertwining is derived from the generated route legs and mate triangle; no solution or intertwining certificate is added to the input."
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "B1 generated diagonal intertwining from actual generated routes"
      - "B1 target-image criterion, residual subgroup, source difference-membership criterion, and right-coset factorization"
      - "new relation positive and negative instances for nonvacuity"
    remaining:
      - "B1 actual input-map characterization"
      - "B2 fixed positive/negative decisions"
      - "C transport/reflection/coherence"
      - "D coefficient observation and nonfactorization"
  certificate_provenance:
    discharged:
      - "intertwining consumes generatedBaseCompositeFiberAutAt_fac, generatedPulledCompositeFiberAutAt_fac, and generatedCompatibleUpperGeometryMateAt_triangle"
    unresolved:
      - "B2/C/D named decision and transport witnesses"
  proof_use:
    used:
      - "Cycle 2 target stabilizer and target-lift MulAction in the reverse residual implication"
      - "both generated endpoint MonoidHom maps in the subgroup preimage and difference calculation"
      - "strongly-cartesian route-leg extensionality in the arbitrary-source intertwining proof"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "cd research/lean && lake build ResearchLean.AG.DoctrineFiberProduct.QualifiedComparisonStabilizer; exit 0; targeted direct dependency DAG only, not the Research aggregate/full build"
    - "cd research/lean && lake env lean ResearchLean/AG/DoctrineFiberProduct/QualifiedComparisonGeneratedClassification.lean; exit 0"
    - "module terminal axiom audit: 9 namespace declarations, including 8 public mapped declarations, standard axioms only"
    - "PR #4372 final fixed head 293e45c9fcad0595aba346859ac1c5c727da3e88; CI 7/7 pass"
    - "four fresh independent final fixed-head lanes: all No major findings"
    - "review audit: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4372#issuecomment-5549773608"
    - "acceptance regression: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4372#issuecomment-5549773604"
    - "merged by PR #4372 at 202effb88355309bbae041dfcaf782d2401e3722"
  blocking_findings: []
  next_obligation: "B1b: characterize residual-kernel membership by the literal actual Geometry input maps and close with GeomReadHom/GeometryTotalHom extensionality"
```

## Cycle 4 — B1 actual generated input-map characterization

```yaml
ledger_type: target_cycle_result
goal: G-118-aat-diagnostic-descent-transport
cycle: 4
goal_blob_sha: 641f3255062d2578ef070cbb77c019cc28c3febf
base_oid: 202effb88355309bbae041dfcaf782d2401e3722
tracking_issue: 4367
report_path: research/reports/G-118-aat-diagnostic-descent-transport.md
selection:
  proof_state_ref: "Issue #4367 Cycle 4 selection: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/4367#issuecomment-5549820812"
  proof_dag_predecessors:
    - "Cycle 3 generatedPulledComparisonKernel and generatedQualifiedComparisonRelation_iff_difference_mem"
    - "SignedExactCoreReadingHom.ext, PackageTotalHom.ext, GeomReadHom.ext, and GeometryTotalHom.ext"
    - "the fixed Cycle 3 negative generated relation witness"
  proof_obligation: "B1b: characterize J_i membership by every literal computational component of the actual generated comparison composite and connect that iff to R_i(a,d) through d*a^-1"
  selection_reason: "This is the sole remaining B1 clause and prevents the residual subgroup from remaining an opaque membership predicate."
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - research/lean/ResearchLean/AG/DoctrineFiberProduct/QualifiedComparisonInputCharacterization.lean
    - AAT.AG.DoctrineFiberProduct.UpperGeometryCompatibleProblemInputData.mem_generatedPulledComparisonKernel_iff_inputConditions
    - AAT.AG.DoctrineFiberProduct.UpperGeometryCompatibleProblemInputData.generatedQualifiedComparisonRelation_iff_inputConditions
  risks:
    - "dependent equation-transport and geometry maps require HEq rather than an ill-typed homogeneous equality"
    - "the condition package must contain computational components, not whole-hom equality or the desired membership conclusion"
    - "the necessary direction and a concrete failing instance must remain visible"
  unchecked:
    - "all B2/C/D obligations"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "For all I,i and source changes, membership in J_i is equivalent to equality of the actual composite and comparison on pointed source/atom maps, signed atom/object maps, all three equation computational equivalences, operation/invariant/axis/coordinate maps, coefficient hom, and support/axis/observable composites. The extensionality spine reconstructs whole equality only as a derived conclusion. R_i(a,d) is equivalent to these conditions on d*a^-1. Identity satisfies them and the fixed comparator inverse fails them."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/DoctrineFiberProduct/QualifiedComparisonInputCharacterization.lean
    - research/lean/ResearchLean/AG/DoctrineFiberProduct.lean
  claim_mapping:
    theorem_names:
      - equationSystemExactTransport_heq_of_computational
      - GeometryTotalHomInputConditions
      - GeometryTotalHomInputConditions.of_eq
      - geomReadHom_heq_of_base_eq
      - GeometryTotalHomInputConditions.eq
      - generatedPulledEndpointHomAt
      - generatedPulledComparisonCompositeAt
      - GeneratedPulledKernelInputConditions
      - mem_generatedPulledComparisonKernel_iff_inputConditions
      - generatedQualifiedComparisonRelation_iff_inputConditions
      - UpperDecisionWitness.generatedPulledKernelInputConditions_one
      - UpperDecisionWitness.generatedPulledKernelInputConditions_comparator_inv_not
    source_labels:
      - "target theorem (B1), literal generated input-map characterization"
    conjuncts:
      - "pointed core -> pointedSourceMap and pointedAtomEquiv, reconstructed by ExtInstHom.ext / ExactDoctrineHom.ext"
      - "signed core -> atomEquiv, objectMap, equation computational fields, operationMap, invariantMap, axisMap, coordinateEquiv, reconstructed by SignedExactCoreReadingHom.ext"
      - "equation HEq -> equationSystemExactTransport_heq_of_computational from context/equation/observable equivalences"
      - "geometry -> coefficientHom and support/axis/observable composites, reconstructed by GeomReadHom.ext and GeometryTotalHom.ext"
      - "necessary and sufficient J_i condition -> mem_generatedPulledComparisonKernel_iff_inputConditions"
      - "same chain as the generated relation -> generatedQualifiedComparisonRelation_iff_inputConditions"
      - "positive and fixed negative instances -> generatedPulledKernelInputConditions_one and generatedPulledKernelInputConditions_comparator_inv_not"
    undischarged_assumptions:
      - "all B2/C/D material-premise rows"
    acceptance_point: "The Prop structure exposes only literal computational equalities and HEq fields; membership and whole GeometryTotalHom equality are derived in both directions."
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "B1 actual generated input-map characterization of J_i"
      - "B1 connection from R_i(a,d) through d*a^-1 to every literal input component"
      - "B1 input-condition nonvacuity through named positive and negative instances"
    remaining:
      - "B2 fixed comparison decisions"
      - "C transport/reflection/coherence"
      - "D coefficient observation and nonfactorization"
  certificate_provenance:
    discharged:
      - "the reverse iff derives equation/core/geometry equality through the existing extensionality declarations"
      - "the fixed negative input instance consumes UpperDecisionWitness.generatedQualifiedComparisonRelation_base_identity_not"
    unresolved:
      - "B2/C/D named decision and transport witnesses"
  proof_use:
    used:
      - "Cycle 3 difference-membership iff and fixed negative relation"
      - "ExactDoctrineHom.ext, SignedExactCoreReadingHom.ext, PackageTotalHom.ext, GeomReadHom.ext, and GeometryTotalHom.ext"
      - "all listed computational condition fields in the reverse reconstruction"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "cd research/lean && lake env lean ResearchLean/AG/DoctrineFiberProduct/QualifiedComparisonInputCharacterization.lean; exit 0"
    - "module terminal axiom audit: 31 namespace declarations, standard axioms only"
    - "PR #4373 implementation head 0cd556420d0fd761601c0aff43bb9c63e21e009e; CI 7/7 pass"
    - "four fresh independent implementation-head lanes: all No major findings"
    - "review audit: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4373#issuecomment-5549854766"
    - "final reviewed head 415de16198bc820598544c3a2c9e93fa6dcb78cb; CI 7/7 pass; four fresh final lanes all No major findings"
    - "final review audit: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4373#issuecomment-5549885211"
    - "acceptance regression: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4373#issuecomment-5549886301"
    - "merged by PR #4373 at 396efffb6f3a6cc31751e0263059cfcc255dd471"
  blocking_findings: []
  next_obligation: "B2: decide IsIso, both endpoint stabilizers, both projection surjectivities, and the fixed evaluation-pair fiber cardinality"
```

## Cycle 5 — B2 fixed comparison decisions

```yaml
ledger_type: target_cycle_result
goal: G-118-aat-diagnostic-descent-transport
cycle: 5
goal_blob_sha: 641f3255062d2578ef070cbb77c019cc28c3febf
base_oid: 396efffb6f3a6cc31751e0263059cfcc255dd471
tracking_issue: 4367
report_path: research/reports/G-118-aat-diagnostic-descent-transport.md
selection:
  proof_state_ref: "Issue #4367 Cycle 5 evidence comparison: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/4367#issuecomment-5549920902"
  proof_dag_predecessors:
    - "generatedRouteCoreMateIso and the actual upper geometry mate triangle"
    - "strong Cartesianity of both generated refinement geometry route legs"
    - "exactGeometryHomOfRefinement_isIso and faithful exact embedding"
    - "Cycle 2 isomorphic-comparison graph, stabilizer, and projection API"
    - "fixed generated comparator positive and base/identity negative pairs"
  proof_obligation: "B2: decide IsIso c_*, both endpoint stabilizers, both comparison projections, and the mandatory fixed-pair fiber consequence"
  selection_reason: "Evidence comparison selects the constructive positive IsIso branch; carrier injectivity alone and base/identity failure alone were explicitly rejected as insufficient inferences."
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - research/lean/ResearchLean/AG/DoctrineFiberProduct/QualifiedComparisonFixedDecision.lean
    - AAT.AG.DoctrineFiberProduct.UpperGeometryCleavage.upperGeometryMate_isIso
    - AAT.AG.DoctrineFiberProduct.UpperDecisionWitness.solution_component_isIso
    - AAT.AG.DoctrineFiberProduct.UpperDecisionWitness.solution_baseComparator_targetPartner_existsUnique
  risks:
    - "core IsIso must not be confused with complete geometry IsIso"
    - "full endpoint automorphism groups are not finite enumerations"
    - "failure of partner 1 does not imply absence of all partners"
  unchecked:
    - "all C/D obligations"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "The complete generated mate is structurally IsIso for every compatible input: its refinement image is strongly Cartesian by cancellation in the actual triangle, its base is the already constructed core iso, and its refinement inverse is reflected through exactification. At the fixed datum this yields c_* IsIso, both stabilizers equal bottom, both projections surjective, and Gamma as the conjugation graph. The named pair (b_*,p_*) is in Gamma, (b_*,1) is not, p_* is nonidentity, and both named partner fibers are singleton."
  completion_candidate: no
  decision_branches:
    isIso_c_star: positive
    target_stabilizer_trivial: positive
    source_stabilizer_trivial: positive
    source_projection_surjective: positive
    target_projection_surjective: positive
    fixed_target_partner_fiber: unique
  lean_artifacts:
    - research/lean/ResearchLean/AG/DoctrineFiberProduct/QualifiedComparisonFixedDecision.lean
    - research/lean/ResearchLean/AG/DoctrineFiberProduct.lean
  claim_mapping:
    theorem_names:
      - geometryTotalHom_isIso_of_refinement_isIso
      - upperGeometryMate_isIso
      - generatedCompatibleUpperGeometryMateAt_isIso
      - UpperDecisionWitness.solution_component_isIso
      - UpperDecisionWitness.solutionComponentIso
      - UpperDecisionWitness.solution_targetStabilizer_eq_bot
      - UpperDecisionWitness.solution_sourceStabilizer_eq_bot
      - UpperDecisionWitness.solutionQualifiedComparisonGraphMulEquiv
      - UpperDecisionWitness.solution_sourceProjection_surjective
      - UpperDecisionWitness.solution_targetProjection_surjective
      - UpperDecisionWitness.solution_comparator_pair_mem
      - UpperDecisionWitness.solution_base_identity_pair_not_mem
      - UpperDecisionWitness.generated_pulled_comparator_ne_one
      - UpperDecisionWitness.solution_baseComparator_targetPartner_existsUnique
      - UpperDecisionWitness.solution_pulledComparator_sourcePartner_existsUnique
    source_labels:
      - "target theorem (B2), fixed comparison decision"
    conjuncts:
      - "full c_* IsIso -> solution_component_isIso, via the general upperGeometryMate_isIso"
      - "K_Y(c_*)={1} and K_X(c_*)={1} -> solution_targetStabilizer_eq_bot and solution_sourceStabilizer_eq_bot"
      - "Gamma is the conjugation graph -> solutionQualifiedComparisonGraphMulEquiv"
      - "both projections are surjective -> solution_sourceProjection_surjective and solution_targetProjection_surjective"
      - "mandatory positive and negative pairs -> solution_comparator_pair_mem and solution_base_identity_pair_not_mem"
      - "the fixed nonempty fiber is unique -> both existsUnique partner theorems"
      - "the named pulled partner is nonidentity -> generated_pulled_comparator_ne_one"
    undischarged_assumptions:
      - "all C/D material-premise rows"
    acceptance_point: "The positive decisions are derived from a complete-geometry inverse route; neither finite enumeration nor carrier injection is used as an IsIso certificate."
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "B2 complete fixed comparison IsIso decision"
      - "B2 both endpoint stabilizer decisions"
      - "B2 both projection surjectivity decisions and graph connection"
      - "B2 fixed evaluation pair membership, identity-partner failure, and unique fiber"
    remaining:
      - "C transport/reflection/coherence"
      - "D coefficient observation and nonfactorization"
  certificate_provenance:
    discharged:
      - "IsIso consumes actual mate triangle, both route Cartesian theorems, core mate Iso, and exactification inverse"
      - "fixed positive/negative pair consumes the actual solution comparator equation and reviewed support-incoherence route"
    unresolved:
      - "C/D transport and observation witnesses"
  proof_use:
    used:
      - "upperGeometryMate_fac and both route strong-Cartesian declarations in the refinement mate cancellation"
      - "generatedRouteCoreMateIso in the base IsIso"
      - "exactGeometryHomOfRefinement_isIso and exactGeometryHomOfRefinement_toRefinement in complete reflection"
      - "Cycle 2 isomorphic graph, projection-surjectivity, and stabilizer-bottom declarations"
      - "the route-integrity gate upperDecisionSolution_comparatorDescentAt and generated relation negative theorem"
      - "both fixed stabilizer-bottom decisions and the Cycle 2 transitive fiber actions in the two partner uniqueness proofs"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "targeted direct dependency build only: lake build ResearchLean.AG.DoctrineFiberProduct.QualifiedComparisonInputCharacterization; no Research aggregate/full build"
    - "cd research/lean && lake env lean ResearchLean/AG/DoctrineFiberProduct/QualifiedComparisonFixedDecision.lean; exit 0"
    - "module terminal axiom audit: 15 namespace declarations, standard axioms only"
    - "revised implementation head 48776fbdfc13d93b44afde0c06d888c4545eb0c4: GitHub CI 7/7 pass"
    - "four fresh independent revised-head lanes (MATH, LEAN, PREMISE, ROUTE): all No major findings"
    - "revised fixed-head audit: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4374#issuecomment-5550022475"
  blocking_findings: []
  next_obligation: "C1: transport Gamma, both stabilizers, fibers, projections, and coefficient identities across the two fixed complete endpoint presentation isomorphisms"
```

## Cycle 6 — C1 complete-geometry presentation transport

```yaml
ledger_type: target_cycle_result
goal: G-118-aat-diagnostic-descent-transport
cycle: 6
goal_blob_sha: 641f3255062d2578ef070cbb77c019cc28c3febf
base_oid: 4e6d1cf8590cb4e1691f0262c7b9a7267256c529
tracking_issue: 4367
report_path: research/reports/G-118-aat-diagnostic-descent-transport.md
selection:
  proof_state_ref: "Issue #4367 Cycle 6 evidence comparison: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/4367#issuecomment-5550063833"
  proof_dag_predecessors:
    - "canonicalAuthoredBaseToGeneratedRouteExactGeometryIsoAt and canonicalAuthoredPulledToGeneratedRouteExactGeometryIsoAt"
    - "canonicalGeneratedUpperRefinementBCSolutionEquiv_companion"
    - "canonicalSolutionForwardAt_exact_normalization and generatedSolutionBackwardAt_exact_normalization"
    - "CompositeFiberAut.conjugationMulEquiv"
    - "qualifiedComparison subgroup, stabilizer, projection-kernel, and lift-action API"
  proof_obligation: "C1: transport the full qualified comparison classification across the two selected complete endpoint presentations, including Gamma, both projections and kernels, both stabilizers, nonempty lift fibers and their actions, and coefficient observations"
  selection_reason: "The selected route proves the actual comparison equality first and then transports the existing full groups. Graph-of-an-iso alone and arbitrary decoded-presentation replacement were rejected because neither matches the fixed C1 route."
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - research/lean/ResearchLean/AG/DoctrineFiberProduct/QualifiedComparisonEndpointTransport.lean
    - AAT.AG.DoctrineFiberProduct.UpperGeometryCompatibleProblemInputData.generatedCompatibleUpperGeometryMateAt_eq_endpoint_conjugation
    - AAT.AG.DoctrineFiberProduct.UpperGeometryCompatibleProblemInputData.canonicalGeneratedQualifiedComparisonMulEquivAt
    - AAT.AG.DoctrineFiberProduct.qualifiedComparisonEndpointConjugation_targetLift_smul
  risks:
    - "the categorical composition order must state v_i o c_can o u_i^-1, represented in Lean as u_i.inv then c_can then v_i.hom"
    - "transport must range over full CompositeFiberAut groups and actual comparison subgroups, not finite witnesses"
    - "presentation replacement must remain restricted to the two selected complete upper presentation changes"
  unchecked:
    - "C2/C3/D and final closure obligations"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "For every compatible input and vertex, the actual generated comparison is exactly the canonical companion comparison conjugated by the selected base and pulled complete endpoint isomorphisms, with the reverse equality supplied by the independent backward exactification. Simultaneous endpoint conjugation gives a multiplicative equivalence of Gamma, commutes with both projections, restricts to both stabilizers, transports both projection kernels, and gives equivariant equivalences of every source and target lift fiber; hence nonemptiness is preserved and reflected. All four endpoint hom/inverse coefficient identities are consumed to show coefficient observations are unchanged in both directions."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/DoctrineFiberProduct/QualifiedComparisonEndpointTransport.lean
    - research/lean/ResearchLean/AG/DoctrineFiberProduct.lean
  claim_mapping:
    theorem_names:
      - generatedCompatibleUpperGeometryMateAt_eq_endpoint_conjugation
      - canonicalCompanionUpperGeometryMateAt_eq_endpoint_conjugation
      - qualifiedComparisonEndpointConjugationMulEquiv
      - qualifiedComparisonEndpointConjugation_sourceProjection
      - qualifiedComparisonEndpointConjugation_targetProjection
      - qualifiedComparisonEndpointConjugationTargetStabilizerMulEquiv
      - qualifiedComparisonEndpointConjugationSourceStabilizerMulEquiv
      - qualifiedComparisonEndpointConjugationSourceKernelMulEquiv
      - qualifiedComparisonEndpointConjugationTargetKernelMulEquiv
      - qualifiedComparisonEndpointConjugationTargetLiftEquiv
      - qualifiedComparisonEndpointConjugationSourceLiftEquiv
      - qualifiedComparisonEndpointConjugation_targetLift_smul
      - qualifiedComparisonEndpointConjugation_sourceLift_smul
      - canonicalGeneratedQualifiedComparisonMulEquivAt
      - canonicalGeneratedTargetStabilizerMulEquivAt
      - canonicalGeneratedSourceStabilizerMulEquivAt
      - canonicalGeneratedSourceProjectionKernelMulEquivAt
      - canonicalGeneratedTargetProjectionKernelMulEquivAt
      - canonicalGeneratedQualifiedComparisonTargetLiftEquivAt
      - canonicalGeneratedQualifiedComparisonSourceLiftEquivAt
      - canonicalGeneratedQualifiedComparisonTargetLift_nonempty_iff
      - canonicalGeneratedQualifiedComparisonSourceLift_nonempty_iff
      - canonicalAuthoredBaseConjugation_coefficientHom
      - canonicalAuthoredBaseConjugation_symm_coefficientHom
      - canonicalAuthoredPulledConjugation_coefficientHom
      - canonicalAuthoredPulledConjugation_symm_coefficientHom
    source_labels:
      - "target theorem (C1), selected complete-presentation transport"
    conjuncts:
      - "actual exact comparison equality and its reverse"
      - "Gamma multiplicative equivalence and both projection squares"
      - "both stabilizer and both projection-kernel equivalences"
      - "both lift-fiber equivalences, nonempty iff, and action equivariance"
      - "base/pulled coefficient-observation preservation forward and backward"
    undischarged_assumptions:
      - "C2/C3/D and final identity/inverse/composition closure"
    acceptance_point: "The actual comparison equality is proof-used before subtype transport, and the specialized declarations quantify only over the fixed canonical-authored/generated complete endpoints."
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "C1 actual complete comparison conjugation equality in both directions"
      - "C1 Gamma, projections, stabilizers, kernels, lift fibers, and action transport"
      - "C1 coefficient identity in both presentation directions"
    remaining:
      - "C2 actual edge reselection"
      - "C3 generated base-transport preservation via T_i and reflection from J_i = {1}"
      - "D observation and nonfactorization"
      - "identity/inverse/finite-composition closure and completion audit"
  certificate_provenance:
    discharged:
      - "comparison equality comes from the theorem-generated companion equivalence and both independent exact normalizations"
      - "group and fiber transport comes from the selected exact endpoint isomorphisms and existing full CompositeFiberAut conjugation"
    unresolved:
      - "C2/C3/D witnesses and final closure"
  proof_use:
    used:
      - "canonicalGeneratedUpperRefinementBCSolutionEquiv_companion and canonicalSolutionForwardAt_exact_normalization in the forward exact equality"
      - "generatedSolutionBackwardAt_exact_normalization in the reverse exact equality"
      - "conjugationMulEquiv hom, inverse, multiplication, and injectivity laws in Gamma, kernel, stabilizer, and lift transport"
      - "existing qualified comparison projections, stabilizers, kernels, and lift-action definitions"
      - "all four canonical-authored base/pulled exact hom/inverse coefficient-id declarations"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "cd research/lean && lake env lean ResearchLean/AG/DoctrineFiberProduct/QualifiedComparisonEndpointTransport.lean; exit 0"
    - "module terminal axiom audit: 27 declarations, standard axioms only"
    - "revised implementation/report head 3bf0f9a0c9dc69f4cc0b64d15bdd504094ce9a6a: GitHub CI 7/7 pass"
    - "four fresh independent revised-head lanes (MATH, LEAN, PREMISE, ROUTE): all No major findings"
    - "revised fixed-head audit: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4375#issuecomment-5550231048"
  blocking_findings: []
  next_obligation: "C2: classify actual coefficient-trivial edge reselection pairs and the product stabilizer action on partner families"
```

## Cycle 7 — C2 actual coefficient-trivial edge reselection

```yaml
ledger_type: target_cycle_result
goal: G-118-aat-diagnostic-descent-transport
cycle: 7
goal_blob_sha: 641f3255062d2578ef070cbb77c019cc28c3febf
base_oid: 61bee41de6b6d772df786d56f56baf36ad7e26d0
tracking_issue: 4367
report_path: research/reports/G-118-aat-diagnostic-descent-transport.md
selection:
  proof_state_ref: "Issue #4367 Cycle 7 evidence comparison: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/4367#issuecomment-5550469098"
  proof_dag_predecessors:
    - "CoefficientTrivialUpperReselectionEndpointIntertwining and its edge/path/full-pair/raw-cochain consumers"
    - "qualifiedComparisonTargetLiftAction with free and transitive laws"
    - "generatedCompatibleUpperGeometryMateAt_isIso and qualifiedComparisonIsoGraphMulEquiv"
    - "generatedQualifiedComparisonRelation_diagonal and the H_B/H_P Cartesian factorizations"
    - "C1 canonical-authored/generated reselection transport"
  proof_obligation: "C2: classify all actual coefficient-trivial edge pairs, construct the nonempty product-stabilizer torsor for fixed base families, connect source H_B/H_P generation to downstream consumers, and preserve the mandatory fixed positive/negative decisions through inverse presentation"
  selection_reason: "The existing endpoint predicate is definitionally the all-edge Gamma product. The selected action uses the literal target stabilizer intersected with the kernel of the newly bundled coefficient observation, while source qualification comes from the B1 diagonal theorem rather than a supplied pairing certificate."
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - research/lean/ResearchLean/AG/DoctrineFiberProduct/QualifiedCoefficientObservation.lean
    - research/lean/ResearchLean/AG/DoctrineFiberProduct/QualifiedComparisonEdgeReselection.lean
    - research/lean/ResearchLean/AG/DoctrineFiberProduct/QualifiedComparisonEdgeReselectionConsequences.lean
  risks:
    - "the stabilizer product must retain ker kappa and the coefficient-trivial reselection fields"
    - "edge comparison is at the target vertex j"
    - "source-to-paired existence must remain separate from arbitrary paired preservation"
    - "the fixed negative pair must survive the inverse canonical-authored presentation"
  unchecked:
    - "C3, the remainder of D beyond coefficientObservation, and final closure"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "For arbitrary compatible input and arbitrary coefficient-trivial generated base/pulled edge families, endpoint intertwining is exactly pointwise membership in Gamma_(c_j). For each fixed base family the partner family is nonempty and carries a free and transitive action of the dependent edge product of K_(P_j)(c_j) intersect ker kappa_(P_j). A coefficient-trivial source family is mapped through H_B/H_P to a qualified generated pair and hence to the existing path, path-leg, authored-comparator, full-pair, and raw-cochain routes. At DecisionEdge.twist the generated comparator pair is positive, the pulled-identity pair is negative, the base is nonidentity, and inverse canonical-authored transport retains the positive pair, nonidentity, and negative identity decision."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/DoctrineFiberProduct/QualifiedCoefficientObservation.lean
    - research/lean/ResearchLean/AG/DoctrineFiberProduct/QualifiedComparisonEdgeReselection.lean
    - research/lean/ResearchLean/AG/DoctrineFiberProduct/QualifiedComparisonEdgeReselectionConsequences.lean
    - research/lean/ResearchLean/AG/DoctrineFiberProduct.lean
  claim_mapping:
    theorem_names:
      - CompositeFiberAut.coefficientObservation
      - CompositeFiberAut.mem_coefficientObservation_ker_iff
      - qualifiedComparisonCoefficientTrivialTargetStabilizer
      - coefficientTrivialUpperReselectionEndpointIntertwining_iff_forall_mem
      - GeneratedCoefficientTrivialTargetStabilizerFamily
      - GeneratedCoefficientTrivialPulledPartner
      - generatedCoefficientTrivialPulledPartnerAction
      - generatedCoefficientTrivialPulledPartnerAction_free
      - generatedCoefficientTrivialPulledPartnerAction_transitive
      - generatedCoefficientTrivialPulledPartner_existsUnique
      - generatedCoefficientTrivialPulledPartnerOrigin
      - generatedCoefficientTrivialPulledPartner_nonempty
      - generatedBaseCompositeFiberAutAt_coefficient_id
      - generatedPulledCompositeFiberAutAt_coefficient_id
      - generatedBaseOfSourceCoefficientTrivialUpperEdgeReselection
      - generatedPulledOfSourceCoefficientTrivialUpperEdgeReselection
      - sourceCoefficientTrivialUpperEdgeReselection_generated_mem
      - sourceCoefficientTrivialUpperEdgeReselection_generated_endpointIntertwining
      - sourceCoefficientTrivialUpperEdgeReselection_generatedPath_legTriangle
      - sourceCoefficientTrivialUpperEdgeReselection_generatedAuthoredComparator_pasting
      - sourceCoefficientTrivialUpperEdgeReselection_generatedPaired
      - sourceCoefficientTrivialUpperEdgeReselection_generatedRawCochain_intertwining
      - UpperDecisionWitness.generatedComparatorUpperReselections_twist_mem_qualifiedComparison
      - UpperDecisionWitness.generatedBaseComparatorPulledIdentity_twist_not_mem_qualifiedComparison
      - UpperDecisionWitness.canonicalCompanionBaseComparatorCoefficientTrivialUpperReselection_forward
      - UpperDecisionWitness.canonicalCompanionUpperRefinementBCSolution_forward
      - UpperDecisionWitness.generatedBaseComparatorCoefficientTrivialUpperReselection_ne_one
      - UpperDecisionWitness.canonicalCompanionComparatorUpperReselections_paired_fires
      - UpperDecisionWitness.canonicalCompanionBaseComparatorCoefficientTrivialUpperReselection_ne_one
      - UpperDecisionWitness.canonicalCompanionBaseComparatorPulledIdentity_not_endpointIntertwining
    source_labels:
      - "target theorem (C2), actual coefficient-trivial edge reselection"
    conjuncts:
      - "all-edge Gamma decision iff existing endpoint intertwining"
      - "literal product of K target stabilizer intersect coefficient kernel acts freely and transitively on the nonempty fixed-base partner family"
      - "source coefficient-trivial family is qualified through H_B/H_P and connected to existing downstream APIs"
      - "fixed twist positive and pulled-identity negative decisions, including inverse-presentation tracking"
    undischarged_assumptions:
      - "C3, D nonfactorization/transport, and final closure"
    acceptance_point: "The action and existence theorems quantify over arbitrary edge families on the fixed generated routes; the finite twist datum is used only for mandatory nonvacuity and negative separation."
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "C2 arbitrary paired-family all-edge qualification"
      - "C2 nonempty fixed-base partner-family torsor with coefficient kernel retained"
      - "C2 source H_B/H_P qualification and downstream connection"
      - "C2 fixed generated and inverse-presentation positive/negative decisions"
    remaining:
      - "C3 preservation/reflection and fixed J decision"
      - "D coefficient nonfactorization and C1/C2/C3 transport"
      - "identity/inverse/finite-composition closure and completion audit"
  certificate_provenance:
    discharged:
      - "partner existence comes from the complete generated comparison IsIso and its qualified graph"
      - "coefficient triviality comes from the Gamma equation plus base/comparison coefficient identities"
      - "source qualification comes from generatedQualifiedComparisonRelation_diagonal; H_B/H_P coefficient preservation comes from Cartesian factorization and route-leg coefficient identities"
      - "fixed inverse negative decision is reflected forward to the existing generated negative theorem"
    unresolved:
      - "C3 and D witnesses and final closure"
  proof_use:
    used:
      - "qualifiedComparisonTargetLiftAction and its free/transitive laws in the product action"
      - "generatedCompatibleUpperGeometryMateAt_isIso and qualifiedComparisonIsoGraphMulEquiv in arbitrary-partner existence"
      - "generatedBaseCompositeFiberAutAt_fac, generatedPulledCompositeFiberAutAt_fac, and both route-leg coefficient identities"
      - "generatedQualifiedComparisonRelation_diagonal in source-to-paired generation"
      - "existing endpoint edge/path, path-leg, authored-comparator, toPaired, and raw-cochain routes"
      - "generatedComparatorUpperReselections_endpointIntertwining_fires, generatedBaseComparatorPulledIdentity_not_endpointIntertwining, and generatedBaseComparatorCoefficientTrivialUpperReselection_ne_one"
      - "canonicalCompanionComparatorUpperReselections_paired_fires, canonicalCompanionBaseComparatorCoefficientTrivialUpperReselection_ne_one, and canonical-authored forward/backward reselection transport"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "targeted direct dependency builds only; no Research aggregate/full build"
    - "cd research/lean && lake env lean ResearchLean/AG/DoctrineFiberProduct/QualifiedCoefficientObservation.lean; exit 0; 5 declarations standard-only"
    - "cd research/lean && lake env lean ResearchLean/AG/DoctrineFiberProduct/QualifiedComparisonEdgeReselection.lean; exit 0; 20 declarations standard-only"
    - "cd research/lean && lake env lean ResearchLean/AG/DoctrineFiberProduct/QualifiedComparisonEdgeReselectionConsequences.lean; exit 0; 9 declarations standard-only"
  blocking_findings: []
  next_obligation: "C3: prove generated base-transport preservation and exact reflection criterion, then decide J_*"
```

## Cycle 8 — C3 generated base transport and reflection

```yaml
ledger_type: target_cycle_result
goal: G-118-aat-diagnostic-descent-transport
cycle: 8
goal_blob_sha: 641f3255062d2578ef070cbb77c019cc28c3febf
base_oid: 3bd575eca0d2539c80364e758cb322b362a9d7c1
tracking_issue: 4367
report_path: research/reports/G-118-aat-diagnostic-descent-transport.md
selection:
  proof_state_ref: "Issue #4367 Cycle 8 evidence comparison: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/4367#issuecomment-5550672875"
  proof_dag_predecessors:
    - "generatedBaseCompositeFiberAutHomAt and generatedPulledCompositeFiberAutHomAt"
    - "generatedQualifiedComparisonRelation_diagonal and generatedQualifiedComparisonRelation_iff_difference_mem"
    - "generatedPulledRouteUpperEquivalenceAt and generatedPulledRouteRealizationExactAt"
    - "mem_generatedPulledComparisonKernel_iff_inputConditions"
    - "solution_targetStabilizer_eq_bot"
  proof_obligation: "C3: define T_i=(H_B,H_P), prove Gamma_(identity) preservation, characterize reflection exactly by J_i=bottom, and decide J_* from the actual input maps"
  selection_reason: "The positive branch is determined without a supplied faithfulness premise: the actual pulled Cartesian factor map is injective because its exact upper map and all three realization total-carrier maps are equivalences. The fixed comparison is an isomorphism, hence its target stabilizer is bottom and J_* is the kernel of an injective H_P."
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - research/lean/ResearchLean/AG/DoctrineFiberProduct/QualifiedComparisonBaseTransport.lean
  risks:
    - "reflection must be equivalent to J_i=bottom rather than assumed from faithfulness"
    - "the source predicate must be the literal qualified group of the identity comparison"
    - "injectivity must reflect upper and geometry carrier maps, not only the package core"
    - "the fixed positive decision must connect to the B1 computational input conditions"
  unchecked:
    - "D, C1/C2/C3 closure, and final completion review"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "For every compatible input and vertex, the actual product homomorphism T_i sends the identity-comparison qualified subgroup into Gamma_(c_i). Reflection of this map is equivalent to J_i=bottom. The generated pulled endpoint homomorphism is injective, proved from its Cartesian factorization, the exact upper equivalence, and the realization-exact Support/Axis/Observable equivalences. At the fixed datum the target stabilizer is bottom, so J_*=bottom; consequently R_*(a,d) iff a=d for all source automorphisms, and the literal B1 input conditions hold exactly for the identity residual."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/DoctrineFiberProduct/QualifiedComparisonBaseTransport.lean
    - research/lean/ResearchLean/AG/DoctrineFiberProduct.lean
  claim_mapping:
    theorem_names:
      - mem_qualifiedComparisonSubgroup_identity_iff
      - ExactUpperEquivalence.forward_comp_injective
      - UpperGeometryCompatibleProblemInputData.generatedPulledRoute_supportSigmaMap_eq
      - UpperGeometryCompatibleProblemInputData.generatedPulledRoute_axisSigmaMap_eq
      - UpperGeometryCompatibleProblemInputData.generatedPulledRoute_observableSigmaMap_eq
      - UpperGeometryCompatibleProblemInputData.generatedPulledCompositeFiberAutHomAt_injective
      - UpperGeometryCompatibleProblemInputData.generatedComparisonPairHomAt
      - UpperGeometryCompatibleProblemInputData.generatedComparisonPairHomAt_preserves_qualifiedComparison
      - UpperGeometryCompatibleProblemInputData.generatedQualifiedComparisonRelation_reflects_iff_kernel_eq_bot
      - UpperGeometryCompatibleProblemInputData.generatedComparisonPairHomAt_reflects_qualifiedComparison_iff
      - UpperDecisionWitness.generatedPulledComparisonKernel_eq_bot
      - UpperDecisionWitness.generatedQualifiedComparisonRelation_iff_eq
      - UpperDecisionWitness.solution_generatedComparisonPairHom_mem_iff_source_identity_mem
      - UpperDecisionWitness.generatedPulledKernelInputConditions_iff_eq_one
    source_labels:
      - "target theorem (C3), generated base-transport preservation and reflection"
    conjuncts:
      - "T_i is the actual product of H_B and H_P"
      - "Gamma_(identity source) is the diagonal and is preserved by T_i"
      - "reflection iff J_i=bottom for every input and vertex"
      - "actual H_P injectivity and fixed positive decision J_*=bottom"
      - "fixed all-pair reflection and computational input-condition decision"
    undischarged_assumptions:
      - "D, C1/C2/C3 closure, and final completion review"
    acceptance_point: "No injectivity, faithfulness, reflection, or trivial-kernel certificate is accepted from the caller; H_P injectivity is constructed from the generated route equivalences and used to decide the fixed branch."
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "C3 preservation under T_i"
      - "C3 exact reflection criterion J_i=bottom"
      - "actual H_P injectivity"
      - "fixed J_*=bottom and all-pair positive reflection branch"
    remaining:
      - "D coefficient nonfactorization and transport"
      - "C1/C2/C3 identity, inverse, and finite-composition closure"
      - "final completion review"
  certificate_provenance:
    discharged:
      - "preservation is generated by the B1 diagonal theorem"
      - "reflection is derived from the B1 residual-difference iff"
      - "H_P injectivity uses the actual Cartesian factorization, exact upper inverse, and realization-exact total-carrier equivalences"
      - "J_* uses the reviewed fixed target-stabilizer decision and the constructed H_P injectivity"
    unresolved:
      - "D and closure witnesses"
  proof_use:
    used:
      - "generatedQualifiedComparisonRelation_diagonal"
      - "generatedQualifiedComparisonRelation_iff_difference_mem"
      - "generatedPulledCompositeFiberAutAt_fac"
      - "generatedPulledRouteUpperEquivalenceAt_forward_eq and backward_forward"
      - "generatedPulledRouteRealizationExactAt supportSigmaEquiv, axisSigmaEquiv, and observableSigmaEquiv"
      - "solution_targetStabilizer_eq_bot"
      - "mem_generatedPulledComparisonKernel_iff_inputConditions"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "targeted direct dependency builds only; no Research aggregate/full build"
    - "cd research/lean && lake env lean ResearchLean/AG/DoctrineFiberProduct/QualifiedComparisonBaseTransport.lean; exit 0; 25 declarations standard-only"
  blocking_findings: []
  next_obligation: "D: prove fixed coefficient-observation nonfactorization and transport it through C1/C2/C3"
```
