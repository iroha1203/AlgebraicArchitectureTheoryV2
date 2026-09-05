# G-118 — Qualified Comparison Transport and Diagnostic Information Loss

一次仕様は
[`research/goals/G-118-aat-diagnostic-descent-transport.md`](../goals/G-118-aat-diagnostic-descent-transport.md)
である。本 report は固定 target A–D の proof obligation、Lean 宣言、入力 provenance、
proof-use、査読結果を cycle ごとに記録する。

## Proof state

- fixed base: `42cec580bbe8b748360abaa17145cb4af3be0be0`
- tracking Issue: #4367
- completed obligations: F0 typing、A comparison stabilizer API、B1 generated-image / actual input-map classification
- current obligation: B2 fixed comparison decisions
- pending obligations: B2、C1、C2、C3、D、completion audit
- current target state: Cycle 4 acceptance 後の `target-proof-checkpoint`
- next obligation: B2 fixed comparison decisions

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
  blocking_findings: []
  next_obligation: "B2: decide IsIso, both endpoint stabilizers, both projection surjectivities, and the fixed evaluation-pair fiber cardinality"
```
