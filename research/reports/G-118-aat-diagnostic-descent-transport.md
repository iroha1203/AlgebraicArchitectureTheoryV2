# G-118 — Source-Presentation-Natural Qualified Comparison Transport and Diagnostic Information Loss

一次仕様は
[`research/goals/G-118-aat-diagnostic-descent-transport.md`](../goals/G-118-aat-diagnostic-descent-transport.md)
である。本 report は固定 target A–D の proof obligation、Lean 宣言、入力 provenance、
proof-use、査読結果を cycle ごとに記録する。

## Proof state

- revision 1 fixed base: `42cec580bbe8b748360abaa17145cb4af3be0be0`
- revision 2 source base: `4f8ba8f8396ce3bbdd00c581941acee73967096b`
- revision 2 review: PR #4383 の fixed-head 数学/Lean 査読を通過し、merge `7d4080a28fbb7d0e20189709c2fbcc59f74809c3` で固定した。
- tracking Issue: #4367
- reusable revision 1 artifacts: F0 typing、A comparison stabilizer API、B1 generated-image / actual input-map classification、B2 fixed comparison decisions、C1t complete-geometry endpoint transport and typed finite-chain closure、C2 actual edge reselection pointwise-product and finite-path closure、C3 generated base-transport preservation/reflection and target-side C1t postcomposition、D fixed coefficient nonfactorization and all-C1t-chain transport
- current obligation: C1s generated endpoint factorization / coefficient laws と comparison-component naturality
- pending obligations: revision 1 artifact の statement/proof-use 再監査、C1s input reconstruction、C3 source-presentation naturality、Γ/J/生成像/係数 correspondence、C1s/C1t/C2/D connection、fixed induced-action firing、final completion review
- current target state: revision 2 の `target-proof-checkpoint`
- revision rule: revision 1 の cycle result を自動継承しない。各宣言を revision 2 の固定 statement と material premise ledger に再照合する。
- next obligation: independently generated `η_B/η_P` の factorization・coefficient identity を固定し、比較成分可換式へ接続する

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

## Cycle 13 — revision 2 F0s result

```yaml
ledger_type: target_cycle_result
goal: G-118-aat-diagnostic-descent-transport
cycle: 13
goal_blob_sha: 6eff0d6913d91ac4e8965f2b9459dbf69ca0739a
base_oid: 7d4080a28fbb7d0e20189709c2fbcc59f74809c3
tracking_issue: 4367
report_path: research/reports/G-118-aat-diagnostic-descent-transport.md
result:
  classification: proof-obligation-discharged
  progress_class: progress
  terminal_status: target-proof-checkpoint
  theorem_map:
    - UpperGeometryCompatibleSourcePresentationChange
    - UpperGeometryCompatibleSourcePresentationChange.changedSourceFiberDiagram
    - UpperGeometryCompatibleSourcePresentationChange.sourceFiberDiagramIso
    - UpperGeometryCompatibleSourcePresentationChange.changedEdgeLift
    - UpperGeometryCompatibleSourcePresentationChange.changedPathLift_base
    - UpperGeometryCompatibleSourcePresentationChange.changedTwoCellBase
    - UpperGeometryCompatibleSourcePresentationChange.changedSourceTransport
    - UpperGeometryCompatibleSourcePresentationChange.changedInput
    - UpperGeometryCompatibleSourcePresentationChange.generatedBaseRouteExactCoreIsoAt_hom_fac
    - UpperGeometryCompatibleSourcePresentationChange.generatedBaseRouteRefinementGeometryIsoAt
    - UpperGeometryCompatibleSourcePresentationChange.generatedBaseRouteExactGeometryIsoAt
    - UpperGeometryCompatibleSourcePresentationChange.generatedPulledRouteExactCoreIsoAt_hom_fac
    - UpperGeometryCompatibleSourcePresentationChange.generatedPulledRouteRefinementGeometryIsoAt
    - UpperGeometryCompatibleSourcePresentationChange.generatedPulledRouteExactGeometryIsoAt
  source_labels:
    - "C1s source complete-geometry presentation change"
    - "C1s changed-input reconstruction"
    - "C1s generated eta_B/eta_P construction gate"
  acceptance_point: "The change datum stops at replacement source objects, selected core-fiber isomorphisms, exact complete-geometry isomorphisms, projection equations, and the two coefficient identities. The changed diagram, edges, comparator, both local qualifications, two-cell base law, coefficient laws, changed input, lower naturality maps, and both generated endpoint isomorphisms are derived definitions or theorems."
  port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "typed C1s change datum without changed-output certificates"
      - "certificate-free changed source diagram and complete transport"
      - "geometry/core strongly-cocartesian qualification after source conjugation"
      - "base and pulled generated exact endpoint isomorphism constructibility"
    remaining:
      - "exact endpoint factorization and coefficient laws"
      - "comparison-component and central T naturality"
      - "C1s identity, inverse, and finite-composition coherence"
      - "Gamma, projection, kernel, fiber, J, range, observation, fixed firing, and D transport"
  certificate_provenance:
    discharged:
      - "changed edges and comparator are literal conjugates reconstructed from input and geometryIso"
      - "two-cell base equality is derived from actual morphisms in the reconstructed fixed core fiber"
      - "generated lower comparisons use baseCompositeLegAt_naturality and pulledCompositeLegAt_naturality"
      - "generated geometry comparisons use IsStronglyCartesian.domainIsoOfBaseIso and exactGeometryHomOfRefinement"
    unresolved: []
  proof_use:
    used:
      - "sourceTransportGeometryEdge_isIso, itself derived from source strong-cocartesian qualifications"
      - "generatedBaseRouteLegAt_isStronglyCartesian and generatedPulledRouteLegAt_isStronglyCartesian"
      - "baseRouteComparisonCoreIso and pulledRouteComparisonCoreIso normalization factors"
      - "exactGeometryHomOfRefinement_toRefinement and faithful map_injective for both inverse laws"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  validation_refs:
    - "cd research/lean && lake env lean ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCompatibleSourcePresentationNaturalityF0.lean; exit 0; 54 declarations under AAT.AG.DoctrineFiberProduct standard axioms only"
    - "git diff --check; clean"
    - "literal scan for sorry/admit/axiom/unsafe; only #assert_standard_axioms_only matched"
    - "hidden/bidirectional Unicode scan; clean"
  blocking_findings: []
  next_obligation: "C1s generated endpoint factorization/coefficient laws and comparison-component naturality"
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
    - "reviewed head 4ed6181aecfd00983225bb45b90d0bd6754fa598: direct-response review resolved all bounded noncentral findings; GitHub CI 7/7 pass"
    - "fixed-head audit: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4376#issuecomment-5550584684"
    - "root acceptance: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4376#issuecomment-5550584800"
    - "merged by PR #4376 at 3bd575eca0d2539c80364e758cb322b362a9d7c1"
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
  proof_obligation_delta: "For every compatible input and vertex, the actual product homomorphism T_i sends the identity-comparison qualified subgroup into Gamma_(c_i). Reflection of this map is equivalent to J_i=bottom. The generated pulled endpoint homomorphism is injective: its Cartesian factorization reflects the exact upper map; composite-fiber qualification fixes the lower pointed map; coefficient-triviality reflects the coefficient map; and the realization-exact Support/Axis/Observable Sigma equivalences reflect all dependent carrier maps before GeometryTotalHom extensionality. At the fixed datum the target stabilizer is bottom, so J_*=bottom; consequently R_*(a,d) iff a=d for all source automorphisms, and the literal B1 input conditions hold exactly for the identity residual."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/DoctrineFiberProduct/QualifiedComparisonBaseTransport.lean
    - research/lean/ResearchLean/AG/DoctrineFiberProduct.lean
  claim_mapping:
    theorem_names:
      - mem_qualifiedComparisonSubgroup_identity_iff
      - ExactUpperEquivalence.forward_comp_injective
      - UpperGeometryCompatibleProblemInputData.refinementGeometrySupportSigmaMap
      - UpperGeometryCompatibleProblemInputData.refinementGeometrySupportSigmaMap_comp
      - UpperGeometryCompatibleProblemInputData.refinementGeometryAxisSigmaMap
      - UpperGeometryCompatibleProblemInputData.refinementGeometryAxisSigmaMap_comp
      - UpperGeometryCompatibleProblemInputData.refinementGeometryObservableSigmaMap
      - UpperGeometryCompatibleProblemInputData.refinementGeometryObservableSigmaMap_comp
      - UpperGeometryCompatibleProblemInputData.geometryTotalHom_supportComp_heq_of_sigmaMap_eq
      - UpperGeometryCompatibleProblemInputData.geometryTotalHom_axisComp_heq_of_sigmaMap_eq
      - UpperGeometryCompatibleProblemInputData.geometryTotalHom_observableComp_heq_of_sigmaMap_eq
      - UpperGeometryCompatibleProblemInputData.generatedPulledRoute_supportSigmaMap_eq
      - UpperGeometryCompatibleProblemInputData.generatedPulledRoute_axisSigmaMap_eq
      - UpperGeometryCompatibleProblemInputData.generatedPulledRoute_observableSigmaMap_eq
      - UpperGeometryCompatibleProblemInputData.generatedPulledGeometryComparatorCandidateAt_coefficientHom
      - UpperGeometryCompatibleProblemInputData.generatedPulledGeometryComparatorCandidateAt_supportSigmaMap
      - UpperGeometryCompatibleProblemInputData.generatedPulledGeometryComparatorCandidateAt_axisSigmaMap
      - UpperGeometryCompatibleProblemInputData.generatedPulledGeometryComparatorCandidateAt_observableSigmaMap
      - UpperGeometryCompatibleProblemInputData.generatedPulledCompositeFiberAutHomAt_injective
      - UpperGeometryCompatibleProblemInputData.generatedComparisonPairHomAt
      - UpperGeometryCompatibleProblemInputData.generatedComparisonPairHomAt_apply
      - UpperGeometryCompatibleProblemInputData.generatedComparisonPairHomAt_preserves_qualifiedComparison
      - UpperGeometryCompatibleProblemInputData.generatedQualifiedComparisonRelation_reflects_iff_kernel_eq_bot
      - UpperGeometryCompatibleProblemInputData.generatedComparisonPairHomAt_reflects_qualifiedComparison_iff
      - UpperGeometryCompatibleProblemInputData.generatedPulledComparisonKernel_eq_ker_of_targetStabilizer_eq_bot
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
      - "H_P injectivity uses the actual Cartesian factorization, exact upper inverse, composite-fiber lower-pointed identity, generated route coefficient identity, and realization-exact total-carrier equivalences; PackageTotalHom.ext, geomReadHom_heq_of_base_eq, GeometryTotalHom.ext, and Iso.ext reconstruct equality of the complete automorphisms"
      - "J_* uses the reviewed fixed target-stabilizer decision and the constructed H_P injectivity"
    unresolved:
      - "D and closure witnesses"
  proof_use:
    used:
      - "generatedQualifiedComparisonRelation_diagonal"
      - "generatedQualifiedComparisonRelation_iff_difference_mem"
      - "generatedPulledCompositeFiberAutAt_fac"
      - "generatedPulledRouteUpperEquivalenceAt_forward_eq and backward_forward"
      - "CompositeFiberAut.hom_base_base_eq and PackageTotalHom.ext for the lower pointed and upper package components"
      - "generatedPulledRouteLegAt_coefficient_id via generatedPulledGeometryComparatorCandidateAt_coefficientHom"
      - "generatedPulledRouteRealizationExactAt supportSigmaEquiv, axisSigmaEquiv, and observableSigmaEquiv"
      - "refinementGeometry Support/Axis/Observable Sigma-map composition and HEq bridge declarations, followed by geomReadHom_heq_of_base_eq, GeometryTotalHom.ext, and Iso.ext"
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
    - "cd research/lean && lake env lean ResearchLean/AG/DoctrineFiberProduct/QualifiedComparisonBaseTransport.lean; exit 0; 30 declarations standard-only"
    - "reviewed head c82d7527743e6372cd60b7db4a2e2fecb1583970: four fresh full-head lanes and one bounded direct-response review accepted; GitHub CI 7/7 pass"
    - "fixed-head audit: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4377#issuecomment-5550776351"
    - "root acceptance: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4377#issuecomment-5550776344"
    - "merged by PR #4377 at 17e644f0c2c986994d4120c533c42b62991f33eb"
  blocking_findings: []
  next_obligation: "D: prove fixed coefficient-observation nonfactorization and transport it through C1/C2/C3"
```

## Cycle 9 — D fixed coefficient nonfactorization

```yaml
ledger_type: target_cycle_result
goal: G-118-aat-diagnostic-descent-transport
cycle: 9
goal_blob_sha: 641f3255062d2578ef070cbb77c019cc28c3febf
base_oid: 17e644f0c2c986994d4120c533c42b62991f33eb
tracking_issue: 4367
report_path: research/reports/G-118-aat-diagnostic-descent-transport.md
selection:
  proof_state_ref: "Issue #4367 Cycle 9 evidence comparison: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/4367#issuecomment-5550784957"
  proof_dag_predecessors:
    - "CompositeFiberAut.coefficientObservation"
    - "generatedBaseComparatorCoefficientTrivialUpperReselection and generatedPulledComparatorCoefficientTrivialUpperReselection"
    - "generatedComparatorUpperReselections_twist_mem_qualifiedComparison"
    - "generatedBaseComparatorPulledIdentity_twist_not_mem_qualifiedComparison"
  proof_obligation: "D fixed datum: define literal Q_*, O_*, and D_*; prove an observation-colliding positive/negative pair and nonfactorization of D_* through O_*"
  selection_reason: "The reviewed C2 pair is already the literal fixed generated pair required by D. Its positive and pulled-identity negative values have equal product coefficient observations, while C2 proves opposite membership decisions."
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - research/lean/ResearchLean/AG/DoctrineFiberProduct/QualifiedComparisonCoefficientNonfactorization.lean
  risks:
    - "D_* must be literal qualifiedComparisonSubgroup membership rather than a proxy boolean"
    - "the observations must be equal as the full product coefficient automorphisms"
    - "the nonfactorization theorem must quantify over every predicate on the observation space"
  unchecked:
    - "D transport through C1/C2/C3"
    - "C1/C2/C3 identity, inverse, and finite-composition closure"
    - "final completion review"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "At the fixed B2 datum, Q_* is the literal product of the generated base and pulled complete automorphism groups, O_* is the product of their coefficient observations, and D_* is literal Gamma_(c_*) membership. The generated comparator pair and its pulled-identity companion have equal O_* values, but D_* accepts the first and rejects the second. Therefore no predicate on the coefficient-observation space factors D_* for all pairs."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/DoctrineFiberProduct/QualifiedComparisonCoefficientNonfactorization.lean
    - research/lean/ResearchLean/AG/DoctrineFiberProduct.lean
  claim_mapping:
    theorem_names:
      - UpperDecisionWitness.FixedQualifiedPair
      - UpperDecisionWitness.FixedCoefficientObservationSpace
      - UpperDecisionWitness.fixedCoefficientObservation
      - UpperDecisionWitness.FixedQualifiedDecision
      - UpperDecisionWitness.fixedPositiveQualifiedPair
      - UpperDecisionWitness.fixedNegativeQualifiedPair
      - UpperDecisionWitness.fixedPositivePulled_coefficientObservation_eq_one
      - UpperDecisionWitness.fixedNegativePulled_coefficientObservation_eq_one
      - UpperDecisionWitness.fixedCoefficientObservation_positive_eq_negative
      - UpperDecisionWitness.fixedPositiveQualifiedDecision
      - UpperDecisionWitness.fixedNegativeNotQualifiedDecision
      - UpperDecisionWitness.fixedQualifiedDecision_not_factor_through_coefficientObservation
    source_labels:
      - "target theorem (D), fixed coefficient-invisible comparison information"
    conjuncts:
      - "literal Q_*, product coefficient observation O_*, and literal Gamma decision D_*"
      - "positive/negative observation collision"
      - "positive Gamma membership and negative nonmembership"
      - "universal predicate nonfactorization"
    undischarged_assumptions:
      - "D transport, closure, and final completion review"
    acceptance_point: "The diagnostic is quantified as an arbitrary predicate on the complete product coefficient-observation space; no restriction on the candidate diagnostic encodes the contradiction."
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "D fixed observation equality"
      - "D fixed positive/negative qualified-decision separation"
      - "D fixed universal nonfactorization"
    remaining:
      - "D transport through C1/C2/C3"
      - "C1/C2/C3 closure"
      - "final completion review"
  certificate_provenance:
    discharged:
      - "positive and negative pairs are the reviewed C2 fixed generated witnesses"
      - "pulled positive coefficient identity is the actual generatedPulledRouteTransport comparator coefficient theorem; pulled negative coefficient identity is generatedPulledIdentityComparator_coefficient_id for the named copied-transport comparator"
      - "decision separation is supplied by the reviewed C2 literal membership and nonmembership theorems"
    unresolved:
      - "transported separation and closure witnesses"
  proof_use:
    used:
      - "CompositeFiberAut.coefficientObservation and coefficientObservation_hom"
      - "generatedPulledRouteTransport.comparator_coefficient_id"
      - "generatedPulledIdentityComparator_coefficient_id"
      - "generatedComparatorUpperReselections_twist_mem_qualifiedComparison"
      - "generatedBaseComparatorPulledIdentity_twist_not_mem_qualifiedComparison"
      - "fixedCoefficientObservation_positive_eq_negative in the universal contradiction"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "targeted direct dependency builds only; no Research aggregate/full build"
    - "cd research/lean && lake env lean ResearchLean/AG/DoctrineFiberProduct/QualifiedComparisonCoefficientNonfactorization.lean; exit 0; 12 declarations standard-only"
    - "reviewed head 1f97320f378f4b301d507a969a88a939bcf50110: four fresh full-head lanes accepted; GitHub CI 7/7 pass"
    - "fixed-head audit: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4378#issuecomment-5550849734"
    - "root acceptance: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4378#issuecomment-5550849735"
    - "merged by PR #4378 at ddb1c26c87a9e282c84606cfc0ec74801cdc6b73"
  blocking_findings: []
  next_obligation: "D transport the observation collision and qualified separation through C1/C2/C3"
```

## Cycle 10 — D transport through C1 and C3

```yaml
ledger_type: target_cycle_result
goal: G-118-aat-diagnostic-descent-transport
cycle: 10
goal_blob_sha: 641f3255062d2578ef070cbb77c019cc28c3febf
base_oid: ddb1c26c87a9e282c84606cfc0ec74801cdc6b73
tracking_issue: 4367
report_path: research/reports/G-118-aat-diagnostic-descent-transport.md
selection:
  proof_state_ref: "Issue #4367 Cycle 10 evidence comparison: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/4367#issuecomment-5550858958; final route correction superseding the provisional route: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/4367#issuecomment-5551078880"
  proof_dag_predecessors:
    - "canonicalGeneratedQualifiedComparisonMulEquivAt and the two selected endpoint conjugation equivalences"
    - "Cycle 9 fixed generated positive/negative pairs, observation collision, and literal qualified decisions"
    - "generatedBaseCompositeFiberAutAt_fac and generatedPulledCompositeFiberAutAt_fac"
    - "generatedComparisonPairHomAt preservation and exact J_i=bottom reflection criterion"
    - "Cycle 9 fixed coefficient nonfactorization"
  proof_obligation: "D transport: show that C1 and C3 commute with the complete product coefficient observation, preserve and reflect the literal qualified decision under their exact hypotheses, and retain coefficient-invisible nonfactorization; C2 is the fixed edge pair already used by Cycle 9"
  selection_reason: "C1 is an exact endpoint-presentation equivalence and C3 is the actual pair homomorphism. Their observation laws and literal Gamma transport isolate exactly which part of D survives each map."
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - research/lean/ResearchLean/AG/DoctrineFiberProduct/QualifiedComparisonCoefficientTransport.lean
  risks:
    - "raw-pair membership reconstruction must not replace the existing exact subgroup MulEquiv"
    - "coefficient preservation must hold for arbitrary automorphisms, not only coefficient-trivial witnesses"
    - "C3 reflection must remain conditional on the exact J_i=bottom criterion"
    - "fixed canonical pairs must be proved equal to the C1 backward images of the Cycle 9 generated witnesses, so both prior witnesses and C1 are proof-used"
  unchecked:
    - "C1/C2/C3 identity, inverse, and typed finite-composition closure"
    - "final completion review"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "For every generated endpoint pair, C1 backward conjugation commutes with the complete product coefficient observation and preserves and reflects literal qualified membership. The raw-pair iff is generated from the same endpoint-conjugation MulEquiv that supplies canonicalGeneratedQualifiedComparisonMulEquivAt. The fixed canonical positive and negative pairs are proved equal to the backward images of the Cycle 9 generated pairs; the observation equality and opposite decisions, hence universal nonfactorization, now consume that same transport chain. For every source pair, the actual C3 product homomorphism preserves both coefficient observations. Under exactly J_i=bottom it preserves and reflects literal qualified membership, and every source observation collision separated by the identity-comparison qualified decision transports to target nonfactorization."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/DoctrineFiberProduct/QualifiedComparisonEndpointTransport.lean
    - research/lean/ResearchLean/AG/DoctrineFiberProduct/QualifiedComparisonCoefficientTransport.lean
    - research/lean/ResearchLean/AG/DoctrineFiberProduct.lean
  claim_mapping:
    theorem_names:
      - inverseConjugatedPair_mem_qualifiedComparison_iff
      - UpperGeometryCompatibleProblemInputData.CanonicalQualifiedPairAt
      - UpperGeometryCompatibleProblemInputData.GeneratedQualifiedPairAt
      - UpperGeometryCompatibleProblemInputData.canonicalPairCoefficientObservationAt
      - UpperGeometryCompatibleProblemInputData.generatedPairCoefficientObservationAt
      - UpperGeometryCompatibleProblemInputData.canonicalPairBackwardAt
      - UpperGeometryCompatibleProblemInputData.canonicalPairBackwardAt_mem_qualifiedComparison_iff
      - UpperGeometryCompatibleProblemInputData.canonicalPairBackwardAt_coefficientObservation
      - UpperGeometryCompatibleProblemInputData.generatedBaseCompositeFiberAutAt_coefficientHom
      - UpperGeometryCompatibleProblemInputData.generatedPulledCompositeFiberAutAt_coefficientHom
      - UpperGeometryCompatibleProblemInputData.sourcePairCoefficientObservationAt
      - UpperGeometryCompatibleProblemInputData.generatedComparisonPairHomAt_coefficientObservation
      - UpperGeometryCompatibleProblemInputData.generatedComparisonPairHomAt_mem_qualifiedComparison_iff_of_kernel_eq_bot
      - UpperGeometryCompatibleProblemInputData.generatedQualifiedDecision_not_factor_of_source_collision
      - UpperDecisionWitness.CanonicalFixedQualifiedPair
      - UpperDecisionWitness.canonicalFixedCoefficientObservation
      - UpperDecisionWitness.CanonicalFixedQualifiedDecision
      - UpperDecisionWitness.canonicalFixedPositiveQualifiedPair
      - UpperDecisionWitness.canonicalFixedNegativeQualifiedPair
      - UpperDecisionWitness.canonicalFixedPositiveQualifiedPair_eq_backward
      - UpperDecisionWitness.canonicalFixedNegativeQualifiedPair_eq_backward
      - UpperDecisionWitness.canonicalFixedCoefficientObservation_positive_eq_negative
      - UpperDecisionWitness.canonicalFixedPositiveQualifiedDecision
      - UpperDecisionWitness.canonicalFixedNegativeNotQualifiedDecision
      - UpperDecisionWitness.canonicalFixedQualifiedDecision_not_factor_through_coefficientObservation
    source_labels:
      - "target theorem (D), transport through C1/C2/C3"
    conjuncts:
      - "C1 all-pair product coefficient-observation commutation"
      - "C1 all-raw-pair qualified-membership iff generated from the endpoint-conjugation MulEquiv underlying canonicalGeneratedQualifiedComparisonMulEquivAt"
      - "fixed canonical positive/negative pairs identified with the Cycle 9 backward images, with transported separation and nonfactorization"
      - "C3 all-source-pair product coefficient-observation preservation"
      - "C3 literal Gamma iff under exactly J_i=bottom"
      - "generic C3 transport of observation-collision nonfactorization"
      - "C2 fixed edge pair is the Cycle 9 witness connected by the native canonical companion pair"
    undischarged_assumptions:
      - "C1/C2/C3 closure and final completion review"
    acceptance_point: "The raw-pair iff is proved from the generic endpoint-conjugation MulEquiv and the actual comparison normalization, avoiding costly reduction of the specialized wrapper while retaining the identical map. No stronger unconditional C3 reflection is claimed."
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "D transport through C1"
      - "D transport through the fixed C2 edge connection"
      - "D transport through C3 under its exact reflection condition"
    remaining:
      - "C1/C2/C3 closure"
      - "final completion review"
  certificate_provenance:
    discharged:
      - "C1 coefficient commutation uses both inverse-conjugation coefficientHom theorems"
      - "C1 literal qualified transport specializes inverseConjugatedPair_mem_qualifiedComparison_iff after the actual comparison normalization; that generic iff is constructed by the endpoint-conjugation MulEquiv underlying canonicalGeneratedQualifiedComparisonMulEquivAt"
      - "fixed canonical pairs are definitionally connected to the reviewed reselection backward transport and proved equal to the Cycle 9 generated pair images"
      - "C3 coefficient preservation is extracted from both actual route factorization equations and coefficient-identity route legs"
      - "C3 decision iff uses the reviewed preservation theorem and the exact J_i=bottom reflection equivalence"
    unresolved:
      - "closure witnesses"
  proof_use:
    used:
      - "canonicalAuthoredBaseConjugation_symm_coefficientHom and canonicalAuthoredPulledConjugation_symm_coefficientHom"
      - "qualifiedComparisonEndpointConjugationMulEquiv via inverseConjugatedPair_mem_qualifiedComparison_iff and canonicalPairBackwardAt_mem_qualifiedComparison_iff"
      - "canonicalFixedPositiveQualifiedPair_eq_backward and canonicalFixedNegativeQualifiedPair_eq_backward"
      - "Cycle 9 fixedCoefficientObservation_positive_eq_negative, fixedPositiveQualifiedDecision, and fixedNegativeNotQualifiedDecision through the C1 transport chain"
      - "generatedBaseCompositeFiberAutAt_fac and generatedPulledCompositeFiberAutAt_fac"
      - "generatedComparisonPairHomAt_preserves_qualifiedComparison and generatedComparisonPairHomAt_reflects_qualifiedComparison_iff"
      - "both product coefficient observation equalities inside the two universal nonfactorization contradictions"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "targeted direct dependency build only: lake build ResearchLean.AG.DoctrineFiberProduct.QualifiedComparisonEndpointTransport; exit 0; 4136 jobs; 28 declarations standard-only"
    - "cd research/lean && lake env lean ResearchLean/AG/DoctrineFiberProduct/QualifiedComparisonCoefficientTransport.lean; exit 0; 24 declarations standard-only"
    - "cd research/lean && lake build ResearchLean.AG.DoctrineFiberProduct.QualifiedComparisonCoefficientTransport; exit 0; 4170 jobs; 24 declarations standard-only"
    - "git diff --check and hidden/BiDi plus axiom/admit/sorry/unsafe scans; clean"
    - "PR #4379 first fixed-head review found the missing integrated C1 chain; repaired by generic/specialized raw Gamma iff, fixed backward-image equalities, and actual proof-use in collision and decisions"
  blocking_findings: []
  next_obligation: "C1/C2/C3 identity, inverse, and typed finite-composition closure"
```

## Cycle 11 — typed C1/C2/C3 closure

```yaml
ledger_type: target_cycle_result
goal: G-118-aat-diagnostic-descent-transport
cycle: 11
goal_blob_sha: 641f3255062d2578ef070cbb77c019cc28c3febf
base_oid: 8899ae98391b285cd6651d6048ad6442c8551709
tracking_issue: 4367
report_path: research/reports/G-118-aat-diagnostic-descent-transport.md
selection:
  proof_state_ref: "Cycle 10 left only the explicit closure paragraph at GOAL lines 190--194 and the all-finite-C1-chain D packet at lines 214--217"
  proof_dag_predecessors:
    - "the selected canonical/generated exact endpoint conjugation equivalences and raw Gamma iff"
    - "C2 coefficient-trivial pointwise multiplication and paired finite-path naturality"
    - "C3 generatedComparisonPairHomAt, exact J_i=bottom reflection, and all-pair coefficient observation"
    - "Cycle 9 fixed positive/negative pair, observation collision, and literal decision separation"
  proof_obligation: "Close C1 under identity, inverse, and type-correct finite composition; close C2 under pointwise product and every finite path; compose C3 only with type-matching selected C1 display changes, with identity/composition laws, Gamma preservation and exact reflection, coefficient compatibility, and generated-image status; transport the fixed D packet through every finite C1 chain"
  selection_reason: "An indexed two-display C1 groupoid exposes exactly the selected canonical/generated changes and makes ill-typed arbitrary-context C3 composition unrepresentable. The fixed source contains no nonidentity selected C1 datum, so source precomposition is the proved identity law; all nontrivial selected C1 composition is typed after C3."
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - research/lean/ResearchLean/AG/DoctrineFiberProduct/QualifiedComparisonTransportClosure.lean
  risks:
    - "an arbitrary endpoint-Iso certificate would move the C1 conclusion into caller input"
    - "C2 finite path must use actual reselected path naturality, not multiply elements from differently typed edge fibers"
    - "C3 must be called surjective only onto MonoidHom.range, never onto the ambient pair group"
    - "C3 reflection must remain equivalent to J_i=bottom"
  unchecked:
    - "fixed-head implementation review"
    - "final four-lane completion review"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "C1 is now the finite indexed groupoid freely generated by the selected forward/backward canonical/generated change. Its raw-pair MulEquiv has explicit identity, append, reverse/inverse, Gamma iff, coefficient-observation commutation, and bijectivity laws. C2 pointwise products retain edgewise Gamma membership, both coefficient identities, and actual solution naturality on every finite path. C3 is the actual generated pair hom followed by a type-correct finite C1 chain; identity and append laws, Gamma preservation, exact J_i=bottom reflection, coefficient commutation, and unconditional surjectivity onto its generated range are proved. The fixed positive/negative observation collision, opposite decisions, and universal nonfactorization are bundled after every finite C1 chain."
  completion_candidate: yes
  lean_artifacts:
    - research/lean/ResearchLean/AG/DoctrineFiberProduct/QualifiedComparisonTransportClosure.lean
    - research/lean/ResearchLean/AG/DoctrineFiberProduct.lean
  claim_mapping:
    theorem_names:
      - UpperGeometryCompatibleProblemInputData.canonicalPairBackwardAt_forward
      - UpperGeometryCompatibleProblemInputData.QualifiedComparisonC1Step.reverse_pairMulEquivAt_apply
      - UpperGeometryCompatibleProblemInputData.QualifiedComparisonC1Step.decision_iff
      - UpperGeometryCompatibleProblemInputData.QualifiedComparisonC1Step.observation_apply
      - UpperGeometryCompatibleProblemInputData.QualifiedComparisonC1Chain.pairMulEquivAt_nil_apply
      - UpperGeometryCompatibleProblemInputData.QualifiedComparisonC1Chain.pairMulEquivAt_append_apply
      - UpperGeometryCompatibleProblemInputData.QualifiedComparisonC1Chain.pairMulEquivAt_reverse_apply
      - UpperGeometryCompatibleProblemInputData.QualifiedComparisonC1Chain.decision_iff
      - UpperGeometryCompatibleProblemInputData.QualifiedComparisonC1Chain.observation_apply
      - UpperGeometryCompatibleProblemInputData.QualifiedComparisonC1Chain.pairMulEquivAt_bijective
      - UpperGeometryCompatibleProblemInputData.coefficientTrivialUpperReselectionEndpointIntertwining_mul_mem
      - UpperGeometryCompatibleProblemInputData.coefficientTrivialUpperReselection_mul_coefficient_id
      - UpperGeometryCompatibleProblemInputData.coefficientTrivialUpperReselectionEndpointIntertwining_mul_path
      - UpperGeometryCompatibleProblemInputData.closedComparisonPairHomAt_nil
      - UpperGeometryCompatibleProblemInputData.closedComparisonPairHomAt_append_apply
      - UpperGeometryCompatibleProblemInputData.closedComparisonPairHomAt_comp_id
      - UpperGeometryCompatibleProblemInputData.closedComparisonPairHomAt_preserves_qualifiedComparison
      - UpperGeometryCompatibleProblemInputData.closedComparisonPairHomAt_reflects_qualifiedComparison_iff
      - UpperGeometryCompatibleProblemInputData.closedComparisonPairHomAt_coefficientObservation
      - UpperGeometryCompatibleProblemInputData.closedComparisonPairHomAt_rangeRestrict_surjective
      - UpperDecisionWitness.fixedQualifiedDecision_not_factor_after_c1_chain
    source_labels:
      - "target theorem (C1/C2/C3 closure and D finite-chain packet)"
    conjuncts:
      - "C1 identity, inverse, typed finite composition, Gamma iff, coefficient commutation, and bijectivity"
      - "C2 pointwise multiplication, literal edge qualification, coefficient identities, and finite-path naturality"
      - "C3 identity source precomposition, typed C1 postcomposition, Gamma preservation, exact reflection, coefficient compatibility, and generated-image surjectivity"
      - "D collision, separation, and nonfactorization after every finite selected C1 chain"
    undischarged_assumptions: []
    acceptance_point: "The closure constructors contain only the two selected actual presentation changes. No arbitrary comparison equality or endpoint certificate is accepted, no cross-context C3--C3 composite is quantified, and the C3 codomain claim stops at its actual range."
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "C1 identity, inverse, and type-correct finite composition"
      - "C2 pointwise product and finite-path connection"
      - "C3 type-correct selected-display composition and identity law"
      - "C1 Gamma/coefficient closure and all-finite-chain D packet"
      - "C3 Gamma preservation, exact reflection, coefficient compatibility, and range status"
    remaining:
      - "independent fixed-head and final completion review"
  certificate_provenance:
    discharged:
      - "C1 constructors are exactly the selected forward/backward endpoint conjugation MulEquiv"
      - "C2 product consumes the existing coefficient-trivial mul and paired endpoint law; path closure consumes the actual reselectedPath_naturality theorem"
      - "C3 starts from generatedComparisonPairHomAt and composes only with an indexed selected C1 chain"
      - "D consumes the Cycle 9 fixed witnesses through the chain Gamma and observation laws"
    unresolved: []
  proof_use:
    used:
      - "canonicalPairBackwardAt_mem_qualifiedComparison_iff and canonicalPairBackwardAt_coefficientObservation in both step directions"
      - "CoefficientTrivialUpperReselectionEndpointIntertwining.mul, coefficient_id, coefficientTrivialUpperReselectionEndpointIntertwining_iff_forall_mem, and reselectedPath_naturality"
      - "generatedComparisonPairHomAt_preserves_qualifiedComparison, generatedComparisonPairHomAt_reflects_qualifiedComparison_iff, and generatedComparisonPairHomAt_coefficientObservation"
      - "fixedCoefficientObservation_positive_eq_negative, fixedPositiveQualifiedDecision, and fixedNegativeNotQualifiedDecision"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "cd research/lean && lake env lean ResearchLean/AG/DoctrineFiberProduct/QualifiedComparisonTransportClosure.lean; exit 0; 91 declarations under AAT.AG.DoctrineFiberProduct standard axioms only"
    - "cd research/lean && lake build ResearchLean.AG.DoctrineFiberProduct.QualifiedComparisonTransportClosure; exit 0; 4171 jobs; 91 declarations under AAT.AG.DoctrineFiberProduct standard axioms only"
    - "git diff --check; clean"
  blocking_findings: []
  next_obligation: "fixed-head implementation review, then final completion audit"
```

## Revision 2 authorization — source-presentation naturality

2026-09-05、人間の指示により、Issue #4367 の第1案を採用して GOAL を revision 2 へ
改訂した。revision 1 の C1 は canonical-authored / generated の target endpoint 表示変更
だけを量化したため、その pair type は `A_B × A_P` であり、C3 の source pair
`A_S × A_S` の前には置けなかった。Cycle 11 の identity-only precomposition は要求未達、
PR #4382 の source coefficient-kernel inner conjugation は固定 C1 の量化域外であり、
`goal-defect` と判定した。

Revision 2 は source input 全体の表示変更 `C1s` と、既存 target endpoint 表示変更 `C1t` を
分ける。C1s は別 source complete geometry、同じ `CoreFiber` 内の iso、その上の exact
complete-geometry iso、両方向 coefficient identity だけを量化する。変更後の diagram、
edge、comparator、transport、両段の qualification、two-cell/coefficient laws は元の入力と
source iso から構成する。変更後 input を既存 generator へ独立に通し、generated endpoint
iso、比較成分の可換式、`T` の中心自然性、Γ/J/生成像/係数観測の対応を theorem として
導く。これらの出力や可換式を certificate field として受け取らない。

Revision 1 の A/B/C1t/C2/C3/D declaration は predecessor artifact として保持するが、
revision 2 の completion evidence へ自動昇格させない。最初の obligation は F0s とし、
`UpperGeometryCompatibleProblemInputData` の changed-input constructor と actual two-stage
generator からの exact endpoint iso の構成可能性を先に確定する。固定 finite witness は
`swap01Iso` / `compositeSwap01` と `compositeSwap12` の local `Fin 4` evaluation を使い、
作用元ではなく induced pair action の非恒等性を証明する。

## Cycle 13 — revision 2 F0s selection

```yaml
ledger_type: target_cycle_result
goal: G-118-aat-diagnostic-descent-transport
cycle: 13
goal_blob_sha: 6eff0d6913d91ac4e8965f2b9459dbf69ca0739a
base_oid: 7d4080a28fbb7d0e20189709c2fbcc59f74809c3
tracking_issue: 4367
report_path: research/reports/G-118-aat-diagnostic-descent-transport.md
selection:
  proof_state_ref: "revision 2 merge #4383 and Issue #4367 synchronization"
  proof_dag_predecessors:
    - UpperGeometryCompatibleProblemInputData
    - FixedCoefficientTwoLayerTransportOver
    - ActiveRefinementBCContext.baseCompositeLegAt_naturality
    - ActiveRefinementBCContext.pulledCompositeLegAt_naturality
    - generatedBaseRouteLegAt_isStronglyCartesian
    - generatedPulledRouteLegAt_isStronglyCartesian
    - CategoryTheory.Functor.IsStronglyCartesian.domainIsoOfBaseIso
    - UpperGeometryCleavage.exactGeometryHomOfRefinement
  proof_obligation: "F0s: source change data と certificate-free changed-input constructor を型付けし、actual lower naturality と strongly-cartesian domain comparison から generated exact endpoint iso を構成できるか判定する"
  selection_reason: "revision 2 の全新規義務が依存する最短の型・provenance gateであり、欠けたsemantic primitiveがあれば後続実装前に固定できる"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCompatibleSourcePresentationNaturalityF0.lean
  risks:
    - dependent functor/structure equality
    - source edge cocartesian qualification under conjugation
    - reverse-route base naturality orientation
    - refinement domain iso exactification
    - conclusion-equivalent endpoint/naturality certificate escape
  unchecked:
    - changed-input constructor elaboration
    - generated exact endpoint iso construction
```
