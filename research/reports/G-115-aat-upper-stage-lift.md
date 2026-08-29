# G-115 — Geometry-Refinement Bridge and Upper BC Relational Naturality

- primary specification: [`research/goals/G-115-aat-upper-stage-lift.md`](../goals/G-115-aat-upper-stage-lift.md)
- tracking Issue: [#4250](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/4250)
- GOAL revision: 2
- proof state: `target-proof-checkpoint`
- completion candidate: no

This report records incremental proof obligations against the fixed revision-2
target. Lean acceptance is evidence for the named cycle only; it is not a
completion verdict for G-115.

## Fixed target

- merged GOAL revision PR: #4252
- final reviewed GOAL head: `ee3e400c92a2946ad2c8e4ee15e8b2cc235b8e39`
- merged GOAL commit and implementation base: `5cb6994f72063e23733bcefb081b11ed4b6f5fef`
- GOAL blob SHA: `b307ba6dfe0c098a85160292c86999b63c8f19c1`

## Cycle 1 — F0 geometry-over-refinement category

```yaml
ledger_type: target_cycle_result
goal: G-115-aat-upper-stage-lift
cycle: 1
goal_blob_sha: b307ba6dfe0c098a85160292c86999b63c8f19c1
base_oid: 5cb6994f72063e23733bcefb081b11ed4b6f5fef
tracking_issue: 4250
report_path: research/reports/G-115-aat-upper-stage-lift.md
selection:
  proof_state_ref: research/goals/G-115-aat-upper-stage-lift.md next action F0
  proof_dag_predecessors: [G-108 exact geometry contract, G-114 refinement category]
  proof_obligation: Define the geometry-over-refinement category, its lax projection, and the faithful exact embedding without inventing an exact lower leg.
  selection_reason: This is the missing bridge required to type every later G-114 geometry leg.
  expected_result_type: proof-obligation-discharged
  lean_targets: [ResearchLean/AG/DoctrineFiberProduct/RefinementGeometry.lean]
  risks: [lax lower provenance, upper index-map coherence, category laws, exact embedding faithfulness, competing category instances]
  unchecked: [G-114 composite geometry legs, upper decision and negative problems, paired orbit and conditional exchange interface]
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: The F0 bridge primitive is constructed and focused-checked; clauses (b)--(d) remain.
  completion_candidate: no
  lean_artifacts: [RefinementGeometryHom, RefinementGeometryCategory, refinementGeometryProjection, exactGeometryToRefinementGeometry]
  evidence: [RefinementCoverageTransport.no_transport_to_emptyTarget, exact_refinementGeometry_projection_square, exactGeometryToRefinementGeometry_faithful, standard-axiom audit]
  claim_mapping:
    theorem_names: [refinementGeometryCategory, refinementGeometryProjection, exactGeometryToRefinementGeometry, exact_refinementGeometry_projection_square]
    source_labels: [target theorem clause (a), target proof strategy F0]
    conjuncts: [lax base field and upper-indexed geometry contract, identity and composition laws, lax projection, faithful exact embedding and projection square]
    undischarged_assumptions: [source fiber diagram and individual legs, named decision and negative problems, paired cochain and restricted orbit theorem, conditional orbit equivalence]
    acceptance_point: Clause (a) is discharged by definitions and proofs whose lower projection is the stored RefinementPackageHom.
    port_status: not-applicable
audits:
  premise_delta:
    discharged: [RefinementGeometryHom category projection and exact embedding]
    remaining: [target theorem clauses (b)--(d)]
  certificate_provenance:
    discharged: [exact embedding comes from PointedRefinementHom.ofExact through exactPackageToRefinement]
    unresolved: [named decision and negative witnesses, paired reselection witnesses]
  proof_use:
    used: [RefinementPackageHom.upper for every geometry index map, stored lax base for projection, exactPackageToRefinement for the exact comparison]
    unused: [G-114 mate and selected composite legs, G-109 comparator and cochain]
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found — identity supplies the positive coverage certificate and RefinementCoverageTransport.no_transport_to_emptyTarget supplies the negative instance
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [lake env lean ResearchLean/AG/DoctrineFiberProduct/RefinementGeometry.lean — exit 0; axiom audit 121 declarations standard axioms only; source SHA-256 afd00798ddb448659ca2a0ddc5826cb67855805ba7ac3427f4c5f70883eba6b1]
  blocking_findings: []
  next_obligation: K1 define the G-114 composite refinement-geometry legs and factorization triangle.
```

The category object uses a transparent wrapper around `GeometryPackage` only
to prevent the exact and lax hom structures from competing for the same Lean
category instance. The mathematical object data are unchanged. A general lax
morphism stores `RefinementPackageHom` as its base and derives all context,
equation, support, axis, and observable indices from that base's complete
`upper` reading. The projection therefore returns the actual lax lower route.

The exact embedding is separately constructed through
`exactPackageToRefinement`; its faithfulness is proved by recovering both the
exact package morphism and the four computational geometry fields. No exact
lower morphism is added to the lax hom structure.

## Cycle 2 — K1a G-114 composite package-route base

```yaml
ledger_type: target_cycle_result
goal: G-115-aat-upper-stage-lift
cycle: 2
goal_blob_sha: b307ba6dfe0c098a85160292c86999b63c8f19c1
base_oid: e2c4e3d773b928860f08608f4b126a00ed2f4497
tracking_issue: 4250
report_path: research/reports/G-115-aat-upper-stage-lift.md
selection:
  proof_state_ref: research/goals/G-115-aat-upper-stage-lift.md target proof strategy K1 package-route sub-obligation
  proof_dag_predecessors: [G-112 exact selected lifts, G-114 active context and canonical mate, Cycle 1 refinement-geometry bridge]
  proof_obligation: Fix the package bases of the two actual G-112/G-114 composite legs and derive mate verticality and the complete-upper factorization equation without selecting geometry transport data. This is K1a, not the whole K1 geometry obligation.
  selection_reason: The later geometry legs must project to these routes; their lower provenance and upper mate equation must be available before finite problem fixtures are constructed.
  expected_result_type: proof-obligation-discharged
  lean_targets: [ResearchLean/AG/DoctrineFiberProduct/UpperRefinementBCRoutes.lean]
  risks: [dependent CoreFiber endpoint transport, replacement of a lax leg by an exact leg, conflation of lower factor laws with the upper equation]
  unchecked: [individual refinement-geometry legs and projection factor laws and geometry-level triangle, finite source fiber diagram, full geometry naturality hypotheses, named decision and negative problems, paired orbit and conditional exchange interface]
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: The package-route sub-obligation is discharged; individual RefinementGeometryHom legs, their projection factor laws, and the geometry-level triangle remain in K1b.
  completion_candidate: no
  lean_artifacts: [refinementPackageHomOfOver, ActiveRefinementBCContext.baseCompositeLeg, ActiveRefinementBCContext.pulledCompositeLeg, ActiveRefinementBCContext.refinementMateAtTarget]
  evidence: [ActiveRefinementBCContext.baseCompositeLeg_base, ActiveRefinementBCContext.pulledCompositeLeg_base, ActiveRefinementBCContext.refinementMate_isHomLift, ActiveRefinementBCContext.refinementMate_upper_triangle, standard-axiom audit]
  claim_mapping:
    theorem_names: [ActiveRefinementBCContext.baseCompositeLeg_base, ActiveRefinementBCContext.pulledCompositeLeg_base, ActiveRefinementBCContext.refinementMate_isHomLift, ActiveRefinementBCContext.refinementMate_upper_triangle]
    source_labels: [target theorem clause (b), target proof strategy K1]
    conjuncts: [G-112 then G-114 base composite, G-114 then G-112 pulled composite, exact vertical mate embedding, universal-property upper factorization]
    undischarged_assumptions: [source fiber diagram and individual geometry legs and projection factor laws and geometry-level triangle, named decision and negative problems, paired cochain and restricted orbit theorem, conditional orbit equivalence]
    acceptance_point: The K1a package routes are definitions using the reviewed G-112 and G-114 morphisms, while the upper equation consumes the G-114 hom-equivalence factor law and mate-route factor law. This does not discharge the K1 geometry-level triangle.
    port_status: not-applicable
audits:
  premise_delta:
    discharged: [K1a G-114 composite package-route definitions and objectwise upper mate factorization]
    remaining: [K1b individual refinement-geometry legs and projection factor laws and geometry-level triangle, target theorem clause (b) finite problems and solutions, clauses (c)--(d)]
  certificate_provenance:
    discharged: [mate is ctx.mateAtTarget; exact legs are exact_bottom_semantic_global_selected_lift; lax legs are ctx.legacyRegime cleavage outputs generated from ctx.condition]
    unresolved: [named decision and negative witnesses, paired reselection witnesses]
  proof_use:
    used: [pulledCleavage.homEquiv_fac, legacyRegime.mateRoute_fac, pulled_square route definitions, exactPackageToRefinement]
    unused: [G-109 comparator and cochain, geometry support axis and observable comparisons]
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: not-applicable — this cycle fixes actual routes and does not claim a geometry solution
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [lake env lean ResearchLean/AG/DoctrineFiberProduct/UpperRefinementBCRoutes.lean — exit 0; axiom audit 8 declarations standard axioms only; source SHA-256 ea3ca8e28aea2ce61988b217d25740a78eacf18dd50f94c0c745b36bbfe2f01a]
  blocking_findings: []
  next_obligation: K1b type the individual RefinementGeometryHom legs over these package bases, prove their projection factor laws, and construct the geometry-level factorization triangle before starting K2 finite problems.
```

The dependent endpoint equalities carried by `CoreFiber` are retained when a
relative G-114 hom is read as a refinement-package hom.  The base and pulled
legs therefore use the authored lax refinements themselves.  The mate theorem
does not infer lower data from its complete upper map: the two lower composite
laws, the mate's vertical projection, and the complete-upper factorization are
separate declarations. They are the package-route base for K1, not a substitute
for the still-unproved refinement-geometry legs or geometry-level triangle.
