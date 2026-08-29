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
  validation_refs: [research/lean/check_research_modules.sh --focused ResearchLean/AG/DoctrineFiberProduct/UpperRefinementBCRoutes.lean — exit 0; module registered in research/lean/research-modules.txt and ResearchLean/AG/DoctrineFiberProduct.lean; axiom audit 8 declarations standard axioms only; source SHA-256 ea3ca8e28aea2ce61988b217d25740a78eacf18dd50f94c0c745b36bbfe2f01a]
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

## Cycle 3 — K1b indexed refinement-geometry legs

```yaml
ledger_type: target_cycle_result
goal: G-115-aat-upper-stage-lift
cycle: 3
goal_blob_sha: b307ba6dfe0c098a85160292c86999b63c8f19c1
base_oid: 93dbf67f1896212a6cc351f089dc9424927c7090
tracking_issue: 4250
report_path: research/reports/G-115-aat-upper-stage-lift.md
selection:
  proof_state_ref: research/goals/G-115-aat-upper-stage-lift.md target theorem clause (b), target proof strategy K1
  proof_dag_predecessors: [Cycle 1 refinement-geometry bridge, Cycle 2 K1a composite package routes]
  proof_obligation: Index the two actual composite routes by every target package, type individual RefinementGeometryHom legs over those routes with a definitionally fixed coefficient ring, prove their projection and lower factor laws, and expose the exact computational criterion used later to construct the geometry-level triangle. Do not store a route-between component or triangle in raw leg data.
  selection_reason: A finite source diagram requires one route pair per vertex. The former K1a definitions were the specialization at ctx.targetPackage and could not by themselves type a vertex family.
  expected_result_type: proof-obligation-discharged
  lean_targets: [ResearchLean/AG/DoctrineFiberProduct/UpperRefinementBCGeometry.lean]
  risks: [single-target route mistaken for a finite family, dependent coefficient casts, unrelated exact lower arrow, package upper equality mistaken for full geometry equality, route-between conclusion moved into direction data]
  unchecked: [finite presentation and source fiber diagram, route-internal edge naturality and its projection laws, actual vertical geometry components and triangles, named decision and negative problems, paired orbit and conditional exchange interface]
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: K1b route indexing, individual leg typing, coefficient identity, projection and lower factor laws, and the solution-side triangle extensionality criterion are discharged. Actual geometry components and triangle inhabitants remain part of the K2 solution construction.
  completion_candidate: no
  lean_artifacts: [FixedCoefficientGeometryAt, ActiveRefinementBCContext.retarget, ActiveRefinementBCContext.baseCompositeLegAt, ActiveRefinementBCContext.pulledCompositeLegAt, ActiveRefinementBCGeometryLegData, ActiveRefinementBCGeometryLegData.baseLeg, ActiveRefinementBCGeometryLegData.pulledLeg, RefinementGeometryHom.exact_comp_eq]
  evidence: [ActiveRefinementBCContext.compositeLegAt_upper_triangle, ActiveRefinementBCGeometryLegData.baseLeg_projection, ActiveRefinementBCGeometryLegData.pulledLeg_projection, ActiveRefinementBCGeometryLegData.baseLeg_lower_factor, ActiveRefinementBCGeometryLegData.pulledLeg_lower_factor, ActiveRefinementBCGeometryLegData.baseLeg_coefficient_id, ActiveRefinementBCGeometryLegData.pulledLeg_coefficient_id, standard-axiom audit]
  claim_mapping:
    theorem_names: [ActiveRefinementBCGeometryLegData.baseLeg_projection, ActiveRefinementBCGeometryLegData.pulledLeg_projection, ActiveRefinementBCGeometryLegData.baseLeg_lower_factor, ActiveRefinementBCGeometryLegData.pulledLeg_lower_factor, RefinementGeometryHom.exact_comp_eq]
    source_labels: [target theorem clause (b), target proof strategy K1]
    conjuncts: [all-target package indexing, individual actual-route geometry legs, coefficient identity, separate lower factor laws, non-core-only triangle criterion]
    undischarged_assumptions: [finite source diagram and route-internal naturality, named actual solution and non-liftable problem, paired cochain and restricted orbit theorem, conditional orbit equivalence]
    acceptance_point: Geometry transport remains the allowed route-internal direction hypothesis, but its base is definitionally the reviewed actual composite route and its coefficient morphism is fixed to identity. The triangle helper requires full package equality and coefficient/support/axis/observable comparisons rather than inferring geometry equality from the upper route law.
    port_status: not-applicable
audits:
  premise_delta:
    discharged: [K1b per-target route family and individual refinement-geometry leg interface, projection and lower route factor laws, geometry triangle assembly criterion]
    remaining: [target theorem clause (b) finite problems and named positive and negative artifacts, clauses (c)--(d)]
  certificate_provenance:
    discharged: [route family is ctx.retarget applied to the reviewed G-112 and G-114 constructions; geometry data is explicitly classified as direction-hypothesis]
    unresolved: [named decision and negative witnesses, paired reselection witnesses]
  proof_use:
    used: [Cycle 2 package routes, RefinementPackageHom base as the geometry-contract index, refinementGeometryProjection, exactGeometryToRefinementGeometry, RefinementGeomReadHom extensionality]
    unused: [actual geometry mate component, G-109 comparator and cochain]
  structure_field_escape: none-found — leg data contains only route-internal geometry direction data and coefficient identity; no route-between component, triangle, edge equation, comparator equation, IsIso, or non-liftability certificate
  route_integrity: pass
  target_fitting: none-found
  vacuity: not-applicable — this cycle types the required nonempty per-vertex interface and does not claim a named solution
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [research/lean/check_research_modules.sh --focused ResearchLean/AG/DoctrineFiberProduct/UpperRefinementBCGeometry.lean — exit 0; module registered in research/lean/research-modules.txt and ResearchLean/AG/DoctrineFiberProduct.lean; axiom audit 49 declarations standard axioms only; source SHA-256 8cc44533649b1db6da278181c84ba2756d5d297a27e48f23693f5b2eecb6381d]
  blocking_findings: []
  next_obligation: K2 define the finite UpperRefinementBCProblem source fiber diagram, per-route qualified geometry data and route-internal naturality, then construct the named decision solution and named non-liftable problem without placing route-between conclusions in the raw problem.
```

`retarget` changes only the chosen target package; the configuration, compatible
source, and realized-support condition are unchanged. Thus the two package
routes are generated by the same reviewed G-112/G-114 constructions at every
vertex. The geometry contracts occur over those routes as dependent indices,
so a caller cannot satisfy the interface with an unrelated exact lower arrow.

The triangle helper deliberately exposes four computational geometry
comparisons in addition to the full package equality. Coverage, overlap, and
the remaining proposition-valued laws are eliminated by the existing
extensionality theorem. This helper is not an actual solution and does not turn
the later route-between triangle into a raw-problem hypothesis.

## Cycle 4 — K2a finite raw upper-problem interface

```yaml
ledger_type: target_cycle_result
goal: G-115-aat-upper-stage-lift
cycle: 4
goal_blob_sha: b307ba6dfe0c098a85160292c86999b63c8f19c1
base_oid: ebf948e91c0bacb46f7e14e8bb374215cad0717e
tracking_issue: 4250
report_path: research/reports/G-115-aat-upper-stage-lift.md
selection:
  proof_state_ref: research/goals/G-115-aat-upper-stage-lift.md target theorem clause (b), target proof strategy K2 raw-problem sub-obligation
  proof_dag_predecessors: [G-109 TwoLayerTransportData, Cycle 3 indexed refinement-geometry legs]
  proof_obligation: Define the finite raw UpperRefinementBCProblem with a root-connected free-path presentation, an actual source CoreFiber functor, source/base/pulled qualified G-109 data, fixed coefficient identities, and route-internal full geometry naturality. Exclude every route-between solution field.
  selection_reason: Named positive and negative artifacts must share one exact raw-problem contract whose source edges are fiber-vertical and whose route provenance is definitionally tied to the G-112/G-114 functors.
  expected_result_type: proof-obligation-discharged
  lean_targets: [ResearchLean/AG/DoctrineFiberProduct/UpperRefinementBCProblem.lean]
  risks: [arbitrary object family mistaken for an actual functor, quotienting away authored parallel paths, dependent core and coefficient casts, route-between conclusion stored in raw data, edge-only naturality not extended to paths]
  unchecked: [G-112/G-114 factor-graph reconstruction of the projected naturality equation, actual UpperRefinementBCSolution, named decision and non-liftable problems, paired orbit and conditional exchange interface]
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: The K2a raw-problem type is constructed. Actual solution and named positive/negative inhabitants remain K2b.
  completion_candidate: no
  lean_artifacts: [PresentedPathCategory, FixedCoefficientTwoLayerTransportOver, ActiveRefinementBCContext.baseCoreDiagram, ActiveRefinementBCContext.pulledCoreDiagram, UpperRefinementBCProblemData, UpperRefinementBCProblem]
  evidence: [FixedCoefficientTwoLayerTransportOver.edge_projection, UpperRefinementBCProblemData.base_naturality_projection, UpperRefinementBCProblemData.pulled_naturality_projection, UpperRefinementBCProblemData.base_path_naturality, UpperRefinementBCProblemData.pulled_path_naturality, standard-axiom audit]
  claim_mapping:
    theorem_names: [FixedCoefficientTwoLayerTransportOver.edge_projection, UpperRefinementBCProblemData.base_naturality_projection, UpperRefinementBCProblemData.pulled_naturality_projection, UpperRefinementBCProblemData.base_path_naturality, UpperRefinementBCProblemData.pulled_path_naturality]
    source_labels: [target theorem clause (b), target proof strategy K2]
    conjuncts: [finite free-path category, root reachability, actual source CoreFiber functor, three fixed-coefficient qualified G-109 data sets, actual route diagrams, generator and path geometry naturality, separate package projection]
    undischarged_assumptions: [actual solution components and route-between equations, named decision and non-liftable problems, paired cochain and restricted orbit theorem, conditional orbit equivalence]
    acceptance_point: Source/base/pulled object cores are definitionally the objects of actual CoreFiber diagrams. Geometry edge projection is an equality with the diagram map; route naturality is the only conclusion-like direction hypothesis and is internal to each route.
    port_status: not-applicable
audits:
  premise_delta:
    discharged: [K2a finite raw problem interface, source fiber-vertical diagram, G-109 qualification packaging, coefficient identity signature, route-internal path naturality]
    remaining: [projected predecessor factor-graph comparison, K2b named positive and negative artifacts, clauses (c)--(d)]
  certificate_provenance:
    discharged: [base and pulled core diagrams are functor composites of sourceFiberDiagram with reviewed G-114 reverse functors and G-112 reindex functors]
    unresolved: [named decision and negative witnesses, paired reselection witnesses]
  proof_use:
    used: [PresentedPath.append laws, actual CoreFiber functor maps, G-109 TwoLayerTransportData, K1b actual-route legs, exact geometry embedding, route generator naturality]
    unused: [G-114 mate component, G-109 route-between comparator equation and cochain]
  structure_field_escape: none-found — raw data contains only source/base/pulled route-internal fields; no route-between component, triangle, route-between edge or comparator equation, IsIso, orbit law, or non-liftability certificate
  route_integrity: pass
  target_fitting: none-found
  vacuity: not-applicable — this cycle fixes a raw type and does not claim a named inhabitant
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [research/lean/check_research_modules.sh --focused ResearchLean/AG/DoctrineFiberProduct/UpperRefinementBCProblem.lean — exit 0; module registered in research/lean/research-modules.txt and ResearchLean/AG/DoctrineFiberProduct.lean; axiom audit 85 declarations standard axioms only; source SHA-256 6483f02181ed7649c8dfd6148b53fd9df8a803000f34534bcf1c46955e6bbe9a]
  blocking_findings: []
  next_obligation: K2b reconstruct the package projection factor graphs from the G-112 reindex-map and G-114 reverse-map laws, define UpperRefinementBCSolution, and construct named decision and non-liftable artifacts without changing the raw problem.
```

The free path category does not quotient declared parallel paths: G-109's
authored comparators still compare two distinct path evaluations. The actual
source functor fixes every edge in one `CoreFiber`, while the base and pulled
core diagrams are derived by functor composition rather than supplied again.

Generator-level full geometry naturality is the permitted direction
hypothesis. The two path theorems extend it by identity, composition, and the
exact geometry embedding. Applying the refinement-geometry projection yields
separate package equations; this cycle does not call those equations an actual
route-between solution.
