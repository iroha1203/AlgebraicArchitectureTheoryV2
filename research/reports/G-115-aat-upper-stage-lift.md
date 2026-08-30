# G-115 — Geometry-Refinement Bridge and Upper BC Relational Naturality

- primary specification: [`research/goals/G-115-aat-upper-stage-lift.md`](../goals/G-115-aat-upper-stage-lift.md)
- tracking Issue: [#4250](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/4250)
- GOAL revision: 3 candidate
- proof state: `target-proof-checkpoint`
- completion candidate: no

This report records incremental proof obligations through the revision-3
candidate. Cycles 1--5 remain accepted evidence for their named interfaces;
revision 3 adds the G-115-local geometry cleavage required before the named
fixture cycle. Lean acceptance is evidence for the named cycle only; it is not
a completion verdict for G-115.

## Fixed target

- merged GOAL revision PR: #4252
- final reviewed GOAL head: `ee3e400c92a2946ad2c8e4ee15e8b2cc235b8e39`
- merged GOAL commit and implementation base: `5cb6994f72063e23733bcefb081b11ed4b6f5fef`
- GOAL blob SHA: `b307ba6dfe0c098a85160292c86999b63c8f19c1`

Revision 3 candidate is based on merge `f09dc1fe36853eea5f9854cc4ecfad8f60a667f8`.
Its GOAL blob is `3c7dd5c34934205817b88d39c00d53b116fbb8f9` and its
SHA-256 is `a11f61a5790c8ac75ce7f13da1277a859e2ab600ac96038bc55c338b80d38985`.
The revision becomes the fixed target only after its PR review and merge.

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

## Cycle 5 — K2b1 factor graphs and actual-solution contract

```yaml
ledger_type: target_cycle_result
goal: G-115-aat-upper-stage-lift
cycle: 5
goal_blob_sha: b307ba6dfe0c098a85160292c86999b63c8f19c1
base_oid: 420ce1fc6cc066409b6cca660f816590537fcb48
tracking_issue: 4250
report_path: research/reports/G-115-aat-upper-stage-lift.md
selection:
  proof_state_ref: research/goals/G-115-aat-upper-stage-lift.md target theorem clause (b), K2 actual-solution sub-obligation
  proof_dag_predecessors: [Cycle 4 finite raw problem, G-112 reindex-map factor graph, G-114 reverse-map factor graph]
  proof_obligation: Reconstruct both full RefinementPackageHom route-naturality projections from predecessor factor laws, define UpperRefinementBCSolution without changing the raw problem, and derive nil/path/append/authored-two-cell equations.
  selection_reason: The actual solution contract must expose route-between geometry data while independently checking that the raw route projections retain the G-112/G-114 lower provenance.
  expected_result_type: target-proof-checkpoint
  lean_targets: [ResearchLean/AG/DoctrineFiberProduct/UpperRefinementBCSolution.lean]
  risks: [upper-only factor graph, raw-field escape, caller-supplied solution counted as O10 discharge, comparator treated as canonical, authored raw defect forced to vanish, dependent endpoint casts]
  unchecked: [named upperDecisionProblem and upperDecisionSolution, concrete nonidentity component evaluation, named non-liftable problem, paired orbit and conditional exchange interface]
result:
  proposed_result_type: target-proof-checkpoint
  proof_obligation_delta: Full package factor graphs and the actual solution signature are fixed. Named positive and negative inhabitants remain K2b2 and are not claimed here.
  completion_candidate: no
  lean_artifacts: [refinementPackageHomOfOver_precomp, refinementPackageHomOfOver_postcomp, ActiveRefinementBCContext.baseCompositeLegAt_naturality, ActiveRefinementBCContext.pulledCompositeLegAt_naturality, UpperRefinementBCSolution]
  evidence: [UpperRefinementBCProblemData.base_naturality_factor_graph, UpperRefinementBCProblemData.pulled_naturality_factor_graph, UpperRefinementBCSolution.nil_naturality, UpperRefinementBCSolution.path_naturality, UpperRefinementBCSolution.append_naturality, UpperRefinementBCSolution.authored_twoCell_pasting, standard-axiom audit]
  claim_mapping:
    theorem_names: [ActiveRefinementBCContext.baseCompositeLegAt_naturality, ActiveRefinementBCContext.pulledCompositeLegAt_naturality, UpperRefinementBCProblemData.base_naturality_factor_graph, UpperRefinementBCProblemData.pulled_naturality_factor_graph, UpperRefinementBCSolution.path_naturality, UpperRefinementBCSolution.append_naturality, UpperRefinementBCSolution.authored_twoCell_pasting]
    source_labels: [target theorem clause (b), target proof strategy K2]
    conjuncts: [full package projection factor graph, vertical component signature, actual mate base, coefficient identity, geometry triangle, route-between edge naturality, authored comparator intertwining, nil/path/append/two-cell equations]
    undischarged_assumptions: [actual named solution inhabitant, named non-liftability proof, concrete nonidentity support-axis-observable evaluation, paired reselection and exchange artifacts]
    acceptance_point: Generic route theorems consume the named G-112 and G-114 factor laws directly. Edge corollaries use only the three edge_base equations and derived core diagrams, never the raw geometry-naturality fields.
    port_status: not-applicable
audits:
  premise_delta:
    discharged: [projected predecessor factor-graph comparison, actual solution type, nil/path/append equations, authored left-path two-cell pasting]
    remaining: [K2b2 named decision and non-liftable artifacts, clauses (c)--(d)]
  certificate_provenance:
    discharged: [route factor equations derive from exact_bottom_semantic_global_reindex_map_fac and LegacyRefinementCartesianCleavage.reverseMap_fac]
    unresolved: [named solution and negative witnesses, paired reselection witnesses]
  proof_use:
    used: [G-112 reindex-map factor law, G-114 base and pulled reverse-map factor laws, exact vertical HomLift equations, route edge projections, solution edge naturality, solution comparator intertwining]
    unused: [raw base_naturality and pulled_naturality in factor-graph proofs, G-109 canonical comparator, orbit membership]
  structure_field_escape: none-found — route-between fields occur only in UpperRefinementBCSolution; the raw UpperRefinementBCProblemData is unchanged
  route_integrity: pass
  target_fitting: none-found
  vacuity: not-applicable — this checkpoint fixes a solution contract and does not claim a named inhabitant
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [research/lean/check_research_modules.sh --focused ResearchLean/AG/DoctrineFiberProduct/UpperRefinementBCSolution.lean — exit 0; lake build ResearchLean.AG.DoctrineFiberProduct.UpperRefinementBCSolution — exit 0; module registered in research/lean/research-modules.txt and ResearchLean/AG/DoctrineFiberProduct.lean; axiom audit 28 declarations standard axioms only; source SHA-256 dd95c2e0b890650a00b7a63b90b4669bc54f1aa7048dfd0e1b8e0c25709ff52d]
  blocking_findings: []
  next_obligation: K2b2 construct upperDecisionContext, upperDecisionProblem, upperDecisionSolution, a concrete nonidentity component firing, and a separate named non-liftable problem without adding certificates to the raw problem.
```

The base and pulled generic naturality proofs are full package equalities. Each
one composes a G-112 reindex-map factor graph with the corresponding G-114
reverse-map factor graph through explicit exact-vertical pre/postcomposition
bridges. The problem-level corollaries then rewrite only the actual diagram
edge projections.

`UpperRefinementBCSolution` contains the route-between data that were excluded
from the raw problem: actual vertical components, their mate and coefficient
projections, full geometry triangles, edge naturality, and authored-comparator
intertwining. The authored two-cell theorem pastes the left path with the
authored comparator; it does not identify the authored comparator with the
canonical comparator or force the raw defect to vanish.

## Cycle 6 — revision 3 geometry-cleavage repair

```yaml
ledger_type: target_cycle_result
goal: G-115-aat-upper-stage-lift
cycle: 6
goal_blob_sha: 3c7dd5c34934205817b88d39c00d53b116fbb8f9
base_oid: f09dc1fe36853eea5f9854cc4ecfad8f60a667f8
tracking_issue: 4250
report_path: research/reports/G-115-aat-upper-stage-lift.md
selection:
  proof_state_ref: research/goals/G-115-aat-upper-stage-lift.md revision 3 disposition and K2b2a
  proof_dag_predecessors: [G-108 geometry contract, G-112 explicit strongCartesianLiftOfTarget constructor, G-114 active context and mate, Cycles 1--5]
  proof_obligation: Repair the K2b2 route inside G-115 by constructing a geometry-compatible exact/refinement cleavage, a generated geometry-level comparison to the unchanged G-114 mate, and the induced solution/reselection/cochain transport.
  selection_reason: The G-112 selected core lift intentionally exposes only the core universal property. Geometry realization is a new downstream obligation and must not be supplied by editing a completed predecessor or by adding a caller field.
  expected_result_type: target-proof-checkpoint
  lean_targets: [ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCleavage.lean]
  risks: [parallel route disconnected from G-114, core-only comparison that cannot transport solutions or reselections, existential suborbit membership without witness transport, caller-supplied HGeom, endpoint equality cast replacing comparison iso, retrospective predecessor edit, scope overclaim]
  unchecked: [Lean signature and construction of UpperGeometryCleavage, upperGeometryMate, geometry-level G-114 mate comparison, solution-space equivalence, restricted reselection transport, named positive and negative artifacts, paired orbit and conditional exchange interface]
result:
  proposed_result_type: target-proof-checkpoint
  proof_obligation_delta: Revision 3 fixes the missing obligation in the current GOAL while preserving G-112 and G-114 unchanged. Lean implementation remains the next cycle.
  completion_candidate: no
  lean_artifacts: []
  evidence: [revision-3 GOAL contract and material-premise ledger]
  claim_mapping:
    theorem_names: []
    source_labels: [target theorem clause (b), revision disposition, target proof artifacts, material premise ledger]
    conjuncts: [G-115-local generated geometry cleavage, generated upper mate, G-114 geometry-level mate comparison, solution-space reselection and cochain transport, predecessor immutability]
    undischarged_assumptions: [all revision-3 Lean artifacts, named decision and negative artifacts, paired reselection and exchange artifacts]
    acceptance_point: This cycle revises the fixed target only; it does not claim implementation or O10 discharge.
    port_status: not-applicable
audits:
  premise_delta:
    discharged: []
    remaining: [G-115-local geometry cleavage, geometry-level mate comparison and solution-space equivalence, named decision and negative problems, clauses (c)--(d)]
  certificate_provenance:
    discharged: []
    unresolved: [generated geometry cleavage, G-114 geometry comparison and solution/reselection/cochain transport, named solution and negative witnesses]
  proof_use:
    used: [K2b2 blocker analysis distinguishing core strong lift data from geometry realization data]
    unused: [explicit lift constructors and universal comparison theorems pending Lean implementation]
  structure_field_escape: prohibited by revised anti-weakening rule
  route_integrity: pending Lean implementation and fixed-head review
  target_fitting: pending Lean implementation
  vacuity: pending named fixtures
  one_way_as_equivalence: prohibited by explicit two-sided solution-space transport requirement
  goal_or_report_reinterpretation: revision is explicit and does not rewrite predecessor GOALs
  validation_refs: [git diff --check; hidden and bidirectional Unicode scan]
  blocking_findings: [review round 1 found that a core-only comparison square did not prevent a geometry-level parallel route; review round 2 found that existential suborbit agreement did not identify reselection witnesses; revised target now requires generated geometry comparison, solution-space equivalence, restricted reselection transport, and cochain compatibility]
  next_obligation: Re-review revision 3, then construct UpperGeometryCleavage, upperGeometryMate, and the generated geometry comparison without changing G-112 or G-114.
```

The former K2b2 stop correctly identified that generic realization transport
does not follow from an arbitrary core `StrongCartesianLift`. Its proposed
repair was wrong: changing G-112 would make a downstream need retroactive.
Revision 3 instead places the missing cleavage at the geometry stage that first
needs it. The literal G-114 mate remains the immutable core comparison target.
Review round 1 showed that a core-only square could leave a parallel geometry
route. The revised candidate therefore requires the generated comparison to
lift to geometry, preserve the presentation, legs, edges, and authored
comparators, induce two-sided transports of solution spaces and restricted
reselection spaces, and be consumed again by the cochain and paired-relation
theorems. Endpoint casts and supplied fields remain forbidden.

## Cycle 7 — K2b2a explicit upper geometry pullback checkpoint

```yaml
ledger_type: target_cycle_result
goal: G-115-aat-upper-stage-lift
cycle: 7
goal_blob_sha: 3c7dd5c34934205817b88d39c00d53b116fbb8f9
base_oid: 79fcc84a3c651edccc286ea1b55873cfc13f6749
tracking_issue: 4250
report_path: research/reports/G-115-aat-upper-stage-lift.md
selection:
  proof_state_ref: research/goals/G-115-aat-upper-stage-lift.md revision 3 K2b2a
  proof_dag_predecessors: [G-108 geometry contract, G-112 explicit inverse-package upper pair, G-114 realized-refinement transport]
  proof_obligation: Construct HGeom-free geometry source packages and strict raw roundtrips for the explicit exact/refinement lifts, then expose the exact lift's objectwise realization carrier and reading transport.
  selection_reason: Revision 3 places the missing geometry cleavage in G-115 and forbids retrospective predecessor edits or caller-supplied HGeom. The generic refinement construction remains relative to G-114's reviewed RealizedLocusExtractionReflecting ambient input; specialization to the active ctx.condition remains pending.
  expected_result_type: target-proof-checkpoint
  lean_targets: [ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCleavage.lean, ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCleavageRealization.lean]
  risks: [strict raw equality, dependent carrier casts, restriction naturality, accidental lower inverse]
  unchecked: [complete exact/refinement geometry hom, generated cleavage, upper geometry mate, G-114 comparison, solution/reselection transport, named artifacts, clauses (c)--(d)]
result:
  proposed_result_type: target-proof-checkpoint
  proof_obligation_delta: The explicit exact/refinement target-to-source geometry packages, upper-only raw reindex algebra, and strict forward raw equalities are constructed. On the exact branch, carrier comparisons and three reading-preservation laws are also constructed. Refinement realization comparisons and both branches' restriction naturality remain open.
  completion_candidate: no
  lean_artifacts: [exactSourceGeometry, exactSourceGeometry_raw_forward, refinementSourceGeometry, refinementBaseHom, refinementSourceGeometry_raw_forward, exactSupportComp, exactAxisComp, exactObservableComp, exactSupportReads, exactAxisReads, exactObservableReads]
  evidence: [two focused Lean checks, namespace standard-axiom audits, source hashes, literal scans]
  source_sha256:
    UpperGeometryCleavage.lean: 6cc5a6f0a781895af34a58ed2ae4bda1be9da28eed43242ab3adcb8ac5742d8e
    UpperGeometryCleavageRealization.lean: 2ca20e5333c0dbb7b91996a27e57ee3b524b1e3e398443d443f52808b0cdce19
  claim_mapping:
    theorem_names: [rawReindexUpper_id, rawReindexUpper_comp, rawReindexUpper_cancel, exactSourceGeometry_raw_forward, refinementSourceGeometry_raw_forward, exactSupportReads, exactAxisReads, exactObservableReads]
    source_labels: [target theorem clause (b), material premise G-115-local geometry cleavage]
    conjuncts: [HGeom-free source geometry generation, coefficient-ring retention, exact/refinement strict raw roundtrip, exact realization carrier and reading preservation]
    undischarged_assumptions: [refinement realization carrier and reading preservation, exact/refinement support/axis/observable restriction naturality, total geometry hom, all later revision-3 artifacts]
    acceptance_point: This is a data and reading checkpoint only; it does not construct UpperGeometryCleavage or discharge O10.
    port_status: not-applicable
audits:
  premise_delta:
    ambient_boundary: [G-112 explicit exact upper pair, G-114 realized-refinement transport, RealizedLocusExtractionReflecting r as a generic helper input; active ctx.condition specialization remains pending]
    direction_hypothesis: []
    discharged: [exact/refinement source geometry package generation relative to their reviewed inputs, exact/refinement strict raw equality, exact support/axis/observable carrier comparison and reading preservation]
    remaining: [refinement support/axis/observable carrier comparison and reading preservation, exact/refinement restriction naturality, total geometry hom, geometry cleavage and mate comparison, named problems, clauses (c)--(d)]
  certificate_provenance:
    discharged: [exact source package and raw equality generated from the explicit upper pair; refinement source package and raw equality generated from r plus the reviewed realized-locus condition]
    unresolved: [complete realization transport and downstream comparison]
  proof_use:
    used: [inverseCorePackageBackward_comp_forward, SelectedRefinementTransport.inverseCorePackageBackward_comp_forward, realized-reflection selected transport data, explicit carrier preservation]
    unused: [the readable-morphism computation route required for restriction naturality is not yet identified or connected through the explicit source-reading cast]
  structure_field_escape: no caller HGeom, completed geometry lift, or naturality field was added; the refinement condition is a reviewed ambient input, not a conclusion certificate
  route_integrity: exact/refinement source cores and raw systems are definitionally generated from reviewed explicit lifts relative to their fixed inputs
  target_fitting: no target-chosen cleavage or opaque comparison
  vacuity: not yet applicable before named fixtures
  one_way_as_equivalence: not claimed
  goal_or_report_reinterpretation: none
  validation_refs: [research/lean/check_research_modules.sh --focused ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCleavage.lean => exit 0 and 12 declarations standard axioms only; research/lean/check_research_modules.sh --focused ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCleavageRealization.lean => exit 0 and 7 declarations standard axioms only; git diff --check 79fcc84a3c651edccc286ea1b55873cfc13f6749..ab7c5131513e82e265f1084dce2d1b4a07976151 => exit 0; rg -nP "[\\x{200B}-\\x{200F}\\x{202A}-\\x{202E}\\x{2066}-\\x{2069}]" research/lean/ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCleavage.lean research/lean/ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCleavageRealization.lean research/lean/ResearchLean/AG/DoctrineFiberProduct.lean research/lean/research-modules.txt research/reports/G-115-aat-upper-stage-lift.md => exit 1/no matches; rg -n "\\b(sorry|admit|unsafe|axiom)\\b" research/lean/ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCleavage.lean research/lean/ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCleavageRealization.lean => exit 1/no matches]
  blocking_findings: [the readable-morphism computation declarations required by RefinementGeomReadHom naturality are not yet identified or connected through the public inverse-package/source-reading interface]
  next_obligation: Prove G-115-local source-reading-cast naturality without predecessor edits; if the same API blocker persists, record target-blocked with the exact missing declarations or missing public route.
```

The raw obstruction was discharged without inventing a lower inverse. The
G-115-local `rawReindexUpper` uses only the complete upper equivalence, and its
identity/composition laws reduce both explicit roundtrips to strict raw-system
equalities. Exact-branch realization carrier casts and reading preservation are
also generated locally. The remaining undischarged obligation is fixed by the
current declaration surface: the completed predecessor exposes objectwise
carrier equalities, while the readable-morphism computation route needed for
naturality has not yet been identified or connected through the public API. The
refinement realization comparisons remain a separate undischarged obligation.
No naturality field or `HGeom` certificate was added to bypass either gap.

## Cycle 8 — G-115-local exact restriction naturality

```yaml
ledger_type: target_cycle_result
goal: G-115-aat-upper-stage-lift
cycle: 8
goal_blob_sha: 3c7dd5c34934205817b88d39c00d53b116fbb8f9
base_oid: 99ed49cacde78dfda5ab1f4168aba213a78c310b
tracking_issue: 4250
report_path: research/reports/G-115-aat-upper-stage-lift.md
selection:
  proof_state_ref: Cycle 7 merged checkpoint and revision 3 K2b2a
  proof_dag_predecessors: [Cycle 7 source geometry pullback, inverseCoreEquationForward, deconjugateEquationSystemExact]
  proof_obligation: Construct the missing exact support/axis/observable restriction-naturality API inside G-115 without changing completed predecessor modules.
  selection_reason: Exact restriction naturality is the shortest remaining step from the Cycle 7 carrier/read data to an exact geometry hom.
  expected_result_type: proof-obligation-discharged
  lean_targets: [ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCleavageNaturality.lean]
  risks: [dependent source-reading cast, contravariant observable direction, certificate escape]
  unchecked: [refinement realization and naturality, exact coverage and overlap packaging, total geometry hom, downstream cleavage and comparisons]
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: A G-115-local source-reading-cast computation route now generates exact support, axis, and observable comparisons together with their reading-preservation and restriction-naturality laws.
  completion_candidate: no
  lean_artifacts: [inverseCoreEquationForward_eq_geometryCast, generatedExactSupportComp, generatedExactSupportComp_naturality, generatedExactAxisComp, generatedExactAxisComp_naturality, generatedExactObservableComp, generatedExactObservableComp_naturality, generatedExactSupportComp_reads, generatedExactAxisComp_reads, generatedExactObservableComp_reads]
  evidence: [focused Lean check, namespace standard-axiom audit, source hash, literal scans]
  source_sha256:
    UpperGeometryCleavageNaturality.lean: 582126fedb8a1c2ede30ed41e37c94958597ae27b5398d47a412f0ea276e76b3
  claim_mapping:
    theorem_names: [generatedExactSupportComp_naturality, generatedExactAxisComp_naturality, generatedExactObservableComp_naturality, generatedExactSupportComp_reads, generatedExactAxisComp_reads, generatedExactObservableComp_reads]
    source_labels: [target theorem clause (b), K2b2a exact branch]
    conjuncts: [exact realization carrier comparison, exact reading preservation, exact restriction naturality]
    undischarged_assumptions: [refinement realization and naturality, exact coverage and overlap packaging, all later revision-3 artifacts]
    acceptance_point: The exact restriction-naturality obligation is discharged; this cycle does not claim a complete geometry hom or O10.
    port_status: not-applicable
audits:
  premise_delta:
    ambient_boundary: [G-112 explicit exact upper pair]
    direction_hypothesis: []
    discharged: [exact support/axis/observable restriction naturality generated from the explicit upper construction]
    remaining: [refinement realization and naturality, coverage and overlap packaging, geometry cleavage and mate comparison, named problems, clauses (c)--(d)]
  certificate_provenance:
    discharged: [source-reading cast computation and deconjugate context transport are constructed in G-115]
    unresolved: [refinement realization and downstream comparison]
  proof_use:
    used: [inverseCoreEquationForward, deconjugateEquationSystemExact, transport context equivalence, source-reading equality]
    unused: []
  structure_field_escape: no supplied realization, naturality, or HGeom field
  route_integrity: the comparisons and naturality laws are generated from the exact upper equation transport and its explicit source cast
  target_fitting: none-found
  vacuity: not yet applicable before named fixtures
  one_way_as_equivalence: not claimed
  goal_or_report_reinterpretation: none
  validation_refs: [research/lean/check_research_modules.sh --focused ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCleavageNaturality.lean => exit 0 and 10 declarations standard axioms only; git diff --check => exit 0; rg -n "\\b(axiom|admit|sorry|unsafe)\\b" research/lean/ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCleavageNaturality.lean => exit 1/no matches]
  blocking_findings: []
  next_obligation: Generate the refinement realization and restriction-naturality route locally in G-115, then package coverage, overlap, and total geometry homs.
```

The Cycle 7 API gap was resolved in the current GOAL.  The new source-cast
computation layer is local to G-115 and leaves G-112 and G-114 unchanged.  It
proves all three exact restriction squares from the constructed equation
transport, including the contravariant observable square, while retaining the
separate reading-preservation laws.  Refinement realization and packaging into
the complete geometry morphism remain unimplemented.

## Cycle 9 — generated exact/refinement geometry cleavage

```yaml
ledger_type: target_cycle_result
goal: G-115-aat-upper-stage-lift
cycle: 9
goal_blob_sha: 3c7dd5c34934205817b88d39c00d53b116fbb8f9
base_oid: e812075ab2939059c01b9a99bd76828c5e8f921e
tracking_issue: 4250
report_path: research/reports/G-115-aat-upper-stage-lift.md
selection:
  proof_state_ref: Cycle 8 merged checkpoint and revision 3 K2b2a
  proof_dag_predecessors: [Cycle 7 source geometry pullback, Cycle 8 exact deconjugation naturality, selectedTransportDataOfRealizedReflection]
  proof_obligation: Generate the realized-refinement comparison and restriction laws locally, then package both explicit pullbacks as complete geometry morphisms.
  selection_reason: This closes the remaining G-115-local cleavage fields before the route-mate comparison is constructed.
  expected_result_type: proof-obligation-discharged
  lean_targets: [ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCleavageNaturality.lean]
  risks: [caller-supplied realization escape, overlap roundtrip, observable direction, retrospective predecessor edits]
  unchecked: [geometry route mate and universal-uniqueness comparison, named finite problem and solution, clauses (c)--(d)]
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: The exact and realized-refinement pullbacks now generate coverage, overlap, coefficient identity, raw equality, all three geometry comparisons, reading laws, restriction naturality, and total geometry homs.
  completion_candidate: no
  lean_artifacts: [selectedInverseCoreEquationForward_eq_geometryCast, generatedRefinementSupportComp, generatedRefinementAxisComp, generatedRefinementObservableComp, generatedRefinementSupportComp_naturality, generatedRefinementAxisComp_naturality, generatedRefinementObservableComp_naturality, generatedRefinementSupportComp_reads, generatedRefinementAxisComp_reads, generatedRefinementObservableComp_reads, generatedExactCoverage, generatedExactOverlap, generatedExactGeometryHom, generatedRefinementCoverage, generatedRefinementOverlap, generatedRefinementGeometryHom]
  evidence: [focused Lean check, namespace standard-axiom audit, source hash, literal scans]
  source_sha256:
    UpperGeometryCleavageNaturality.lean: 9f72c54ce55efb05d7ebf1abb4518ffc314a2c6bba59d65be2f454a7b2535378
  claim_mapping:
    theorem_names: [generatedExactGeometryHom, generatedRefinementGeometryHom, generatedExactGeometryHom_base, generatedRefinementGeometryHom_base]
    source_labels: [target theorem clause (b), K2b2a exact/refinement cleavage]
    conjuncts: [exact geometry hom, realized-refinement geometry hom, coverage, overlap, coefficient identity, raw equality, support/axis/observable realization and naturality]
    undischarged_assumptions: [geometry route mate and generated comparison square, named problems and solutions, clauses (c)--(d)]
    acceptance_point: The G-115-local cleavage is complete relative to its reviewed explicit exact and realized-refinement inputs; this cycle does not claim the route mate or O10.
    port_status: not-applicable
audits:
  premise_delta:
    ambient_boundary: [G-112 explicit exact upper pair, G-114 realized-refinement transport, RealizedLocusExtractionReflecting r]
    direction_hypothesis: []
    discharged: [exact and refinement geometry realization, restriction naturality, coverage and overlap packaging, coefficient identity, total geometry hom construction]
    remaining: [geometry mate comparison and universal-uniqueness square, named finite problems and solutions, clauses (c)--(d)]
  certificate_provenance:
    discharged: [all geometry fields are generated from the explicit upper equivalences and pulled target geometry]
    unresolved: [route-level mate and downstream solution artifacts]
  proof_use:
    used: [exact and selected inverseCoreEquationForward, deconjugateEquationSystemExact, context forward/backward object computations, pullback overlap, raw roundtrip equalities]
    unused: []
  structure_field_escape: no supplied HGeom, completed geometry hom, comparison, reading, or naturality certificate
  route_integrity: exact base is inverseCorePackageHom; refinement base retains the actual PointedRefinementHom and selected realized-refinement upper map
  target_fitting: none-found
  vacuity: not yet applicable before named fixtures
  one_way_as_equivalence: not claimed
  goal_or_report_reinterpretation: none
  validation_refs: [research/lean/check_research_modules.sh --focused ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCleavageNaturality.lean => exit 0 and 34 declarations standard axioms only; git diff --check => exit 0; rg placeholder and hidden/BiDi scans => no matches]
  blocking_findings: []
  next_obligation: Generate the two geometry-compatible reverse routes and the upper geometry mate comparison from the completed local cleavage and G-114 actual route.
```

Cycle 9 follows the forward-only rule for completed work: G-112 and G-114 are
unchanged. The missing refinement geometry API is constructed in G-115 from the
realized-reflection data, and the exact/refinement branches are packaged as
actual geometry morphisms rather than accepted as caller certificates.

## Cycle 10 — actual geometry-compatible reverse routes

```yaml
ledger_type: target_cycle_result
goal: G-115-aat-upper-stage-lift
cycle: 10
goal_blob_sha: 3c7dd5c34934205817b88d39c00d53b116fbb8f9
base_oid: e35e42ce1d14998480c9e1cdde02ab58d45c360e
tracking_issue: 4250
selection:
  proof_state_ref: Cycle 9 merged geometry cleavage
  proof_obligation: Apply the generated exact/refinement cleavage to both reverse orders of the actual G-114 context without drifting to a parallel target package.
  expected_result_type: proof-obligation-discharged
  lean_targets: [ResearchLean/AG/DoctrineFiberProduct/UpperGeometryRoutes.lean]
  unchecked: [upperGeometryMate, universal-uniqueness comparison with ctx.mate, geometry-level comparison, named problems and solutions, clauses (c)--(d)]
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: The actual base-first and pulled-first geometry packages, their four generated legs, and their two composite refinement-geometry routes now exist over the fixed active context.
  completion_candidate: no
  lean_artifacts: [UpperGeometryCleavage.TargetGeometry, baseRefinementGeometry, baseRouteGeometry, pullbackTargetGeometry, pulledRouteGeometry, baseRefinementGeometryHom, baseRouteExactGeometryHom, pullbackTargetGeometryHom, pulledRefinementGeometryHom, baseRouteGeometryHom, pulledRouteGeometryHom, baseRouteCoreFiber, pulledRouteCoreFiber]
  evidence: [focused Lean check, namespace standard-axiom audit, source hash, literal scans]
  source_sha256:
    UpperGeometryRoutes.lean: 4d3d99e8178deee4874542bbb00d0871299a6225cdd33c84847b9a25bad12716
  claim_mapping:
    source_labels: [target theorem clause (b), K2b2a actual reverse routes]
    conjuncts: [actual target-package anchoring, base-first route, pulled-first route, exact/refinement leg provenance, common mixed-pullback fiber]
    undischarged_assumptions: [mate and comparison artifacts, named problem/solution, clauses (c)--(d)]
    acceptance_point: Both geometry-compatible routes are generated from ctx and its fixed target geometry; the route-between comparison is not yet claimed.
audits:
  premise_delta:
    ambient_boundary: [ActiveRefinementBCContext ctx, geometry on ctx.targetPackage]
    direction_hypothesis: []
    discharged: [two actual geometry route objects, four route legs, two composite route homs, common-fiber endpoint equations]
    remaining: [upperGeometryMate and G-114 mate comparison, downstream named artifacts]
  certificate_provenance:
    discharged: [every route leg comes from Cycle 9 generated cleavage]
    unresolved: [route-between comparison]
  proof_use:
    used: [ctx base and pulled refinements, ctx.condition, pulledRealizedReflection, actual pullbackFst and pulledFst, exact and refinement generated geometry homs]
    unused: []
  structure_field_escape: TargetGeometry carries only geometry and literal core equality to ctx.targetPackage; no route, mate, or comparison certificate
  route_integrity: both endpoints are proved to lie in ctx.configuration.pullbackSourceAt ctx.source and all legs retain their actual exact/lax lower arrows
  target_fitting: none-found
  goal_or_report_reinterpretation: none
  validation_refs: [research/lean/check_research_modules.sh --focused ResearchLean/AG/DoctrineFiberProduct/UpperGeometryRoutes.lean => exit 0 and 33 declarations standard axioms only; git diff --check => exit 0; placeholder and hidden/BiDi scans => no matches]
  blocking_findings: []
  next_obligation: Construct universal-uniqueness endpoint comparison isos and upperGeometryMate, then prove the separate square with ctx.mateAtTarget.
```

The target geometry is indexed by the actual `ctx.targetPackage`, not merely by
an equal pointed endpoint. Both generated route cores are separately proved to
belong to the actual mixed pullback fiber. G-112 and G-114 remain unchanged.

## Cycle 11 — universal refinement-package comparison of the geometry routes

```yaml
ledger_type: target_cycle_result
goal: G-115-aat-upper-stage-lift
cycle: 11
goal_blob_sha: 3c7dd5c34934205817b88d39c00d53b116fbb8f9
base_oid: 77334f7b7f58de859b3b9346661a809404540604
tracking_issue: 4250
report_path: research/reports/G-115-aat-upper-stage-lift.md
selection:
  proof_state_ref: Cycle 10 merged actual geometry-compatible reverse routes
  proof_obligation: Prove both literal route bases strongly cartesian, identify their lower paths from the actual pullback square, and generate their complete-upper comparison by universal uniqueness.
  expected_result_type: proof-obligation-discharged
  lean_targets: [ResearchLean/AG/DoctrineFiberProduct/UpperGeometryMate.lean]
  unchecked: [exact core-fiber packaging of the generated comparison, comparison square with ctx.mateAtTarget, geometry-level upperGeometryMate, named problems and solutions, clauses (c)--(d)]
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: Exact and realized-refinement geometry legs are strongly cartesian from their generated upper inverses; both literal route composites inherit strong cartesianness; both endpoint-cast lower triangles follow from pulled_square_commutes_at; the G-114-direction route comparison, its inverse-direction companion, and both full package factor triangles are generated by the two cartesian universal properties.
  completion_candidate: no
  lean_artifacts: [exactGeometryBase_isStronglyCartesian, refinementGeometryBase_isStronglyCartesian, baseRouteGeometryBase_isStronglyCartesian, pulledRouteGeometryBase_isStronglyCartesian, refinementSourceGeometry_packagePoint_eq_source, refinementBaseHom_base_eq_casts, routeSourceBase, routeSourceForward, routeSourceForward_comp_base, routeSourceBase_fac, routeSourceForward_fac, generatedRouteRefinementMateInverse, generatedRouteRefinementMateInverse_fac, generatedRouteRefinementMate, generatedRouteRefinementMate_fac]
  evidence: [focused Lean check, namespace standard-axiom audit, source hash, literal scans]
  source_sha256:
    UpperGeometryMate.lean: 73baf52db113397dd89cd46033babbf2a8e40eaf8dfe502fd5ecd0c80e5605eb
  claim_mapping:
    source_labels: [target theorem clause (b), K2b2a universal route comparison]
    conjuncts: [generated strong-cartesian route bases, actual lower-square identification in both directions, G-114-direction universal complete-upper factor triangle, inverse-direction companion triangle]
    undischarged_assumptions: [exact core-fiber mate packaging, G-114 universal comparison square, geometry-level comparison and downstream artifacts]
    acceptance_point: The comparison in the lax refinement-package category is generated rather than supplied; this cycle does not yet claim upperGeometryMate.
audits:
  premise_delta:
    ambient_boundary: [Cycle 10 route geometry homs, explicit exact upper inverses, realized-refinement selected upper inverses, current pulled square]
    direction_hypothesis: []
    discharged: [strong cartesianness of both route bases, equality-transported lower factor laws in both directions, universal refinement-package mate in the G-114 direction and inverse companion with factor triangles]
    remaining: [exact core and geometry comparison packaging, comparison with G-114 mate, downstream named contracts]
  certificate_provenance:
    discharged: [all cartesian witnesses come from generated two-sided upper inverses; both comparison directions come from IsStronglyCartesian.map]
    unresolved: [geometry fields on the generated comparison and comparison with ctx.mateAtTarget]
  proof_use:
    used: [inverseCorePackageForward_comp_backward, inverseCorePackageBackward_comp_forward, selected refinement inverse laws, IsStronglyCartesian.comp, pulled_square_commutes_at, endpoint transport cancellation, IsStronglyCartesian.map, IsStronglyCartesian.fac]
    unused: []
  structure_field_escape: no inverse, cartesian witness, lower-square equality, or comparison is accepted as problem data
  route_integrity: the lower triangle retains both actual Cycle 10 route projections and discharges only their endpoint transports before using the current configuration square
  target_fitting: none-found
  goal_or_report_reinterpretation: none
  validation_refs: [research/lean/check_research_modules.sh --focused ResearchLean/AG/DoctrineFiberProduct/UpperGeometryMate.lean => exit 0 and 15 declarations standard axioms only; git diff --check => exit 0; placeholder and hidden/BiDi scans => no matches]
  blocking_findings: []
  next_obligation: Package the generated comparison as the exact vertical core mate, compare it separately with ctx.mateAtTarget by universal uniqueness, then lift it to the geometry-level upperGeometryMate.
```

Cycle 11 adds the missing API only in G-115. Completed G-112 and G-114 files
remain untouched and serve solely as inputs and the later comparison target.

## Cycle 12 — exact vertical packaging and uniqueness surface

```yaml
ledger_type: target_cycle_result
goal: G-115-aat-upper-stage-lift
cycle: 12
goal_blob_sha: 3c7dd5c34934205817b88d39c00d53b116fbb8f9
base_oid: c55bb13126ca2a09b1943b303e15fffc4cda0169
tracking_issue: 4250
report_path: research/reports/G-115-aat-upper-stage-lift.md
selection:
  proof_state_ref: Cycle 11 merged universal refinement-package comparison
  proof_obligation: Package the generated comparison as an exact vertical morphism in the actual mixed-pullback core fiber and expose the uniqueness theorem needed for the separate G-114 mate comparison.
  expected_result_type: proof-obligation-discharged
  lean_targets: [ResearchLean/AG/DoctrineFiberProduct/UpperGeometryMate.lean]
  unchecked: [route-domain comparison isos with G-114 selected lift domains, comparison square with ctx.mateAtTarget, geometry-level upperGeometryMate, named problems and solutions, clauses (c)--(d)]
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: The universally generated lax-package comparison is proved to lie over the exact endpoint transport, packaged as a vertical CoreFiber morphism, recovered exactly by the exact-to-refinement embedding, and characterized by the pulled-route universal property.
  completion_candidate: no
  lean_artifacts: [generatedRouteRefinementMate_isHomLift, generatedRouteRefinementMate_base, generatedRouteCoreMate, generatedRouteCoreMate_toRefinement, generatedRouteRefinementMate_unique]
  evidence: [focused Lean check, namespace standard-axiom audit, source hash, literal scans]
  source_sha256:
    UpperGeometryMate.lean: 1354aab13db906b5f9f32120d8ed20694d14d2b8713d6471f1ef75aed69735bf
  claim_mapping:
    source_labels: [target theorem clause (b), K2b2a exact core mate packaging]
    conjuncts: [exact lower provenance, vertical CoreFiber membership, faithful exact embedding recovery, universal uniqueness]
    undischarged_assumptions: [G-114 selected-domain bridge isos, G-114 mate comparison square, geometry-level comparison and downstream artifacts]
    acceptance_point: The local route mate is now an exact core-fiber morphism; it is not identified with the differently typed G-114 selected-domain mate by endpoint casts.
audits:
  premise_delta:
    ambient_boundary: [Cycle 11 generated comparison and factor triangle, actual mixed-pullback endpoint equations]
    direction_hypothesis: []
    discharged: [exact endpoint lower map, vertical core-fiber packaging, embedding recovery, uniqueness among comparisons with the same lower map and route triangle]
    remaining: [universal route-domain bridges and G-114 mate square, geometry lift, downstream named contracts]
  certificate_provenance:
    discharged: [the exact mate upper is the generated universal comparison upper; its lower exactness follows from the generated IsHomLift equation]
    unresolved: [comparison with G-114 selected lift domains and geometry fields]
  proof_use:
    used: [IsStronglyCartesian.map_isHomLift, IsHomLift.fac, exact endpoint equations, exactPackageToRefinement, IsStronglyCartesian.map_uniq]
    unused: []
  structure_field_escape: no exact mate, lower identity, factor triangle, or uniqueness certificate is accepted as input
  route_integrity: exact embedding recovers the full generated refinement-package comparison, not only its upper field
  target_fitting: none-found
  goal_or_report_reinterpretation: none
  validation_refs: [research/lean/check_research_modules.sh --focused ResearchLean/AG/DoctrineFiberProduct/UpperGeometryMate.lean => exit 0 and 20 declarations standard axioms only; git diff --check => exit 0; placeholder scan => no matches]
  blocking_findings: []
  next_obligation: Construct G-115-local universal route-domain bridge isos to the G-114 selected lift domains, then prove the lower and upper parts of the mate comparison square separately.
```

Cycle 12 does not equate the generated route cores with the G-114 selected
domains. Those endpoints arise from different universal choices, so their
comparison must be generated as isomorphisms in the current G-115 rather than
forced by equality or by editing the completed predecessor GOALs.

## Cycle 13 — base-route universal domain bridge

```yaml
ledger_type: target_cycle_result
goal: G-115-aat-upper-stage-lift
cycle: 13
goal_blob_sha: 3c7dd5c34934205817b88d39c00d53b116fbb8f9
base_oid: dbeaf48f5c031965c6dc1500af817c36fc587178
tracking_issue: 4250
report_path: research/reports/G-115-aat-upper-stage-lift.md
selection:
  proof_state_ref: Cycle 12 merged exact vertical route mate
  proof_obligation: Compare the explicit base-first geometry route domain with the independently selected G-114 base mate domain by universal uniqueness, without endpoint-equality substitution for the selected objects.
  expected_result_type: proof-obligation-discharged
  lean_targets: [ResearchLean/AG/DoctrineFiberProduct/UpperGeometryMateComparison.lean]
  unchecked: [pulled-route domain bridge, full base and pulled composite triangles, comparison square with ctx.mateAtTarget, geometry-level upperGeometryMate, named problems and solutions, clauses (c)--(d)]
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: The chosen target core and intermediate refinement package are anchored to the retargeted active context; the explicit and G-112-selected exact lift domains are connected by the canonical cartesian domain isomorphism with both factor triangles; this yields the actual base-route-to-base-mate endpoint iso.
  completion_candidate: no
  lean_artifacts: [targetCoreFiber, retargetedContext, baseRefinementCoreFiber, refinementSourceGeometry_core_eq_refinementLiftDomain, baseRefinementCoreFiber_eq_legacy, selectedBaseExactLift, explicitBaseExactLift, baseRouteCoreFiber_eq_explicit, selectedBaseExactLift_domain_eq_baseMate, baseRouteSelectedDomainIso, baseRouteSelectedDomainIso_hom_fac, baseRouteSelectedDomainIso_inv_fac, baseRouteBaseMateIso]
  evidence: [focused Lean check, namespace standard-axiom audit, source hash, literal scans]
  source_sha256:
    UpperGeometryMateComparison.lean: b2a62253e12ed8d3c7efd25014f5852f3ea54a7925917c8bb979a78617a75e44
  claim_mapping:
    source_labels: [target theorem clause (b), K2b2a componentwise comparison iso]
    conjuncts: [actual target-core anchoring, explicit-to-public refinement-domain coherence, explicit-versus-selected exact universal iso, forward and inverse exact factor graphs, retargeted G-114 endpoint comparison]
    undischarged_assumptions: [pulled-route universal bridge, complete route comparison square, geometry-level comparison and downstream artifacts]
    acceptance_point: The base endpoint comparison is generated from cartesian uniqueness; equality is used only to normalize proven representations before assembling the iso.
audits:
  premise_delta:
    ambient_boundary: [Cycle 12 explicit route core, G-112 selected exact lift, G-114 retarget and legacy-domain coherence]
    direction_hypothesis: []
    discharged: [base intermediate package coherence, base explicit/selected domain iso, both exact-lift factor triangles, actual base endpoint iso]
    remaining: [pulled endpoint iso, full route triangles and mate square, geometry lift, downstream named contracts]
  certificate_provenance:
    discharged: [base comparison comes from StrongCartesianLift.domainIso and its generated HomLift witnesses]
    unresolved: [pulled refinement comparison and route-level mate square]
  proof_use:
    used: [legacyRefinementLift_domain_coherence, StrongCartesianLift.domainIso, domainIso_hom_fac, domainIso_inv_fac, domainIso hom and inverse IsHomLift]
    unused: []
  structure_field_escape: no domain comparison, endpoint iso, or factor triangle is supplied by the caller
  route_integrity: the selected endpoint is the retargeted G-114 baseMatePackage and the explicit endpoint is the actual Cycle 10 baseRouteCoreFiber
  target_fitting: none-found
  goal_or_report_reinterpretation: none
  validation_refs: [research/lean/check_research_modules.sh --focused ResearchLean/AG/DoctrineFiberProduct/UpperGeometryMateComparison.lean => exit 0 and 13 declarations standard axioms only; git diff --check => exit 0; placeholder scan => no matches]
  blocking_findings: []
  next_obligation: Construct the pulled-route domain bridge using exact-domain comparison followed by refinement universal uniqueness, then prove both complete route triangles.
```

Cycle 13 uses the completed G-112 and G-114 APIs only as immutable inputs. The
fact that two universal choices have isomorphic domains is represented by the
generated isomorphism itself; it is not collapsed into an endpoint cast.

## Cycle 14 — pulled-route universal domain bridge

```yaml
ledger_type: target_cycle_result
goal: G-115-aat-upper-stage-lift
cycle: 14
goal_blob_sha: 3c7dd5c34934205817b88d39c00d53b116fbb8f9
base_oid: 068b357e40d91d606fa21a4cd440b3f4e5d3313d
tracking_issue: 4250
report_path: research/reports/G-115-aat-upper-stage-lift.md
selection:
  proof_state_ref: Cycle 13 merged base-route universal domain bridge
  proof_obligation: Compare the explicit pulled-first geometry route with the independently selected G-114 pulled mate domain, accounting for both the exact pullback-target choice and the refinement-lift choice by universal uniqueness.
  expected_result_type: proof-obligation-discharged
  lean_targets: [ResearchLean/AG/DoctrineFiberProduct/UpperGeometryMateComparison.lean]
  unchecked: [full base and pulled composite triangles, comparison square with ctx.mateAtTarget, geometry-level upperGeometryMate, named problems and solutions, clauses (c)--(d)]
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: The explicit and selected pullback-target exact lift domains are compared by the canonical cartesian domain isomorphism with both exact factor triangles; after transporting the explicit realized-refinement lift along that target iso, refinement cartesian uniqueness generates mutually inverse source comparisons and both transported factor triangles; these assemble the actual pulled-route-to-pulled-mate endpoint iso.
  completion_candidate: no
  lean_artifacts: [pullbackTargetCoreFiber, selectedPullbackExactLift, explicitPullbackExactLift, pullbackTargetCoreFiber_eq_explicit, selectedPullbackExactLift_domain_eq_target, pullbackTargetSelectedDomainIso, pullbackTargetSelectedDomainIso_hom_fac, pullbackTargetSelectedDomainIso_inv_fac, pullbackTargetPackageIso, explicitPulledRefinementLift, pulledRouteCoreFiber_eq_explicit, explicitPulledLegacyLift, explicitPulledRefinementLift_domain_eq_legacy, pulledLegacyDomainComparisonHom, pulledLegacyDomainComparisonInv, pulledLegacyDomainComparisonHom_fac, pulledLegacyDomainComparisonInv_fac, pulledLegacyDomainIso, pulledRouteCoreFiber_eq_legacy, pulledRoutePulledMateIso]
  evidence: [focused Lean check, namespace standard-axiom audit, source hash, literal scans]
  source_sha256:
    UpperGeometryMateComparison.lean: 814ae593945e43e1ef0bcbd7f4519a92d3e48b974418d480541d74b44e581713
  claim_mapping:
    source_labels: [target theorem clause (b), K2b2a componentwise comparison iso]
    conjuncts: [explicit-versus-selected pullback-target exact iso, both exact factor triangles, target-transported refinement comparison, both refinement factor triangles, inverse laws from refinement cartesian uniqueness, retargeted G-114 pulled endpoint comparison]
    undischarged_assumptions: [complete base and pulled route triangles, G-114 mate comparison square, geometry-level comparison and downstream artifacts]
    acceptance_point: Both changes of universal choice on the pulled route are represented by generated isomorphisms; equality is used only for proved representation normalization at the explicit route endpoint.
audits:
  premise_delta:
    ambient_boundary: [Cycle 13 target anchoring, G-112 selected exact lift, G-114 legacy pulled cleavage, realized-refinement domain coherence]
    direction_hypothesis: []
    discharged: [pullback-target exact domain iso and both factor triangles, target-transported refinement source iso and both factor triangles, actual pulled endpoint iso]
    remaining: [full route triangles and mate square, geometry lift, downstream named contracts]
  certificate_provenance:
    discharged: [exact comparison comes from StrongCartesianLift.domainIso; refinement comparison and inverse laws come from the two LegacyRefinementCartesianLift universal properties]
    unresolved: [route-level mate square and geometry fields]
  proof_use:
    used: [StrongCartesianLift.domainIso, domainIso_hom_fac, domainIso_inv_fac, legacyRefinementLift_domain_coherence, RefinementOverHom precomp and postcomp laws, LegacyRefinementCartesianLift.factor_fac, factor_unique]
    unused: []
  structure_field_escape: no exact-domain comparison, refinement-domain comparison, inverse law, endpoint iso, or factor triangle is accepted from the caller
  route_integrity: the explicit endpoint is the actual Cycle 10 pulledRouteCoreFiber and the selected endpoint is the retargeted G-114 pulledMatePackage; the intervening target transport is the exact-lift uniqueness iso
  target_fitting: none-found
  goal_or_report_reinterpretation: none
  validation_refs: [research/lean/check_research_modules.sh --focused ResearchLean/AG/DoctrineFiberProduct/UpperGeometryMateComparison.lean => exit 0 and 33 declarations standard axioms only; git diff --check => exit 0; placeholder scan => no matches]
  blocking_findings: []
  next_obligation: Use the two endpoint bridge isos and their factor triangles to prove the complete base and pulled route comparisons, then prove the generated mate square against the retargeted G-114 mate.
```

Cycle 14 again adds the missing comparison surface only in G-115. Completed
G-112 and G-114 remain unchanged and are consumed solely through their exported
universal properties.

## Cycle 15 — cartesian qualification of the retargeted G-114 routes

```yaml
ledger_type: target_cycle_result
goal: G-115-aat-upper-stage-lift
cycle: 15
goal_blob_sha: 3c7dd5c34934205817b88d39c00d53b116fbb8f9
base_oid: 0344608378315331d3e764df4b536c48d7390861
tracking_issue: 4250
report_path: research/reports/G-115-aat-upper-stage-lift.md
selection:
  proof_state_ref: Cycle 14 merged both universal route-domain bridges
  proof_obligation: Qualify the two retargeted G-114 selected composites as strongly cartesian in the G-115 refinement-package projection so the complete route comparison and mate square can be generated by universal uniqueness.
  expected_result_type: proof-obligation-discharged
  lean_targets: [ResearchLean/AG/DoctrineFiberProduct/UpperGeometryMateSquare.lean]
  unchecked: [complete route comparison isos and factor triangles, mate comparison square, geometry-level upperGeometryMate, named problems and solutions, clauses (c)--(d)]
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: A legacy realized-refinement relative lift becomes a strongly cartesian refinement-package morphism from its generated two-sided upper inverse; a G-112-selected exact lift remains strongly cartesian after exact-to-refinement embedding; composition gives strong cartesianness of both actual retargeted G-114 route composites.
  completion_candidate: no
  lean_artifacts: [legacyRefinementPackageLift_isStronglyCartesian, selectedExactRefinementLift_isStronglyCartesian, retargetedBaseComposite_isStronglyCartesian, retargetedPulledComposite_isStronglyCartesian]
  evidence: [focused Lean check, namespace standard-axiom audit, source hash, literal scans]
  source_sha256:
    UpperGeometryMateSquare.lean: deda76820d43754adfb14c6f66f914d6ac296d08b1f858ecb0470d6d277e7e2a
  claim_mapping:
    source_labels: [target theorem clause (b), K2b2a universal mate comparison]
    conjuncts: [legacy refinement upper inverse qualification, selected exact embedding qualification, base composite cartesianness, pulled composite cartesianness]
    undischarged_assumptions: [complete route comparison maps, their factor graphs and inverse laws, G-114 mate square, geometry-level comparison and downstream artifacts]
    acceptance_point: This cycle establishes only the universal-property eligibility needed to generate the comparison; it does not treat endpoint cast normalization or later square assembly as a mathematical finding.
audits:
  premise_delta:
    ambient_boundary: [G-112 selected exact lift upper inverse, G-114 legacy relative lifts, Cycle 14 retargeted endpoints]
    direction_hypothesis: []
    discharged: [strong cartesianness of both selected exact embeddings, both legacy refinement package lifts, and both retargeted G-114 composites]
    remaining: [generated complete-route isos and triangles, mate square, geometry lift, downstream named contracts]
  certificate_provenance:
    discharged: [legacy refinement certificates come from selected transport forward/backward cancellation; exact certificates come from the exported G-112 selected-lift upper inverse; composite certificates come from IsStronglyCartesian.comp]
    unresolved: [route comparison and mate-square uniqueness]
  proof_use:
    used: [SelectedRefinementTransport forward/backward inverse laws, exact_bottom_semantic_global_selected_lift_upperInverse, refinementPackageHom_isStronglyCartesian_of_upper_inverse, IsStronglyCartesian.comp]
    unused: []
  structure_field_escape: no cartesian certificate is added to problem data or accepted from a caller
  route_integrity: the qualified composites are literally the retargeted G-114 baseCompositeLeg and pulledCompositeLeg at the actual G-115 target core
  target_fitting: none-found
  goal_or_report_reinterpretation: none
  validation_refs: [research/lean/check_research_modules.sh --focused ResearchLean/AG/DoctrineFiberProduct/UpperGeometryMateSquare.lean => exit 0 and 4 declarations standard axioms only; git diff --check => exit 0; placeholder scan => no matches]
  blocking_findings: []
  next_obligation: Generate complete route comparison isomorphisms and factor triangles from the newly qualified cartesian composites, then prove their mate square against generatedRouteCoreMate.
```

Cycle 15 supplies a missing G-115-local eligibility theorem, not a retroactive
change to G-112 or G-114. The completed predecessor route definitions remain
unchanged.

## Cycle 16 — complete comparison of generated and selected routes

```yaml
ledger_type: target_cycle_result
goal: G-115-aat-upper-stage-lift
cycle: 16
goal_blob_sha: a11f61a5790c8ac75ce7f13da1277a859e2ab600ac96038bc55c338b80d38985
base_oid: fd65c165135578a7f89c5ed84ec70015793fa0f2
tracking_issue: 4250
report_path: research/reports/G-115-aat-upper-stage-lift.md
selection:
  proof_state_ref: Cycle 15 qualified both actual retargeted G-114 composites as strongly cartesian
  proof_obligation: Compare each geometry-generated route with the corresponding actual retargeted G-114 route by a complete package isomorphism, including lower normalization, both factor triangles, and inverse laws.
  expected_result_type: proof-obligation-discharged
  lean_targets: [ResearchLean/AG/DoctrineFiberProduct/UpperGeometryRouteComparison.lean]
  unchecked: [G-114 mate comparison square, identification with generatedRouteCoreMate, geometry-level upperGeometryMate, named problems and solutions, clauses (c)--(d)]
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: G-115 now exposes exact endpoint transports from each generated route source to its selected G-114 source and back; proves both lower factor laws by normalizing exact and relative lift projections; generates forward and inverse complete package comparisons by strong-cartesian universality; proves both package factor triangles and both inverse laws on the base and pulled routes.
  completion_candidate: no
  lean_artifacts: [exactLiftRefinementBase_eq_casts, refinementPackageHomOfOver_base_eq_casts, baseRouteActualSource, baseRouteActualSource_fac, pulledRouteActualSource, pulledRouteActualSource_fac, baseActualRouteSource, baseActualRouteSource_fac, pulledActualRouteSource, pulledActualRouteSource_fac, baseRouteComparisonHom, baseRouteComparisonInv, baseRouteComparisonIso, pulledRouteComparisonHom, pulledRouteComparisonInv, pulledRouteComparisonIso]
  evidence: [focused Lean check, namespace standard-axiom audit, source hash, literal scans]
  source_sha256:
    UpperGeometryRouteComparison.lean: 83fa9f38a11624d13596aa10fe6c3cd8605f483d16501bdba8f4f254f54ca931
  claim_mapping:
    source_labels: [target theorem clause (b), K2b2a universal mate comparison]
    conjuncts: [base lower normalization, pulled lower normalization, complete forward and inverse comparisons, four factor triangles, four inverse identities]
    undischarged_assumptions: [mate square against the retargeted G-114 mate, exact-core identification, geometry lift, downstream named contracts]
    acceptance_point: The comparison maps and their inverses are generated from cartesian uniqueness. Endpoint cast normalization is an implementation lemma, not a new mathematical finding or caller-supplied certificate.
audits:
  premise_delta:
    ambient_boundary: [Cycle 15 route cartesianness, authored G-114 route composites, geometry-generated route cartesianness]
    direction_hypothesis: []
    discharged: [both lower route factor laws, both complete comparison maps and inverse maps, all four package factor triangles, both route comparison isomorphisms]
    remaining: [mate square and core identification, geometry lift, downstream named contracts]
  certificate_provenance:
    discharged: [comparison maps come from IsStronglyCartesian.map; factor triangles come from IsStronglyCartesian.fac; inverse laws come from IsStronglyCartesian.ext after proved endpoint cancellation]
    unresolved: [mate-square uniqueness and geometry fields]
  proof_use:
    used: [IsHomLift.fac', IsStronglyCartesian.map, IsStronglyCartesian.fac, IsStronglyCartesian.ext, Cycle 15 route cartesianness, generated route cartesianness]
    unused: []
  structure_field_escape: no comparison, inverse, lower factor, or inverse law is accepted from a caller
  route_integrity: the compared selected legs are literally retargetedContext.baseCompositeLeg and pulledCompositeLeg; the generated legs are literally baseRouteGeometryHom.base and pulledRouteGeometryHom.base
  predecessor_integrity: completed G-112 and G-114 files and declarations are unchanged; all missing normalization and comparison APIs are added in G-115
  target_fitting: none-found
  goal_or_report_reinterpretation: none
  validation_refs: [research/lean/check_research_modules.sh --focused ResearchLean/AG/DoctrineFiberProduct/UpperGeometryRouteComparison.lean => exit 0 and 33 declarations standard axioms only; git diff --check => exit 0; placeholder scan => no proof placeholders]
  blocking_findings: []
  next_obligation: Conjugate the retargeted G-114 mate by the two complete route comparison isomorphisms, prove its route triangle, and identify it with generatedRouteRefinementMate and generatedRouteCoreMate by uniqueness.
```

Cycle 16 adds the comparison surface entirely in G-115. Completed G-112 and
G-114 remain fixed and are used only through their exported route and mate
properties.

## Cycle 17 — identification of the generated and G-114 mates

```yaml
ledger_type: target_cycle_result
goal: G-115-aat-upper-stage-lift
cycle: 17
goal_blob_sha: a11f61a5790c8ac75ce7f13da1277a859e2ab600ac96038bc55c338b80d38985
base_oid: df53dceed1cbbcf9b9f1bdf3c940bc7c55a8c60b
tracking_issue: 4250
report_path: research/reports/G-115-aat-upper-stage-lift.md
selection:
  proof_state_ref: Cycle 16 merged complete comparison isomorphisms for both routes
  proof_obligation: Conjugate the retargeted G-114 mate by the route comparisons, prove its complete route triangle, and identify it with the generated refinement and core mates.
  expected_result_type: proof-obligation-discharged
  lean_targets: [ResearchLean/AG/DoctrineFiberProduct/UpperGeometryMateIdentification.lean]
  unchecked: [geometry-level upperGeometryMate, named problem and solution contracts, target clauses (c)--(d), final target assembly]
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: The conjugated G-114 mate has the generated routeSourceForward lower map and the full package route triangle; cartesian uniqueness identifies it with generatedRouteRefinementMate, and exact embedding identifies the resulting square with generatedRouteCoreMate.
  completion_candidate: no
  lean_artifacts: [transportedG114RefinementMate, transportedG114RefinementMate_upper_fac, baseRouteCommonSource, commonSourcePulledRoute, baseRouteComparisonHom_isHomLift_common, pulledRouteComparisonInv_isHomLift_common, transportedG114RefinementMate_isHomLift, transportedG114RefinementMate_fac, transportedG114RefinementMate_eq_generated, generatedRouteRefinementMate_comparison_square, generatedRouteCoreMate_comparison_square]
  evidence: [focused Lean check, namespace standard-axiom audit, source hash, literal scans]
  source_sha256:
    UpperGeometryMateIdentification.lean: f31914166e086e1483cf3ab727026955ea9096d91ca4fc873595e8fc4be5aba4
  claim_mapping:
    source_labels: [target theorem clause (b), K2b2a universal mate comparison]
    conjuncts: [conjugated G-114 mate, normalized lower endpoint transport, complete route triangle, uniqueness identification, exact-core comparison square]
    undischarged_assumptions: [geometry lift, named contracts, clauses (c)--(d), final assembly]
    acceptance_point: Lower equality and upper factorization are proved separately before universal uniqueness is invoked; neither is inferred from the other.
audits:
  premise_delta:
    ambient_boundary: [Cycle 16 comparison isomorphisms, exported G-114 upper triangle, generated route cartesianness]
    direction_hypothesis: []
    discharged: [G-114 mate comparison square, refinement mate identification, embedded core mate comparison square]
    remaining: [geometry lift and downstream target contracts]
  certificate_provenance:
    discharged: [lower HomLift composition is generated from the two comparison lifts and G-114 mate verticality; mate equality comes from generatedRouteRefinementMate_unique]
    unresolved: [geometry-component provenance and downstream assembly]
  proof_use:
    used: [Cycle 16 route comparison factors and inverse laws, refinementMate_upper_triangle, refinementMate_isHomLift, IsHomLift.comp, generatedRouteRefinementMate_unique, generatedRouteCoreMate_toRefinement]
    unused: []
  structure_field_escape: no mate square, lower equality, or triangle is caller data
  route_integrity: the square uses the literal retargeted G-114 refinementMateAtTarget and the literal generatedRouteRefinementMate/generatedRouteCoreMate
  predecessor_integrity: completed G-112 and G-114 remain unchanged
  target_fitting: none-found
  goal_or_report_reinterpretation: none
  validation_refs: [research/lean/check_research_modules.sh --focused ResearchLean/AG/DoctrineFiberProduct/UpperGeometryMateIdentification.lean => exit 0 and 13 declarations standard axioms only; git diff --check => exit 0; placeholder scan => no matches]
  blocking_findings: []
  next_obligation: Lift the identified core mate to the fixed-coefficient geometry level, then instantiate the named upperGeometryProblem and upperGeometrySolution contracts and discharge clauses (c)--(d).
```

Cycle 17 proves the G-115 mate comparison square without reopening any
completed predecessor GOAL.

## Cycle 18 — reversible generated route mate

```yaml
ledger_type: target_cycle_result
goal: G-115-aat-upper-stage-lift
cycle: 18
goal_blob_sha: a11f61a5790c8ac75ce7f13da1277a859e2ab600ac96038bc55c338b80d38985
base_oid: 821765d31f200e2a25d90175c528facb9c96acf3
tracking_issue: 4250
report_path: research/reports/G-115-aat-upper-stage-lift.md
selection:
  proof_state_ref: Cycle 17 identified the generated core mate with the conjugated G-114 mate
  proof_obligation: Supply the missing G-115-local reversible core API needed to attach the explicit geometry transport, without changing completed G-112 or G-114 declarations.
  expected_result_type: proof-obligation-discharged
  lean_targets: [ResearchLean/AG/DoctrineFiberProduct/UpperGeometryMateIso.lean]
  unchecked: [geometry-level upperGeometryMate and triangle, geometry-level comparison naturality, named positive and negative problems, clauses (c)--(d), final target assembly]
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: The universally generated forward and inverse route comparisons are proved mutually inverse as complete refinement-package morphisms; the inverse is separately packaged as an exact vertical core-fiber morphism, exact embedding recovers the complete inverse comparison, and the two exact core mates form a generated isomorphism.
  completion_candidate: no
  lean_artifacts: [routeSourceBase_comp_forward, generatedRouteRefinementMateIso, generatedRouteCoreMateInverse, generatedRouteCoreMateInverse_toRefinement, generatedRouteCoreMateIso]
  evidence: [focused Lean check, namespace standard-axiom audit, source hash, literal scans]
  source_sha256:
    UpperGeometryMateIso.lean: 804a80c30e371bfa75ec89826e21f67e0a02fd3b7295c30d2e8535bda1d58069
  claim_mapping:
    source_labels: [target theorem clause (b), K2b2a geometry-mate construction input]
    conjuncts: [both endpoint cancellation laws, complete refinement-package mate iso, exact inverse core mate, exact-embedding recovery, exact core-fiber mate iso]
    undischarged_assumptions: [explicit support/axis/observable transport for the geometry mate, geometry triangle, downstream named contracts]
    acceptance_point: Reversibility is derived from both route factor triangles and strong-cartesian extensionality; it is not accepted as a caller certificate and does not decide IsIso for the later decision solution component.
audits:
  premise_delta:
    ambient_boundary: [Cycle 17 generated mate identification, both generated route cartesianness and factor triangles]
    direction_hypothesis: []
    discharged: [both refinement-package inverse identities, exact inverse verticality, full exact-embedding recovery, generated core mate isomorphism]
    remaining: [geometry-component construction and triangle, finite-presentation comparison and downstream artifacts]
  certificate_provenance:
    discharged: [inverse identities come from IsStronglyCartesian.ext after proved lower cancellation and route triangles; exact inverse uses the same complete upper map and actual endpoint equality; exact iso identities are reflected through the faithful exact-to-refinement embedding]
    unresolved: [geometry realization comparisons and downstream solution-space equivalence]
  proof_use:
    used: [generatedRouteRefinementMate_fac, generatedRouteRefinementMateInverse_fac, IsStronglyCartesian.ext, IsHomLift.fac', exactPackageToRefinement_map_injective]
    unused: []
  structure_field_escape: no inverse identity, exact inverse, or core isomorphism is supplied by a caller
  route_integrity: both directions connect the literal baseRouteGeometry and pulledRouteGeometry and project to the actual common mixed-pullback endpoint
  predecessor_integrity: completed G-112 and G-114 declarations and GOALs are unchanged; the missing reversible API is created in G-115
  target_fitting: none-found
  goal_or_report_reinterpretation: none
  validation_refs: [research/lean/check_research_modules.sh --focused ResearchLean/AG/DoctrineFiberProduct/UpperGeometryMateIso.lean => exit 0 and 5 declarations standard axioms only; git diff --check => exit 0; placeholder and hidden/BiDi scans => no matches]
  blocking_findings: []
  next_obligation: Construct the explicit geometry comparison from the base-route forward realization maps and pulled-route backward realization maps, identify its core with generatedRouteCoreMate, and prove upperGeometryMate_triangle.
```

Cycle 18 adds the missing reversible construction inside the active G-115
surface. Completed predecessor GOALs remain immutable inputs.

## Cycle 19 — explicit backward realization of the pulled route

```yaml
ledger_type: target_cycle_result
goal: G-115-aat-upper-stage-lift
cycle: 19
goal_blob_sha: a11f61a5790c8ac75ce7f13da1277a859e2ab600ac96038bc55c338b80d38985
base_oid: b9909f60c3af9546f4e58e1bd440e7a6e6c4f3e9
tracking_issue: 4250
report_path: research/reports/G-115-aat-upper-stage-lift.md
selection:
  proof_state_ref: Cycle 18 merged the reversible exact core mate API
  proof_obligation: Generate the pulled route's backward upper realization from its two literal cleavage legs, prove both cancellations, and expose the generated core mate as base-forward followed by pulled-backward transport.
  expected_result_type: proof-obligation-discharged
  lean_targets: [ResearchLean/AG/DoctrineFiberProduct/UpperGeometryMateRealization.lean]
  unchecked: [Support/Axis/Observable backward components, geometry-level upperGeometryMate and triangle, finite-presentation comparison, named problems, clauses (c)--(d)]
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: The selected realized-refinement transport data of the actual pulled route is exposed; its backward upper map is composed with the exact pullback backward upper; both composite cancellation laws are proved from the two constituent inverse laws; the generated exact core mate upper is identified with the literal base-route forward upper followed by this backward realization.
  completion_candidate: no
  lean_artifacts: [pulledRouteTransportData, pulledRouteBackwardUpper, pulledRouteGeometryHom_upper_eq, pulledRouteBackwardUpper_comp_forward, pulledRouteForward_comp_backwardUpper, generatedRouteCoreMate_upper_eq_explicit]
  evidence: [focused Lean check, namespace standard-axiom audit, source hash, literal scans]
  source_sha256:
    UpperGeometryMateRealization.lean: cfcb20c7693f9aba436a5892a64e3f7d94265adee50245684138ed068af47cf7
  claim_mapping:
    source_labels: [target theorem clause (b), K2b2a explicit geometry-mate realization]
    conjuncts: [actual pulled selected transport data, literal backward composite, backward-forward cancellation, forward-backward cancellation, generated mate upper factorization]
    undischarged_assumptions: [carrier-level backward comparisons and their reading/naturality laws, complete geometry triangle, downstream artifacts]
    acceptance_point: The backward map is generated from the exact and realized-refinement inverse cleavages already constructed in G-115; no caller-supplied inverse or geometry certificate is accepted.
audits:
  premise_delta:
    ambient_boundary: [Cycle 18 core mate iso, generated exact and realized-refinement forward/backward inverse laws]
    direction_hypothesis: []
    discharged: [pulled route backward upper provenance, both cancellations, explicit upper factorization of generatedRouteCoreMate]
    remaining: [Support/Axis/Observable backward realization, reads and naturality, geometry triangle and downstream contracts]
  certificate_provenance:
    discharged: [all inverse laws are compositions of the two explicit G-115 cleavage inverse pairs; core upper factorization uses the generated route mate triangle]
    unresolved: [carrier-level comparison maps]
  proof_use:
    used: [inverseCorePackage backward/forward laws, SelectedRefinementTransport backward/forward laws, generatedRouteRefinementMate_fac]
    unused: []
  structure_field_escape: no backward upper map, cancellation law, or upper factorization is caller data
  route_integrity: the construction uses the literal pulledRefinementAt, pullbackTargetExactArrow, pulledRouteGeometryHom, and baseRouteGeometryHom of the active G-115 context
  predecessor_integrity: completed G-112 and G-114 remain unchanged; the absent backward realization API is added to G-115
  target_fitting: none-found
  goal_or_report_reinterpretation: none
  validation_refs: [research/lean/check_research_modules.sh --focused ResearchLean/AG/DoctrineFiberProduct/UpperGeometryMateRealization.lean => exit 0 and 6 declarations standard axioms only; git diff --check => exit 0; placeholder and hidden/BiDi scans => no matches]
  blocking_findings: []
  next_obligation: Construct the backward Support/Axis/Observable comparisons over pulledRouteBackwardUpper, compose them with the base-route forward comparisons, and prove upperGeometryMate_triangle over generatedRouteCoreMate.
```

Cycle 19 creates the missing realization API in G-115 and treats the completed
G-112 and G-114 surfaces only as immutable inputs.
