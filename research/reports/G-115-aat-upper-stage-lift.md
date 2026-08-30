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
  proof_obligation: Construct caller-free geometry source packages and strict raw roundtrips for the explicit exact/refinement lifts, then expose their realization transport.
  selection_reason: Revision 3 places the missing geometry cleavage in G-115 and forbids retrospective predecessor edits or caller-supplied HGeom.
  expected_result_type: target-proof-checkpoint
  lean_targets: [ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCleavage.lean, ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCleavageRealization.lean]
  risks: [strict raw equality, dependent carrier casts, restriction naturality, accidental lower inverse]
  unchecked: [complete exact/refinement geometry hom, generated cleavage, upper geometry mate, G-114 comparison, solution/reselection transport, named artifacts, clauses (c)--(d)]
result:
  proposed_result_type: target-proof-checkpoint
  proof_obligation_delta: The explicit exact/refinement target-to-source geometry packages, upper-only raw reindex algebra, strict forward raw equalities, carrier comparisons, and three reading-preservation laws are constructed. Restriction naturality remains blocked on an unexposed computation law.
  completion_candidate: no
  lean_artifacts: [exactSourceGeometry, exactSourceGeometry_raw_forward, refinementSourceGeometry, refinementBaseHom, refinementSourceGeometry_raw_forward, exactSupportComp, exactAxisComp, exactObservableComp, exactSupportReads, exactAxisReads, exactObservableReads]
  evidence: [two focused Lean checks, namespace standard-axiom audits, source hashes, literal scans]
  source_sha256:
    UpperGeometryCleavage.lean: 6cc5a6f0a781895af34a58ed2ae4bda1be9da28eed43242ab3adcb8ac5742d8e
    UpperGeometryCleavageRealization.lean: 2ca20e5333c0dbb7b91996a27e57ee3b524b1e3e398443d443f52808b0cdce19
  claim_mapping:
    theorem_names: [rawReindexUpper_id, rawReindexUpper_comp, rawReindexUpper_cancel, exactSourceGeometry_raw_forward, refinementSourceGeometry_raw_forward, exactSupportReads, exactAxisReads, exactObservableReads]
    source_labels: [target theorem clause (b), material premise G-115-local geometry cleavage]
    conjuncts: [caller-free source geometry generation, coefficient-ring retention, strict raw roundtrip, realization carrier and reading preservation]
    undischarged_assumptions: [support/axis/observable restriction naturality, total geometry hom, all later revision-3 artifacts]
    acceptance_point: This is a data and reading checkpoint only; it does not construct UpperGeometryCleavage or discharge O10.
    port_status: not-applicable
audits:
  premise_delta:
    discharged: [source geometry package generation, exact/refinement strict raw equality, support/axis/observable carrier comparison and reading preservation]
    remaining: [restriction naturality, total geometry hom, geometry cleavage and mate comparison, named problems, clauses (c)--(d)]
  certificate_provenance:
    discharged: [source packages and raw equalities generated from explicit forward/backward upper maps]
    unresolved: [complete realization transport and downstream comparison]
  proof_use:
    used: [inverseCorePackageBackward_comp_forward, SelectedRefinementTransport.inverseCorePackageBackward_comp_forward, realized-reflection selected transport data, explicit carrier preservation]
    unused: [restriction-morphism computation hidden behind the explicit source-reading cast]
  structure_field_escape: no caller realization or naturality field was added
  route_integrity: exact/refinement source cores and raw systems are definitionally generated from reviewed explicit lifts
  target_fitting: no target-chosen cleavage or opaque comparison
  vacuity: not yet applicable before named fixtures
  one_way_as_equivalence: not claimed
  goal_or_report_reinterpretation: none
  validation_refs: [focused Lean checks for both leaf files; git diff --check; hidden and bidirectional Unicode scan; placeholder scan]
  blocking_findings: [the public inverse-package API exposes context-object carrier equalities but not the support/axis/observable readable-morphism computation laws required by RefinementGeomReadHom naturality]
  next_obligation: Prove G-115-local source-reading-cast naturality without predecessor edits; if the same API-visibility blocker persists, record target-blocked with the exact missing declarations.
```

The raw obstruction was discharged without inventing a lower inverse. The
G-115-local `rawReindexUpper` uses only the complete upper equivalence, and its
identity/composition laws reduce both explicit roundtrips to strict raw-system
equalities. Realization carrier casts and reading preservation are also
generated locally. Three independent proof attempts then reached the same
remaining boundary: the completed predecessor exposes objectwise carrier
equalities, while the corresponding readable-morphism computation lemmas are
private. No naturality field or `HGeom` certificate was added to bypass it.
