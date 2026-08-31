# G-115 — Geometry-Refinement Bridge and Upper BC Relational Naturality

- primary specification: [`research/goals/G-115-aat-upper-stage-lift.md`](../goals/G-115-aat-upper-stage-lift.md)
- tracking Issue: [#4250](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/4250)
- GOAL revision: 8 human-approved
- proof state: `target-proof-checkpoint` (revision 8 Cycle 69)
- completion candidate: no

This report records incremental proof obligations against the current fixed
target. Cycles 1--45 remain evidence for their named interfaces under their
then-current target revisions. Revision 5 replaced the selected-endpoint
realization requirement with a realization-exact upper-equivalence locus, and
Cycle 45 fixed the lossiness obstruction in its original negative producer.
Human-approved revision 6 preserves the positive locus and replaces only that
producer by a structure-preserving exact upper automorphism. Cycle 46 proves
the replacement's full cancellation and concrete realization obstruction.
Lean acceptance is evidence for each named cycle only; it is not a completion
verdict for G-115.

Cycle 63 proves that the theorem-generated solution preserves every local
Support, Axis, and Observable carrier value by heterogeneous equality. This
refuted revision 6's requirement that one such vertical value differ from
identity or equality transport. Human-approved revision 7 retains that generic
theorem family as carrier-conservativity evidence and assigns nondegenerate
firing to the genuinely lax horizontal refinement and strong edge, the
authored and generated comparators, and the derived raw cochain. The generated
vertical component continues to carry route coherence, while G-116 retains the
full-component `IsIso` decision.

Cycle 67 records the revision 7 negative-route defect: its custom raw problem
did not inhabit the actual problem / solution contract and imported an unrelated
selected-endpoint realization obligation. Human-approved revision 8 replaces
that route with typed comparator descent on qualified route transports over the
existing generated route and canonical component. The positive pair is read
from the actual solution field. The negative side copies the generated pulled
transport's geometry, edge lifts, qualifications, and comparator-independent
laws, changing only its authored comparator to identity. The resulting pair
must fail separately on Support, Axis, and Observable. It does not claim a
failure for the common-source-generated pair, raw solution emptiness, or a
decision of the G-116 `IsIso` branch.

## Historical revision 6 target

- merged GOAL revision PR: #4300
- final reviewed GOAL head: `044c30255c8a2cc38873880717320a519b78b251`
- merged GOAL commit and implementation base: `9bc1189e776bc2cab6eee95abaa3ec5298965dff`
- GOAL blob SHA: `74ed227d3cb23734f84c43d6022bceab054b31e5`
- GOAL SHA-256: `65a084cfe6eb6094d2dc33193e0b9185393043f44387e12151c17b355911044c`

Revision 6 is the fixed target approved and merged by PR #4300 after four
independent math/Lean review lanes returned `No major findings`. Its positive
endpoint, solution, reselection, cochain, and O12 contracts are unchanged from
revision 5. Only the refuted lossy negative producer is replaced.

## Revision 7 fixed-statement disposition

Revision 7 was explicitly approved after Cycle 63. It preserves every accepted
revision 6 construction and records the Cycle 63 theorem family as a positive
carrier-conservativity artifact. The named positive packet now proves concrete
nonidentity on the horizontal strong edge, authored and generated comparators,
and derived raw cochain, then specializes the actual solution edge and
comparator equations to those witnesses. The generated and canonical companion
solutions share one named compatible problem data object; their solution-type
`Equiv` relates the solutions and is not claimed to generate another problem.

- merged GOAL revision PR: #4319
- final reviewed GOAL head: `0100caf1dc105aa182bede61bd7db67fa5e8cc67`
- merged GOAL commit and implementation base: `8d916de9cd77b88efdb37cdbba4dd171f96a2f4b`
- GOAL blob SHA: `2e0c792a9387f9f4d0272590ad0129bfea5e04ff`
- GOAL SHA-256: `14c9f071c1815252693ab0e060f6dcd7172057bc1cb2a572e9ef5bd77159507b`

The revision 7 review head, merge commit, GOAL hash, and implementation base are
also fixed in tracking Issue #4250. Cycle 63 remains the terminal record for
revision 6 and is not rewritten as a successful proof of its refuted conjunct.

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

## Cycle 20 — backward geometry carriers, readings, and naturality

```yaml
ledger_type: target_cycle_result
goal: G-115-aat-upper-stage-lift
cycle: 20
goal_blob_sha: a11f61a5790c8ac75ce7f13da1277a859e2ab600ac96038bc55c338b80d38985
base_oid: cc618c5c6a8dc7903570101ef814db69c9bfa984
tracking_issue: 4250
report_path: research/reports/G-115-aat-upper-stage-lift.md
selection:
  proof_state_ref: Cycle 19 merged the literal pulled-route backward upper realization
  proof_dag_predecessors: [pulledRouteBackwardUpper, generatedRouteCoreMate_upper_eq_explicit, exact and selected canonical inverse transports]
  proof_obligation: Construct Support, Axis, and Observable maps for the actual pulled-route backward upper, and prove their reading-preservation and restriction-naturality laws from the two explicit backward transports.
  selection_reason: These are the missing computational fields required to lift generatedRouteCoreMate from its exact core upper map to a geometry comparison; carrier equalities alone do not preserve reading predicates or morphism maps.
  expected_result_type: proof-obligation-discharged
  lean_targets: [ResearchLean/AG/DoctrineFiberProduct/UpperGeometryMateComponents.lean]
  risks: [dependent target casts could hide a supplied comparison; carrier equalities could be mistaken for reading preservation; composite naturality could lose one route leg]
  unchecked: [complete upperGeometryMate GeomReadHom, coverage/overlap/raw equality, geometry triangle, finite-presentation comparison, named problems, clauses (c)--(d)]
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: Each exact and realized-refinement backward leg is locally identified with its canonical target transport; their generated carrier maps preserve Support/Axis/Observable readings and restriction maps; the two legs are then literally composed to obtain the public pulled-route backward maps and laws.
  completion_candidate: no
  lean_artifacts: [pulledRouteBackwardUpper_contextForward_support_type, pulledRouteBackwardUpper_contextForward_axis_type, pulledRouteBackwardUpper_contextForward_observable_type, pulledRouteBackwardSupportComp, pulledRouteBackwardSupportComp_reads, pulledRouteBackwardSupportComp_naturality, pulledRouteBackwardAxisComp, pulledRouteBackwardAxisComp_reads, pulledRouteBackwardAxisComp_naturality, pulledRouteBackwardObservableComp, pulledRouteBackwardObservableComp_reads, pulledRouteBackwardObservableComp_naturality]
  evidence: [focused Lean check, namespace standard-axiom audit, source hash, literal scans]
  source_sha256:
    UpperGeometryMateComponents.lean: d1a258700a9d29bfa900096eac077a7dc032d57fb8d9e0ac830df0878ea172a9
  claim_mapping:
    theorem_names: [pulledRouteBackwardSupportComp_reads, pulledRouteBackwardSupportComp_naturality, pulledRouteBackwardAxisComp_reads, pulledRouteBackwardAxisComp_naturality, pulledRouteBackwardObservableComp_reads, pulledRouteBackwardObservableComp_naturality]
    source_labels: [target theorem clause (b), K2b2a explicit Support/Axis/Observable transport]
    conjuncts: [backward carrier preservation, reading preservation for all three carriers, restriction naturality for all three carriers, literal exact-then-refinement route composition]
    undischarged_assumptions: [coverage/overlap/raw equality for the complete geometry mate, geometry triangle, downstream named contracts]
    acceptance_point: The public maps are generated from the actual exact and selected backward transports and their computational context transports; no caller map, HGeom, or comparison certificate is accepted.
    port_status: not-applicable
audits:
  premise_delta:
    discharged: [pulled-route backward Support/Axis/Observable comparison generation, their reading preservation, their full restriction naturality]
    remaining: [complete geometry mate and triangle, finite-presentation comparison and solution-space equivalence, positive/negative named artifacts, paired orbit/cochain and exchange-exact interface]
  certificate_provenance:
    discharged: [all three maps arise from transportEquationSystemExact on the exact pullback leg and the selected realized-refinement leg; target casts are eliminated by equality induction]
    unresolved: [complete geometry-level comparison]
  proof_use:
    used: [pulledRouteTransportData, pullbackTargetExactArrow, inverseCorePackageBackwardUpper, SelectedRefinementTransport.inverseCorePackageBackwardUpper, transportContextFunctor_supportMap, transportContextFunctor_axisMap, transportContextFunctor_observableRestrict]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [research/lean/check_research_modules.sh --focused ResearchLean/AG/DoctrineFiberProduct/UpperGeometryMateComponents.lean => exit 0 and 12 declarations standard axioms only; git diff --check => exit 0; placeholder and hidden/BiDi scans => no matches; protected G-112/G-114 and AAT mathematical-source diff scan => no matches]
  blocking_findings: []
  next_obligation: Compose the base-route forward geometry maps with these backward maps, construct the complete upperGeometryMate GeomReadHom over generatedRouteCoreMate, and prove its geometry triangle.
```

Cycle 20 adds the missing geometry-carrier realization in the active G-115
surface. Completed G-112 and G-114 APIs and GOAL cards remain unchanged.

## Cycle 21 — complete exact geometry mate and factorization triangle

```yaml
ledger_type: target_cycle_result
goal: G-115-aat-upper-stage-lift
cycle: 21
goal_blob_sha: a11f61a5790c8ac75ce7f13da1277a859e2ab600ac96038bc55c338b80d38985
base_oid: c0ee6bc22145bbf5648c36365d61b59cbb6d35dd
tracking_issue: 4250
report_path: research/reports/G-115-aat-upper-stage-lift.md
selection:
  proof_state_ref: Cycle 20 merged the pulled-route backward realization maps and laws
  proof_dag_predecessors: [generatedRouteCoreMate_upper_eq_explicit, baseRouteGeometryHom, pulledRouteGeometryHom, pulledRouteBackwardUpper and its carrier maps]
  proof_obligation: Create every missing exact geometry-mate field inside G-115, identify its base with generatedRouteCoreMate, and prove the full geometry-level factorization triangle without modifying completed G-112 or G-114.
  selection_reason: The core mate alone does not supply coverage, overlap, coefficient/raw transport, realization maps, or equality of the dependent geometry data in the route triangle.
  expected_result_type: proof-obligation-discharged
  lean_targets: [ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCleavage.lean, ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCleavageNaturality.lean, ResearchLean/AG/DoctrineFiberProduct/UpperGeometryMateComponents.lean, ResearchLean/AG/DoctrineFiberProduct/UpperGeometryMateGeometry.lean]
  risks: [inventing a backward coefficient map without provenance, inferring overlap from core equality, treating HEq carrier values as strict function equality before the base triangle, reopening completed predecessor GOALs]
  unchecked: [geometry-level comparison naturality and solution-space equivalence, named positive and negative problems, target clauses (c)--(d), final target assembly]
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: G-115 now supplies canonical exact and realized-refinement backward coefficient maps and raw laws, forward/backward context and carrier computation laws, a complete GeometryTotalHom upperGeometryMate over generatedRouteCoreMate, and a pointwise-proved geometry-level factorization triangle through pulledRouteGeometryHom.
  completion_candidate: no
  lean_artifacts: [exactSourceCoefficientBackwardHom, refinementSourceCoefficientBackwardHom, refinementSourceBackwardUpper, rawReindexUpper_baseChange, generatedExactSupportComp_heq, generatedRefinementSupportComp_heq, generatedExactAxisComp_heq, generatedRefinementAxisComp_heq, generatedExactObservableComp_heq, generatedRefinementObservableComp_heq, pulledRouteBackwardSupportComp_heq, pulledRouteBackwardAxisComp_heq, pulledRouteBackwardObservableComp_heq, upperGeometryMate, upperGeometryMate_raw_eq, upperGeometryMate_fac]
  evidence: [four focused Lean checks, namespace standard-axiom audits, source hashes, literal scans]
  source_sha256:
    UpperGeometryCleavage.lean: 18b9224f7ed015fbdba8dd898f8d23a57fd229245017b5bedee8aae60c779499
    UpperGeometryCleavageNaturality.lean: a495859f5238fdb8149b55418076cd086fd63617ca783c79d8939b9ec78afb0c
    UpperGeometryMateComponents.lean: 85dd63b2ab8e5978a1d59e1f16b26c2f368433c4b0a7225a5ad3f2775a2db9a8
    UpperGeometryMateGeometry.lean: 464da064fa5a5012b63bc7e7804af09bc7bb6854e414139047f35bdd712f5975
  claim_mapping:
    theorem_names: [upperGeometryMateExplicitBase_eq, upperGeometryMateOverlap, upperGeometryMate_raw_eq, upperGeometryMateCoefficient_fac, upperGeometryMate_fac]
    source_labels: [target theorem clause (b), K2b2a complete geometry mate and leg triangle]
    conjuncts: [generated exact core base, all nine coverage clauses, selected overlap comparison, coefficient and raw transport, support axis observable readings and naturality, exact-to-refinement geometry triangle]
    undischarged_assumptions: [edgewise geometry comparison, solution-space equivalence, named fixtures, paired cochain and exchange-exact artifacts]
    acceptance_point: The dependent triangle is proved only after the lower package triangle and pointwise forward/backward carrier cancellation laws; no geometry equality is inferred from the core upper equation alone.
    port_status: not-applicable
audits:
  premise_delta:
    discharged: [complete upperGeometryMate construction, canonical coefficient provenance, raw reindex/base-change compatibility, selected overlap transport, geometry-level route factorization]
    remaining: [finite-presentation comparison and solution-space equivalence, positive and negative named artifacts, paired orbit/cochain and exchange-exact interface]
  certificate_provenance:
    discharged: [backward coefficient maps are identity maps induced by the two G-115 pullback geometries; overlap is the mapped base-route overlap followed by explicit pulled context inversion; the triangle consumes generatedRouteRefinementMate_fac and all three carrier cancellation laws]
    unresolved: [downstream solution and reselection witnesses]
  proof_use:
    used: [baseRouteGeometryHom geometry fields, pulledRouteBackwardUpper_comp_forward, exact and selected context inverse laws, rawReindexUpper_comp, RawAmbientRestrictionSystem.baseChange_comp, generatedRouteCoreMate_toRefinement, generatedRouteRefinementMate_fac]
    unused: []
  structure_field_escape: no mate field, triangle, overlap, raw law, or cancellation certificate is caller data
  route_integrity: the mate connects the literal baseRouteGeometry and pulledRouteGeometry and factors their literal refinement-geometry legs
  predecessor_integrity: completed G-112 and G-114 source and GOAL cards are unchanged; every absent API is created in the active G-115 surface
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [focused checks for all four changed Lean modules => exit 0 with standard axioms only; git diff --check => exit 0; placeholder and hidden/BiDi scans => no matches; protected G-112/G-114 and AAT mathematical-source diff scan => no matches]
  blocking_findings: []
  next_obligation: Lift upperGeometryMate pointwise over the finite presentation, prove edge naturality and the G-114 authored comparator intertwining, and construct the geometry/core solution-space equivalence before named positive and negative problems.
```

Cycle 21 creates the complete missing geometry mate in G-115. Completed G-112
and G-114 remain immutable inputs rather than retroactive edit targets.

## Cycle 22 — finite pointwise mate family

```yaml
ledger_type: target_cycle_result
goal: G-115-aat-upper-stage-lift
cycle: 22
goal_blob_sha: a11f61a5790c8ac75ce7f13da1277a859e2ab600ac96038bc55c338b80d38985
base_oid: 7087f8a812d1971364ec67379639f8756af4c4fa
tracking_issue: 4250
report_path: research/reports/G-115-aat-upper-stage-lift.md
selection:
  proof_state_ref: Cycle 21 merged the complete objectwise upper geometry mate and full route triangle
  proof_dag_predecessors: [upperGeometryMate, upperGeometryMate_fac, generatedRouteCoreMate_comparison_square, UpperRefinementBCProblemData]
  proof_obligation: Evaluate the generated target geometry and upper mate at every vertex of the actual finite problem, retaining its coefficient carriers, full geometry triangle, and G-114 comparison square without identifying independently authored route geometries.
  selection_reason: Edge naturality and solution transport require a named dependent family over the actual sourceFiberDiagram; a standalone mate at one target does not provide that finite indexing boundary.
  expected_result_type: proof-obligation-discharged
  lean_targets: [ResearchLean/AG/DoctrineFiberProduct/UpperGeometryFiniteMate.lean]
  risks: [casting generated route geometries to authored problem geometries, replacing the G-114 comparison square by endpoint equality, claiming edge or comparator naturality before constructing it]
  unchecked: [generated route edge maps, edge naturality, authored comparator intertwining, geometry/core solution-space equivalence, named positive and negative problems, target clauses (c)--(d), final target assembly]
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: G-115 now provides a target geometry, generated base and pulled route geometries, and canonical upper geometry mate at every vertex of an arbitrary actual finite upper problem, together with both coefficient-carrier identifications, the full pointwise triangle, and the pointwise G-114 comparison square.
  completion_candidate: no
  lean_artifacts: [generatedTargetGeometryAt, generatedBaseRouteGeometryAt, generatedPulledRouteGeometryAt, generatedUpperGeometryMateAt, generatedUpperGeometryMateAt_base, generatedBaseRouteGeometryAt_coefficient_eq, generatedPulledRouteGeometryAt_coefficient_eq, generatedUpperGeometryMateAt_triangle, generatedUpperGeometryMateAt_comparison_square]
  evidence: [focused Lean check, namespace standard-axiom audit, source hash, literal scans]
  source_sha256:
    UpperGeometryFiniteMate.lean: 70a2b047d14aad4a70f748856481789ebfb89540496c091e1fa4c53d91d92dd9
  claim_mapping:
    theorem_names: [generatedUpperGeometryMateAt_base, generatedUpperGeometryMateAt_triangle, generatedUpperGeometryMateAt_comparison_square]
    source_labels: [target theorem clause (b), finite presentation pointwise comparison boundary]
    conjuncts: [actual sourceFiberDiagram indexing, generated complete geometry mate, retained coefficient carriers, full pointwise factorization, explicit G-114 comparison square]
    undischarged_assumptions: [edgewise comparison naturality, authored comparator intertwining, solution-space equivalence, named fixtures, paired cochain and exchange-exact artifacts]
    acceptance_point: Generated and independently authored route geometries remain distinct; the new family fixes the vertices and comparison square that later bridge maps must consume.
    port_status: not-applicable
audits:
  premise_delta:
    discharged: [finite pointwise evaluation of the generated mate, pointwise full triangle, pointwise G-114 core comparison square]
    remaining: [finite edge maps and naturality, comparator intertwining, solution equivalence, positive and negative named artifacts, paired orbit/cochain and exchange-exact interface]
  certificate_provenance:
    discharged: [each component is generated directly from the common target geometry in the actual problem and the retargeted active context]
    unresolved: [geometry-level endpoint comparison and downstream solution transports]
  proof_use:
    used: [problem sourceFiberDiagram, problem commonTarget geometry, upperGeometryMate_fac, generatedRouteCoreMate_comparison_square]
    unused: []
  structure_field_escape: no component, triangle, comparison square, edge law, or solution is supplied by the caller
  route_integrity: every vertex is evaluated on its literal sourceFiberDiagram object and retargeted G-114 context
  predecessor_integrity: completed G-112 and G-114 source and GOAL cards are unchanged; the finite-family API is added only in G-115
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: not-yet-claimed
  goal_or_report_reinterpretation: none-found
  validation_refs: [research/lean/check_research_modules.sh --focused ResearchLean/AG/DoctrineFiberProduct/UpperGeometryFiniteMate.lean => exit 0 and 9 declarations standard axioms only]
  blocking_findings: []
  next_obligation: Construct the generated base and pulled edge maps over this family, prove upperGeometryMate edge naturality and authored comparator intertwining, then build the two solution transports and their inverse laws.
```

Cycle 22 fixes the finite pointwise domain of the comparison without collapsing
generated and authored geometry endpoints. Completed predecessor GOALs remain
unchanged.

## Cycle 23 — conjugated finite core diagrams and natural transformation

```yaml
ledger_type: target_cycle_result
goal: G-115-aat-upper-stage-lift
cycle: 23
goal_blob_sha: a11f61a5790c8ac75ce7f13da1277a859e2ab600ac96038bc55c338b80d38985
base_oid: 766e681016f4a6b13a1737322b0fa59453e2b14d
tracking_issue: 4250
report_path: research/reports/G-115-aat-upper-stage-lift.md
selection:
  proof_state_ref: Cycle 22 merged the generated pointwise geometry mate family and its G-114 comparison square
  proof_dag_predecessors: [baseRouteBaseMateIso, pulledRoutePulledMateIso, ActiveRefinementBCContext.baseCoreDiagram, ActiveRefinementBCContext.pulledCoreDiagram, ctx.mate]
  proof_obligation: Put the actual G-114 finite route diagrams onto the literal G-115-generated endpoint families and transport the completed G-114 mate naturality across those endpoint isomorphisms.
  selection_reason: Generated endpoints are not definitionally equal to the independently selected G-114 endpoints. Edgewise work therefore needs explicit conjugated functors and a natural transformation, not a cast or a retroactive predecessor API change.
  expected_result_type: proof-checkpoint
  lean_targets: [ResearchLean/AG/DoctrineFiberProduct/UpperGeometryFiniteCoreNaturality.lean]
  risks: [reopening G-112 or G-114, claiming equality with generatedRouteCoreMate before proving it, treating endpoint isomorphism as definitional equality]
  unchecked: [identification with generatedRouteCoreMate, generated geometry edge maps, geometry-mate edge naturality, authored comparator intertwining, solution-space equivalence, named fixtures, clauses (c)--(d)]
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: At every finite-presentation vertex G-115 now exposes exact endpoint isomorphisms to the actual G-114 route objects; conjugating both actual route functors by those isomorphisms gives literal generated-endpoint core diagrams; conjugating ctx.mate gives a natural transformation between them along every presented path.
  completion_candidate: no
  lean_artifacts: [generatedBaseCoreIsoAt, generatedPulledCoreIsoAt, generatedBaseCoreDiagram, generatedPulledCoreDiagram, generatedConjugateCoreMateAt, generatedConjugateCoreMateAt_naturality, generatedConjugateCoreMate]
  evidence: [focused Lean check, namespace standard-axiom audit, source hash, literal scans]
  source_sha256:
    UpperGeometryFiniteCoreNaturality.lean: ba63d92613d05f87bdbcde72304b5a6e96b6af920d7c2d9d5e30f733accb5456
  claim_mapping:
    theorem_names: [generatedConjugateCoreMateAt_naturality]
    source_labels: [target theorem clause (b), finite-presentation G-114 comparison naturality substrate]
    conjuncts: [literal generated core endpoints, actual route functor transport, exact endpoint provenance, path naturality of the conjugated completed mate]
    undischarged_assumptions: [equality with the pointwise generated mate, geometry edge realization, comparator compatibility, downstream solution and orbit contracts]
    acceptance_point: This cycle proves only the transported actual-core natural transformation. It does not infer geometry naturality or identify it with generatedRouteCoreMate without the remaining universal-property argument.
    port_status: not-applicable
audits:
  premise_delta:
    ambient_boundary: [completed G-114 base and pulled core diagrams and ctx.mate, Cycle 22 pointwise generated endpoints]
    direction_hypothesis: []
    discharged: [finite generated-endpoint core functors, exact endpoint comparison provenance, conjugated core path naturality]
    remaining: [generated mate identification, geometry edge maps and naturality, comparator intertwining, solution equivalence, positive and negative named artifacts, paired orbit/cochain and exchange-exact interface]
  certificate_provenance:
    discharged: [endpoint isomorphisms are the G-115-local universal comparisons baseRouteBaseMateIso and pulledRoutePulledMateIso; naturality is transported directly from ctx.mate.naturality]
    unresolved: [geometry-level edge and comparator comparison]
  proof_use:
    used: [baseRouteBaseMateIso, pulledRoutePulledMateIso, sourceFiberDiagram map, ctx.mate.naturality]
    unused: []
  structure_field_escape: no route-between component or naturality law is supplied by the problem input
  route_integrity: both conjugated diagrams are obtained from the literal actual G-114 route functors at the actual sourceFiberDiagram, with explicit endpoint isomorphisms
  predecessor_integrity: completed G-112 and G-114 source and GOAL cards are unchanged; the absent finite comparison API is created only in G-115
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: not-claimed
  goal_or_report_reinterpretation: none-found
  validation_refs: [research/lean/check_research_modules.sh --focused ResearchLean/AG/DoctrineFiberProduct/UpperGeometryFiniteCoreNaturality.lean => exit 0 and 7 declarations standard axioms only]
  blocking_findings: []
  next_obligation: Identify generatedConjugateCoreMateAt with generatedRouteCoreMate by the endpoint-comparison universal properties, then lift the conjugated edge maps to the generated geometry families and prove upperGeometryMate edge naturality.
```

Cycle 23 creates the missing finite comparison API in G-115. Completed G-112
and G-114 remain immutable sources of the actual diagrams and mate.

## Cycle 24 — exactification and generated core mate naturality

```yaml
ledger_type: target_cycle_result
goal: G-115-aat-upper-stage-lift
cycle: 24
goal_blob_sha: a11f61a5790c8ac75ce7f13da1277a859e2ab600ac96038bc55c338b80d38985
base_oid: b00c49a6b4c4fba72ca1f9911f9178fdace5cb0a
tracking_issue: 4250
report_path: research/reports/G-115-aat-upper-stage-lift.md
selection:
  proof_state_ref: Cycle 23 merged the actual G-114 finite mate conjugated onto generated core endpoints
  proof_dag_predecessors: [baseRouteComparisonIso, pulledRouteComparisonIso, transportedG114RefinementMate_eq_generated, generatedRouteCoreMate_toRefinement, generatedConjugateCoreMateAt_naturality]
  proof_obligation: Exactify the G-115 universal refinement endpoint comparisons, identify the conjugated actual G-114 mate with the pointwise generated exact mate, and transfer finite path naturality to generatedRouteCoreMate itself.
  selection_reason: The exact endpoint choices and universal refinement comparisons are not definitionally equal. G-115 therefore needs an explicit exactification/recovery theorem instead of an rfl cast or a predecessor edit.
  expected_result_type: proof-obligation-discharged
  lean_targets: [ResearchLean/AG/DoctrineFiberProduct/UpperGeometryFiniteCoreNaturality.lean]
  risks: [assuming exact/refinement comparisons definitionally equal, losing complete upper data during exactification, inferring geometry edge naturality from core naturality]
  unchecked: [generated geometry edge maps, geometry-mate edge naturality, authored comparator intertwining, solution-space equivalence, named fixtures, clauses (c)--(d)]
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: A refinement comparison over literal exact endpoint transport is now exactified to a vertical CoreFiber morphism and recovered faithfully after refinement embedding. Both universal endpoint comparison isomorphisms are lifted this way. The conjugated actual G-114 mate embeds to transportedG114RefinementMate, hence equals generatedRouteCoreMate by the previously proved universal identification. The generated components therefore assemble into a natural transformation over the finite presentation.
  completion_candidate: no
  lean_artifacts: [exactCoreHomOfRefinementComparison, exactCoreHomOfRefinementComparison_toRefinement, baseRouteComparisonCoreHom, baseRouteComparisonCoreHom_toRefinement, baseRouteComparisonCoreInv, baseRouteComparisonCoreInv_toRefinement, baseRouteComparisonCoreIso, pulledRouteComparisonCoreHom, pulledRouteComparisonCoreHom_toRefinement, pulledRouteComparisonCoreInv, pulledRouteComparisonCoreInv_toRefinement, pulledRouteComparisonCoreIso, generatedConjugateCoreMateAt_toRefinement, generatedConjugateCoreMateAt_eq_generated, generatedRouteCoreMateAt_naturality, generatedRouteCoreMateNatTrans]
  evidence: [focused Lean check, namespace standard-axiom audit, source hash, literal scans]
  source_sha256:
    UpperGeometryFiniteCoreNaturality.lean: 4d2bede615f74fec8bb2ac4c6c37cb42d75ba0930ff2ba7f832a88e7322f2147
  claim_mapping:
    theorem_names: [exactCoreHomOfRefinementComparison_toRefinement, baseRouteComparisonCoreHom_toRefinement, pulledRouteComparisonCoreHom_toRefinement, generatedConjugateCoreMateAt_toRefinement, generatedConjugateCoreMateAt_eq_generated, generatedRouteCoreMateAt_naturality]
    source_labels: [target theorem clause (b), finite-presentation generated core comparison naturality]
    conjuncts: [complete-upper-preserving exactification, endpoint comparison isomorphisms, transported G-114 mate identification, generated core mate path naturality, finite natural transformation]
    undischarged_assumptions: [geometry realization of route edges, geometry mate edge naturality, authored comparator compatibility, downstream solution and orbit contracts]
    acceptance_point: Exactification consumes the full RefinementPackageHom upper map and proves faithful recovery. Generated mate equality then uses both endpoint recovery theorems, the actual ctx.mate component, transportedG114RefinementMate_eq_generated, and exact embedding injectivity.
    port_status: not-applicable
audits:
  premise_delta:
    ambient_boundary: [completed G-114 actual mate, Cycle 17 universal refinement comparisons, Cycle 23 conjugated core naturality]
    direction_hypothesis: []
    discharged: [exact core realization of both endpoint comparisons, exact/refinement recovery, conjugated-to-generated component equality, generated core mate finite naturality]
    remaining: [geometry edge generation and naturality, comparator intertwining, solution equivalence, positive and negative named artifacts, paired orbit/cochain and exchange-exact interface]
  certificate_provenance:
    discharged: [exact lower maps are literal endpoint equality transports; complete upper maps come from the universal refinement comparison isomorphisms; inverse laws are reflected through exactPackageToRefinement_map_injective]
    unresolved: [geometry-level edge and comparator lifts]
  proof_use:
    used: [baseRouteComparisonHom_base, baseRouteComparisonInv_base, pulledRouteComparisonHom_base, pulledRouteComparisonInv_base, exactPackageToRefinement_map_injective, transportedG114RefinementMate_eq_generated, generatedRouteCoreMate_toRefinement, ctx.mate.naturality]
    unused: []
  structure_field_escape: no exact comparison, mate equality, or route-between naturality is supplied by the finite problem
  route_integrity: exactification recovers the literal G-115 universal comparisons; conjugation still uses the actual G-114 route diagrams and mate at each actual sourceFiberDiagram object
  predecessor_integrity: completed G-112 and G-114 source and GOAL cards are unchanged; all new exactification and identification APIs are local to active G-115
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: both endpoint comparison inverses and both exact iso laws are constructed
  goal_or_report_reinterpretation: none-found
  validation_refs: [research/lean/check_research_modules.sh --focused ResearchLean/AG/DoctrineFiberProduct/UpperGeometryFiniteCoreNaturality.lean => exit 0 and 23 declarations standard axioms only]
  blocking_findings: []
  next_obligation: Use the now-natural generated core diagrams to construct strongly cocartesian generated geometry edge maps, prove upperGeometryMate edge naturality, and then address authored comparator intertwining.
```

Cycle 24 identifies the actual and generated finite core mates through a
G-115-local exactification of the universal comparisons. Completed predecessor
GOALs remain unchanged.

## Cycle 25 — G-115-local geometry exactification and conditional edge naturality

```yaml
ledger_type: target_cycle_result
goal: G-115-aat-upper-stage-lift
cycle: 25
goal_blob_sha: a11f61a5790c8ac75ce7f13da1277a859e2ab600ac96038bc55c338b80d38985
base_oid: 6a63eee016815ac8f6cfd2f43c2767b5a6223c6d
tracking_issue: 4250
report_path: research/reports/G-115-aat-upper-stage-lift.md
selection:
  proof_state_ref: Cycle 24 merged generated core mate naturality on the literal generated endpoints
  proof_dag_predecessors: [generatedRouteCoreMateAt_naturality, generatedBaseCoreDiagram, generatedPulledCoreDiagram, baseRouteGeometryHom, pulledRouteGeometryHom]
  proof_obligation: Exactify universal refinement-geometry factors whose lower maps are exact, construct finite generated geometry edges from route-leg cartesianness, and prove the complete upper geometry mate edge square.
  selection_reason: Core naturality alone cannot produce coefficient, support, axis, or observable transport. The missing exactification and geometry-factor APIs therefore belong to active G-115 rather than completed G-112 or G-114.
  expected_result_type: target-proof-checkpoint
  lean_targets: [ResearchLean/AG/DoctrineFiberProduct/UpperGeometryFiniteGeometryExactification.lean]
  risks: [treating core equality as geometry equality, accepting route-leg cartesianness as discharged merely because it appears as an argument, reopening completed predecessor APIs]
  unchecked: [G-115-local construction of both route-leg cartesianness witnesses, unconditional generated edge family, authored comparator intertwining, solution-space equivalence, named fixtures, clauses (c)--(d)]
result:
  proposed_result_type: target-proof-checkpoint
  proof_obligation_delta: G-115 now exactifies a complete refinement-geometry morphism over an exact lower package map and proves faithful recovery after re-embedding. Assuming the still-explicit cartesian qualifications of the two generated route legs, it constructs exact generated base and pulled geometry edges, proves their full geometry factor laws against the actual common-source edge, and proves finite-edge naturality of the generated upper geometry mate from the two full route triangles.
  completion_candidate: no
  lean_artifacts: [exactGeomReadHomOfRefinement, exactGeometryHomOfRefinement, exactGeometryHomOfRefinement_toRefinement, generatedBaseCoreEdge_fac, generatedPulledCoreEdge_fac, generatedBaseRefinementGeometryEdge, generatedBaseGeometryEdge, generatedBaseGeometryEdge_toRefinement, generatedBaseGeometryEdge_fac, generatedPulledRefinementGeometryEdge, generatedPulledGeometryEdge, generatedPulledGeometryEdge_toRefinement, generatedPulledGeometryEdge_fac, generatedUpperGeometryMateAt_edge_naturality]
  evidence: [focused Lean check, targeted direct-module build, namespace standard-axiom audit, source hash, literal scans]
  source_sha256:
    UpperGeometryFiniteGeometryExactification.lean: fb86e1c5c8ddc3c06bfcae8c5f1602e83c5e2041007fdc391c6d7c7c80e59c21
  claim_mapping:
    theorem_names: [exactGeometryHomOfRefinement_toRefinement, generatedBaseCoreEdge_fac, generatedPulledCoreEdge_fac, generatedBaseGeometryEdge_fac, generatedPulledGeometryEdge_fac, generatedUpperGeometryMateAt_edge_naturality]
    source_labels: [target theorem clause (b), G-115-local geometry cleavage finite-edge boundary]
    conjuncts: [full refinement-geometry exactification, exact embedding recovery, actual-source route factorization, coefficient and local-reading preservation through complete geometry equality, conditional finite mate naturality]
    undischarged_assumptions: [baseRouteGeometryHom cartesianness for refinementGeometryProjection, pulledRouteGeometryHom cartesianness for refinementGeometryProjection, comparator compatibility, downstream solution and orbit contracts]
    acceptance_point: The conditional edge square is a reusable intermediate theorem only. Its two explicit cartesian arguments are not counted as premise discharge and must be generated by the G-115 cleavage before the unconditional finite geometry solution exists.
    port_status: not-applicable
audits:
  premise_delta:
    ambient_boundary: [completed G-114 actual route diagrams and mate, actual G-115 source geometry edges and route-internal naturality]
    direction_hypothesis: [raw problem base_naturality, raw problem pulled_naturality]
    discharged: [full refinement-geometry exactification over exact lower maps, generated core edge factor graphs, conditional exact geometry edge construction, conditional mate edge naturality]
    remaining: [G-115-generated route-leg cartesianness, unconditional edge maps and mate naturality, comparator intertwining, solution equivalence, positive and negative named artifacts, paired orbit/cochain and exchange-exact interface]
  certificate_provenance:
    discharged: [exact lower maps are generated core-diagram edges; complete geometry factors come from the refinementGeometryProjection universal property and are recovered faithfully by exact embedding]
    unresolved: [the two route-leg cartesian qualifications, downstream comparator and reselection witnesses]
  proof_use:
    used: [generatedRouteCoreMateAt_naturality, generatedUpperGeometryMateAt_triangle, generatedBaseCoreEdge_fac, generatedPulledCoreEdge_fac, sourceTransport.edgeLift, base_naturality_projection, pulled_naturality_projection, exactGeometryToRefinementGeometry faithfulness]
    unused: []
  structure_field_escape: no exactification, geometry edge, factor law, or mate naturality equation is stored in problem data; the temporary cartesian arguments remain explicitly marked undischarged
  route_integrity: both generated edges factor their literal G-115 route legs through the actual common-source geometry edge; the mate square consumes both full geometry factors and both pointwise mate triangles
  predecessor_integrity: completed G-112 and G-114 source and GOAL cards are unchanged; every absent API is created in the active G-115 module
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: not-claimed
  goal_or_report_reinterpretation: none-found
  validation_refs: [research/lean/check_research_modules.sh --focused ResearchLean/AG/DoctrineFiberProduct/UpperGeometryFiniteGeometryExactification.lean => exit 0 and 25 declarations standard axioms only; lake build ResearchLean.AG.DoctrineFiberProduct.UpperGeometryFiniteGeometryExactification => exit 0 and 25 declarations standard axioms only; git diff --check => exit 0; placeholder and hidden/BiDi scans => no matches]
  blocking_findings: []
  next_obligation: Construct the two route-leg strong-cartesianness theorems from the explicit G-115 geometry transports, eliminate the temporary cartesian arguments, and then prove authored comparator intertwining.
```

Cycle 25 adds the missing exactification and finite geometry-factor API only to
G-115. It is deliberately not a completion claim: the route-leg cartesian
qualifications remain the next G-115-local construction obligation.

## Cycle 26 — generated geometry cartesianness and unconditional edge naturality

```yaml
ledger_type: target_cycle_result
goal: G-115-aat-upper-stage-lift
cycle: 26
goal_blob_sha: a11f61a5790c8ac75ce7f13da1277a859e2ab600ac96038bc55c338b80d38985
base_oid: 1c81c20465ec4099ec36156176c28f89e1139ef2
tracking_issue: 4250
report_path: research/reports/G-115-aat-upper-stage-lift.md
selection:
  proof_state_ref: Cycle 25 exposed conditional finite geometry edges whose only undischarged inputs were the two generated route-leg Cartesian qualifications
  proof_dag_predecessors: [generatedExactGeometryHom, generatedRefinementGeometryHom, generatedBaseGeometryEdge, generatedPulledGeometryEdge, generatedUpperGeometryMateAt_edge_naturality]
  proof_obligation: Prove the exact and realized-refinement G-115 geometry cleavages strongly Cartesian, inherit this property along both literal route composites, and eliminate the temporary Cartesian arguments from finite geometry naturality.
  selection_reason: The missing universal properties concern G-115-generated geometry reading data. They are constructed locally from the existing two-sided context and carrier transports; no completed predecessor needs revision.
  expected_result_type: target-proof-checkpoint
  lean_targets: [ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCleavageNaturality.lean, ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCartesian.lean, ResearchLean/AG/DoctrineFiberProduct/UpperGeometryFiniteCartesianNaturality.lean]
  risks: [using carrier casts without reading reflection, proving only lower-package cartesianness, retaining caller-supplied Cartesian certificates, reopening completed predecessor APIs]
  unchecked: [authored comparator intertwining, solution-space equivalence, named positive and negative fixtures, clauses (c)--(d)]
result:
  proposed_result_type: target-proof-checkpoint
  proof_obligation_delta: Exact and realized-refinement support, axis, and observable transports now expose reading reflection, cancellation, and injectivity. These generate complete geometry factors, factor laws, uniqueness, and strong cartesianness for both primitive legs. Composition proves both literal geometry routes strongly Cartesian, yielding unconditional exact finite edge maps, their full geometry factor laws, and upper geometry mate edge naturality with no caller certificate.
  completion_candidate: no
  lean_artifacts: [generatedExactSupportComp_reads_iff, generatedExactAxisComp_reads_iff, generatedExactObservableComp_reads_iff, generatedRefinementSupportComp_reads_iff, generatedRefinementAxisComp_reads_iff, generatedRefinementObservableComp_reads_iff, generatedExactCartesianFactor, generatedExactCartesianFactor_fac, generatedExactCartesianFactor_unique, generatedExactGeometryHom_isStronglyCartesian, generatedRefinementCartesianFactor, generatedRefinementCartesianFactor_fac, generatedRefinementCartesianFactor_unique, generatedRefinementGeometryHom_isStronglyCartesian, baseRouteGeometryHom_isStronglyCartesian, pulledRouteGeometryHom_isStronglyCartesian, generatedBaseGeometryEdgeUnconditional, generatedPulledGeometryEdgeUnconditional, generatedBaseGeometryEdgeUnconditional_fac, generatedPulledGeometryEdgeUnconditional_fac, generatedUpperGeometryMateAt_edge_naturality_unconditional]
  evidence: [three focused Lean checks, targeted direct-module build, namespace standard-axiom audits, source hashes, literal scans]
  source_sha256:
    UpperGeometryCleavageNaturality.lean: 34d61065049243c6ee49676b3a2c6315225362ece635a6f7beee8d090419f13d
    UpperGeometryCartesian.lean: bf2fd6e25cdeba75edf30e97307bb727cadb9868288711557f0d6d640494a0fb
    UpperGeometryFiniteCartesianNaturality.lean: 83a640f50d80d7d0761270f5feb5ab084aecef1b7530211579f336ea44ab4b8e
  claim_mapping:
    theorem_names: [generatedExactGeometryHom_isStronglyCartesian, generatedRefinementGeometryHom_isStronglyCartesian, baseRouteGeometryHom_isStronglyCartesian, pulledRouteGeometryHom_isStronglyCartesian, generatedBaseGeometryEdgeUnconditional_fac, generatedPulledGeometryEdgeUnconditional_fac, generatedUpperGeometryMateAt_edge_naturality_unconditional]
    source_labels: [target theorem clause (b), G-115-local geometry cleavage and finite naturality boundary]
    conjuncts: [primitive exact geometry cartesianness, primitive realized-refinement geometry cartesianness, both literal route composite Cartesian qualifications, unconditional finite exact geometry edges, both full route factor laws, unconditional upper mate edge naturality]
    undischarged_assumptions: [authored comparator compatibility, downstream solution and orbit contracts]
    acceptance_point: Strong cartesianness is proved by explicit factor construction and uniqueness for every compatible complete geometry hom. The finite APIs instantiate those generated proofs internally; no Cartesian witness remains in their signatures.
    port_status: not-applicable
audits:
  premise_delta:
    ambient_boundary: [completed G-112 exact lower cleavage API, completed G-114 realized-refinement and actual route data, Cycle 25 conditional geometry exactification]
    direction_hypothesis: [realized-locus extraction reflection already required by the active G-115 route]
    discharged: [exact primitive geometry cartesianness, realized-refinement primitive geometry cartesianness, both composite route qualifications, unconditional exact edge generation, unconditional mate edge naturality]
    remaining: [authored comparator intertwining, solution equivalence, positive and negative named artifacts, paired orbit/cochain and exchange-exact interface]
  certificate_provenance:
    discharged: [context inverse cancellation comes from generated equation equivalences; carrier cancellation and reading reflection come from G-115 deconjugation transports; factor uniqueness is proved by complete geometry contract extensionality]
    unresolved: [downstream comparator and reselection witnesses]
  proof_use:
    used: [generated exact and refinement reading iff laws, generated exact and refinement carrier HEq laws, generated exact and refinement carrier inverse laws, generated exact and refinement carrier injectivity laws, generated exact and refinement carrier naturality laws, rawReindexUpper_comp, IsStronglyCartesian.mk, IsStronglyCartesian.comp, Cycle 25 universal geometry edge factorization]
    unused: []
  structure_field_escape: no Cartesian certificate, factor, uniqueness equation, edge factor law, or mate naturality equation is stored in problem data or accepted from a caller
  route_integrity: both unconditional finite edges still factor the literal generated baseRouteGeometryHom and pulledRouteGeometryHom through the actual sourceTransport edge, and the mate square uses both full geometry triangles
  predecessor_integrity: completed G-112 and G-114 source, GOAL, report, and implementation files are unchanged; all missing semantic APIs are added under active G-115
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: both primitive Cartesian proofs include existence and uniqueness; no unsupported equivalence is claimed
  goal_or_report_reinterpretation: none-found
  validation_refs: [three check_research_modules.sh --focused invocations => exit 0 with 58, 16, and 9 declarations standard axioms only; lake build ResearchLean.AG.DoctrineFiberProduct.UpperGeometryFiniteCartesianNaturality => exit 0 with 4077 jobs and standard-axiom audits]
  blocking_findings: []
  next_obligation: Prove the authored comparator intertwining against the now-unconditional finite generated geometry mate, then continue to the solution-space and named-fixture obligations.
```

Cycle 26 removes the last caller-supplied Cartesian certificates from the
finite geometry route. It remains a G-115 checkpoint rather than a completion
claim; authored comparator intertwining is the next obligation.

## Cycle 27 — authored comparator intertwining

```yaml
ledger_type: target_cycle_result
goal: G-115-aat-upper-stage-lift
cycle: 27
goal_blob_sha: a11f61a5790c8ac75ce7f13da1277a859e2ab600ac96038bc55c338b80d38985
base_oid: 4e09d885bf1b9852df7b6cdbb857717d0444ba89
tracking_issue: 4250
report_path: research/reports/G-115-aat-upper-stage-lift.md
selection:
  proof_state_ref: Cycle 26 merged unconditional generated geometry edges and mate naturality
  proof_dag_predecessors: [generatedBaseGeometryEdgeUnconditional, generatedPulledGeometryEdgeUnconditional, generatedUpperGeometryMateAt_edge_naturality_unconditional, UpperRefinementBCSolution.comparator_intertwining]
  proof_obligation: Prove authored comparator intertwining for the unconditional finite generated upper geometry mate without replacing the problem comparators by canonical or identity comparators and without storing a route-between equation in the raw problem.
  selection_reason: This is the next fixed-GOAL equation after generator naturality and the shortest remaining path to the geometry-compatible solution contract.
  expected_result_type: proof-obligation-discharged
  lean_targets: [ResearchLean/AG/DoctrineFiberProduct/UpperGeometryFiniteComparatorNaturality.lean]
  risks: [generated and authored endpoint type mismatch, comparator replacement, core-only equality, caller-supplied route-between certificate, missing comparison-map provenance]
  unchecked: [solution-space equivalence, named positive and negative fixtures, coefficient-trivial reselection transport, paired cochain theorem, conditional exchange interface]
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: The authored base and pulled route endpoints now map to the generated G-115 endpoints by complete exact geometry comparisons obtained from the generated route Cartesian universal properties. For every actual solution, the solution component and generated mate form a full geometry square. Pasting that square with the stored solution comparator equation proves authored comparator intertwining without regenerating either comparator.
  completion_candidate: no
  lean_artifacts: [generatedBaseGeometryComparisonRefinementAt, generatedBaseGeometryComparisonAt, generatedBaseGeometryComparisonAt_fac, generatedPulledGeometryComparisonRefinementAt, generatedPulledGeometryComparisonAt, generatedPulledGeometryComparisonAt_fac, generated_component_base_square, generated_component_geometry_square, generated_authored_comparator_intertwining]
  evidence: [focused Lean check, 13-declaration standard-axiom audit, source hash, placeholder and hidden-character scans]
  source_sha256:
    UpperGeometryFiniteComparatorNaturality.lean: 49f84b9eb79a068da16cdf2d5de11c8a843159e031a6856e9aee51daecf0fab7
  claim_mapping:
    theorem_names: [generatedBaseGeometryComparisonAt_fac, generatedPulledGeometryComparisonAt_fac, generated_component_geometry_square, generated_authored_comparator_intertwining]
    source_labels: [target theorem clause (b), geometry-level G-114 comparison and authored-comparator compatibility]
    conjuncts: [authored-to-generated complete endpoint comparisons, exact lower recovery, both route-leg factor laws, solution-to-generated-mate geometry square, authored comparator pasting]
    undischarged_assumptions: [construction of the two solution-space transports and inverse laws, named actual positive and negative artifacts, clause (c) restricted reselection and paired cochain, clause (d) conditional exchange interface]
    acceptance_point: Comparator compatibility is derived for every existing actual solution from its triangle and authored comparator equation together with G-115-generated endpoint comparisons. The theorem accepts no new comparator equation or comparison certificate.
    port_status: not-applicable
audits:
  premise_delta:
    ambient_boundary: [the raw problem's authored route geometries and comparator families, completed G-114 mate, Cycle 26 generated mate and route Cartesianity]
    direction_hypothesis: []
    solution_contract_input: [the existing actual solution supplies its route-between triangle]
    conclusion_equivalent_risk: [the existing actual solution supplies its authored comparator equation; Cycle 27 does not discharge that stored equation, but proves its preservation after the generated endpoint comparison]
    discharged: [complete endpoint comparison maps, comparison-square proof-use, authored comparator intertwining against the generated mate]
    remaining: [solution-space equivalence, positive and negative named artifacts, coefficient-trivial reselection transport, paired cochain theorem, conditional exchange interface]
  certificate_provenance:
    discharged: [both endpoint comparisons are generated by IsStronglyCartesian.map over the exact inverse endpoint core isomorphisms and exactified with faithful recovery]
    unresolved: [named solution and negative witnesses, reselection witness transports]
  proof_use:
    used: [baseRouteGeometryHom_isStronglyCartesian, pulledRouteGeometryHom_isStronglyCartesian, baseRouteComparisonCoreInv, pulledRouteComparisonCoreInv, generatedUpperGeometryMateAt_triangle, generatedConjugateCoreMateAt_eq_generated, UpperRefinementBCSolution.triangle, UpperRefinementBCSolution.comparator_intertwining]
    unused: []
  structure_field_escape: no endpoint comparison or generated comparator equation is added to raw problem data; the only route-between fields consumed belong to the pre-existing solution contract
  route_integrity: both comparison maps factor the literal authored route legs through the literal generated G-115 routes; the geometry square uses the actual G-114 component base equality and the generated conjugate-mate identification
  predecessor_integrity: completed G-112 and G-114 files are unchanged; all comparison and comparator-pasting APIs are local to active G-115
  target_fitting: none-found
  vacuity: not yet decided before the named positive and negative fixtures
  one_way_as_equivalence: no solution-space equivalence is claimed in this cycle
  goal_or_report_reinterpretation: none-found
  validation_refs: [check_research_modules.sh --focused ResearchLean/AG/DoctrineFiberProduct/UpperGeometryFiniteComparatorNaturality.lean => exit 0 and 13 declarations standard axioms only; git diff --check => exit 0; placeholder, hidden/BiDi, privacy, and reverse-import scans => no matches]
  blocking_findings: []
  next_obligation: Define the geometry-compatible generated solution contract and construct both transports with inverse laws to the core-selected companion solution space.
```

Cycle 27 retains both authored comparator families. The new theorem is
conditional only on an actual solution already carrying the route-between
triangle and authored comparator equation required by the fixed contract; it
does not move either equation into the raw problem or claim the still-missing
solution-space equivalence.

## Cycle 29 — certificate-free compatible input and generated route spine

```yaml
ledger_type: target_cycle_result
goal: G-115-aat-upper-stage-lift
cycle: 29
goal_blob_sha: fcd33815da27d5e1390b101223de49173967a349ad5f2e85324ec3b8d25b597c
base_oid: 98a3a59140e406c613a26056fb1ef46ba3a4a670
tracking_issue: 4250
report_path: research/reports/G-115-aat-upper-stage-lift.md
selection:
  proof_state_ref: revision 4 merged after Cycle 28 identified that arbitrary raw authored endpoints do not admit inverse comparisons
  proof_dag_predecessors: [FixedCoefficientTwoLayerTransportOver, UpperGeometryCleavage.baseRouteGeometryHom, UpperGeometryCleavage.pulledRouteGeometryHom, baseRouteGeometryHom_isStronglyCartesian, pulledRouteGeometryHom_isStronglyCartesian]
  proof_obligation: Define the certificate-free compatible input, retain its one source transport for successor finite-edge and comparator constructions, and generate both literal reverse-route geometries, route legs, coefficient identifications, and strong-cartesian qualifications from the actual source geometry family.
  selection_reason: The revision-4 compatible locus must be independent of raw authored route legs. This source-only spine is the common domain required before cartesian comparator pullback, endpoint isomorphisms, or solution transport can be stated without certificate escape.
  expected_result_type: target-proof-checkpoint
  lean_targets: [ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCompatibleInput.lean]
  risks: [reusing raw legData, storing a route comparator or cartesianness certificate, duplicating a raw cochain, confusing coefficient type equality with morphism identity]
  unchecked: [cartesian pullback and exactification of the source comparator and inverse, map-id and map-mul, finite generated route transports, endpoint comparison isomorphisms, solution equivalence, named positive and negative artifacts, clauses (c)--(d)]
result:
  proposed_result_type: target-proof-checkpoint
  proof_obligation_delta: A source-only compatible input now fixes the finite presentation, root reachability, actual target-fiber diagram, source geometry family, and exactly one fixed-coefficient G-109 transport. Both reverse-route geometries and literal legs are generated pointwise by the G-112/G-114 cleavage, retain the coefficient ring, and are proved strongly Cartesian without input fields or theorem arguments.
  completion_candidate: no
  lean_artifacts: [UpperGeometryCompatibleProblemInputData, UpperGeometryCompatibleProblemInput, sourceTargetGeometryAt, generatedBaseRouteGeometryAt, generatedPulledRouteGeometryAt, generatedBaseRouteLegAt, generatedPulledRouteLegAt, generatedBaseRouteLegAt_isStronglyCartesian, generatedPulledRouteLegAt_isStronglyCartesian, generatedBaseRouteGeometryAt_coefficient_eq, generatedPulledRouteGeometryAt_coefficient_eq]
  evidence: [focused Lean check, 41-declaration namespace standard-axiom audit, module registration, source hash, literal scans]
  source_sha256:
    UpperGeometryCompatibleInput.lean: 2ad1afce030e76d60f9a315219e32df3fcb00b932b4b8224fa26d59bf8ff188f
  claim_mapping:
    theorem_names: [generatedBaseRouteLegAt_isStronglyCartesian, generatedPulledRouteLegAt_isStronglyCartesian]
    source_labels: [revision 4 compatible-input boundary, target theorem clause (b)]
    conjuncts: [source-only finite input, two generated literal route geometries and legs, theorem-derived strong cartesianness, retained coefficient ring]
    undischarged_assumptions: [cartesian comparator pullback laws, generated finite route transports, endpoint comparison isomorphisms, solution equivalence and downstream artifacts]
    acceptance_point: This cycle fixes only the certificate-free domain and generated route spine. It does not claim comparator pullback, endpoint inverses, or solution equivalence; those remain explicit successor obligations.
    port_status: not-applicable
audits:
  premise_delta:
    ambient_boundary: [completed G-112 exact and G-114 realized-refinement cleavages, G-109 source transport]
    direction_hypothesis: []
    discharged: [certificate-free source input, both literal generated route geometries and legs, both theorem-derived strong-cartesian qualifications, coefficient-ring retention]
    remaining: [cartesian comparator pullback and laws, endpoint comparison isomorphisms, solution equivalence, named artifacts, paired orbit/cochain and exchange-exact interface]
  certificate_provenance:
    discharged: [both route qualifications are inherited from the explicit G-115 exact and realized-refinement cleavage constructors rather than stored or caller-supplied]
    unresolved: [source comparator pullback, endpoint inverse uniqueness, solution transports]
  proof_use:
    used: [sourceFiberDiagram objects, sourceGeometry, UpperGeometryCleavage.baseRouteGeometry, UpperGeometryCleavage.pulledRouteGeometry, UpperGeometryCleavage.baseRouteGeometryHom, UpperGeometryCleavage.pulledRouteGeometryHom, baseRouteGeometryHom_isStronglyCartesian, pulledRouteGeometryHom_isStronglyCartesian]
    unused: [root, rootPath, and sourceTransport are retained for successor finite-path, edge, and comparator constructions but are not consumed by this pointwise route-spine proof]
  structure_field_escape: the input has no generated route leg, route comparator, endpoint comparison, IsIso, generated-route cartesianness certificate, solution, or raw cochain field; sourceTransport contains only the permitted G-109 source-edge cocartesianness qualifications and its single authored source comparator
  route_integrity: both pointwise routes target the literal source geometry and are generated by the active retargeted G-112/G-114 context in the required two orders
  predecessor_integrity: completed G-112 and G-114 implementation files remain unchanged
  target_fitting: none-found
  vacuity: pending downstream named fixtures
  one_way_as_equivalence: not-claimed
  goal_or_report_reinterpretation: none-found
  validation_refs: [research/lean/check_research_modules.sh --focused ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCompatibleInput.lean => exit 0 and 41 declarations standard axioms only; module registered in research/lean/research-modules.txt and ResearchLean/AG/DoctrineFiberProduct.lean; git diff --check => exit 0; placeholder, hidden/BiDi, privacy, and reverse-import scans => no matches]
  blocking_findings: []
  next_obligation: Construct the G-115-local two-stage cartesian pullback and exactification of the source comparator and inverse on both generated routes, including map-id and map-mul.
```

## Cycle 30 — package stage of cartesian comparator pullback

```yaml
ledger_type: target_cycle_result
goal: G-115-aat-upper-stage-lift
cycle: 30
goal_blob_sha: fcd33815da27d5e1390b101223de49173967a349ad5f2e85324ec3b8d25b597c
base_oid: 40cf37a3786af3a203b56632596c3292ff9e2c04
tracking_issue: 4250
report_path: research/reports/G-115-aat-upper-stage-lift.md
selection:
  proof_state_ref: Cycle 29 merged the certificate-free source input and both theorem-qualified generated route legs
  proof_dag_predecessors: [UpperGeometryCompatibleProblemInputData, baseRouteGeometryBase_isStronglyCartesian, pulledRouteGeometryBase_isStronglyCartesian, CompositeFiberAut.hom_base_base_eq, IsStronglyCartesian.map, exactPackageToRefinement]
  proof_obligation: Pull the package map of an arbitrary source CompositeFiberAut along each generated strongly Cartesian route, prove both factor laws and pointed-identity projections, and exactify both universal factors to PackageTotalHom.
  selection_reason: CompositeFiberAut is vertical only after the pointed projection, not necessarily after geometryProjection. The package pullback must therefore be exposed and checked before the geometry-stage pullback can be typed without a false verticality inference.
  expected_result_type: target-proof-checkpoint
  lean_targets: [ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCompatibleComparator.lean]
  risks: [skipping the package stage, using G-109 covariant map on a contravariant refinement route, accepting a cartesianness argument, treating source automorphism base as a package identity]
  unchecked: [geometry-stage pullback and exactification, generated CompositeFiberAut inverse laws, map-id and map-mul, compositor/unitor compatibility, finite route comparator families and derived cochain, endpoint comparison isomorphisms, solution equivalence, named artifacts, clauses (c)--(d)]
result:
  proposed_result_type: target-proof-checkpoint
  proof_obligation_delta: Both generated reverse routes now canonically pull back the package map of any source CompositeFiberAut by their theorem-derived strong-cartesian universal property. Each factor has a proved route factorization and lies over the exact pointed identity, so a local exactification recovers an exact PackageTotalHom without assuming that the source geometry automorphism is already package-vertical.
  completion_candidate: no
  lean_artifacts: [exactPackageHomOfRefinement, exactPackageHomOfRefinement_base, exactPackageHomOfRefinement_toRefinement, generatedBasePackageComparatorCandidateAt, generatedBasePackageComparatorCandidateAt_base, generatedBasePackageComparatorRefinementAt, generatedBasePackageComparatorRefinementAt_fac, generatedBasePackageComparatorRefinementAt_base, generatedBasePackageComparatorAt, generatedBasePackageComparatorAt_toRefinement, generatedPulledPackageComparatorCandidateAt, generatedPulledPackageComparatorCandidateAt_base, generatedPulledPackageComparatorRefinementAt, generatedPulledPackageComparatorRefinementAt_fac, generatedPulledPackageComparatorRefinementAt_base, generatedPulledPackageComparatorAt, generatedPulledPackageComparatorAt_toRefinement]
  evidence: [focused Lean check, 17-declaration namespace standard-axiom audit, targeted direct-predecessor module construction, module registration, source hash, literal scans]
  source_sha256:
    UpperGeometryCompatibleComparator.lean: e662de8a482e90a0ca7d877c7aa995c64a4be7bb059c33a6b1fe55809585929a
  claim_mapping:
    theorem_names: [generatedBasePackageComparatorCandidateAt_base, generatedBasePackageComparatorRefinementAt_fac, generatedBasePackageComparatorRefinementAt_base, generatedBasePackageComparatorAt_toRefinement, generatedPulledPackageComparatorCandidateAt_base, generatedPulledPackageComparatorRefinementAt_fac, generatedPulledPackageComparatorRefinementAt_base, generatedPulledPackageComparatorAt_toRefinement]
    source_labels: [revision 4 cartesian comparator pullback, target theorem clause (b)]
    conjuncts: [two package-stage cartesian pullbacks, pointed verticality, two route factor laws, exact package recovery]
    undischarged_assumptions: [geometry-stage pullback, inverse and group laws, finite comparator transport and global mate equation, endpoint isomorphisms and solution equivalence]
    acceptance_point: The constructors accept an arbitrary source CompositeFiberAut but no route, cartesianness, comparison, or solution certificate. Passing its group inverse to the same API supplies the inverse-side package factor; proving that the geometry factors form an automorphism remains a successor obligation.
    port_status: not-applicable
audits:
  premise_delta:
    ambient_boundary: [Cycle 29 compatible input, G-109 source CompositeFiberAut, completed G-112/G-114 generated route cleavages]
    direction_hypothesis: []
    discharged: [package-stage pullback on both routes, pointed identity projection, exact PackageTotalHom recovery, both package factor laws]
    remaining: [geometry-stage exact pullback, generated comparator group laws, finite comparator/cochain/global equation, endpoint isomorphisms, solution equivalence, named artifacts and clauses (c)--(d)]
  certificate_provenance:
    discharged: [route cartesianness comes from Cycle 29 predecessors; factors come from IsStronglyCartesian.map; exact lower identity follows from CompositeFiberAut.hom_base_base_eq; exactification reuses the complete universal factor upper map]
    unresolved: [geometry inverse laws, endpoint inverse uniqueness, solution transports]
  proof_use:
    used: [CompositeFiberAut.hom_base_base_eq, baseRouteGeometryBase_isStronglyCartesian, pulledRouteGeometryBase_isStronglyCartesian, IsStronglyCartesian.map, IsStronglyCartesian.fac, IsHomLift.eq_of_isHomLift, exactPointedToRefinement, exactPackageToRefinement]
    unused: [root and rootPath; source edge and two-cell fields are reserved for successor finite transport]
  structure_field_escape: no package factor, route cartesianness, generated comparator, comparison, solution, or cochain is stored in the input or accepted as a theorem argument
  route_integrity: base and pulled factors use the two literal Cycle 29 legs at the actual retargeted source object; neither route is reconstructed from the other
  predecessor_integrity: completed G-112/G-114 implementation and GOAL files are unchanged
  target_fitting: none-found
  vacuity: pending downstream named fixtures
  one_way_as_equivalence: no automorphism or solution equivalence is claimed at this package-only checkpoint
  goal_or_report_reinterpretation: none-found
  validation_refs: [targeted `lake build ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleInput` constructed only the direct predecessor DAG; `check_research_modules.sh --focused ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCompatibleComparator.lean` => exit 0 and 17 declarations standard axioms only; git diff --check => exit 0; placeholder, hidden/BiDi, privacy, and reverse-import scans => no matches]
  blocking_findings: []
  next_obligation: Use each exact package factor as the lower map for the second IsStronglyCartesian.map at refinementGeometryProjection, exactify the geometry factor, and prove hom/inverse laws to obtain both generated CompositeFiberAut families.
```

## Cycle 31 — geometry-stage pullback and generated automorphisms

```yaml
ledger_type: target_cycle_result
goal: G-115-aat-upper-stage-lift
cycle: 31
goal_blob_sha: fcd33815da27d5e1390b101223de49173967a349ad5f2e85324ec3b8d25b597c
base_oid: 5bd2304d48d916b6705539bd832810597e85a4e3
tracking_issue: 4250
report_path: research/reports/G-115-aat-upper-stage-lift.md
selection:
  proof_state_ref: Cycle 30 merged both package-stage universal factors, factor laws, pointed verticality, and exact package recovery
  proof_dag_predecessors: [generatedBasePackageComparatorAt, generatedPulledPackageComparatorAt, generatedBaseRouteLegAt_isStronglyCartesian, generatedPulledRouteLegAt_isStronglyCartesian, exactGeometryHomOfRefinement, IsStronglyCartesian.map, IsStronglyCartesian.ext]
  proof_obligation: Use each exact package factor as the lower map for the second strongly Cartesian pullback, exactify both complete geometry factors, pull back the source inverse, prove both inverse laws at the package and geometry levels, and package the results as generated CompositeFiberAut families.
  selection_reason: A source CompositeFiberAut is vertical only after both projections. Cycle 30 discharged the package stage; the geometry stage and its inverse laws must now be generated from the literal route universal properties before any map law or finite comparator family can be stated honestly.
  expected_result_type: target-proof-checkpoint
  lean_targets: [ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCompatibleComparatorGeometry.lean]
  risks: [treating the package factor as an input certificate, omitting the inverse pullback, proving inverse laws only after forgetting complete geometry data, collapsing the two routes, claiming map-id or map-mul without proof]
  unchecked: [map-id and map-mul for both generated automorphism families, compositor/unitor compatibility, finite route comparator families and derived cochain, global mate equation, endpoint comparison isomorphisms, solution equivalence, named artifacts, clauses (c)--(d)]
result:
  proposed_result_type: target-proof-checkpoint
  proof_obligation_delta: Both generated routes now perform the second strongly Cartesian pullback over their exact Cycle 30 package factors. The complete refinement-geometry factors are exactified without losing local reading data. Pulling the same construction back on the source inverse and applying Cartesian uniqueness at both projection levels proves both inverse laws, yielding actual generated CompositeFiberAut values with exposed forward, inverse, and route-factorization theorems.
  completion_candidate: no
  lean_artifacts: [generatedBaseGeometryComparatorCandidateAt, generatedBaseGeometryComparatorCandidateAt_base, generatedBaseGeometryComparatorRefinementAt, generatedBaseGeometryComparatorRefinementAt_fac, generatedBaseGeometryComparatorRefinementAt_base, generatedBaseGeometryComparatorAt, generatedBaseGeometryComparatorAt_toRefinement, generatedBaseGeometryComparatorAt_fac, generatedBasePackageComparatorRefinementAt_hom_inv, generatedBasePackageComparatorRefinementAt_inv_hom, generatedBasePackageComparatorAt_hom_inv, generatedBasePackageComparatorAt_inv_hom, generatedBaseGeometryComparatorRefinementAt_hom_inv, generatedBaseGeometryComparatorRefinementAt_inv_hom, generatedBaseGeometryComparatorAt_hom_inv, generatedBaseGeometryComparatorAt_inv_hom, generatedBaseCompositeFiberAutAt, generatedBaseCompositeFiberAutAt_hom, generatedBaseCompositeFiberAutAt_inv, generatedBaseCompositeFiberAutAt_fac, generatedPulledGeometryComparatorCandidateAt, generatedPulledGeometryComparatorCandidateAt_base, generatedPulledGeometryComparatorRefinementAt, generatedPulledGeometryComparatorRefinementAt_fac, generatedPulledGeometryComparatorRefinementAt_base, generatedPulledGeometryComparatorAt, generatedPulledGeometryComparatorAt_toRefinement, generatedPulledGeometryComparatorAt_fac, generatedPulledPackageComparatorRefinementAt_hom_inv, generatedPulledPackageComparatorRefinementAt_inv_hom, generatedPulledPackageComparatorAt_hom_inv, generatedPulledPackageComparatorAt_inv_hom, generatedPulledGeometryComparatorRefinementAt_hom_inv, generatedPulledGeometryComparatorRefinementAt_inv_hom, generatedPulledGeometryComparatorAt_hom_inv, generatedPulledGeometryComparatorAt_inv_hom, generatedPulledCompositeFiberAutAt, generatedPulledCompositeFiberAutAt_hom, generatedPulledCompositeFiberAutAt_inv, generatedPulledCompositeFiberAutAt_fac]
  evidence: [focused Lean check, 40-declaration namespace standard-axiom audit, targeted direct-predecessor module construction, module registration, source hash, literal scans]
  source_sha256:
    UpperGeometryCompatibleComparatorGeometry.lean: b18c482911467c29542c98d8009e8baca7a6e7e22c9f72f429370585caa834f8
  claim_mapping:
    theorem_names: [generatedBaseGeometryComparatorCandidateAt_base, generatedBaseGeometryComparatorRefinementAt_fac, generatedBaseGeometryComparatorRefinementAt_base, generatedBaseGeometryComparatorAt_toRefinement, generatedBasePackageComparatorAt_hom_inv, generatedBasePackageComparatorAt_inv_hom, generatedBaseGeometryComparatorAt_hom_inv, generatedBaseGeometryComparatorAt_inv_hom, generatedBaseCompositeFiberAutAt_fac, generatedPulledGeometryComparatorCandidateAt_base, generatedPulledGeometryComparatorRefinementAt_fac, generatedPulledGeometryComparatorRefinementAt_base, generatedPulledGeometryComparatorAt_toRefinement, generatedPulledPackageComparatorAt_hom_inv, generatedPulledPackageComparatorAt_inv_hom, generatedPulledGeometryComparatorAt_hom_inv, generatedPulledGeometryComparatorAt_inv_hom, generatedPulledCompositeFiberAutAt_fac]
    source_labels: [revision 4 cartesian comparator pullback, target theorem clause (b)]
    conjuncts: [two geometry-stage cartesian pullbacks, exact complete geometry recovery, package and geometry inverse laws in both orders, two generated CompositeFiberAut families, two literal route factor laws]
    undischarged_assumptions: [functorial map laws, finite comparator transport and global mate equation, endpoint isomorphisms and solution equivalence]
    acceptance_point: The generated automorphisms contain only theorem-generated exact factors and their separately pulled-back inverses. Their inverse laws are proved through both package and geometry universal properties. No map-id, map-mul, finite naturality, endpoint comparison, or solution equivalence is claimed in this cycle.
    port_status: not-applicable
audits:
  premise_delta:
    ambient_boundary: [Cycle 29 compatible input, Cycle 30 exact package factors, completed G-112/G-114 generated route cleavages, G-109 source CompositeFiberAut]
    direction_hypothesis: []
    discharged: [geometry-stage pullback on both routes, exact GeometryTotalHom recovery, source inverse pullback, package inverse laws, geometry inverse laws, generated CompositeFiberAut construction, both forward factor laws]
    remaining: [map-id and map-mul, compositor/unitor compatibility, finite comparator/cochain/global equation, endpoint isomorphisms, solution equivalence, named artifacts and clauses (c)--(d)]
  certificate_provenance:
    discharged: [geometry factors come from IsStronglyCartesian.map over the exact Cycle 30 lower maps; inverse laws come from IsStronglyCartesian.ext and the source Aut hom_inv_id; exactification re-embeds to the complete universal factors]
    unresolved: [functoriality laws, endpoint inverse uniqueness, solution transports]
  proof_use:
    used: [generatedBasePackageComparatorAt, generatedPulledPackageComparatorAt, generatedBaseRouteLegAt_isStronglyCartesian, generatedPulledRouteLegAt_isStronglyCartesian, IsStronglyCartesian.map, IsStronglyCartesian.fac, IsStronglyCartesian.ext, exactGeometryHomOfRefinement, exactGeometryToRefinementGeometry_faithful, CompositeFiberAut.hom, CompositeFiberAut.inv, Aut.hom_inv_id]
    unused: [root and rootPath; source edge and two-cell fields remain reserved for successor finite transport and global comparator construction]
  structure_field_escape: no geometry factor, inverse, route cartesianness, generated automorphism, comparison, solution, or cochain is stored in the input or accepted as a theorem argument
  route_integrity: base and pulled automorphisms are constructed independently from their two literal generated route legs; each inverse is obtained by rerunning the same two-stage universal construction on the source group inverse
  predecessor_integrity: completed G-112/G-114 implementation and GOAL files are unchanged
  target_fitting: none-found
  vacuity: pending downstream named fixtures
  one_way_as_equivalence: the generated endomorphisms are promoted to automorphisms only after both inverse compositions are proved at complete geometry level
  goal_or_report_reinterpretation: none-found
  validation_refs: [targeted `lake build ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleComparator` constructed only the direct predecessor DAG; `check_research_modules.sh --focused ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCompatibleComparatorGeometry.lean` => exit 0 and 40 declarations standard axioms only; git diff --check => exit 0; placeholder, hidden/BiDi, privacy, and reverse-import scans => no matches]
  blocking_findings: []
  next_obligation: Prove map-id and map-mul for both generated CompositeFiberAut families from the same route factorization and Cartesian uniqueness, then assemble the finite comparator families and global mate equation.
```

## Cycle 32 — functorial laws for generated comparator pullback

```yaml
ledger_type: target_cycle_result
goal: G-115-aat-upper-stage-lift
cycle: 32
goal_blob_sha: fcd33815da27d5e1390b101223de49173967a349ad5f2e85324ec3b8d25b597c
base_oid: eca54d47a78f452c5b764666315250b3b23e7585
tracking_issue: 4250
report_path: research/reports/G-115-aat-upper-stage-lift.md
selection:
  proof_state_ref: Cycle 31 merged the two exact geometry pullbacks, inverse laws, actual generated CompositeFiberAut values, and literal route factor laws
  proof_dag_predecessors: [generatedBaseCompositeFiberAutAt, generatedPulledCompositeFiberAutAt, generatedBasePackageComparatorRefinementAt_fac, generatedPulledPackageComparatorRefinementAt_fac, generatedBaseGeometryComparatorRefinementAt_fac, generatedPulledGeometryComparatorRefinementAt_fac, generatedBaseRouteLegAt_isStronglyCartesian, generatedPulledRouteLegAt_isStronglyCartesian, exactPackageToRefinement, exactGeometryToRefinementGeometry]
  proof_obligation: Prove identity and multiplication preservation for both generated comparator pullbacks, first at the exact package level and then at complete exact geometry level, promote both pointwise constructions to group homomorphisms, and do so without accepting any map-law certificate.
  selection_reason: The finite comparator families must be derived by applying a lawful G-115-local pullback to the single source comparator. Package map laws are required material premises for the geometry-level Cartesian uniqueness proof and cannot be skipped or inferred from pointed verticality alone.
  expected_result_type: target-proof-checkpoint
  lean_targets: [ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCompatibleComparatorMapLaws.lean]
  risks: [reversing the Aut multiplication order, proving geometry map laws without matching complete package lower maps, using definitional equality in place of Cartesian uniqueness, collapsing base and pulled routes, storing map laws in the input]
  unchecked: [two-stage compositor/unitor compatibility for finite source paths and cells, finite base/pulled comparator families and derived cochains, route naturality, global canonical-mate equation, endpoint comparison isomorphisms, solution equivalence, named artifacts, clauses (c)--(d)]
result:
  proposed_result_type: target-proof-checkpoint
  proof_obligation_delta: Both route pullbacks now preserve identity and multiplication. Each package law is derived by strong-cartesian uniqueness against the literal package leg; each complete geometry law consumes the corresponding package law as its lower-map qualification and then applies strong-cartesian uniqueness against the literal geometry leg. The resulting base and pulled pointwise maps are bundled as actual group homomorphisms.
  completion_candidate: no
  lean_artifacts: [generatedBasePackageComparatorAt_one, generatedBasePackageComparatorAt_mul, generatedPulledPackageComparatorAt_one, generatedPulledPackageComparatorAt_mul, generatedBaseGeometryComparatorAt_one, generatedBaseGeometryComparatorAt_mul, generatedPulledGeometryComparatorAt_one, generatedPulledGeometryComparatorAt_mul, generatedBaseCompositeFiberAutAt_one, generatedBaseCompositeFiberAutAt_mul, generatedPulledCompositeFiberAutAt_one, generatedPulledCompositeFiberAutAt_mul, generatedBaseCompositeFiberAutHomAt, generatedPulledCompositeFiberAutHomAt, generatedBaseCompositeFiberAutHomAt_apply, generatedPulledCompositeFiberAutHomAt_apply]
  evidence: [focused Lean check, 16-declaration namespace standard-axiom audit, module registration, source hash, literal scans]
  source_sha256:
    UpperGeometryCompatibleComparatorMapLaws.lean: f296a5fda755b4eb6372a6cdbfe2d7251f27e74ebddeae050a74a88fdd402795
  claim_mapping:
    theorem_names: [generatedBasePackageComparatorAt_one, generatedBasePackageComparatorAt_mul, generatedPulledPackageComparatorAt_one, generatedPulledPackageComparatorAt_mul, generatedBaseGeometryComparatorAt_one, generatedBaseGeometryComparatorAt_mul, generatedPulledGeometryComparatorAt_one, generatedPulledGeometryComparatorAt_mul, generatedBaseCompositeFiberAutAt_one, generatedBaseCompositeFiberAutAt_mul, generatedPulledCompositeFiberAutAt_one, generatedPulledCompositeFiberAutAt_mul]
    source_labels: [revision 4 cartesian comparator pullback, target theorem clause (b)]
    conjuncts: [package map-id and map-mul on both routes, complete geometry map-id and map-mul on both routes, generated CompositeFiberAut map-id and map-mul on both routes, two bundled group homomorphisms]
    undischarged_assumptions: [finite compositor/unitor normalization, finite comparator transport and global mate equation, endpoint isomorphisms and solution equivalence]
    acceptance_point: The multiplication theorem follows the actual Aut convention hom(left * right) = hom(right) ≫ hom(left). Both factor compositions are compared through their literal generated route leg. The geometry proof explicitly uses the proved package multiplication equality to put both complete factors over the same package morphism.
    port_status: not-applicable
audits:
  premise_delta:
    ambient_boundary: [Cycle 31 generated automorphisms and factor laws, G-109 source CompositeFiberAut group laws, completed G-112/G-114 generated route cleavages]
    direction_hypothesis: []
    discharged: [package map-id and map-mul on both routes, geometry map-id and map-mul on both routes, CompositeFiberAut map-id and map-mul on both routes, group-homomorphism bundling]
    remaining: [finite compositor/unitor compatibility, finite comparator/cochain/global equation, endpoint isomorphisms, solution equivalence, named artifacts and clauses (c)--(d)]
  certificate_provenance:
    discharged: [all map laws come from literal route factor laws, source group identity/multiplication, theorem-derived route cartesianness, and IsStronglyCartesian.ext; no law is accepted as an input]
    unresolved: [finite route naturality and canonical-mate compatibility, endpoint inverse uniqueness, solution transports]
  proof_use:
    used: [generatedBasePackageComparatorRefinementAt_fac, generatedPulledPackageComparatorRefinementAt_fac, generatedBaseGeometryComparatorRefinementAt_fac, generatedPulledGeometryComparatorRefinementAt_fac, generatedBasePackageComparatorAt_one, generatedBasePackageComparatorAt_mul, generatedPulledPackageComparatorAt_one, generatedPulledPackageComparatorAt_mul, IsStronglyCartesian.ext, exactPackageToRefinement_map_injective, exactGeometryToRefinementGeometry_faithful, CompositeFiberAut multiplication order]
    unused: [root and rootPath; source edge and two-cell fields remain reserved for the next finite-family and global-equation construction]
  structure_field_escape: no map-id, map-mul, route, cartesianness, comparator family, comparison, solution, or cochain certificate is stored in the input or accepted as a theorem argument
  route_integrity: base and pulled laws independently use their own package and geometry factors and their own literal strong-cartesian route legs
  predecessor_integrity: completed G-112/G-114 implementation and GOAL files are unchanged
  target_fitting: none-found
  vacuity: pending downstream named fixtures
  one_way_as_equivalence: pointwise pullbacks are bundled only as group homomorphisms; no route-between isomorphism or solution equivalence is claimed
  goal_or_report_reinterpretation: none-found
  validation_refs: [`check_research_modules.sh --focused ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCompatibleComparatorMapLaws.lean` => exit 0 and 16 declarations standard axioms only; module registered in research/lean/research-modules.txt and ResearchLean/AG/DoctrineFiberProduct.lean; git diff --check => exit 0; placeholder, hidden/BiDi, privacy, and reverse-import scans => no matches]
  blocking_findings: []
  next_obligation: Apply the two generated group homomorphisms to the single source transport comparator, prove the finite path/cell compositor-unitor compatibility and route naturality, derive both comparator families and cochains, and establish the constructor-level global canonical-mate equation.
```

## Cycle 33 — finite comparator families from the single source comparator

```yaml
ledger_type: target_cycle_result
goal: G-115-aat-upper-stage-lift
cycle: 33
goal_blob_sha: fcd33815da27d5e1390b101223de49173967a349ad5f2e85324ec3b8d25b597c
base_oid: f03ac77e9c2302788a00f6a2c7ab7a6ba2bf8974
tracking_issue: 4250
report_path: research/reports/G-115-aat-upper-stage-lift.md
selection:
  proof_state_ref: Cycle 32 merged two lawful group homomorphisms pulling source CompositeFiberAut values onto the generated base and pulled endpoints
  proof_dag_predecessors: [generatedBaseCompositeFiberAutHomAt, generatedPulledCompositeFiberAutHomAt, generatedBaseCompositeFiberAutAt_fac, generatedPulledCompositeFiberAutAt_fac, FixedCoefficientTwoLayerTransportOver.comparator]
  proof_obligation: Apply both generated group homomorphisms to the sole authored comparator family stored in sourceTransport, expose the resulting dependent finite comparator families, and prove that each family factors its own literal generated route leg through that same authored source comparator.
  selection_reason: Revision 4 forbids base and pulled comparators as input fields. The first finite constructor step must therefore visibly consume sourceTransport.comparator and produce both route families independently before route transport data or cochains are assembled.
  expected_result_type: target-proof-checkpoint
  lean_targets: [ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCompatibleFiniteComparators.lean]
  risks: [copying the source comparator without cartesian pullback, storing route comparator certificates in the input, using one generated route family for both routes, hiding authored-comparator use behind an opaque wrapper, claiming a cochain before route transport data exists]
  unchecked: [generated route edge transports and G-109 qualifications, two-cell path compatibility, finite compositor/unitor compatibility, derived route cochains, route naturality, global canonical-mate equation, endpoint comparison isomorphisms, solution equivalence, named artifacts, clauses (c)--(d)]
result:
  proposed_result_type: target-proof-checkpoint
  proof_obligation_delta: The single sourceTransport.comparator family now generates separate base-first and pulled-first CompositeFiberAut families at every two-cell target. Both output families are evaluations of the Cycle 32 group homomorphisms, and their explicit factor laws show that each literal generated route leg followed by the authored source comparator is exactly the corresponding pulled-back comparator followed by that route leg.
  completion_candidate: no
  lean_artifacts: [generatedBaseRouteComparator, generatedPulledRouteComparator, generatedBaseRouteComparator_apply, generatedPulledRouteComparator_apply, generatedBaseRouteComparator_fac, generatedPulledRouteComparator_fac]
  evidence: [focused Lean check, 6-declaration namespace standard-axiom audit, targeted direct-predecessor module construction, module registration, source hash, literal scans]
  source_sha256:
    UpperGeometryCompatibleFiniteComparators.lean: c8ee9a431ba5ab9cc9aa1350917ddcfb14c8abfe2d06db8434331ee6f3880adf
  claim_mapping:
    theorem_names: [generatedBaseRouteComparator_apply, generatedPulledRouteComparator_apply, generatedBaseRouteComparator_fac, generatedPulledRouteComparator_fac]
    source_labels: [revision 4 cartesian-compatible finite comparator constructor, target theorem clause (b)]
    conjuncts: [base finite comparator family, pulled finite comparator family, literal base route factor law, literal pulled route factor law, authored source comparator proof-use]
    undischarged_assumptions: [generated finite route transports and their G-109 qualifications, path/cell normalization, route cochains and global mate equation, endpoint isomorphisms and solution equivalence]
    acceptance_point: Each output is defined by evaluating its route-specific generated group homomorphism on input.sourceTransport.comparator cell. The factor-law right sides contain that same authored comparator literally; no independent route comparator is accepted from a caller.
    port_status: not-applicable
audits:
  premise_delta:
    ambient_boundary: [Cycle 32 generated group homomorphisms, the single fixed-coefficient source transport and its authored comparator family]
    direction_hypothesis: []
    discharged: [dependent base comparator family, dependent pulled comparator family, both authored-comparator factor laws]
    remaining: [generated edge transports and cocartesian qualifications, finite compositor/unitor and two-cell compatibility, derived cochains, global equation, endpoint isomorphisms, solution equivalence, named artifacts and clauses (c)--(d)]
  certificate_provenance:
    discharged: [both comparator families come only from the Cycle 32 theorem-generated homomorphisms applied to sourceTransport.comparator; both factor laws specialize the Cycle 31 literal route laws]
    unresolved: [route edge qualification, finite path compatibility and cochain laws, endpoint inverse uniqueness, solution transports]
  proof_use:
    used: [sourceTransport.comparator, generatedBaseCompositeFiberAutHomAt, generatedPulledCompositeFiberAutHomAt, generatedBaseCompositeFiberAutAt_fac, generatedPulledCompositeFiberAutAt_fac]
    unused: [root and rootPath; source edges and coefficient-identity fields remain reserved for construction of the generated route transports]
  structure_field_escape: the input still contains only one authored source comparator family; neither generated route comparator, factor law, route, cartesianness, cochain, comparison, or solution is stored or accepted as a theorem argument
  route_integrity: base and pulled families are evaluations of distinct route-specific homomorphisms and satisfy factor laws against distinct literal generated legs
  predecessor_integrity: completed G-112/G-114 implementation and GOAL files are unchanged
  target_fitting: none-found
  vacuity: pending downstream named fixtures
  one_way_as_equivalence: two finite families and their one-route factor laws are constructed; no route-between isomorphism or solution equivalence is claimed
  goal_or_report_reinterpretation: none-found
  validation_refs: [targeted `lake build ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleComparatorMapLaws` constructed only the direct predecessor DAG; `check_research_modules.sh --focused ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCompatibleFiniteComparators.lean` => exit 0 and 6 declarations standard axioms only; module registered in research/lean/research-modules.txt and ResearchLean/AG/DoctrineFiberProduct.lean; git diff --check => exit 0; placeholder, hidden/BiDi, privacy, and reverse-import scans => no matches]
  blocking_findings: []
  next_obligation: Generate the base and pulled finite edge transports from sourceTransport.edgeLift using the two literal cartesian route legs, prove exact lower projections, factor laws, coefficient identity and G-109 cocartesian qualifications, then combine those transports with the two generated comparator families to derive route cochains.
```

## Cycle 34 — generated route core diagrams and edge factor graphs

```yaml
ledger_type: target_cycle_result
goal: G-115-aat-upper-stage-lift
cycle: 34
goal_blob_sha: fcd33815da27d5e1390b101223de49173967a349ad5f2e85324ec3b8d25b597c
base_oid: 2b6b7a0c208dbbc4314d61d8162b51eb9bdaeae5
tracking_issue: 4250
report_path: research/reports/G-115-aat-upper-stage-lift.md
selection:
  proof_state_ref: Cycle 33 merged both finite comparator families generated from the sole authored source comparator
  proof_dag_predecessors: [sourceFiberDiagram, sourceTransport.edgeLift, sourceTransport.edge_base, generatedBaseRouteLegAt, generatedPulledRouteLegAt, baseRouteComparisonCoreIso, pulledRouteComparisonCoreIso, baseCompositeLegAt_naturality, pulledCompositeLegAt_naturality]
  proof_obligation: Conjugate the theorem-generated G-114 base and pulled core diagrams onto the literal route geometry endpoints, expose their actual edge maps, and prove that each edge factors its own literal route leg through the corresponding authored source edge without accepting a route transport or naturality certificate.
  selection_reason: A complete geometry edge lift must lie over an exact core edge with a proved route factor graph. Generating this lower layer first separates the G-114 exact diagrammatic input from the next geometry-cartesian pullback and prevents a stored route transport from entering the compatible input.
  expected_result_type: target-proof-checkpoint
  lean_targets: [ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCompatibleRouteCoreEdges.lean]
  risks: [reusing stored baseTransport or pulledTransport, replacing the source edge by an unrelated morphism, collapsing the two route diagrams, accepting a naturality certificate, claiming a geometry transport before the second cartesian pullback]
  unchecked: [complete generated geometry edge lifts, coefficient identity and G-109 cocartesian qualifications, path and two-cell compatibility, derived route cochains, global canonical-mate equation, endpoint comparison isomorphisms, solution equivalence, named artifacts, clauses (c)--(d)]
result:
  proposed_result_type: target-proof-checkpoint
  proof_obligation_delta: The two G-114 core diagrams are independently conjugated onto the pointwise base-first and pulled-first route endpoints. For every presented edge, each exact generated core map now factors its literal route leg through the actual sourceTransport edgeLift. The proofs use the theorem-generated naturality of the two composite route legs and rewrite the right side through sourceTransport.edge_base.
  completion_candidate: no
  lean_artifacts: [generatedBaseRouteCoreIsoAt, generatedPulledRouteCoreIsoAt, generatedBaseRouteCoreDiagram, generatedPulledRouteCoreDiagram, generatedBaseRouteCoreEdge_fac, generatedPulledRouteCoreEdge_fac]
  evidence: [focused Lean check, 6-declaration namespace standard-axiom audit, targeted direct-predecessor module construction, module registration, source hash, literal scans]
  source_sha256:
    UpperGeometryCompatibleRouteCoreEdges.lean: edcf51398915489e566936caeffe5c6428e3c00c7eaa546ebf6c7d592a1c1e6c
  claim_mapping:
    theorem_names: [generatedBaseRouteCoreEdge_fac, generatedPulledRouteCoreEdge_fac]
    source_labels: [revision 4 certificate-free route edge construction, target theorem clause (b)]
    conjuncts: [base route core endpoint comparison, pulled route core endpoint comparison, two functorial generated core diagrams, base source-edge factor graph, pulled source-edge factor graph]
    undischarged_assumptions: [geometry-stage edge pullbacks, G-109 edge qualifications and coefficient identity, finite path and cell coherence, route cochains and global mate equation, endpoint isomorphisms and solution equivalence]
    acceptance_point: Both edge maps are functorial conjugations of distinct G-114 core diagrams. Their factor laws terminate literally at input.sourceTransport.edgeLift edge, after sourceTransport.edge_base is used to connect the authored lift to the source diagram map. No route edge or naturality witness is an input field or theorem argument.
    port_status: not-applicable
audits:
  premise_delta:
    ambient_boundary: [Cycle 33 compatible input and comparators, completed G-114 base and pulled core diagrams, theorem-generated composite route-leg naturality, authored G-109 source edge lifts]
    direction_hypothesis: []
    discharged: [two exact endpoint comparison families, two generated core diagrams, both source-edge factor graphs]
    remaining: [complete geometry edge lifts, edge coefficient identity and G-109 cocartesian qualifications, finite path and two-cell compatibility, derived cochains and global equation, endpoint isomorphisms, solution equivalence, named artifacts and clauses (c)--(d)]
  certificate_provenance:
    discharged: [endpoint comparisons come from G-112/G-114 route comparison isomorphisms; edge maps are conjugations of actual G-114 diagrams; factor graphs come from baseCompositeLegAt_naturality or pulledCompositeLegAt_naturality plus sourceTransport.edge_base]
    unresolved: [geometry-stage cartesian edge pullback, edge cocartesianness and coefficient identity, cochain laws, endpoint inverse uniqueness, solution transports]
  proof_use:
    used: [sourceFiberDiagram, sourceTransport.edgeLift, sourceTransport.edge_base, baseRouteComparisonCoreIso, pulledRouteComparisonCoreIso, baseCompositeLegAt_naturality, pulledCompositeLegAt_naturality, baseRouteComparisonInv_fac, pulledRouteComparisonInv_fac, baseRouteComparisonHom_fac, pulledRouteComparisonHom_fac]
    unused: [root and rootPath; source comparator fields were consumed in Cycle 33 and are not needed for this lower edge layer]
  structure_field_escape: no route core diagram, edge, transport, naturality, cartesianness, cochain, comparison, or solution is stored in the input or accepted as a theorem argument
  route_integrity: base and pulled core diagrams are separate conjugations of the corresponding G-114 diagrams and each factor law uses its own literal generated route leg
  predecessor_integrity: completed G-112/G-114 implementation and GOAL files are unchanged
  target_fitting: none-found
  vacuity: pending downstream named fixtures
  one_way_as_equivalence: endpoint core isomorphisms are used only to conjugate diagrams; no route-between solution or solution-space equivalence is claimed
  goal_or_report_reinterpretation: none-found
  validation_refs: [targeted `lake build ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleFiniteComparators` constructed only the direct predecessor DAG; `check_research_modules.sh --focused ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCompatibleRouteCoreEdges.lean` => exit 0 and 6 declarations standard axioms only; module registered in research/lean/research-modules.txt and ResearchLean/AG/DoctrineFiberProduct.lean; git diff --check => exit 0; placeholder, hidden/BiDi, privacy, and reverse-import scans => no matches]
  blocking_findings: []
  next_obligation: Use each generated exact core edge and factor graph as the lower map for the strongly Cartesian geometry pullback, exactify the complete geometry edge, and prove its literal route factorization before assembling G-109 edge qualifications and route transports.
```

## Cycle 35 — complete generated route geometry edges

```yaml
ledger_type: target_cycle_result
goal: G-115-aat-upper-stage-lift
cycle: 35
goal_blob_sha: fcd33815da27d5e1390b101223de49173967a349ad5f2e85324ec3b8d25b597c
base_oid: ca3a5731a6dfd93d6055246073338507091bb5a4
tracking_issue: 4250
report_path: research/reports/G-115-aat-upper-stage-lift.md
selection:
  proof_state_ref: Cycle 34 merged both exact route core diagrams and their authored source-edge factor graphs
  proof_dag_predecessors: [generatedBaseRouteCoreDiagram, generatedPulledRouteCoreDiagram, generatedBaseRouteCoreEdge_fac, generatedPulledRouteCoreEdge_fac, generatedBaseRouteLegAt_isStronglyCartesian, generatedPulledRouteLegAt_isStronglyCartesian, exactGeometryHomOfRefinement]
  proof_obligation: Pull the authored source geometry edge independently through both literal strongly Cartesian route legs over the corresponding exact Cycle 34 core edges, prove the lower projections, exactify the complete geometry factors, and retain both literal source-edge factor graphs.
  selection_reason: G-109 route transports require actual GeometryTotalHom edge lifts. The complete geometry pullback must be generated before its coefficient identity and cocartesian qualifications can be audited.
  expected_result_type: target-proof-checkpoint
  lean_targets: [ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCompatibleRouteGeometryEdges.lean]
  risks: [accepting route cartesianness as an argument, losing the exact lower map during exactification, using a stored route transport, reversing the Cartesian factor law, claiming G-109 qualification before it is proved]
  unchecked: [coefficient identity and G-109 cocartesian qualifications, route transport path and two-cell laws, derived route cochains, global canonical-mate equation, endpoint comparison isomorphisms, solution equivalence, named artifacts, clauses (c)--(d)]
result:
  proposed_result_type: target-proof-checkpoint
  proof_obligation_delta: The same authored source geometry edge is independently pulled back through both theorem-generated strongly Cartesian route legs. Each universal refinement factor is proved to lie over its corresponding exact Cycle 34 core edge, exactified to a complete GeometryTotalHom, and shown to satisfy full literal route-leg naturality against that shared sourceTransport.edgeLift.
  completion_candidate: no
  lean_artifacts: [generatedBaseRouteRefinementGeometryEdge, generatedBaseRouteRefinementGeometryEdge_base, generatedBaseRouteGeometryEdge, generatedBaseRouteGeometryEdge_base, generatedBaseRouteGeometryEdge_toRefinement, generatedBaseRouteGeometryEdge_fac, generatedPulledRouteRefinementGeometryEdge, generatedPulledRouteRefinementGeometryEdge_base, generatedPulledRouteGeometryEdge, generatedPulledRouteGeometryEdge_base, generatedPulledRouteGeometryEdge_toRefinement, generatedPulledRouteGeometryEdge_fac]
  evidence: [focused Lean check, 12-declaration namespace standard-axiom audit, targeted direct-predecessor module construction, module registration, source hash, literal scans]
  source_sha256:
    UpperGeometryCompatibleRouteGeometryEdges.lean: e1674558f9e50642e8f7d880e0b2204cfe21b78bbb88c6843eea7ce710baeb59
  claim_mapping:
    theorem_names: [generatedBaseRouteRefinementGeometryEdge_base, generatedBaseRouteGeometryEdge_base, generatedBaseRouteGeometryEdge_toRefinement, generatedBaseRouteGeometryEdge_fac, generatedPulledRouteRefinementGeometryEdge_base, generatedPulledRouteGeometryEdge_base, generatedPulledRouteGeometryEdge_toRefinement, generatedPulledRouteGeometryEdge_fac]
    source_labels: [revision 4 certificate-free route edge construction, target theorem clause (b)]
    conjuncts: [two geometry-stage Cartesian pullbacks, exact lower projection laws, two complete exact geometry edges, two refinement recovery laws, two authored source-edge factor graphs]
    undischarged_assumptions: [G-109 coefficient identity and cocartesian qualifications, route path and cell coherence, cochains and global equation, endpoint isomorphisms and solution equivalence]
    acceptance_point: Each route edge is generated from the literal route leg's theorem-level strong cartesianness and the actual sourceTransport.edgeLift. The exact lower edge and full refinement factor are both exposed. No route edge, qualification, transport, or naturality certificate is an input or theorem argument.
    port_status: not-applicable
audits:
  premise_delta:
    ambient_boundary: [Cycle 34 exact core edges and factor graphs, theorem-generated route-leg strong cartesianness, authored source geometry edge lifts]
    direction_hypothesis: []
    discharged: [two refinement geometry pullbacks, exact lower projections, exact complete geometry edges, refinement recovery, both complete geometry factor laws]
    remaining: [coefficient identity and G-109 cocartesian qualifications, finite route transport coherence, derived cochains and global equation, endpoint isomorphisms, solution equivalence, named artifacts and clauses (c)--(d)]
  certificate_provenance:
    discharged: [refinement factors come from IsStronglyCartesian.map over the exact Cycle 34 lower maps; exactification uses the proved lower projection; factor laws come from IsStronglyCartesian.fac]
    unresolved: [edge cocartesianness and coefficient identity, path and cell laws, endpoint inverse uniqueness, solution transports]
  proof_use:
    used: [sourceTransport.edgeLift, generatedBaseRouteCoreEdge_fac, generatedPulledRouteCoreEdge_fac, generatedBaseRouteLegAt_isStronglyCartesian, generatedPulledRouteLegAt_isStronglyCartesian, IsStronglyCartesian.map, IsStronglyCartesian.fac, IsHomLift.eq_of_isHomLift, exactGeometryHomOfRefinement, exactGeometryHomOfRefinement_toRefinement]
    unused: [root and rootPath; comparator fields are reserved for route cochain assembly]
  structure_field_escape: no route edge, Cartesian qualification, transport, path law, cochain, comparison, or solution is stored in the input or accepted as a theorem argument
  route_integrity: base and pulled edges independently use their own core diagrams, factor laws, literal route legs, and theorem-generated Cartesian instances while sharing only the authored source edge
  predecessor_integrity: completed G-112/G-114 implementation and GOAL files are unchanged
  target_fitting: none-found
  vacuity: pending downstream named fixtures
  one_way_as_equivalence: complete edge morphisms and one-way factor laws are generated; no edge isomorphism, route-between endpoint isomorphism, or solution equivalence is claimed
  goal_or_report_reinterpretation: none-found
  validation_refs: [targeted `lake build ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleRouteCoreEdges` constructed only the direct predecessor DAG; `check_research_modules.sh --focused ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCompatibleRouteGeometryEdges.lean` => exit 0 and 12 declarations standard axioms only; module registered in research/lean/research-modules.txt and ResearchLean/AG/DoctrineFiberProduct.lean; git diff --check => exit 0; placeholder, hidden/BiDi, privacy, and reverse-import scans => no matches]
  blocking_findings: []
  next_obligation: Prove that both generated complete route edges retain coefficient identity and derive the G-109 cocartesian qualifications needed to assemble actual FixedCoefficientTwoLayerTransportOver values and their route cochains.
```

## Cycle 36 — canonical mate naturality on generated compatible routes

```yaml
ledger_type: target_cycle_result
goal: G-115-aat-upper-stage-lift
cycle: 36
goal_blob_sha: fcd33815da27d5e1390b101223de49173967a349ad5f2e85324ec3b8d25b597c
base_oid: 1edb23e4f07ef660d1fafb2a967bd503cf5bbe3a
tracking_issue: 4250
report_path: research/reports/G-115-aat-upper-stage-lift.md
selection:
  proof_state_ref: Cycle 35 merged both complete generated route geometry edges and their literal factor graphs through the same authored source edge
  proof_dag_predecessors: [generatedBaseRouteCoreIsoAt, generatedPulledRouteCoreIsoAt, generatedBaseRouteCoreDiagram, generatedPulledRouteCoreDiagram, generatedBaseRouteGeometryEdge, generatedPulledRouteGeometryEdge, generatedBaseRouteGeometryEdge_fac, generatedPulledRouteGeometryEdge_fac, UpperGeometryCleavage.upperGeometryMate, UpperGeometryCleavage.generatedRouteCoreMate, ActiveRefinementBCContext.mate]
  proof_obligation: Conjugate the actual G-114 canonical mate onto the two generated compatible core diagrams, identify it with the theorem-generated exact core mate, prove path naturality, and lift that equation to complete geometry naturality along every generated route edge without accepting a route transport or naturality certificate.
  selection_reason: Coefficient equality for the generated endpoints is propositional rather than definitional, so packaging the route edges as fixed-coefficient G-109 transports requires a separate normalization step. The mate equation itself is already determined by the reviewed route comparisons and Cycle 35 factor graphs and can be discharged independently without weakening or assuming that downstream qualification.
  expected_result_type: target-proof-checkpoint
  lean_targets: [ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCompatibleMateNaturality.lean]
  risks: [replacing the actual G-114 mate by an unrelated pointwise map, proving only core naturality while claiming complete geometry naturality, accepting route naturality as an argument, using coefficient or cocartesian qualifications not yet proved, collapsing the two route diagrams]
  unchecked: [generated endpoint coefficient normalization, G-109 edge cocartesian qualifications, actual FixedCoefficientTwoLayerTransportOver route values, finite compositor/unitor and two-cell compatibility, derived route cochains, global canonical-mate equation, endpoint comparison isomorphisms, solution equivalence, named artifacts, clauses (c)--(d)]
result:
  proposed_result_type: target-proof-checkpoint
  proof_obligation_delta: The actual G-114 natural transformation component is conjugated through the two generated route-core endpoint isomorphisms and proved equal to the existing generated exact core mate after refinement embedding. Naturality of the G-114 mate therefore gives path naturality on the generated diagrams. The Cycle 35 geometry edge factor graphs and the pointwise mate triangles then lift the core equation by strong-cartesian uniqueness to a complete geometry naturality theorem for every authored edge.
  completion_candidate: no
  lean_artifacts: [generatedCompatibleUpperGeometryMateAt, generatedCompatibleUpperGeometryMateAt_base, generatedCompatibleUpperGeometryMateAt_triangle, generatedCompatibleConjugateCoreMateAt, generatedCompatibleConjugateCoreMateAt_toRefinement, generatedCompatibleConjugateCoreMateAt_eq_generated, generatedCompatibleConjugateCoreMateAt_naturality, generatedCompatibleRouteCoreMateAt_naturality, generatedCompatibleUpperGeometryMateAt_edge_naturality]
  evidence: [focused Lean check, 9-declaration namespace standard-axiom audit, targeted direct-predecessor module construction, module registration, source hash, literal scans]
  source_sha256:
    UpperGeometryCompatibleMateNaturality.lean: 8e54b0c80ceaa875eb65b02d174459f999d9f9223aabe5f2a523f21e633faa89
  claim_mapping:
    theorem_names: [generatedCompatibleUpperGeometryMateAt_base, generatedCompatibleUpperGeometryMateAt_triangle, generatedCompatibleConjugateCoreMateAt_toRefinement, generatedCompatibleConjugateCoreMateAt_eq_generated, generatedCompatibleConjugateCoreMateAt_naturality, generatedCompatibleRouteCoreMateAt_naturality, generatedCompatibleUpperGeometryMateAt_edge_naturality]
    source_labels: [revision 4 canonical-mate compatibility, target theorem clause (b)]
    conjuncts: [actual G-114 mate conjugation, equality with the generated exact core mate, path naturality on both generated route diagrams, complete geometry edge naturality]
    undischarged_assumptions: [endpoint coefficient normalization, G-109 cocartesian qualifications, fixed-coefficient route packaging, finite compositor/unitor and two-cell coherence, derived cochains and global equation, endpoint isomorphisms and solution equivalence]
    acceptance_point: The conjugated map contains ctx.mate.app literally. Its equality with the generated route mate is proved through the exact-package refinement embedding. Complete geometry naturality is proved from that core naturality, both Cycle 35 factor graphs, both pointwise route triangles, and strong-cartesian uniqueness; no route naturality equation is supplied by the caller.
    port_status: not-applicable
audits:
  premise_delta:
    ambient_boundary: [Cycle 34 generated core diagrams and endpoint isomorphisms, Cycle 35 generated geometry edges and factor graphs, completed G-114 canonical mate and G-115-local pointwise upper geometry mate]
    direction_hypothesis: []
    discharged: [G-114 mate conjugation, refinement-level identification, exact-core identification, path naturality, complete geometry edge naturality]
    remaining: [coefficient normalization, G-109 cocartesian qualifications, fixed-coefficient route construction, finite path and two-cell coherence, derived cochains and global equation, endpoint isomorphisms, solution equivalence, named artifacts and clauses (c)--(d)]
  certificate_provenance:
    discharged: [core naturality comes from ctx.mate.naturality and theorem-generated endpoint isomorphisms; exact-core identification comes from refinement faithfulness; geometry naturality comes from Cycle 35 factor laws, generated mate triangles, and IsStronglyCartesian.ext]
    unresolved: [coefficient equality transport, edge cocartesianness, cochain laws, endpoint inverse uniqueness, solution transports]
  proof_use:
    used: [ctx.mate.app, ctx.mate.naturality, generatedBaseRouteCoreIsoAt, generatedPulledRouteCoreIsoAt, UpperGeometryCleavage.transportedG114RefinementMate_eq_generated, UpperGeometryCleavage.generatedRouteCoreMate_toRefinement, generatedBaseRouteGeometryEdge_fac, generatedPulledRouteGeometryEdge_fac, generatedBaseRouteLegAt_isStronglyCartesian, generatedPulledRouteLegAt_isStronglyCartesian, IsStronglyCartesian.ext]
    unused: [root and rootPath; source coefficient identities and comparator fields remain reserved for fixed-coefficient route packaging and cochain construction]
  structure_field_escape: no conjugated mate, route naturality, coefficient normalization, edge qualification, route transport, cochain, comparison, or solution is stored in the input or accepted as a theorem argument
  route_integrity: the mate is transported between two separately generated core diagrams, and complete naturality uses each route's own edge and literal leg factorization
  predecessor_integrity: completed G-112/G-114 implementation and GOAL files are unchanged
  target_fitting: none-found
  vacuity: the theorem is universally quantified over every presented path or edge; named downstream fixtures remain pending
  one_way_as_equivalence: a pointwise mate and its naturality are proved; no mate invertibility, endpoint isomorphism, or solution equivalence is claimed
  goal_or_report_reinterpretation: none-found
  validation_refs: [targeted `lake build ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleRouteGeometryEdges` constructed only the direct predecessor DAG; `check_research_modules.sh --focused ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCompatibleMateNaturality.lean` => exit 0 and 9 declarations standard axioms only; module registered in research/lean/research-modules.txt and ResearchLean/AG/DoctrineFiberProduct.lean; git diff --check => exit 0; placeholder, hidden/BiDi, privacy, and reverse-import scans => no matches]
  blocking_findings: []
  next_obligation: Normalize the propositionally fixed generated endpoint coefficients and determine whether the existing G-109 APIs derive strong cocartesianness of the two cartesian-pulled route edges; package actual fixed-coefficient route transports if they do, or record the exact missing public preservation primitive after exhausting the relevant interfaces.
```

## Cycle 37 — vertical-source isomorphisms and generated core-edge qualification

```yaml
ledger_type: target_cycle_result
goal: G-115-aat-upper-stage-lift
cycle: 37
goal_blob_sha: fcd33815da27d5e1390b101223de49173967a349ad5f2e85324ec3b8d25b597c
base_oid: 7e2d43ed2818b50e0e24c96503fbc01f79ed988e
tracking_issue: 4250
report_path: research/reports/G-115-aat-upper-stage-lift.md
selection:
  proof_state_ref: Cycle 35 generated both route edges by Cartesian pullback; a proposed goal-defect in closed PR 4289 was vetoed because every authored source edge lies over the identity of one fixed core fiber
  proof_dag_predecessors: [sourceFiberDiagram, sourceTransport.edge_base, sourceTransport.edgeCoreStrong, sourceTransport.edgeGeometryStrong, IsStronglyCocartesian.isIso_of_base_isIso, coreFiberHom_isIso_of_total_isIso, generatedBaseRouteCoreDiagram, generatedPulledRouteCoreDiagram]
  proof_obligation: Prove that every authored source core and geometry edge is an isomorphism, transport that invertibility through both generated route core diagrams, and derive the core-stage strong-cocartesian qualifications required by the G-109 route contract without adding a Beck--Chevalley or edge-qualification certificate.
  selection_reason: Independent review of PR 4289 identified the fixed-fiber verticality that the rejected generic bifibration argument had omitted. This existing premise turns source strong-cocartesian edges into isomorphisms and opens a certificate-free route through functoriality, Cartesian cancellation, and exactification.
  expected_result_type: target-proof-checkpoint
  lean_targets: [ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCompatibleRouteEdgeQualifications.lean]
  risks: [forgetting that IsHomLift over the fixed fiber requires retagging, treating a raw PackageTotalHom as an unbundled IsIso proposition, assuming the geometry edge is iso before proving its core base iso, failing to transport IsIso through the two distinct generated core functors, adding route qualification to the input]
  unchecked: [refinement generated-edge cartesianness and isomorphism, complete geometry-edge inverse exactification and strong cocartesianness, coefficient normalization and identity, fixed-coefficient route transports, path/two-cell coherence, cochains/global equation, endpoint geometry isomorphisms, solution equivalence, named artifacts, clauses (c)--(d)]
result:
  proposed_result_type: target-proof-checkpoint
  proof_obligation_delta: Each source diagram edge is retagged as a strongly cocartesian morphism over the identity of the fixed core fiber and is therefore an isomorphism. Its underlying package edge and then its strongly cocartesian geometry lift are isomorphisms as well. Functorial transport and endpoint-isomorphism conjugation make every base and pulled generated core edge an isomorphism. Both exact core projections of the Cycle 35 complete route edges consequently acquire theorem-generated strong-cocartesian qualifications via of_isIso.
  completion_candidate: no
  lean_artifacts: [stronglyCocartesian_of_isHomLift_support, sourceFiberDiagramEdge_isIso, sourceTransportCoreEdge_isIso, sourceTransportGeometryEdge_isIso, generatedBaseRouteCoreEdge_isIso, generatedPulledRouteCoreEdge_isIso, generatedBaseRouteCoreEdge_isStronglyCocartesian, generatedPulledRouteCoreEdge_isStronglyCocartesian]
  evidence: [focused Lean check, 8-declaration namespace standard-axiom audit, targeted direct-predecessor construction, module registration, source hash, literal scans]
  source_sha256:
    UpperGeometryCompatibleRouteEdgeQualifications.lean: 3d6d96365f1c1c40b6724bb158f6f85b0590461f1049d12496db75fedc72f1ea
  claim_mapping:
    theorem_names: [sourceFiberDiagramEdge_isIso, sourceTransportCoreEdge_isIso, sourceTransportGeometryEdge_isIso, generatedBaseRouteCoreEdge_isIso, generatedPulledRouteCoreEdge_isIso, generatedBaseRouteCoreEdge_isStronglyCocartesian, generatedPulledRouteCoreEdge_isStronglyCocartesian]
    source_labels: [revision 4 source qualified transport, target theorem clause (b)]
    conjuncts: [fixed-fiber source edge isomorphism, package and geometry source-edge isomorphisms, two generated route core-edge isomorphisms, two core-stage cocartesian qualifications]
    undischarged_assumptions: [complete geometry-edge isomorphisms and cocartesian qualifications, coefficient normalization and identity, route transport/cochain/global equation, endpoint isomorphisms and solution equivalence]
    acceptance_point: The proof consumes the existing source edgeCoreStrong and edgeGeometryStrong fields only at the authored source boundary. Generated route core qualifications are conclusions obtained from functorial IsIso transport and of_isIso; they are not compatible-input fields or theorem arguments.
    port_status: not-applicable
audits:
  premise_delta:
    ambient_boundary: [single FixedCoefficientTwoLayerTransportOver on a PresentedPathCategory diagram valued in one CoreFiber]
    direction_hypothesis: []
    discharged: [source fiber-edge IsIso, source package-edge IsIso, source geometry-edge IsIso, both generated core-edge IsIso propositions, both generated core-stage strong-cocartesian qualifications]
    remaining: [both complete geometry-stage strong-cocartesian qualifications, coefficient identity, route packaging and all downstream coherence/solution artifacts]
  certificate_provenance:
    discharged: [source invertibility comes from fixed-fiber IsHomLift plus reviewed source strong-edge qualifications; generated core invertibility comes from functor maps and endpoint isomorphisms; generated core cocartesianness comes from IsIso]
    unresolved: [complete geometry inverse exactification and coefficient casts]
  proof_use:
    used: [sourceTransport.edge_base, sourceTransport.edgeCoreStrong, sourceTransport.edgeGeometryStrong, stronglyCocartesian_of_isHomLift_support, IsStronglyCocartesian.isIso_of_base_isIso, coreFiberHom_isIso_of_total_isIso, generatedBaseRouteCoreIsoAt, generatedPulledRouteCoreIsoAt, IsStronglyCocartesian.of_isIso]
    unused: [source comparator and coefficient identity fields remain reserved for route packaging and cochain construction]
  structure_field_escape: no route edge, route IsIso, route cartesianness/cocartesianness, inverse, or Beck--Chevalley certificate is added to compatible input
  route_integrity: base and pulled core edges are transported through distinct route functors and conjugated by their own endpoint isomorphisms
  predecessor_integrity: completed G-109, G-112, and G-114 declarations and GOAL files are unchanged
  target_fitting: none-found
  vacuity: every generator edge is covered; named nonidentity firing remains downstream
  one_way_as_equivalence: IsIso is derived only from the universal strong-cocartesian property over an identity base or from functorial transport of that actual isomorphism
  goal_or_report_reinterpretation: closed PR 4289 is recorded as a rejected stop attempt and is not merged; the fixed revision-4 target remains active
  validation_refs: [targeted `lake build ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleMateNaturality` and `lake build ResearchLean.AG.DoctrineFiberProduct.PackageProjectionBeckChevalleyExactness` constructed only direct predecessor DAGs; `check_research_modules.sh --focused ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCompatibleRouteEdgeQualifications.lean` => exit 0 and 8 declarations standard axioms only; module registered in research/lean/research-modules.txt and ResearchLean/AG/DoctrineFiberProduct.lean; git diff --check => exit 0; placeholder, hidden/BiDi, privacy, and reverse-import scans => no matches]
  blocking_findings: []
  next_obligation: Use source geometry IsIso, both route-leg Cartesian qualifications, and Cycle 35 factor laws with IsStronglyCartesian.of_comp to prove each generated refinement edge is Cartesian and IsIso; exactify its inverse and reflect both inverse laws to obtain complete geometry IsIso and strong cocartesianness.
```


## Cycle 38 — complete route geometry-edge qualification

```yaml
ledger_type: target_cycle_result
goal: G-115-aat-upper-stage-lift
cycle: 38
goal_blob_sha: fcd33815da27d5e1390b101223de49173967a349ad5f2e85324ec3b8d25b597c
base_oid: 1bba4b7a07b4acabaf75e5b2f3db6fcb81dcffd9
tracking_issue: 4250
report_path: research/reports/G-115-aat-upper-stage-lift.md
selection:
  proof_state_ref: Cycle 37 merged source and generated core-edge isomorphisms together with both core-stage cocartesian qualifications
  proof_dag_predecessors: [sourceTransportGeometryEdge_isIso, generatedBaseRouteCoreEdge_isIso, generatedPulledRouteCoreEdge_isIso, generatedBaseRouteGeometryEdge_fac, generatedPulledRouteGeometryEdge_fac, generatedBaseRouteLegAt_isStronglyCartesian, generatedPulledRouteLegAt_isStronglyCartesian, IsStronglyCartesian.of_comp, exactGeometryHomOfRefinement, exactGeometryToRefinementGeometry_faithful]
  proof_obligation: Cancel each generated route leg from the Cycle 35 factor graph to qualify the refinement geometry edge as strongly Cartesian, derive its isomorphism from the Cycle 37 exact core isomorphism, exactify the actual inverse, and obtain complete geometry-stage strong cocartesianness without a route certificate.
  selection_reason: This is the certificate-free route identified by the independent rejection of PR 4289. It closes the second G-109 edge qualification before coefficient normalization and fixed-coefficient route packaging.
  expected_result_type: target-proof-checkpoint
  lean_targets: [ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCompatibleRouteGeometryQualifications.lean]
  risks: [using the source-edge isomorphism without its actual factor law, cancelling a non-Cartesian route leg, assuming a faithful functor reflects isomorphisms, accepting an inverse or route qualification as input, collapsing the base and pulled routes]
  unchecked: [generated endpoint coefficient normalization and identity, actual FixedCoefficientTwoLayerTransportOver route values, finite path and two-cell laws, derived route cochains, global canonical-mate equation, endpoint comparison isomorphisms, solution equivalence, named artifacts, clauses (c)--(d)]
result:
  proposed_result_type: target-proof-checkpoint
  proof_obligation_delta: Both generated refinement geometry edges are strongly Cartesian by cancellation against their distinct target route legs after the Cycle 35 factor laws identify the composites with a strongly Cartesian source-leg/source-edge composite. Their exact core bases are Cycle 37 isomorphisms, hence both refinement edges are isomorphisms. A reusable exactification theorem constructs the complete inverse from the actual refinement and core inverses and proves both inverse laws through the faithful exact embedding. The complete base and pulled geometry edges are therefore isomorphisms and acquire geometry-stage strong-cocartesian qualifications by of_isIso.
  completion_candidate: no
  lean_artifacts: [exactGeometryHomOfRefinement_isIso, generatedBaseRouteRefinementGeometryEdge_isStronglyCartesian, generatedPulledRouteRefinementGeometryEdge_isStronglyCartesian, generatedBaseRouteRefinementGeometryEdge_isIso, generatedPulledRouteRefinementGeometryEdge_isIso, generatedBaseRouteGeometryEdge_isIso, generatedPulledRouteGeometryEdge_isIso, generatedBaseRouteGeometryEdge_isStronglyCocartesian, generatedPulledRouteGeometryEdge_isStronglyCocartesian]
  evidence: [focused Lean check, 9-declaration namespace standard-axiom audit, targeted direct-predecessor construction, module registration, source hash, literal scans]
  source_sha256:
    UpperGeometryCompatibleRouteGeometryQualifications.lean: 14184011377ae6a42fc9a1b7319ce5c560b6f2f7b52572c202e193542a61d0b3
  claim_mapping:
    theorem_names: [generatedBaseRouteRefinementGeometryEdge_isStronglyCartesian, generatedPulledRouteRefinementGeometryEdge_isStronglyCartesian, generatedBaseRouteRefinementGeometryEdge_isIso, generatedPulledRouteRefinementGeometryEdge_isIso, generatedBaseRouteGeometryEdge_isIso, generatedPulledRouteGeometryEdge_isIso, generatedBaseRouteGeometryEdge_isStronglyCocartesian, generatedPulledRouteGeometryEdge_isStronglyCocartesian]
    source_labels: [revision 4 certificate-free route edge construction, target theorem clause (b)]
    conjuncts: [two refinement-edge Cartesian cancellations, two refinement-edge isomorphisms, explicit inverse exactification, two complete geometry-edge isomorphisms, two geometry-stage cocartesian qualifications]
    undischarged_assumptions: [coefficient normalization and identity, route path and cell coherence, cochains and global equation, endpoint isomorphisms and solution equivalence]
    acceptance_point: Every qualification is a theorem output. The only source-side edge premise is the existing authored source transport qualification already consumed by Cycle 37; the generated proof uses the actual Cycle 35 factor laws and the two separately generated route legs. No Beck--Chevalley, inverse, Cartesian, cocartesian, or route-transport certificate is added to the compatible input or accepted as a theorem argument.
    port_status: not-applicable
audits:
  premise_delta:
    ambient_boundary: [Cycle 35 route edges and factor laws, Cycle 37 source and generated core-edge isomorphisms, theorem-generated pointwise route-leg cartesianness]
    direction_hypothesis: []
    discharged: [both refinement geometry-edge strong-Cartesian qualifications, both refinement geometry-edge isomorphisms, both complete geometry-edge isomorphisms, both geometry-stage strong-cocartesian qualifications]
    remaining: [coefficient normalization and identity, fixed-coefficient route packaging, finite coherence, route cochains and global equation, endpoint geometry isomorphisms, solution equivalence, named artifacts and clauses (c)--(d)]
  certificate_provenance:
    discharged: [Cartesian cancellation uses the literal Cycle 35 factor equations; base isomorphisms are the Cycle 37 generated core conclusions; complete inverses are exactifications of the actual refinement inverses and their laws are reflected by faithful map_injective; cocartesianness comes from the resulting actual isomorphisms]
    unresolved: [coefficient equality casts, route path and cell laws, endpoint inverse uniqueness, solution transports]
  proof_use:
    used: [sourceTransportGeometryEdge_isIso, generatedBaseRouteGeometryEdge_fac, generatedPulledRouteGeometryEdge_fac, generatedBaseRouteLegAt_isStronglyCartesian, generatedPulledRouteLegAt_isStronglyCartesian, generatedBaseRouteCoreEdge_isIso, generatedPulledRouteCoreEdge_isIso, IsStronglyCartesian.comp, IsStronglyCartesian.of_comp, IsStronglyCartesian.isIso_of_base_isIso, exactGeometryHomOfRefinement_toRefinement, exactGeometryToRefinementGeometry.map_injective, IsStronglyCocartesian.of_isIso]
    unused: [source coefficient identities and comparator fields remain reserved for coefficient normalization, fixed-coefficient packaging, and cochain construction]
  structure_field_escape: no route edge qualification, inverse, transport, path law, cochain, comparison, or solution is stored in the input or accepted as a theorem argument
  route_integrity: base and pulled cancellations use their own route legs, edge factor laws, generated core diagrams, and complete exactifications; only the authored source edge is shared
  predecessor_integrity: completed G-109, G-112, and G-114 declarations and fixed GOAL files are unchanged
  target_fitting: none-found
  vacuity: every generator edge is qualified; named nonidentity firing remains downstream
  one_way_as_equivalence: edge isomorphisms are proved from universal properties and explicit exact inverses; no endpoint solution-space equivalence is claimed
  goal_or_report_reinterpretation: none-found
  validation_refs: [targeted `lake build ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleRouteEdgeQualifications` constructed only the direct predecessor DAG; `check_research_modules.sh --focused ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCompatibleRouteGeometryQualifications.lean` => exit 0 and 9 declarations standard axioms only; module registered in research/lean/research-modules.txt and ResearchLean/AG/DoctrineFiberProduct.lean; git diff --check => exit 0; placeholder, hidden/BiDi, privacy, and reverse-import scans => no matches]
  blocking_findings: []
  next_obligation: Normalize both generated endpoint coefficient systems and prove that each generated complete route edge has identity coefficient map, then package the two actual FixedCoefficientTwoLayerTransportOver route transports from the now-derived core and geometry qualifications.
```

## Cycle 39 — fixed-coefficient compatible route transports

```yaml
ledger_type: target_cycle_result
goal: G-115-aat-upper-stage-lift
cycle: 39
goal_blob_sha: fcd33815da27d5e1390b101223de49173967a349ad5f2e85324ec3b8d25b597c
base_oid: 8843a5b7ed7815ad5fb2dfa6d1efba58c7c297a9
tracking_issue: 4250
report_path: research/reports/G-115-aat-upper-stage-lift.md
selection:
  proof_state_ref: Cycle 38 merged both complete route geometry-edge isomorphisms and strong-cocartesian qualifications
  proof_dag_predecessors: [generatedBaseRouteGeometryAt_coefficient_eq, generatedPulledRouteGeometryAt_coefficient_eq, generatedBaseRouteGeometryEdge_fac, generatedPulledRouteGeometryEdge_fac, generatedBaseRouteComparator_fac, generatedPulledRouteComparator_fac, generatedBaseRouteCoreEdge_isStronglyCocartesian, generatedPulledRouteCoreEdge_isStronglyCocartesian, generatedBaseRouteGeometryEdge_isStronglyCocartesian, generatedPulledRouteGeometryEdge_isStronglyCocartesian, FixedCoefficientTwoLayerTransportOver]
  proof_obligation: Normalize both generated endpoint families at the authored coefficient ring, derive edge and comparator coefficient identities from their literal factor graphs, prove finite path projection and two-cell base coherence, and package two actual fixed-coefficient G-109 route transports without adding route data to the compatible input.
  selection_reason: Clause (b) requires actual generated base and pulled G-109 transports rather than isolated edge qualifications. Coefficient normalization, finite path projection, and two-cell base equality are precisely the remaining fields of FixedCoefficientTwoLayerTransportOver after Cycles 37--38.
  expected_result_type: target-proof-checkpoint
  lean_targets: [ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCleavage.lean, ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCompatibleRouteCoefficientNormalization.lean]
  risks: [casting only the coefficient carrier while changing its CommRing instance, asserting generated coefficient identity without consuming the source identity, using one route transport for both routes, treating arbitrary parallel total morphisms as equal, accepting path or two-cell coherence from the caller]
  unchecked: [finite compositor/unitor compatibility, derived route cochains, global canonical-mate equation, endpoint comparison isomorphisms, solution equivalence, named positive and negative artifacts, clauses (c)--(d)]
result:
  proposed_result_type: target-proof-checkpoint
  proof_obligation_delta: The realized-refinement pullback now retains the source coefficient carrier and ring structure definitionally instead of introducing an unnecessary endpoint-equality recursor. Both generated endpoint families therefore package as FixedCoefficientGeometryAt values with literal package recovery. The base and pulled route-leg coefficient maps reduce to identity. Applying coefficientHom to the actual edge and comparator factor laws, and then consuming the authored source edge/comparator identity fields, proves all four generated identity laws. Path lifts project to the corresponding generated core-diagram maps by induction, and parallel paths have equal extraction projections because each actual diagram is valued in one CoreFiber. These results assemble two independent FixedCoefficientTwoLayerTransportOver values.
  completion_candidate: no
  lean_artifacts: [generatedBaseRouteFixedGeometryAt, generatedPulledRouteFixedGeometryAt, generatedBaseRouteLegAt_coefficient_id, generatedPulledRouteLegAt_coefficient_id, generatedBaseRouteFixedGeometryEdge, generatedPulledRouteFixedGeometryEdge, generatedBaseRouteFixedGeometryEdge_coefficient_id, generatedPulledRouteFixedGeometryEdge_coefficient_id, generatedBaseRouteFixedComparator, generatedPulledRouteFixedComparator, generatedBaseRouteFixedComparator_coefficient_id, generatedPulledRouteFixedComparator_coefficient_id, generatedBaseRouteLiftData, generatedPulledRouteLiftData, generatedBaseRoutePathLift_base, generatedPulledRoutePathLift_base, generatedBaseRouteTwoCellBase, generatedPulledRouteTwoCellBase, generatedBaseRouteTransport, generatedPulledRouteTransport]
  evidence: [focused Lean check, 26-declaration namespace standard-axiom audit, targeted direct-predecessor construction, module registration, source hashes, literal scans]
  source_sha256:
    UpperGeometryCleavage.lean: ef36cc1f4ab418bb2c55ede5a94cde9b3ff290708eacadeee8d51be78eb974e8
    UpperGeometryCompatibleRouteCoefficientNormalization.lean: 56941c71fe655cdcce0d466a448283909881fb99756c6874c22c8e211563ef04
  claim_mapping:
    theorem_names: [generatedBaseRouteFixedGeometryAt_package, generatedPulledRouteFixedGeometryAt_package, generatedBaseRouteFixedGeometryEdge_coefficient_id, generatedPulledRouteFixedGeometryEdge_coefficient_id, generatedBaseRouteFixedComparator_coefficient_id, generatedPulledRouteFixedComparator_coefficient_id, generatedBaseRoutePathLift_base, generatedPulledRoutePathLift_base, generatedBaseRouteTwoCellBase, generatedPulledRouteTwoCellBase, generatedBaseRouteTransport, generatedPulledRouteTransport]
    source_labels: [revision 4 certificate-free compatible locus, target theorem clause (b)]
    conjuncts: [two definitionally fixed endpoint families, two generated edge coefficient identities, two generated comparator coefficient identities, two finite path projection laws, two two-cell base laws, two actual G-109 transports]
    undischarged_assumptions: [finite compositor/unitor compatibility, route cochain and global mate equations, endpoint comparison isomorphisms and solution equivalence]
    acceptance_point: The only authored coefficient evidence is sourceTransport.edge_coefficient_id and sourceTransport.comparator_coefficient_id, each consumed through the corresponding generated factor graph. Path and two-cell laws are theorem outputs from actual generated core-fiber diagrams. No route edge, comparator, coefficient identity, path law, cell law, or transport is accepted as input.
    port_status: not-applicable
audits:
  premise_delta:
    ambient_boundary: [single authored FixedCoefficientTwoLayerTransportOver, Cycle 35 edge and comparator factor laws, Cycles 37--38 core and geometry qualifications]
    direction_hypothesis: []
    discharged: [endpoint coefficient normalization, both route-leg coefficient identities, both edge coefficient identities, both comparator coefficient identities, finite path projection, both two-cell base laws, both actual fixed-coefficient route transports]
    remaining: [finite compositor/unitor compatibility, derived route cochains and global canonical-mate equation, endpoint geometry isomorphisms, solution equivalence, named artifacts and clauses (c)--(d)]
  certificate_provenance:
    discharged: [coefficient carriers and ring instances are retained definitionally by the generated cleavage; edge and comparator identities are cancellations of the literal factor equations against generated identity legs and authored source identities; two-cell base equality comes from the verticality witnesses of the actual generated CoreFiber diagrams]
    unresolved: [finite compositor/unitor compatibility, route cochain comparison laws, endpoint inverse uniqueness, solution transports]
  proof_use:
    used: [refinementSourceGeometry, refinementCoefficientHom, generatedBaseRouteGeometryEdge_fac, generatedPulledRouteGeometryEdge_fac, sourceTransport.edge_coefficient_id, generatedBaseRouteComparator_fac, generatedPulledRouteComparator_fac, sourceTransport.comparator_coefficient_id, generatedBaseRouteCoreDiagram.map_id, generatedBaseRouteCoreDiagram.map_comp, generatedPulledRouteCoreDiagram.map_id, generatedPulledRouteCoreDiagram.map_comp, IsHomLift.fac', both core and geometry strong-cocartesian qualifications]
    unused: [sourceTransport.twoCellBase is unnecessary for the extraction-level route field because every actual CoreFiber diagram already supplies the stronger verticality equation; finite compositor/unitor compatibility and the cochain/global-mate equations for the already-consumed authored comparator values remain downstream]
  structure_field_escape: no generated endpoint, edge, comparator, qualification, coefficient law, path law, two-cell law, or route transport is stored in UpperGeometryCompatibleProblemInputData or accepted as a theorem argument
  route_integrity: base and pulled transports use separate endpoint families, core diagrams, complete edges, factor laws, qualification theorems, comparators, path inductions, and two-cell proofs; only the single authored source transport is shared
  predecessor_integrity: the fixed GOAL and completed G-109, G-112, and G-114 declarations are unchanged; the G-115-local cleavage implementation is definitionally normalized without changing its signature or mathematical output
  target_fitting: none-found
  vacuity: every generator edge and declared two-cell is covered; named nonidentity firing remains downstream
  one_way_as_equivalence: no endpoint or solution equivalence is claimed
  goal_or_report_reinterpretation: none-found
  validation_refs: [targeted `lake build ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleRouteGeometryQualifications` constructed only the direct predecessor DAG after the local cleavage normalization; `check_research_modules.sh --focused ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCompatibleRouteCoefficientNormalization.lean` => exit 0 and 26 declarations standard axioms only; module registered in research/lean/research-modules.txt and ResearchLean/AG/DoctrineFiberProduct.lean; git diff --check => exit 0; placeholder, hidden/BiDi, privacy, and reverse-import scans => no matches]
  blocking_findings: []
  next_obligation: Prove finite compositor/unitor compatibility, derive the base and pulled finite route cochains from the two generated transports and their generated comparator families, then prove the global canonical upper-mate equation before constructing endpoint isomorphisms and the solution-space equivalence.
```

## Cycle 40 — finite path factorization and route raw cochains

```yaml
ledger_type: target_cycle_result
goal: G-115-aat-upper-stage-lift
cycle: 40
goal_blob_sha: fcd33815da27d5e1390b101223de49173967a349ad5f2e85324ec3b8d25b597c
base_oid: eca53dbb1c55c985a37c79d4b2f4b6e6462a86cc
tracking_issue: 4250
report_path: research/reports/G-115-aat-upper-stage-lift.md
selection:
  proof_state_ref: Cycle 39 merged two actual fixed-coefficient G-109 transports on the generated base and pulled routes
  proof_dag_predecessors: [generatedBaseRouteTransport, generatedPulledRouteTransport, generatedBaseRouteGeometryEdge_fac, generatedPulledRouteGeometryEdge_fac, TwoLayerLiftData.pathLift, upperRawDefectCochain]
  proof_obligation: Extend both generator factor graphs to every finite path, expose the empty-path unit and two-stage append factorizations separately, forget the source and generated transports into the G-109 vocabulary, and derive the three initial raw cochains from the actual transports rather than accepting cochains as input.
  selection_reason: The remaining comparator pullback compatibility and cochain image equations require route-wide path normalization first. The nil and append factorizations are the finite unit/composition boundary, while the raw cochain constructors fix the exact G-109 codomains needed by the successor uniqueness proof.
  expected_result_type: target-proof-checkpoint
  lean_targets: [ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCompatibleRouteCochains.lean]
  risks: [repackaging pathLift_append without consuming route legs, treating the source and generated routes as definitionally equal, storing a cochain in the compatible input, claiming canonical-comparator compatibility from path factorization alone, claiming the global mate equation before the two-level Cartesian uniqueness proof]
  unchecked: [finite compositor/unitor compatibility beyond the path-factor prerequisite, canonical-comparator pullback compatibility, route raw-cochain image equations, global canonical upper-mate equation, endpoint comparison isomorphisms, solution equivalence, named positive and negative artifacts, clauses (c)--(d)]
result:
  proposed_result_type: target-proof-checkpoint
  proof_obligation_delta: The base and pulled generator factor laws now extend independently to every presented path. Their nil specializations give the literal two-sided unit factorization, and their append specializations expose both finite stages and use each path factor law separately. The source, base, and pulled fixed-coefficient transports are forgotten to three actual G-109 TwoLayerTransportData values, from which the three identity-reselection upper raw-defect cochains are derived by upperRawDefectCochain. No cochain or path equation is added to the compatible input.
  completion_candidate: no
  lean_artifacts: [generatedBaseRouteData, generatedPulledRouteData, compatibleSourceRouteData, generatedBaseRoutePath_fac, generatedPulledRoutePath_fac, generatedBaseRoutePath_nil_fac, generatedPulledRoutePath_nil_fac, generatedBaseRoutePath_append_fac, generatedPulledRoutePath_append_fac, compatibleSourceRawDefectCochain, generatedBaseRouteRawDefectCochain, generatedPulledRouteRawDefectCochain, compatibleSourceRawDefectCochain_apply, generatedBaseRouteRawDefectCochain_apply, generatedPulledRouteRawDefectCochain_apply]
  evidence: [focused Lean check, 15-declaration namespace standard-axiom audit, targeted module construction, module registration, source hash, literal scans]
  source_sha256:
    UpperGeometryCompatibleRouteCochains.lean: ddc59ec7f4ca6637bfa4bfa1e83841b1957150dd4bf9f6fd264efd51d0d1e36f
  claim_mapping:
    theorem_names: [generatedBaseRoutePath_fac, generatedPulledRoutePath_fac, generatedBaseRoutePath_nil_fac, generatedPulledRoutePath_nil_fac, generatedBaseRoutePath_append_fac, generatedPulledRoutePath_append_fac, compatibleSourceRawDefectCochain_apply, generatedBaseRouteRawDefectCochain_apply, generatedPulledRouteRawDefectCochain_apply]
    source_labels: [revision 4 finite path normalization, target theorem clause (b)]
    conjuncts: [base all-path factor law, pulled all-path factor law, two literal unit factorizations, two two-stage append factorizations, three transport-derived raw cochains]
    undischarged_assumptions: [finite compositor/unitor compatibility beyond the path-factor prerequisite, canonical-comparator compatibility and cochain image laws, global mate equation, endpoint comparison isomorphisms and solution equivalence]
    acceptance_point: Each all-path theorem is an induction from the corresponding generated edge factor law. Each append theorem consumes the first and second path factor laws separately. Each raw cochain is evaluated by the G-109 upperRawTwoCellDefect definition on its own actual route transport; no authored comparator is identified with the canonical comparator.
    port_status: not-applicable
audits:
  premise_delta:
    ambient_boundary: [single source fixed-coefficient transport, two Cycle 39 generated fixed-coefficient transports, Cycle 35 route edge factor laws, G-109 path-lift and upper-obstruction APIs]
    direction_hypothesis: []
    discharged: [base and pulled all-path factorization, empty-path unit factorization on both routes, two-stage append factorization on both routes, source/base/pulled initial raw-cochain construction]
    remaining: [finite compositor/unitor compatibility beyond the path-factor prerequisite, canonical-comparator pullback compatibility, route cochain image laws, global canonical-mate equation, endpoint geometry isomorphisms, solution equivalence, named artifacts and clauses (c)--(d)]
  certificate_provenance:
    discharged: [path equations are derived by induction from theorem-generated edge factors; cochains are outputs of the G-109 upper obstruction API applied to actual transports]
    unresolved: [finite compositor/unitor compatibility, two-level Cartesian uniqueness for canonical comparator pullback and the global mate equation, endpoint inverse uniqueness, solution transports]
  proof_use:
    used: [generatedBaseRouteTransport, generatedPulledRouteTransport, sourceTransport.toTwoLayerTransportData, generatedBaseRouteGeometryEdge_fac, generatedPulledRouteGeometryEdge_fac, Category.assoc, Category.id_comp, Category.comp_id, upperRawDefectCochain, upperRawTwoCellDefect]
    unused: [the generated group homomorphisms and canonical comparator are reserved for the successor cochain image theorem; the pointwise mate and comparator factor laws are reserved for the global equation]
  structure_field_escape: no path law, cochain, comparator compatibility, route equation, or solution is stored in UpperGeometryCompatibleProblemInputData or accepted as a theorem argument
  route_integrity: base and pulled path inductions use their own transport, edge factor law, and route leg; their raw cochains are formed from distinct generated G-109 data
  predecessor_integrity: the fixed GOAL and completed G-109, G-112, and G-114 declarations are unchanged
  target_fitting: none-found
  vacuity: all finite paths are covered; named nonidentity cochain firing remains downstream
  one_way_as_equivalence: no comparator, endpoint, or solution equivalence is claimed
  goal_or_report_reinterpretation: none-found
  validation_refs: [targeted `lake build ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleRouteCochains` constructed the direct module DAG and passed; `check_research_modules.sh --focused ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCompatibleRouteCochains.lean` => exit 0 and 15 declarations standard axioms only; module registered in research/lean/research-modules.txt and ResearchLean/AG/DoctrineFiberProduct.lean; git diff --check => exit 0; placeholder, hidden/BiDi, privacy, and reverse-import scans => no matches]
  blocking_findings: []
  next_obligation: Use the all-path unit/composition factor laws to prove the remaining finite compositor/unitor compatibility and the two-level Cartesian uniqueness theorem identifying each generated canonical comparator with the pullback of the source canonical comparator, then derive both raw-cochain image equations and prove the global canonical upper-mate comparator equation.
```

## Cycle 41 — two-level canonical-comparator pullback

```yaml
ledger_type: target_cycle_result
goal: G-115-aat-upper-stage-lift
cycle: 41
goal_blob_sha: fcd33815da27d5e1390b101223de49173967a349ad5f2e85324ec3b8d25b597c
base_oid: bebd406794c3d9c6e78cdb88124260176009171e
tracking_issue: 4250
report_path: research/reports/G-115-aat-upper-stage-lift.md
selection:
  proof_state_ref: Cycle 40 merged all-path factor laws and three transport-derived raw cochains
  proof_dag_predecessors: [generatedBaseRoutePath_fac, generatedPulledRoutePath_fac, upperCanonicalTwoCellComparator_fac, generatedBaseCompositeFiberAutAt_fac, generatedPulledCompositeFiberAutAt_fac]
  proof_obligation: Identify each generated route canonical comparator with the Cartesian pullback of the source canonical comparator, without equating authored and canonical comparators.
  selection_reason: The raw-cochain image laws require the canonical factor, not only the authored comparator, to commute with each generated group homomorphism. The two-stage Cartesian proof is therefore the next non-circular obligation after all-path normalization.
  expected_result_type: target-proof-checkpoint
  lean_targets: [ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCompatibleCanonicalComparators.lean]
  risks: [skipping package-level uniqueness, treating identity reselection path lifts as definitionally equal, identifying authored and canonical comparators, sharing a route certificate, claiming cochain image or global mate prematurely]
  unchecked: [finite compositor/unitor compatibility beyond path-factor prerequisites, route raw-cochain image equations, global canonical upper-mate equation, endpoint isomorphisms, solution equivalence, named artifacts, clauses (c)--(d)]
result:
  proposed_result_type: target-proof-checkpoint
  proof_obligation_delta: Both route canonical comparators are now proved equal to the corresponding generated pullback of the source canonical comparator. Each theorem derives the factor equality after the endpoint leg, establishes package equality first, geometry equality second, and finally cancels the route path; no compatibility is added to the input.
  completion_candidate: no
  lean_artifacts: [generatedBaseRouteCanonicalComparator_eq_pullback, generatedPulledRouteCanonicalComparator_eq_pullback]
  source_sha256:
    UpperGeometryCompatibleCanonicalComparators.lean: cc3cec52732354ea86f4219c875ccf19fe375dcbdfe8c4af6cafd127912296fe
  evidence: [focused Lean check, 2-declaration namespace standard-axiom audit, targeted direct-module construction, module registration, source hash, literal scans]
  claim_mapping:
    theorem_names: [generatedBaseRouteCanonicalComparator_eq_pullback, generatedPulledRouteCanonicalComparator_eq_pullback]
    source_labels: [revision 4 finite compatible upper pseudofunctor, target theorem clause (b)]
    conjuncts: [base canonical comparator pullback, pulled canonical comparator pullback]
    undischarged_assumptions: [finite compositor/unitor compatibility beyond path-factor prerequisites, raw-cochain image laws, global mate, endpoint and solution equivalences]
    acceptance_point: Each proof consumes its all-path factor laws and the source canonical factor law, then applies refinement-package uniqueness, refinement-geometry uniqueness, and strong-path CompositeFiberAut cancellation in order.
    port_status: not-applicable
audits:
  premise_delta:
    ambient_boundary: [Cycle 40 all-path factor laws, source and generated G-109 route data, route-leg Cartesian qualifications, generated pointwise composite-fiber pullbacks]
    direction_hypothesis: []
    discharged: [base and pulled canonical-comparator pullback compatibility]
    remaining: [finite compositor/unitor compatibility, two raw-cochain image laws, global canonical-mate equation, endpoint isomorphisms, solution equivalence, named artifacts, clauses (c)--(d)]
  certificate_provenance:
    discharged: [both equalities are outputs of two-level Cartesian uniqueness]
    unresolved: [cochain image, global mate, endpoint inverse uniqueness, solution transports]
  proof_use:
    used: [generatedBaseRoutePath_fac, generatedPulledRoutePath_fac, upperCanonicalTwoCellComparator_fac, generatedBaseCompositeFiberAutAt_fac, generatedPulledCompositeFiberAutAt_fac, refinementPackageProjection Cartesian uniqueness, refinementGeometryProjection Cartesian uniqueness, CompositeFiberAut.ext_of_strong_fac]
    unused: [authored comparator values and raw cochains are reserved for the successor image equations; the pointwise upper mate is reserved for the global mate equation]
  structure_field_escape: no comparator compatibility or route equation is stored in the input or accepted as an argument
  route_integrity: base and pulled proofs use distinct route data, legs, pointwise composite-fiber pullbacks, and Cartesian qualifications
  predecessor_integrity: the fixed GOAL and completed G-109, G-112, and G-114 declarations are unchanged
  target_fitting: none-found
  vacuity: both theorems quantify over every declared two-cell; named nonidentity firing remains downstream
  one_way_as_equivalence: no endpoint or solution equivalence is claimed
  goal_or_report_reinterpretation: none-found
  validation_refs: [targeted `lake build ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleCanonicalComparators` passed; focused checker passed with 2 declarations standard axioms only; module registered in research-modules.txt and DoctrineFiberProduct.lean; git diff --check and hidden/BiDi, privacy, placeholder, reverse-import scans clean]
  blocking_findings: []
  next_obligation: Prove the remaining finite compositor/unitor compatibility, derive both raw-cochain image equations through the generated group homomorphisms, then prove the global canonical upper-mate equation.
```

## Cycle 42 — raw-cochain images under generated route homomorphisms

```yaml
ledger_type: target_cycle_result
goal: G-115-aat-upper-stage-lift
cycle: 42
goal_blob_sha: fcd33815da27d5e1390b101223de49173967a349ad5f2e85324ec3b8d25b597c
base_oid: eb0cfde7221a562742a81bbaad6bfa3750b80f87
tracking_issue: 4250
report_path: research/reports/G-115-aat-upper-stage-lift.md
selection:
  proof_state_ref: Cycle 41 merged the two canonical-comparator pullback equalities
  proof_dag_predecessors: [generatedBaseRouteRawDefectCochain, generatedPulledRouteRawDefectCochain, compatibleSourceRawDefectCochain, generatedBaseCompositeFiberAutHomAt, generatedPulledCompositeFiberAutHomAt, generatedBaseRouteCanonicalComparator_eq_pullback, generatedPulledRouteCanonicalComparator_eq_pullback]
  proof_obligation: Prove that each generated route raw cochain is pointwise the image of the source raw cochain under its generated composite-fiber group homomorphism.
  selection_reason: The G-109 raw defect is authored comparator times inverse canonical comparator, so Cycle 41 supplies exactly the missing canonical factor required to transport it by map_mul and map_inv.
  expected_result_type: proof-obligation-discharged
  lean_targets: [ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCompatibleRawCochainImages.lean]
  risks: [using only authored-comparator functoriality, omitting inverse preservation, conflating dependent route codomains, claiming the global mate from pointwise cochain images]
  unchecked: [finite compositor/unitor compatibility beyond path-factor prerequisites, global canonical upper-mate equation, endpoint isomorphisms, solution equivalence, named artifacts, clauses (c)--(d)]
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: Both generated raw cochains are now identified pointwise with the image of the source raw cochain. The proof unfolds the actual G-109 raw defect and consumes map_mul, map_inv, the authored comparator pullback definition, and the corresponding canonical-comparator pullback theorem.
  completion_candidate: no
  lean_artifacts: [generatedBaseRouteRawDefectCochain_eq_image, generatedPulledRouteRawDefectCochain_eq_image]
  source_sha256:
    UpperGeometryCompatibleRawCochainImages.lean: 5655786aac814597228073b364a2927c59d419cd165edfcd0d31d91aab789557
  evidence: [focused Lean check, 2-declaration namespace standard-axiom audit, targeted direct-module construction, module registration, source hash, literal scans]
  claim_mapping:
    theorem_names: [generatedBaseRouteRawDefectCochain_eq_image, generatedPulledRouteRawDefectCochain_eq_image]
    source_labels: [revision 4 finite compatible upper pseudofunctor, target theorem clause (b)]
    conjuncts: [base raw-cochain image law, pulled raw-cochain image law]
    undischarged_assumptions: [finite compositor/unitor compatibility, global mate, endpoint and solution equivalences]
    acceptance_point: Each equality is derived from the actual transport-generated cochains and its route-specific group homomorphism; neither cochain nor image law is accepted from the caller.
    port_status: not-applicable
audits:
  premise_delta:
    ambient_boundary: [three Cycle 40 transport-derived raw cochains, two generated group homomorphisms, two Cycle 41 canonical-comparator pullback equalities]
    direction_hypothesis: []
    discharged: [base raw-cochain image law, pulled raw-cochain image law]
    remaining: [finite compositor/unitor compatibility, global canonical-mate equation, endpoint isomorphisms, solution equivalence, named artifacts, clauses (c)--(d)]
  certificate_provenance:
    discharged: [both image laws are computed from map_mul and map_inv on theorem-generated group homomorphisms]
    unresolved: [global mate, endpoint inverse uniqueness, solution transports]
  proof_use:
    used: [upperRawTwoCellDefect, map_mul, map_inv, generatedBaseCompositeFiberAutHomAt_apply, generatedPulledCompositeFiberAutHomAt_apply, generatedBaseRouteCanonicalComparator_eq_pullback, generatedPulledRouteCanonicalComparator_eq_pullback]
    unused: [the pointwise upper mate is reserved for the global mate equation]
  structure_field_escape: no cochain, image law, or comparator compatibility is stored in the input or accepted as an argument
  route_integrity: base and pulled equalities use distinct raw cochains, group homomorphisms, and canonical pullback theorems
  predecessor_integrity: the fixed GOAL and completed predecessor declarations are unchanged
  target_fitting: none-found
  vacuity: theorems quantify over every declared two-cell; named nonidentity firing remains downstream
  one_way_as_equivalence: no endpoint or solution equivalence is claimed
  goal_or_report_reinterpretation: none-found
  validation_refs: [targeted `lake build ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleRawCochainImages` passed; focused checker passed with 2 declarations standard axioms only; module registered in research-modules.txt and DoctrineFiberProduct.lean; git diff --check and hidden/BiDi, privacy, placeholder, reverse-import scans clean]
  blocking_findings: []
  next_obligation: Prove the remaining finite compositor/unitor compatibility and the global canonical upper-mate equation, then construct endpoint isomorphisms and the solution equivalence.
```

## Cycle 43 — pseudofunctor normalization and global compatible mate

```yaml
ledger_type: target_cycle_result
goal: G-115-aat-upper-stage-lift
cycle: 43
goal_blob_sha: fcd33815da27d5e1390b101223de49173967a349ad5f2e85324ec3b8d25b597c
base_oid: b2f9585334f116340a0cb1edc68ea41dc1775c56
tracking_issue: 4250
report_path: research/reports/G-115-aat-upper-stage-lift.md
selection:
  proof_state_ref: Cycle 42 merged both raw-cochain image laws while leaving genuine pseudofunctor normalization and the global mate equation open
  proof_dag_predecessors: [compatibleSourceRouteData, generatedBaseRouteData, generatedPulledRouteData, generatedBaseRouteCanonicalComparator_eq_pullback, generatedPulledRouteCanonicalComparator_eq_pullback, generatedBaseRouteComparator_fac, generatedPulledRouteComparator_fac, generatedCompatibleUpperGeometryMateAt_triangle, generatedPulledRouteLegAt_isStronglyCartesian]
  proof_obligation: Consume the actual geometry-fiber unitor and compositor normalization on the compatible finite routes, then prove that the canonical generated upper mate intertwines the two comparator families pulled back from the single authored source comparator.
  selection_reason: Map-one/map-mul and recursive nil/append factor laws alone do not mention the genuine pseudofunctor cells. The unitor factor theorem and pseudofunctor-normalized comparator must be connected explicitly before the constructor-level global equation closes clause (b)'s remaining coherence prerequisite.
  expected_result_type: proof-obligation-discharged
  lean_targets: [ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCompatiblePseudofunctorCoherence.lean, ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCompatibleGlobalMate.lean]
  risks: [renaming map-one or path-nil as unitor compatibility, aliasing the upper canonical comparator without consuming the genuine compositor, replacing the authored comparator by the canonical comparator, proving only the equation after the route leg, skipping package-level uniqueness, accepting comparator intertwining from the caller]
  unchecked: [endpoint comparison isomorphisms, generated solution constructor, solution equivalence, named positive and negative artifacts, clauses (c)--(d)]
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: The genuine geometry-fiber unitor now normalizes the canonical identity lift to the literal source empty path at geometry and package levels. Each generated endpoint unitor is separately identified with its theorem-generated pullback of the source identity by map-one, and both generated/source unitor normalizations are connected through the corresponding route-specific nil factor at geometry and package levels. The genuine pseudofunctor-compositor normalization on each generated route is proved to be the route-specific Cartesian pullback of the source normalization. Finally, both authored-comparator factor laws and the canonical mate triangle give the global comparator equation after the pulled leg; package and geometry strong-cartesian uniqueness reflect it to the required literal equality.
  completion_candidate: no
  lean_artifacts: [compatibleSourceRoutePathNil_unitor, compatibleSourceRoutePathNil_unitor_base, generatedBaseRouteUnitor_eq_pullback_one, generatedPulledRouteUnitor_eq_pullback_one, generatedBaseRouteUnitor_compatibility, generatedPulledRouteUnitor_compatibility, generatedBaseRouteUnitor_compatibility_base, generatedPulledRouteUnitor_compatibility_base, generatedBaseRoutePseudofunctorComparator_eq_pullback, generatedPulledRoutePseudofunctorComparator_eq_pullback, generatedCompatibleUpperGeometryMateAt_comparator_intertwining]
  source_sha256:
    UpperGeometryCompatiblePseudofunctorCoherence.lean: e93d04fcbd9cc43a61126c8bb4d3af72e798f33c4f4333ee08d8b8171724ed50
    UpperGeometryCompatibleGlobalMate.lean: c94efa66927838b0c12b8cbc307b07c36dc8b1a523bb551d8c67e5da1db3d7d2
  evidence: [focused Lean checks, 10-declaration and 1-declaration namespace standard-axiom audits, targeted direct-module construction, module registration, source hashes, literal scans]
  claim_mapping:
    theorem_names: [compatibleSourceRoutePathNil_unitor, compatibleSourceRoutePathNil_unitor_base, generatedBaseRouteUnitor_eq_pullback_one, generatedPulledRouteUnitor_eq_pullback_one, generatedBaseRouteUnitor_compatibility, generatedPulledRouteUnitor_compatibility, generatedBaseRouteUnitor_compatibility_base, generatedPulledRouteUnitor_compatibility_base, generatedBaseRoutePseudofunctorComparator_eq_pullback, generatedPulledRoutePseudofunctorComparator_eq_pullback, generatedCompatibleUpperGeometryMateAt_comparator_intertwining]
    source_labels: [revision 4 finite compatible pseudofunctor coherence, revision 4 global canonical upper-mate equation, target theorem clause (b)]
    conjuncts: [source geometry and package unitor normalization, base and pulled generated unitor map-one normalization, base and pulled route-specific unitor compatibility at geometry and package levels, base and pulled compositor-normalized comparator pullback, global authored-comparator intertwining by the canonical upper mate]
    undischarged_assumptions: [endpoint comparison inverse laws, componentwise generated solution laws, solution equivalence]
    acceptance_point: The global equation is not an input field or an equality after forgetting geometry. It consumes the same literal sourceTransport.comparator on both routes through separate factor laws and is reflected through package then complete-geometry Cartesian uniqueness.
    port_status: not-applicable
audits:
  premise_delta:
    ambient_boundary: [G-109 geometry-fiber unitor and pseudofunctor compositor normalization, Cycles 32 and 40 route pullback and finite path laws, Cycle 41 canonical-comparator pullback, Cycle 36 canonical mate triangle]
    direction_hypothesis: []
    discharged: [literal source empty-path unitor normalization, generated base and pulled unitor pullback-one normalizations, both route-specific generated/source unitor compatibilities at geometry and package levels, both generated pseudofunctor-compositor normalization pullbacks, constructor-level global canonical upper-mate comparator equation]
    remaining: [endpoint comparison isomorphisms, generated solution, solution equivalence, named artifacts, clauses (c)--(d)]
  certificate_provenance:
    discharged: [unitor compatibility comes from generated and source geomFiberUnitorApp_hom_fac, both theorem-generated map-one laws, and both route nil factor laws; compositor compatibility comes from pseudofunctorCanonicalComparator_eq_upper plus two-level Cartesian comparator uniqueness; global mate comes from both authored comparator factor laws, the mate triangle, and two-level Cartesian uniqueness]
    unresolved: [endpoint inverse uniqueness, solution transports, named firing and negative classification]
  proof_use:
    used: [geomFiberUnitorApp_hom_fac, generatedBaseCompositeFiberAutAt_one, generatedPulledCompositeFiberAutAt_one, generatedBaseRoutePath_nil_fac, generatedPulledRoutePath_nil_fac, pseudofunctorCanonicalComparator_eq_upper, generatedBaseRouteCanonicalComparator_eq_pullback, generatedPulledRouteCanonicalComparator_eq_pullback, generatedBaseRouteComparator_fac, generatedPulledRouteComparator_fac, generatedCompatibleUpperGeometryMateAt_triangle, pulledRouteGeometryBase_isStronglyCartesian, generatedPulledRouteLegAt_isStronglyCartesian, IsStronglyCartesian.ext]
    unused: [raw-cochain image laws remain adjacent diagnostic consequences rather than substitutes for comparator intertwining]
  structure_field_escape: no unitor, compositor normalization, route comparator equation, mate equation, endpoint comparison, or solution is stored in the compatible input or accepted as a theorem argument
  route_integrity: base and pulled pseudofunctor comparator normalizations use distinct generated transports and pullback maps; the global equation consumes both distinct route comparator factor laws and the one shared authored source comparator
  predecessor_integrity: the fixed GOAL and completed predecessor declarations are unchanged
  target_fitting: none-found
  vacuity: all statements quantify over actual vertices or two-cells; the global equation uses the literal authored comparator at every cell; named nonidentity firing remains downstream
  one_way_as_equivalence: no endpoint or solution equivalence is claimed
  goal_or_report_reinterpretation: none-found
  validation_refs: [targeted direct-module builds passed; focused checkers passed with 10 and 1 declarations standard axioms only; both modules registered in research-modules.txt and DoctrineFiberProduct.lean; git diff --check and hidden/BiDi, privacy, placeholder, reverse-import scans clean]
  blocking_findings: []
  next_obligation: Construct the base and pulled endpoint comparison isomorphisms from base-iso-normalized strong-cartesian uniqueness, prove their inverse, factor, coefficient, component, edge, and authored-comparator conjugation laws, then build the generated solution and solution equivalence.
```

## Cycle 44 — authored-compatible endpoint normalization

```yaml
ledger_type: target_cycle_result
goal: G-115-aat-upper-stage-lift
cycle: 44
goal_blob_sha: fcd33815da27d5e1390b101223de49173967a349ad5f2e85324ec3b8d25b597c
base_oid: 185de03d4c25ef5e66ab67f5c2ad72e47bccaa1e
tracking_issue: 4250
report_path: research/reports/G-115-aat-upper-stage-lift.md
selection:
  proof_state_ref: Cycle 43 merged the global compatible mate while endpoint comparison isomorphisms remained open
  proof_dag_predecessors: [generatedBaseRouteCoreIsoAt, generatedPulledRouteCoreIsoAt, generatedBaseRouteFixedGeometryAt, generatedPulledRouteFixedGeometryAt]
  proof_obligation: Construct complete fixed-coefficient authored-compatible geometry endpoints on the literal G-114 base and pulled route packages, keeping them distinct from the canonical generated endpoints and deriving their normalization maps from the theorem-generated exact core isomorphisms.
  selection_reason: The existing one-way endpoint comparison and raw solution contract are indexed by literal G-114 route packages, whereas the compatible construction currently exposes only canonically isomorphic generated packages. Endpoint comparison isomorphisms cannot be typed naturally until this object-level base-iso normalization boundary exists.
  expected_result_type: proof-checkpoint
  lean_targets: [ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCleavage.lean, ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCompatibleAuthoredEndpoints.lean]
  risks: [identifying isomorphic endpoint cores definitionally, discarding selected geometry or raw data, accepting an endpoint comparison or inverse in the input, normalizing only one route, treating object construction as the completed endpoint isomorphism]
  unchecked: [authored route geometry legs and their strong-cartesian qualifications, authored edge and comparator transports, raw compatible problem constructor, complete endpoint comparison isomorphisms and their laws, generated solution and solution equivalence, named artifacts, clauses (c)--(d)]
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: A reusable object-level upper-pair normalization now rebuilds selected geometry and raw data on an independently specified core while retaining the coefficient ring. Applying it separately to the inverse/hom upper maps of the generated base and pulled core isomorphisms produces complete fixed-coefficient geometry endpoints on the literal G-114 route packages. Four cancellation theorems expose that both specialized upper pairs are actual inverses rather than unrelated maps.
  completion_candidate: no
  lean_artifacts: [pullGeometryPackageAlongUpperPair, pullGeometryPackageAlongUpperPair_core, pullGeometryPackageAlongUpperPair_coefficient, pullGeometryPackageAlongUpperPair_raw, generatedBaseRouteEndpointUpper_inv_hom, generatedBaseRouteEndpointUpper_hom_inv, generatedPulledRouteEndpointUpper_inv_hom, generatedPulledRouteEndpointUpper_hom_inv, generatedAuthoredBaseRouteGeometryAt, generatedAuthoredPulledRouteGeometryAt, generatedAuthoredBaseRouteGeometryAt_core, generatedAuthoredPulledRouteGeometryAt_core, generatedAuthoredBaseRouteGeometryAt_coefficient, generatedAuthoredPulledRouteGeometryAt_coefficient, generatedAuthoredBaseRouteFixedGeometryAt, generatedAuthoredPulledRouteFixedGeometryAt, generatedAuthoredBaseRouteFixedGeometryAt_package, generatedAuthoredPulledRouteFixedGeometryAt_package]
  source_sha256:
    UpperGeometryCleavage.lean: c526120f8ae68911f999daec0d070b0821939f6d79c620d9505425e0e2d1cdbd
    UpperGeometryCompatibleAuthoredEndpoints.lean: e93e98f62ddda6cf0ed6628c47627f0996c36cc1d4cf2dd549f09353df19e826
  evidence: [targeted direct-module construction, focused 18-declaration checker, declaration-level standard-axiom audit, module registration, source hashes, literal scans]
  claim_mapping:
    theorem_names: [generatedBaseRouteEndpointUpper_inv_hom, generatedBaseRouteEndpointUpper_hom_inv, generatedPulledRouteEndpointUpper_inv_hom, generatedPulledRouteEndpointUpper_hom_inv, generatedAuthoredBaseRouteGeometryAt, generatedAuthoredPulledRouteGeometryAt, generatedAuthoredBaseRouteFixedGeometryAt, generatedAuthoredPulledRouteFixedGeometryAt]
    source_labels: [revision 4 authored-compatible route generation, revision 4 endpoint comparison isomorphism prerequisite, target theorem clause (b)]
    conjuncts: [base and pulled exact upper-pair cancellation, literal G-114 endpoint core placement, complete selected-geometry and raw-data reconstruction, fixed authored coefficient ring]
    undischarged_assumptions: [geometry comparison homs and inverse laws, authored leg and transport laws, solution transport laws]
    acceptance_point: This checkpoint closes the object-index mismatch without calling the endpoints equal and without storing a comparison certificate. It deliberately does not claim an endpoint geometry isomorphism before the full authored legs and Cartesian uniqueness proofs exist.
    port_status: not-applicable
audits:
  premise_delta:
    ambient_boundary: [Cycle 39 fixed-coefficient canonical route endpoints, Cycle 34 exact core endpoint isomorphisms]
    direction_hypothesis: []
    discharged: [actual G-114 base endpoint geometry object, actual G-114 pulled endpoint geometry object, both fixed-coefficient wrappers, both upper inverse-pair laws]
    remaining: [authored route legs, authored route transports and naturality, compatible raw problem constructor, endpoint comparison isomorphisms and all component laws, solution equivalence, named artifacts, clauses (c)--(d)]
  certificate_provenance:
    discharged: [normalization maps are projections of generatedBaseRouteCoreIsoAt and generatedPulledRouteCoreIsoAt; inverse laws are projections of their Iso laws]
    unresolved: [strong-cartesian authored legs, exactified geometry comparisons, edge and authored-comparator conjugation]
  proof_use:
    used: [pullSelectedGeometry, pullRaw, rawReindexUpper, generatedBaseRouteCoreIsoAt hom and inv, generatedPulledRouteCoreIsoAt hom and inv, fixed-coefficient canonical endpoints]
    unused: [Cycle 43 global mate is reserved for the compatible solution constructor; one-way raw endpoint comparisons await the raw compatible problem]
  structure_field_escape: none-found
  route_integrity: base and pulled endpoints use distinct core isomorphisms and distinct fixed-coefficient canonical endpoints while landing on their corresponding literal G-114 route packages
  predecessor_integrity: the fixed GOAL and completed G-109, G-112, and G-114 declarations are unchanged
  target_fitting: none-found
  vacuity: both constructions quantify over every presentation vertex and rebuild complete geometry and raw data; neither is an identity-only fixture
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [targeted `lake build ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleAuthoredEndpoints` passed and reported 14 declarations standard axioms only; `/tmp/G115Cycle44Check.lean` passed with 18 declarations and each `#print axioms` reported only propext, Classical.choice, Quot.sound; module registered in research-modules.txt and DoctrineFiberProduct.lean; git diff --check and placeholder scan clean]
  blocking_findings: []
  next_obligation: Construct the complete authored base and pulled geometry legs from these normalized endpoints, prove their strong-cartesian qualifications and route-internal transport laws, and assemble the certificate-free compatible raw problem before exactifying the endpoint comparison isomorphisms.
```

## Cycle 45 — revision-5 realization-exact upper primitive and negative-fixture no-go

```yaml
ledger_type: target_cycle_result
goal: G-115-aat-upper-stage-lift
cycle: 45
goal_blob_sha: 13e97feb2063108c91a074862aad07566813ceb15c439899a927aa45758758c9
base_oid: 07aeb56235ae6310045936cd9462ace9d59934e4
tracking_issue: 4250
report_path: research/reports/G-115-aat-upper-stage-lift.md
selection:
  proof_state_ref: revision 5 requires realization-exact upper equivalences and specifically requires NegativeGeometryWitness.coreHom.upper as the forward map of the negative exact upper equivalence
  proof_dag_predecessors: [NegativeGeometryWitness.coreHom, NegativeGeometryWitness.not_hGeom, SignedExactCoreReadingHom.comp, SignedExactCoreReadingHom.refl, revision-5 ExactUpperEquivalence signature]
  proof_obligation: Define the upper-indexed realization algebra and construct the required negative exact upper equivalence before proving its realization nonexistence
  selection_reason: K2b2b-r lists the negative equivalence as a mandatory boundary artifact; it must exist before the planned adapter can reduce realization-exactness to NegativeGeometryWitness.not_hGeom.
  expected_result_type: blocker-fixed
  lean_targets: [ResearchLean/AG/DoctrineFiberProduct/UpperGeometryRealizationExactness.lean, ResearchLean/AG/DoctrineFiberProduct/UpperGeometryRealizationExactnessWitnesses.lean]
  risks: [confusing Atom involutivity with full upper-hom invertibility, hiding carrier mismatch by unchecked cast, replacing the literal G-108 witness with a parallel fixture, reporting partial primitive algebra as target completion]
  unchecked: [RealizationExactUpperEquivalence composition and reading reflection, canonical exact and realized-refinement positive inhabitants, base and pulled route inhabitants, all downstream endpoint and solution artifacts]
result:
  proposed_result_type: blocker-fixed
  stop_reason: goal-defect
  proof_obligation_delta: ExactUpperEquivalence, UpperRealizationTransportSupply, the total-hom supply equivalence, cancellation-transported six-field RealizationExactUpperEquivalence, identity, symmetry, and conditional total-hom/HGeom adapters are implemented. The required negative fixture is impossible before realization data are considered because coreHom.upper.objectMap canonicalizes arbitrary ArchitectureObjects and is not injective, while forward_backward would give it a left inverse.
  completion_candidate: no
  lean_artifacts: [ExactUpperEquivalence, UpperRealizationTransportSupply, upperRealizationTransportSupplyEquiv, RealizationExactUpperEquivalence, RealizationExactUpperEquivalence.refl, RealizationExactUpperEquivalence.symm, RealizationExactUpperEquivalence.homTotalSupply, RealizationExactUpperEquivalence.invTotalSupply, RealizationExactUpperEquivalence.homHGeom, RealizationExactUpperEquivalence.invHGeom, negativeUpperUnitObject, negativeUpperBoolObject, negativeCoreUpper_objectMap_not_injective, no_negativeExactUpperEquivalence]
  source_sha256:
    UpperGeometryRealizationExactness.lean: 6577a3bce6bac41787be079daa6c566eef0cddf8155d6356adcd5e3b3c351451
    UpperGeometryRealizationExactnessWitnesses.lean: 59391b0258bfad0097178cdb58939536aa75b0e1e7ce120aeab2493f0a737aa5
  evidence: [focused Lean checks, declaration-level standard-axiom audits, explicit pair of collapsed but unequal ArchitectureObjects, module registration]
  claim_mapping:
    theorem_names: [negativeUpperUnitObject_ne_boolObject, negativeCoreUpper_objectMap_not_injective, no_negativeExactUpperEquivalence]
    source_labels: [revision 5 K2b2b-r negative upper equivalence, revision 5 target failure policy]
    conjuncts: [literal negative forward map, full upper cancellation, explicit nonvacuous firing of the negative-producer obstruction]
    undischarged_assumptions: [all positive endpoint producers and downstream K2b2b-r algebra]
    acceptance_point: no_negativeExactUpperEquivalence uses the literal required coreHom.upper and its actual objectMap; it does not assume realization failure or accept an obstruction certificate.
    port_status: not-applicable
audits:
  premise_delta:
    discharged: [upper-indexed supply signature, compatibility with existing total-hom supply, explicit cancellation-indexed carrier inverse-law signature, identity, symmetry, conditional HGeom adapters]
    remaining: [negativeExactUpperEquivalence, not_realizationExact_negativeExactUpperEquivalence, downstream completion of K2b2b-r]
  proof_use:
    used: [NegativeGeometryWitness.coreHom.upper.objectMap, ExactUpperEquivalence.forward_backward, SignedExactCoreReadingHom.comp objectMap, SignedExactCoreReadingHom.refl objectMap]
    unused: [NegativeGeometryWitness.not_hGeom is downstream of the equivalence that cannot be constructed]
  certificate_provenance:
    discharged: [noninjectivity is generated by two explicit ArchitectureObjects and definitional equality of their literal forward images]
    unresolved: [a replacement negative fixture requires human mathematical selection]
  structure_field_escape: none; forward_backward is the defining law being refuted, and no blocker certificate is accepted by ExactUpperEquivalence
  route_integrity: the blocker uses the literal G-108 coreHom.upper required by the fixed GOAL, not a parallel fixture
  predecessor_integrity: revision 5 GOAL and G-108 declarations are unchanged
  target_fitting: none-found
  vacuity: noninjectivity fires on two explicit ArchitectureObjects with the same configuration and distinct PUnit/Bool StructureMaps carriers
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none; the failure is classified by revision 5's own explicit policy
  validation_refs: [`./check_research_modules.sh --focused ResearchLean/AG/DoctrineFiberProduct/UpperGeometryRealizationExactness.lean` passed with 72 declarations standard axioms only; `./check_research_modules.sh --focused ResearchLean/AG/DoctrineFiberProduct/UpperGeometryRealizationExactnessWitnesses.lean` passed with 5 declarations standard axioms only; targeted `lake build ResearchLean.AG.DoctrineFiberProduct.UpperGeometryRealizationExactnessWitnesses` passed; research module manifest entries added; git diff --check, hidden/BiDi, placeholder, and reverse-import scans clean]
  blocking_findings: [revision 5 incorrectly treats Atom-level involutivity of coreHom.upper as full SignedExactCoreReadingHom invertibility]
  next_obligation: Human GOAL revision must either choose a genuinely invertible negative SignedExactCoreReadingHom with a realization obstruction, or weaken the negative boundary artifact without weakening the positive realization-exact endpoint target.
```

## Cycle 46 — revision-6 structure-preserving exact upper nonrealization

```yaml
ledger_type: target_cycle_result
goal: G-115-aat-upper-stage-lift
cycle: 46
goal_blob_sha: 65a084cfe6eb6094d2dc33193e0b9185393043f44387e12151c17b355911044c
base_oid: 9bc1189e776bc2cab6eee95abaa3ec5298965dff
tracking_issue: 4250
report_path: research/reports/G-115-aat-upper-stage-lift.md
selection:
  proof_state_ref: revision 6 replaces only the lossy negative producer by a G-115-local configuration-transport automorphism preserving all other ArchitectureObject data
  proof_dag_predecessors: [no_negativeExactUpperEquivalence, nonidentityExactCoreChange public projections, NegativeGeometryWitness.doctrineHom, NegativeGeometryWitness.package, RealizationExactUpperEquivalence.homHGeom, AtomFoundation transport laws]
  proof_obligation: Construct structurePreservingSwapUpper, prove full SignedExactCoreReadingHom self-cancellation including dependent equation and operation fields, assemble the matching total hom, and derive concrete realization nonexistence
  selection_reason: This is the first active K2b2b-r obligation under the reviewed revision-6 target and removes Cycle 45's exact blocker without changing any positive endpoint contract.
  expected_result_type: proof-obligation-discharged
  lean_targets: [ResearchLean/AG/DoctrineFiberProduct/UpperGeometryRealizationExactnessSwapWitnesses.lean]
  risks: [mistaking Atom involutivity for full upper cancellation, dropping opaque ArchitectureObject fields, reusing the lossy object map, hiding dependent equation or operation mismatch, renaming the old HGeom no-go]
  unchecked: [RealizationExactUpperEquivalence composition and reading reflection, canonical exact and realized-refinement positive inhabitants, base and pulled route inhabitants, endpoint comparison and downstream solution artifacts]
result:
  proposed_result_type: proof-obligation-discharged
  proof_state: target-proof-checkpoint
  proof_obligation_delta: The revision-6 negative producer is constructed. Its object map transports configuration only and preserves StructureMaps, SelectedQuantities, and both values. The complete upper self-composition equals refl through named equation-transport and operation-map HEq cancellation bridges. A matching total hom retains the concrete component-A/component-B support-reading contradiction, and the conditional HGeom adapter refutes realization-exactness.
  completion_candidate: no
  lean_artifacts: [structurePreservingSwapObjectMap, structurePreservingSwapAtom_involutive, structurePreservingSwapObjectMap_structureMaps, structurePreservingSwapObjectMap_selectedQuantities, structurePreservingSwapObjectMap_structureMaps_value, structurePreservingSwapObjectMap_selectedQuantities_value, structurePreservingSwapUpper, structurePreservingSwapUpper_equationResidual_transport, structurePreservingSwapUpper_operation_conjugation, structurePreservingSwapUpper_operation_naturality, structurePreservingSwapUpper_invariant_transport, structurePreservingSwapUpper_comp_self_equationTransport, structurePreservingSwapUpper_comp_self_operationMap, structurePreservingSwapUpper_comp_self, structurePreservingSwapCoreHom, structurePreservingSwapExactUpperEquivalence, not_hGeom_structurePreservingSwap, not_realizationExact_structurePreservingSwap]
  source_sha256:
    UpperGeometryRealizationExactnessSwapWitnesses.lean: 37f9f41e5535532045043c44e9a23a7044f670850f30929aabe4395c687d4646
  evidence: [focused Lean file check, in-module standard-axiom audit, explicit full-field extensionality, direct support-reading contradiction, module wiring]
  claim_mapping:
    theorem_names: [structurePreservingSwapUpper_comp_self, structurePreservingSwapExactUpperEquivalence, not_hGeom_structurePreservingSwap, not_realizationExact_structurePreservingSwap]
    source_labels: [revision 6 K2b2b-r negative producer, target material premise ledger realization-exact upper equivalence, target failure policy]
    conjuncts: [same public Atom involution and identity context action, arbitrary ArchitectureObject nonconfiguration-field preservation, full computational cancellation, matching exact lower provenance, concrete realization obstruction]
    undischarged_assumptions: [all positive endpoint producers and downstream K2b2b-r algebra]
    acceptance_point: The nonrealization theorem consumes the newly constructed exact upper equivalence and matching total hom through homHGeom, then closes with a fresh direct support-reading evaluation. It neither assumes nonrealization nor reuses the lossy upper.
    port_status: not-applicable
audits:
  premise_delta:
    ambient_boundary: [public G-108 finite Atom involution, exact doctrine hom, concrete negative geometry package]
    direction_hypothesis: []
    discharged: [structure-preserving object transport, equation residual bridge, operation conjugation and naturality, invariant transport, dependent equation and operation cancellation, full upper equivalence, matching total hom, concrete HGeom nonexistence, realization-exactness nonexistence]
    remaining: [composition and reading reflection for realization-exact equivalences, positive canonical exact and realized-refinement inhabitants, base and pulled compositions, all endpoint and solution artifacts]
  certificate_provenance:
    discharged: [all upper data are constructed from public finite fixture projections and AtomFoundation transport; no realization or cancellation certificate is an input]
    unresolved: [positive realization supplies and endpoint geometry isomorphisms]
  proof_use:
    used: [nonidentityExactCoreChange atom equivalence, extraction and composition laws, direct configuration transport, equation residual computation, operation conjugation, invariant computation, SignedExactCoreReadingHom.ext, NegativeGeometryWitness doctrine hom and support reading, RealizationExactUpperEquivalence.homHGeom]
    unused: [the old NegativeGeometryWitness.not_hGeom theorem is not called; the direct contradiction is reproved for the new total hom]
  structure_field_escape: none; opaque object fields are preserved by named equalities and the cancellation theorem covers every computational field required by SignedExactCoreReadingHom.ext
  route_integrity: the matching total hom uses the reviewed negative doctrine hom and exactly the new upper map; its context action and Atom firing reproduce the concrete obstruction
  predecessor_integrity: G-108 declarations and the revision-6 GOAL are unchanged; no Formal characterization API addition was necessary after focused elaboration
  target_fitting: none-found
  vacuity: the Atom map swaps componentA/componentB, the geometry package has a concrete componentA support read, and the image context concretely fails the corresponding componentB read
  one_way_as_equivalence: none-found; both exact upper cancellation directions are the proved full self-composition theorem
  goal_or_report_reinterpretation: none-found
  validation_refs: [`./check_research_modules.sh --focused ResearchLean/AG/DoctrineFiberProduct/UpperGeometryRealizationExactnessSwapWitnesses.lean` passed and reported 21 declarations standard axioms only; targeted `lake build ResearchLean.AG.DoctrineFiberProduct.UpperGeometryRealizationExactnessSwapWitnesses` passed; module registered in research-modules.txt and DoctrineFiberProduct.lean; Research aggregate and full build were not run]
  blocking_findings: []
  next_obligation: Complete RealizationExactUpperEquivalence composition and reading reflection, then construct the explicit canonical exact and realized-refinement positive inhabitants and their base/pulled compositions.
```

## Cycle 47 — realization-exact composition and reading reflection

```yaml
ledger_type: target_cycle_result
goal: G-115-aat-upper-stage-lift
cycle: 47
goal_blob_sha: 65a084cfe6eb6094d2dc33193e0b9185393043f44387e12151c17b355911044c
base_oid: 65850c0bb4ad12a61d19a5c8709581be61dfee75
tracking_issue: 4250
report_path: research/reports/G-115-aat-upper-stage-lift.md
selection:
  proof_state_ref: Cycle 46 discharged the revision-6 negative producer and selected the first remaining positive realization algebra obligation
  proof_dag_predecessors: [ExactUpperEquivalence.comp, UpperRealizationTransportSupply.comp, RealizationExactUpperEquivalence componentwise inverse laws, forward and backward reading preservation]
  proof_obligation: Prove composition for RealizationExactUpperEquivalence and derive Support, Axis, and Observable reading reflection from inverse preservation and component cancellation
  selection_reason: These are the minimal algebraic operations required before the canonical exact and realized-refinement endpoint inhabitants can be composed into base and pulled routes.
  expected_result_type: proof-obligation-discharged
  lean_targets: [ResearchLean/AG/DoctrineFiberProduct/UpperGeometryRealizationExactness.lean]
  risks: [hiding dependent casts in unchecked simplification, assuming reflection independently, losing reverse composition order, introducing a lower inverse]
  unchecked: [canonical exact and realized-refinement positive inhabitants, base and pulled route inhabitants, endpoint comparison and downstream solution artifacts]
result:
  proposed_result_type: proof-obligation-discharged
  proof_state: target-proof-checkpoint
  proof_obligation_delta: Realization-exact upper equivalences now compose in route order with reverse-order inverse supplies. A dependent-sigma cancellation proof discharges all six transported carrier inverse laws. Forward-backward Atom cancellation is exposed, and three iff theorems derive reading reflection by applying the inverse supply preservation law and then the corresponding component cancellation.
  completion_candidate: no
  lean_artifacts: [ExactUpperEquivalence.forwardBackwardAtom, ExactUpperEquivalence.backwardForwardAtom, RealizationExactUpperEquivalence.comp, RealizationExactUpperEquivalence.supportReads_iff, RealizationExactUpperEquivalence.axisReads_iff, RealizationExactUpperEquivalence.observableReads_iff]
  source_sha256:
    UpperGeometryRealizationExactness.lean: 2a26f1bc7fc44a97bdde0754694a04525121e10662551a56a580daa3e1acbafe
  evidence: [focused Lean file check, targeted direct module build, in-module standard-axiom audit, dependent Sigma cancellation, inverse-preservation proof-use]
  claim_mapping:
    theorem_names: [RealizationExactUpperEquivalence.comp, RealizationExactUpperEquivalence.supportReads_iff, RealizationExactUpperEquivalence.axisReads_iff, RealizationExactUpperEquivalence.observableReads_iff]
    source_labels: [target proof artifacts realization-exact minimal algebra, material premise ledger realization-exact upper equivalence]
    conjuncts: [composition, Support reflection, Axis reflection, Observable reflection]
    undischarged_assumptions: [positive endpoint realization supplies and downstream geometry comparison data]
    acceptance_point: Each reflection theorem consumes the stored backward reading-preservation field and the relevant forward-backward component inverse law; Support additionally consumes authored Atom cancellation. No reflected-reading premise is accepted as input.
    port_status: not-applicable
audits:
  premise_delta:
    ambient_boundary: [reviewed exact upper equivalence and bidirectional realization supplies]
    direction_hypothesis: []
    discharged: [realization-exact composition, Support reading reflection, Axis reading reflection, Observable reading reflection]
    remaining: [canonical exact endpoint inhabitant, realized-refinement endpoint inhabitant, base and pulled compositions, endpoint comparison and all downstream solution artifacts]
  certificate_provenance:
    discharged: [all composite inverse laws are derived from the two input realization-exact structures; all reflection laws are derived rather than supplied]
    unresolved: [positive endpoint supply provenance]
  proof_use:
    used: [both exact-upper context cancellation laws, both component cancellation layers in composition, inverse supply reading preservation, Atom cancellation for Support]
    unused: [no total hom or HGeom adapter is needed for the upper-only algebra]
  structure_field_escape: none; composition accepts only the two predecessor realization-exact structures and derives every output field
  route_integrity: forward supplies compose in forward route order and inverse supplies in reverse order; the dependent total-space proof fixes the transported carrier indices before extracting component equality
  predecessor_integrity: no reviewed predecessor module or GOAL statement changed
  target_fitting: none-found
  vacuity: each iff has its original reading proposition on one side and the concrete forward carrier and Atom maps on the other
  one_way_as_equivalence: none-found; reverse implications explicitly call the inverse supply
  goal_or_report_reinterpretation: none-found
  validation_refs: [`./check_research_modules.sh --focused ResearchLean/AG/DoctrineFiberProduct/UpperGeometryRealizationExactness.lean` passed and reported 78 declarations standard axioms only; targeted `lake build ResearchLean.AG.DoctrineFiberProduct.UpperGeometryRealizationExactness` passed; Research aggregate and full build were not run]
  blocking_findings: []
  next_obligation: Construct the explicit canonical exact and realized-refinement RealizationExactUpperEquivalence inhabitants, then compose them into the base and pulled route inhabitants.
```

## Cycle 48 — theorem-generated positive realization-exact route inhabitants

```yaml
ledger_type: target_cycle_result
goal: G-115-aat-upper-stage-lift
cycle: 48
goal_blob_sha: 65a084cfe6eb6094d2dc33193e0b9185393043f44387e12151c17b355911044c
base_oid: 0a8692367fa8906270512206def66ddbb0e5c37c
tracking_issue: 4250
report_path: research/reports/G-115-aat-upper-stage-lift.md
selection:
  proof_state_ref: Cycle 47 supplied realization-exact composition and reading reflection; the next fixed obligation is to generate the positive primitive inhabitants and actual route compositions
  proof_dag_predecessors: [inverseCorePackageForwardUpper and backward cancellation, generated exact carrier comparisons, selected realized-refinement forward and backward uppers, generated refinement carrier comparisons, RealizationExactUpperEquivalence.comp]
  proof_obligation: Construct bidirectional upper realization supplies and six component inverse laws for the canonical exact and realized-refinement inverse packages, then specialize and compose them for both generated routes
  selection_reason: This discharges the positive realization provenance required before endpoint comparison isomorphisms may be constructed; accepting endpoint HGeom or realization certificates would violate the fixed GOAL.
  expected_result_type: proof-obligation-discharged
  lean_targets: [ResearchLean/AG/DoctrineFiberProduct/UpperGeometryMateComponents.lean]
  risks: [repackaging only the forward HGeom, using the forward context inverse instead of the authored backward upper, retaining realization as caller data, omitting one carrier or one cancellation direction, composing route legs in the wrong order]
  unchecked: [endpoint comparison isomorphisms, canonicalized solution equivalence, reselection conjugation, paired cochain theorem, negative problem, exchange-exact companion iff]
result:
  proposed_result_type: proof-obligation-discharged
  proof_state: target-proof-checkpoint
  proof_obligation_delta: Generic exact and realized-refinement inverse packages now each generate independent forward and backward UpperRealizationTransportSupply values from concrete carrier maps, reading preservation, and naturality. Their six component inverse laws yield RealizationExactUpperEquivalence inhabitants. Specializations to both base-first legs and both pulled-first legs are composed in route order, and the resulting forward upper maps are identified with the actual generated route uppers.
  completion_candidate: no
  lean_artifacts: [exactBackwardSupportComp, exactBackwardAxisComp, exactBackwardObservableComp, exactInversePackageUpperEquivalence, exactForwardUpperRealizationSupply, exactBackwardUpperRealizationSupply, exactInversePackageRealizationExact, refinementBackwardSupportComp, refinementBackwardAxisComp, refinementBackwardObservableComp, refinementInversePackageUpperEquivalence, refinementForwardUpperRealizationSupply, refinementBackwardUpperRealizationSupply, refinementInversePackageRealizationExact, baseRouteExactRealizationExact, baseRouteRefinementRealizationExact, baseRouteRealizationExact, baseRouteRealizationExact_forward_eq, pulledRouteRefinementRealizationExact, pullbackTargetExactRealizationExact, pulledRouteRealizationExact, pulledRouteRealizationExact_forward_eq]
  source_sha256:
    UpperGeometryMateComponents.lean: 216526380f47d2a55b49aec320d115b994a98f968296363bd33ce6c14fc4ebbe
  evidence: [focused Lean file check, targeted direct module build, in-module standard-axiom audit, concrete forward and backward reading/naturality laws, componentwise HEq cancellation, actual route-upper identifications]
  claim_mapping:
    theorem_names: [exactInversePackageRealizationExact, refinementInversePackageRealizationExact, baseRouteRealizationExact, pulledRouteRealizationExact, baseRouteRealizationExact_forward_eq, pulledRouteRealizationExact_forward_eq]
    source_labels: [revision 6 K2b2b-r positive producer, target material premise ledger realization-exact upper equivalence, target proof artifacts endpoint generation]
    conjuncts: [canonical exact inhabitant, realized-refinement inhabitant, base route composition, pulled route composition, actual route-upper agreement]
    undischarged_assumptions: [endpoint geometry inverse construction and downstream solution contracts]
    acceptance_point: Both primitive inhabitants consume authored forward and backward upper maps, concrete Support Axis Observable maps, reading preservation, restriction naturality, and both component cancellation directions. Route inhabitants are theorem-generated specializations and compositions, not caller fields.
    port_status: not-applicable
audits:
  premise_delta:
    ambient_boundary: [exact inverse-package constructors, realized-reflection selected transport, existing generated forward carrier comparisons]
    direction_hypothesis: []
    discharged: [generic exact backward supply, generic realized-refinement backward supply, both generic realization-exact inhabitants, base-route two-leg composition, pulled-route two-leg composition, route upper-map agreement]
    remaining: [endpoint comparison isomorphisms, canonicalized solution and reselection equivalences, named positive and negative problems, paired cochain relation, exchange-exact companion iff]
  certificate_provenance:
    discharged: [all supplies and inverse laws are generated from public exact or realized-reflection transport data; no HGeom realization or route leg is an input field]
    unresolved: [geometry endpoint inverse provenance and strong-cartesian uniqueness use]
  proof_use:
    used: [exact forward and backward upper cancellation, selected refinement forward and backward upper cancellation, Support Axis Observable forward comparison laws, newly exposed backward comparison laws, six carrier HEq cancellation pairs, Cycle 47 composition]
    unused: [opaque G-112 selected-domain iso is not a producer; conditional HGeom adapters are not used]
  structure_field_escape: none; the output structures are assembled field by field from concrete maps and the six inverse laws are proved from carrier transport HEqs
  route_integrity: base route composes exact then base-refinement; pulled route composes pulled-refinement then exact; both forward composites are definitionally identified with the actual route hom upper map
  predecessor_integrity: G-108 G-112 G-114 and Formal are unchanged; only G-115 mate component API and this ledger changed
  target_fitting: none-found
  vacuity: generic inhabitants quantify over arbitrary target geometry and actual exact or realized-reflection inputs; route specializations use an active context and actual TargetGeometry, while pointwise specialization through sourceTargetGeometryAt remains for the endpoint-comparison stage
  one_way_as_equivalence: none-found; every primitive has independent backward carrier maps and both cancellation directions
  goal_or_report_reinterpretation: none-found
  validation_refs: [`./check_research_modules.sh --focused ResearchLean/AG/DoctrineFiberProduct/UpperGeometryMateComponents.lean` passed and reported 59 declarations standard axioms only; targeted `lake build ResearchLean.AG.DoctrineFiberProduct.UpperGeometryMateComponents` passed; Research aggregate and full build were not run]
  blocking_findings: []
  next_obligation: Use the theorem-generated base and pulled route realization-exact inhabitants to construct the canonical endpoint comparison isomorphisms and componentwise conjugation solution equivalence.
```

## Cycle 49 — finite route-realization and endpoint-normalization bridge

```yaml
ledger_type: target_cycle_result
goal: G-115-aat-upper-stage-lift
cycle: 49
goal_blob_sha: 65a084cfe6eb6094d2dc33193e0b9185393043f44387e12151c17b355911044c
base_oid: 99285338c976b887ed8a6cc1b972722824246956
tracking_issue: 4250
report_path: research/reports/G-115-aat-upper-stage-lift.md
selection:
  proof_state_ref: Cycle 48 generated realization-exact inhabitants for arbitrary active contexts and target geometries; the endpoint stage needs their exact finite-vertex specialization separated from core-only normalization
  proof_obligation: Fix both generated route realization equivalences at every compatible finite vertex, identify their forward uppers with the literal route legs, and package the independent base and pulled endpoint core upper equivalences without inferring realization from object normalization
  selection_reason: Endpoint comparison construction must consume theorem-generated route realization while retaining the distinction between realization data and the upper-pair object normalization already used for canonical-authored endpoints.
  expected_result_type: proof-obligation-discharged
  lean_targets: [ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCompatibleEndpointComparisons.lean]
  risks: [treating core upper cancellation as realization, silently inserting Support Axis Observable maps, using the raw G-114 one-way comparison, failing to specialize through sourceTargetGeometryAt, conflating route and endpoint equivalences]
  unchecked: [canonical-authored route realization supplies, complete endpoint comparison homs, strong-cartesian factor laws, endpoint isomorphisms, edge naturality, comparator conjugation, solution equivalence]
result:
  proposed_result_type: proof-obligation-discharged
  proof_state: target-proof-checkpoint
  proof_obligation_delta: The base and pulled route ExactUpperEquivalence values and their RealizationExactUpperEquivalence inhabitants are now specialized at every compatible finite vertex through sourceTargetGeometryAt. Their forward maps are identified with the literal generated route-leg uppers. Separately, the base and pulled core endpoint isomorphisms generate exact upper equivalences with both cancellation laws, but no realization supply is inferred from those core-only structures.
  completion_candidate: no
  lean_artifacts: [generatedBaseRouteUpperEquivalenceAt, generatedBaseRouteRealizationExactAt, generatedBaseRouteUpperEquivalenceAt_forward_eq, generatedPulledRouteUpperEquivalenceAt, generatedPulledRouteRealizationExactAt, generatedPulledRouteUpperEquivalenceAt_forward_eq, generatedBaseEndpointUpperEquivalenceAt, generatedPulledEndpointUpperEquivalenceAt]
  source_sha256:
    UpperGeometryCompatibleEndpointComparisons.lean: 94841a1059d379a6c931d1d54759a24e96bbb1192f75a96cd63c6e8d1a44c961
  evidence: [focused Lean file check, targeted direct module dependency-DAG build, namespace standard-axiom audit, explicit finite specialization, literal route-upper equalities, endpoint upper cancellation from core isomorphisms]
audits:
  premise_delta:
    ambient_boundary: [certificate-free compatible input, generated finite route legs, theorem-generated route realization inhabitants, generated endpoint core isomorphisms]
    direction_hypothesis: []
    discharged: [finite base route realization inhabitant, finite pulled route realization inhabitant, both literal route-upper identifications, base endpoint exact upper equivalence, pulled endpoint exact upper equivalence]
    remaining: [canonical-authored route realization, endpoint complete geometry comparison homs and inverse laws, comparison naturality and comparator compatibility, solution equivalence]
  certificate_provenance:
    route_realization: specialized from Cycle 48 constructors using the actual sourceTargetGeometryAt geometry; no endpoint field or theorem argument is accepted
    endpoint_upper: projected from theorem-generated core isomorphism hom and inv with cancellation obtained by congrArg on the categorical inverse laws
    unresolved: endpoint Support Axis Observable comparison maps are not inferred from the endpoint upper equivalence
  proof_use:
    used: [baseRouteRealizationExact, pulledRouteRealizationExact, sourceTargetGeometryAt, actual generated route legs, both endpoint core iso inverse laws]
    rejected_refutation: A generic claim that pullGeometryPackageAlongUpperPair alone supplies realization was tested and rejected at carrier-map typing; no such declaration remains
  structure_field_escape: none; realization values are theorem-generated route specializations, while endpoint structures contain upper maps and cancellation only
  route_integrity: both finite route equivalences unfold to the same exact/refinement order as the actual generated route legs
  predecessor_integrity: G-108 G-112 G-114 Formal and the fixed GOAL are unchanged; one G-115 bridge module and its registration are added
  target_fitting: none-found
  vacuity: declarations quantify over every vertex of every certificate-free compatible input; no inhabitation or endpoint comparison is accepted from the caller
  one_way_as_equivalence: none-found; route inhabitants retain both realization directions and six cancellation laws, while endpoint core equivalences are explicitly not claimed realization-exact
  goal_or_report_reinterpretation: none-found
  validation_refs: [`./check_research_modules.sh --focused ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCompatibleEndpointComparisons.lean` passed and reported 8 declarations standard axioms only; targeted `lake build ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleEndpointComparisons` passed; Research aggregate and full build were not run]
  blocking_findings: []
  next_obligation: Generate the canonical-authored route realization supplies from the explicit inverse-package transports and normalization laws, then use strong-cartesian factorization to construct the base and pulled complete endpoint comparison isomorphisms.
```

## Cycle 50 — direct canonical-authored route normalization

```yaml
ledger_type: target_cycle_result
goal: G-115-aat-upper-stage-lift
cycle: 50
goal_blob_sha: 65a084cfe6eb6094d2dc33193e0b9185393043f44387e12151c17b355911044c
base_oid: dda963ca50c80c95dc03cb71b2dd6753eaafb941
tracking_issue: 4250
report_path: research/reports/G-115-aat-upper-stage-lift.md
selection:
  proof_state_ref: Cycle 49 separated theorem-generated route realization from the opaque G-114 selected-endpoint core normalization
  proof_obligation: Construct the canonical-authored base and pulled route geometries by directly normalizing the actual source geometry along the two theorem-generated realization-exact route equivalences, and expose both realization directions and the raw normalization law
  selection_reason: The endpoint comparison must start from the explicit inverse-package route realization, not by upgrading the unrelated G-114 selected-endpoint core isomorphism to realization data.
  expected_result_type: proof-obligation-discharged
  lean_targets: [ResearchLean/AG/DoctrineFiberProduct/UpperGeometryRealizationNormalization.lean]
  risks: [confusing direct route normalization with G-114 selected-endpoint normalization, alias-only checkpoint, losing the opposite route order, exposing only a forward supply, failing to connect raw normalization to upper cancellation]
  unchecked: [complete canonical-authored route geometry legs, composite context cancellation, strong-cartesian factor constructors, complete endpoint comparison isomorphisms, edge naturality, comparator conjugation, solution equivalence]
result:
  proposed_result_type: proof-obligation-discharged
  proof_state: target-proof-checkpoint
  proof_obligation_delta: The actual source geometry is now normalized directly along the base and pulled theorem-generated ExactUpperEquivalence values. The two direct route objects retain the generated route cores and authored coefficient ring, expose genuine forward and backward realization supplies from the Cycle 49 inhabitants, and satisfy literal backward raw reindexing plus forward cancellation. No realization is inferred for the G-114 selected-endpoint core equivalences.
  completion_candidate: no
  lean_artifacts: [realizationNormalizedGeometry, realizationNormalizedGeometry_core, realizationNormalizedGeometry_coefficient, canonicalAuthoredBaseRouteGeometryAt, canonicalAuthoredPulledRouteGeometryAt, canonicalAuthoredBaseRouteGeometryAt_core, canonicalAuthoredPulledRouteGeometryAt_core, canonicalAuthoredBaseRouteGeometryAt_coefficient, canonicalAuthoredPulledRouteGeometryAt_coefficient, canonicalAuthoredBaseRouteGeometryAt_raw, canonicalAuthoredPulledRouteGeometryAt_raw, canonicalAuthoredBaseRouteForwardSupplyAt, canonicalAuthoredBaseRouteBackwardSupplyAt, canonicalAuthoredPulledRouteForwardSupplyAt, canonicalAuthoredPulledRouteBackwardSupplyAt, canonicalAuthoredBaseRouteRaw_forward, canonicalAuthoredPulledRouteRaw_forward]
  source_sha256:
    UpperGeometryRealizationNormalization.lean: 0772c1f81fea34df93eb3f7537d15927b0c580944630d22610447316dcc809b4
  evidence: [focused Lean file check, namespace standard-axiom audit, direct authored source geometry use, both route-order specializations, both realization directions, explicit raw reindexing cancellation]
audits:
  premise_delta:
    ambient_boundary: [certificate-free compatible input, actual source geometry, theorem-generated finite route equivalences and realization inhabitants]
    direction_hypothesis: []
    discharged: [direct base canonical-authored geometry normalization, direct pulled canonical-authored geometry normalization, both forward realization supplies, both backward realization supplies, both coefficient identities, both raw backward normalizations, both forward raw cancellation laws]
    remaining: [complete direct route geometry homs, route context cancellation, strong-cartesian universality, endpoint comparison homs and inverse laws, comparison naturality and comparator compatibility, solution equivalence]
  certificate_provenance:
    route_realization: both supply directions are projections of the theorem-generated Cycle 49 RealizationExactUpperEquivalence inhabitants specialized at the actual finite vertex
    object_normalization: pullGeometryPackageAlongUpperPair is applied to the actual source geometry with the explicit composite route forward and backward upper maps
    raw_normalization: the backward upper literally defines the direct raw system and backward_forward cancellation proves its forward recovery
    excluded: generatedBaseEndpointUpperEquivalenceAt and generatedPulledEndpointUpperEquivalenceAt are not upgraded or consumed as realization producers
  proof_use:
    used: [generatedBaseRouteUpperEquivalenceAt, generatedPulledRouteUpperEquivalenceAt, generatedBaseRouteRealizationExactAt, generatedPulledRouteRealizationExactAt, pullGeometryPackageAlongUpperPair, rawReindexUpper_cancel, both backward_forward laws]
  structure_field_escape: none; no route geometry leg, endpoint comparison, realization inhabitant, context cancellation, or cartesianness is accepted from the compatible input
  route_integrity: base and pulled direct normalizations consume the already reviewed explicit exact/refinement composites in their distinct actual route orders
  predecessor_integrity: G-108 G-112 G-114 Formal and the fixed GOAL are unchanged; one G-115 normalization module and its registrations are added
  target_fitting: none-found
  vacuity: all artifacts are data or equations at every vertex of every compatible input; no new Prop premise is introduced
  one_way_as_equivalence: none-found; both genuine realization supply directions remain present and originate in the reviewed six-cancellation inhabitants
  goal_or_report_reinterpretation: none-found
  validation_refs: [`./check_research_modules.sh --focused ResearchLean/AG/DoctrineFiberProduct/UpperGeometryRealizationNormalization.lean` passed and reported 17 declarations under AAT.AG.DoctrineFiberProduct standard axioms only; targeted `lake build ResearchLean.AG.DoctrineFiberProduct.UpperGeometryRealizationNormalization` passed; Research aggregate and full build were not run]
  blocking_findings: []
  next_obligation: Build the direct base and pulled RefinementGeometryHom legs from these supplies, proving composite context cancellation internally, then prove their strong-cartesian universal property for the endpoint comparison isomorphisms.
```

## Cycle 51 — theorem-generated composite context cancellation

```yaml
ledger_type: target_cycle_result
goal: G-115-aat-upper-stage-lift
cycle: 51
goal_blob_sha: 65a084cfe6eb6094d2dc33193e0b9185393043f44387e12151c17b355911044c
base_oid: ba1697772ee3aa5a4f702ec18280a94e7fb82958
tracking_issue: 4250
report_path: research/reports/G-115-aat-upper-stage-lift.md
selection:
  proof_state_ref: Cycle 50 direct canonical-authored route normalizations have theorem-generated realization supplies but still need the composite context cancellation used by overlap transport
  proof_obligation: Derive forward-after-chosen-inverse context-object cancellation for the actual base and pulled composite route uppers, in their distinct route orders, and specialize it to every finite compatible vertex
  selection_reason: The direct geometry legs must not accept context cancellation as a compatible-input field; the equality must be generated from the explicit exact and realized-refinement transports before constructing overlap preservation.
  expected_result_type: proof-obligation-discharged
  lean_targets: [ResearchLean/AG/DoctrineFiberProduct/UpperGeometryRouteContextCancellation.lean]
  risks: [accepting a new context equality premise, confusing an equivalence counit iso with raw context equality, reversing the base or pulled cancellation order, proving only a generic route theorem without finite specialization]
  unchecked: [direct route coverage and overlap transport, complete direct route geometry homs, strong-cartesian factor constructors, endpoint comparison isomorphisms, edge naturality, comparator conjugation, solution equivalence]
result:
  proposed_result_type: proof-obligation-discharged
  proof_state: target-proof-checkpoint
  proof_obligation_delta: The base composite context cancellation is generated by cancelling the inner exact transport and then the outer realized-refinement transport. The pulled composite cancellation is independently generated in the opposite order. Both are specialized to the literal generated route bases at every compatible finite vertex, with no new input field or theorem premise.
  completion_candidate: no
  lean_artifacts: [baseRouteContextForward_backward_ctx, pulledRouteContextForward_backward_ctx, canonicalAuthoredBaseRouteContextForward_backwardAt, canonicalAuthoredPulledRouteContextForward_backwardAt]
  source_sha256:
    UpperGeometryRouteContextCancellation.lean: 714955aae38617b559d8e3f7dc9c3a60f537be4cfbd4f7b69edbec010dccb940
  evidence: [focused Lean file check, namespace standard-axiom audit, explicit two-stage cancellation, finite sourceTargetGeometryAt specialization]
audits:
  premise_delta:
    ambient_boundary: [active context, actual target geometry, certificate-free compatible finite input]
    direction_hypothesis: []
    discharged: [base composite forward-after-inverse context equality, pulled composite forward-after-inverse context equality, finite base specialization, finite pulled specialization]
    remaining: [direct route coverage and overlap preservation, complete direct RefinementGeometryHom legs, strong-cartesian universality, endpoint comparison homs and inverse laws, comparison naturality and comparator compatibility, solution equivalence]
  certificate_provenance:
    base: generatedExactContextForward_backward_ctx followed by generatedRefinementContextForward_backward_ctx
    pulled: generatedRefinementContextForward_backward_ctx followed by generatedExactContextForward_backward_ctx
    finite: specialized through the actual retargeted context and sourceTargetGeometryAt; no stored context equality is read from input
  proof_use:
    used: [actual baseRouteGeometryHom base, actual pulledRouteGeometryHom base, exact inverse-package context cancellation, realized-refinement context cancellation, sourceTargetGeometryAt]
  structure_field_escape: none; context cancellation remains a theorem output and is not added to UpperGeometryCompatibleProblemInputData
  route_integrity: the two proof terms cancel the exact and realized-refinement stages in the order forced by each actual composite route
  predecessor_integrity: G-108 G-112 G-114 Formal and the fixed GOAL are unchanged; one G-115 context-cancellation module and its registrations are added
  target_fitting: none-found
  vacuity: the declarations are equalities for every target context and every finite compatible vertex; no Prop premise or inhabitance argument is introduced
  one_way_as_equivalence: not-applicable; the result is object-level cancellation of already reviewed context equivalences, not a new realization or endpoint equivalence claim
  goal_or_report_reinterpretation: none-found
  validation_refs: [`./check_research_modules.sh --focused ResearchLean/AG/DoctrineFiberProduct/UpperGeometryRouteContextCancellation.lean` passed and reported 4 declarations under AAT.AG.DoctrineFiberProduct standard axioms only; targeted `lake build ResearchLean.AG.DoctrineFiberProduct.UpperGeometryRouteContextCancellation` passed; Research aggregate and full build were not run]
  blocking_findings: []
  next_obligation: Use the generated context cancellation with the Cycle 50 realization supplies and raw recovery to construct the direct base and pulled RefinementGeometryHom legs, including coverage and overlap preservation, without new compatible-input fields.
```

## Cycle 52 — direct canonical-authored route geometry homs

```yaml
ledger_type: target_cycle_result
goal: G-115-aat-upper-stage-lift
cycle: 52
goal_blob_sha: 65a084cfe6eb6094d2dc33193e0b9185393043f44387e12151c17b355911044c
base_oid: e00a907e37a0b88b6deb676475d102a8d36d7163
tracking_issue: 4250
report_path: research/reports/G-115-aat-upper-stage-lift.md
selection:
  proof_state_ref: Cycle 50 generated direct normalizations and forward realization supplies; Cycle 51 generated the raw context cancellation required by overlap transport
  proof_obligation: Construct complete base and pulled RefinementGeometryHom legs from each canonical-authored route normalization to the authored source geometry, using the literal lax route bases and no caller-supplied geometry contract
  selection_reason: Endpoint comparison requires actual geometry morphisms, not only object normalizations, upper supplies, or raw cancellation lemmas.
  expected_result_type: proof-obligation-discharged
  lean_targets: [ResearchLean/AG/DoctrineFiberProduct/UpperGeometryDirectRouteHoms.lean]
  risks: [casting the existing generated-route geometry contract onto a different normalization, replacing the lax lower route by an exact hom, accepting coverage overlap or context cancellation as input data, using only core transport, omitting coefficient identity]
  unchecked: [strong-cartesianness of the direct route homs, universal factor constructors, endpoint comparison isomorphisms, edge naturality, comparator conjugation, solution equivalence]
result:
  proposed_result_type: proof-obligation-discharged
  proof_state: target-proof-checkpoint
  proof_obligation_delta: A generic upper-pair pullback constructor now builds all coverage, overlap, coefficient, raw, Support, Axis, Observable, reading, and naturality fields over an actual lax route base. Premise-free finite base and pulled specializations consume the literal generated route bases, theorem-generated forward realization supplies, upper cancellation, and Cycle 51 context cancellation.
  completion_candidate: no
  lean_artifacts: [upperPairPullRefinementGeomReadHom, upperPairPullRefinementGeometryHom, canonicalAuthoredBaseRouteGeometryHomAt, canonicalAuthoredBaseRouteGeometryHomAt_base, canonicalAuthoredBaseRouteGeometryHomAt_coefficientHom, canonicalAuthoredPulledRouteGeometryHomAt, canonicalAuthoredPulledRouteGeometryHomAt_base, canonicalAuthoredPulledRouteGeometryHomAt_coefficientHom]
  source_sha256:
    UpperGeometryDirectRouteHoms.lean: 9417879a97760a8a69d846becee0bf6bef1ad0d12bc088b449c5dc75921ce38e
  evidence: [focused Lean file check, targeted direct-module dependency-DAG build, 8-declaration namespace standard-axiom audit, complete RefinementGeomReadHom field construction, literal finite route specializations]
audits:
  premise_delta:
    ambient_boundary: [authored source geometry, actual generated lax route bases, theorem-generated route realization equivalences]
    direction_hypothesis: []
    discharged: [direct route coverage preservation, direct route selected-overlap preservation, coefficient identity, forward raw recovery, Support Axis Observable transport, reading preservation, context naturality, complete base and pulled RefinementGeometryHom legs]
    remaining: [strong-cartesian universality for both direct route legs, endpoint comparison homs and inverse laws, comparison naturality and comparator compatibility, solution equivalence]
  certificate_provenance:
    generic: normalized coverage is definitional pullback; overlap uses the four generated raw context equalities; raw recovery uses backward-comp-forward upper cancellation; carrier maps and laws use the supplied theorem-generated forward upper realization supply
    base: actual generatedBaseRouteLegAt base, generatedBaseRouteUpperEquivalenceAt backward and backward_forward, canonicalAuthoredBaseRouteForwardSupplyAt, canonicalAuthoredBaseRouteContextForward_backwardAt
    pulled: actual generatedPulledRouteLegAt base, generatedPulledRouteUpperEquivalenceAt backward and backward_forward, canonicalAuthoredPulledRouteForwardSupplyAt, canonicalAuthoredPulledRouteContextForward_backwardAt
  proof_use:
    used: [literal lax lower route bases, pullGeometryPackageAlongUpperPair coverage and overlap definitions, rawReindexUpper_cancel, forward realization support axis observable maps and reading naturality laws, Cycle 51 context cancellation]
    deliberately_not_used: [existing generated-route geometry contract, G-114 selected endpoint comparison, backward realization supply, opaque selected-domain iso]
  structure_field_escape: none; the compatible input is unchanged and neither geometry contract nor cancellation is accepted from the caller
  route_integrity: both finite homs retain the literal generated route base and independently generated base versus pulled upper equivalence
  predecessor_integrity: G-108 G-112 G-114 Formal and the fixed GOAL are unchanged; one G-115 direct-route module and its registrations are added
  target_fitting: none-found; the generic constructor normalizes along f.upper itself and each finite specialization uses the actual route base definitionally
  vacuity: coverage contains nine explicit preservation functions, overlap is constructed at every context triple, and all realization maps and laws are populated; no existence-only wrapper is used
  one_way_as_equivalence: not-applicable; these are forward complete geometry homs and are not claimed to be endpoint isomorphisms
  goal_or_report_reinterpretation: none-found
  validation_refs: [`./check_research_modules.sh --focused ResearchLean/AG/DoctrineFiberProduct/UpperGeometryDirectRouteHoms.lean` passed and reported 8 declarations under AAT.AG.DoctrineFiberProduct standard axioms only; targeted `lake build ResearchLean.AG.DoctrineFiberProduct.UpperGeometryDirectRouteHoms` passed with 4103 jobs; Research aggregate and full build were not run]
  blocking_findings: []
  next_obligation: Prove both direct canonical-authored route homs strongly Cartesian by constructing universal factors from the backward realization supplies and the componentwise inverse laws, then derive the endpoint comparison isomorphisms by strong-cartesian uniqueness.
```

## Cycle 53 — dependent realization-factor carrier equivalences

```yaml
ledger_type: target_cycle_result
goal: G-115-aat-upper-stage-lift
cycle: 53
goal_blob_sha: 65a084cfe6eb6094d2dc33193e0b9185393043f44387e12151c17b355911044c
base_oid: d0f76895412d208c73c2a7799dd0e6c1994b8e41
tracking_issue: 4250
report_path: research/reports/G-115-aat-upper-stage-lift.md
selection:
  proof_state_ref: Cycle 52 constructed the complete direct route homs; their strong-Cartesian factor must invert realization carrier maps in dependent context fibers
  proof_obligation: Convert the six component inverse laws of every RealizationExactUpperEquivalence into actual equivalences of the dependent Support Axis Observable total spaces, fiberwise inverse-at-forward maps, both cancellation directions, and reading reflection
  selection_reason: The universal factor cannot be constructed by a nondependent inverse function because its carrier types vary with the context equivalence; the dependent cast and cancellation proof must be fixed before the factor contract.
  expected_result_type: proof-obligation-discharged
  lean_targets: [ResearchLean/AG/DoctrineFiberProduct/UpperGeometryRealizationFactorCarriers.lean]
  risks: [discarding dependent context indices, using only one inverse direction, silently identifying transported carrier types, proving set-level bijectivity without reading reflection, treating this algebra checkpoint as strong cartesianness]
  unchecked: [inverse carrier naturality, complete universal factor geometry contract, factorization and uniqueness, direct route strong cartesianness, endpoint comparison isomorphisms, solution equivalence]
result:
  proposed_result_type: proof-obligation-discharged
  proof_state: target-proof-checkpoint
  proof_obligation_delta: The theorem-generated forward and backward realization supplies now form genuine Equiv values on the three dependent Sigma carrier spaces. Their inverse-at-forward maps land in the literal source context fiber, reflect all three readings, and satisfy both fiberwise cancellation directions.
  completion_candidate: no
  lean_artifacts: [supportSigmaEquiv, axisSigmaEquiv, observableSigmaEquiv, supportInverseAtForward, axisInverseAtForward, observableInverseAtForward, supportInverseAtForward_reads, axisInverseAtForward_reads, observableInverseAtForward_reads, support_forward_inverse, axis_forward_inverse, observable_forward_inverse, support_inverse_forward, axis_inverse_forward, observable_inverse_forward]
  source_sha256:
    UpperGeometryRealizationFactorCarriers.lean: b174a42144205e7bf2406e3a4a676f818bb3777bcc7df4e399ea5dc0b2296cbe
  evidence: [focused Lean file check, targeted direct-module dependency-DAG build, 15-declaration namespace standard-axiom audit, three dependent Sigma equivalences, six fiberwise cancellation theorems, three reading-reflection theorems]
audits:
  premise_delta:
    ambient_boundary: [ExactUpperEquivalence, theorem-generated RealizationExactUpperEquivalence]
    direction_hypothesis: []
    discharged: [dependent Support total-space equivalence, dependent Axis total-space equivalence, dependent Observable total-space equivalence, inverse-at-forward carrier maps, both component cancellation directions, inverse reading preservation]
    remaining: [inverse carrier restriction naturality, universal factor coverage overlap coefficient raw and carrier contract, factor composition law, factor uniqueness, direct route strong cartesianness, endpoint comparison isomorphisms, solution equivalence]
  certificate_provenance:
    total_spaces: constructed directly from homSupply and invSupply; left_inv and right_inv consume the authored context cancellation and each corresponding component inverse law
    fiber_maps: invSupply component transported only along ExactUpperEquivalence.forwardBackwardContext
    readings: invSupply reading preservation followed by dependent Sigma equality and forwardBackwardAtom
  proof_use:
    used: [all six RealizationExactUpperEquivalence component inverse laws, homSupply carrier maps, invSupply carrier maps and reading laws, both context cancellation directions, forwardBackwardAtom]
    deliberately_not_used: [HGeom adapter, lower inverse, G-114 endpoint core iso, selected-domain iso, caller geometry contract]
  structure_field_escape: none; no compatible input or route structure is changed, and this generic algebra is not counted as the finite route strong-Cartesian conclusion
  route_integrity: route-neutral algebra only; the next finite strong-Cartesian specializations remain fixed to the base and pulled theorem-generated inhabitants
  predecessor_integrity: G-108 G-112 G-114 Formal and the fixed GOAL are unchanged; one G-115 carrier-factor module and its registrations are added
  target_fitting: none-found; the equivalences quantify over every ExactUpperEquivalence and use its complete authored cancellation laws
  vacuity: each Equiv has concrete toFun invFun and both inverse proofs; each fiber map has two concrete cancellation theorems and a reading theorem
  one_way_as_equivalence: none-found; both Sigma inverse laws and both fiberwise cancellation directions are proved
  goal_or_report_reinterpretation: none-found; strong cartesianness remains explicitly unchecked
  validation_refs: [`./check_research_modules.sh --focused ResearchLean/AG/DoctrineFiberProduct/UpperGeometryRealizationFactorCarriers.lean` passed and reported 15 declarations under AAT.AG.DoctrineFiberProduct standard axioms only; targeted `lake build ResearchLean.AG.DoctrineFiberProduct.UpperGeometryRealizationFactorCarriers` passed with 4104 jobs; Research aggregate and full build were not run]
  blocking_findings: []
  next_obligation: Prove restriction naturality of the three inverse-at-forward maps, use these carriers in the complete universal factor geometry contract, and close factorization uniqueness for both finite direct route homs.
```

## Cycle 54 — naturality of realization-factor carrier inverses

```yaml
ledger_type: target_cycle_result
goal: G-115-aat-upper-stage-lift
cycle: 54
goal_blob_sha: 65a084cfe6eb6094d2dc33193e0b9185393043f44387e12151c17b355911044c
base_oid: 41319c669629738d9095cca006d88eb077a6368b
tracking_issue: 4250
report_path: research/reports/G-115-aat-upper-stage-lift.md
selection:
  proof_state_ref: Cycle 53 produced literal-source-fiber inverses and both cancellation directions, but the universal factor still needs those inverses to commute with all context restrictions
  proof_obligation: Prove injectivity of the forward realization component maps and restriction naturality of inverse-at-forward for Support Axis and contravariant Observable
  selection_reason: These are the last carrier-level laws required to populate the complete RefinementGeomReadHom factor without accepting a backward naturality certificate from the caller.
  expected_result_type: proof-obligation-discharged
  lean_targets: [ResearchLean/AG/DoctrineFiberProduct/UpperGeometryRealizationFactorNaturality.lean]
  risks: [assuming inverse naturality from bijectivity without proof, reversing Observable variance, erasing dependent context casts, introducing a new naturality premise, using only one cancellation direction]
  unchecked: [complete universal factor geometry contract, factorization and uniqueness, direct route strong cartesianness, endpoint comparison isomorphisms, solution equivalence]
result:
  proposed_result_type: proof-obligation-discharged
  proof_state: target-proof-checkpoint
  proof_obligation_delta: Forward Support Axis and Observable realization maps are now injective by the Cycle 53 inverse laws. Applying that injectivity reduces each inverse-at-forward naturality square to the existing forward naturality square and forward-after-inverse cancellation, including the contravariant Observable direction.
  completion_candidate: no
  lean_artifacts: [supportComp_injective, axisComp_injective, observableComp_injective, supportInverseAtForward_naturality, axisInverseAtForward_naturality, observableInverseAtForward_naturality]
  source_sha256:
    UpperGeometryRealizationFactorNaturality.lean: d46c766f5e26c5fc496bfade40d95afbc3fae73382d0cdca04b07cbc6f153662
  evidence: [focused Lean file check, targeted dependency-DAG module build, 6-declaration namespace standard-axiom audit, explicit forward-map injectivity, covariant Support and Axis naturality, contravariant Observable naturality]
audits:
  premise_delta:
    ambient_boundary: [ExactUpperEquivalence, theorem-generated RealizationExactUpperEquivalence]
    direction_hypothesis: []
    discharged: [forward Support component injectivity, forward Axis component injectivity, forward Observable component injectivity, inverse Support restriction naturality, inverse Axis restriction naturality, inverse Observable restriction naturality]
    remaining: [universal factor coverage overlap coefficient raw and carrier contract, factor composition law, factor uniqueness, direct route strong cartesianness, endpoint comparison isomorphisms, solution equivalence]
  certificate_provenance:
    injectivity: each proof applies the corresponding Cycle 53 inverse-after-forward cancellation law to an equality of forward component values
    naturality: each proof applies forward component injectivity, rewrites by the existing homSupply naturality field, and cancels both forward-after-inverse occurrences
    observable_variance: the theorem starts at the target context V and restricts to W, exactly matching UpperRealizationTransportSupply.observable_naturality
  proof_use:
    used: [all three homSupply component naturality laws, all three inverse-after-forward laws, all three forward-after-inverse laws, exact upper context functor maps]
    deliberately_not_used: [caller-supplied inverse naturality, compatible-input geometry contract, lower inverse, G-114 endpoint core iso]
  structure_field_escape: none; no new premise or input field is introduced, and inverse naturality is derived from the existing realization-exact laws
  route_integrity: route-neutral algebra only; finite base and pulled strong-Cartesian specializations remain tied to their independently generated route realization inhabitants
  predecessor_integrity: G-108 G-112 G-114 Formal and the fixed GOAL are unchanged; one G-115 naturality module and its registrations are added
  target_fitting: none-found; each result is stated over the literal dependent context fibers produced by the exact upper equivalence
  vacuity: all six declarations are pointwise equations or injectivity results for arbitrary carrier values and arbitrary context morphisms
  one_way_as_equivalence: none-found; the proofs materially use both Cycle 53 cancellation directions
  goal_or_report_reinterpretation: none-found; strong cartesianness and endpoint isomorphisms remain explicitly unchecked
  validation_refs: [`./check_research_modules.sh --focused ResearchLean/AG/DoctrineFiberProduct/UpperGeometryRealizationFactorNaturality.lean` passed and reported 6 declarations under AAT.AG.DoctrineFiberProduct standard axioms only; targeted `lake build ResearchLean.AG.DoctrineFiberProduct.UpperGeometryRealizationFactorNaturality` passed with 4105 jobs; Research aggregate and full build were not run]
  blocking_findings: []
  next_obligation: Use the inverse-at-forward maps, inverse reading laws, and these naturality theorems to construct the complete universal factor RefinementGeomReadHom, then prove factorization and uniqueness.
```

## Cycle 55 — complete realization-exact universal factor contract

```yaml
ledger_type: target_cycle_result
goal: G-115-aat-upper-stage-lift
cycle: 55
goal_blob_sha: 65a084cfe6eb6094d2dc33193e0b9185393043f44387e12151c17b355911044c
base_oid: d06f200d6b03d691b7e27558d8e2907bfb21c1b5
tracking_issue: 4250
report_path: research/reports/G-115-aat-upper-stage-lift.md
selection:
  proof_state_ref: Cycles 53 and 54 supplied dependent inverse carriers, reflected readings, both cancellations, and restriction naturality
  proof_obligation: Construct the complete RefinementGeomReadHom universal factor through an arbitrary realization-exact upper-pair normalization, and specialize it without premises to both finite routes
  selection_reason: Strong cartesianness requires an actual factor carrying coverage overlap coefficient raw Support Axis Observable reading and naturality data, not only component inverses.
  expected_result_type: proof-obligation-discharged
  lean_targets: [ResearchLean/AG/DoctrineFiberProduct/UpperGeometryRealizationUniversalFactor.lean]
  risks: [accepting backward-after-forward context equality as a new certificate, retaining only carrier maps, losing Observable variance, using a package-only factor, omitting finite route inhabitation, conflating the factor contract with factorization or uniqueness]
  unchecked: [total universal factor, factor composition law, recovery of a factor from its composite, factor uniqueness, direct route strong cartesianness, endpoint comparison isomorphisms, solution equivalence]
result:
  proposed_result_type: proof-obligation-discharged
  proof_state: target-proof-checkpoint
  proof_obligation_delta: A generic factor now reconstructs every RefinementGeomReadHom field through an upper-pair normalization. Coverage and coefficient data are inherited, overlap is pulled back along the actual lax base, raw transport cancels the authored upper inverse, and all three carriers use the realization-exact inverse maps with reflected readings and restriction naturality. The missing backward-after-forward raw context equality is derived from the supplied forward-after-backward equality and authored exact upper cancellation. Premise-free base and pulled finite specializations consume only previously generated route evidence.
  completion_candidate: no
  lean_artifacts: [refinementExactUpperEquivalence, upperPairPullCartesianFactorGeomCore, canonicalAuthoredBaseRouteCartesianFactorGeomCoreAt, canonicalAuthoredPulledRouteCartesianFactorGeomCoreAt]
  source_sha256:
    UpperGeometryRealizationUniversalFactor.lean: c678c66f81cd5ffb0399d8daa38a0ac8190321639e46f3142fbc4db6b61deea6
  evidence: [focused Lean file check, targeted dependency-DAG module build, 6-declaration namespace standard-axiom audit including private context lemmas, complete RefinementGeomReadHom construction, premise-free finite base and pulled specializations]
audits:
  premise_delta:
    ambient_boundary: [actual lax refinement base, authored exact upper inverse and both cancellation laws, theorem-generated RealizationExactUpperEquivalence, forward-after-backward raw context cancellation]
    direction_hypothesis: []
    discharged: [backward-after-forward raw context cancellation derived internally, universal factor coverage, universal factor overlap, coefficient transport, raw transport, inverse Support Axis Observable maps, reflected readings, all restriction naturality fields, finite base factor contract, finite pulled factor contract]
    remaining: [total factor, factor composition law, factor recovery and uniqueness, direct route strong cartesianness, endpoint comparison homs and inverse laws, comparison naturality and comparator compatibility, solution equivalence]
  certificate_provenance:
    upper_equivalence: refinementExactUpperEquivalence packages the literal lax base upper together with the reviewed authored backward map and both upper cancellation equations
    missing_context_direction: apply the authored backward context functor to forward-after-backward cancellation at a forward image, then cancel both backward-after-forward composites by ExactUpperEquivalence.forwardBackwardContext
    overlap: inverse-context image of the supplied composite overlap iso, with four endpoint equalities generated by the derived context cancellation
    finite: generated route upper equivalence, generated route realization exactness, and Cycle 51 context cancellation; no new input field
  proof_use:
    used: [all nine coverage fields, overlap mapIso, both exact upper cancellation laws, Cycle 51 forward-after-backward context law, rawReindexUpper_comp, coefficient hom, Cycle 53 inverse carrier and reading theorems, Cycle 54 inverse naturality, all composite contract fields]
    deliberately_not_used: [caller-supplied backward context law, caller-supplied factor, lower inverse, G-114 endpoint core iso, selected-domain iso]
  structure_field_escape: none; generic premises are all factor ambient data, while both finite target-facing constructors take only input i g and the arbitrary composite contract T
  route_integrity: finite base and pulled specializations use their literal generated route bases and independently generated realization equivalences in the two route orders
  predecessor_integrity: G-108 G-112 G-114 Formal and the fixed GOAL are unchanged; one G-115 universal-factor module and its registrations are added
  target_fitting: none-found; the factor is over the actual lax g and the normalized object formed from the literal f.upper and authored backward
  vacuity: the generic constructor populates every computational field of RefinementGeomReadHom and both finite routes instantiate it for arbitrary K g and composite T
  one_way_as_equivalence: none-found; both upper cancellation equations and both realization carrier cancellation directions are materially consumed across the factor construction
  goal_or_report_reinterpretation: none-found; factorization uniqueness strong cartesianness and endpoint isomorphisms remain explicitly unchecked
  validation_refs: [`./check_research_modules.sh --focused ResearchLean/AG/DoctrineFiberProduct/UpperGeometryRealizationUniversalFactor.lean` passed and reported 6 declarations under AAT.AG.DoctrineFiberProduct standard axioms only; targeted `lake build ResearchLean.AG.DoctrineFiberProduct.UpperGeometryRealizationUniversalFactor` passed with 4106 jobs; Research aggregate and full build were not run]
  blocking_findings: []
  next_obligation: Lift the componentwise contract to a total factor, prove its composition and recovery equations from the Cycle 53 cancellation laws, then prove uniqueness and both finite direct route strong-Cartesian theorems.
```

## Cycle 56 — realization-exact factorization and strong cartesianness

```yaml
ledger_type: target_cycle_result
goal: G-115-aat-upper-stage-lift
cycle: 56
goal_blob_sha: 65a084cfe6eb6094d2dc33193e0b9185393043f44387e12151c17b355911044c
base_oid: 9038ea5db85972e8a047685c477c0d0918edbc1f
tracking_issue: 4250
report_path: research/reports/G-115-aat-upper-stage-lift.md
selection:
  proof_state_ref: Cycle 55 constructed the complete componentwise factor contract and finite base/pulled specializations
  proof_obligation: Lift that contract to a total factor, prove factor composition and recovery, prove uniqueness, derive the generic strongly Cartesian universal property, and specialize it to both finite direct route legs
  selection_reason: Endpoint comparison isomorphisms require actual strongly Cartesian geometry legs with authored factorization and uniqueness, not only complete component fields.
  expected_result_type: proof-obligation-discharged
  lean_targets: [ResearchLean/AG/DoctrineFiberProduct/UpperGeometryRealizationStrongCartesian.lean]
  risks: [proving only existence without uniqueness, using one carrier cancellation direction, losing the actual lax lower map under casts, relying on typeclass inference without authored factor equations, claiming route strong cartesianness only generically without finite discharge]
  unchecked: [complete endpoint comparison isomorphisms, comparison naturality, comparator conjugation, solution equivalence, final endpoint IsIso correspondence]
result:
  proposed_result_type: proof-obligation-discharged
  proof_state: target-proof-checkpoint
  proof_obligation_delta: The Cycle 55 contract is now a total refinement-geometry factor. Composition with the direct normalization leg recovers the supplied hom by forward-after-inverse carrier cancellation; factoring a composite recovers the original factor contract by inverse-after-forward cancellation. Extensionality and base-cast coherence prove uniqueness, yielding the generic IsStronglyCartesian theorem and premise-free finite base and pulled route specializations.
  completion_candidate: no
  lean_artifacts: [upperPairPullCartesianFactor, upperPairPullCartesianFactor_fac, upperPairPullCartesianFactorGeomCore_of_composite, upperPairPullCartesianFactor_unique, upperPairPullRefinementGeometryHom_isStronglyCartesian, canonicalAuthoredBaseRouteGeometryHomAt_isStronglyCartesian, canonicalAuthoredPulledRouteGeometryHomAt_isStronglyCartesian]
  source_sha256:
    UpperGeometryRealizationStrongCartesian.lean: 8f8830a2ee8f0fe66cb2b1d705177b50d7fb9936caa2adfd5dbacb410f840e9c
  evidence: [focused Lean file check, targeted dependency-DAG module build, 7-declaration namespace standard-axiom audit, authored factor composition, authored factor recovery, total uniqueness, generic strong cartesianness, finite base and pulled strong-cartesian specializations]
audits:
  premise_delta:
    ambient_boundary: [Cycle 55 universal factor data, arbitrary lower factor base g, arbitrary compatible total hom h, standard IsHomLift interface]
    direction_hypothesis: []
    discharged: [total factor construction, factor composition equation, factor contract recovery, total factor uniqueness, generic realization-exact strong cartesianness, finite base direct-route strong cartesianness, finite pulled direct-route strong cartesianness]
    remaining: [endpoint comparison homs and inverse laws, comparison edge naturality, comparator conjugation, solution equivalence, actual endpoint IsIso iff]
  certificate_provenance:
    factorization: Cycle 55 factor carrier maps followed by the direct homSupply maps, cancelled with Cycle 53 forward-after-inverse laws
    recovery: arbitrary factor carrier maps followed by the direct homSupply and then Cycle 55 inverse maps, cancelled with Cycle 53 inverse-after-forward laws
    uniqueness: equality of lower bases plus equality of composites, normalized through explicit base casts and RefinementGeomReadHom extensionality
    strong_cartesian: CategoryTheory.Functor.IsStronglyCartesian.mk receives the authored total factor, IsHomLift witness, factorization equation, and uniqueness theorem
    finite: literal generated route bases, generated route realization exactness, and Cycle 51 context cancellation; no IsStronglyCartesian input
  proof_use:
    used: [all three forward-after-inverse realization laws, all three inverse-after-forward realization laws, Cycle 55 complete factor contract, direct route complete geometry hom, RefinementGeometryHom extensionality, IsHomLift base equality, IsStronglyCartesian.mk]
    deliberately_not_used: [caller-supplied factor uniqueness, caller-supplied cartesianness, lower inverse, G-114 endpoint core iso, selected-domain iso]
  structure_field_escape: none; strong cartesianness is a theorem output, and the finite compatible input remains unchanged
  route_integrity: base and pulled finite theorems close independently over their literal actual route bases and route-specific realization producers
  predecessor_integrity: G-108 G-112 G-114 Formal and the fixed GOAL are unchanged; one G-115 strong-cartesian module and its registrations are added
  target_fitting: none-found; factor lower maps are equal to the arbitrary requested g and the direct legs are the literal canonical-authored route geometry homs
  vacuity: the theorem satisfies existence factorization and uniqueness clauses of IsStronglyCartesian for every K g h and IsHomLift witness
  one_way_as_equivalence: none-found; factorization and recovery consume opposite realization cancellation families
  goal_or_report_reinterpretation: none-found; endpoint isomorphisms and solution equivalence remain explicitly unchecked
  validation_refs: [`./check_research_modules.sh --focused ResearchLean/AG/DoctrineFiberProduct/UpperGeometryRealizationStrongCartesian.lean` passed and reported 7 declarations under AAT.AG.DoctrineFiberProduct standard axioms only; targeted `lake build ResearchLean.AG.DoctrineFiberProduct.UpperGeometryRealizationStrongCartesian` passed with 4107 jobs; Research aggregate and full build were not run]
  blocking_findings: []
  next_obligation: Combine the reviewed direct strong-Cartesian legs with the existing generated route legs and endpoint core equivalences to construct complete base and pulled endpoint comparison isomorphisms, then prove their naturality and comparator conjugation.
```

## Cycle 57 — complete canonical-authored/generated endpoint geometry isomorphisms

```yaml
ledger_type: target_cycle_result
goal: G-115-aat-upper-stage-lift
cycle: 57
goal_blob_sha: 65a084cfe6eb6094d2dc33193e0b9185393043f44387e12151c17b355911044c
base_oid: 6a7e2c254e00763a154e335becb41f5ace84613d
tracking_issue: 4250
report_path: research/reports/G-115-aat-upper-stage-lift.md
selection:
  proof_state_ref: Cycle 56 proved that the canonical-authored and generated legs are independently strongly Cartesian over the same literal base and pulled route maps
  proof_obligation: Construct complete base and pulled geometry isomorphisms between the canonical-authored normalizations and generated route endpoints, together with both factorization triangles
  selection_reason: The later presentation naturality and solution conjugation must use actual complete geometry isomorphisms, not the raw G-114 one-way selected-endpoint comparison or a core-only equivalence.
  expected_result_type: proof-obligation-discharged
  lean_targets: [ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCompatibleEndpointGeometryIsos.lean]
  risks: [reusing the raw selected endpoint comparison, proving only core equivalence, importing an endpoint comparison as input, omitting one inverse triangle, attaching a lower inverse to the backward upper map]
  unchecked: [comparison edge naturality, leg and edge conjugation, authored-comparator conjugation, solution equivalence, final endpoint IsIso correspondence]
result:
  proposed_result_type: proof-obligation-discharged
  proof_state: target-proof-checkpoint
  proof_obligation_delta: Strong-Cartesian uniqueness now compares the independently generated canonical-authored and generated route lifts over the literal identical base map. It yields complete RefinementGeometryCategory isomorphisms at every base and pulled vertex. The hom and inverse factorization triangles identify both directions with their authored route legs.
  completion_candidate: no
  lean_artifacts: [canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt, canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt_hom_fac, canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt_inv_fac, canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt, canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt_hom_fac, canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt_inv_fac]
  source_sha256:
    UpperGeometryCompatibleEndpointGeometryIsos.lean: 317fa8dec7127a7145957d65aeb527a9b8bb6f5a3e898f8d119db64d9f446623
  evidence: [focused Lean file check, targeted dependency-DAG module build, 6-declaration namespace standard-axiom audit, complete category isomorphisms, hom and inverse factorization triangles for both finite routes]
audits:
  premise_delta:
    ambient_boundary: [Cycle 56 theorem-generated strong cartesianness of both independently constructed endpoint legs, literal generated route lower maps]
    direction_hypothesis: []
    discharged: [base endpoint complete geometry isomorphism, base hom factorization, base inverse factorization, pulled endpoint complete geometry isomorphism, pulled hom factorization, pulled inverse factorization]
    remaining: [named hom and inv core projection laws, named hom-inv and inv-hom laws, coefficient identity, Support Axis and Observable inverse laws, endpoint comparison presentation naturality, leg and edge conjugation, literal authored-comparator conjugation, canonical-authored/generated solution equivalence, named decision and negative problems, paired cochain and restricted reselection transport, UpperStageExchangeExact companion iff]
  certificate_provenance:
    isomorphisms: IsStronglyCartesian.domainIsoOfBaseIso applied to the Cycle 56 canonical-authored lift and the pre-existing generated lift over the identity package iso
    triangles: IsStronglyCartesian.fac gives the hom factorization; the inverse factorization follows from it and the category iso hom-inv law
  proof_use:
    used: [both independently generated route legs, both Cycle 56 canonical-authored strong-cartesian theorems, both pre-existing generated strong-cartesian theorems, literal base-map equality, strong-Cartesian uniqueness, category iso cancellation]
    deliberately_not_used: [G-114 selected endpoint comparison, G-114 endpoint core iso as the comparison, caller-supplied endpoint iso, caller-supplied HGeom, lower inverse, solution wrapper]
  structure_field_escape: none; each isomorphism is theorem-generated from the compatible input and vertex only
  route_integrity: base and pulled isomorphisms are constructed separately from their corresponding route-specific legs and literal route bases
  predecessor_integrity: G-108 G-112 G-114 Formal and the fixed GOAL are unchanged; one G-115 endpoint-isomorphism module and its registrations are added
  target_fitting: none-found; the comparison is a complete RefinementGeometryCategory iso and its triangles use the actual authored and generated geometry legs
  vacuity: both finite routes provide an isomorphism at every presentation vertex, and both morphism directions satisfy explicit factorization equations
  one_way_as_equivalence: none-found; the raw G-114 one-way selected-endpoint comparison is not referenced or used by any Cycle 57 declaration
  goal_or_report_reinterpretation: none-found; presentation naturality, comparator conjugation, and solution equivalence remain explicitly unchecked
  validation_refs: [`./check_research_modules.sh --focused ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCompatibleEndpointGeometryIsos.lean` passed and reported 6 declarations under AAT.AG.DoctrineFiberProduct standard axioms only; targeted `lake build ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleEndpointGeometryIsos` passed with 4108 jobs; Research aggregate and full build were not run]
  blocking_findings: []
  next_obligation: Expose the hom and inv core projections, category inverse laws, coefficient identity, and Support Axis Observable inverse laws as named theorems; then prove presentation-edge naturality for both endpoint comparison isomorphisms and use it for leg edge and literal authored-comparator conjugation before constructing the solution-space equivalence.
```

## Cycle 58 — named complete endpoint component laws

```yaml
ledger_type: target_cycle_result
goal: G-115-aat-upper-stage-lift
cycle: 58
goal_blob_sha: 65a084cfe6eb6094d2dc33193e0b9185393043f44387e12151c17b355911044c
base_oid: d04880a6b2039967f99e9844256ddd6ac27f30bc
tracking_issue: 4250
report_path: research/reports/G-115-aat-upper-stage-lift.md
selection:
  proof_state_ref: Cycle 57 constructed complete base and pulled endpoint geometry isomorphisms and both factorization triangles
  proof_obligation: Expose each route iso's hom and inverse core projections, category inverse laws, coefficient identities, and dependent Support Axis Observable cancellation laws as named theorems
  selection_reason: The fixed GOAL requires these component laws separately, and later solution and reselection transport must cite their exact proof-use rather than only the opaque Iso record.
  expected_result_type: proof-obligation-discharged
  lean_targets: [ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCompatibleEndpointGeometryLaws.lean]
  risks: [core-only laws, one cancellation direction only, proof-irrelevance in place of carrier computation, loss of Observable dependency, route aliasing, coefficient identity without factor provenance]
  unchecked: [presentation edge naturality, leg and edge conjugation, literal authored-comparator conjugation, solution equivalence, named decision and negative problems, paired cochain and restricted reselection transport, UpperStageExchangeExact companion iff]
result:
  proposed_result_type: proof-obligation-discharged
  proof_state: target-proof-checkpoint
  proof_obligation_delta: Both endpoint isomorphisms now expose identity lower projections for hom and inverse, named category hom-inverse and inverse-hom equations, coefficient identities derived through the route factor triangles, and pointwise dependent HEq cancellation in both directions for Support Axis and Observable. Base and pulled routes have separate public theorem families.
  completion_candidate: no
  lean_artifacts: [base and pulled hom_base, base and pulled inv_base, base and pulled hom_inv, base and pulled inv_hom, base and pulled hom_coefficient_id, base and pulled inv_coefficient_id, base and pulled Support hom_inv and inv_hom, base and pulled Axis hom_inv and inv_hom, base and pulled Observable hom_inv and inv_hom]
  source_sha256:
    UpperGeometryCompatibleEndpointGeometryLaws.lean: f6c8666fa05690d8846f171e8850803ea0de858cb25f88afd51c0e21491fdc3d
  evidence: [focused Lean file check, targeted dependency-DAG module build, 24-declaration namespace standard-axiom audit, identity core projections from IsHomLift, coefficient identities from factor triangles, six dependent carrier cancellations per route]
audits:
  premise_delta:
    ambient_boundary: [Cycle 57 theorem-generated complete endpoint isomorphisms, route factor triangles, generated and canonical-authored coefficient identity laws]
    direction_hypothesis: []
    discharged: [four core projection laws, four named category inverse laws, four coefficient identity laws, twelve dependent Support Axis Observable inverse laws]
    remaining: [endpoint presentation naturality, leg and edge conjugation, literal authored-comparator conjugation, canonical-authored/generated solution equivalence, named decision and negative problems, paired cochain and restricted reselection transport, UpperStageExchangeExact companion iff]
  certificate_provenance:
    core: domainIsoOfBaseIso IsHomLift instances over the typed identity core iso
    category_inverse: the actual Cycle 57 category Iso hom_inv_id and inv_hom_id
    coefficient: congruence of the Cycle 57 hom and inverse route factor triangles followed by generated and canonical-authored coefficient identities
    carriers: explicit Support Axis Observable evaluation of category hom-inverse and inverse-hom; HEq retains the dependent context transports
  proof_use:
    used: [both Cycle 57 endpoint isomorphisms, all four route factor triangles, both category inverse directions, both route-specific generated and canonical-authored coefficient laws, all three carrier maps in both comparison directions]
    deliberately_not_used: [raw G-114 selected-endpoint comparison, lower inverse, caller-supplied endpoint law, proof-irrelevance as a carrier inverse, solution wrapper]
  structure_field_escape: none; every theorem is generated from compatible input and a vertex, with carrier values quantified pointwise
  route_integrity: base and pulled laws cite their own route iso, leg, core, coefficient, context, and carrier data
  predecessor_integrity: G-108 G-112 G-114 Formal and the fixed GOAL are unchanged; one G-115 law module and registrations are added
  target_fitting: none-found; named results expose the complete comparison morphisms and their dependent geometry maps, not only core equivalences
  vacuity: carrier laws quantify over arbitrary endpoint contexts and arbitrary Support Axis Observable elements in both directions
  one_way_as_equivalence: none-found; every carrier family contains both hom-inverse and inverse-hom cancellation
  goal_or_report_reinterpretation: none-found; naturality comparator and solution obligations remain explicit
  validation_refs: [`./check_research_modules.sh --focused ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCompatibleEndpointGeometryLaws.lean` passed and reported 24 declarations under AAT.AG.DoctrineFiberProduct standard axioms only; targeted `lake build ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleEndpointGeometryLaws` passed with 4109 jobs; Research aggregate and full build were not run]
  blocking_findings: []
  next_obligation: Construct the canonical-authored base and pulled presentation edges independently through their strongly Cartesian legs, then prove both endpoint comparison naturality squares by strong-Cartesian uniqueness.
```

## Cycle 59 — independently generated endpoint presentation naturality

```yaml
ledger_type: target_cycle_result
goal: G-115-aat-upper-stage-lift
cycle: 59
goal_blob_sha: 65a084cfe6eb6094d2dc33193e0b9185393043f44387e12151c17b355911044c
base_oid: e29a55f65199ca7fae9db3814d2ca951b29a57ec
tracking_issue: 4250
report_path: research/reports/G-115-aat-upper-stage-lift.md
selection:
  proof_state_ref: Cycle 58 exposed the complete endpoint isomorphism component and inverse laws; Issue #4250 names presentation naturality as the next obligation
  proof_dag_predecessors: [canonicalAuthoredBaseRouteGeometryHomAt_isStronglyCartesian, canonicalAuthoredPulledRouteGeometryHomAt_isStronglyCartesian, generatedBaseRouteCoreEdge_fac, generatedPulledRouteCoreEdge_fac, generatedBaseRouteGeometryEdge_fac, generatedPulledRouteGeometryEdge_fac, both Cycle 57 endpoint geometry isomorphisms and hom factor triangles]
  proof_obligation: Construct the canonical-authored base and pulled presentation edges independently through the two direct strongly Cartesian route legs, then prove both endpoint comparison naturality squares by strong-Cartesian uniqueness
  selection_reason: The fixed target needs presentation-compatible endpoint comparison isomorphisms before the literal authored comparator can be conjugated and the generated/authored solution spaces can be related. Defining these edges by endpoint conjugation would store the desired coherence and fail route integrity.
  expected_result_type: proof-obligation-discharged
  lean_targets: [ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCompatibleEndpointNaturality.lean]
  risks: [defining authored edges by endpoint conjugation, accepting a naturality equation, proving only core naturality, losing complete reading fields during exactification, using one route for both orders, omitting the literal source-edge factor graphs]
  unchecked: [leg and literal authored-comparator conjugation, canonical-authored/generated solution equivalence, named decision and negative problems, paired cochain and restricted reselection transport, UpperStageExchangeExact companion iff]
result:
  proposed_result_type: proof-obligation-discharged
  proof_state: target-proof-checkpoint
  proof_obligation_delta: Each canonical-authored route now has its own exact core edge, complete refinement-geometry Cartesian pullback, exactified complete geometry edge, lower-map recovery, and literal source-edge factor theorem. The two Cycle 57 endpoint isomorphism families satisfy presentation-edge naturality because both sides have the same lower map and agree after composition with the corresponding generated strongly Cartesian route leg.
  completion_candidate: no
  lean_artifacts: [canonicalAuthoredBaseRouteCoreEdge, canonicalAuthoredBaseRouteRefinementGeometryEdge, canonicalAuthoredBaseRouteRefinementGeometryEdge_base, canonicalAuthoredBaseRouteGeometryEdge, canonicalAuthoredBaseRouteGeometryEdge_base, canonicalAuthoredBaseRouteGeometryEdge_toRefinement, canonicalAuthoredBaseRouteGeometryEdge_fac, canonicalAuthoredPulledRouteCoreEdge, canonicalAuthoredPulledRouteRefinementGeometryEdge, canonicalAuthoredPulledRouteRefinementGeometryEdge_base, canonicalAuthoredPulledRouteGeometryEdge, canonicalAuthoredPulledRouteGeometryEdge_base, canonicalAuthoredPulledRouteGeometryEdge_toRefinement, canonicalAuthoredPulledRouteGeometryEdge_fac, canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt_naturality, canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt_naturality]
  source_sha256:
    UpperGeometryCompatibleEndpointNaturality.lean: 2d97e0dd1013779247d9123d3b532e8bffb797590f16c834b74a08318a37bdfa
  evidence: [focused Lean file check, targeted direct-predecessor dependency construction, 16-declaration namespace standard-axiom audit, two independently generated complete edge families, two strong-Cartesian uniqueness naturality proofs]
audits:
  premise_delta:
    ambient_boundary: [certificate-free compatible input, literal authored source transport edge, theorem-generated direct and generated route strong cartesianness, Cycle 57 complete endpoint geometry isomorphisms]
    direction_hypothesis: []
    discharged: [independent base canonical-authored presentation edge, independent pulled canonical-authored presentation edge, both exact lower projections, both literal source-edge factor graphs, base endpoint comparison naturality, pulled endpoint comparison naturality]
    remaining: [leg and literal authored-comparator conjugation, solution-space equivalence, named decision and negative artifacts, paired cochain and restricted reselection transport, UpperStageExchangeExact companion iff]
  certificate_provenance:
    edges: both complete edges are Cartesian factors of the literal sourceTransport.edgeLift through the corresponding theorem-generated direct route leg, followed by faithful exactification
    naturality: both squares follow from the route factor triangles, independently generated source-edge factor graphs, and generated-leg strong-Cartesian uniqueness
    unresolved: [authored comparator conjugation, solution transports and inverse laws]
  proof_use:
    used: [both direct-route strong-Cartesian theorems, both generated core-edge factor laws, both generated complete geometry-edge factor laws, both endpoint hom factor triangles, exactGeometryHomOfRefinement_toRefinement, IsStronglyCartesian.map, IsStronglyCartesian.fac, IsStronglyCartesian.ext]
    deliberately_not_used: [endpoint isomorphism as the definition of either authored edge, caller-supplied route edge or route naturality certificate, raw G-114 selected-endpoint one-way comparison, lower inverse]
  structure_field_escape: the literal source edge and its G-109 qualifications are ambient input fields; direct and generated route cartesianness, canonical-authored route edges, endpoint isomorphisms, and endpoint naturality are theorem-generated and absent from the input structure
  route_integrity: base and pulled authored edges are constructed separately from their literal direct legs and the common source edge; naturality is proved only after construction
  predecessor_integrity: G-108 G-112 G-114 Formal and the fixed GOAL are unchanged; all new evidence is local to G-115
  target_fitting: none-found; the desired naturality is not used in either edge definition or accepted as a premise
  vacuity: every finite presentation edge is quantified, and both squares compare complete geometry maps carrying all reading fields
  one_way_as_equivalence: none-found; this cycle uses the already reviewed complete category isomorphisms and proves only their forward naturality squares
  goal_or_report_reinterpretation: none-found; comparator conjugation and solution equivalence remain explicit
  validation_refs: [`lake build ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleEndpointGeometryLaws ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleRouteGeometryEdges` constructed only the direct predecessor DAG and passed with 4109 jobs; `lake env lean ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCompatibleEndpointNaturality.lean` passed and reported 16 declarations under AAT.AG.DoctrineFiberProduct standard axioms only; Research aggregate and full build were not run]
  blocking_findings: []
  next_obligation: Use the two endpoint naturality squares and endpoint factor triangles to prove the leg-edge and literal authored-comparator conjugation equations, then construct the generated/authored solution-space equivalence.
```

## Cycle 60 — literal authored-comparator endpoint conjugation

```yaml
ledger_type: target_cycle_result
goal: G-115-aat-upper-stage-lift
cycle: 60
goal_blob_sha: 65a084cfe6eb6094d2dc33193e0b9185393043f44387e12151c17b355911044c
base_oid: 9a10a2ba31e9a8e967617050f61379b5fe1a2008
tracking_issue: 4250
report_path: research/reports/G-115-aat-upper-stage-lift.md
selection:
  proof_state_ref: Cycle 59 merged independently generated canonical-authored presentation edges and both complete endpoint naturality squares
  proof_dag_predecessors: [both canonical-authored direct route strong-Cartesian theorems, generated base and pulled comparator factor laws, both endpoint comparison hom factor triangles, both endpoint comparison category inverse laws]
  proof_obligation: Pull the literal source-authored comparator directly through each canonical-authored route leg and prove forward and backward conjugation by the complete endpoint comparison isomorphisms
  selection_reason: The solution-space transport must preserve the authored comparator equation in both directions. Defining a canonical-authored comparator by endpoint conjugation would encode that result and violate route integrity.
  expected_result_type: proof-obligation-discharged
  lean_targets: [ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCompatibleEndpointComparatorConjugation.lean]
  risks: [defining authored comparators by endpoint conjugation, accepting a comparator equation, using only core automorphisms, losing complete reading fields during exactification, aliasing base and pulled routes, proving only the forward transport]
  unchecked: [canonical-authored/generated solution equivalence, named decision and negative problems, paired cochain and restricted reselection transport, UpperStageExchangeExact companion iff]
result:
  proposed_result_type: proof-obligation-discharged
  proof_state: target-proof-checkpoint
  proof_obligation_delta: Each route now has an independently constructed complete canonical-authored comparator obtained by Cartesian pullback of the literal sourceTransport comparator through its direct strongly Cartesian leg. Exactification preserves the lower factor. Strong-Cartesian uniqueness and the endpoint factor triangles prove forward conjugation to the generated comparator; cancellation by the actual endpoint isomorphism proves the inverse equation returning to the literal canonical-authored comparator.
  completion_candidate: no
  lean_artifacts: [canonicalAuthoredBaseRouteComparatorCore, canonicalAuthoredBaseRouteComparatorRefinement, canonicalAuthoredBaseRouteComparatorRefinement_base, canonicalAuthoredBaseRouteComparator, canonicalAuthoredBaseRouteComparator_toRefinement, canonicalAuthoredBaseRouteComparator_fac, canonicalAuthoredBaseRouteComparator_conjugation, canonicalAuthoredBaseRouteComparator_conjugation_inv, canonicalAuthoredPulledRouteComparatorCore, canonicalAuthoredPulledRouteComparatorRefinement, canonicalAuthoredPulledRouteComparatorRefinement_base, canonicalAuthoredPulledRouteComparator, canonicalAuthoredPulledRouteComparator_toRefinement, canonicalAuthoredPulledRouteComparator_fac, canonicalAuthoredPulledRouteComparator_conjugation, canonicalAuthoredPulledRouteComparator_conjugation_inv]
  source_sha256:
    UpperGeometryCompatibleEndpointComparatorConjugation.lean: 8a3ca00ae1a54c1ab3ef2e8b5777f9319078eb65616f111e36a626401790e375
  evidence: [focused Lean file check, 16-declaration namespace standard-axiom audit, two direct comparator pullbacks from the single literal source comparator, two forward and two inverse endpoint conjugation equations]
audits:
  premise_delta:
    ambient_boundary: [certificate-free compatible input, literal sourceTransport comparator and its existing G-109 qualification, theorem-generated direct and generated route cartesianness, complete endpoint geometry isomorphisms]
    direction_hypothesis: []
    discharged: [direct canonical-authored base comparator, direct canonical-authored pulled comparator, both complete literal source-comparator factor laws, both forward endpoint conjugations, both inverse endpoint conjugations]
    remaining: [canonical-authored/generated solution equivalence, named decision and negative artifacts, paired cochain and restricted reselection transport, UpperStageExchangeExact companion iff]
  certificate_provenance:
    comparators: both are independently generated by IsStronglyCartesian.map from input.sourceTransport.comparator and then exactified; neither endpoint comparison appears in their definitions
    conjugation: route factor triangles and both literal source-comparator factor graphs identify the forward squares by strong-Cartesian uniqueness; category cancellation and hom-inverse laws derive the reverse squares
    unresolved: [solution transports and inverse laws]
  proof_use:
    used: [input.sourceTransport.comparator, both direct-route strong-Cartesian theorems, generated package comparator base factors, generated complete comparator factor laws, both endpoint hom factor triangles, endpoint category hom-inverse cancellation, exactGeometryHomOfRefinement_toRefinement, IsStronglyCartesian.map, IsStronglyCartesian.fac, IsStronglyCartesian.ext]
    deliberately_not_used: [endpoint isomorphism as the definition of either canonical-authored comparator, caller-supplied route comparator or conjugation certificate, raw G-114 selected-endpoint one-way comparison, lower inverse, solution wrapper]
  structure_field_escape: the only comparator input is the single literal sourceTransport comparator; both route comparators, their complete factors, endpoint isomorphisms, and conjugation equations are theorem-generated
  route_integrity: base and pulled comparators are constructed separately through their distinct direct route legs from the same literal source comparator; comparison is applied only after construction
  predecessor_integrity: G-108 G-112 G-114 Formal and the fixed GOAL are unchanged; all new evidence is local to G-115
  target_fitting: none-found; neither desired conjugation equation is used to define a comparator or accepted as a premise
  vacuity: every presented two-cell is quantified and each equation is a complete refinement-geometry equality retaining coefficient Support Axis and Observable data
  one_way_as_equivalence: none-found; both comparison directions are separately exposed and the reverse theorem uses the actual endpoint inverse
  goal_or_report_reinterpretation: none-found; solution-space equivalence remains explicit
  validation_refs: [`lake env lean ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCompatibleEndpointComparatorConjugation.lean` passed and reported 16 declarations under AAT.AG.DoctrineFiberProduct standard axioms only; only direct predecessor modules were targeted when missing; Research aggregate and full build were not run]
  blocking_findings: []
  next_obligation: Define the canonical-authored and generated compatible solution contracts, construct componentwise forward and backward transports through the endpoint isomorphisms, and prove preservation and inverse laws for component base, coefficient identity, triangle, edge naturality, and authored comparator equations.
```

## Cycle 61 — canonical-authored and generated solution contracts

```yaml
ledger_type: target_cycle_result
goal: G-115-aat-upper-stage-lift
cycle: 61
goal_blob_sha: 65a084cfe6eb6094d2dc33193e0b9185393043f44387e12151c17b355911044c
base_oid: 7b21ded43ddadf0321127d96058e4758a072e6b3
tracking_issue: 4250
report_path: research/reports/G-115-aat-upper-stage-lift.md
selection:
  proof_state_ref: Cycle 60 merged both independently generated literal authored-comparator conjugation directions
  proof_dag_predecessors: [generated compatible upper mate triangle edge naturality and global comparator equation, both endpoint comparison isomorphisms and component laws, both endpoint edge naturality squares, both literal authored-comparator conjugation directions, both direct canonical-authored route legs edges and comparators]
  proof_obligation: Define separate canonical-authored and theorem-generated compatible solution contracts with explicit nil append and two-cell equations, and construct a caller-free actual solution of each contract
  selection_reason: The fixed target requires typed solution spaces before arbitrary solutions can be transported. Building both canonical inhabitants now also proves the endpoint comparison and literal comparator APIs compose coherently on the intended G-115 mate.
  expected_result_type: proof-obligation-discharged
  lean_targets: [ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCompatibleSolutionContracts.lean]
  risks: [aliasing the old G-114 selected-route solution, storing only core components, treating nil append or two-cell equations as omitted corollaries, caller-supplied solution, defining authored comparators by conjugation, wrapper-based inverse preparation, coefficient carrier equality without identity hom]
  unchecked: [forward transport of arbitrary canonical-authored solutions, backward transport of arbitrary generated solutions, fieldwise preservation by both transports, both solution-space inverse laws, named solution Equiv, named decision and negative artifacts, paired cochain and restricted reselection transport, UpperStageExchangeExact companion iff]
result:
  proposed_result_type: proof-obligation-discharged
  proof_state: target-proof-checkpoint
  proof_obligation_delta: Separate CanonicalUpperRefinementBCSolution and GeometryCompatibleUpperRefinementBCSolution structures now require complete vertical components, the fixed G-115 core mate, coefficient identity, the appropriate route triangle, edge naturality, comparator intertwining, and explicit nil append and authored two-cell pasting equations. The generated contract is inhabited directly by the theorem-generated upper mate. The canonical-authored mate is exactified from base-hom followed by the generated mate followed by pulled-inverse endpoint conjugation; its triangle, coefficient identity, edge naturality, and literal comparator equation are proved from the actual endpoint laws, and it inhabits the canonical contract without caller data.
  completion_candidate: no
  lean_artifacts: [canonicalAuthoredBaseRoutePathLift, canonicalAuthoredPulledRoutePathLift, CanonicalUpperRefinementBCSolution, GeometryCompatibleUpperRefinementBCSolution, generatedCompatibleUpperGeometryMateAt_coefficient_id, generatedCompatibleUpperGeometryMateAt_path_naturality, generatedCompatibleUpperGeometryMateAt_append_naturality, generatedCompatibleUpperGeometryMateAt_authored_twoCell_pasting, generatedGeometryCompatibleUpperRefinementBCSolution, canonicalAuthoredUpperGeometryMateCoreAt, canonicalAuthoredUpperGeometryMateRefinementAt, canonicalAuthoredUpperGeometryMateRefinementAt_base, canonicalAuthoredUpperGeometryMateAt, canonicalAuthoredUpperGeometryMateAt_toRefinement, canonicalAuthoredUpperGeometryMateAt_base, canonicalAuthoredUpperGeometryMateAt_triangle, canonicalAuthoredUpperGeometryMateAt_coefficient_id, canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt_naturality_inv, canonicalAuthoredUpperGeometryMateAt_edge_naturality, canonicalAuthoredUpperGeometryMateAt_comparator_intertwining, canonicalAuthoredUpperGeometryMateAt_path_naturality, canonicalAuthoredUpperGeometryMateAt_append_naturality, canonicalAuthoredUpperGeometryMateAt_authored_twoCell_pasting, canonicalUpperRefinementBCSolution]
  source_sha256:
    UpperGeometryCompatibleSolutionContracts.lean: 60dbd87b77fcece1cc4c9b27367996668d540cce2dcc8b32b0b9c943e5ef8b56
  evidence: [focused Lean file check, 64-declaration namespace standard-axiom audit, two distinct solution structures, two caller-free actual solutions, direct coefficient-identity derivations from route triangles, endpoint-conjugated complete canonical component, explicit edge and literal comparator proof-use chains]
audits:
  premise_delta:
    ambient_boundary: [certificate-free compatible input, theorem-generated route geometry and mate, Cycle 57 endpoint isomorphisms, Cycle 59 endpoint naturality, Cycle 60 direct literal authored comparators and conjugation]
    direction_hypothesis: []
    discharged: [two typed G-115 solution contracts, explicit nil append and two-cell equations in each contract, generated actual solution, canonical-authored actual solution, both actual component lower projections, both coefficient identities, both triangles, both edge equations, both comparator equations]
    remaining: [arbitrary-solution forward and backward transports, preservation of every solution field in both directions, both solution-space inverse laws, final solution Equiv, named decision and negative artifacts, paired cochain and restricted reselection transport, UpperStageExchangeExact companion iff]
  certificate_provenance:
    generated_solution: constructed solely from generatedCompatibleUpperGeometryMateAt and its independently proved triangle edge and global comparator theorems
    canonical_component: exactGeometryHomOfRefinement applied to endpoint base hom, generated mate, and endpoint pulled inverse; its exact lower map is the same generatedRouteCoreMate
    canonical_equations: endpoint edge naturality and literal comparator conjugation are composed with the generated mate equations and pulled inverse equations; no equation is accepted from a caller
  proof_use:
    used: [both route-leg coefficient identities, generated mate triangle, generated edge naturality, generated global comparator equation, both endpoint hom and inverse factor laws, both endpoint edge naturality squares, both Cycle 60 literal comparator conjugation directions, exactGeometryHomOfRefinement_toRefinement, category associativity and endpoint inverse cancellation]
    deliberately_not_used: [old UpperRefinementBCSolution as either new contract, G-114 selected endpoint comparison, endpoint isomorphism as the definition of canonical-authored edges or comparators, caller-supplied solution or solution equation, lower inverse, sigma or wrapper storage]
  structure_field_escape: compatible input remains source-only; neither new solution, endpoint map, route equation, nor comparator equation is added to an input structure
  route_integrity: generated and canonical-authored contracts mention their own independently generated route legs edges path evaluations and comparators; the canonical component uses endpoint conjugation only after those objects exist independently
  predecessor_integrity: G-108 G-112 G-114 Formal and the fixed GOAL are unchanged; one G-115 solution-contract module and registrations are added
  target_fitting: none-found; the actual solutions are theorem-generated, and their component and equation proofs consume the preceding route constructions
  vacuity: both structures quantify every presentation vertex edge path pair and two-cell; both named inhabitants have complete GeometryTotalHom components and literal coefficient identity proofs
  one_way_as_equivalence: none-found; no solution-space equivalence is claimed in this cycle, and both arbitrary-solution transports remain explicit obligations
  goal_or_report_reinterpretation: none-found; this remains target-proof-checkpoint and the final Equiv plus downstream artifacts are unchecked
  validation_refs: [`./check_research_modules.sh --focused ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCompatibleSolutionContracts.lean` passed and reported 64 declarations under AAT.AG.DoctrineFiberProduct standard axioms only; only the direct Cycle 60 comparator-conjugation dependency DAG was targeted when its olean was absent; Research aggregate and full build were not run]
  blocking_findings: []
  next_obligation: Construct componentwise forward and backward transports for arbitrary solutions through the endpoint isomorphisms, prove separate preservation of component base coefficient identity triangle edge naturality comparator nil append and two-cell fields, prove both pointwise component cancellation laws and structure-level inverse laws, and package the two solution types as an Equiv without wrapper storage.
```

## Cycle 62 — wrapper-free compatible solution equivalence

```yaml
ledger_type: target_cycle_result
goal: G-115-aat-upper-stage-lift
cycle: 62
goal_blob_sha: 65a084cfe6eb6094d2dc33193e0b9185393043f44387e12151c17b355911044c
base_oid: 60564b90951bdeb99550da359e33b5e0762de09e
tracking_issue: 4250
report_path: research/reports/G-115-aat-upper-stage-lift.md
selection:
  proof_state_ref: Cycle 61 merged separate canonical-authored and generated solution contracts plus caller-free actual inhabitants
  proof_dag_predecessors: [both Cycle 61 solution structures, both endpoint comparison isomorphisms and inverse laws, both endpoint edge naturality directions, all four literal comparator conjugation directions, both route factor triangles]
  proof_obligation: Construct componentwise forward and backward transports for arbitrary solutions through the endpoint isomorphisms, prove every solution field and both inverse laws, and package a wrapper-free Equiv of the two solution types
  selection_reason: The fixed target explicitly rejects a stored-source wrapper and requires the endpoint comparison isomorphisms to act on the full solution equations. This is the remaining K2b2b-i equivalence obligation before decision fixtures and paired cochains.
  expected_result_type: proof-obligation-discharged
  lean_targets: [ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCompatibleSolutionEquivalence.lean]
  risks: [source-solution storage, sigma wrapper, proof-irrelevance-only inverse, wrong conjugation direction, core-only component equality, omitted coefficient or comparator preservation, one-sided inverse, named companion not constructed from the Equiv]
  unchecked: [named canonical companion problem, named upperDecisionContext problem and solution, genuinely lax nonidentity firing fixture, comparator-incoherent negative problem and no-solution theorem, paired cochain and restricted reselection bidirectional transport, UpperStageExchangeExact companion iff]
result:
  proposed_result_type: proof-obligation-discharged
  proof_state: target-proof-checkpoint
  proof_obligation_delta: Arbitrary canonical-authored components are transported as base inverse followed by the source component followed by pulled hom; arbitrary generated components are transported as base hom followed by the source component followed by pulled inverse. Each refinement composite is exactified over the unchanged G-115 core mate. Both directions separately preserve component base, coefficient identity, route triangle, edge naturality, comparator intertwining, nil, append, and two-cell pasting. Actual endpoint inverse cancellation proves pointwise complete GeometryTotalHom recovery through the faithful exact embedding; structure extensionality then proves both solution-level inverse laws. The resulting Equiv stores no source solution. A named canonical companion is constructed by applying its inverse to the theorem-generated solution.
  completion_candidate: no
  lean_artifacts: [canonicalSolutionForwardCoreAt, canonicalSolutionForwardRefinementAt, canonicalSolutionForwardRefinementAt_base, canonicalSolutionForwardAt, canonicalSolutionForwardAt_toRefinement, canonicalSolutionForwardAt_base, canonicalSolutionForwardAt_triangle, canonicalSolutionForwardAt_coefficient_id, canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt_naturality_inv, canonicalSolutionForwardAt_edge_naturality, canonicalSolutionForwardAt_comparator_intertwining, canonicalSolutionForwardAt_path_naturality, canonicalSolutionForwardAt_authored_twoCell_pasting, canonicalSolutionForward, generatedSolutionBackwardCoreAt, generatedSolutionBackwardRefinementAt, generatedSolutionBackwardRefinementAt_base, generatedSolutionBackwardAt, generatedSolutionBackwardAt_toRefinement, generatedSolutionBackwardAt_base, generatedSolutionBackwardAt_triangle, generatedSolutionBackwardAt_coefficient_id, generatedSolutionBackwardAt_edge_naturality, generatedSolutionBackwardAt_comparator_intertwining, generatedSolutionBackwardAt_path_naturality, generatedSolutionBackwardAt_authored_twoCell_pasting, generatedSolutionBackward, generatedSolutionBackwardAt_canonicalSolutionForward, canonicalSolutionForwardAt_generatedSolutionBackward, CanonicalUpperRefinementBCSolution.ext, GeometryCompatibleUpperRefinementBCSolution.ext, generatedSolutionBackward_canonicalSolutionForward, canonicalSolutionForward_generatedSolutionBackward, canonicalGeneratedUpperRefinementBCSolutionEquiv, canonicalCompanionUpperRefinementBCSolution, canonicalGeneratedUpperRefinementBCSolutionEquiv_companion]
  source_sha256:
    UpperGeometryCompatibleSolutionEquivalence.lean: b48f1d23dd31c88ca95eead93250f2de6a6a6df49cf1a59ebf416b1b6314e9dd
  evidence: [focused Lean file check, 38-declaration namespace standard-axiom audit, two componentwise exactification directions, separate base coefficient triangle edge comparator and path preservation theorem families, two faithful complete-component cancellation theorems, two structure-level inverse laws, wrapper-free Equiv]
audits:
  premise_delta:
    ambient_boundary: [Cycle 61 typed solution contracts, complete endpoint geometry isomorphisms, independent authored and generated route edges and comparators]
    direction_hypothesis: []
    discharged: [arbitrary canonical-to-generated solution transport, arbitrary generated-to-canonical solution transport, all forward field preservation, all backward field preservation, forward component cancellation, backward component cancellation, both solution-level inverse laws, wrapper-free solution Equiv, named canonical companion from the Equiv]
    remaining: [named canonical companion problem, named decision and genuinely lax firing fixture, comparator-incoherent negative artifact and no-solution theorem, paired cochain and restricted reselection transport, UpperStageExchangeExact companion iff]
  certificate_provenance:
    forward: exactification of base endpoint inverse, arbitrary canonical component, and pulled endpoint hom
    backward: exactification of base endpoint hom, arbitrary generated component, and pulled endpoint inverse
    inverses: faithful exactGeometryToRefinementGeometry reflection after literal category hom-inverse and inverse-hom cancellation; source solutions are not retained
  proof_use:
    used: [all four endpoint hom and inverse base laws, both route endpoint factor laws, both edge naturality directions, both comparator conjugation directions per transport, arbitrary source solution triangle edge comparator fields, both route coefficient identity laws, exactGeometryHomOfRefinement_toRefinement, exact embedding map_injective, category Iso cancellation]
    deliberately_not_used: [old G-114 selected solution, G-114 selected endpoint comparison, caller-supplied transport or inverse law, source-solution field, sigma or wrapper, proof irrelevance as the component inverse, lower inverse]
  structure_field_escape: neither transport adds an input or certificate; each output structure is freshly constructed from the transformed complete components and newly proved equations
  route_integrity: forward and backward directions use opposite actual endpoint hom/inv conjugations, their route-specific edge and comparator equations, and both independently generated endpoint families
  predecessor_integrity: G-108 G-112 G-114 Formal and the fixed GOAL are unchanged; one G-115 solution-equivalence module and registrations are added
  target_fitting: none-found; arbitrary solution data are transformed rather than copied, and component recovery is a complete geometry equality reflected by the faithful exact embedding
  vacuity: the Equiv acts on the full solution types and the named generated inhabitant yields a named canonical companion through its actual inverse
  one_way_as_equivalence: none-found; both functions and both inverse laws are explicit theorem artifacts
  goal_or_report_reinterpretation: none-found; the named canonical companion problem, decision and negative fixtures, cochain, and exchange-exact obligations remain unchecked and status stays target-proof-checkpoint
  validation_refs: [`./check_research_modules.sh --focused ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCompatibleSolutionEquivalence.lean` passed and reported 38 declarations under AAT.AG.DoctrineFiberProduct standard axioms only; only the direct Cycle 61 solution-contract dependency DAG was targeted when its olean was absent; Research aggregate and full build were not run]
  blocking_findings: []
  next_obligation: Construct the named canonical companion problem and the named upperDecisionContext upperDecisionProblem and upperDecisionSolution from a genuinely lax root-connected finite compatible input with nonidentity refinement strong edge comparator and raw cochain, prove a concrete nonidentity complete solution component without deciding IsIso, then construct the comparator-incoherent negative raw problem and its no-solution theorem.
```

## Cycle 63 — generated decision-component carrier no-go

```yaml
ledger_type: target_cycle_result
goal: G-115-aat-upper-stage-lift
cycle: 63
goal_blob_sha: 65a084cfe6eb6094d2dc33193e0b9185393043f44387e12151c17b355911044c
base_oid: 986beb0ee08465b393229478f67094979f10ae76
tracking_issue: 4250
report_path: research/reports/G-115-aat-upper-stage-lift.md
selection:
  proof_state_ref: Cycle 62 merged the wrapper-free canonical-authored/generated solution Equiv and left the named genuinely lax decision fixture as the next fixed obligation
  proof_dag_predecessors: [generated exact forward carrier transports, generated realized-refinement forward carrier transports, exact and realized-refinement backward carrier transports, upperGeometryMate construction, theorem-generated compatible solution constructor]
  proof_obligation: Determine whether a theorem-generated compatible solution can satisfy the fixed GOAL requirement that one actual solution component differ from identity or equality transport by a concrete Support Axis or Observable value evaluation
  selection_reason: Every otherwise suitable finite fixture still uses the same theorem-generated vertical component. A generic carrier theorem decides the requirement before adding new fixture data and prevents a target-fitting core-only witness from being accepted.
  expected_result_type: blocker-fixed
  lean_targets: [ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCompatibleDecisionNoGo.lean]
  risks: [mistaking nonidentity base Atom or signature action for a local geometry carrier value, known invertible twist repackaging, fixture-specific argument, proof by empty carrier, conflating HEq with unproved definitional equality]
  unchecked: [any human-approved GOAL reinterpretation or new semantic primitive, named positive and negative problem packets, paired cochain transport, UpperStageExchangeExact companion iff]
result:
  proposed_result_type: blocker-fixed
  proof_state: target-refuted
  stop_reason: target-refuted
  proof_obligation_delta: The base forward route preserves every Support Axis and Observable carrier value by composing the existing generated exact and realized-refinement HEq laws. The pulled reverse comparison has the existing backward HEq laws. Their composite is the explicit upper geometry mate, and the actual mate base cast preserves the same HEq results. Unfolding the caller-free generated solution constructor therefore proves, for every compatible input vertex context and carrier value, that each of its three local geometry component maps is equality transport. Consequently no finite presentation active refinement source edge authored comparator or derived raw cochain can make a value of this fixed generated solution component differ.
  completion_candidate: no
  lean_artifacts: [UpperGeometryCleavage.baseRouteForwardSupportComp_heq, UpperGeometryCleavage.baseRouteForwardAxisComp_heq, UpperGeometryCleavage.baseRouteForwardObservableComp_heq, UpperGeometryCleavage.upperGeometryMateSupportComp_heq, UpperGeometryCleavage.upperGeometryMateAxisComp_heq, UpperGeometryCleavage.upperGeometryMateObservableComp_heq, UpperGeometryCleavage.upperGeometryMate_actual_supportComp_heq, UpperGeometryCleavage.upperGeometryMate_actual_axisComp_heq, UpperGeometryCleavage.upperGeometryMate_actual_observableComp_heq, UpperGeometryCompatibleProblemInputData.generatedGeometryCompatibleSolution_supportComp_heq, UpperGeometryCompatibleProblemInputData.generatedGeometryCompatibleSolution_axisComp_heq, UpperGeometryCompatibleProblemInputData.generatedGeometryCompatibleSolution_observableComp_heq]
  source_sha256:
    UpperGeometryCompatibleDecisionNoGo.lean: 4c47ea755e5678a8626fe9211a1fe6ab8b053f1b59db30c3236778a0bf4a6e03
  evidence: [focused Lean file check, 12-declaration namespace standard-axiom audit, direct predecessor targeted build only, generic three-carrier HEq theorem family, theorem-generated solution unfolding]
audits:
  premise_delta:
    ambient_boundary: [current generated exact and realized-refinement geometry transport primitives, fixed compatible solution constructor, fixed GOAL literal Support Axis Observable nonidentity evaluation requirement]
    direction_hypothesis: []
    discharged: [generic base-route forward carrier preservation, generic explicit mate carrier preservation, actual mate cast carrier preservation, generated compatible solution carrier preservation at every vertex]
    remaining: [positive decision input edge comparator and raw cochain construction cannot discharge the contradicted local-carrier nonidentity requirement, named canonical companion problem remains semantically unspecified by the solution-only Equiv, negative problem, paired cochain, exchange-exact iff]
  certificate_provenance:
    forward: generatedExactSupport Axis Observable HEq and generatedRefinementSupport Axis Observable HEq theorem families
    backward: pulledRouteBackwardSupport Axis Observable HEq theorem families
    solution: generatedGeometryCompatibleUpperRefinementBCSolution component is the actual upperGeometryMate at each vertex
  proof_use:
    used: [exact forward carrier laws, realized-refinement forward carrier laws, pulled backward carrier laws, base-route composition order, explicit-to-actual mate equality, generated solution constructor]
    deliberately_not_used: [activeReverse core Atom nonidentity as a substitute, NoncentralTwist known automorphism as a substitute, IsIso or not IsIso of any decision component, caller-supplied solution, empty presentation or empty carrier]
  structure_field_escape: no input field or certificate is added; the no-go quantifies over every existing certificate-free compatible input
  route_integrity: both generated base-route forward stages and the opposite pulled-route backward stages are consumed before concluding carrier preservation
  predecessor_integrity: G-108 G-112 G-114 Formal the fixed GOAL and all Cycle 62 declarations are unchanged; one G-115-local generic no-go module and registrations are added
  target_fitting: none-found; the proof blocks the core-only and known-twist substitutions that the fixed GOAL explicitly rejects
  vacuity: every theorem quantifies an arbitrary actual vertex site context and existing carrier value; no emptiness is used to claim a nonidentity witness
  one_way_as_equivalence: not-applicable
  goal_or_report_reinterpretation: required; under the ordinary GeomReadHom meaning of Support Axis Observable component the fixed requested nonidentity value is contradicted by the generic theorem family. Counting the base upper Atom or signature axis map instead changes the target reading, while permitting nonidentity local carrier maps requires a new semantic transport primitive.
  validation_refs: [`./check_research_modules.sh --focused ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCompatibleDecisionNoGo.lean` passed and reported 12 declarations under AAT.AG.DoctrineFiberProduct standard axioms only; only the direct Cycle 62 solution-equivalence dependency DAG was targeted when its olean was absent; Research aggregate and full build were not run]
  blocking_findings: [The fixed O10 nonvacuity clause requires a theorem-generated solution local Support Axis or Observable value to differ from identity or equality transport, but all three are generically HEq to the input carrier value.]
  next_obligation: Human GOAL revision is required before implementation can continue. The revision must either identify a different nonidentity observation surface such as the base upper map, or introduce and specify a semantic primitive capable of generating nonidentity local geometry carrier actions. The solution-type Equiv also cannot itself construct a problem object until the intended canonical companion problem type is specified.
```

## Cycle 64 — revision 7 named compatible decision packet

```yaml
ledger_type: target-proof-checkpoint
goal: G-115-aat-upper-stage-lift
cycle: 64
goal_blob_sha: 2e0c792a9387f9f4d0272590ad0129bfea5e04ff
goal_sha256: 14c9f071c1815252693ab0e060f6dcd7172057bc1cb2a572e9ef5bd77159507b
base_oid: 8d916de9cd77b88efdb37cdbba4dd171f96a2f4b
tracking_issue: 4250
report_path: research/reports/G-115-aat-upper-stage-lift.md
selection:
  proof_state_ref: Revision 7 merged in PR 4319 after four independent central audits and one finding-limited direct response; Cycle 63 remains the terminal revision-6 target refutation
  proof_dag_predecessors: [activeReverseContext and its outside-exact nonidentity refinement witnesses, certificate-free UpperGeometryCompatibleProblemInput, generated base and pulled route transports and comparators, generated compatible solution constructor, wrapper-free canonical-generated solution Equiv, generic generated-component carrier-conservativity]
  proof_obligation: Construct one named root-connected finite compatible problem over the active reverse context whose genuinely lax horizontal strong edge, authored comparator, generated comparator, and derived raw cochain fire by concrete evaluations; construct the named generated and canonical-companion solutions over that same problem data; specialize the actual solution edge and comparator equations to the named witnesses without deciding the full component IsIso
  selection_reason: This is the first revision-7 discharge-required obligation and the common positive packet consumed by the later negative, paired-cochain, exchange-exactness, and G-116 decision stages. Closing it as one packet prevents an existence-only fixture or a comparator-only witness from being mistaken for Gr4 nondegeneracy.
  expected_result_type: proof-obligation-discharged
  lean_targets: [ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCompatibleDecisionFixtures.lean]
  risks: [identity-only or core-only witness, known twist or gauge repackaging, nonidentity certificate stored in an input field, generated comparator assumed nonidentity without concrete evaluation, raw cochain supplied instead of derived, unspecified reselection, separate generated and companion problems, solution equation fields left unused, accidental full-component IsIso decision]
  unchecked: [named comparator-incoherent negative problem and no-solution theorem, paired cochain and restricted reselection bidirectional transport, UpperStageExchangeExact companion iff, G-116 O12 full-component branch decision, final K4 completion review]
result:
  proposed_result_type: proof-obligation-discharged
  proof_state: target-proof-checkpoint
  proof_obligation_delta: A four-axis finite core and selected geometry are generated inside the actual active-reverse target fiber. A pointed finite-meet local-context preorder exposes four actual Support Axis and Observable values at the named decision context, with a Support/Axis-empty and uniquely observable bottom making the adjacent transpositions natural on the whole site. Its one-vertex presentation is root-connected and has a coefficient-trivial nonidentity strongly cocartesian edge. The edge fires 0 to 1 and the authored comparator fires 1 to 2 on all three local geometry carriers. For the generated base-route Cartesian comparator, the reviewed realization-exact Support Axis and Observable equivalences pull the concrete source values one and two back to actual generated-route total carrier values; the full Cartesian factorization proves the generated comparator itself sends each generated one-value to the corresponding two-value and hence moves that value. The source and generated base raw cochains are independently derived and fire on the signature axis. The named generated and canonical-companion solutions share exactly one problem data object, the solution Equiv maps the companion to the generated solution, the generic vertical carrier-conservativity family is specialized to this named solution, and its actual edge and comparator equations are specialized to the firing witnesses. No full-component IsIso statement is made.
  completion_candidate: no
  lean_artifacts: [UpperDecisionWitness.decisionContext, UpperDecisionWitness.bottomContext, UpperDecisionWitness.decisionContextPreorder, UpperDecisionWitness.decisionContextFiniteMeet, UpperDecisionWitness.reading, UpperDecisionWitness.core, UpperDecisionWitness.coreObject, UpperDecisionWitness.package, UpperDecisionWitness.presentation, UpperDecisionWitness.sourceFiberDiagram, UpperDecisionWitness.sourceTransport, UpperDecisionWitness.problemData, UpperDecisionWitness.problem, UpperDecisionWitness.solution, UpperDecisionWitness.canonicalCompanionSolution, upperDecisionContext, upperDecisionProblem, upperDecisionSolution, upperDecisionCanonicalCompanionSolution, upperDecisionCanonicalCompanion_maps_to_generated, UpperDecisionWitness.active_refinement_fires, UpperDecisionWitness.context_outside_exact_image, UpperDecisionWitness.problem_root_connected, UpperDecisionWitness.source_edge_local_support_fires, UpperDecisionWitness.source_edge_local_axis_fires, UpperDecisionWitness.source_edge_local_observable_fires, UpperDecisionWitness.source_edge_ne_identity, UpperDecisionWitness.authored_comparator_local_support_fires, UpperDecisionWitness.authored_comparator_local_axis_fires, UpperDecisionWitness.authored_comparator_local_observable_fires, UpperDecisionWitness.authored_comparator_ne_one, UpperDecisionWitness.refinementSupportSigmaMap, UpperDecisionWitness.refinementSupportSigmaMap_comp, UpperDecisionWitness.refinementAxisSigmaMap, UpperDecisionWitness.refinementAxisSigmaMap_comp, UpperDecisionWitness.refinementObservableSigmaMap, UpperDecisionWitness.refinementObservableSigmaMap_comp, UpperDecisionWitness.generatedBaseRealizationExact, UpperDecisionWitness.generatedBaseRouteLeg_supportComp_eq_homSupply, UpperDecisionWitness.generatedBaseRouteLeg_axisComp_eq_homSupply, UpperDecisionWitness.generatedBaseRouteLeg_observableComp_eq_homSupply, UpperDecisionWitness.generatedBaseRoute_supportSigmaMap_eq, UpperDecisionWitness.generatedBaseRoute_axisSigmaMap_eq, UpperDecisionWitness.generatedBaseRoute_observableSigmaMap_eq, UpperDecisionWitness.generatedBaseSupportValue, UpperDecisionWitness.generatedBaseAxisValue, UpperDecisionWitness.generatedBaseObservableValue, UpperDecisionWitness.generatedBaseRoute_support_value, UpperDecisionWitness.generatedBaseRoute_axis_value, UpperDecisionWitness.generatedBaseRoute_observable_value, UpperDecisionWitness.authoredComparator_support_value, UpperDecisionWitness.authoredComparator_axis_value, UpperDecisionWitness.authoredComparator_observable_value, UpperDecisionWitness.generated_base_comparator_local_support_fires, UpperDecisionWitness.generated_base_comparator_local_support_ne_input, UpperDecisionWitness.generated_base_comparator_local_axis_fires, UpperDecisionWitness.generated_base_comparator_local_axis_ne_input, UpperDecisionWitness.generated_base_comparator_local_observable_fires, UpperDecisionWitness.generated_base_comparator_local_observable_ne_input, UpperDecisionWitness.generated_base_comparator_axis_fires, UpperDecisionWitness.generated_base_comparator_ne_one, UpperDecisionWitness.source_raw_cochain_axis_fires, UpperDecisionWitness.source_raw_cochain_ne_one, UpperDecisionWitness.generated_base_raw_cochain_axis_fires, UpperDecisionWitness.generated_base_raw_cochain_ne_one, UpperDecisionWitness.solution_support_carrier_conservative, UpperDecisionWitness.solution_axis_carrier_conservative, UpperDecisionWitness.solution_observable_carrier_conservative, UpperDecisionWitness.solution_edge_naturality_fires, UpperDecisionWitness.solution_comparator_intertwining_fires]
  source_sha256:
    UpperGeometryCompatibleDecisionFixtures.lean: a853df47a837f523b3b6ff94a1cb19cebc7eaedf00e8caacc2fdf4ba1fe904f5
  evidence: [focused Lean single-file check, 184-declaration namespace standard-axiom audit, concrete local Support Axis Observable evaluations for the horizontal edge authored comparator and Cartesian-generated comparator, independent generated-comparator factorization and source and generated raw-cochain signature-axis evaluations, named vertical carrier-conservativity specializations, actual solution field specialization, same-problem solution Equiv computation]
audits:
  premise_delta:
    ambient_boundary: [revision 7 activeReverseContext, certificate-free compatible input, theorem-generated route comparators and solution, wrapper-free solution Equiv, generic vertical carrier-conservativity]
    direction_hypothesis: [one authored finite source transport with independently qualified edge and authored comparator]
    discharged: [named upperDecisionContext problem generated solution and canonical companion, active outside-exact refinement, root-connected finite source diagram, local Support Axis Observable nonidentity strong-edge firing, local Support Axis Observable authored-comparator firing, generated-route Support Axis Observable values corresponding to concrete one and two, Cartesian-generated comparator local three-carrier firing and moved-input witnesses, identity-reselection source and generated raw-cochain firing, coefficient identities, same-problem Equiv application, named vertical carrier-conservativity specializations, named solution edge and comparator equation specializations]
    remaining: [comparator-incoherent negative raw problem and no-solution theorem, paired cochain and restricted reselection bidirectional transport, UpperStageExchangeExact companion iff, G-116 O12 full-component branch decision, K4 completion audit]
  certificate_provenance:
    problem: one UpperGeometryCompatibleProblemInput containing only presentation coefficient source diagram source geometry and authored source transport
    generated_comparator: Cartesian pullback of the authored comparator through generatedBaseCompositeFiberAutHomAt; nonidentity is proved from its actual factorization equation and a concrete signature-axis evaluation
    raw_cochains: compatibleSourceRawDefectCochain and generatedBaseRouteRawDefectCochain at the fixed identity reselection; the generated cochain is the proved group-hom image of the source cochain
    solutions: generated by generatedGeometryCompatibleUpperRefinementBCSolution and canonicalCompanionUpperRefinementBCSolution over the same problem.data
  proof_use:
    used: [activeReverse outside-exact and Atom witness, both independent strong qualifications of the source edge, generated base-route realization-exact Support Axis Observable equivalences, generated comparator full factorization projected to total local carriers, canonical comparator uniqueness, raw defect formula, generated raw-cochain image theorem, solution Equiv companion equation, actual solution edge_naturality and comparator_intertwining fields]
    deliberately_not_used: [caller-supplied solution, stored generated comparator, stored raw cochain, nonidentity Prop field, known post-composed twist or gauge, separate companion problem, full component IsIso or not-IsIso]
  structure_field_escape: no new input or certificate field; all generated comparators cochains solutions and nonidentity theorems are downstream declarations
  route_integrity: source authored data generate the base and pulled routes; the positive packet proves firing on the generated base comparator and generated base raw cochain, then consumes the generated solution equations on the named edge and cell
  predecessor_integrity: G-108 G-109 G-112 G-114 Formal and the revision-7 GOAL are unchanged; one G-115-local fixture module and its two registrations are added
  target_fitting: none-found after central-finding repair; the core and geometry are rebuilt in the actual active target fiber, the edge and authored comparator move actual local Support Axis and Observable values, the generated comparator moves actual generated-route total carrier values proved through its full Cartesian factorization rather than a core-only projection, cochains are separately derived, and no nonidentity claim is stored as an input certificate
  vacuity: the source site has a named context and top cover, the coefficient ring and raw relation are nonzero, and the named edge cell axis values and problem solutions are all inhabited
  one_way_as_equivalence: none-found; both named solutions inhabit the same indexed problem fiber and the existing two-sided Equiv is evaluated on the companion
  goal_or_report_reinterpretation: none-found; vertical carrier-conservativity remains unchanged, horizontal and two-cell firing is newly discharged, and full IsIso truth remains exclusively unchecked in G-116 O12
  validation_refs: [`./check_research_modules.sh --focused ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCompatibleDecisionFixtures.lean` passed and reported 184 declarations under AAT.AG.DoctrineFiberProduct standard axioms only; only the missing direct dependency targets RefinementBaseChange.Witnesses ComparisonDescentInstances and UpperGeometryCompatibleDecisionNoGo were built; Research aggregate and full build were not run]
  blocking_findings: []
  next_obligation: Construct the named comparator-incoherent raw problem outside the compatible locus, its rigid comparator-free pre-solution, and the concrete no-solution theorem without adding a comparator certificate or applying the compatible solution Equiv.
```

## Cycle 66 — coefficient-trivial upper-reselection suborbit

```yaml
ledger_type: target_cycle_result
goal: G-115-aat-upper-stage-lift
cycle: 66
goal_blob_sha: 2e0c792a9387f9f4d0272590ad0129bfea5e04ff
goal_sha256: 14c9f071c1815252693ab0e060f6dcd7172057bc1cb2a572e9ef5bd77159507b
base_oid: a1bf604b8637e4a95052e5925bcb9c8bb079de9b
tracking_issue: 4250
report_path: research/reports/G-115-aat-upper-stage-lift.md
selection:
  proof_state_ref: Revision 7 Cycle 64 is the latest merged checkpoint. Cycle 65 was rejected before merge because its custom raw problem did not inhabit the fixed UpperRefinementBCProblem and UpperRefinementBCSolution contract or fire the required local comparator surface. The actual negative bridge remains open, so this cycle selects the independent runnable predecessor of clause (c).
  proof_dag_predecessors: [existing actual UpperEdgeReselection, existing actual InUpperReselectionOrbit, fixed-coefficient two-layer transport, generated compatible base and pulled route transports]
  proof_obligation: Define coefficient-trivial upper edge reselections from the existing actual reselection family and edgewise coefficient identity, cut out their generated suborbit inside the actual upper reselection orbit, prove identity and pointwise multiplication closure, and specialize the construction to both generated compatible routes.
  selection_reason: Clause (c) explicitly requires this subtype and suborbit before the paired solution-intertwining relation can be typed. The fixed GOAL also explicitly says that suborbit extent or membership alone is not an outcome, so this cycle is only a proof-checkpoint.
  expected_result_type: proof-checkpoint
  lean_targets: [ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCoefficientTrivialReselection.lean]
  risks: [invented reselection space, coefficient identity stored without the actual automorphism, custom orbit replacing InUpperReselectionOrbit, suborbit membership misreported as paired preservation, generic API not specialized to generated routes]
  unchecked: [actual comparator-incoherent raw problem and no-solution theorem, paired solution-intertwining relation, relation closure under identity vertical composition and path concatenation, componentwise raw-cochain intertwining, bidirectional conjugation transport and inverse laws, paired restricted-suborbit preservation, named nondegenerate intertwined pair, UpperStageExchangeExact companion iff, K4 completion audit]
result:
  proposed_result_type: proof-checkpoint
  proof_state: target-proof-checkpoint
  proof_obligation_delta: CoefficientTrivialUpperEdgeReselection now contains the literal existing UpperEdgeReselection together with edgewise equality of each target-fiber automorphism coefficient hom to RingHom.id. Identity and the existing pointwise reselection multiplication preserve this property. InCoefficientTrivialUpperReselectionOrbit is generated by those actual witnesses using upperRawDefectCochain, and every restricted member maps directly to the existing InUpperReselectionOrbit with the same witness and equality. The identity raw cochain is inhabited explicitly. Both generated compatible base and independently generated pulled transports now expose this exact restricted reselection type and identity-orbit theorem. No paired solution relation, cochain equivalence, full orbit map, selector, or unconditional MapsTo statement is claimed.
  completion_candidate: no
  lean_artifacts: [CoefficientTrivialUpperEdgeReselection, CoefficientTrivialUpperEdgeReselection.ext, CoefficientTrivialUpperEdgeReselection.one, CoefficientTrivialUpperEdgeReselection.mul, InCoefficientTrivialUpperReselectionOrbit, InCoefficientTrivialUpperReselectionOrbit.toInUpperReselectionOrbit, identityRawDefectCochain_mem_coefficientTrivialOrbit, UpperGeometryCompatibleProblemInputData.GeneratedBaseCoefficientTrivialUpperEdgeReselection, UpperGeometryCompatibleProblemInputData.GeneratedPulledCoefficientTrivialUpperEdgeReselection, UpperGeometryCompatibleProblemInputData.generatedBaseIdentityRawDefectCochain_mem_coefficientTrivialOrbit, UpperGeometryCompatibleProblemInputData.generatedPulledIdentityRawDefectCochain_mem_coefficientTrivialOrbit]
  source_sha256:
    UpperGeometryCoefficientTrivialReselection.lean: 720030064200a23c907038cf89586c61e8fe512d75b91f3ef15e83c73e2d9996
  evidence: [focused Lean single-file check, 27-declaration namespace standard-axiom audit, literal actual-reselection projection, literal actual-orbit witness projection, generated-base and generated-pulled route specializations]
  claim_mapping:
    theorem_names: [CoefficientTrivialUpperEdgeReselection, CoefficientTrivialUpperEdgeReselection.one, CoefficientTrivialUpperEdgeReselection.mul, InCoefficientTrivialUpperReselectionOrbit, InCoefficientTrivialUpperReselectionOrbit.toInUpperReselectionOrbit, identityRawDefectCochain_mem_coefficientTrivialOrbit, UpperGeometryCompatibleProblemInputData.generatedBaseIdentityRawDefectCochain_mem_coefficientTrivialOrbit, UpperGeometryCompatibleProblemInputData.generatedPulledIdentityRawDefectCochain_mem_coefficientTrivialOrbit]
    source_labels: [revision 7 target theorem clause (c) actual paired orbit intertwining typing predecessor, target proof artifacts coefficient-trivial reselection and actual restricted suborbit]
    conjuncts: [actual upper reselection subtype, edgewise coefficient identity, identity witness, pointwise multiplication closure, actual restricted suborbit inclusion, generated base and pulled route specializations]
    undischarged_assumptions: []
    acceptance_point: The declarations construct only the literal actual reselection subtype and its actual raw-cochain suborbit, prove identity and pointwise multiplication closure, and specialize them to both theorem-generated compatible routes. This is a typing predecessor and does not discharge or restate the required paired relation.
    port_status: not-applicable
audits:
  premise_delta:
    discharged: [the existing G-109 actual upper reselection is retained literally, the existing actual raw defect cochain is retained literally, edgewise coefficient identity is proved for identity and pointwise multiplication, both theorem-generated compatible route transports are consumed]
    remaining: [paired relation over an arbitrary actual compatible solution, use of solution component triangle edge and comparator equations, path-concatenation closure, componentwise cochain intertwining, forward and backward endpoint-conjugation transport with inverse laws, paired restricted membership preservation, named nonidentity firing, negative raw standard-contract problem, exchange-exactness companion iff]
  certificate_provenance:
    discharged: [reselection is the existing UpperEdgeReselection on FixedCoefficientTwoLayerTransportOver.toTwoLayerLiftData, coefficient identity is proved from the actual CompositeFiberAut hom geometry coefficientHom, restricted membership uses an existential actual reselection witness and the existing upperRawDefectCochain equality]
    unresolved: [paired solution-intertwining witness, endpoint-conjugation transport and inverse certificate, named nonidentity intertwined pair]
  proof_use:
    used: [actual target-fiber automorphism, coefficient hom of that automorphism, existing pointwise reselection multiplication, existing raw defect cochain, actual generated base and pulled route transports]
    unused: [caller-supplied orbit class, custom cochain, selector, Set.MapsTo, full-orbit coincidence, solution equation fields reserved for the successor paired relation]
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [`./check_research_modules.sh --focused ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCoefficientTrivialReselection.lean` passed and reported 27 declarations under AAT.AG.DoctrineFiberProduct standard axioms only; `lake build ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCoefficientTrivialReselection` passed for the targeted module and its dependency DAG; Research aggregate and full build were not run]
  blocking_findings: []
  next_obligation: Define the paired base and pulled coefficient-trivial reselection relation for an arbitrary GeometryCompatibleUpperRefinementBCSolution, beginning with identity closure and separately consuming the solution component, factorization triangle, edge naturality, authored comparator equation, and coefficient identity. The unmerged Cycle 65 negative route remains a separate obligation and must eventually use the actual UpperRefinementBCProblem and UpperRefinementBCSolution contracts.
```

## Cycle 67 — revision 8 comparator-descent target repair

```yaml
ledger_type: target_cycle_result
goal: G-115-aat-upper-stage-lift
cycle: 67
goal_blob_sha: 9bf5b5d9ffc209dd050a90e4e3aad7c4d8378961
goal_sha256: 9a57647e18671e9903c695bea7276140172c0d59ce56e006cced8bd260a0dc38
base_oid: b51d3b792f947e316d3727843c661832239c23ff
tracking_issue: 4250
report_path: research/reports/G-115-aat-upper-stage-lift.md
selection:
  proof_state_ref: Revision 7 Cycle 65 was rejected before merge and Issue 4250 comment 5481630778 fixed the actual-endpoint bridge defect. Human approval selects revision 8 comparator descent as the replacement target.
  proof_dag_predecessors: [Cycle 64 generated compatible route transports and named solution component, generated nonidentity base comparator, fixed-coefficient authored transport contract, identity CompositeFiberAut, actual and compatible solution comparator equations]
  proof_obligation: Replace the custom raw no-solution problem with a typed comparator descent condition on two qualified fixed-coefficient route transports and the existing actual component, retaining a solution-derived positive pair and a same-route negative pair whose pulled transport preserves all comparator-independent data and laws while changing only its comparator to identity.
  selection_reason: The rejected raw problem imported a selected-endpoint realization obligation unrelated to comparator coherence and did not inhabit the actual UpperRefinementBCProblem or UpperRefinementBCSolution contract. Qualified-transport comparator descent is the exact O10 law surface already carried by actual solutions and presents the descent locus inside the product of individually qualified authored comparator choices without changing the route geometry or local mate.
  expected_result_type: blocker-fixed
  lean_targets: [ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCompatibleComparatorIncoherence.lean]
  risks: [custom problem reintroduced, selected-endpoint realization reintroduced, unqualified endpoint automorphism pair used as the negative witness, comparator failure encoded as an input certificate, negative pair changes route geometry edge lifts qualifications or component, one carrier evaluation overclaimed as all three, comparator descent confused with O12 IsIso failure]
  unchecked: [Lean definition of qualified-transport UpperComparatorDescentAt, actual and compatible solution bridge theorems, positive generated pair, generatedPulledIdentityComparatorTransport and its retained transport fields, both comparator coefficient laws, Support Axis and Observable negative evaluations, paired solution-intertwining relation, cochain transport, UpperStageExchangeExact companion iff]
result:
  proposed_result_type: blocker-fixed
  proof_state: target-proof-checkpoint
  proof_obligation_delta: The fixed target no longer requires a new raw problem, pre-solution, or proof that UpperRefinementBCSolution is empty. It requires the literal GeometryTotalHom comparator-descent equality on two qualified fixed-coefficient route transports, connections from both actual solution contracts, and the Cycle 64 solution-derived positive pair. The negative side must copy the generated pulled transport's geometry edge lifts core projections strong-cartesian qualifications two-cell-base equality and edge coefficient law, replacing only its comparator by identity and proving that comparator's coefficient law. With the existing nonidentity generated base comparator and the same canonical component, descent failure is required independently on Support Axis and Observable. Comparator-sensitive pasting is not claimed for the negative pair.
  completion_candidate: no
  lean_artifacts: []
  evidence: [Issue 4250 Cycle 67 actual-endpoint bridge analysis, human-approved revision 8, synchronized G-115 G-116 and n1007 contracts]
  claim_mapping:
    theorem_names: [planned UpperComparatorDescentAt, planned UpperRefinementBCSolution.comparatorDescentAt, planned GeometryCompatibleUpperRefinementBCSolution.comparatorDescentAt, planned upperDecisionSolution_comparatorDescentAt, planned generatedPulledIdentityComparatorTransport, planned generatedPulledIdentityComparator_coefficient_id, planned generatedBaseIdentityPair_support_incoherent, planned generatedBaseIdentityPair_axis_incoherent, planned generatedBaseIdentityPair_observable_incoherent]
    source_labels: [revision 8 target theorem clause b comparator descent, O10 comparator descent positive and negative pair]
    conjuncts: [typed qualified-transport hom equality, actual solution connection, compatible solution connection, generated positive pair, same-route same-component qualified negative pair, retained comparator-independent transport fields and laws, both comparator coefficient identities, Support failure, Axis failure, Observable failure, O12 IsIso separation]
    undischarged_assumptions: [all revision 8 Lean artifacts]
    acceptance_point: Human approval repairs a specification defect and restores a typed proof route. This cycle does not claim a Lean implementation or O10 discharge.
    port_status: not-applicable
audits:
  premise_delta:
    discharged: [negative witness scope is fixed to the existing generated route canonical component and qualified authored transport contract, selected-endpoint realization is removed from the negative obligation, O10 and O12 roles are separated]
    remaining: [all revision 8 comparator descent Lean declarations, clauses c and d, final K4 completion audit]
  certificate_provenance:
    discharged: [statement-level provenance fixes positive comparators to the existing compatible solution, negative base comparator to the existing Cycle 64 generated comparator, and negative pulled comparator to identity inside a copied qualified pulled transport]
    unresolved: [Lean construction of the identity-comparator pulled transport, retained-field equalities, both comparator coefficient laws, two solution bridges, and three concrete negative evaluations]
  proof_use:
    used: []
    unused: [planned dependencies pending Lean implementation include the Cycle 64 generated comparator nonidentity and carrier evaluations generated vertical carrier-conservativity literal solution comparator equation and fixed-coefficient transport fields; excluded dependencies are the custom raw problem pre-solution rigidity selected-endpoint realization caller-supplied incoherence certificate and full-component IsIso decision]
  structure_field_escape: cannot-determine
  route_integrity: cannot-determine
  target_fitting: none-found
  vacuity: cannot-determine
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [docs-only git diff --check passed; changed-file hidden and bidirectional Unicode scan had no hits; added-line placeholder scan had no hits; no Lean build is appropriate for this specification-only cycle]
  blocking_findings: []
  next_obligation: Implement qualified-transport UpperComparatorDescentAt and the actual and compatible solution bridge theorems. Then copy the generated pulled route transport with only its comparator changed to identity, prove every retained transport field and both comparator coefficient laws, and focused-check the positive generated pair plus the same-route base-nonidentity pulled-identity negative pair with independent Support Axis and Observable failures.
```

## Cycle 68 — qualified comparator-descent positive and negative pair

```yaml
ledger_type: target_cycle_result
goal: G-115-aat-upper-stage-lift
cycle: 68
goal_blob_sha: 9bf5b5d9ffc209dd050a90e4e3aad7c4d8378961
goal_sha256: 9a57647e18671e9903c695bea7276140172c0d59ce56e006cced8bd260a0dc38
base_oid: d171030411922033c9ed300dc297eb46adfba237
tracking_issue: 4250
report_path: research/reports/G-115-aat-upper-stage-lift.md
selection:
  proof_state_ref: Cycle 67 merged the human-approved revision 8 statement repair and fixed the exact qualified-transport comparator-descent obligation
  proof_dag_predecessors: [UpperRefinementBCSolution.comparator_intertwining, GeometryCompatibleUpperRefinementBCSolution.comparator_intertwining, Cycle 64 generated base and pulled fixed-coefficient route transports, Cycle 64 generated solution component, generated base comparator Support Axis Observable firing theorems, generated base route realization-exact carrier equivalences, generated solution triangle]
  proof_obligation: Implement UpperComparatorDescentAt on two qualified fixed-coefficient transports, connect both actual solution contracts and the named positive solution, construct the same-route pulled identity-comparator transport, and prove independent Support Axis and Observable failures for the resulting negative pair
  selection_reason: This directly discharges the revision 8 replacement for the rejected Cycle 65 raw-problem route. It closes the remaining O10 negative-classification gap without importing selected-endpoint realization or deciding the O12 IsIso question.
  expected_result_type: proof-obligation-discharged
  lean_targets: [ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCompatibleComparatorIncoherence.lean]
  risks: [changing comparator-independent route data, weakening the predicate to a local carrier equation, accepting an incoherence certificate, proving only one carrier failure, losing connection to literal solution fields, claiming common-source pair failure raw solution absence or IsIso failure]
  unchecked: [paired base and pulled coefficient-trivial reselection relation, identity vertical-composition and path-concatenation closure, componentwise raw-cochain intertwining, bidirectional endpoint-conjugation transport and inverse laws, paired restricted-suborbit preservation, named nonidentity intertwined pair, UpperStageExchangeExact companion iff, K4 completion audit]
result:
  proposed_result_type: proof-obligation-discharged
  proof_state: target-proof-checkpoint
  proof_obligation_delta: UpperComparatorDescentAt is the literal complete GeometryTotalHom equality for the two qualified route comparators and the actual target component. Both actual solution contracts imply it from their comparator_intertwining fields, and the Cycle 64 named generated solution supplies the positive pair. generatedPulledIdentityComparatorTransport has the same indexed route geometry and copies edgeLift, edge_base, both strong-cartesian qualifications, twoCellBase, and edge_coefficient_id definitionally from the generated pulled transport while replacing only comparator by identity. Its comparator coefficient law is proved. For the negative pair, the generated solution triangle and the realization-exact base route leg prove its component is injective on each total Support Axis and Observable sigma carrier. Separately, sigma-map carrier-conservativity theorems directly consume the reviewed pointwise Support Axis and Observable conservativity family. Each negative artifact exposes conservation of the post-comparator value and the input value together with the explicit composite-map inequality derived from the existing generated-base comparator 1-to-2 firing theorem. The Support inequality refutes the full comparator-descent equality.
  completion_candidate: no
  lean_artifacts: [UpperComparatorDescentAt, UpperRefinementBCSolution.comparatorDescentAt, UpperGeometryCompatibleProblemInputData.GeometryCompatibleUpperRefinementBCSolution.comparatorDescentAt, UpperGeometryCompatibleProblemInputData.generatedPulledIdentityComparatorTransport, UpperGeometryCompatibleProblemInputData.generatedPulledIdentityComparatorTransport_comparator, UpperGeometryCompatibleProblemInputData.generatedPulledIdentityComparator_coefficient_id, UpperDecisionWitness.upperDecisionSolution_comparatorDescentAt, UpperDecisionWitness.solution_supportSigmaMap_injective, UpperDecisionWitness.solution_axisSigmaMap_injective, UpperDecisionWitness.solution_observableSigmaMap_injective, UpperDecisionWitness.solution_supportSigmaMap_carrier_conservative, UpperDecisionWitness.solution_axisSigmaMap_carrier_conservative, UpperDecisionWitness.solution_observableSigmaMap_carrier_conservative, UpperDecisionWitness.generatedBaseIdentityPair_support_incoherent, UpperDecisionWitness.generatedBaseIdentityPair_axis_incoherent, UpperDecisionWitness.generatedBaseIdentityPair_observable_incoherent, UpperDecisionWitness.generatedBaseIdentityPair_not_comparatorDescentAt]
  source_sha256:
    UpperGeometryCompatibleComparatorIncoherence.lean: 62d8d61b2810d5452961ff8e97ebd2829d7dccd65abc5e525a67b50ac3317384
  evidence: [focused Lean single-file check, 17-declaration namespace standard-axiom audit, literal bridges from both solution comparator fields, definitionally comparator-only transport replacement, existing generated-base comparator coefficient theorem plus new pulled-identity coefficient theorem, direct proof-use of all three reviewed carrier-conservativity theorems, three carrier-specific conservation-and-inequality artifacts, full predicate negation]
  claim_mapping:
    theorem_names: [UpperComparatorDescentAt, UpperRefinementBCSolution.comparatorDescentAt, UpperGeometryCompatibleProblemInputData.GeometryCompatibleUpperRefinementBCSolution.comparatorDescentAt, UpperDecisionWitness.upperDecisionSolution_comparatorDescentAt, UpperGeometryCompatibleProblemInputData.generatedPulledIdentityComparatorTransport, UpperGeometryCompatibleProblemInputData.generatedPulledIdentityComparator_coefficient_id, UpperDecisionWitness.generated_base_comparator_coefficient_id, UpperDecisionWitness.solution_supportSigmaMap_carrier_conservative, UpperDecisionWitness.solution_axisSigmaMap_carrier_conservative, UpperDecisionWitness.solution_observableSigmaMap_carrier_conservative, UpperDecisionWitness.generatedBaseIdentityPair_support_incoherent, UpperDecisionWitness.generatedBaseIdentityPair_axis_incoherent, UpperDecisionWitness.generatedBaseIdentityPair_observable_incoherent, UpperDecisionWitness.generatedBaseIdentityPair_not_comparatorDescentAt]
    source_labels: [revision 8 target theorem clause b qualified comparator descent, O10 comparator descent positive and negative pair]
    conjuncts: [actual complete-hom descent equality, actual solution bridge, compatible solution bridge, generated positive pair, same generated routes and canonical component, comparator-only pulled transport replacement, both comparator coefficient identities, direct Support Axis Observable carrier-conservativity proof-use, Support failure, Axis failure, Observable failure, full descent negation, O12 separation]
    undischarged_assumptions: []
    acceptance_point: The negative artifact is not a custom raw problem. Both endpoint transports inhabit the existing fixed-coefficient qualified transport type, use the same generated route geometry and actual component, and differ only in the pulled authored comparator. The three failures are consequences of existing generated-comparator firing plus a route-factorization injectivity theorem, not stored certificates. This discharges the revision 8 O10 comparator-descent obligation but not clauses c or d.
    port_status: not-applicable
audits:
  premise_delta:
    discharged: [typed qualified-transport descent predicate, both literal solution bridges, named generated positive pair, comparator-only identity transport construction, both comparator coefficient identities, Support Axis Observable negative evaluations, full negative-pair descent refutation]
    remaining: [paired coefficient-trivial reselection relation and closure, componentwise cochain theorem, endpoint-conjugation transport and inverse laws, paired restricted-suborbit preservation, named nonidentity intertwined pair, UpperStageExchangeExact companion iff, K4 completion audit]
  certificate_provenance:
    discharged: [positive pair uses the existing generated solution comparator_intertwining field, base comparator and its coefficient law are the Cycle 64 generated route artifacts, pulled negative comparator is constructed as identity inside a transport copying all other fields, carrier inequalities derive from generated route realization equivalence solution triangle and existing comparator firing]
    unresolved: [paired intertwining and cochain transport witnesses]
  proof_use:
    used: [both literal solution comparator_intertwining fields, generated base and pulled fixed-coefficient transports, generated solution component and triangle, base-route realization-exact Support Axis Observable equivalences, generated-base comparator Support Axis Observable firing and non-input theorems, fixed-coefficient comparator coefficient fields]
    deliberately_not_used: [Cycle 65 custom raw problem or pre-solution, selected G-114 endpoint realization, caller-supplied incoherence certificate, compatible solution Equiv on the negative pair, common-source comparator generation for the negative pulled choice, full-component IsIso or not-IsIso]
  structure_field_escape: none-found
  route_integrity: pass; the pulled negative transport reuses the exact generated pulled route geometry edge lifts projections qualifications and laws and changes only its authored comparator
  predecessor_integrity: G-108 G-109 G-112 G-114 Formal and the fixed revision 8 GOAL are unchanged
  target_fitting: none-found; the descent predicate is the specified complete-hom equality and the negative proof consumes independently established route and carrier theorems
  vacuity: none-found; the positive predicate is inhabited and the negative side is refuted by three explicit values in inhabited total carrier spaces
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [`./check_research_modules.sh --focused ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCompatibleComparatorIncoherence.lean` passed and reported 17 declarations under AAT.AG.DoctrineFiberProduct standard axioms only; module registered in ResearchLean/AG/DoctrineFiberProduct.lean and research-modules.txt; `git diff --check` passed; changed-file placeholder and hidden or bidirectional Unicode scans had no hits; Research aggregate and full build were not run]
  blocking_findings: []
  next_obligation: Define the paired base and pulled coefficient-trivial reselection relation for an arbitrary GeometryCompatibleUpperRefinementBCSolution and prove identity closure while explicitly consuming the component, triangle, edge naturality, comparator equation, and coefficient identity before advancing to cochain intertwining and endpoint conjugation.
```

## Cycle 69 — coefficient-trivial endpoint precursor and nonvacuity

```yaml
ledger_type: target_cycle_result
goal: G-115-aat-upper-stage-lift
cycle: 69
goal_blob_sha: 9bf5b5d9ffc209dd050a90e4e3aad7c4d8378961
goal_sha256: 9a57647e18671e9903c695bea7276140172c0d59ce56e006cced8bd260a0dc38
base_oid: 0e4906b8ed965c81584b1729782f64a979ba6c01
tracking_issue: 4250
report_path: research/reports/G-115-aat-upper-stage-lift.md
selection:
  proof_state_ref: Revision 8 Cycle 68 is merged and discharges clause (b). Cycle 66 already supplies the actual coefficient-trivial reselection subtype and restricted suborbit, but no relation connects the two generated routes.
  proof_dag_predecessors: [Cycle 66 CoefficientTrivialUpperEdgeReselection and generated route specializations, GeometryCompatibleUpperRefinementBCSolution component and edge_naturality, actual upper reselected edge and path lifts]
  proof_obligation: Define the typed edgewise endpoint-component precursor for arbitrary compatible actual solutions; construct identity and pointwise vertical-product closure; derive reselected edge and path naturality; and establish both a named nonidentity positive instance and an explicit negative instance on the actual decision fixture.
  selection_reason: The endpoint precursor must remain a visible complete-geometry equation rather than opaque orbit membership or a core-only proxy, while the unrestricted paired-relation name remains reserved for the full clause (c) contract. Edge and path naturality plus positive and negative instances are the minimal nonvacuous algebraic API required before the raw two-cell cochain calculation can consume triangle comparator and coefficient data.
  expected_result_type: proof-checkpoint
  lean_targets: [ResearchLean/AG/DoctrineFiberProduct/UpperGeometryPairedCoefficientTrivialReselection.lean]
  risks: [paired conclusion hidden in membership or certificate input, core-only equation, invented reselection type, identity-only vacuity, wrong group multiplication order, path theorem bypasses actual edge_naturality, premature full-orbit MapsTo or selector claim]
  unchecked: [full paired relation consuming factorization triangle authored comparator and coefficient component, componentwise raw-cochain intertwining, paired restricted-suborbit preservation, endpoint-comparison conjugation transports and inverse laws, UpperStageExchangeExact companion iff, K4 completion audit]
result:
  proposed_result_type: proof-checkpoint
  proof_state: target-proof-checkpoint
  proof_obligation_delta: CoefficientTrivialUpperReselectionEndpointIntertwining is the literal edge-target GeometryTotalHom precursor between actual coefficient-trivial reselections and an arbitrary compatible solution component; it is explicitly not named or claimed as the full clause (c) paired relation. Identity and pointwise product laws respect the CompositeFiberAut categorical multiplication order, and reselected edge and path naturality directly consume the endpoint equation and solution.edge_naturality. On the one-vertex decision presentation, the authored generated base and pulled comparators define actual edge-indexed coefficient-trivial reselections; solution.comparator_intertwining proves the resulting pair, the base member is nonidentity, and pairing that same base member with pulled identity is refuted by the independently proved Cycle 68 complete comparator-descent obstruction. No orbit-membership equivalence or cochain theorem is claimed yet.
  completion_candidate: no
  lean_artifacts: [upperReselectedEdgeLift_eq_for_g115, upperReselectedPathLift_nil_for_g115, upperReselectedPathLift_cons_for_g115, UpperGeometryCompatibleProblemInputData.CoefficientTrivialUpperReselectionEndpointIntertwining, UpperGeometryCompatibleProblemInputData.coefficientTrivialUpperReselectionEndpointIntertwining_one, UpperGeometryCompatibleProblemInputData.CoefficientTrivialUpperReselectionEndpointIntertwining.mul, UpperGeometryCompatibleProblemInputData.CoefficientTrivialUpperReselectionEndpointIntertwining.reselectedEdge_naturality, UpperGeometryCompatibleProblemInputData.CoefficientTrivialUpperReselectionEndpointIntertwining.reselectedPath_naturality, UpperDecisionWitness.generatedBaseComparatorCoefficientTrivialUpperReselection, UpperDecisionWitness.generatedPulledComparatorCoefficientTrivialUpperReselection, UpperDecisionWitness.generatedBaseComparatorCoefficientTrivialUpperReselection_ne_one, UpperDecisionWitness.generatedComparatorUpperReselections_endpointIntertwining_fires, UpperDecisionWitness.generatedBaseComparatorPulledIdentity_not_endpointIntertwining]
  source_sha256:
    UpperGeometryPairedCoefficientTrivialReselection.lean: 4f06451794c101b4a50cd245df82c08c58571b30a5b995a8ff22ea80ec917453
  evidence: [focused Lean single-file check, 13-declaration namespace standard-axiom audit, explicit identity and vertical-product constructions, edge and path proofs through G-115-local no-unfold rewrite APIs, named nonidentity positive instance, explicit negative instance inherited from Cycle 68 complete-hom refutation]
  claim_mapping:
    theorem_names: [CoefficientTrivialUpperReselectionEndpointIntertwining, coefficientTrivialUpperReselectionEndpointIntertwining_one, CoefficientTrivialUpperReselectionEndpointIntertwining.mul, CoefficientTrivialUpperReselectionEndpointIntertwining.reselectedEdge_naturality, CoefficientTrivialUpperReselectionEndpointIntertwining.reselectedPath_naturality, generatedBaseComparatorCoefficientTrivialUpperReselection_ne_one, generatedComparatorUpperReselections_endpointIntertwining_fires, generatedBaseComparatorPulledIdentity_not_endpointIntertwining]
    source_labels: [revision 8 clause c endpoint-component precursor, target proof strategy K3 paired cochain typing predecessor]
    conjuncts: [typed base and pulled coefficient-trivial witnesses, endpoint component intertwining, identity closure, vertical composition closure, edge naturality, path naturality by induction, named nonidentity positive instance, concrete non-instance]
    undischarged_assumptions: [the full clause c paired relation and its triangle comparator coefficient cochain orbit and conjugation obligations remain target-level obligations]
    acceptance_point: The precursor and its constructors live on the existing actual coefficient-trivial reselection spaces and arbitrary compatible actual solutions. The unrestricted full paired-relation name is deliberately not introduced. The decision specialization proves that the precursor contains a theorem-generated nonidentity pair and excludes another fully typed pair; neither fact is supplied as a relation certificate.
    port_status: not-applicable
audits:
  premise_delta:
    discharged: [actual base and pulled coefficient-trivial reselection typing, arbitrary compatible solution component, identity pair, vertical-product closure, generator edge equation use, path naturality, one-vertex generated comparator reselection construction, named nonidentity positive instance, explicit negative instance]
    remaining: [full paired relation using leg triangle component coefficient and authored comparator, raw-cochain componentwise intertwining, paired restricted membership preservation, bidirectional endpoint conjugation and inverse laws, exchange-exactness companion iff]
  certificate_provenance:
    discharged: [precursor is an exposed GeometryTotalHom equality, identity and multiplication witnesses are theorem-generated, path law is derived by induction from actual edge_naturality, positive pair is generated from authored comparators and the actual solution comparator field, negative pair is reduced to the independently proved complete comparator-descent obstruction]
    unresolved: [full paired contract, cochain intertwining, conjugation transport]
  proof_use:
    used: [existing actual coefficient-trivial reselections and coefficient laws, solution.component, solution.edge_naturality, solution.comparator_intertwining, generated comparator coefficient identities, generated base comparator nonidentity, Cycle 68 complete comparator-descent refutation, CompositeFiberAut hom multiplication order, actual upperReselectedEdgeLift and upperReselectedPathLift]
    deliberately_not_used: [opaque orbit membership as relation, custom cochain, selector, Set.MapsTo, full orbit equality, caller-supplied path law]
  structure_field_escape: none-found; the relation is a transparent Prop and every inhabitant reported in this cycle is constructed by a theorem
  route_integrity: pass; both witnesses remain on the exact generated base and pulled fixed-coefficient transports
  predecessor_integrity: pass; G-108 G-109 G-112 G-114 Formal and the fixed revision 8 GOAL are unchanged; all no-unfold characterization theorems are G-115-local declarations in the new module
  target_fitting: none-found; the declaration and report are limited to the complete-geometry endpoint precursor and leave the actual full paired relation open
  vacuity: pass; identity inhabits the precursor, the named generated comparator reselection pair inhabits it with a proved nonidentity base member, and the same base member paired with pulled identity is explicitly excluded
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found; the endpoint precursor is not mapped to the full clause c paired relation and no cochain or orbit-preservation completion is claimed
  validation_refs: [`./check_research_modules.sh --focused ResearchLean/AG/DoctrineFiberProduct/UpperGeometryPairedCoefficientTrivialReselection.lean` passed and reported 13 declarations under AAT.AG.DoctrineFiberProduct standard axioms only; prior targeted module build passed over its dependency DAG before the conservative relocation of rfl characterization lemmas into this module; module registered in ResearchLean/AG/DoctrineFiberProduct.lean and research-modules.txt; Research aggregate and full build were not run]
  blocking_findings: []
  next_obligation: Define the full transparent clause c paired relation and derive its componentwise upperRawDefectCochain intertwining theorem from endpoint and path naturality while materially consuming solution.triangle solution.comparator_intertwining and solution.component_coefficient_id; then prove paired restricted-suborbit preservation and endpoint conjugation inverse laws.
```
