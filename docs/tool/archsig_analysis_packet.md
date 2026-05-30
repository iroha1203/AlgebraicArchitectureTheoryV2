# ArchSig Analysis Packet

`archsig-analysis-packet-v0` is the North Star ArchSig output artifact.
It reads a source-grounded ArchMap together with one selected interpretation
profile and records AAT-based, bounded analysis for LLM and human review.

```text
ArchMap
  records law-independent Atom observations.

InterpretationProfile
  selects the LawUniverse, witness rules, signature axes, coverage, and exactness.
  The current JSON artifact is still named law-policy-v0 for the profile input.

ArchSig Analysis Packet
  records AAT concept surfaces, architecture state, design pressure, change
  impact, molecule readings, obstruction circuits, signature axes, analytic
  representations, workflow risk readings, spectral analysis readings, design
  principle readings, spectral mode readings, spectral drilldown readings,
  transfer bridge readings, Atom support / compatibility readings,
  LawUniverse coverage, feature extension formula axes, operation calculus law
  axes, path signature trajectories, homotopy / operation-order sensitivity,
  diagram fillability, bounded judgements, repair operation candidates,
  operation deltas, path / homotopy / diagram readings, child-level evidence
  boundaries, ArchMapStore refs, monodromy / boundary holonomy reading family
  policy surfaces, and an LLM interpretation packet.
```

## Responsibility

The packet owns structured analysis results. It is not a theorem proof and not
a single architecture quality score.

The implemented schema records:

- `interpretationProfileRef`
- `selectedLawPolicyRef`
- `archMapRef`
- `archMapStoreRefs`
- `architectureState`
- `designPressure`
- `changeImpact`
- `aatConceptSurfaces`
- `atomConfigurationSummary`
- `architectureObjectProjections`
- `invariantFamilyReadings`
- `lawUniverseReading`
- `moleculeReadings`
- `obstructionCircuits`
- `signatureAxes`
- `analyticRepresentations`
- `couplingCohesionReadings`
- `workflowRiskReadings`
- `spectralAnalysisReadings`
- `spectralModeReadings`
- `spectralDrilldownReadings`
- `transferBridgeReadings`
- `atomSupportAxisReadings`
- `atomCompatibilityReadings`
- `lawUniverseCoverageReadings`
- `featureExtensionFormulaReadings`
- `operationCalculusLawReadings`
- `pathSignatureTrajectoryReadings`
- `homotopyOrderSensitivityReadings`
- `diagramFillabilityReadings`
- `axisForgettingRiskReadings`
- `signatureTrajectoryHomotopyRefutationReadings`
- `bridgeSplitObstructionTransferReadings`
- `operationSquareCandidates`
- `pathContinuationTraces`
- `axisWiseMonodromyDefects`
- `amiAggregateReadings`
- `nonzeroMonodromyWitnesses`
- `featureBoundaryResidualReadings`
- `featureExtensionDiagnosisReadings`
- `monodromyReadingFamily`
- `boundaryHolonomyReadingFamily`
- `representationStrengthReadings`
- `localCurvatureDiagramReadings`
- `threeLayerFlatnessReadings`
- `observationProjectionReadings`
- `stateTransitionAlgebraReadings`
- `operationInvariantGaloisReadings`
- `splitReadinessReadings`
- `designPrincipleReadings`
- `flatnessReading`
- `staticRuntimeSemanticLayerSplit`
- `repairOperationCandidates`
- `operationDeltas`
- `pathHomotopyDiagramReadings`
- `boundedJudgements`
- `llmInterpretationPacket`
- `evidenceBoundary`
- `interpretationNotesForLLM`
- `excludedReadings`
- `nonConclusions`

## Validation Boundary

Packet validation checks identity, ArchMap / interpretation profile references,
AAT concept coverage, bounded judgement statuses, analytic axes, workflow risk
readings, spectral analysis readings, spectral mode readings, design principle
readings, spectral drilldown readings, transfer bridge readings and bridge-edge
source refs, v0.3.0 measurement expansion readings, AAT structural state
readings, ArchMapStore delta / commit / snapshot / index refs, operation square
candidates, axis-wise path continuation traces, monodromy / boundary holonomy
reading family policy surfaces, law-relative obstruction links, signature /
flatness references, repair candidate guardrails, LLM interpretation notes,
evidence boundary, and required non-conclusions.
Each obstruction circuit, signature axis reading, and repair operation candidate
must carry its own `missingEvidence` and `excludedReadings`. Packet-level
`excludedReadings` does not stand in for child-record evidence boundaries.

Validation does not imply:

- Lean theorem proof
- global architecture truth
- source extraction completeness
- universal quality score
- global flatness proof
- automatic repair safety
- source extraction completeness
- merge approval
- LLM output as architecture truth

## Current Fixture

- `tools/archsig/tests/fixtures/minimal/archsig_analysis_packet.json`
- `tools/archsig/tests/fixtures/coupon_rounding/archsig_analysis_packet.json`

The fixture is locked against the static Rust builder and the schema catalog
records both `archsig-analysis-packet-v0` and
`archsig-analysis-packet-validation-report-v0`.

## Builder

`build_archsig_analysis_packet` deterministically builds a packet from one
`ArchMapDocumentV0` and one `LawPolicyDocumentV0`.

The builder:

- evaluates selected interpretation-profile witness rules over ArchMap atom and semantic observations
- uses `concernHints` only as auxiliary evidence
- constructs obstruction circuits only as ArchSig outputs
- values required signature axes from constructed obstruction circuits
- preserves observation gaps as flatness blockers, not measured zero
- emits AAT concept surfaces for Atom, Configuration, ArchitectureObject,
  Invariant, LawUniverse, ObstructionCircuit, ArchitectureSignature, Operation,
  Path, Homotopy, Diagram, and AnalyticRepresentation
- emits architecture state, design pressure, change impact, bounded judgements,
  LLM interpretation, analytic representation, semantic coupling/cohesion,
  workflow risk readings, spectral analysis readings, and design principle readings
- workflow risk readings rank molecule-local review pressure using ArchMap
  atoms, molecule roles, semantic observations, concern hints, and observation
  gaps. They are review-prioritization readings, not quality scores.
- spectral analysis readings build finite matrix-like AAT representations for
  workflow-risk axis pressure, molecule atom/family overlap coupling,
  obstruction-to-axis curvature, and operation-to-signature delta. They record
  matrix shape, entry rule, bounded values, dominant components, coverage
  boundary, and zero-reflecting boundary. They are spectral proxies for review,
  not exact eigenvalue theorems or quality scores.
- spectral mode readings lift spectral analysis into bounded mode proxies:
  dominant/residual gap, localization, matrix density, decomposability, and
  repair perturbation. They are review modes, not exact eigenvector theorems.
- spectral drilldown readings explain spectral modes using dominant atom-family
  composition, high-overlap molecule pair rankings, and positive / negative /
  neutral repair axis deltas.
- transfer bridge readings summarize repair-operation-by-transferred-axis
  matrices, indirect bridge atom families between architecture hubs, and
  evolution risk rankings for repairs and boundary preparation. Each bridge
  edge records shared atom families, exact shared atom refs when present,
  family-supporting atom refs, source refs, source-ref rationale, reviewer
  focus, explicit-contract / implicit-dependency reading, LLM review summary,
  and a recommended cut kind: interface, policy, transaction boundary, or
  anti-corruption layer.
- v0.3.0 measurement expansion readings add current-state coordinates for
  Atom support / axis restriction, Atom compatibility / conflict, LawUniverse
  coverage / witness exactness, feature extension formula axes, operation
  calculus law axes, path signature trajectory, homotopy / operation-order
  sensitivity, diagram fillability, axis-forgetting / projection reflection
  loss, selected trajectory homotopy refutation, and bridge split obstruction
  transfer. These readings keep source refs, observation refs, coverage
  boundaries, evidence boundaries, and non-conclusions; they are not PR / diff
  evolution analysis.
- ArchMapStore is the forward history boundary for PR and longitudinal
  workflows. `ArchMapDelta` and `ArchMapCommit` carry ArchMap-level change
  evidence; `ArchMapSnapshot` and `ArchMapIndex` support large-repository
  current-state inspection. Raw source diffs may narrow source refs, but they
  are not canonical semantic inputs to this packet.
- `codebase-inspection` reads the latest `ArchMapSnapshot`, `ArchMapIndex`, an
  `archsig-analysis-packet-v0`, optional recent deltas, and optional LawPolicy
  provenance to produce `archsig-codebase-inspection-report-v0`. The report is
  a current-state architecture health surface: subsystem boundaries,
  feature-like clusters, operation-like relations, top boundary holonomy, top
  order-sensitive squares, coverage / exactness boundary, and next action cues.
  It is not PR / diff evolution analysis and does not prove global lawfulness or
  safety.
- `archMapStoreRefs` records the packet's canonical history substrate:
  `archmap-delta-v0`, `archmap-commit-v0`, `archmap-snapshot-v0`, and
  `archmap-index-v0`. It also records raw-diff and compaction boundaries so
  review readers can distinguish change-local evidence from snapshot-level
  current-state evidence.
- `monodromyReadingFamily` and `boundaryHolonomyReadingFamily` are schema
  foundation surfaces. They carry selected axes, distance kind, weight policy,
  coverage policy, and the ArchMapStore ref set used by later operation-square,
  axis-wise defect, AMI, boundary residual, and feature-extension attribution
  readings. They define the shared measurement policy boundary while concrete
  valuation fields live in the corresponding reading records.
- `operationSquareCandidates` enumerates supplied or inferred operation pairs as
  path pairs `p = g . f` and `q = f . g`. Inferred candidates are review cues
  derived from shared Atom support, state / effect / contract / semantic /
  authority / runtime / projection evidence; they are not operation truth.
- `pathContinuationTraces` records the selected continuation trace for each
  candidate path and axis family: static, contract, semantic, state, effect,
  authority, runtime, and projection. Unmeasured axes are retained as
  `missingRefs` and must not be read as zero defect.
- `axisWiseMonodromyDefects` records `mu_x(sigma)` for each selected operation
  square and axis. Each defect carries distance kind, measured support,
  witness refs, source / observation / missing refs, coverage boundary,
  exactness assumption status, zero-reflection assumptions, and cancellation
  boundary.
- `amiAggregateReadings` records `AMI_X(A)` as a bounded weighted aggregate for
  review prioritization. It reports selected square family, selected axis
  family, weight policy, top contributors, zero-reflection assumptions, and the
  aggregate-to-local reading boundary. It is not a single architecture quality
  score, merge gate, or global path-flatness theorem.
- `nonzeroMonodromyWitnesses` lifts positive measured `mu_x(sigma)` defects
  into reviewer-readable witness records. Each witness records operation pair,
  path pair, axis, defect value, compared trace summary, affected Atom /
  observation refs, law refs, signature axis refs, suggested filler / lifting /
  boundary evidence, review focus cues, coverage boundary, and machine-readable
  non-conclusions. It does not assert repair safety or merge safety.
- `featureBoundaryResidualReadings` records `Boundary(A, f)` review readings for
  feature-extension boundaries. Each reading separates core-local,
  feature-local, and mixed boundary support, exposes `Hol_static`,
  `Hol_contract`, `Hol_semantic`, `Hol_state`, `Hol_effect`, `Hol_authority`,
  `Hol_runtime`, and `Hol_projection` residual axes, and keeps support
  separation, coverage, exactness, attribution policy, evidence boundary, and
  machine-readable non-conclusions. It does not claim an unconditional
  `Ob(B) = Ob(A) + Ob(f) + Hol(Boundary(A,f))` theorem or decide feature
  safety.
- `featureExtensionDiagnosisReadings` classifies feature-extension witnesses
  with non-disjoint multi-label attribution. The seven labels are inherited core
  obstruction, feature-local obstruction, boundary holonomy, lifting failure,
  filling failure, complexity transfer, and residual coverage gap. A single
  witness can carry multiple labels; the classifier records this as review
  attribution, not as a mutually disjoint decomposition, and keeps the ArchSig /
  FieldSig boundary explicit.
- axis-forgetting risk records when a coarse observation projection has
  forgotten selected axes or collapsed mixed-axis support. It blocks
  `ZeroReflecting` and `ObstructionReflecting` readings unless explicit axis
  preservation, witness completeness, and selected LawPolicy coverage are
  supplied.
- signature trajectory homotopy refutation records trajectory disagreement
  separately from endpoint delta. It can refute only a selected
  signature-preserving homotopy; it does not claim operation commutativity,
  global path inequivalence, or future repository trajectory.
- bridge split obstruction transfer connects split readiness, bridge-edge
  support, interaction obstruction refs, and required boundary operations. It
  states that filler / lifting / boundary-operation evidence is required before
  reading a split as obstruction removal.
- AAT structural state readings expose representation strength, local curvature
  diagrams, three-layer flatness, observation projection loss, state transition
  algebra, operation / invariant Galois-style correspondence, and split
  readiness. These readings describe the current architecture state; PR / diff
  projection remains a FieldSig responsibility.
- representation strength records `ZeroPreserving`, `ZeroReflecting`,
  `ObstructionPreserving`, and `ObstructionReflecting` status for analytic,
  spectral, matrix, curvature, and aggregate readings. Aggregate zero safety is
  represented as a strength boundary: zero aggregates only reflect local zero
  under the recorded assumptions and cancellation constraints.
- `structuralReadingReviewSurface` connects the AAT structural reading families
  into one review guide. It states that ArchSig reads current architecture
  state, not just violations, and lists the review focus for representation
  blockers, curvature, flatness, projection loss, state/effect algebra,
  operation/invariant constraints, and split readiness.
- `currentStateEvolutionBoundary` records the product boundary: ArchSig computes
  current AAT structural state from `ArchMap + LawPolicy` and future
  change-local structural cues from ArchMapStore deltas / commits. FieldSig
  studies PR / diff / change-vector evolution over ArchMapStore and serialized
  `archsig-analysis-packet-v0` chains. The packet must not be read as forecast
  correctness, causal truth, raw-diff semantic truth, or raw-ArchMap forecast
  truth.
- analytic representations include weighted adjacency, walk count, reachable
  cone size, nilpotence boundary, selected subgraph spectrum, propagation depth,
  spectral radius, curvature valuation, state algebra boundary, and
  zero-reflecting aggregate boundary
- emits repair operation candidates with preserved invariants, preconditions,
  transfer risks, evidence boundaries, and non-conclusions
- emits operation deltas and path / homotopy / diagram readings for repair
  planning and review focus
- fills child-level `missingEvidence` / `excludedReadings` from ArchMap
  observation gaps, interpretation-profile coverage and exactness assumptions, selected
  witness rules, and repair-candidate evidence limits

## Downstream Handoff

`analyze` treats the analysis packet as the source artifact and
emits only ArchMap validation, LawPolicy validation, the analysis packet, packet
validation, and the LLM interpretation packet. Pre-Atom projections and review
surfaces are not current ArchSig CLI surface or compatibility commands.

`pr-review` and `codebase-inspection` are separate report surfaces:

- `archsig-pr-review-report-v1` reads base `archmap-observation-map-v0`,
  PR-local `archmap-delta-v0`, and required `law-policy-v0`. No LawPolicy, no
  ArchSig judgement. Raw diff, `archmap-commit-v0`, and base/head analysis
  packets are not PR-review inputs.
- `archsig-codebase-inspection-report-v0` reads latest
  `archmap-snapshot-v0`, `archmap-index-v0`, optional recent deltas, optional
  LawPolicy provenance, and one packet. It is current-state architecture health
  telemetry.

Both reports preserve measured witnesses, coverage / exactness boundary,
missing evidence, and non-conclusions. Neither report is a merge approval,
global lawfulness proof, raw-diff semantic parser, forecast, governance,
calibration, or longitudinal FieldSig analysis.

FieldSig handoff projects child-level `missingEvidence` / `excludedReadings`
as unknown remainder and evidence-boundary refs instead of rounding them to
absence, measured zero, forecast truth, or repair safety.
