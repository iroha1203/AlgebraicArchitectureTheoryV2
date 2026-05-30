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
  boundaries, and an LLM interpretation packet.
```

## Responsibility

The packet owns structured analysis results. It is not a theorem proof and not
a single architecture quality score.

The implemented schema records:

- `interpretationProfileRef`
- `selectedLawPolicyRef`
- `archMapRef`
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
readings, law-relative obstruction links, signature / flatness references,
repair candidate guardrails, LLM interpretation notes, evidence boundary, and
required non-conclusions.
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
  current AAT structural state from `ArchMap + LawPolicy`; FieldSig studies
  PR / diff / change-vector evolution over the serialized
  `archsig-analysis-packet-v0`. The packet must not be read as PR diff
  analysis, forecast correctness, causal truth, or raw-ArchMap forecast truth.
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

FieldSig handoff projects child-level `missingEvidence` / `excludedReadings`
as unknown remainder and evidence-boundary refs instead of rounding them to
absence, measured zero, forecast truth, or repair safety.
