# ArchSig Analysis Packet

For `archmap/v1` and `law-policy/v1`, ArchSig now uses a typed evaluator
artifact chain:

```text
ArchMap v1
  -> normalized-archmap/v1
  -> typed-evaluator-results/v1
  -> archsig-analysis-packet/v1
  -> archsig-analysis-summary/v1
  -> archsig-atom-viewer-data-v1
```

The v1 packet / summary / viewer path is computed from normalized atoms,
generated molecule candidates, LawPolicy-selected evaluator manifests, typed
evaluator statuses, support atom refs, support molecule refs, basis refs, and
detail refs. `blocked`, `unknown`, and `unmeasured` statuses remain non-zero
blocking states; they are not collapsed into measured zero.

Current v1 also exposes `removed-v0-field-replacement-registry@1`. The raw
packet and typed evaluator artifact carry:

- `replacementRegistry`: registry manifests for `semantic.interpretation@1`,
  `projection.reading@1`, `operation-square.reading@1`,
  `missing-evidence.reading@1`, `concern.boundary@1`, and
  `non-conclusion.boundary@1`.
- `replacementEvaluatorResults`: replacement readings derived from normalized
  atoms, generated molecule candidates, selected evaluator requirements, and
  registry manifests.
- `replacementEvaluatorResultsById`: id-keyed lookup surface used by
  `typedOutputPacketRefs`; every manifest ref must resolve as a packet JSON
  pointer.
- `replacementRegistryResolution`: manifest / resolved / blocked /
  non-diagnostic replacement counts and the removed v0 fields covered by the
  registry.

Replacement readings are packet support refs. They do not re-enable removed v0
ArchMap fields as input, and they do not turn concern notes or non-conclusion
prose into diagnostic findings.
FieldSig handoff can still validate the v1 raw packet, but FieldSig does not
yet preserve replacement reading refs as its own downstream evidence surface;
that integration remains tracked separately.

Current v1 also restores the first generated packet refs as derived output:

- `generatedLawInputs`: one row per selected typed evaluator result. Each row
  points back to `/typedEvaluatorResults/{i}`, registry basis refs, support atom
  refs, support molecule refs, and the derived signature axis id.
- `signatureAxes`: one row per selected typed evaluator result. Each axis
  points to its generated law input and the corresponding
  `/architectureDistance/signatureDistanceReadings/{i}` row.
- `generatedObstructions`: rows for measured violations and blocked /
  unmeasured evaluator results. A blocked row is a missing-evidence obstruction
  candidate, not a measured violation.
- `generatedRepairTargets`: bounded review targets generated from
  `generatedObstructions`. They name review / evidence-collection targets; they
  do not prove a repair operation.
- `generatedPacketRefs`: top-level JSON pointers for the generated surfaces so
  packet validation and the detail index can resolve v1 generated surfaces
  without reading v0 LawPolicy DSL fields. FieldSig can already accept the v1
  packet as bounded current structural state; preserving these generated refs as
  first-class downstream evidence remains tracked in the FieldSig handoff issue.

Current v1 also emits the ACTS / ArchitectureSpectrumReport family as derived
output:

- `curvatureSupportReadings`: selected-axis support rows derived from typed
  evaluator status and normalized support refs. `measuredPass` becomes bounded
  measured zero, `measuredViolation` becomes bounded nonzero curvature, and
  `blocked` / `unknown` / `unmeasured` become coverage gaps.
- `curvatureTransferReadings`: finite selected-support transfer rows. Recurrent
  obstruction entries are current-state review signals, not empirical
  amplification or future incident predictions.
- `spectralAnalysisReadings`, `spectralModeReadings`, and
  `spectralDrilldownReadings`: compact spectrum surfaces over emitted v1
  curvature support rows.
- `architectureSpectrumReport`: hotspots, witness clusters, recurrent
  obstruction readings, coverage gaps, measured boundary, review focus, and
  non-conclusions. Spectrum zero is bounded to selected measured support and
  does not imply global lawfulness or flatness.
- `pathHomotopyDiagramReadings`, `homotopyHolonomyReadings`,
  `stokesStyleReadings`, and `homotopyDistanceReadings`: bounded homotopy /
  holonomy / Stokes-style output over normalized relations and explicit
  molecule candidates. Generated molecule candidates are read as measured
  fillers; blocked molecule candidates become missing filler evidence and do
  not become zero holonomy.
- `architectureHomotopyReport`: filled loops, unfilled loops, nonzero holonomy
  loops, local curvature cells, missing filler evidence, architectural hole
  readings, aggregate review counters, coverage gaps, review focus, and
  non-conclusions.
- `representationMetricReadings`, `localCurvatureDiagramReadings`,
  `threeLayerFlatnessReadings`, `observationProjectionReadings`,
  `stateTransitionAlgebraReadings`, `effectRelationAlgebraReadings`,
  `synthesisBlockageReadings`, `operationPreconditionReadinessReadings`, and
  `pathMultiplicityLossReadings`: compact structural review readings derived
  from normalized atoms / molecules, typed evaluator refs, architecture
  distance refs, spectrum / homotopy refs, generated obstructions, generated
  repair targets, and coverage gaps.
- `structuralReadingReviewSurface`: current-state review surface connecting the
  structural reading refs. Blocked rows remain blockers / review queues; they
  are not measured zero, repair safety, synthesis certificates, or global
  quality scores.

The v1 path does not read v0 helper fields such as `semanticObservations`,
`projectionInfo`, `operationSquareEvidence`, `concernHints`, or
`observationGaps` as positive readings. It also does not read v0
`spectrumMeasurementProfile` or `homotopyMeasurementProfile` as measurement
recipes, call Lean, or require a Lean proof object. `--emit-raw-artifacts`
writes v1 raw packet, detail-index, and LLM interpretation artifacts; without
it, summary / viewer / manifest remain the primary reading surface.

`archsig-analysis-packet-v0` is the legacy ArchSig output artifact for
`archmap-observation-map-v0` / `law-policy-v0`.
It reads a source-grounded ArchMap together with one selected interpretation
profile and records AAT-based, bounded analysis for LLM and human review.

```text
ArchMap
  records law-independent Atom observations.

InterpretationProfile
  selects the LawUniverse, witness rules, signature axes, coverage, exactness,
  optional spectrum measurement profile, optional homotopy path / filler /
  loop measurement profile, and the selected Part IV distance profile boundary.
  In the legacy path, the JSON artifact is named law-policy-v0.

ArchSig Analysis Packet
  records AAT concept surfaces, architecture state, design pressure, change
  impact, molecule readings, obstruction circuits, signature axes, analytic
  representations, spectral analysis readings, design principle readings,
  spectral mode readings, spectral drilldown readings,
  Part IV distance foundation rows,
  transfer bridge readings, Atom support / compatibility readings,
  LawUniverse coverage, feature extension formula axes, operation calculus law
  axes, path signature trajectories, homotopy / operation-order sensitivity,
  diagram fillability, observation projection fidelity, Atom origin closure
  debt, effect relation algebra, synthesis blockage, operation precondition
  readiness, path multiplicity loss, Homotopy / Holonomy / Stokes readings,
  ArchitectureHomotopyReport, bounded judgements, repair operation candidates,
  operation deltas, path / homotopy / diagram readings, child-level evidence
  boundaries, ArchMapStore refs, Part IV Atom distance readings, monodromy /
  boundary holonomy reading family policy surfaces, and an LLM interpretation
  packet.
```

## Responsibility

The packet owns structured analysis results. The user-facing summary is a
compact reading artifact: for the supplied ArchMap and selected LawPolicy,
ArchSig states the measured verdict, quality measurement counts, dominant
findings, and action queue before showing metadata boundaries. Summary entries
do not reprint packet evidence arrays. They point back to packet detail through
`detailRefs`, `packetRefs`, and `detailIndex`.

For product workflow, ArchMap authoring is complete-first. The intended entry
experience is not "create a thin map and ask the user to grow it." An LLM-native
ArchMap authoring pass should collect source inventory, atoms, explicit
molecule candidates, path candidates, endpoint / continuation evidence, filler
evidence, non-fillability witnesses, and source-backed semantic atoms before
presenting ArchSig results. `archsig-analysis-summary.json` and
`llm-interpretation-packet` then serve two readers:

- user-facing diagnosis: measured verdict, quality counts, distance insights,
  distance diagnosis, hotspots, holes, and action queue first
- authoring feedback: coverage blockers, unfilled loops, missing filler
  evidence, and unmeasured spectrum support become a repair queue before final
  handoff

Only evidence that is truly private, unavailable, or out of scope should remain
as residual `blockedByCoverageGap` in a complete-first handoff.

`archsig-analysis-summary.json` is the preferred reading surface for humans and LLM agents.
It is designed to be read whole without jq slicing. It exposes:

- `verdict`: selected-policy flatness, quality state, primary conclusion,
  actionability, and reading mode.
- `qualityMeasurement`: nonzero axis count, hotspot count, recurrent
  obstruction count, architectural hole count, nonzero holonomy count, and
  coverage gap count, with compact Part IV distance-reading counts.
- `distanceInsights`: engineer-facing architecture-distance reading. It reports
  architectural center, change-sensitive areas, selected policy-obstruction
  state, blocked evidence, recommended source / atom / molecule refs, and
  `comparisonNeeded` for baseline-dependent trend or improvement claims.
- `distanceDiagnosis`: Part IV diagnostic-distance first surface. It reports
  the distance verdict, measured movement, unmeasured axes, compact moved atom
  / axis rows, safe margin, repair distance, curvature / homotopy distance,
  representation metrics, and packet detail refs. Blocked or unmeasured
  distance is preserved as blocked / unmeasured, not collapsed to measured
  zero. `unmeasuredAxes` is derived after Part IV evaluator execution from the
  synchronized `DiagnosticScope`; a signature axis with measured or zero
  `axisDistance` must not remain in this summary-level unmeasured list.
- `measurementStatusSummary`: compact measured / partial / proxy /
  unmeasured / blocked / `schemaFoundationOnly` counts. This is the first
  summary-level guardrail against reading proxy or schema-only rows as measured
  AAT analysis.
- `trendDiagnosis`: the repository-wide tendency view. It keeps compact counts
  and refs for concentrated law-axis pressure, spectrum hotspots, recurrent
  obstruction support, bridge pressure, path multiplicity loss,
  projection fidelity loss, and Atom origin closure debt. It also carries
  `trendInsights`, a compact second-order diagnosis surface that intersects
  packet readings instead of recounting them: cross-axis co-occurrence,
  operation freedom loss, selected path continuation defects, boundary
  residual localization, and repair transfer risk.
- `reviewSupport`: the review queue view. It keeps the action queue count,
  compact blocker refs, coverage gap refs, and packet refs for evidence lookup
  without turning review support into automatic repair safety or merge
  approval.
- `dominantFindings`: compact nonzero axes, hotspots, recurrent pressure,
  architectural holes, nonzero holonomy, bridge pressure, and
  compact AAT observation-axis pressure.
- `richDominantFindings`: current v1 compact packet refs for spectrum hotspots,
  recurrent obstructions, architectural holes, nonzero holonomy, and structural
  review families. It is a ref surface, not a copy of raw packet arrays.
- `richPacketRefs`: packet refs grouped for distance diagnosis, spectrum,
  homotopy, and structural reading lookup. These refs are the bridge from the
  first summary read to optional raw artifacts.
- `richReadingGuide`: conclusion-first reading order and detail policy for LLMs
  and reviewers. It explicitly tells the reader to inspect packet refs before
  converting a compact queue item into a source-level finding.
- `actionQueue`: the full prioritized queue for hotspots, unfilled loops,
  nonzero holonomy loops, nonzero signature axes, workflow pressure, bridge
  pressure, projection fidelity loss, Atom origin closure debt, effect relation
  pressure, synthesis blockage, operation precondition readiness, and path
  multiplicity loss. Each entry stays compact and carries `detailRefs` instead
  of nested evidence arrays.
- `axisSummary`, `aatObservationAxisSummary`, `architecturalHoleSummary`,
  `bridgeSummary`, and `coverageGapSummary`: counts plus compact examples or
  refs for the major reading surfaces.
- `detailIndex`: packet sections and `packet:<json-pointer>` refs for looking
  up the full evidence in `archsig-analysis-packet.json`.
- `measurementBasis`: ArchMap / LawPolicy refs, validation results, coverage
  gaps, and measured boundaries.
- `metadata`: non-conclusions and excluded readings preserved after the main
  diagnosis.

The full `archsig-analysis-packet.json` remains the evidence store. Raw
`supportRefs`, `sourceRefs`, witness clusters, spectral rows, homotopy
aggregate readings, and measurement-expansion detail belong in the packet, not
in `archsig-analysis-summary.json`.

`archsig-atom-viewer-data.json` keeps visual layout distance separate from
Part IV diagnostic distance. `viewerDistanceInputs` support Atom Viewer
placement only. Diagnostic distance overlays are bounded projections of packet
distance readings and are exposed through `diagnosticDistanceReadings`,
`diagnosticDistanceBoundary`, omitted counts, and the report pane
`distanceInsights` / `distanceDiagnosis` sections. The report pane reads the
same compact `distanceInsights` and `distanceDiagnosis` objects as
`archsig-analysis-summary.json`, so measured or zero signature axes and
engineer-facing distance readings cannot drift across summary, viewer, and LLM
surfaces. The viewer should help a human inspect where the diagnostic readings
point; it must not reinterpret visual layout distance as an ArchSig metric.

Current v1 viewer data also mirrors `richPacketRefs`, `richDominantFindings`,
`richReadingGuide`, and `actionQueue` into `analysisOverlays` / `reportPane`.
It records omitted raw packet array counts so that the viewer remains a bounded
projection rather than a second analysis engine.

`llmInterpretationPacket.distanceInsightsSummary` and
`llmInterpretationPacket.distanceDiagnosisSummary` are the compact LLM notes for
distance-first reading. They tell an agent to read summary distance insights and
diagnosis before raw Part IV rows, record measured / blocked / unmeasured
status, and record the evaluator-synchronized `DiagnosticScope` measured /
unmeasured / blocker counts. Operation and curvature axes can remain unmeasured
when a partial measured contribution still has evidence blockers. They keep
non-claims bounded to the selected ArchMap + LawPolicy evidence contract.

Current v1 `llm-interpretation-packet.json` also carries `richPacketRefs`,
`readingGuidance`, and `actionQueueSummary`, so an LLM can start from the same
compact packet refs as summary / viewer without treating raw packet retention as
mandatory.

`trendInsights` is intentionally short. Each item reports a bounded claim, why
the claim is nontrivial, a small measurement summary, and packet refs. The full
evidence remains in the packet. The insights are concrete ArchSig measurements
because they cross-check existing packet readings:

- `crossAxisCooccurrence` normalizes packet support refs and measures when
  law-axis, workflow, spectrum, homotopy, and bridge readings concentrate on
  the same support.
- `operationFreedomLoss` reads the operation / invariant Galois surface
  together with precondition readiness and transfer evidence.
- `pathContinuationDefect` reads axis-wise monodromy defects instead of
  treating same-endpoint paths as homotopy-equivalent.
- `boundaryResidualLocalization` reads feature-boundary residuals by separating
  core-local, feature-local, boundary, residual-axis, and coverage-blocked
  support.
- `repairTransferRisk` pairs decreased selected axes with transferred
  obstruction, bridge-split, and precondition evidence.

`ArchitectureHomotopyReport` is a bounded v1 derived output surface. It
reads candidate path pairs, loops, fillers, architectural holes, selected-axis
holonomy, and Stokes-style review queues from normalized ArchMap v1 atoms,
explicit molecule candidates, typed evaluator status, and packet coverage gaps.
It does not read the legacy v0 `homotopyMeasurementProfile` as a measurement
recipe. Nonzero holonomy is emitted only when the selected typed evaluator
surface exposes measured nonzero curvature support for the explicit molecule;
semantic / runtime axis differences without that support remain unmeasured
coverage gaps. User-facing summaries should report measured unfilled loops and
nonzero holonomy as architectural holes / review queues first; path truth,
global homology, future safety, and repair-safety boundaries belong in packet
detail and metadata.

Spectrum and Homotopy surfaces expose `measurementStatus` and
`readingBoundary` so a reader can distinguish measured rows, bounded proxy
operators, unmeasured candidates, and readings blocked by coverage gaps. A
zero reading is meaningful only inside the recorded zero-reflection
assumptions, obstruction-reflection assumptions, coverage requirements, and
witness-completeness boundary.

`part4DistanceFoundation` is the packet-level Distance Engine contract. It
records `DistanceProfile`, `DiagnosticScope`, `DistanceValue` status rows, and
anti-proxy guardrails before any individual Part IV evaluator is allowed to
emit a measured distance. The foundation may expose unmeasured distance
families, but those rows are blockers for downstream evaluator work; they are
not placeholders for hidden zeroes, fixed fixture values, concern-only scores,
or viewer layout distances. The builder initializes `DiagnosticScope` from
ArchMap and LawPolicy coverage, then synchronizes it from evaluator readings
before output.

`atomDistanceReadings[]` is the Part IV Atom geometry evaluator surface. Each
row compares a source / target Atom pair in molecule scope and reports
`fiberDistance`, `carrierDistance`, `valenceDistance`,
`semanticAnchorDistance`, and an `atomLayoutDistanceBundle`. Fiber, carrier,
and valence are measured from ArchMap atom fields, carrier refs, source refs,
and derived affordance sets. Semantic anchor distance is measured only when
both atoms have semantic observation support; otherwise it remains unmeasured
with blocker refs. `viewerDistanceInputRefs` may be retained for visual
projection lookup, but those refs do not become the diagnostic distance.

`configurationDistanceReadings[]` is the Part IV configuration geometry
evaluator surface. Rows cover all observed molecule-local Atom pairs plus a
bounded cross-context diagnostic sample for disconnected / unreachable review;
they are not a complete all-pairs architecture metric. Each row records the
typed configuration hypergraph evidence used for the reading. Hyperedges are
extracted from explicit ArchMap evidence such as molecule membership, shared
subject/object refs, relation endpoints, contract attachment, semantic
interpretation, operation-square evidence, boundary/effect surfaces, concern
surfaces, and source-backed co-observation. `configurationIndexedDistance` is
the shortest path length in that typed hypergraph. `contextDistance` is the
molecule-context Jaccard distance. `smallMoleculeWeightMilli` records the Part
IV small-molecule overlap weight. Observation gaps and missing relations block
the configuration bundle; they are not filled in as measured zero or inferred
architecture completeness.

`signatureDistanceReadings[]` is the Part IV signature geometry evaluator
surface. It aggregates selected LawPolicy signature axes into axis-wise
`rhoI`, `axisDistance`, measured / unmeasured / incomparable axis partitions,
`totalMeasuredDistance`, `safeRegionMargin`, `pathDrift`,
`endpointDistance`, and `hiddenExcursionStatus`. Existing `signatureAxes[]`
remain the law-relative axis reading surface, but each axis must point to the
first-class signature distance reading through `signatureDistanceReadingRefs`.
Coverage gaps block safe-region and drift conclusions; a zero axis count alone
is not a global lawfulness or flatness claim.

`operationDistanceReadings[]` is the Part IV operation geometry evaluator
surface. Each row links an `operationDelta` and optional repair candidate to
`operationCost`, `targetDistanceDecrease`, `protectedAxisMovement`,
`distanceToSelectedFlat`, and `sideEffectBound`. `repairOperationCandidates[]`
and `operationDeltas[]` carry `part4DistanceRefs` back to these readings.
Target decrease and protected-axis movement are separate fields, and transfer
risk / unmeasured protected axes block side-effect bounds rather than becoming
repair-safety claims.

`obstructionMeasureReadings[]` and `curvatureMassReadings[]` are the Part IV
obstruction / curvature evaluator surfaces. Obstruction measure rows are built
from selected LawPolicy witness support rows and keep missing witnesses as
blockers, not zero curvature. Curvature mass rows aggregate those selected
measure rows and separate before-operation mass, after-operation mass,
target-axis decrease, protected-axis movement, and curvature transport distance.
`curvatureSupportReadings[]`, `curvatureTransferReadings[]`, transfer edges,
and `architectureSpectrumReport` retain Part IV distance refs back to these
rows.

`homotopyDistanceReadings[]` is the Part IV homotopy / filling evaluator
surface. Each row links a selected loop and path pair to `homotopyDistance`,
`fillingCost`, `observationGapLowerBound`, and `selectedDehnArea`. Missing
filler evidence blocks filling cost and selected Dehn-style area rather than
becoming zero cost. Loop, filler, architectural-hole, holonomy, Stokes-style,
and `ArchitectureHomotopyReport` surfaces retain `part4DistanceRefs`.

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
- `part4DistanceFoundation`
- `atomDistanceReadings`
- `configurationDistanceReadings`
- `signatureDistanceReadings`
- `operationDistanceReadings`
- `obstructionMeasureReadings`
- `curvatureMassReadings`
- `obstructionCircuits`
- `signatureAxes`
- `analyticRepresentations`
- `couplingCohesionReadings`
- `spectralAnalysisReadings`
- `spectralModeReadings`
- `spectralDrilldownReadings`
- `curvatureSupportReadings`
- `curvatureTransferReadings`
- `architectureSpectrumReport`
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
- `observationProjectionFidelityReadings`
- `atomOriginClosureDebtReadings`
- `effectRelationAlgebraReadings`
- `synthesisBlockageReadings`
- `operationPreconditionReadinessReadings`
- `pathMultiplicityLossReadings`
- `signatureTrajectoryHomotopyRefutationReadings`
- `bridgeSplitObstructionTransferReadings`
- `homotopyComplexSummary`
- `pathPairCandidates`
- `loopCandidates`
- `fillerCandidateReadings`
- `architecturalHoleReadings`
- `homotopyHolonomyReadings`
- `stokesStyleReadings`
- `architectureHomotopyReport`
- `homotopyDistanceReadings`
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
- `representationMetricReadings`
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

`stateTransitionAlgebraReadings[]` is not an Atom-family presence summary.
It now carries `transitionRelationInputs[]` rows with from/event/to,
operation, invariant, runtime/trace, and source refs, plus `lawEvaluations[]`
for transition relation, commutativity, idempotency, replay safety, ordering
preservation, and invariant preservation. Missing runtime or test evidence is
kept as `blocked`, not interpreted as measured zero.

`effectRelationAlgebraReadings[]` similarly exposes `relationInputs[]` and
`relationEvaluations[]` for ordering preservation, replay safety, idempotency,
compensation availability, and authority requirements. This keeps effect
ordering / replay / compensation separate from general state transition
pressure and from raw effect Atom presence.
- `boundedJudgements`
- `llmInterpretationPacket`
- `evidenceBoundary`
- `interpretationNotesForLLM`
- `excludedReadings`
- `nonConclusions`

## Validation Boundary

Packet validation has separate JSON surface, measurement-depth, and
proxy-regression checks. Surface checks confirm the packet contract and
cross-references; measurement-depth checks require evaluator input refs,
distance value provenance, witness rule / law / axis alignment, and coverage
blockers for measured or blocked readings, require Part IV rows to stay tied
to the selected `DistanceProfile` / `DiagnosticScope`, and reject hard-coded
fixture markers as measured provenance; proxy-regression checks reject
`schemaFoundationOnly` or bounded proxy rows when they masquerade as measured analysis. Packet
validation checks identity, ArchMap / interpretation profile
references, AAT concept coverage, bounded judgement statuses, analytic axes,
spectral analysis readings, spectral mode readings,
design principle readings, spectral drilldown readings, curvature support
readings, curvature transfer readings, ArchitectureSpectrumReport, transfer
bridge readings and bridge-edge source refs, v0.3.0 measurement expansion
readings, AAT observation-axis readings, homotopy complex summaries, path pair
candidates, loop candidates, filler candidate readings,
architectural hole readings, homotopy holonomy readings, Stokes-style readings,
ArchitectureHomotopyReport, AAT structural state readings, ArchMapStore delta /
commit / snapshot / index refs, operation square candidates, axis-wise path
continuation traces, `measurementStatus` and `readingBoundary` fields for ACTS
and Homotopy measurement records, Part IV distance foundation rows, Part IV Atom
distance readings, monodromy / boundary holonomy reading family
policy surfaces, law-relative obstruction links, signature / flatness
references, repair candidate guardrails, selected-axis continuation defect refs
for nonzero homotopy holonomy, LLM interpretation notes, evidence boundary,
and required non-conclusions.
Validation also checks that `part4DistanceFoundation.diagnosticScope` is
post-evaluator state: `measuredAxisRefs` and `unmeasuredAxisRefs` must be
disjoint, measured or zero signature-distance axes must appear in
`measuredAxisRefs`, non-measured signature axes must stay in
`unmeasuredAxisRefs`, and closed implementation Issue placeholder refs such as
`issue:#...` or `unmeasuredAxis:<axis>` blockers for already measured
signature-distance axes must not remain as final `DiagnosticScope.blockerRefs`.
Each obstruction circuit, signature axis reading, and repair operation candidate
must carry its own `missingEvidence` and `excludedReadings`. Packet-level
`excludedReadings` does not stand in for child-record evidence boundaries.

Validation metadata records that validation does not imply:

- Lean theorem proof
- global architecture truth
- source extraction completeness
- universal quality score
- global flatness proof
- automatic repair safety
- source extraction completeness
- merge approval
- LLM output as architecture truth

## Legacy Fixture

- `tools/archsig/tests/fixtures/minimal/archsig_analysis_packet.json`
- `tools/archsig/tests/fixtures/coupon_rounding/archsig_analysis_packet.json`
- `tools/archsig/tests/fixtures/homotopy_report/archsig_analysis_packet.json`
- `tools/archsig/tests/fixtures/complete_archmap_acceptance/`

These fixtures are locked against the legacy static Rust builder and the schema
catalog records both `archsig-analysis-packet-v0` and
`archsig-analysis-packet-validation-report-v0`.

`complete_archmap_acceptance` is a sanitized large-repo class fixture. It
validates the complete-first workflow without private identifiers: ArchMap
validation, LawPolicy validation, and packet validation pass; spectrum emits
hotspots / recurrent pressure; homotopy emits filled loops, nonzero holonomy,
one targeted unfilled loop, and Stokes-style local curvature cells.

## Legacy Builder

`build_archsig_analysis_packet` deterministically builds a packet from one
`ArchMapDocumentV0` and one `LawPolicyDocumentV0`.

The builder:

- evaluates selected interpretation-profile witness rules over ArchMap atom and semantic observations
- uses `concernHints` only as auxiliary evidence
- constructs obstruction circuits only from family-complete witness rules whose
  required atom families and `moleculePatternRefs` are observed under the
  selected LawPolicy
- values required signature axes from constructed obstruction circuits; a
  nonzero signature axis must not be emitted from concern hints, blocked
  witnesses, incomplete molecule patterns, or policy text alone
- preserves observation gaps as flatness blockers, not measured zero
- emits AAT concept surfaces for Atom, Configuration, ArchitectureObject,
  Invariant, LawUniverse, ObstructionCircuit, ArchitectureSignature, Operation,
  Path, Homotopy, Diagram, and AnalyticRepresentation
- emits architecture state, design pressure, change impact, bounded judgements,
  LLM interpretation, analytic representation, semantic coupling/cohesion,
  spectral analysis readings, and design principle
  readings. Design principles are principle-specific witness readings with
  `witnessRuleRef`, `witnessStatus`, witness evidence refs, source refs, and
  per-principle next actions; they are not global obstruction summaries or
  static lint rules.
- spectral analysis readings build finite matrix-like AAT representations for
  molecule atom/family overlap coupling, obstruction-to-axis curvature, and
  operation-to-signature delta. They record
  matrix shape, entry rule, bounded values, dominant components, coverage
  boundary, and zero-reflecting boundary. They are spectral proxies for review,
  not exact eigenvalue theorems or quality scores.
- spectral mode readings lift spectral analysis into bounded mode proxies:
  dominant/residual gap, localization, matrix density, decomposability, and
  repair perturbation. They are review modes, not exact eigenvector theorems.
- spectral drilldown readings explain spectral modes using dominant atom-family
  composition, high-overlap molecule pair rankings, and positive / negative /
  neutral repair axis deltas.
- curvature support readings use the optional LawPolicy
  `spectrumMeasurementProfile` to report selected-axis / measured-witness
  support rows, bounded curvature values, weights, top modes, witness clusters,
  coverage boundaries, exactness refs, and non-conclusions. Each support row
  records the local curvature reference `kappa(D)`, diagram reference, lhs/rhs
  observation refs, distance kind and inputs, soundness boundary, and coverage
  status. Missing support is `blockedByCoverageGap`, not zero.
- obstruction measure and curvature mass readings integrate the support and
  transfer surfaces with Part IV `DistanceValue` provenance. `Omega_U(A)` is
  emitted as selected witness-backed measure rows, `curv_mass_U(A)` is a
  selected-scope aggregate, and unmeasured axes block mass / transport instead
  of becoming zero curvature. Curvature transport keeps target decrease,
  protected-axis movement, transferred obstruction refs, and complexity-transfer
  distance refs separate.
- curvature transfer readings build a finite nonnegative transfer operator over
  measured curvature support rows. Transfer entries are backed by selected
  relation-graph evidence or shared selected-axis support, and report row/column
  support refs, sparse matrix entries, source-backed transfer edges, a
  `rho(T^kappa)` reading, and self-loop or multi-row recurrent obstruction modes
  only as bounded current-state diagnostics. They do not conclude future
  incidents, empirical cost increase, amplification, repair safety, or FieldSig
  forecast truth.
- `architectureSpectrumReport` summarizes the ACTS surface for human and LLM
  review: top hotspots, top bounded mode data, witness clusters, recurrent
  obstruction entries, coverage gaps, measured boundary, and recommended next
  actions. Top modes carry operator component refs, localization, source refs,
  and a recommended review target; witness clusters carry evidence-backed basis
  refs. It is the current-state architecture quality measurement surface for
  selected-axis pressure.
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
- `lawUniverseCoverageReadings[]` separates required law coverage, witness
  family coverage, signature-axis coverage, coverage-requirement status, and
  exactness-assumption status. The `lawWitnessAxisEvaluations[]` rows are the
  machine-readable alignment evaluator: they record required/observed/missing
  witness refs, required/observed/missing axis refs, coverage requirement refs,
  exactness assumption refs, source-backed evidence refs, blockers, and
  separate coverage / exactness statuses. Atom family presence alone is not a
  covered law claim.
- `atomCompatibilityReadings[]` evaluates same subject / predicate slots with a
  payload comparison policy. It compares object refs, observation status,
  confidence, uncertainty, source refs, and semantic observations that reference
  the conflicting atom refs. A no-conflict status is bounded to observed slots;
  it is not global Atom ontology consistency.
- Homotopy / Holonomy / Stokes readings add current-state coordinates for
  `homotopyComplexSummary`, `pathPairCandidates`, `loopCandidates`,
  `fillerCandidateReadings`, `architecturalHoleReadings`,
  `homotopyHolonomyReadings`, `stokesStyleReadings`, and
  `architectureHomotopyReport`. Path-pair and operation-square candidates carry
  first-class operation sequences, endpoint object refs, and generator
  candidate refs. Holonomy value is computed from source-backed continuation
  comparison inputs: exact path-rule semantic observations, supplied p/q
  continuation traces, axis-wise `mu_x` defects, filler evidence, and explicit
  missing filler refs. Path-pair id / path ref string containment is not the
  value calculator. Continuation traces carry step refs and selected-axis
  continuation states. Axis-wise defects record `mu_x` distance inputs and
  positive witness boundaries, and AMI aggregates name the selected measured
  squares, positive contributors, and zero-weight defects. Filled nonzero
  holonomy loops point reviewers to measured local curvature cells; unfilled
  loops point reviewers to missing contract, test, runtime, policy, or semantic
  filler evidence. Stokes-style local curvature is measured only when measured
  filler evidence and measured nonzero holonomy are present; holes preserve
  non-fillability witness refs instead.
  Neither case is a theorem discharge, architecture score, future forecast, or
  automatic violation proof.
- `homotopyDistanceReadings[]` computes selected homotopy generator cost,
  measured filler cost, observation-gap lower bound with explicit Lipschitz
  assumptions, and selected finite Dehn-style area. Missing filler evidence
  remains a blocker on filling cost and Dehn area; the reading is not path truth,
  global homology, or repair safety.
- ArchMapStore is the historical forward history boundary for PR and
  longitudinal workflows. In the current v1 runtime, `pr-review` reads
  PR-local `archmap-delta-v0` refs plus base / optional head / optional path
  `archmap/v1` snapshots. Raw source diffs may narrow source refs, but they are
  not canonical semantic inputs to this packet.
- `codebase-inspection` is not a current v1 runtime surface. The current-state
  structural readings that used to be read through inspection reports are
  emitted as v1 packet / summary / viewer refs by `analyze`.
- `archMapStoreRefs` records the packet's canonical history substrate:
  `archmap-delta-v0`, `archmap-commit-v0`, `archmap-snapshot-v0`, and
  `archmap-index-v0`. It also records raw-diff and compaction boundaries so
  review readers can distinguish change-local evidence from snapshot-level
  current-state evidence.
- `monodromyReadingFamily` and `boundaryHolonomyReadingFamily` carry
  evidence-derived status, not just schema presence. Their `status` is derived
  from measured axis count, unmeasured axis count, positive witness count, and
  coverage blocker count. `schemaFoundationOnly` means the family has no
  measurable inputs yet and must not be read as completed measurement.
- `part4DistanceFoundation` is the shared distance-engine boundary. It records
  the selected `DistanceProfile`, observed `DiagnosticScope`, status-summary
  counts, and `supportingDistances[]` rows for Atom, configuration, signature,
  operation, curvature, homotopy/filling, and representation distance families.
  The final `DiagnosticScope` is synchronized after evaluator execution, so
  measured or zero signature axes are removed from `unmeasuredAxisRefs` while
  actual evidence / coverage gaps remain blockers. Unmeasured-axis blockers are
  also filtered when the named axis has become measured or zero in the
  signature-distance partition; operation / curvature partial measurements may
  still leave the corresponding law axis as unmeasured when blocker evidence
  remains.
  A measured or zero `DistanceValue` must carry provenance refs, evaluator-basis
  refs, and coverage refs. Unmeasured, unavailable, incomparable, infinite, and
  blocked rows must carry blocker refs and must not be aggregated as zero.
- `atomDistanceReadings[]` computes Atom geometry distance from ArchMap atom
  observations and semantic observations, not from names, raw presence, or
  viewer layout coordinates. The evaluator records component-specific basis
  refs for fiber, carrier, valence, and semantic anchor distance. Missing
  semantic anchor evidence blocks the selected layout bundle rather than
  contributing zero.
- `configurationDistanceReadings[]` computes selected configuration geometry
  distances from typed ArchMap hyperedges and molecule context, not from raw
  relation counts or schema presence. The evaluator records hyperedge IDs,
  shortest-path atom refs, shortest-path hyperedge refs,
  `configurationIndexedDistance`, `contextDistance`, and
  `smallMoleculeWeightMilli`. Unreachable sampled pairs remain `infinite` with
  blocker refs. Observation gaps block `configurationDistanceBundle` and the
  `configurationGeometry` family-level row rather than contributing zero.
- `signatureDistanceReadings[]` computes selected signature geometry distance
  from LawPolicy signature axes, not from a single raw signature score. The
  evaluator records axis-wise `rhoI`, `axisDistance`, measured / unmeasured /
  incomparable axis partitions, `totalMeasuredDistance`, `safeRegionMargin`,
  `pathDrift`, `endpointDistance`, and `hiddenExcursionStatus`.
  `signatureAxes[]` retain `signatureDistanceReadingRefs` so axis counts
  cannot be read without distance provenance and coverage blockers.
- `operationDistanceReadings[]` computes selected operation cost and repair
  route distance from operation deltas, repair candidates, and the Part IV
  operation cost profile. The evaluator keeps target distance decrease,
  protected-axis movement, distance to selected flat region, and side-effect
  bound separate. Transfer risks and unmeasured protected axes remain blocker
  refs, and `repairOperationCandidates[]` / `operationDeltas[]` retain
  `part4DistanceRefs` so repair candidates cannot be read as automatic safe
  patches.
- `representationMetricReadings[]` computes selected Part IV representation
  metric readings from `analyticRepresentations[]`,
  `spectralAnalysisReadings[]`, `spectralModeReadings[]`,
  `spectralDrilldownReadings[]`, and `representationStrengthReadings[]`.
  Each row separates `structuralDistance`, `analyticDistance`,
  `lipschitzStability`, and `biLipschitzFaithfulness`. Analytic distance is a
  selected representation reading, not an architecture quality score.
  Bi-Lipschitz lower-bound faithfulness remains `blocked` while coverage or
  witness-completeness blockers remain. The source analytic / spectral /
  strength surfaces retain `part4DistanceRefs` so representation conclusions
  cannot be read without the metric evidence boundary.
- `operationSquareCandidates` enumerates supplied, inferred, or blocked
  operation pairs as path pairs `p = g . f` and `q = f . g`. Supplied
  candidates are derived from normalized relations and explicit molecule
  candidates, then carry endpoint refs, generator candidates, support refs, and
  source-backed `candidateBasisRefs`. Inferred candidates are review cues
  derived from shared Atom support, state / effect / contract / semantic /
  authority / runtime / projection evidence; they are not operation truth.
  Blocked candidates preserve missing operation-pair or endpoint evidence
  instead of synthesizing a `:continuation` operation.
- `pathContinuationTraces` records the selected continuation trace for each
  candidate path and axis family: static, contract, semantic, state, effect,
  authority, runtime, and projection. Each axis trace carries a
  `distanceEvaluatorKind`, source-backed `distanceInputRefs`, and
  `comparableContinuationValues` used as the bounded input to
  `d_x(Cont_x(p), Cont_x(q))`. Unmeasured axes are retained as `missingRefs`
  and must not be read as zero defect.
- `axisWiseMonodromyDefects` records `mu_x(sigma)` for each selected operation
  square and axis. Each defect dispatches on the LawPolicy distance kind plus
  axis family, then compares the p/q comparable continuation values rather than
  using observation-ref symmetric difference alone. Defects carry measured
  support, witness refs, source / observation / missing refs, coverage boundary,
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
- `featureExtensionFormulaReadings` and `featureExtensionDiagnosisReadings`
  classify feature-extension witnesses with non-disjoint multi-label
  attribution. The seven labels are inherited core obstruction, feature-local
  obstruction, boundary holonomy, lifting failure, filling failure, complexity
  transfer, and residual coverage gap. Formula readings retain `witnessBasis`
  entries with observation and source refs; diagnosis records carry those refs
  into witness-level attribution. The classifier records review attribution, not
  a mutually disjoint decomposition, and keeps the ArchSig / FieldSig boundary
  explicit.
- `operationCalculusLawReadings` evaluates operation law axes as
  evidence-relative readings. Each axis reports `observed`, `unmeasured`,
  `blocked`, or `notApplicable` with required evidence refs, observed evidence
  refs, blocked reasons, and exactness assumptions. Operation kind tags may make
  an axis applicable, but they do not by themselves discharge an observed law;
  repair monotonicity is tied to selected obstruction valuation and transfer
  risk refs.
- observation projection readings now use canonical Atom projection rows rather
  than treating subject / predicate slot collision as the whole signal. They
  separate source coordinates, observed coordinates, forgotten expected
  coordinates, typed non-injectivity candidates, hidden atom family hints, and
  typed reconstruction blockers with evidence refs.
- axis-forgetting risk records when a coarse observation projection has
  forgotten selected axes, collapsed mixed-axis support, or reconstruction
  blockers connected to selected signature axes. It blocks `ZeroReflecting` and
  `ObstructionReflecting` readings unless explicit axis preservation, witness
  completeness, and selected LawPolicy coverage are supplied.
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
  current AAT structural state from `ArchMap + LawPolicy`. FieldSig studies
  PR / diff / change-vector evolution over workflow evidence and serialized
  `archsig-analysis-packet/v1` handoff artifacts. The packet must not be read as forecast
  correctness, causal truth, raw-diff semantic truth, or raw-ArchMap forecast
  truth.
- analytic representations include weighted adjacency, walk count, reachable
  cone size, nilpotence boundary, selected subgraph spectrum, propagation depth,
  spectral radius, curvature valuation, state algebra boundary, and
  zero-reflecting aggregate boundary. The graph and matrix readings expose
  selected graph nodes, source-backed relation edges, sparse matrix entries, and
  bounded walk witnesses; spectral radius is a bounded finite-matrix estimate
  over that selected relation graph, not a global architecture score.
- spectral analysis readings now include
  `relationAtomWeightedAdjacencyMatrix`, which constructs a finite weighted
  adjacency matrix directly from selected relation atom endpoints and reports
  row/column pressure, Frobenius norm, and a bounded `spectralRadius` estimate.
  The older workflow / molecule / obstruction / operation matrices remain
  bounded review representations over their own measured surfaces.
- emits repair operation candidates with preserved invariants, preconditions,
  transfer risks, evidence boundaries, and non-conclusions
- emits operation deltas and path / homotopy / diagram readings for repair
  planning and review focus
- fills child-level `missingEvidence` / `excludedReadings` from ArchMap
  observation gaps, interpretation-profile coverage, exactness assumptions,
  selected witness rules, optional spectrum measurement boundaries, and
  repair-candidate evidence limits

## Downstream Handoff

`analyze` treats summary / viewer / manifest as the default reading surface.
For v1 input it emits ArchMap validation, LawPolicy validation, normalized
ArchMap, typed evaluator results, architecture distance, summary, viewer data,
and run manifest by default. Raw packet, detail index, packet validation, and
LLM interpretation packet are emitted only with `--emit-raw-artifacts`.
Pre-Atom projections and standalone packet-builder / summary commands are not
current ArchSig CLI surfaces or compatibility commands.

`pr-review` is the separate change-local report surface:

- `archsig-pr-review-report-v1` reads base `archmap/v1`, PR-local
  `archmap-delta-v0`, required `law-policy/v1`, and optional head /
  intermediate `archmap/v1` snapshots. It reports report-local v1 snapshots,
  delta refs matched to typed / derived packet refs, endpoint
  architecture-distance movement, total path movement, hidden-excursion
  boundary, safe-change budget, and structural review focus. Raw diff,
  `archmap-commit-v0`, v0 witness-rule reconstruction, and base/head analysis
  packets are not PR-review inputs.

The report preserves measured witnesses, coverage / exactness boundary,
missing evidence, and non-conclusions. It is not merge approval, global
lawfulness proof, raw-diff semantic parser, forecast, governance, calibration,
or longitudinal FieldSig analysis.

FieldSig handoff projects child-level `missingEvidence` / `excludedReadings`
as unknown remainder and evidence-boundary refs instead of rounding them to
absence, measured zero, forecast truth, or repair safety.
