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
  representations, workflow risk readings, design principle readings, bounded
  judgements, repair operation candidates, operation deltas, path / homotopy /
  diagram readings, child-level evidence boundaries, and an LLM interpretation
  packet.
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
readings, design principle readings, law-relative obstruction links, signature /
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
  workflow risk readings, and design principle readings
- workflow risk readings rank molecule-local review pressure using ArchMap
  atoms, molecule roles, semantic observations, concern hints, and observation
  gaps. They are review-prioritization readings, not quality scores.
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

`llm-native-workflow` treats the analysis packet as the source artifact and
emits only ArchMap validation, LawPolicy validation, the analysis packet, packet
validation, and the LLM interpretation packet. Pre-Atom projections and review
surfaces are not current ArchSig CLI surface or compatibility commands.

FieldSig handoff projects child-level `missingEvidence` / `excludedReadings`
as unknown remainder and evidence-boundary refs instead of rounding them to
absence, measured zero, forecast truth, or repair safety.
