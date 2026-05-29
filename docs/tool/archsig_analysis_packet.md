# ArchSig Analysis Packet

`archsig-analysis-packet-v0` is the LLM-native ArchSig output artifact.
It reads a source-grounded ArchMap together with one selected LawPolicy and
records AAT-based, law-relative analysis.

```text
ArchMap
  records law-independent Atom observations.

LawPolicy
  selects the LawUniverse, witness rules, signature axes, coverage, and exactness.

ArchSig Analysis Packet
  records molecule readings, obstruction circuits, signature axes, flatness
  reading, repair operation candidates, child-level evidence boundaries, and
  LLM notes.
```

## Responsibility

The packet owns structured analysis results. It is not a theorem proof and not
a single architecture quality score.

The implemented schema records:

- `selectedLawPolicyRef`
- `archMapRef`
- `atomConfigurationSummary`
- `moleculeReadings`
- `obstructionCircuits`
- `signatureAxes`
- `flatnessReading`
- `staticRuntimeSemanticLayerSplit`
- `repairOperationCandidates`
- `evidenceBoundary`
- `interpretationNotesForLLM`
- `excludedReadings`
- `nonConclusions`

## Validation Boundary

Packet validation checks identity, ArchMap / LawPolicy references, law-relative
obstruction links, signature / flatness references, repair candidate guardrails,
LLM interpretation notes, evidence boundary, and required non-conclusions.
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

## Current Fixture

- `tools/archsig/tests/fixtures/minimal/archsig_analysis_packet.json`

The fixture is locked against the static Rust builder and the schema catalog
records both `archsig-analysis-packet-v0` and
`archsig-analysis-packet-validation-report-v0`.

## Builder

`build_archsig_analysis_packet` deterministically builds a packet from one
`ArchMapDocumentV0` and one `LawPolicyDocumentV0`.

The builder:

- evaluates selected LawPolicy witness rules over ArchMap atom and semantic observations
- uses `concernHints` only as auxiliary evidence
- constructs obstruction circuits only as ArchSig outputs
- values required signature axes from constructed obstruction circuits
- preserves observation gaps as flatness blockers, not measured zero
- emits repair operation candidates with preserved invariants, preconditions,
  transfer risks, evidence boundaries, and non-conclusions
- fills child-level `missingEvidence` / `excludedReadings` from ArchMap
  observation gaps, LawPolicy coverage and exactness assumptions, selected
  witness rules, and repair-candidate evidence limits

## Downstream Handoff

`llm-native-workflow` treats the analysis packet as the source artifact and
emits only ArchMap validation, LawPolicy validation, the analysis packet, packet
validation, and the LLM interpretation packet. Old AIR, theorem-check, Feature
Report, and AAT Observable Bundle projections are no longer current ArchSig
CLI surface.

FieldSig handoff projects child-level `missingEvidence` / `excludedReadings`
as unknown remainder and evidence-boundary refs instead of rounding them to
absence, measured zero, forecast truth, or repair safety.
