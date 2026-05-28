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
  reading, repair operation candidates, evidence boundaries, and LLM notes.
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
