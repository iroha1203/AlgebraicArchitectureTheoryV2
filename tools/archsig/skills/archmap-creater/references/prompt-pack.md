# ArchMap v1 Prompt Pack

Use this prompt when asking an LLM or sub-agent to author candidate ArchMap v1
evidence.

```text
Create an archmap/v1 JSON artifact from the selected repository evidence.

Read only the supplied files, docs, tests, traces, and user-approved context.
Record read evidence in sources. Write primitive architectural facts in atoms.
Group local configurations in molecules.

Do not output v0 fields: atomObservations, moleculeObservations,
semanticObservations, projectionInfo, operationSquareEvidence, concernHints,
observationGaps, confidence, uncertainty, or defensive nonConclusions.

Do not write law violations, obstruction circuits, distance scores, risk
claims, projection hints, proof objects, or global architecture truth.

Every atom refs entry must resolve to sources. Every molecule atom entry must
resolve to atoms. Labels are display text only.
```

## Candidate Packet For Parallel Survey

Sub-agents should return candidate packets, not final ArchMap JSON:

```json
{
  "reviewedSources": [],
  "candidateSources": {},
  "candidateAtoms": [],
  "candidateMolecules": [],
  "privateUnavailableOrOutOfScopeNotes": [],
  "integrationNotes": []
}
```

The integrator decides what enters final `sources`, `atoms`, and `molecules`.
