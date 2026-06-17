# ArchMap v2 Prompt Pack

Use this prompt when asking an LLM or sub-agent to author candidate ArchMap v2
evidence.

```text
Create candidate evidence for an archmap/v2 JSON artifact from the selected repository evidence.

Read only the supplied files, docs, tests, traces, and user-approved context.
Record read evidence in sources. Write primitive architectural facts in atoms.
Group finite observation regions in contexts and selected finite families in covers.
Do not include extractionDoctrineRef; ArchSig supplies the fixed
doctrine:aat-canonical@1 contract during validation and normalization.

Do not create atoms mechanically from a script, AST dump, import graph, route list,
or filename template. Use such outputs only as navigation aids. Final candidate
atoms must come from reading the supplied evidence.

Do not stop at coarse component/relation atoms when the evidence shows
capabilities, states, effects, authority, contracts, runtime behavior, or domain
semantic use. Split those into primitive atoms with direct refs.

For semantic atoms, extract meaning from use. Include only meanings grounded in
commands, tests, docs, invariants, transitions, permissions, or traces. Do not
write dictionary glosses, vibes, or lawfulness conclusions.

Do not output v0 fields: atomObservations, moleculeObservations,
semanticObservations, projectionInfo, operationSquareEvidence, concernHints,
observationGaps, confidence, uncertainty, or defensive nonConclusions.
Do not output v1 molecules for archmap/v2.

Do not write law violations, obstruction circuits, distance scores, risk
claims, projection hints, proof objects, or global architecture truth.
Do not invent diagnostic-shaped atom ids or predicates such as *_mismatch,
*_obstruction, *_violation, *_risk, *_debt, *_unsafe, *_lawful, *_nonzero, or
*_failure. These tokens are forbidden in authored ids and predicates; write
neutral observed relations and let ArchSig evaluators derive diagnostic readings.

Every atom refs entry must resolve to sources. Every context atom entry must
resolve to atoms. Every cover context entry must resolve to contexts. Labels are
display text only.
```

## Candidate Packet For Parallel Survey

Sub-agents should return candidate packets, not final ArchMap JSON:

```json
{
  "reviewedSources": [],
  "candidateSources": {},
  "candidateAtoms": [],
  "candidateContexts": [],
  "candidateCovers": [],
  "privateUnavailableOrOutOfScopeNotes": [],
  "integrationNotes": [],
  "selfReview": {
    "notScriptGenerated": true,
    "notCoarseWhenEvidenceWasRicher": true,
    "semanticAtomsHaveUseEvidence": true,
    "noDiagnosticShortcutAtoms": true
  }
}
```

The integrator decides what enters final `sources`, `atoms`, `contexts`, and
`covers`.

## Self-Review Gate

Before delivering final ArchMap JSON, answer these gates from the artifact and
source notes:

- `notScriptGenerated`: final atoms were selected by source reading, not by a
  mechanical dump.
- `notCoarseWhenEvidenceWasRicher`: all observed capabilities, states, effects,
  authority, contracts, runtime behavior, and semantic use relevant to scope are
  represented or explicitly out of scope.
- `semanticAtomsHaveUseEvidence`: every semantic atom cites observed use.
- `noDiagnosticShortcutAtoms`: ids / predicates do not encode evaluator
  conclusions or diagnostic shortcut tokens.

Any `false` gate blocks delivery.
