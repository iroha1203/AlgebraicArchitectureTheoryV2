# Prompt Pack

Use this prompt shape for each reading-pass chunk.

## System Task

Read the assigned worklist rows and emit one
`archmap-candidate-packet/v0.5.1`. You are not producing the final ArchMap. You are
not allowed to use generated inventories as final atoms. Every candidate must
be source-grounded.

## Inputs To The Reader

- `scopeManifestRef`
- pass id: `pass-a` or `pass-b`
- deterministic chunk range
- assigned worklist rows
- `schema-cheatsheet.md`
- `mapping-guide.md`
- `vocabulary-catalog.md`

Do not read the other pass's candidate packets.

## Required Output Shape

```json
{
  "schema": "archmap-candidate-packet/v0.5.1",
  "id": "candidates:pass-a:chunk-01",
  "scopeManifestRef": "scope:orders-service",
  "passId": "pass-a",
  "chunk": { "worklistOrderFrom": 1, "worklistOrderTo": 20 },
  "reviewedSources": [],
  "candidateSources": {},
  "candidateAtoms": [],
  "candidateContexts": [],
  "candidateCovers": [],
  "surveyRows": [
    {
      "sourceId": "src:path/from-worklist",
      "status": "skipped",
      "reason": "unreadable",
      "surveyedKinds": [],
      "candidateAtomIds": [],
      "notes": []
    }
  ],
  "privateUnavailableNotes": [],
  "selfReview": {
    "notScriptGenerated": false,
    "notCoarseWhenEvidenceWasRicher": false,
    "semanticAtomsHaveUseEvidence": false,
    "noDiagnosticShortcutAtoms": false,
    "worklistChunkFullyRead": false,
    "aliasPreservingSemantics": false
  }
}
```

Set a self-review field to `true` only when it is actually satisfied.
The candidate-packet validator treats any false self-review field as not ready.

## Candidate Rules

- Add one `surveyRows` entry for every assigned worklist row.
- Use `status: "read"` when the source was read enough for the surveyed kinds.
- Use `status: "partial"` or `status: "skipped"` only with procedural reasons:
  `private`, `binary`, `unreadable`, or `tooling-error`.
- Do not use `out-of-scope` as a pass-time reason. Report scope mismatch to the
  integrator for a round trip.
- Survey every file for semantic use evidence, even when no semantic atom is
  emitted.
- Semantic candidate atoms must include `object`.
- Do not emit diagnostic-shaped ids or predicates.
- Do not merge different semantic uses of the same subject.
- Keep notes sanitized. Do not include local absolute paths, personal names,
  nonpublic labels, secrets, or machine-specific identifiers.

## Self Review Gate

- `notScriptGenerated`: candidate atoms were written from source reading, not
  generated from an index or script.
- `notCoarseWhenEvidenceWasRicher`: source evidence was not collapsed to a
  coarse component or relation when capabilities, state, effects, authority,
  contracts, runtime, or semantic use were present.
- `semanticAtomsHaveUseEvidence`: every semantic atom cites observed use.
- `noDiagnosticShortcutAtoms`: ids and predicates do not pre-author diagnostic
  conclusions.
- `worklistChunkFullyRead`: every assigned worklist row has a survey row.
- `aliasPreservingSemantics`: different observed semantic uses remain separate.

## Reader Notes

Unmatched candidates are useful. The integrator will compare passes and reread
sources. Do not adjust your output to match another pass.
