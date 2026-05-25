# IntentMap Schema Cheatsheet

Use `intentmap-v0` for Epic / PRD / Spec / Issue / proposal intent before planning forecast.

Required top-level shape:

```json
{
  "schemaVersion": "intentmap-v0",
  "intentMapId": "...",
  "sourceUniverse": {},
  "generator": {},
  "items": [],
  "missingDecisions": [],
  "ambiguousIntents": [],
  "missingEvidence": [],
  "nonConclusions": []
}
```

Each `items[]` entry should include:

- `intentItemId`
- `intentKind`
- `sourceRefs`
- `targetIntentRef`
- `preserves`
- `forgets`
- `claimClassification`
- `confidence`
- `requiredAssumptions`
- `missingDecisions`
- `missingEvidence`
- `nonConclusions`

Preferred `intentKind` values:

- `requirement`
- `operation`
- `workflow`
- `state`
- `transition`
- `invariant`
- `acceptance`
- `non-goal`
- `ambiguity`

Preferred `claimClassification` values:

- `measured`
- `assumed`
- `unmeasured`
- `ambiguous`
- `decision-needed`

Validate with:

```bash
${FIELDSIG_BIN:-fieldsig} intent-map \
  --input <intentmap.json> \
  --out .archsig/intent/intentmap-validation.json
```
