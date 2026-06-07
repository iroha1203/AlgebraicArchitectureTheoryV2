# ArchMap v1 Schema Cheatsheet

## Root

```json
{
  "schema": "archmap/v1",
  "id": "project-or-scope-id",
  "sources": {},
  "atoms": [],
  "molecules": []
}
```

Unknown root fields fail validation.

## Sources

`sources` is the source ledger for evidence used by the ArchMap.

Common source shapes:

```json
"src.app": { "kind": "file", "path": "src/app.rs" }
```

```json
"src.app.place_order": {
  "kind": "symbol",
  "source": "src.app",
  "symbol": "place_order",
  "line": 23
}
```

Do not list unread private / unavailable / out-of-scope inventory in primary
ArchMap JSON. Keep it in authoring notes or CI reports.

## Atoms

| kind | Required fields |
| --- | --- |
| `component` | `subject` |
| `relation` | `edge` or `subject`, `object`, `predicate` |
| `capability` | `subject`, `predicate` |
| `dataState` | `diagram`, `state` |
| `effect` | `diagram`, `effect` |
| `authority` | `subject`, `authority` |
| `contract` | `diagram`, `contract` |
| `semantic` | `diagram`, `meaning` |
| `runtime` | `edge`, `interaction` |

All `refs` must resolve to `sources` ids.

## Molecules

```json
{
  "id": "mol:local-flow",
  "atoms": ["atom:a", "atom:b"],
  "refs": ["src.app.place_order"],
  "label": "local flow"
}
```

Molecules are explicit membership only. ArchMap does not store generated
molecule proof, operation square evidence, obstruction, distance, or risk.

## Removed v0 Fields

Do not emit:

- `atomObservations`
- `moleculeObservations`
- `semanticObservations`
- `projectionInfo`
- `operationSquareEvidence`
- `concernHints`
- `observationGaps`
- `confidence`
- `uncertainty`
- `nonConclusions`
