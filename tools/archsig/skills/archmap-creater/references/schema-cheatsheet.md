# ArchMap v2 Schema Cheatsheet

## Root

```json
{
  "schema": "archmap/v2",
  "id": "project-or-scope-id",
  "extractionDoctrineRef": {
    "doctrineId": "doctrine:project@1",
    "fingerprint": "sha256:project-doctrine",
    "components": ["V", "Gamma", "R", "rho", "E", "N"]
  },
  "sources": {},
  "atoms": [],
  "contexts": [],
  "covers": []
}
```

Unknown root fields fail validation.

## Extraction Doctrine

`extractionDoctrineRef` is required for A8-relative determinism. Components
must resolve the AAT atom vocabulary expected by ArchSig; the AG fixtures use
`["V", "Gamma", "R", "rho", "E", "N"]`.

The doctrine ref is a comparability boundary. Do not compare or merge ArchMaps
with different doctrine fingerprints unless the tool explicitly accepts it.

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

Every v2 atom has `id`, `kind`, `subject`, `axis`, and `refs`. It may also have
`predicate`, `object`, and `label`.

Common AG axes:

- `static`
- `restriction`
- `cech`
- `square-free`
- `tor`
- `support`
- `cohomology`
- `repair`
- `conflict`
- `laplacian`
- `period`
- `transfer`

This is a practical fixture-aligned list, not a closed schema enum. Prefer
existing fixture/evaluator axis tokens when authoring AG measurement inputs.

All `refs` must resolve to `sources` ids.

## Contexts

```json
{
  "id": "ctx:order",
  "atoms": ["atom:a", "atom:b"],
  "restrictsTo": ["ctx:shared"],
  "refs": ["src.order"],
  "label": "order context"
}
```

Contexts form a finite poset over atom subfamilies. `restrictsTo` entries must
resolve to contexts and must be acyclic.

## Covers

```json
{
  "id": "cover:order-inventory",
  "contexts": ["ctx:order", "ctx:inventory", "ctx:shared"],
  "refs": ["src.cover"],
  "label": "order/inventory cover"
}
```

Covers are observed finite context families. U-adequacy, coefficients, witness
families, verdict predicates, exactness, and repair semantics are selected in
MeasurementProfile, not in ArchMap.

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
- `molecules` in `archmap/v2`
