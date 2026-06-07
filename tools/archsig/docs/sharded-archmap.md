# Sharded ArchMap Design

This document defines a planned sharded ArchMap authoring layout. The current
runtime artifact remains a monolithic `archmap/v1`; sharding is an authoring
and review layout that must bundle/export back to one v1 ArchMap before current
`archsig archmap` or `archsig analyze` commands consume it.

The primary sharding model is horizontal: each shard is a bounded observation
slice over a repository surface, subsystem, package, team-owned area, or
sub-agent assignment. Vertical shards by schema field are allowed only as a
secondary export optimization; they are not the recommended authoring shape for
large codebases.

## Directory Shape

Use this layout by default:

```text
.archsig/archmap/
  manifest.json
  slices/
    authority.archmap-slice.json
    state.archmap-slice.json
    effects.archmap-slice.json
    providers.archmap-slice.json
    runtime.archmap-slice.json
```

Each slice owns a small ArchMap-like fragment:

- local source records
- local generation boundary
- Atom rows
- explicit molecule candidate rows
- local non-conclusions

The manifest owns ordering, slice identity, export policy, and validation
boundary. The manifest is not a source inventory, runtime trace, LawPolicy, or
ArchSig analysis packet.

## Manifest Shape

Minimal manifest:

```json
{
  "schemaVersion": "archmap-shard-manifest-v1",
  "manifestId": "archmap-manifest-<scope>",
  "mapId": "archmap-<scope>",
  "architectureId": "<architecture-id>",
  "canonicalSchema": "archmap/v1",
  "root": ".archsig/archmap",
  "shardingMode": "horizontal-bounded-observation-slices",
  "slices": [
    {
      "sliceId": "authority",
      "sliceKind": "boundedObservationSlice",
      "surface": "authority/authentication",
      "path": "slices/authority.archmap-slice.json",
      "ownedSourceScopes": ["src/auth", "src/routes"],
      "mayReferenceSlices": ["state", "providers"],
      "required": true
    },
    {
      "sliceId": "effects",
      "sliceKind": "boundedObservationSlice",
      "surface": "effects/jobs",
      "path": "slices/effects.archmap-slice.json",
      "ownedSourceScopes": ["src/jobs", "src/mail", "src/events"],
      "mayReferenceSlices": ["state", "providers"],
      "required": false
    }
  ],
  "exportPolicy": {
    "targetSchema": "archmap/v1",
    "targetPath": "archmap.json",
    "sliceOrdering": ["authority", "state", "effects", "providers", "runtime"],
    "idCollisionPolicy": "fail",
    "missingSlicePolicy": "fail-required-warn-optional",
    "sourceMergePolicy": "union-with-boundary-preservation",
    "nonConclusions": [
      "bundle/export preserves observation refs; it does not prove source completeness"
    ]
  },
  "crossReferenceValidation": {
    "requiredChecks": [
      "all slice paths resolve under manifest root",
      "all slice ids are unique",
      "all source ids are globally unique after bundling",
      "all atom ids are globally unique after bundling",
      "all molecule ids are globally unique after bundling",
      "all atom source refs resolve to exported sources",
      "all molecule member atom refs resolve to bundled atoms",
      "all molecule source refs resolve to exported sources",
      "cross-slice references are either allowed by mayReferenceSlices or downgraded to an explicit boundary before export"
    ],
    "nonConclusions": [
      "cross-reference validation is not architecture lawfulness",
      "cross-reference validation is not certified Atom truth"
    ]
  },
  "nonConclusions": [
    "sharded ArchMap is an authoring layout, not a new proof surface",
    "monolithic archmap/v1 export remains the current ArchSig analysis contract"
  ]
}
```

## Slice Shape

A horizontal slice uses this shape:

```json
{
  "schemaVersion": "archmap-observation-slice/v1",
  "sliceId": "authority",
  "sliceKind": "boundedObservationSlice",
  "surface": "authority/authentication",
  "generationBoundary": {},
  "sources": {},
  "atoms": [],
  "molecules": [],
  "nonConclusions": []
}
```

The field names mirror `archmap/v1` so export is a structural merge rather than
semantic reinterpretation. Removed v0 helper fields such as
`semanticObservations`, `projectionInfo`, `operationSquareEvidence`,
`concernHints`, and `observationGaps` are not slice fields.

Recommended slice surfaces:

| Surface | Typical owner | Notes |
| --- | --- | --- |
| `authority/authentication` | roles, session, route gates, admin bypasses | Good first slice because authority observations often cite many source areas. |
| `state/model` | schemas, migrations, persisted state, projections | Cross-references effects and contracts. |
| `effects/jobs` | writes, queues, workers, emails, provider calls | Keeps effect atoms close to job/runtime boundaries. |
| `providers/trust` | webhooks, tokens, LLM/provider outputs, delegated credentials | Keeps trust boundary and provider uncertainty local. |
| `domain/contracts` | DTO validation, contract tests, invariants, operation terms | Often feeds semantic atoms. |
| `runtime/framework` | traces, generated code, framework conventions, dynamic loading | Often mostly boundary notes and unavailable evidence. |
| `docs/governance` | architecture policy, layer docs, review rules | Provides LawPolicy basis refs without claiming lawfulness. |

## Bundle / Export Compatibility

The bundle/export step must produce one valid `archmap/v1` JSON document.
Current downstream commands consume only the exported monolithic file.

Export rules:

- preserve all ids exactly
- preserve source refs exactly
- merge source fragments by id, path, kind, and boundary
- fail on duplicate source, atom, or molecule ids across slices
- fail when required slices are missing
- warn, but do not fail, when optional slices are absent and the exported
  monolithic artifact still satisfies validation
- fail when bundled cross-reference refs are dangling
- keep unavailable/private/generated/framework evidence as boundary notes, never
  as observed absence
- keep `nonConclusions` from manifest and slices in the exported artifact
- keep per-slice provenance in exported boundary notes

## Validation Test Plan

When bundle/export is implemented, add tests for:

- minimal horizontal-slice fixture exports to a monolithic ArchMap accepted by
  `archsig archmap`
- synthetic large fixture exports deterministically with stable slice ordering
- duplicate ids across slices fail validation
- dangling source / atom / molecule refs fail validation
- removed v0 helper fields in a slice fail validation
- missing required slice fails validation
- missing optional slice warns when monolithic validation still passes
- cross-slice references not allowed by `mayReferenceSlices` fail or require an
  explicit boundary before export
- source refs outside exported `sources` fail unless they are explicitly marked
  unavailable / private before export
