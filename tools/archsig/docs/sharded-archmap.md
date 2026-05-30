# Sharded ArchMap Design

This document defines the planned sharded ArchMap authoring format. The current
runtime artifact remains `archmap-observation-map-v0`; sharding is an authoring
and review layout that must bundle/export back to the monolithic artifact before
current `archsig archmap`, `archsig archsig-analysis`, or `archsig analyze`
commands consume it.

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

- local source universe fragment
- local provenance and generation boundary
- atom observations
- molecule observations
- semantic observations
- observation gaps
- projection hints
- concern hints
- local non-conclusions

The manifest owns ordering, slice identity, export policy, and validation
boundary. The manifest is not a source inventory, runtime trace, or LawPolicy.

## Manifest Shape

Minimal manifest:

```json
{
  "schemaVersion": "archmap-shard-manifest-v0",
  "manifestId": "archmap-manifest-<scope>",
  "mapId": "archmap-<scope>",
  "architectureId": "<architecture-id>",
  "canonicalSchemaVersion": "archmap-observation-map-v0",
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
    "targetSchemaVersion": "archmap-observation-map-v0",
    "targetPath": "archmap.json",
    "sliceOrdering": ["authority", "state", "effects", "providers", "runtime"],
    "idCollisionPolicy": "fail",
    "missingSlicePolicy": "fail-required-warn-optional",
    "sourceUniverseMergePolicy": "union-with-boundary-preservation",
    "nonConclusions": [
      "bundle/export preserves JSON observation refs; it does not prove source completeness"
    ]
  },
  "crossReferenceValidation": {
    "requiredChecks": [
      "all slice paths resolve under manifest root",
      "all slice ids are unique",
      "all observation ids are globally unique after bundling",
      "all accepted sourceRefs[].artifactId resolve to the exported sourceUniverse.includedRefs[] unless they are explicit gap/private/unavailable refs",
      "molecule atomObservationRefs resolve to bundled atomObservations[]",
      "semantic atomObservationRefs resolve to bundled atomObservations[]",
      "semantic moleculeObservationRefs resolve to bundled moleculeObservations[]",
      "projection sourceObservationRef resolves to bundled atom, molecule, or semantic observations",
      "concern refs resolve to bundled atom, molecule, or semantic observations",
      "cross-slice references are either allowed by mayReferenceSlices or downgraded to uncertainty/gap before export"
    ],
    "nonConclusions": [
      "cross-reference validation is not architecture lawfulness",
      "cross-reference validation is not certified Atom truth"
    ]
  },
  "fixturePolicy": {
    "minimalFixture": "two bounded slices that export to a valid monolithic ArchMap shape",
    "largeFixture": "many synthetic bounded slices with duplicate-id, dangling-ref, optional-slice, missing-required-slice, and cross-slice-reference cases",
    "privateDataPolicy": "fixtures must not contain private real-codebase source content"
  },
  "nonConclusions": [
    "sharded ArchMap is an authoring layout, not a new proof surface",
    "monolithic export remains the compatibility contract for current ArchSig analysis"
  ]
}
```

## Slice Shape

A horizontal slice uses this shape:

```json
{
  "schemaVersion": "archmap-observation-slice-v0",
  "sliceId": "authority",
  "sliceKind": "boundedObservationSlice",
  "surface": "authority/authentication",
  "generationBoundary": {},
  "sourceUniverseFragment": {},
  "provenanceFragment": {},
  "atomObservations": [],
  "moleculeObservations": [],
  "semanticObservations": [],
  "observationGaps": [],
  "projectionInfo": [],
  "concernHints": [],
  "nonConclusions": []
}
```

The field names intentionally mirror `archmap-observation-map-v0` so export is a
structural merge rather than semantic reinterpretation.

Recommended slice surfaces:

| Surface | Typical owner | Notes |
| --- | --- | --- |
| `authority/authentication` | roles, session, route gates, admin bypasses | Good first slice because authority observations often cite many source areas. |
| `state/model` | schemas, migrations, persisted state, projections | Cross-references effects and contracts. |
| `effects/jobs` | writes, queues, workers, emails, provider calls | Keeps effect atoms close to job/runtime gaps. |
| `providers/trust` | webhooks, tokens, LLM/provider outputs, delegated credentials | Keeps trust boundary and provider uncertainty local. |
| `domain/contracts` | DTO validation, contract tests, invariants, operation terms | Often feeds semantic observations. |
| `runtime/framework` | traces, generated code, framework conventions, dynamic loading | Often mostly gaps and uncertainty. |
| `docs/governance` | architecture policy, layer docs, review rules | Provides policy readings without claiming lawfulness. |

## Bundle / Export Compatibility

The bundle/export step must produce one valid `archmap-observation-map-v0` JSON
document. Current downstream commands consume only the exported monolithic file.

Export rules:

- preserve all ids exactly
- preserve source refs exactly
- merge source-universe fragments by artifact id, path, kind, and boundary
- fail on duplicate observation ids across slices
- fail when required slices are missing
- warn, but do not fail, when optional slices are absent and the exported
  monolithic artifact still satisfies validation
- fail when bundled cross-reference refs are dangling
- keep unavailable/private/generated/framework evidence as gaps or boundary
  notes, never as observed absence
- keep `nonConclusions` from manifest and slices in the exported artifact
- keep per-slice provenance in the exported provenance or non-conclusion notes

## Validation Test Plan

When bundle/export is implemented, add tests for:

- minimal horizontal-slice fixture exports to a monolithic ArchMap accepted by
  `archsig archmap`
- synthetic large fixture exports deterministically with stable slice ordering
- duplicate ids across slices fail validation
- dangling atom/molecule/semantic/projection/concern refs fail validation
- missing required slice fails validation
- missing optional slice warns when monolithic validation still passes
- cross-slice references not allowed by `mayReferenceSlices` fail or require
  explicit uncertainty before export
- source refs outside exported `sourceUniverse.includedRefs[]` fail unless they
  are explicit gap/private/unavailable refs

These tests validate JSON packaging and reference integrity only. They do not
prove source completeness, architecture lawfulness, Lean theorem discharge, or
forecast correctness.
