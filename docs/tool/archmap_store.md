# ArchMapStore Delta / Snapshot / Index Model

This document defines the storage boundary for future ArchMap, ArchSig, and
FieldSig workflows.

The purpose is to avoid making raw source diffs the semantic input to ArchSig.
Raw diffs are language-dependent. Python, TypeScript, Rust, Lean, and other
languages each need different parsers, symbol rules, import semantics, and
runtime / semantic adapters. Those language-specific readers belong outside
ArchSig core.

ArchSig and FieldSig should instead share an ArchMap-level history model:

```text
ArchMapStore
  = ArchMapDelta
  + ArchMapCommit
  + ArchMapSnapshot
  + ArchMapIndex
  + validation reports
```

The model is Git-like, but it is not Git. Git stores textual source history.
ArchMapStore stores bounded AAT observation history.

## Product Boundary

ArchSig and FieldSig consume the same history substrate with different product
responsibilities.

```text
ArchSig
  = CI / PR review / lightweight structural diagnosis

FieldSig
  = batch / longitudinal monitoring / evolution quality diagnosis
```

ArchSig reads current or change-local ArchMap evidence and produces bounded AAT
structural review cues. It does not forecast future behavior, replace human
review, or decide merge safety.

FieldSig reads longer ArchMap / ArchSig packet trajectories and studies software
field evolution. It may use batch windows, calibration records, operational
feedback, and governance surfaces. Those are FieldSig responsibilities, not
ArchSig CI responsibilities.

## Canonical Inputs

The canonical input for ArchSig PR review mode is not a raw diff.

```text
base ArchMap
+ PR-local ArchMapDelta
+ LawPolicy
-> ArchSig lightweight PR review
```

Raw diffs are not ArchSig PR-review inputs. A language adapter, extractor, LLM
reader, or manual author supplies ArchMap-level observations and deltas.

## ArchMapDelta

`ArchMapDelta` is the change-local observation artifact.

```text
schema: archmap-delta-v0
```

It records changes to ArchMap-level observations.

```json
{
  "schema": "archmap-delta-v0",
  "deltaId": "amd-...",
  "baseArchMapRef": "archmap-...",
  "provenance": {
    "sourceKind": "git-pr | manual | llm-reader | extractor",
    "sourceRefs": [],
    "adapterRefs": []
  },
  "changedSourceRefs": [],
  "atomChanges": {
    "added": [],
    "removed": [],
    "changed": []
  },
  "moleculeChanges": {
    "added": [],
    "removed": [],
    "changed": []
  },
  "semanticChanges": {
    "added": [],
    "removed": [],
    "changed": []
  },
  "boundaryChanges": {
    "added": [],
    "removed": [],
    "changed": []
  },
  "operationHints": [],
  "featureExtensionHints": [],
  "coverageChanges": [],
  "nonConclusions": []
}
```

`ArchMapDelta` is useful for PR review because it is small and change-local.
It is not a proof that the source diff was completely extracted. It must carry
provenance, coverage gaps, and non-conclusions.

## ArchMapCommit

`ArchMapCommit` connects one or more parent ArchMap states to a resulting
ArchMap state.

```text
schema: archmap-commit-v0
```

```json
{
  "schema": "archmap-commit-v0",
  "commitId": "amc-...",
  "parents": ["amc-..."],
  "deltaRef": "amd-...",
  "resultArchMapRef": "archmap-...",
  "resultStateHash": "...",
  "validationReportRef": "amv-...",
  "nonConclusions": []
}
```

The commit chain is the AAT operation path substrate:

```text
ArchMapCommit_0
  -> ArchMapCommit_1
  -> ArchMapCommit_2
  -> ...
```

ArchSig can read short commit windows as change-local structural evidence.
FieldSig can read longer commit / packet chains as evolution trajectory evidence.

## ArchMapSnapshot

`ArchMapSnapshot` is a materialized ArchMap state checkpoint.

```text
schema: archmap-snapshot-v0
```

```json
{
  "schema": "archmap-snapshot-v0",
  "snapshotId": "ams-...",
  "parents": ["amc-..."],
  "archMapRef": "archmap-...",
  "coveredCommitRange": {
    "from": "amc-...",
    "to": "amc-..."
  },
  "stateHash": "...",
  "policyRefs": [],
  "coverageSummary": {},
  "compactionReport": {
    "squashedDeltaCount": 0,
    "lostChangeGranularity": false,
    "preservedRefs": [],
    "nonConclusions": []
  }
}
```

Snapshots make large repositories practical. Codebase inspection should usually
start from the latest suitable snapshot and then read an optional recent delta
window.

Snapshot compaction has a claim boundary. A compacted snapshot supports
current-state diagnosis. It may not preserve enough ordering detail to replay
all historical operation-order monodromy. The `compactionReport` records that
boundary.

## Checkpoint Policy

An implementation may create a snapshot when any of these conditions hold:

- the delta chain exceeds a configured length
- cumulative changed Atom refs exceed a configured threshold
- removed or rewritten observations exceed a configured threshold
- LawPolicy, coverage policy, or schema version changes
- a release boundary is reached
- a branch merge boundary is reached
- the commit is a frequent PR review base

Checkpoint policy is an implementation choice. The policy must be recorded so
that downstream tools understand the coverage and compaction boundary.

## ArchMapIndex

`ArchMapIndex` is a lookup artifact for large repositories.

```text
schema: archmap-index-v0
```

The index maps review and analysis keys to ArchMap evidence refs.

```json
{
  "schema": "archmap-index-v0",
  "indexId": "ami-...",
  "snapshotRef": "ams-...",
  "sourceRefIndex": {},
  "atomRefIndex": {},
  "boundaryRefIndex": {},
  "axisRefIndex": {},
  "operationHintIndex": {},
  "featureHintIndex": {},
  "coverageGapIndex": {},
  "nonConclusions": []
}
```

The index is an acceleration structure. It does not create new evidence and
must not be used to infer absence from missing index entries unless the index
coverage states that the relevant universe is complete.

## ArchSig Usage

ArchSig CI / PR review mode should use:

```text
base ArchMap
+ PR-local ArchMapDelta
+ LawPolicy
-> change-local structural diagnosis
```

The output is a lightweight review surface:

- changed support
- touched axes
- candidate operation squares
- boundary holonomy witnesses
- missing filler / lifting evidence
- coverage and exactness boundary
- non-conclusions

ArchSig codebase inspection mode should use:

```text
latest ArchMapSnapshot
+ ArchMapIndex
+ optional recent delta window
+ LawPolicy
-> current-state architectural diagnosis
```

This supports top boundary / top order-sensitive square reports without scanning
all historical deltas on every run.

## FieldSig Usage

FieldSig batch mode should use:

```text
ArchMapCommit chain
+ ArchSigPacket chain
+ FieldSigMeasurement chain
+ optional operational feedback
-> evolution quality diagnosis
```

FieldSig may build:

- field trajectories
- ForecastCone / ConsequenceEnvelope inputs
- calibration windows
- governance cues
- quality drift and attractor / basin readings

These are not ArchSig CI outputs.

## Validation Boundary

ArchMapStore validation checks artifact shape, required refs, schema names,
state hashes when supplied, and coverage / compaction reports. It does not prove:

- source extraction completeness
- semantic correctness
- runtime telemetry completeness
- global architecture truth
- operation commutativity
- merge safety
- FieldSig forecast correctness
- Lean theorem discharge

Those non-conclusions travel with deltas, commits, snapshots, and indexes.
