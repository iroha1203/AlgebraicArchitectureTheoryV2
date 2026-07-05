# ArchSig v1 Migration Note

ArchSig v1 is a destructive migration for ArchMap and LawPolicy inputs.

The v1 contract is:

```text
archmap/v1
  -> normalized-archmap/v1
  -> law-policy/v1
  -> typed-evaluator-results/v1
  -> archsig-analysis-packet/v1
  -> archsig-analysis-summary/v1
```

## What Changes

- ArchMap primary JSON is `sources` / `atoms` / `molecules`.
- LawPolicy primary JSON is `policies[]` selector entries.
- ArchSig evaluator registry owns witness requirements, missing blocker rules,
  axes, and distance contribution.
- `analyze` emits `typed-evaluator-results.json`,
  `archsig-analysis-summary.json`, `archsig-atom-viewer-data.json`, and
  `archsig-run-manifest.json` by default.
- `--emit-raw-artifacts` emits v1 packet, detail index, and LLM interpretation
  artifacts.
- `--strict-distance` rejects blocked / unknown / unmeasured typed distance.

## Removed From v1 Inputs

ArchMap v1 does not accept:

- `atomObservations`
- `moleculeObservations`
- `semanticObservations`
- `projectionInfo`
- `operationSquareEvidence`
- `concernHints`
- `observationGaps`

LawPolicy v1 does not accept:

- `selectedLaws`
- `requiredZeroAxes`
- `witnessRules`
- `obstructionCircuitDefinitions`
- `signatureAxisDefinitions`
- `measurementPolicy`
- `part4DistanceProfile`
- `spectrumMeasurementProfile`
- `homotopyMeasurementProfile`
- `coverageRequirements`
- `exactnessAssumptions`

## Compatibility Boundary

No v0 runtime compatibility, dual reader, legacy alias, or compatibility shim is
part of the v1 completion target. Existing v0 artifacts are migration inputs or
historical fixtures, not v1 authoring examples.

`archmap-creater` and `law-policy-creater` now generate v1 artifacts. They must
not emit removed v0 fields as primary output.
