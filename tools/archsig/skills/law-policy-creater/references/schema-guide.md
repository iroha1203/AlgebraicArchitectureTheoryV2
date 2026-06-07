# LawPolicy v1 Schema Guide

LawPolicy v1 is a selector over ArchSig evaluator registry entries.

## Root

```json
{
  "schema": "law-policy/v1",
  "id": "policy-id",
  "policies": []
}
```

Unknown root fields fail validation.

## Policy Entry

Use either a pack selector:

```json
{
  "pack": "solid@1",
  "basis": ["policy-basis:solid"],
  "scope": ["src."],
  "severity": "review"
}
```

Or an individual evaluator selector:

```json
{
  "law": "domain.no-direct-infra-dependency",
  "evaluator": "domain.no-direct-infra-dependency@1",
  "basis": ["policy-basis:layering"],
  "scope": ["domain."],
  "severity": "error"
}
```

## Known Built-In Selectors

Packs:

- `solid@1`

Evaluator ids:

- `solid.single-responsibility@1`
- `solid.open-closed@1`
- `solid.liskov-substitution@1`
- `solid.interface-segregation@1`
- `solid.dependency-inversion@1`
- `domain.no-direct-infra-dependency@1`

Basis refs:

- `policy-basis:solid`
- `policy-basis:layering`

## Removed v0 Surfaces

Do not emit:

- `schemaVersion: "law-policy-v0"`
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

ArchSig evaluator registry owns witness requirements, axes, missing blocker
rules, distance contribution, and result status computation.
