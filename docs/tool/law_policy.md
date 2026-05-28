# LawPolicy

`law-policy-v0` is the selected LawUniverse artifact used by the
LLM-native ArchMap / ArchSig pipeline.

It is intentionally separate from ArchMap.

```text
ArchMap
  records law-independent Atom observations.

LawPolicy
  selects laws, witness rules, molecule patterns, obstruction definitions,
  signature axes, coverage requirements, and exactness assumptions.

ArchSig
  reads ArchMap + LawPolicy and computes law-relative analysis.
```

## Responsibility

LawPolicy owns the selected analysis policy for a specific review context.
It does not define AAT and does not prove architecture lawfulness.

The implemented schema records:

- `lawPolicyId`
- `selectedLaws`
- `requiredZeroAxes`
- `optionalAxes`
- `witnessRules`
- `moleculePatterns`
- `obstructionCircuitDefinitions`
- `signatureAxisDefinitions`
- `exactnessAssumptions`
- `coverageRequirements`
- `excludedReadings`
- `nonConclusions`

## Validation Boundary

LawPolicy validation checks schema support, identity, uniqueness, cross-reference
integrity, witness / obstruction boundaries, coverage requirements, exactness
assumptions, and required non-conclusions.

Validation does not imply:

- architecture lawfulness
- certified Atom truth
- zero curvature
- Lean theorem discharge
- extractor completeness

Missing coverage remains a coverage gap. It is not measured zero.

## Current Fixture

- `tools/archsig/tests/fixtures/minimal/law_policy.json`

The fixture is locked against the static Rust builder and the schema catalog
records both `law-policy-v0` and `law-policy-validation-report-v0`.
