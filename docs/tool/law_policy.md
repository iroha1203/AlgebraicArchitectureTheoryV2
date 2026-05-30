# Interpretation Profile

`law-policy-v0` is the current JSON schema for the selected interpretation
profile used by the ArchMap / ArchSig AAT analysis pipeline.

It is intentionally separate from ArchMap.

```text
ArchMap
  records law-independent Atom observations.

InterpretationProfile
  selects laws, witness rules, molecule patterns, obstruction definitions,
  signature axes, monodromy measurement policy, coverage requirements, and
  exactness assumptions.

ArchSig
  reads ArchMap + InterpretationProfile and computes the AAT analysis packet.
```

Future ArchMapStore workflows keep the same separation:

```text
ArchMapDelta / ArchMapCommit / ArchMapSnapshot / ArchMapIndex
  record observation history and lookup structure.

InterpretationProfile
  selects the laws, axes, distance kind, weight policy, coverage policy, and
  exactness assumptions used to read that history.
```

Raw source diffs may help an adapter choose source refs, but they do not select
LawPolicy and are not canonical semantic inputs to the interpretation profile.

## Responsibility

The interpretation profile owns the selected analysis policy for a specific
review context. It does not define AAT, does not act as a design-rule
collection, and does not prove architecture lawfulness.

The implemented schema records:

- `lawPolicyId`
- `selectedLaws`
- `requiredZeroAxes`
- `optionalAxes`
- `witnessRules`
- `moleculePatterns`
- `obstructionCircuitDefinitions`
- `signatureAxisDefinitions`
- `measurementPolicy`
- `exactnessAssumptions`
- `coverageRequirements`
- `excludedReadings`
- `nonConclusions`

## Validation Boundary

Profile validation checks schema support, identity, uniqueness,
cross-reference integrity, witness / obstruction boundaries, coverage
requirements, exactness assumptions, the monodromy measurement policy surface,
and required non-conclusions.

`measurementPolicy` fixes the ArchSig reading policy for the current
monodromy / boundary holonomy family. It records:

- `selectedAxisRefs`
- `distanceKind`
- `weightPolicy`
- `coveragePolicy`
- `archMapStoreRefKinds`
- `measurementBoundary`
- `exactnessAssumptionRefs`
- `nonConclusions`

The required `archMapStoreRefKinds` are `archmap-delta`, `archmap-commit`,
`archmap-snapshot`, and `archmap-index`. Raw diffs may scope changed source
refs, but they do not choose axes, distance, weight, or coverage policy.

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
records both `law-policy-v0` and `law-policy-validation-report-v0`. The schema
name remains historical; the current ArchSig output treats it as
`interpretationProfileRef`, while preserving `selectedLawPolicyRef` as
provenance for existing profile content.
