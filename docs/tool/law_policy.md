# Interpretation Profile

`law-policy-v0` is the current JSON schema for the selected interpretation
profile used by the ArchMap / ArchSig AAT analysis pipeline.

It is intentionally separate from ArchMap.

```text
ArchMap
  records law-independent Atom observations.

InterpretationProfile
  selects laws, witness rules, molecule patterns, obstruction definitions,
  signature axes, measurement policy, optional spectrum measurement profile,
  coverage requirements, and exactness assumptions.

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
- `spectrumMeasurementProfile` (optional)
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

`distanceKind` and `weightPolicy` are used by `mu_x(sigma)` and `AMI_X(A)`.
They define bounded review telemetry over selected operation squares and axes.
They do not make `AMI_X(A)` a single quality score, merge gate, or global
flatness theorem. `coveragePolicy` keeps unmeasured axes as missing evidence
instead of treating them as zero.

The same measurement policy is shared by the analysis packet,
`archsig-pr-review-report-v1`, and `archsig-codebase-inspection-report-v0`.
The policy selects how ArchSig reads structural telemetry; it does not authorize
FieldSig forecast, governance, calibration, or longitudinal evolution claims.
FieldSig may consume ArchSig packet chains downstream, but it owns those
evolution readings separately from this profile.

## Spectrum Measurement Profile

`spectrumMeasurementProfile` is an optional subobject inside `law-policy-v0`.
It is used by the Curvature / Transfer Spectrum reading family. It does not
select a different law universe and does not make ArchMap law-relative.

The profile records the measurement recipe for ACTS-style readings:

- `profileId`
- `selectedAxisRefs`
- `measuredWitnessRuleRefs`
- `distanceKinds`
- `weightPolicy`
- `supportProjectionRule`
- `transferEdgeRule`
- `clusteringRankingOptions`
- `reportFocusOptions`
- `coverageRequirementRefs`
- `coverageBoundary`
- `exactnessAssumptionRefs`
- `measurementBoundary`
- `nonConclusions`

Changing `spectrumMeasurementProfile` changes how ArchSig ranks, clusters, and
reports selected curvature / transfer telemetry. It does not change which laws
are selected. If a profile wants to treat a different architecture expectation
as law, that expectation must be represented in `selectedLaws`, witness rules,
axes, coverage requirements, and exactness assumptions instead.

Validation checks that profile refs resolve to known axes, witness rules, and
coverage requirements, and that profile-level non-conclusions remain explicit.
Important boundaries:

- profile differences are not law-universe differences
- unmeasured axes are not zero
- spectrum zero requires coverage, exactness, and zero-reflection assumptions
- spectrum readings are bounded ArchSig diagnostics, not Lean theorem discharge

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
