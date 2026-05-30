# LawPolicy Schema Guide

Use this guide when authoring `law-policy-v0`.

## Required Top-Level Fields

- `schemaVersion`: must be `law-policy-v0`
- `lawPolicyId`: stable id for this project policy
- `policyVersion`: project policy version
- `scope`: bounded analysis scope
- `archmapSchemaRef`: normally `archmap-observation-map-v0`
- `selectedLaws[]`
- `requiredZeroAxes[]`
- `optionalAxes[]`
- `witnessRules[]`
- `moleculePatterns[]`
- `obstructionCircuitDefinitions[]`
- `signatureAxisDefinitions[]`
- `measurementPolicy`
- `spectrumMeasurementProfile` when ACTS / ArchitectureSpectrumReport readings are requested
- `exactnessAssumptions[]`
- `coverageRequirements[]`
- `excludedReadings[]`
- `nonConclusions[]`

## Cross-Reference Rules

- `selectedLaws[].requiredWitnessRefs[]` must resolve to `witnessRules[].witnessRuleId`.
- `selectedLaws[].requiredAxisRefs[]` must resolve to `requiredZeroAxes[].axisId` or `optionalAxes[].axisId`.
- `witnessRules[].lawRef` must resolve to `selectedLaws[].lawId`.
- `witnessRules[].moleculePatternRefs[]` must resolve to `moleculePatterns[].moleculePatternId`.
- `obstructionCircuitDefinitions[].lawRef` must resolve to `selectedLaws[].lawId`.
- `obstructionCircuitDefinitions[].witnessRuleRef` must resolve to `witnessRules[].witnessRuleId`.
- `obstructionCircuitDefinitions[].signatureAxisRefs[]` must resolve to axis ids.
- `signatureAxisDefinitions[].lawRef` must resolve to `selectedLaws[].lawId`.
- `signatureAxisDefinitions[].axisRef` must resolve to an axis id.
- `coverageRequirements[].appliesToLawRefs[]` must resolve to `selectedLaws[].lawId`.
- `measurementPolicy.selectedAxisRefs[]` must resolve to axis ids.
- `spectrumMeasurementProfile.selectedAxisRefs[]` must resolve to axis ids.
- `spectrumMeasurementProfile.measuredWitnessRuleRefs[]` must resolve to `witnessRules[].witnessRuleId`.
- `spectrumMeasurementProfile.distanceKinds[].axisRef` must resolve to an axis id.
- `spectrumMeasurementProfile.coverageRequirementRefs[]` must resolve to `coverageRequirements[].coverageRequirementId`.

## Measurement Policy

`measurementPolicy` is the general finite measurement policy used by ArchSig.
It is not an empirical calibration claim.

Required fields:

- `policyId`
- `selectedAxisRefs[]`
- `distanceKind`
- `weightPolicy`
- `coveragePolicy`
- `archMapStoreRefKinds[]`
- `measurementBoundary`
- `exactnessAssumptionRefs[]`
- `nonConclusions[]`

Keep `selectedAxisRefs[]` aligned with selected law-backed axes. Use optional
axes only when the user explicitly wants auxiliary review surfaces.

## Spectrum Measurement Profile

Use `spectrumMeasurementProfile` for ACTS / ArchitectureSpectrumReport.
The profile is a measurement recipe over selected LawPolicy axes and witness
rules; it is not a second law universe and not a quality score.

Required fields:

- `profileId`
- `selectedAxisRefs[]`
- `measuredWitnessRuleRefs[]`
- `distanceKinds[]`: each item has `axisRef` and `distanceKind`
- `weightPolicy`
- `supportProjectionRule`
- `transferEdgeRule`
- `clusteringRankingOptions[]`
- `reportFocusOptions[]`
- `coverageRequirementRefs[]`
- `coverageBoundary`
- `exactnessAssumptionRefs[]`
- `measurementBoundary`
- `nonConclusions[]`

Author the profile from human intent, repository evidence, and ArchMap
evidence. Use conservative defaults when evidence is absent:

- unit weights until project calibration is declared
- witness mismatch counts before severity scores
- transfer edges from measured witness support overlap, not source proximity alone
- report focus on top modes, witness refs, source refs, coverage gaps, and non-conclusions

Keep unresolved questions outside the JSON as delivery notes, and reflect their
effect inside `coverageBoundary`, `exactnessAssumptionRefs`, `excludedReadings`,
or `nonConclusions`.

## Common Law Families

Use project-specific names when needed, but common families include:

- `dependency-direction`
- `authority-boundary`
- `tenant-boundary`
- `semantic-contract`
- `state-effect-ordering`
- `idempotency-replay`
- `provider-output-mediation`
- `transaction-boundary`
- `data-model-ownership`
- `source-domain-cohesion`

## Atom Families

Use ArchMap atom family names in `appliesToAtomFamilies`, `requiredAtomFamilies`, and coverage requirements. Common names:

- `existence`
- `relation`
- `capability`
- `state`
- `effect`
- `authority`
- `trust`
- `contractSpecification`
- `semantic`
- `runtimeInteraction`

If an existing policy uses historical names such as `boundaryAuthority` or `semanticInterpretation`, keep them only when the ArchMap and ArchSig binary expect them. Prefer current ArchMap atom family names for new project policies.

## Required Non-Conclusions

Keep these ideas in every policy:

- LawPolicy is selected analysis policy, not AAT itself.
- LawPolicy validation does not prove architecture lawfulness.
- LawPolicy validation does not certify atom truth.
- Missing coverage is not measured zero.
- Signature zero requires ArchSig analysis with declared coverage and exactness assumptions.
- Spectrum measurement profile is a measurement recipe, not a selected law universe.
- Profile differences are not law universe differences.
- ArchitectureSpectrumReport is not a single architecture quality score.
- Unmeasured axes are not zero.

Exact wording may vary, but the boundaries must remain clear.
