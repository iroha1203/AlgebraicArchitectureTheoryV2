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
- `homotopyMeasurementProfile` when Homotopy / Holonomy / Stokes readings or ArchitectureHomotopyReport are requested
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
- `spectrumMeasurementProfile.readingBoundary.coverageRequirementRefs[]` must resolve to `coverageRequirements[].coverageRequirementId`.
- `homotopyMeasurementProfile.selectedAxisRefs[]` must resolve to axis ids.
- `homotopyMeasurementProfile.coverageRequirementRefs[]` must resolve to `coverageRequirements[].coverageRequirementId`.
- `homotopyMeasurementProfile.readingBoundary.coverageRequirementRefs[]` must resolve to `coverageRequirements[].coverageRequirementId`.

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
- `readingBoundary`: includes `readingStrength`,
  `zeroReflectionAssumptions[]`, `obstructionReflectionAssumptions[]`,
  `coverageRequirementRefs[]`, and `witnessCompletenessBoundary`
- `nonConclusions[]`

Author the profile from human intent, repository evidence, and ArchMap
evidence. Use conservative defaults when evidence is absent:

- unit weights until project calibration is declared
- witness mismatch counts before severity scores
- transfer edges from measured witness support overlap, not source proximity alone
- report focus on top modes, witness refs, source refs, coverage gaps, and non-conclusions
- reading strength that distinguishes measured support rows from bounded
  transfer proxies and coverage-blocked rows

Keep unresolved questions outside the JSON as delivery notes, and reflect their
effect inside `coverageBoundary`, `exactnessAssumptionRefs`, `excludedReadings`,
or `nonConclusions`.

## Homotopy Measurement Profile

Use `homotopyMeasurementProfile` for Homotopy / Holonomy / Stokes readings and
ArchitectureHomotopyReport. The profile is a measurement recipe over selected
LawPolicy axes. It is not a chain-complex proof object, not a second law
universe, and not a requirement for humans to hand-author topology.

Required fields:

- `profileId`
- `selectedAxisRefs[]`
- `pathDiscoveryRules[]`: each item has `ruleId`, `pathSourceKind`,
  `endpointPolicy`, `candidateSource`, `evidenceBoundary`, and
  `nonConclusions[]`
- `fillerRules[]`: each item has `ruleId`, `fillerKind`,
  `requiredSourceRefKinds[]`, `missingFillerBehavior`, `evidenceBoundary`, and
  `nonConclusions[]`
- `loopMeasurementPolicy`: includes `policyId`, `loopCandidateSources[]`,
  `filledLoopReading`, `unfilledLoopReading`, `holonomyDistanceKind`,
  `localCurvatureReadingBoundary`, and `nonConclusions[]`
- `continuationPolicy`
- `distancePolicy`
- `coverageRequirementRefs[]`
- `coverageBoundary`
- `exactnessAssumptionRefs[]`
- `measurementBoundary`
- `readingBoundary`: includes `readingStrength`,
  `zeroReflectionAssumptions[]`, `obstructionReflectionAssumptions[]`,
  `coverageRequirementRefs[]`, and `witnessCompletenessBoundary`
- `nonConclusions[]`

Author the profile from human intent, repository evidence, and ArchMap
evidence. Use conservative defaults when evidence is absent:

- LLM-discovered path candidates must cite source refs or remain unresolved.
- Filler laws come from contracts, tests, runtime traces, policies, source refs,
  or explicit user approval.
- Missing filler evidence becomes an architectural hole and coverage gap, not a
  violation proof.
- Nonzero holonomy is a bounded current-state review queue, not forecast,
  incident prediction, or repair-safety evidence.
- Operation sequences, endpoint refs, generator candidates, continuation
  distance inputs, and filler evidence determine what is measured. Missing
  inputs stay unmeasured or coverage-blocked.
- `candidateSource` should distinguish supplied operation-square evidence from
  inferred review cues. A LawPolicy may say which supplied / inferred sources
  are eligible, but source-backed operation sequences and endpoints belong in
  ArchMap `operationSquareEvidence[]`, not in the policy.
- ArchitectureHomotopyReport is not a single architecture quality score.

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
- Homotopy measurement profile is a measurement recipe, not a law universe.
- Candidate paths and loops are review cues, not path truth.
- Unfilled loops are architectural holes, not automatic violations.
- Missing filler evidence is not measured zero.
- ArchitectureHomotopyReport is not a single architecture quality score.

Exact wording may vary, but the boundaries must remain clear.
