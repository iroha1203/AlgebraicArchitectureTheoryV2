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

Exact wording may vary, but the boundaries must remain clear.
