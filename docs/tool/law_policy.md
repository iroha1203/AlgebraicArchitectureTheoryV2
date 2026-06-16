# Interpretation Profile

`law-policy/v1` is the current JSON schema for the selected ArchSig evaluator
policy. It is intentionally separate from ArchMap.

LawPolicy v1 is a selector:

```json
{
  "schema": "law-policy/v1",
  "id": "project-policy",
  "distanceProfileRef": "distance-profile:architecture-default@1",
  "policies": [
    {
      "pack": "solid@1",
      "basis": ["policy-basis:solid"],
      "scope": ["src."],
      "severity": "review"
    }
  ]
}
```

It selects policy packs, evaluator ids, basis refs, scope, severity, and an
optional `distanceProfileRef`.
Witness requirements, signature axes, coverage blockers, exactness assumptions,
distance weights, operation costs, and distance contribution belong to the
ArchSig evaluator registry / selected distance profile, not to LawPolicy JSON.

## v1 Distance Profile Selector

`distanceProfileRef` is a selector, not a profile body. LawPolicy v1 must not
embed `part4DistanceProfile`, distance weights, operation cost tables, witness
DSLs, axis formulas, or coverage DSLs. `archsig analyze --strict-distance`
requires an explicit `distanceProfileRef` and rejects unknown refs, so a run
cannot silently pass through a legacy profile fallback.

The current built-in refs are:

- `distance-profile:architecture-default@1`
- `distance-profile:practical-rust-service@1`

`architecture-distance.json` records the selected profile ref and computed
atom / configuration / signature / operation distance readings. Summary,
viewer, and LLM packets expose this as architecture distance; AAT mathematics
source refs may remain raw metadata.

## Legacy v0 Profile

`law-policy-v0` is the legacy JSON schema for the older selected interpretation
profile used by the v0 ArchMap / ArchSig AAT analysis pipeline.

Everything in this section is historical. It does not describe the current
`law-policy/v1` input contract, and it must not be copied into v1 authoring.
Current v1 authoring uses `distanceProfileRef` only.

The legacy profile was intentionally separate from ArchMap.

```text
ArchMap
  records law-independent Atom observations.

InterpretationProfile
  selects laws, witness rules, molecule patterns, obstruction definitions,
  signature axes, measurement policy, optional spectrum measurement profile,
  optional homotopy measurement profile, selected Part IV distance profile
  boundary, coverage requirements, and exactness assumptions.

ArchSig
  reads ArchMap + InterpretationProfile and computes the AAT analysis packet.
```

Historical ArchMapStore design notes used the same separation:

```text
ArchMapDelta / ArchMapCommit / ArchMapSnapshot / ArchMapIndex
  record observation history and lookup structure.

InterpretationProfile
  selects the laws, axes, distance kind, weight policy, coverage policy, and
  exactness assumptions used to read that history.
```

Raw source diffs could help an adapter choose source refs, but they did not
select LawPolicy and were not canonical semantic inputs to the selected
analysis policy.

## Legacy v0 Responsibility

The legacy v0 profile owned the selected analysis policy for a specific review
context. It did not define AAT, did not act as a design-rule collection, and did
not prove architecture lawfulness.

For legacy Part IV distance analysis, the v0 profile was the source of the
selected `DistanceProfile` boundary that ArchSig copied into
`part4DistanceFoundation`. That boundary could select axes, weights, operation
costs, coverage refs, aggregation policy, and unmeasured propagation policy.
It was not empirical calibration, a hidden repair cost model, or a Lean theorem
proof. In v1, this profile body is not embedded in LawPolicy; v1 selects a
registry-owned profile by `distanceProfileRef`.

The legacy implemented schema records:

- `lawPolicyId`
- `selectedLaws`
- `requiredZeroAxes`
- `optionalAxes`
- `witnessRules`
- `moleculePatterns`
- `obstructionCircuitDefinitions`
- `signatureAxisDefinitions`
- `measurementPolicy`
- `part4DistanceProfile`
- `spectrumMeasurementProfile` (optional)
- `homotopyMeasurementProfile` (optional)
- `exactnessAssumptions`
- `coverageRequirements`
- `excludedReadings`
- `nonConclusions`

## Legacy v0 Validation Boundary

Legacy profile validation checks schema support, identity, uniqueness,
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

The same legacy measurement policy was shared by the analysis packet and older
report surfaces. The policy selected how ArchSig read structural telemetry; it
did not authorize FieldSig forecast, governance, calibration, or longitudinal
evolution claims. FieldSig may consume ArchSig packet chains downstream, but it
owns those evolution readings separately from this profile.

## Legacy v0 Part IV Distance Profile

`part4DistanceProfile` was the first-class LawPolicy v0 surface for Part IV
distance measurement. ArchSig copied it into
`part4DistanceFoundation.profile` and used it as the selected source for:

- `atomWeights`
- `signatureWeights`
- `operationCosts`
- `aggregationPolicy`
- `unmeasuredPolicy`
- `lawOverlayPolicy`
- `coverageRequirementRefs`
- `evidenceBoundary`
- `calibrationRefs`
- `nonConclusions`

Legacy validation required the Atom geometry components `atom.fiber`, `atom.carrier`,
`atom.valence`, and `atom.semanticAnchor`; positive weights and operation
costs; signature weights that reference declared `signatureAxisDefinitions`;
coverage refs that reference declared `coverageRequirements`; and an
`unmeasuredPolicy` that states unmeasured distance is not zero.

The legacy v0 strict-distance path rejected a LawPolicy that lacked
`part4DistanceProfile`. Current v1 `archsig analyze --strict-distance` rejects a
missing or unknown `distanceProfileRef` instead.

## Spectrum Measurement Profile

`spectrumMeasurementProfile` is an optional subobject inside `law-policy-v0`.
It is used by the Curvature / Transfer Spectrum reading family. It does not
select a different law universe and does not make ArchMap law-relative.
The intended authoring surface is LLM-native: derive the profile from human
intent, repository evidence, ArchMap evidence, unresolved questions, and
non-conclusions, then validate it with ArchSig. Do not make humans hand-author a
large profile without source evidence.

In the complete-first ArchMap workflow, the profile is authored alongside the
ArchMap evidence. `readingBoundary.coverageRequirementRefs` should point to the
same coverage universe the ArchMap can actually support, and missing support
should drive an authoring repair pass before user handoff. A residual coverage
gap is acceptable only when the needed evidence is private, unavailable, or
out of scope.

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
- `readingBoundary`
- `nonConclusions`

Changing `spectrumMeasurementProfile` changes how ArchSig ranks, clusters, and
reports selected curvature / transfer telemetry. It does not change which laws
are selected. If a profile wants to treat a different architecture expectation
as law, that expectation must be represented in `selectedLaws`, witness rules,
axes, coverage requirements, and exactness assumptions instead.

Validation checks that profile refs resolve to known axes, witness rules, and
coverage requirements, and that profile-level non-conclusions remain explicit.
The `readingBoundary` records the measurement strength, zero-reflection
assumptions, obstruction-reflection assumptions, coverage requirement refs, and
witness-completeness boundary that ArchSig copies into ACTS report rows. It is
the boundary between measured support rows, bounded transfer proxies, and
coverage gaps. `transferEdgeRule`, `distanceKinds`, and `weightPolicy` are
measurement recipes; they are not new laws and not empirical calibration unless
the selected policy explicitly supplies that evidence.

## Law / Witness / Axis Alignment

ArchSig reads `selectedLaws`, `witnessRules`, `signatureAxisDefinitions`,
`coverageRequirements`, and `exactnessAssumptions` as one selected visibility
profile. A law is not treated as covered merely because one required Atom family
appears in ArchMap. The analysis packet emits `lawWitnessAxisEvaluations[]`
inside `lawUniverseCoverageReadings[]`; each row records required and observed
witness refs, required and observed axis refs, coverage requirement refs,
exactness assumption refs, source-backed evidence refs, blockers, and separate
coverage / exactness statuses.

Authoring implication: every selected law should point to witness rules for the
same law and to axes that also have a `signatureAxisDefinitions[]` row for that
law. Missing witness evidence, missing selected axes, missing source-ref kinds,
or unresolved exactness assumptions remain blockers, not measured zero and not
lawfulness proofs.
Important boundaries:

- profile differences are not law-universe differences
- unmeasured axes are not zero
- spectrum zero requires coverage, exactness, and zero-reflection assumptions
- spectrum readings are bounded ArchSig diagnostics, not Lean theorem discharge
- ArchitectureSpectrumReport is not a single architecture quality score
- recurrent obstruction support is not future incident prediction or repair
  safety evidence

Validation does not imply:

- architecture lawfulness
- certified Atom truth
- zero curvature
- Lean theorem discharge
- source-observation layer

Missing coverage remains a coverage gap. It is not measured zero.

## Homotopy Measurement Profile

`homotopyMeasurementProfile` is an optional subobject inside `law-policy-v0`.
It is used by the Homotopy / Holonomy Stokes reading family. It records how
ArchSig should discover candidate paths, distinguish filled loops from
architectural holes, measure selected-axis holonomy, and preserve missing
filler evidence. It does not select a different law universe and does not make
ArchMap law-relative.

The intended authoring surface is LLM-native. A human supplies analysis goal,
risk focus, source scope, normative evidence, excluded readings, and how
conservative the zero / filler reading should be. The LLM uses
`tools/archsig/skills/law-policy-creater` to synthesize the profile from
repository evidence and user intent, then validates it with ArchSig.

The LawPolicy should not make the user compensate for an incomplete ArchMap.
For complete-first authoring, path discovery rules, filler rules, coverage
requirements, and reading boundaries are checked against the ArchMap before
handoff. If a loop is blocked, the authoring pass should either add
contract/test/runtime/source/policy filler evidence or leave a targeted
non-fillability gap whose subject names the affected path rule or operation
square.

The profile records:

- `profileId`
- `selectedAxisRefs`
- `pathDiscoveryRules`
- `fillerRules`
- `loopMeasurementPolicy`
- `continuationPolicy`
- `distancePolicy`
- `coverageRequirementRefs`
- `coverageBoundary`
- `exactnessAssumptionRefs`
- `measurementBoundary`
- `readingBoundary`
- `nonConclusions`

Validation checks that selected axes and coverage refs resolve, that path
discovery / filler / loop rules keep evidence boundaries explicit, and that
required non-conclusions remain present. The `readingBoundary` records the
measurement strength, zero-reflection assumptions, obstruction-reflection
assumptions, coverage requirement refs, and witness-completeness boundary that
ArchSig copies into Homotopy / Holonomy / Stokes records. Path discovery,
endpoint policy, generator rules, distance policy, and filler rules are
measurement recipes over selected evidence; they are not a second law universe,
path truth, or a homology proof.
Important boundaries:

- profile differences are not law-universe differences
- candidate paths and loops are review cues, not path truth
- unfilled loops are architectural holes, not automatic violations
- missing filler evidence is not measured zero
- nonzero holonomy is bounded current-state diagnosis, not future incident
  prediction or repair-safety evidence
- ArchitectureHomotopyReport is not a single architecture quality score,
  theorem proof, path truth, or global homology computation

## Legacy Fixture

- `tools/archsig/tests/fixtures/minimal/law_policy.json`
- `tools/archsig/tests/fixtures/homotopy_report/law_policy.json`
- `tools/archsig/tests/fixtures/complete_archmap_acceptance/law_policy.json`

These fixtures are locked against the legacy static Rust builder, and the
schema catalog records both `law-policy-v0` and
`law-policy-validation-report-v0`. The v1 path uses `law-policy/v1`; the legacy
schema names remain here only to document old profile content.

`complete_archmap_acceptance/law_policy.json` is the sanitized acceptance
profile for complete-first authoring. Its spectrum and homotopy reading
boundaries validate without warnings and are exercised by the ArchSig CLI test
against the sanitized large-repo class ArchMap fixture.
