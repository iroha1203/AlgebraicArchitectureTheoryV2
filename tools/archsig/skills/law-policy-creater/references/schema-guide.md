# LawPolicy v1 Schema Guide

LawPolicy v1 is a selector over ArchSig evaluator registry entries. The AG
measurement path also uses LawPolicy v1 to select a first-class
MeasurementProfile.

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
- `ag.cech-obstruction@1`
- `ag.coherence-obstruction@1`
- `ag.restriction-compatibility@1`
- `ag.section-factorization@1`
- `ag.boundary-residue@1`
- `ag.square-free-repair@1`
- `ag.law-conflict-tor@1`
- `ag.sheaf-laplacian@1`
- `ag.period-stokes@1`
- `ag.period-stokes-audit@1`
- `ag.support-transfer@1`

Basis refs:

- `policy-basis:solid`
- `policy-basis:layering`

## MeasurementProfile v1

AG evaluator selectors require `measurementProfileRef` resolving to
`measurementProfiles[].profileId`.

```json
{
  "schema": "measurement-profile/v1",
  "profileId": "profile:ag-default@1",
  "siteRef": "archmap:/contexts",
  "coverRef": "cover:<archmap-cover-id>",
  "coefficient": "F2",
  "effCoeff": "finite-linear-algebra@1",
  "witnessFamily": [
    {
      "law": "ag.cech-obstruction",
      "variable": "witness:<evaluator-specific-ref>"
    }
  ],
  "resolutionSelector": "taylor@1",
  "domain": "finite-poset-site",
  "zeroPredicate": "rank-zero@1",
  "nonZeroPredicate": "rank-positive@1",
  "certSelector": "finite-certificate@1",
  "verdictDiscipline": "five-valued-structural-verdict@1"
}
```

Rules:

- `siteRef` normally points to `archmap:/contexts`.
- `coverRef` must name a cover in the ArchMap v2 input; replace
  `cover:<archmap-cover-id>` before running `analyze`.
- `verdictDiscipline` must be `five-valued-structural-verdict@1`.
- `witnessFamily[]` entries carry law ids and evaluator-specific witness refs,
  such as square-free variables, cells, cycles, or support targets.
- Algebraic structural profiles commonly use `F2`, `rank-zero@1`,
  `rank-positive@1`, and `finite-certificate@1`; analytic profiles may use
  `R`, `analytic-zero@1`, `analytic-positive@1`, and
  `analytic-reading@1`.
- The profile selects a bounded measurement regime; it does not prove
  U-adequacy, exactness, Leray acyclicity, theorem hypotheses, or source
  extraction soundness.

## Removed v0 Surfaces

Do not emit:

- legacy LawPolicy schema identifiers
- `selectedLaws`
- `requiredZeroAxes`
- `witnessRules`
- legacy obstruction-circuit definition fields
- legacy signature-axis definition fields
- `measurementPolicy`
- legacy distance-profile fields
- legacy spectrum-profile fields
- `homotopyMeasurementProfile`
- `coverageRequirements`
- `exactnessAssumptions`
- `measurementProfile` as a root object
- custom AG evaluator fields outside `measurementProfiles[]`

ArchSig evaluator registry owns witness requirements, axes, missing blocker
rules, distance contribution, and result status computation. MeasurementProfile
owns selected cover, coefficient, witness family, predicates, certificate
selector, and verdict discipline for AG measurement.
