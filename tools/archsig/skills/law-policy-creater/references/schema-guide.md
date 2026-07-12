# LawPolicy Schema Guide

LawPolicy is a selector over ArchSig evaluator registry entries. The AG
measurement path also uses LawPolicy to select a first-class MeasurementProfile.

## Root

```json
{
  "schema": "law-policy/v0.5.1",
  "id": "policy-id",
  "lawSurfaceRef": "law-surface:ag-default-v051",
  "measurementProfileRef": "profile:ag-default@1",
  "basisLedger": [],
  "policies": []
}
```

Unknown root fields fail validation. `lawSurfaceRef` is required and must match
the id of the supplied law-equation-surface.

## Basis Ledger

Every `policies[].basis` entry must resolve to `basisLedger[].basisId`.
ArchSig checks only ledger resolution and field shape. It does not check that a
declared `path` exists.

```json
{
  "basisId": "policy-basis:layering",
  "kind": "repo-document",
  "path": "docs/aat/algebraic_geometric_theory/README.md",
  "revision": "aat-ag-current"
}
```

## Policy Entry

Use individual evaluator selectors. Pack selectors are not part of the current
authoring surface.

```json
{
  "law": "surface:cech-surface-v051",
  "evaluator": "ag.cech-obstruction",
  "basis": ["policy-basis:layering"],
  "scope": ["domain."],
  "severity": "error"
}
```

`policies[].profileRef` is reserved for multi-profile selection and fails closed
when present.

## Known Built-In Selectors

Evaluator ids:

- `ag.cech-obstruction`
- `ag.coherence-obstruction`
- `ag.restriction-compatibility`
- `ag.section-factorization`
- `ag.boundary-residue`
- `ag.square-free-repair`
- `ag.law-conflict-tor`
- `ag.sheaf-laplacian`
- `ag.period-stokes`
- `ag.period-stokes-audit`
- `ag.support-transfer`
- `ag.saga-descent`

## MeasurementProfile

AG evaluator selectors require `measurementProfileRef` resolving to the
external `--measurement-profile` artifact's `profileId`.

```json
{
  "schema": "measurement-profile/v0.5.1",
  "profileId": "profile:ag-default@1",
  "siteRef": "archmap:/contexts",
  "coverRef": "cover:<archmap-cover-id>",
  "coefficient": "F2",
  "effCoeff": "finite-linear-algebra@1",
  "resolutionSelector": "taylor@1",
  "domain": "finite-poset-site",
  "zeroPredicate": "rank-zero@1",
  "nonZeroPredicate": "rank-positive@1",
  "certSelector": "finite-certificate@1",
  "verdictDiscipline": "five-valued-structural-verdict@1",
  "finiteBounds": {
    "maxSquareFreeWitnessVariables": 12,
    "maxCoherenceContexts": 12,
    "maxTorWitnessVariables": 12,
    "maxBoundaryResidueVariables": 16,
    "maxLaplacianCells": 16,
    "maxPeriodCycles": 16,
    "maxTransferTargets": 16
  }
}
```

Rules:

- `siteRef` normally points to `archmap:/contexts`.
- `coverRef` must name a cover in the ArchMap v2 input; replace
  `cover:<archmap-cover-id>` before running `analyze`.
- `verdictDiscipline` must be `five-valued-structural-verdict@1`.
- Witness variables are declared in the referenced `law-equation-surface`; a
  measurement-profile must not contain `witnessFamily`.
- `finiteBounds` can only lower the registry hard caps shown above. Cap
  exceedance fails validation.
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
- policy pack selectors
- legacy spectrum-profile fields
- `homotopyMeasurementProfile`
- `coverageRequirements`
- `exactnessAssumptions`
- `measurementProfile` as a root object
- embedded `measurementProfiles[]`
- custom AG evaluator fields inside LawPolicy

ArchSig evaluator registry owns witness requirements, axes, missing blocker
rules, distance contribution, and result status computation. MeasurementProfile
owns selected cover, coefficient, predicates, certificate
selector, and verdict discipline for AG measurement.
