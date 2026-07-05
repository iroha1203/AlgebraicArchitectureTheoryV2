---
name: law-policy-creater
description: Create and validate ArchSig law-policy/v0.5.0 selector artifacts, including AG measurement MeasurementProfile v1 selection. Use when Codex is asked to draft, update, or review a LawPolicy, select evaluator packs such as solid, select AG evaluators such as ag.cech-obstruction, attach measurementProfileRef/measurementProfiles, or prepare a project-specific policy before running ArchMap through ArchSig.
---

# LawPolicy Creater

## Purpose

Create `law-policy/v0.5.0` as an evaluator selector for ArchSig. For the current
AG measurement path, the same `law-policy/v0.5.0` document also carries
`measurementProfileRef` and `measurementProfiles[]` to select
`measurement-profile/v0.5.0`.

LawPolicy v1 selects policies, evaluator ids, policy packs, basis refs, scope,
severity, and optional first-class profile refs. It is not a DSL. It does not
contain ad hoc witness rules, signature axes, coverage requirements, exactness
assumptions, distance formulas, legacy distance-profile fields, spectrum profiles, or
homotopy profiles. Calculation rules belong to the ArchSig evaluator registry.
AG measurement coordinates belong to `MeasurementProfile`, not to custom
LawPolicy fields.

Changing LawPolicy changes which evaluator manifests ArchSig runs. It does not
prove architecture lawfulness, Atom truth, semantic correctness, zero
curvature, or Lean theorem discharge.

## Inputs

Collect:

- target repository root and scope
- intended LawPolicy path, usually `.archsig/<scope>/law_policy.json`
- ArchMap v2 path if available for AG measurement, or ArchMap v1 path only for
  the bounded legacy structural path
- repository docs, coding standards, ADRs, review policy, or direct user decisions
- whether the user wants a pack such as `solid` or individual evaluator ids
- for AG measurement: ArchMap v2 cover id, coefficient, EffCoeff procedure,
  witness family, resolution selector, domain, zero/nonzero/cert predicates,
  and verdict discipline

If no output path is supplied, prefer `.archsig/<scope>/law_policy.json`.

## Authoring Workflow

1. Define scope.
   - Scope is an array of source prefixes or project slices.
   - Keep it narrow enough that the policy is defensible.

2. Select policies.
   - Use a registry pack when the repo/user adopts a known family, for example `solid`.
   - Use individual `law` + `evaluator` entries for project-specific rules.
   - For AG measurement, use explicit AG evaluator ids such as
     `ag.cech-obstruction`, `ag.square-free-repair`,
     `ag.law-conflict-tor`, `ag.sheaf-laplacian`,
     `ag.period-stokes`, or `ag.support-transfer`.
   - Do not invent evaluator ids. Unknown evaluator ids fail validation.

3. Attach basis refs.
   - Basis refs must be registry-known, such as `policy-basis:solid` or `policy-basis:layering`.
   - Basis refs explain why the policy is selected. They are not proof objects.

4. Set severity.
   - Use severity as triage metadata.
   - Severity does not change witness rules, measured status, or distance formulas.

5. Validate.
   - Run `archsig law-policy --input <law_policy.json> --out <law-policy-validation.json>`.
   - Unknown pack, unknown evaluator, unresolved basis, unresolved
     `measurementProfileRef`, missing AG profile, DSL fields, and legacy v0
     fields must fail.

6. Run ArchSig when ArchMap is available.
   - Run `archsig analyze --archmap <archmap.json> --law-policy <law_policy.json> --out-dir <out>`.
   - Use `--strict-distance` to reject blocked / unknown / unmeasured typed distance.

## Schema Shape

```json
{
  "schema": "law-policy/v0.5.0",
  "id": "project-policy",
  "policies": [
    {
      "pack": "solid",
      "basis": ["policy-basis:solid"],
      "scope": ["src."],
      "severity": "review"
    }
  ]
}
```

Individual evaluator selector:

```json
{
  "schema": "law-policy/v0.5.0",
  "id": "domain-layering",
  "policies": [
    {
      "law": "domain.no-direct-infra-dependency",
      "evaluator": "domain.no-direct-infra-dependency",
      "basis": ["policy-basis:layering"],
      "scope": ["domain."],
      "severity": "error"
    }
  ]
}
```

AG measurement selector:

```json
{
  "schema": "law-policy/v0.5.0",
  "id": "ag-measurement-policy",
  "measurementProfileRef": "profile:ag-default@1",
  "measurementProfiles": [
    {
      "schema": "measurement-profile/v0.5.0",
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
  ],
  "policies": [
    {
      "law": "ag.cech-obstruction",
      "evaluator": "ag.cech-obstruction",
      "basis": ["policy-basis:layering"],
      "scope": ["src/"],
      "severity": "high"
    }
  ]
}
```

The runtime schema name is still `law-policy/v0.5.0`; AG measurement support is
expressed by first-class profile fields rather than by a separate LawPolicy
schema discriminator. Replace placeholder `coverRef` and `witnessFamily`
values with refs selected from the actual ArchMap / profile decision before
running `analyze`.

## Do Not Generate

- `selectedLaws`
- `requiredZeroAxes`
- `optionalAxes`
- `witnessRules`
- `moleculePatterns`
- legacy obstruction-circuit definition fields
- legacy signature-axis definition fields
- `measurementPolicy`
- legacy distance-profile fields
- legacy spectrum-profile fields
- `homotopyMeasurementProfile`
- `coverageRequirements`
- `exactnessAssumptions`
- arbitrary custom evaluator DSL fields
- `measurementProfile` as a single object; use `measurementProfiles[]` plus
  `measurementProfileRef`
- theorem-candidate flags that create structural verdicts

## Commands

```bash
${ARCHSIG_BIN:-archsig} law-policy \
  --input <law_policy.json> \
  --out <law-policy-validation.json>

${ARCHSIG_BIN:-archsig} analyze \
  --archmap <archmap.json> \
  --law-policy <law_policy.json> \
  --out-dir <out-dir> \
  --strict-distance
```

If no binary exists, report that validation was not performed.

## Output Shape

When delivering a LawPolicy, include:

1. LawPolicy path
2. source evidence or user decision used for each policy
3. selected pack/evaluator ids
4. measurement profile id and selected cover when AG evaluators are used
5. basis refs
6. scope and severity
7. validation result
8. optional analyze output directory and verdict

Use concise Japanese when working in this repository.

## References

- `references/schema-guide.md`: v1 selector schema and AG MeasurementProfile shape
- `references/convention-survey.md`: finding policy evidence
- `references/question-bank.md`: questions when policy evidence is missing
- `references/starter_law_policy.json`: AG starter template
