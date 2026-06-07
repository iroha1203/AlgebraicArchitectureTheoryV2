---
name: law-policy-creater
description: Create and validate ArchSig law-policy/v1 selector artifacts from repository architecture policies and user decisions. Use when Codex is asked to draft, update, or review a LawPolicy for ArchSig v1, select evaluator packs such as solid@1, or prepare a project-specific policy before running ArchMap through ArchSig.
---

# LawPolicy Creater

## Purpose

Create `law-policy/v1` as an evaluator selector for ArchSig.

LawPolicy v1 selects policies, evaluator ids, policy packs, basis refs, scope,
and severity. It is not a DSL. It does not contain witness rules, signature
axes, coverage requirements, exactness assumptions, distance formulas,
`part4DistanceProfile`, spectrum profiles, or homotopy profiles. Those
calculation rules belong to the ArchSig evaluator registry.

Changing LawPolicy changes which evaluator manifests ArchSig runs. It does not
prove architecture lawfulness, Atom truth, semantic correctness, zero
curvature, or Lean theorem discharge.

## Inputs

Collect:

- target repository root and scope
- intended LawPolicy path, usually `.archsig/<scope>/law_policy.json`
- ArchMap v1 path if available
- repository docs, coding standards, ADRs, review policy, or direct user decisions
- whether the user wants a pack such as `solid@1` or individual evaluator ids

If no output path is supplied, prefer `.archsig/<scope>/law_policy.json`.

## Authoring Workflow

1. Define scope.
   - Scope is an array of source prefixes or project slices.
   - Keep it narrow enough that the policy is defensible.

2. Select policies.
   - Use a registry pack when the repo/user adopts a known family, for example `solid@1`.
   - Use individual `law` + `evaluator` entries for project-specific rules.
   - Do not invent evaluator ids. Unknown evaluator ids fail validation.

3. Attach basis refs.
   - Basis refs must be registry-known, such as `policy-basis:solid` or `policy-basis:layering`.
   - Basis refs explain why the policy is selected. They are not proof objects.

4. Set severity.
   - Use severity as triage metadata.
   - Severity does not change witness rules, measured status, or distance formulas.

5. Validate.
   - Run `archsig law-policy --input <law_policy.json> --out <law-policy-validation.json>`.
   - Unknown pack, unknown evaluator, unresolved basis, DSL fields, and legacy v0 fields must fail.

6. Run ArchSig when ArchMap is available.
   - Run `archsig analyze --archmap <archmap.json> --law-policy <law_policy.json> --out-dir <out>`.
   - Use `--strict-distance` to reject blocked / unknown / unmeasured typed distance.

## Schema Shape

```json
{
  "schema": "law-policy/v1",
  "id": "project-policy",
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

Individual evaluator selector:

```json
{
  "schema": "law-policy/v1",
  "id": "domain-layering",
  "policies": [
    {
      "law": "domain.no-direct-infra-dependency",
      "evaluator": "domain.no-direct-infra-dependency@1",
      "basis": ["policy-basis:layering"],
      "scope": ["domain."],
      "severity": "error"
    }
  ]
}
```

## Do Not Generate

- `selectedLaws`
- `requiredZeroAxes`
- `optionalAxes`
- `witnessRules`
- `moleculePatterns`
- `obstructionCircuitDefinitions`
- `signatureAxisDefinitions`
- `measurementPolicy`
- `part4DistanceProfile`
- `spectrumMeasurementProfile`
- `homotopyMeasurementProfile`
- `coverageRequirements`
- `exactnessAssumptions`
- arbitrary custom evaluator DSL fields

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
4. basis refs
5. scope and severity
6. validation result
7. optional analyze output directory and verdict

Use concise Japanese when working in this repository.

## References

- `references/schema-guide.md`: v1 selector schema
- `references/convention-survey.md`: finding policy evidence
- `references/question-bank.md`: questions when policy evidence is missing
- `references/starter_law_policy.json`: v1 starter template
