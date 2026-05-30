# PR Review Report Guide

Use this reference when reading `archsig-pr-review-report-v1`.

The report is a triage artifact. It helps select code-review focus from the
base ArchMap, PR-local delta, and LawPolicy. It is not merge approval, a defect
proof, a complete diff analysis, or a FieldSig forecast.

## Top-Level Fields

| Field | Meaning | Reviewer action |
| --- | --- | --- |
| `schemaVersion` | Report schema. Must be `archsig-pr-review-report-v1`. | Stop if different. |
| `reviewId` | Combined id from base map, delta, and policy. | Use for traceability only. |
| `canonicalInputs` | Paths, ids, and schema versions of the three inputs. | Confirm the intended artifacts were used. |
| `policyBoundary` | LawPolicy requirement and selected policy lens. | Keep the selected policy visible. |
| `changeLocalDiagnosis` | Counts and matched families/axes. | Size the review and detect coverage problems. |
| `changedObservations` | Delta refs matched against the base ArchMap. | Build the code-reading queue. |
| `policyMatchedLaws` | LawPolicy laws related to changed atom families. | Turn into review questions. |
| `sourceTargets` | Source refs attached to changed observations and delta intent. | Start source inspection here. |
| `evidenceBoundary` | What the command did and did not inspect. | Include the boundary in the final note. |

## Reading Order

1. Confirm `schemaVersion`.
2. Check `canonicalInputs`:
   - base ArchMap is the intended project/scope
   - delta is the freshly created PR-local delta
   - LawPolicy is the selected project policy
3. Read `changeLocalDiagnosis`:
   - `changedObservationCount`: size of the delta
   - `matchedBaseObservationCount`: how many refs resolved to base map entries
   - `changedAtomFamilies`: kinds of boundaries touched
   - `policyMatchedLawCount`: how many selected laws are relevant
   - `policyMatchedAxisRefs`: review dimensions selected by policy
   - `sourceTargetCount`: how much source evidence was named
4. Read `changedObservations` and separate matched vs unmatched refs.
5. Read `policyMatchedLaws` and rewrite each as a plain review question.
6. Read `sourceTargets` and inspect those files before making claims.

## Count Interpretation

Use counts conservatively:

- high `changedObservationCount`: review scope may be broad; split by file or
  family
- low `matchedBaseObservationCount`: map/delta coverage issue; do not overclaim
- zero `policyMatchedLawCount`: no selected law matched these atom families; not
  proof of safety
- nonempty `policyMatchedAxisRefs`: selected review dimensions to check in code
- zero `sourceTargetCount`: delta/report is too weak for source-first review

## Human Questions From Report Data

Convert report fields into ordinary review questions:

- `authority`: Does the PR preserve permission, ownership, tenancy, or role
  checks?
- `state`: Does the PR preserve state lifecycle, migrations, persistence, or
  cache invariants?
- `effect`: Does the PR preserve write ordering, side effects, retries, jobs, or
  external calls?
- `trust`: Does the PR validate external input, provider output, tokens,
  webhooks, or delegated authority?
- `contractSpecification`: Does the PR preserve input/output contracts,
  validation, errors, idempotency, or retry semantics?
- `relation`: Does the PR change dependency direction, ownership, call paths,
  or data flow?
- `semantic`: Does the PR change business meaning or workflow interpretation?

If the report names raw ids, translate them into file/function/test language
after reading source.

## Suggested Final Summary

Use this pattern:

```text
ArchSig was used to choose review focus, not to approve the PR.

This PR appears to change <plain-language summary>.

Review focus:
- <file/function>: verify <specific condition>.
- <test/doc/runtime evidence>: check <specific evidence>.

Source findings:
- Supported: <what code confirms>.
- Needs verification: <what evidence is still missing>.
- Not supported/stale: <what report item did not match current source>.

Boundary: the judgement depends on the code and tests above; the PR-review
report is a triage artifact over the selected base ArchMap and LawPolicy.
```

## Common Mistakes

Avoid:

- using `policyMatchedLaws[]` as violation findings
- hiding unmatched refs instead of reporting map/delta coverage gaps
- showing raw axis ids to human reviewers when a code-review question is clearer
- saying ArchSig analyzed raw diff
- treating CI success or failure as part of the ArchSig report
- claiming no risk when the report has no matches
