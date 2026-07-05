# PR Review Report Guide

Use this reference when reading `archsig-pr-review-report/v0.5.0`.

The report is a triage artifact. It helps select code-review focus from the
base/head ArchMap, optional intermediate path ArchMaps, PR-local delta, and
LawPolicy. It is not merge approval, a defect proof, a complete diff analysis,
or a FieldSig forecast.

## Top-Level Fields

| Field | Meaning | Reviewer action |
| --- | --- | --- |
| `schema` | Report schema. Must be `archsig-pr-review-report/v0.5.0`. | Stop if different. |
| `canonicalInputs` | Paths, ids, and schema versions of base/head/path ArchMaps, delta, and LawPolicy. | Confirm the intended artifacts were used. |
| `typedEvaluatorSummary` | Base snapshot evaluator status counts. | Check whether selected support is measured, blocked, unknown, or unmeasured. |
| `v1Analysis` | Report-local base / optional after / optional path v1 analysis snapshots. | Use packet refs, structural refs, and distance diagnosis as navigation evidence. |
| `deltaPacketRefIntersections` | Each delta ref matched against base / after / path typed and derived packet refs. | Build the code-reading queue and report unmatched delta refs as blockers. |
| `prStructuralDiagnosis` | Endpoint movement, total path movement, hidden-excursion boundary, safe-change budget, and review focus refs. | Use as bounded architecture navigation, not approval. |
| `reviewFocus` | Compact refs for changed observations and structural packet refs. | Lead source review with these refs and blockers. |
| `nonConclusions` | What the command did and did not inspect. | Include the boundary in the final note. |

## Reading Order

1. Confirm `schema`.
2. Check `canonicalInputs`:
   - base ArchMap is the intended project/scope
   - head ArchMap is present when PR drift / safe budget readings are expected
   - intermediate path ArchMaps are present only when hidden-excursion movement was supplied
   - delta is the freshly created PR-local delta
   - LawPolicy is the selected project policy
3. Read `typedEvaluatorSummary`:
   - `measuredPass`, `measuredViolation`, `blocked`, `unknown`, and
     `unmeasured` are evaluator statuses, not raw diff verdicts
   - blocked / unknown / unmeasured support is not measured zero
4. Read `v1Analysis`:
   - `base` is always present
   - `after` is present only when a head ArchMap was supplied
   - `path[]` is present only when intermediate ArchMap snapshots were supplied
   - `structuralPacketRefs`, `structuralReadingRefs`, `detailRefs`, and
     `distanceDiagnosis` are report-local navigation refs
5. Read `deltaPacketRefIntersections`:
   - `matchedDerivedPacketRefs`: the delta ref intersects typed / derived
     packet refs in at least one supplied snapshot
   - `blockedByMissingPacketRefIntersection`: review the ArchMap / delta
     coverage before making a source-level claim
   - `snapshotMatches[]`: tells whether the ref was visible in base, after, or
     an intermediate path snapshot
6. Read `prStructuralDiagnosis`:
   - `endpointDistanceMovement`: base/head architecture-distance movement or
     blocked if no head ArchMap was supplied
   - `totalPathMovement`: endpoint-only lower bound or supplied path movement
   - `hiddenExcursionBoundary`: bounded only by supplied path snapshots
   - `safeChangeBudget`: blocked by unmatched delta refs or incomplete typed
     support; otherwise bounded within the selected evidence contract
7. Use `reviewFocus` and `reviewIntent.sourceFirstTargets[]` from the delta as
   the compact review queue.
8. Inspect those source files before making claims.

## Count Interpretation

Use counts conservatively:

- high `changedObservationCount`: review scope may be broad; split by file or
  family
- low or zero `matchedPacketRefCount`: map/delta coverage issue; do not
  overclaim
- nonempty `blockedOrUnmeasuredSupportCount`: safe-change budget is blocked by
  incomplete support
- endpoint movement without path snapshots: hidden excursion remains blocked
- zero source targets in the delta: delta/report is too weak for source-first
  review

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

- using `deltaPacketRefIntersections[]` as violation findings
- hiding unmatched refs instead of reporting map/delta coverage gaps
- showing raw axis ids to human reviewers when a code-review question is clearer
- saying ArchSig analyzed raw diff
- treating CI success or failure as part of the ArchSig report
- claiming no risk when the report has no matches
