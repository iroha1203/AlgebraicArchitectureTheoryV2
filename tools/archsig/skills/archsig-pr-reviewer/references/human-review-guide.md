# Human Review Guide

Use this guide after `archsig pr-review` emits
`archsig-pr-review-report/v0.5.0`, before writing a human-facing review.

The goal is to turn ArchSig output into concrete review work:

- what changed
- which project rules or boundaries may matter
- which files to read
- what the reviewer should verify
- what the code evidence actually supports

Do not explain AAT, obstruction circuits, signature axes, flatness, or internal
ArchSig representation unless the user explicitly asks. Human reviewers need a
source-grounded review note, not a theory lecture.

## Review Translation Workflow

1. Start from the PR goal.
   - Read the PR title/body, issue link, changed file list, and delta
     `reviewIntent.summary`.
   - Write one plain sentence: "This PR appears to change..."

2. Read ArchSig as a triage signal.
   - Use `changedObservations[]` to identify the architectural facts that may
     be touched.
   - Use `policyMatchedLaws[]` to identify project rules or boundaries that may
     need review.
   - Use `sourceTargets[]` and `reviewIntent.sourceFirstTargets[]` to build the
     file-reading queue.
   - Treat unmatched observations as map/delta coverage gaps, not accusations.

3. Read code before judging.
   - Inspect the changed files first.
   - Then inspect nearby callers, callees, tests, policy docs, or config that
     decide whether the concern is real.
   - If source evidence is missing, say what evidence is missing.

4. Write findings in reviewer language.
   - Prefer "please verify..." or "this change appears to move..." over
     ArchSig-internal labels.
   - Tie every concern to file paths, functions, contracts, tests, or policy
     docs.
   - Separate confirmed issues from follow-up checks.

5. Preserve the boundary.
   - ArchSig PR review is not merge approval.
   - A matched LawPolicy law is a review question, not a violation proof.
   - A missing match is not proof of safety.

## Output Pattern

Use this structure for a normal human-facing review:

1. Summary
   - One or two sentences about what the PR changes.

2. Review focus
   - Two to five bullets describing what a human should inspect.
   - Each bullet should name files, code paths, tests, docs, or runtime evidence.

3. Source findings
   - Confirmed by code: items supported by source inspection.
   - Needs verification: items that require tests, traces, owner input, or docs.
   - Not supported / stale: report items contradicted by current source.

4. Suggested PR comments
   - Draft only comments that a reviewer could reasonably leave on the PR.
   - Keep comments actionable and specific.

5. Boundary
   - One short sentence such as: "ArchSig was used as review triage; the final
     judgement depends on the code and tests above."

## Translation Rules

Translate ArchSig fields into reviewer concepts:

| ArchSig field | Human-facing reading |
| --- | --- |
| `changedObservationRefs[]` | The architectural facts this PR may touch |
| `matched: true` in `changedObservations[]` | This delta item matched the base map and can be checked against source |
| `matched: false` | The map or delta may need updating before this concern is reliable |
| `changedAtomFamilies[]` | The kind of code boundary touched, such as state, effect, authority, trust, relation, or contract |
| `policyMatchedLaws[]` | Project rules that should guide review |
| `policyMatchedAxisRefs[]` | Review dimensions selected by policy; do not show raw axis ids unless useful |
| `sourceTargets[]` | Start reading here |
| `evidenceBoundary` | What ArchSig did and did not inspect |

When explaining `changedAtomFamilies[]`, use ordinary code-review wording:

- `authority`: permission, ownership, tenancy, or role checks
- `state`: persisted state, lifecycle status, cache, or config
- `effect`: writes, messages, jobs, external calls, or side effects
- `trust`: external input, provider output, tokens, webhooks, or delegated data
- `contractSpecification`: input/output shape, validation, invariants, error
  behavior, idempotency, or retry expectations
- `relation`: dependency, call path, import, ownership, or data flow
- `semantic`: domain meaning, workflow meaning, or business-rule interpretation

## Review Comment Style

Good:

- "This PR changes the create-user route and service contract. Please verify
  that validation still happens before the write path and that the existing
  error-shape tests cover the new branch."
- "ArchSig matched this change against the project boundary policy, so I read
  `src/routes/users.ts` and `src/services/user-service.ts`. The policy concern
  is supported: the route now owns part of the service contract."
- "The delta references an observation that does not exist in the base map. The
  review should update the ArchMap or remove this PR-review item before treating
  it as an architecture concern."

Avoid:

- "This PR has an obstruction circuit."
- "The signature axis is nonzero, so the PR is unsafe."
- "ArchSig proves this violates the architecture."
- "No policy matched, so this PR is safe."
- "AAT says this must be refactored."

## Severity Guidance

Use normal code-review severity, not ArchSig-internal intensity:

- Blocking: source evidence shows the PR breaks a selected project rule,
  security/authority boundary, data integrity rule, or required contract.
- Needs change: source evidence supports a likely maintainability or boundary
  problem, but the PR can be fixed locally.
- Needs verification: the signal is plausible but requires tests, traces, docs,
  owner confirmation, or a map/policy update.
- Informational: the report helps reviewers inspect the change but does not
  justify a requested code change.

When in doubt, downgrade to "needs verification" and say what evidence would
settle the question.
