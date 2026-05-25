# PR Analysis Playbook

Use this playbook for PR / CI architecture review.

## Decision Table

| User asks for | Primary artifacts | Focus |
| --- | --- | --- |
| "what changed" | signature diff, snapshots | architecture deltas, regressions, improvements, unmeasured deltas |
| "is this PR risky" | signature diff, feature report, policy decision | review cues and evidence gaps |
| "is this ArchMap trustworthy" | ArchMap validation | source refs, conflicts, guardrails, non-conclusions |
| "can this become Lean proof" | theorem-check, ArchMap validation | preconditions and blocked formal claims |
| "current architecture state" | Sig0, validation, ArchMap validation, feature report | measured structure, semantic coverage, unmeasured axes |

## Review Rules

- Treat `pr-quality-analysis-report-v0` as review cue, not merge approval.
- Treat `sft-review-summary-v0` as judgement input. Its status is bounded triage, not approval.
- Treat theorem-check as precondition status, not proof discharge.
- Treat absence of measured violations as inconclusive when important axes are unmeasured.
- Prefer concrete evidence gaps over broad refactor advice.
- Do not use forecast cone language for PR merge review.
- If future-impact review is requested, translate unknown remainder, missing invariant, and boundary failure into next actions with evidence refs.

## Recommendation Strategy

Prioritize:

1. Validation failures that block artifact trust.
2. Missing evidence that could change review outcome.
3. Clear policy or architecture conflicts.
4. Unmeasured high-risk axes.
5. Tests or runtime traces for semantic/runtime claims.
6. Lean proof obligations only when preconditions are close and stable.
