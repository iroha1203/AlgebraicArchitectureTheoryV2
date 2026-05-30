# Source Diff To Delta

Use this reference when creating the PR-local `archmap-delta-v0` from the base
branch difference.

The delta is a compact review artifact. It says which ArchMap observations the
PR appears to touch. It is not a raw diff, parser result, approval decision, or
complete semantic analysis.

## Inputs

Collect:

- base branch or merge-base range, such as `origin/main...HEAD`
- changed file list and, when available, changed symbols or hunks
- base ArchMap JSON
- PR title/body or issue summary
- user-stated review concerns

If the base branch range is unknown, ask for it before authoring the delta.

## Diff Reading Steps

1. List changed files from the base branch diff.
2. Group them by likely review surface:
   - routes/controllers/API entry points
   - services/use cases/domain logic
   - persistence/models/migrations
   - background jobs/events/messages
   - external providers/webhooks/LLM integrations
   - auth/permissions/tenancy/trust boundaries
   - tests/docs/config
3. Read the changed files. For each surface, identify the architectural fact
   touched by the PR.
4. Search the base ArchMap for observations whose source refs, subject refs,
   object refs, predicates, molecule refs, or semantic refs match the touched
   fact.
5. Add only relevant observation refs to `changedObservationRefs[]`.
6. Put changed files, symbols, tests, docs, and runtime evidence targets in
   `reviewIntent.sourceFirstTargets[]`.
7. Add expected policy axes only when the base ArchMap, LawPolicy, or repo docs
   give a reason.

## Mapping Heuristics

Use these hints to map source changes to ArchMap observations:

| Source change | Likely ArchMap family |
| --- | --- |
| New or changed permission check | `authority` |
| Tenant / owner / visibility condition | `authority` or `trust` |
| Input validation, DTO, error shape, return shape | `contractSpecification` |
| Database write, migration, cache mutation | `state` or `effect` |
| Queue, email, external API call, provider write | `effect` or `trust` |
| Webhook, token, provider output, LLM output | `trust` |
| Import/call path/dependency direction | `relation` |
| Business-rule meaning or workflow interpretation | `semantic` |
| Cross-file responsibility or role composition | molecule observation |

When a change touches a responsibility, look for the primitive observations
behind it first. Molecules and semantic observations can be included, but they
should not replace primitive changed atom refs when those refs exist.

## Delta Quality Rules

Good delta:

- small enough for a reviewer to inspect
- tied to source files changed by the PR
- uses observation refs present in the base ArchMap
- records source targets for human review
- names missing evidence or map gaps explicitly

Bad delta:

- lists every observation in a subsystem
- uses stale refs copied from an old report
- treats a changed file path as proof that every nearby observation changed
- hides new architectural facts by forcing them into unrelated base refs
- turns missing base-map coverage into a claim that nothing changed

## Handling New Facts

If the PR introduces a fact not present in the base ArchMap:

1. Record the source target in `reviewIntent.sourceFirstTargets[]`.
2. Add a short boundary note in `changeLocalBoundary`.
3. Prefer updating the ArchMap with `archmap-creater` before confident review.
4. If the user wants a quick review, mark the item as "needs map update" in the
   human-facing report instead of pretending it matched the base map.

## Minimal Delta Template

```json
{
  "schemaVersion": "archmap-delta-v0",
  "deltaId": "delta:<pr-or-branch-scope>",
  "baseSnapshotRef": "archmap-snapshot:<scope>:base",
  "headSnapshotRef": "archmap-snapshot:<scope>:head",
  "changedObservationRefs": [],
  "changeLocalBoundary": "Derived from base branch diff; records ArchMap-level touched observations, not raw diff semantics or merge safety.",
  "reviewIntent": {
    "summary": "This PR appears to change <plain-language change>.",
    "expectedReviewAxes": [],
    "sourceFirstTargets": []
  },
  "nonConclusions": [
    "ArchMapDelta is not a language parser output guarantee",
    "delta evidence is not merge safety",
    "unchanged observation refs are not proof of unchanged runtime behavior"
  ]
}
```
