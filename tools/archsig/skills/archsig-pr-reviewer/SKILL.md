---
name: archsig-pr-reviewer
description: Run ArchSig lightweight PR review from base ArchMap v1, base-branch-derived PR-local archmap-delta-v0, and LawPolicy v1; read archsig-pr-review-report-v1 outputs; and turn the report into bounded source-first review questions. Use when Codex is asked to prepare, run, interpret, or automate ArchSig PR review for a pull request.
---

# ArchSig PR Reviewer

## Purpose

Run ArchSig's lightweight PR review surface and turn the JSON report into
bounded review focus.

`pr-review` is change-local. It reads:

- base `archmap/v1`
- optional head `archmap/v1`
- optional intermediate path `archmap/v1` snapshots
- PR-local `archmap-delta-v0`
- required `law-policy/v1`

It does not read raw diff, v0 analysis packets, FieldSig forecasts, CI status,
or GitHub approval state. No LawPolicy, no ArchSig judgement.

This skill must work with only:

- a built `archsig` executable
- this skill directory
- the user's base ArchMap, LawPolicy, PR/base branch diff, and repository
  evidence

Do not require the ArchSig source repository, test fixtures, Cargo project
files, or AAT mathematical docs at runtime. The user's PR diff may come from
local Git history, GitHub PR metadata, or a supplied base/head file list.

## References

This skill is designed for release bundles where only the binary and skills are
available. Load these references as needed:

- `references/release-runtime.md`: release-only runtime assumptions, binary
  resolution, required artifacts, and stop conditions.
- `references/source-diff-to-delta.md`: how to derive `archmap-delta-v0` from
  the base branch diff.
- `references/pr-review-report-guide.md`: how to read
  `archsig-pr-review-report-v1` without source repository docs.
- `references/human-review-guide.md`: how to turn the report and source
  inspection into human code-review language.
- `../archmap-creater/references/mapping-guide.md`,
  `../archmap-creater/references/schema-cheatsheet.md`, and
  `../archmap-creater/references/examples.md`: atom observation boundaries to
  read when the PR introduces new architectural facts or when a delta item
  cannot be mapped confidently to the base ArchMap.

## Inputs

Collect:

- repository root or selected source paths for source comparison
- base ArchMap path, usually `.archsig/<scope>/archmap.json`
- optional head ArchMap path, usually `.archsig/<scope>/head.archmap.json`
- optional intermediate ArchMap path snapshots for hidden-excursion review
- base branch or merge base ref, such as `origin/main...HEAD`
- PR-local delta output path, usually `.archsig/pr-review/archmap_delta.json`
- LawPolicy path, usually `.archsig/<scope>/law_policy.json`
- output path, usually `.archsig/pr-review/archsig-pr-review.json`
- PR context: changed files, branch, issue/PR summary, reviewer concerns, and
  any unavailable private evidence

Required stop conditions:

- If the base ArchMap does not exist, stop. Do not invent one inside this PR
  review skill; use `archmap-creater` first.
- If the LawPolicy does not exist, stop. Do not run PR review with a generic or
  implied policy; use `law-policy-creater` first.
- If the base branch / merge-base diff cannot be determined or supplied, ask for
  that diff boundary before authoring the delta.

Always create the PR-local `archmap-delta-v0` from the base branch difference
for the current PR review. An existing delta can be used only as a draft to
compare against the fresh base-branch-derived delta; do not trust stale delta
files silently. Do not pass raw diff directly to `archsig pr-review`.

In release-only environments, read `references/release-runtime.md` before
assuming any repository-local ArchSig paths, fixtures, or docs exist.

Required procedure:

1. Check that the base ArchMap exists and has `schema: "archmap/v1"`. If it
   does not, stop.
2. Create the PR-local `archmap-delta-v0` from the base branch difference.
3. Check that the LawPolicy exists and has `schema: "law-policy/v1"`. If it
   does not, stop.
4. If the PR introduces new observations, either refine the ArchMap first or
   supply a head ArchMap that contains the PR-local facts.
5. Run `archsig pr-review` with the base ArchMap, optional head / path
   ArchMaps, freshly created delta, and LawPolicy.

## ArchMap Delta Authoring

For non-trivial PRs, read `references/source-diff-to-delta.md` before drafting
the delta.

`archmap-delta-v0` records which existing or PR-local ArchMap observations are
touched by the pull request, as read from the base branch difference. It is not
a parser output, merge-safety claim, or semantic diff proof.

Build the delta in this order:

1. Determine the base diff boundary from PR metadata or the user, such as
   `origin/main...HEAD`.
2. List changed files from the base branch diff.
3. Inspect the changed files and nearby source/docs/tests needed to understand
   the architectural facts touched by the PR.
4. Resolve touched facts to base ArchMap observation refs.
5. Write only those refs into `changedObservationRefs[]`.
6. Put the diff-derived files, symbols, docs, or tests in
   `reviewIntent.sourceFirstTargets[]`.

Minimal shape:

```json
{
  "schemaVersion": "archmap-delta-v0",
  "deltaId": "delta:<short-pr-scope>",
  "baseSnapshotRef": "archmap-snapshot:<scope>:base",
  "headSnapshotRef": "archmap-snapshot:<scope>:head",
  "changedObservationRefs": [
    "atom:<family>:<id>"
  ],
  "changeLocalBoundary": "PR review delta records ArchMap-level observations, not raw source diff semantics",
  "reviewIntent": {
    "summary": "Short source-grounded description of the PR-local change.",
    "expectedReviewAxes": [],
    "sourceFirstTargets": []
  },
  "nonConclusions": [
    "ArchMapDelta is not a language parser output guarantee",
    "delta evidence is not merge safety"
  ]
}
```

Delta authoring rules:

- Resolve every `changedObservationRefs[]` entry against the base ArchMap or a
  clearly marked PR-local ArchMap observation.
- Derive `changedObservationRefs[]` from the base branch difference, not from
  remembered context or an old report.
- Prefer a small review set: touched authority, state, effect, trust, contract,
  relation, and semantic observations.
- Put changed file paths or symbols in `reviewIntent.sourceFirstTargets[]`.
- Put expected LawPolicy axes in `reviewIntent.expectedReviewAxes[]` only when
  source evidence or repo policy supports them.
- Preserve unavailable or private evidence as boundary text; do not turn missing
  evidence into measured absence.
- If the PR creates new architectural facts that the base ArchMap does not
  contain, update/refine the ArchMap with `archmap-creater` first or mark the
  delta as PR-local and report the unresolved base-map gap.

## Run Workflow

Resolve the ArchSig binary before running:

1. use `ARCHSIG_BIN` when the environment variable is set
2. use `archsig` from `PATH`
3. look for released binaries near the skill bundle, such as `bin/archsig`,
   `../bin/archsig`, or `../../bin/archsig`
4. if working inside a source checkout, optionally use an already-built checkout
   binary such as `tools/archsig/target/release/archsig` or
   `tools/archsig/target/debug/archsig`

Before running, verify the JSON inputs have these schema values:

- base ArchMap: `schema: "archmap/v1"`
- delta ArchMap: `archmap-delta-v0`
- LawPolicy: `schema: "law-policy/v1"`

Run:

```bash
ARCHSIG_BIN=${ARCHSIG_BIN:-archsig}

"$ARCHSIG_BIN" pr-review \
  --base-archmap <archmap.json> \
  --after-archmap <optional-head-archmap.json> \
  --path-archmap <optional-intermediate-archmap.json> \
  --delta-archmap <archmap_delta.json> \
  --law-policy <law_policy.json> \
  --out <archsig-pr-review.json>
```

Omit `--after-archmap` and `--path-archmap` for base-only review. If
`--path-archmap` is supplied, `--after-archmap` is required so endpoint
movement is bounded.

If no binary exists, stop and ask for the binary path. Do not require Cargo or
the ArchSig source tree in a released skill-only environment.

## Reading Workflow

For field-level guidance, read `references/pr-review-report-guide.md`.

Read the `archsig-pr-review-report-v1` in this order:

1. `canonicalInputs`
   - Confirm the paths and schema versions are the intended base ArchMap,
     optional head / path ArchMaps, PR-local delta, and LawPolicy.
   - If the wrong LawPolicy was used, stop and rerun with the selected policy.

2. `typedEvaluatorSummary`
   - Treat `measuredPass`, `measuredViolation`, `blocked`, `unknown`, and
     `unmeasured` as evaluator statuses, not as raw diff verdicts.
   - Missing support is not measured zero.

3. `v1Analysis`
   - Read the base snapshot first, then optional after / path snapshots.
   - Use `packetRef`, `structuralPacketRefs`, `structuralReadingRefs`,
     `distanceDiagnosis`, and `detailIndexSummary` as report-local navigation
     refs.
   - Do not treat report-local packet refs as proof objects.

4. `deltaPacketRefIntersections`
   - Confirm every `changedObservationRefs[]` entry intersects at least one
     base / after / path typed or derived packet ref.
   - Treat `blockedByMissingPacketRefIntersection` as a review blocker or
     ArchMap refinement cue, not as a measured absence.

5. `prStructuralDiagnosis`
   - Read endpoint architecture-distance movement when an after ArchMap is
     supplied.
   - Read total path movement and hidden-excursion boundary only over supplied
     path snapshots.
   - Treat safe-change budget as a review cue. It is not merge approval,
     incident forecast, or repair safety.

6. `typedEvaluatorResults`
   - Read support atom refs, support molecule refs, basis refs, detail refs,
     and status reasons.
   - Keep selected evaluator scope as the review lens, not global architecture
     truth.

7. `reviewFocus`
   - Use detail refs and changed source targets to decide which source files
     need human review.

Before writing a human-facing review, read
`references/human-review-guide.md`. It explains how to translate the report
into reviewer-facing code questions without exposing AAT or ArchSig internal
representation as the answer.

## Source-First Review

Always compare report focus against source evidence before telling the user what
to change.

Recommended review queue:

- changed observations with `matched: true`
- unmatched changed refs that look important to the PR goal
- policy-matched laws and axes
- source targets from `reviewIntent.sourceFirstTargets[]`
- coverage or boundary text that blocks a confident reading

For each item, classify it as:

- supported by source comparison
- partially supported / needs more evidence
- stale or contradicted by current source
- unavailable because evidence is private, generated, dynamic, or out of scope

Do not hand the raw ArchSig diagnosis to a human reviewer as the final answer.
Use ArchSig to choose what to read, then report what the code evidence supports.

## Output Shape

For a normal user report, answer in this order:

1. Run result and artifact path
2. Input and schema status
3. Plain-language PR summary
4. Human review focus
5. Source comparison findings
6. Suggested PR comments or next checks
7. Claim boundary / non-conclusions

Use concise Japanese when working in this repository.

Recommended phrasing:

- "このPRは主に ... を変更しています。"
- "ArchSig はレビュー対象を絞るために使いました。実際に読むべき箇所は..."
- "コードを読む限り、この懸念は supported / partially supported / not supported です。"
- "この LawPolicy match は違反証明ではなく、確認すべきレビュー観点です。"

Avoid:

- "ArchSig approved/rejected the PR"
- "This proves the PR is safe/unsafe"
- "No risk exists because no law matched"
- "The raw diff was analyzed by ArchSig"
- "FieldSig forecast says..."
- exposing raw AAT / ArchSig labels when ordinary code-review language is
  clearer

## Maintainer Validation

When editing this skill inside a source checkout, smoke-test the command with
the bundled fixtures:

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- pr-review \
  --base-archmap tools/archsig/tests/fixtures/archmap_v1/archmap.json \
  --after-archmap tools/archsig/tests/fixtures/archmap_v1/archmap_violation.json \
  --path-archmap tools/archsig/tests/fixtures/archmap_v1/archmap.json \
  --delta-archmap tools/archsig/tests/fixtures/pr_review/archmap_delta_v1_refs.json \
  --law-policy tools/archsig/tests/fixtures/archmap_v1/law_policy.json \
  --out .tmp/archsig-pr-reviewer-validation.json
```

Then confirm the output has `schemaVersion: "archsig-pr-review-report-v1"` and
`reviewKind: "v1-output-replacement-structural-pr-review"` and does not
contain a raw-diff input field.
These are maintenance checks, not runtime requirements for released skill users.
