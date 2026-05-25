---
name: arch-pr-analyzer
description: Analyze PR or CI architecture quality from ArchSig, ArchMap, AIR, theorem-check, feature-report, policy, signature diff, and pr-quality-analysis artifacts. Use when Codex is asked to review a PR's architecture impact, inspect CI architecture reports, explain current architecture state for a change, or recommend bounded PR review actions.
---

# Arch PR Analyzer

## Purpose

Analyze PR / CI architecture evidence and produce review cues. This skill simplifies ArchSig's PR surface for Codex: it may run the necessary `archsig` commands, read generated artifacts, and explain architecture risks without treating tool output as merge approval, Lean proof, global architecture truth, or causal diagnosis.

## Inputs To Prefer

- `signature-diff-report-v0`
- Sig0 and validation reports
- `archmap-v0` and `archmap-validation-report-v0`
- AIR, AIR validation, theorem-check, feature-report
- `aat-observable-bundle-v0` and validation report when the PR review asks for AAT concept coverage
- `architecture-policy-v0` and `law-violation-report-v0`
- policy-decision and PR comment summary
- `pr-quality-analysis-report-v0`
- `sft-review-summary-v0` only when the user asks for SFT review judgement or future-impact review

Do not use IntentMap, AlignmentMap, or planning forecast artifacts for PR merge review unless the user explicitly asks for planning context.

## Minimal Execution Rules

- Use `${ARCHSIG_BIN:-archsig}` by default.
- Keep generated files under `.archsig/` unless the user specifies another directory.
- If `${ARCHSIG_BIN:-archsig} --help` fails, ask for `ARCHSIG_BIN=/path/to/archsig`.
- Stop downstream commands after an upstream failure.
- Do not require the ArchSig source repository.

## Workflow

1. Establish the PR evidence boundary.
   - Identify before / after revisions, supplied artifacts, missing artifacts, private refs, unmeasured axes, and non-conclusions.
   - Read `references/pr-analysis-playbook.md` for non-trivial PR review.
   - Read `references/artifact-reading-guide.md` when artifact meaning is unclear.

2. Generate missing PR artifacts when appropriate.

```bash
${ARCHSIG_BIN:-archsig} --root . --out .archsig/signature/current/sig0.json

${ARCHSIG_BIN:-archsig} validate \
  --input .archsig/signature/current/sig0.json \
  --out .archsig/signature/current/validation.json \
  --universe-mode local-only
```

If before / after snapshots are available, use `signature-diff`. If ArchMap-side artifacts are available, validate them and project to AIR:

```bash
${ARCHSIG_BIN:-archsig} archmap \
  --input .archsig/archmap/archmap.json \
  --out .archsig/archmap/validation.json

${ARCHSIG_BIN:-archsig} air-from-archmap \
  --archmap .archsig/archmap/archmap.json \
  --validation .archsig/archmap/validation.json \
  --out .archsig/archmap/air.json

${ARCHSIG_BIN:-archsig} theorem-check \
  --air .archsig/archmap/air.json \
  --out .archsig/archmap/theorem-check.json

${ARCHSIG_BIN:-archsig} feature-report \
  --air .archsig/archmap/air.json \
  --out .archsig/archmap/feature-report.json
```

If a project-local law policy is supplied, validate it and evaluate Layered Architecture findings:

```bash
${ARCHSIG_BIN:-archsig} architecture-policy \
  --input .archsig/policy/architecture-policy.json \
  --out .archsig/policy/architecture-policy-validation.json

${ARCHSIG_BIN:-archsig} law-violation-report \
  --sig0 .archsig/signature/current/sig0.json \
  --policy .archsig/policy/architecture-policy.json \
  --out .archsig/policy/law-violation-report.json
```

Validate supplied PR quality report when present:

```bash
${ARCHSIG_BIN:-archsig} pr-quality-analysis \
  --input .archsig/pr/pr-quality-analysis-report.json \
  --out .archsig/pr/pr-quality-analysis-validation.json
```

Validate supplied AAT observable bundle when the review asks for invariant / witness / operation /
theorem-boundary coverage:

```bash
${ARCHSIG_BIN:-archsig} aat-observable-bundle \
  --input .archsig/aat/aat-observable-bundle.json \
  --out .archsig/aat/aat-observable-bundle-validation.json
```

If an SFT review judgement artifact is supplied, validate it separately from deterministic PR quality analysis:

```bash
${ARCHSIG_BIN:-archsig} sft-review-summary \
  --input .archsig/sft/sft-review-summary.json \
  --out .archsig/sft/sft-review-summary-validation.json
```

3. Produce the review.
   - Separate measured zero from unmeasured.
   - Separate warning, failure, missing evidence, and negative evidence.
   - Treat Layered Architecture `deterministicViolations[]` as deterministic over resolved selectors and measured edges.
   - Treat SRP `semanticRole` / `responsibilityRegions` / `reasonToChange` / `lawRefs` as evidence for LLM judgment, not as tool-only violation.
   - For SRP probable violation, cite both evidence refs and policy refs and distinguish `acceptableOrchestrator`, `allowedException`, and `unmeasured`.
   - Tie each finding to artifact ids or paths.
   - When using `aat-observable-bundle-v0`, translate `reviewActions` into evidence gap,
     blocked formal claim, review guardrail, or next evidence without treating LLM judgment as proof.
   - When using `sft-review-summary-v0`, report opened futures, closed futures, boundary failures,
     and next actions with evidence refs. Do not treat the summary status as merge approval.
   - Keep recommendations bounded to PR review actions.

## Output Shape

```text
PR architecture state
- ...

Review cues
- ...

Evidence gaps
- ...

Recommended next actions
- ...

SFT review judgement
- opened futures:
- closed futures:
- boundary failures:
- next actions:

Non-conclusions
- ...
```

Use Japanese for user-facing reports in this repository, unless the user asks otherwise.
