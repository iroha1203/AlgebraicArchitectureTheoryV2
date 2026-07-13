---
name: archsig-pr-reviewer
description: Compare ArchSig base/head measurement runs, apply gate policy, read the changed code, and turn the result into bounded source-first review questions.
---

# ArchSig PR Reviewer

Use this skill when asked to run ArchSig-assisted PR review.

## Inputs

- Base run directory containing `archsig-measurement-packet.json`.
- Head run directory containing `archsig-measurement-packet.json`.
- Gate policy JSON.
- Source diff or PR checkout for human review.
- Prefer an `archsig-policy-bundle/v0.5.2` for both base and head runs when
  the policy, law surface, and profile are intended to remain fixed.

## Workflow

1. Run `archsig analyze` for the base and head contexts when run directories are not already supplied; use `--policy-bundle` when the bundle is supplied and confirm the three component fingerprints.
2. Run `archsig compare --base-run <base> --head-run <head> --out-dir <compare>`.
3. Run `archsig gate --packet <head>/archsig-measurement-packet.json --policy <policy> --comparison <compare>/archsig-comparison-report.json --out <gate-report>`.
4. Read the comparison report, gate report, summary, insight report, and changed source.
5. Write bounded review questions. Do not treat ArchSig output as merge approval, forecast truth, or source-code proof.

## Output

Report:

- gate decision and blocking rules;
- introduced, cleared, and preexisting measurement transitions;
- source evidence checked for each high-priority finding;
- concrete follow-up questions or patch suggestions.
