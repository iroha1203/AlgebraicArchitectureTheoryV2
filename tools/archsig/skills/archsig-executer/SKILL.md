---
name: archsig-executer
description: Run ArchSig CLI workflows and produce bounded JSON artifacts. Use when Codex is asked to execute ArchSig commands, scan repositories, validate Sig0, ArchMap, IntentMap, or AlignmentMap, create snapshots or signature diffs, project ArchMap or IntentMap x ArchMap alignment to AIR/SFT input, build ForecastConeSkeleton or ConsequenceEnvelope artifacts, create calibration hooks or intent calibration records, run PR quality analysis, or verify the ArchSig tooling pipeline.
---

# ArchSig Executer

## Purpose

Run the deterministic ArchSig artifact pipeline. Generate and validate JSON artifacts, preserve measured vs unmeasured boundaries, and avoid interpreting tool output as proof, causality, or global architecture truth.

## Before Running

- Work from the repository root unless the user specifies another root.
- Keep outputs under `.archsig/` or a user-specified artifact directory.
- Let ArchSig create parent directories through `--out` or `--out-dir`; do not require users to pre-create `.archsig/`.
- Use `${ARCHSIG_BIN:-archsig}` by default, so the skill works with a built executable and does not require the ArchSig source repository.
- If the command surface is unfamiliar, read `references/command-catalog.md`.
- If deciding which pipeline to run, read `references/pipeline-playbook.md`.
- If preparing or finding inputs, read `references/input-output-layout.md`.
- When working inside the ArchSig source repository, `cargo run --manifest-path tools/archsig/Cargo.toml -- <command>` is an acceptable fallback.
- Read `tools/archsig/docs/commands.md` only when the source repository is available and the command surface is unfamiliar.
- Run `cargo test --manifest-path tools/archsig/Cargo.toml` only after changing Rust tooling or fixtures in the source repository.

Check the binary before running a pipeline:

```bash
${ARCHSIG_BIN:-archsig} --help
```

If the binary is missing, ask the user for `ARCHSIG_BIN=/path/to/archsig` or an installed `archsig` on `PATH`.

## Core Pipeline

Use this for repository telemetry and PR-style review artifacts.

```bash
${ARCHSIG_BIN:-archsig} \
  --root . \
  --out .archsig/signature/sig0.json

${ARCHSIG_BIN:-archsig} validate \
  --input .archsig/signature/sig0.json \
  --out .archsig/signature/sig0-validation.json \
  --universe-mode local-only
```

For PR or revision comparison, continue with snapshot and signature diff when before/after artifacts are available:

```bash
${ARCHSIG_BIN:-archsig} snapshot \
  --input .archsig/signature/current/sig0.json \
  --validation-report .archsig/signature/current/validation.json \
  --repo-owner <owner> \
  --repo-name <repo> \
  --revision-sha <sha> \
  --revision-ref <ref> \
  --revision-branch <branch> \
  --scanned-at <iso-utc-time> \
  --out .archsig/signature/current/snapshot.json

${ARCHSIG_BIN:-archsig} signature-diff \
  --before-snapshot .archsig/signature/previous/snapshot.json \
  --after-snapshot .archsig/signature/current/snapshot.json \
  --before-sig0 .archsig/signature/previous/sig0.json \
  --after-sig0 .archsig/signature/current/sig0.json \
  --pr-metadata .archsig/pr-metadata.json \
  --out .archsig/signature/current/diff-report.json
```

## ArchMap Review Pipeline

Use this after `$archmap-creater` has produced or updated an `archmap-v0` artifact.

```bash
${ARCHSIG_BIN:-archsig} archmap \
  --input <archmap.json> \
  --out .archsig/archmap/validation.json

${ARCHSIG_BIN:-archsig} air-from-archmap \
  --archmap <archmap.json> \
  --validation .archsig/archmap/validation.json \
  --out .archsig/archmap/air.json

${ARCHSIG_BIN:-archsig} validate-air \
  --input .archsig/archmap/air.json \
  --out .archsig/archmap/air-validation.json

${ARCHSIG_BIN:-archsig} theorem-check \
  --air .archsig/archmap/air.json \
  --out .archsig/archmap/theorem-check.json
```

Optional review reports:

```bash
${ARCHSIG_BIN:-archsig} feature-report \
  --air .archsig/archmap/air.json \
  --out .archsig/archmap/feature-report.json
```

## ArchMap To SFT Pipeline

Use this when the user asks for ForecastCone, ConsequenceEnvelope, or future evolution artifacts from ArchMap evidence.

```bash
${ARCHSIG_BIN:-archsig} archmap-sft-input \
  --archmap <archmap.json> \
  --out .archsig/archmap/operation-support-estimate.json

${ARCHSIG_BIN:-archsig} forecast-cone-skeleton \
  --operation-support .archsig/archmap/operation-support-estimate.json \
  --out .archsig/archmap/forecast-cone-skeleton.json

${ARCHSIG_BIN:-archsig} consequence-envelope \
  --forecast-cone .archsig/archmap/forecast-cone-skeleton.json \
  --out .archsig/archmap/consequence-envelope-report.json
```

Create calibration hooks only when observed artifact refs are available or the user explicitly asks for a hook skeleton:

```bash
${ARCHSIG_BIN:-archsig} forecast-calibration-hook \
  --out .archsig/sft/forecast-calibration-hook.json
```

## IntentMap Planning Pipeline

Use this when the user asks for Epic / PRD / Spec planning forecast. Do not run PRD-only forecast as
the main result when IntentMap and ArchMap alignment are available.

```bash
${ARCHSIG_BIN:-archsig} intent-map \
  --input .archsig/intent/intentmap.json \
  --out .archsig/intent/intentmap-validation.json

${ARCHSIG_BIN:-archsig} intent-archmap-alignment \
  --input .archsig/intent/intent-archmap-alignment.json \
  --intent-map .archsig/intent/intentmap.json \
  --archmap .archsig/archmap/archmap.json \
  --out .archsig/intent/alignment-validation.json

${ARCHSIG_BIN:-archsig} intent-forecast \
  --intent-map .archsig/intent/intentmap.json \
  --archmap .archsig/archmap/archmap.json \
  --alignment .archsig/intent/intent-archmap-alignment.json \
  --out-dir .archsig/intent/forecast
```

For empirical follow-up, create an intent calibration record when observed PR / test / runtime refs
are available:

```bash
${ARCHSIG_BIN:-archsig} intent-calibration-record \
  --input .archsig/intent/intent-calibration-record.json \
  --out .archsig/intent/intent-calibration-validation.json
```

## PR Quality Pipeline

Use this for PR / CI analysis after ArchMap-side artifacts exist. It is separate from IntentMap
planning forecast and does not decide mergeability.

```bash
${ARCHSIG_BIN:-archsig} pr-quality-analysis \
  --input .archsig/pr/pr-quality-analysis-report.json \
  --out .archsig/pr/pr-quality-analysis-validation.json
```

## Reading Outputs

Always preserve these distinctions in summaries:

- measured zero vs unmeasured
- validation success vs theorem proof
- candidate support vs forecast result
- missing decision vs missing evidence
- unaligned / unsupported intent vs measured zero
- correlation or calibration hook vs causal theorem
- warning vs failure
- missing evidence vs negative evidence

Report generated file paths and command failures clearly. Do not silently continue after a failed upstream command if downstream artifacts would be misleading.

## Handoff

Use `$arch-doctor` after this skill when the user asks for architecture diagnosis, design advice, or forecast interpretation based on the generated artifacts.
