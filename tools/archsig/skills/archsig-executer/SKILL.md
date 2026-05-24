---
name: archsig-executer
description: Run ArchSig CLI workflows and produce bounded JSON artifacts. Use when Codex is asked to execute ArchSig commands, scan repositories, validate Sig0 or ArchMap, create snapshots or signature diffs, project ArchMap to AIR or SFT input, build ForecastConeSkeleton or ConsequenceEnvelope artifacts, create calibration hooks, or verify the ArchSig tooling pipeline.
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

## Reading Outputs

Always preserve these distinctions in summaries:

- measured zero vs unmeasured
- validation success vs theorem proof
- candidate support vs forecast result
- correlation or calibration hook vs causal theorem
- warning vs failure
- missing evidence vs negative evidence

Report generated file paths and command failures clearly. Do not silently continue after a failed upstream command if downstream artifacts would be misleading.

## Handoff

Use `$arch-doctor` after this skill when the user asks for architecture diagnosis, design advice, or forecast interpretation based on the generated artifacts.
