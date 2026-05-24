# ArchSig Command Catalog

Use this catalog when the ArchSig source repository is unavailable. It lists the command surfaces needed for common workflows.

## Binary Check

```bash
${ARCHSIG_BIN:-archsig} --help
```

## Core Signature

Scan repository:

```bash
${ARCHSIG_BIN:-archsig} \
  --root . \
  --out .archsig/signature/sig0.json
```

Validate Sig0:

```bash
${ARCHSIG_BIN:-archsig} validate \
  --input .archsig/signature/sig0.json \
  --out .archsig/signature/sig0-validation.json \
  --universe-mode local-only
```

Python scan:

```bash
${ARCHSIG_BIN:-archsig} \
  --language python \
  --root <repo> \
  --source-root <source-root> \
  --package-root <package-root> \
  --out .archsig/signature/python-sig0.json
```

## Snapshot And Diff

Create snapshot:

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
```

Create signature diff:

```bash
${ARCHSIG_BIN:-archsig} signature-diff \
  --before-snapshot .archsig/signature/previous/snapshot.json \
  --after-snapshot .archsig/signature/current/snapshot.json \
  --before-sig0 .archsig/signature/previous/sig0.json \
  --after-sig0 .archsig/signature/current/sig0.json \
  --pr-metadata .archsig/pr-metadata.json \
  --out .archsig/signature/current/diff-report.json
```

## ArchMap Review

Validate ArchMap:

```bash
${ARCHSIG_BIN:-archsig} archmap \
  --input .archsig/archmap/archmap.json \
  --out .archsig/archmap/validation.json
```

Project ArchMap to AIR:

```bash
${ARCHSIG_BIN:-archsig} air-from-archmap \
  --archmap .archsig/archmap/archmap.json \
  --validation .archsig/archmap/validation.json \
  --out .archsig/archmap/air.json
```

Validate AIR:

```bash
${ARCHSIG_BIN:-archsig} validate-air \
  --input .archsig/archmap/air.json \
  --out .archsig/archmap/air-validation.json
```

Check theorem preconditions:

```bash
${ARCHSIG_BIN:-archsig} theorem-check \
  --air .archsig/archmap/air.json \
  --out .archsig/archmap/theorem-check.json
```

Generate feature report:

```bash
${ARCHSIG_BIN:-archsig} feature-report \
  --air .archsig/archmap/air.json \
  --out .archsig/archmap/feature-report.json
```

## ArchMap To SFT

Project ArchMap to operation support:

```bash
${ARCHSIG_BIN:-archsig} archmap-sft-input \
  --archmap .archsig/archmap/archmap.json \
  --out .archsig/archmap/operation-support-estimate.json
```

Build forecast cone skeleton:

```bash
${ARCHSIG_BIN:-archsig} forecast-cone-skeleton \
  --operation-support .archsig/archmap/operation-support-estimate.json \
  --out .archsig/archmap/forecast-cone-skeleton.json
```

Build consequence envelope:

```bash
${ARCHSIG_BIN:-archsig} consequence-envelope \
  --forecast-cone .archsig/archmap/forecast-cone-skeleton.json \
  --out .archsig/archmap/consequence-envelope-report.json
```

Create forecast calibration hook:

```bash
${ARCHSIG_BIN:-archsig} forecast-calibration-hook \
  --out .archsig/sft/forecast-calibration-hook.json
```

## IntentMap Planning Forecast

Validate IntentMap:

```bash
${ARCHSIG_BIN:-archsig} intent-map \
  --input .archsig/intent/intentmap.json \
  --out .archsig/intent/intentmap-validation.json
```

Validate AlignmentMap:

```bash
${ARCHSIG_BIN:-archsig} intent-archmap-alignment \
  --input .archsig/intent/intent-archmap-alignment.json \
  --intent-map .archsig/intent/intentmap.json \
  --archmap .archsig/archmap/archmap.json \
  --out .archsig/intent/alignment-validation.json
```

Run planning forecast:

```bash
${ARCHSIG_BIN:-archsig} intent-forecast \
  --intent-map .archsig/intent/intentmap.json \
  --archmap .archsig/archmap/archmap.json \
  --alignment .archsig/intent/intent-archmap-alignment.json \
  --out-dir .archsig/intent/forecast
```

Create intent calibration record validation:

```bash
${ARCHSIG_BIN:-archsig} intent-calibration-record \
  --input .archsig/intent/intent-calibration-record.json \
  --out .archsig/intent/intent-calibration-validation.json
```

## PR Quality Analysis

```bash
${ARCHSIG_BIN:-archsig} pr-quality-analysis \
  --input .archsig/pr/pr-quality-analysis-report.json \
  --out .archsig/pr/pr-quality-analysis-validation.json
```

## Failure Handling

- If a command fails, stop the downstream pipeline.
- If an input path is missing, run the upstream artifact command or ask for the correct path.
- If validation emits warnings, preserve them as review cues.
- If validation fails, fix the upstream artifact before generating dependent outputs.
