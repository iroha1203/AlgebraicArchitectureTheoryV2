# FieldSig

`fieldsig` is the SFT-based software evolution measurement layer. It is separate from ArchSig: ArchSig produces AAT structural telemetry and review cues, while FieldSig consumes ArchSig JSON artifact refs together with PRD, SPEC, Issue, CI, test, review, runtime, ownership, history, calibration, and AI proposal policy evidence.

FieldSig artifacts are measurement and workflow evidence. They do not prove forecast correctness, assign probabilities by default, establish causal correctness, provide global safety, or replace CI, tests, and human review.

## Core commands

```bash
cargo run --manifest-path tools/fieldsig/Cargo.toml -- software-field-measurement --fixture --out .fieldsig/software-field-measurement.json
cargo run --manifest-path tools/fieldsig/Cargo.toml -- software-field-measurement --input .fieldsig/software-field-measurement.json --out .fieldsig/software-field-measurement-validation.json
cargo run --manifest-path tools/fieldsig/Cargo.toml -- fieldsig-run-manifest --fixture --out .fieldsig/fieldsig-run-manifest.json
```

## Migrated surface

The SFT and workflow commands moved from ArchSig to FieldSig ownership:

- Intent and forecast: `artifact-descriptor`, `intent-map`, `intent-archmap-alignment`, `intent-forecast`, `operation-support-estimate`, `forecast-cone-skeleton`, `consequence-envelope`, `sft-review-summary`, `forecast-calibration-hook`, `intent-calibration-record`, `sft-forecast`.
- Workflow evidence and operational feedback: `dataset`, `pr-metadata`, `pr-history-dataset`, `feature-extension-dataset`, `outcome-linkage-dataset`, `report-outcome-daily-ledger`, `calibration-review-record`, `team-threshold-policy`, `ownership-boundary-monitor`, `repair-adoption-record`, `incident-correlation-monitor`, `hypothesis-refresh-cycle`.
- Field dynamics and governance: `pr-force-report`, `signature-trajectory-report`, `architecture-field-snapshot`, `operation-proposal-log`, `architecture-dynamics-metrics`, `dynamics-measurements`, `ai-proposal-governance`.

## Test

```bash
cargo test --manifest-path tools/fieldsig/Cargo.toml
```
