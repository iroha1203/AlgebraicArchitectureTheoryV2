# FieldSig

`fieldsig` is the SFT-based software evolution measurement layer. It is separate from ArchSig: ArchSig produces current AAT structural telemetry and review cues, while FieldSig consumes raw `archsig-analysis-packet/v1` handoff artifacts together with PRD, SPEC, Issue, CI, test, review, runtime, ownership, history, calibration, and AI proposal policy evidence to study PR / diff / change-vector evolution over that state.

FieldSig artifacts are measurement and workflow evidence. They do not prove forecast correctness, assign probabilities by default, establish causal correctness, provide global safety, or replace CI, tests, and human review.

## Core commands

```bash
cargo run --manifest-path tools/fieldsig/Cargo.toml -- archsig-analysis-sft-input \
  --analysis-packet .tmp/archsig-analyze-e2e/archsig-raw/archsig-analysis-packet.json \
  --out .fieldsig/operation-support-estimate.json
cargo run --manifest-path tools/fieldsig/Cargo.toml -- software-field-measurement --fixture --out .fieldsig/software-field-measurement.json
cargo run --manifest-path tools/fieldsig/Cargo.toml -- software-field-measurement --input .fieldsig/software-field-measurement.json --out .fieldsig/software-field-measurement-validation.json
cargo run --manifest-path tools/fieldsig/Cargo.toml -- fieldsig-run-manifest --fixture --out .fieldsig/fieldsig-run-manifest.json
```

`archsig-analysis-sft-input` is the current ArchSig handoff. It rejects raw
ArchMap JSON when supplied as the analysis packet and preserves v1 typed
evaluator results, generated packet refs, spectrum readings, homotopy readings,
structural review boundaries, detail refs, and coverage gaps as bounded SFT
input refs / unknown remainder. It does not treat ArchSig current-state
telemetry as forecast correctness or causal truth.

## Migrated surface

The SFT and workflow commands moved from ArchSig to FieldSig ownership:

- Intent and forecast: `artifact-descriptor`, `intent-map`, `intent-archmap-alignment`, `intent-forecast`, `operation-support-estimate`, `forecast-cone-skeleton`, `consequence-envelope`, `sft-review-summary`, `forecast-calibration-hook`, `intent-calibration-record`, `sft-forecast`.
- Workflow evidence and operational feedback: `dataset`, `pr-metadata`, `pr-history-dataset`, `feature-extension-dataset`, `outcome-linkage-dataset`, `report-outcome-daily-ledger`, `calibration-review-record`, `team-threshold-policy`, `ownership-boundary-monitor`, `repair-adoption-record`, `incident-correlation-monitor`, `hypothesis-refresh-cycle`.
- Field dynamics and governance: `pr-force-report`, `signature-trajectory-report`, `architecture-field-snapshot`, `operation-proposal-log`, `architecture-dynamics-metrics`, `dynamics-measurements`, `ai-proposal-governance`.

## Test

```bash
cargo test --manifest-path tools/fieldsig/Cargo.toml
```
