# FieldSig

`fieldsig` is the SFT-based software evolution measurement layer. It is separate from ArchSig: ArchSig produces AAT structural telemetry and review cues, while FieldSig consumes the serialized `archsig-analysis-packet-v0` together with PRD, SPEC, Issue, CI, test, review, runtime, ownership, history, calibration, and AI proposal policy evidence.

FieldSig artifacts are measurement and workflow evidence. They do not prove forecast correctness, assign probabilities by default, establish causal correctness, provide global safety, or replace CI, tests, and human review.

## Core commands

```bash
cargo run --manifest-path tools/fieldsig/Cargo.toml -- archsig-analysis-sft-input \
  --analysis-packet tools/fieldsig/tests/fixtures/minimal/llm_native_handoff/archsig_analysis_packet.json \
  --out .fieldsig/operation-support-estimate.json
cargo run --manifest-path tools/fieldsig/Cargo.toml -- software-field-measurement --fixture --out .fieldsig/software-field-measurement.json
cargo run --manifest-path tools/fieldsig/Cargo.toml -- software-field-measurement --input .fieldsig/software-field-measurement.json --out .fieldsig/software-field-measurement-validation.json
cargo run --manifest-path tools/fieldsig/Cargo.toml -- fieldsig-run-manifest --fixture --out .fieldsig/fieldsig-run-manifest.json
```

`archsig-analysis-sft-input` is the current ArchSig handoff. It rejects raw
ArchMap JSON when supplied as the analysis packet and preserves obstruction
circuits, signature axes, repair candidates, and coverage gaps as bounded SFT
input refs / unknown remainder.

## Migrated surface

The SFT and workflow commands moved from ArchSig to FieldSig ownership:

- Intent and forecast: `artifact-descriptor`, `intent-map`, `intent-archmap-alignment`, `intent-forecast`, `operation-support-estimate`, `forecast-cone-skeleton`, `consequence-envelope`, `sft-review-summary`, `forecast-calibration-hook`, `intent-calibration-record`, `sft-forecast`.
- Workflow evidence and operational feedback: `dataset`, `pr-metadata`, `pr-history-dataset`, `feature-extension-dataset`, `outcome-linkage-dataset`, `report-outcome-daily-ledger`, `calibration-review-record`, `team-threshold-policy`, `ownership-boundary-monitor`, `repair-adoption-record`, `incident-correlation-monitor`, `hypothesis-refresh-cycle`.
- Field dynamics and governance: `pr-force-report`, `signature-trajectory-report`, `architecture-field-snapshot`, `operation-proposal-log`, `architecture-dynamics-metrics`, `dynamics-measurements`, `ai-proposal-governance`.

## Test

```bash
cargo test --manifest-path tools/fieldsig/Cargo.toml
```
