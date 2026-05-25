# FieldSig Commands

FieldSig owns SFT software evolution measurement and workflow-evidence artifacts. ArchSig artifacts enter FieldSig through JSON refs such as `archmap-v0`, `archsig-sig0-v0`, AIR, validation, and review-cue artifact paths. FieldSig does not share Rust types with ArchSig as a contract; the stable boundary is the serialized artifact ref.

## Measurement

- `software-field-measurement`: emits or validates `software-field-measurement-v0`. The artifact keeps observation boundary, ArchSig refs, workflow evidence refs, field estimate, forecast refs, consequence envelope refs, governance candidate refs, operational feedback refs, calibration hooks, unknown remainder, and non-conclusions.
- `fieldsig-run-manifest`: emits or validates `fieldsig-run-manifest-v0`. The manifest records input artifact refs, generated output refs, validation summary, claim boundary, and non-conclusions for a run.

## Forecast and Intent

Use `artifact-descriptor`, `intent-map`, `intent-archmap-alignment`, `intent-forecast`, `operation-support-estimate`, `forecast-cone-skeleton`, `consequence-envelope`, `sft-review-summary`, `forecast-calibration-hook`, `intent-calibration-record`, and `sft-forecast` for bounded SFT forecast artifacts. These commands preserve missing evidence and unknown remainder; they do not create probability or causal-correctness claims.

## Operational and Governance

Use `dataset`, `pr-metadata`, `pr-history-dataset`, `feature-extension-dataset`, `outcome-linkage-dataset`, `report-outcome-daily-ledger`, `calibration-review-record`, `team-threshold-policy`, `ownership-boundary-monitor`, `repair-adoption-record`, `incident-correlation-monitor`, `hypothesis-refresh-cycle`, `pr-force-report`, `signature-trajectory-report`, `architecture-field-snapshot`, `operation-proposal-log`, `architecture-dynamics-metrics`, `dynamics-measurements`, and `ai-proposal-governance` for workflow evidence, feedback, field dynamics, and AI proposal governance.

## Validation

```bash
cargo test --manifest-path tools/fieldsig/Cargo.toml
```
