# FieldSig Commands

FieldSig owns SFT software evolution measurement and workflow-evidence artifacts. The current ArchSig handoff is the serialized `archsig-analysis-packet-v0`: FieldSig reads it as current AAT structural state, not as forecast truth, causal correctness, global safety, or PR diff analysis. `archsig-analysis-sft-input` projects that packet into `operation-support-estimate-v0` while preserving obstruction circuits, signature axes, repair candidates, structural review boundaries, and coverage gaps as bounded refs. `archmap-sft-input` remains a legacy bounded projection and must not promote raw ArchMap observations to forecast truth. FieldSig does not share Rust types with ArchSig as a contract; the stable boundary is the serialized artifact ref.

## Measurement

- `software-field-measurement`: emits or validates `software-field-measurement-v0`. The artifact keeps observation boundary, ArchSig refs, workflow evidence refs, field estimate, forecast refs, consequence envelope refs, governance candidate refs, operational feedback refs, calibration hooks, unknown remainder, and non-conclusions.
- `fieldsig-run-manifest`: emits or validates `fieldsig-run-manifest-v0`. The manifest records input artifact refs, generated output refs, validation summary, claim boundary, and non-conclusions for a run.

## Forecast and Intent

Use `artifact-descriptor`, `intent-map`, `intent-archmap-alignment`, `intent-forecast`, `operation-support-estimate`, `forecast-cone-skeleton`, `consequence-envelope`, `sft-review-summary`, `forecast-calibration-hook`, `intent-calibration-record`, and `sft-forecast` for bounded SFT forecast artifacts. These commands preserve missing evidence and unknown remainder; they do not create probability or causal-correctness claims.

ArchSig analysis packet handoff:

```bash
cargo run --manifest-path tools/fieldsig/Cargo.toml -- archsig-analysis-sft-input \
  --analysis-packet tools/fieldsig/tests/fixtures/minimal/llm_native_handoff/archsig_analysis_packet.json \
  --out .fieldsig/operation-support-estimate.json
```

This command rejects raw ArchMap JSON when it is supplied as the analysis-packet
input. The accepted boundary is `archsig-analysis-packet-v0`.

The end-to-end command transcript is fixed in
[`docs/tool/llm_native_e2e_workflow.md`](../../../docs/tool/llm_native_e2e_workflow.md).
CI runs the same flow from ArchMap and LawPolicy through ArchSig analysis,
LLM interpretation packet emission, and FieldSig handoff.

## Operational and Governance

Use `dataset`, `pr-metadata`, `pr-history-dataset`, `feature-extension-dataset`, `outcome-linkage-dataset`, `report-outcome-daily-ledger`, `calibration-review-record`, `team-threshold-policy`, `ownership-boundary-monitor`, `repair-adoption-record`, `incident-correlation-monitor`, `hypothesis-refresh-cycle`, `pr-force-report`, `signature-trajectory-report`, `architecture-field-snapshot`, `operation-proposal-log`, `architecture-dynamics-metrics`, `dynamics-measurements`, and `ai-proposal-governance` for workflow evidence, feedback, field dynamics, and AI proposal governance.

## Validation

```bash
cargo test --manifest-path tools/fieldsig/Cargo.toml
```
