# FieldSig Commands

FieldSig owns SFT software evolution measurement and workflow-evidence artifacts. The current ArchSig handoff is the serialized `archsig-measurement-packet/v1`: FieldSig reads it as current AG measurement state, not as forecast truth, causal correctness, global safety, or PR diff analysis. `archsig-analysis-sft-input` projects that packet into `operation-support-estimate-v0` while preserving structural verdicts, computed invariants, analytic readings, assumption ledger entries, and non-conclusions as bounded refs / unknown remainder. Legacy `archsig-analysis-packet/v1` and `archsig-analysis-packet-v0` remain accepted as bounded compatibility inputs. `archmap-sft-input` remains a legacy bounded projection and must not promote raw ArchMap observations to forecast truth. FieldSig does not share Rust types with ArchSig as a contract; the stable boundary is the serialized artifact ref.

## Measurement

- `software-field-measurement`: emits or validates `software-field-measurement-v0`. The artifact keeps observation boundary, ArchSig refs, workflow evidence refs, field estimate, forecast refs, consequence envelope refs, governance candidate refs, operational feedback refs, calibration hooks, unknown remainder, and non-conclusions.
- `fieldsig-run-manifest`: emits or validates `fieldsig-run-manifest-v0`. The manifest records input artifact refs, generated output refs, validation summary, claim boundary, and non-conclusions for a run.

## Forecast and Intent

Use `artifact-descriptor`, `intent-map`, `intent-archmap-alignment`, `intent-forecast`, `operation-support-estimate`, `forecast-cone-skeleton`, `consequence-envelope`, `sft-review-summary`, `forecast-calibration-hook`, `intent-calibration-record`, and `sft-forecast` for bounded SFT forecast artifacts. These commands preserve missing evidence and unknown remainder; they do not create probability or causal-correctness claims.

ArchSig measurement packet handoff:

```bash
cargo run --manifest-path tools/fieldsig/Cargo.toml -- archsig-analysis-sft-input \
  --measurement-packet .tmp/archsig-analyze/archsig-measurement-packet.json \
  --out .fieldsig/operation-support-estimate.json
```

This command rejects raw ArchMap JSON when it is supplied as the
measurement-packet input. The primary accepted boundary is
`archsig-measurement-packet/v1`. `--analysis-packet` is retained only for legacy
bounded analysis packet handoff.

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
