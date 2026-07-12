# ArchSig Analyze E2E Workflow

This document fixes the current end-to-end workflow for ArchMap /
LawPolicy / MeasurementProfile / ArchSig `analyze`. It is an implementation
transcript, not a new theory document.

## Flow

```text
source artifacts
  -> supplied ArchMap finite-poset-site evidence
  -> selected LawPolicy + MeasurementProfile
  -> archsig-measurement-packet.json
  -> archsig-analysis-summary.json
  -> archsig-atom-viewer-data.json + ArchView
  -> archsig-run-manifest.json
  -> FieldSig measurement-packet handoff
```

ArchSig owns the ArchMap validation, LawPolicy validation, measurement packet,
summary, viewer data, and run manifest. FieldSig owns the SFT projection that
reads the measurement packet as bounded current architecture-evidence state.

## Command Transcript

```bash
mkdir -p .tmp/archsig-analyze-e2e/archsig .tmp/archsig-analyze-e2e/fieldsig

cargo run --manifest-path tools/archsig/Cargo.toml -- analyze \
  --archmap tools/archsig/tests/fixtures/ag_measurement/archmap_v2_support_transfer.json \
  --law-policy tools/archsig/tests/fixtures/ag_measurement/law_policy_transfer.json \
  --measurement-profile tools/archsig/tests/fixtures/ag_measurement/measurement_profile_transfer.json \
  --law-surface tools/archsig/tests/fixtures/ag_measurement/law_surface_ag_v051.json \
  --out-dir .tmp/archsig-analyze-e2e/archsig

cargo run --manifest-path tools/fieldsig/Cargo.toml -- archsig-analysis-sft-input \
  --measurement-packet .tmp/archsig-analyze-e2e/archsig/archsig-measurement-packet.json \
  --out .tmp/archsig-analyze-e2e/fieldsig/operation-support-estimate.json
```

Expected ArchSig outputs:

```text
archmap-validation.json
law-policy-validation.json
normalized-archmap.json
archsig-measurement-packet.json
archsig-analysis-validation.json
archsig-analysis-summary.json
archsig-insight-report.json
archsig-insight-brief.md
archsig-atom-viewer-data.json
archsig-run-manifest.json
```

## Regression Guardrails

- ArchMap remains source-grounded observation evidence.
- LawPolicy selects evaluators and scope; it is not a proof surface.
- MeasurementProfile selects the finite measurement regime.
- ArchSig emits bounded measurement artifacts and does not infer missing
  evidence as measured zero.
- FieldSig reads `archsig-measurement-packet/v0.5.1` as the current handoff.
- Raw ArchMap JSON is not a FieldSig handoff input.
- Compare + gate are the current PR / CI decision surfaces.

`.github/workflows/tool.yml` contains the current e2e job. It runs ArchSig
`analyze`, validates gate / compare / catalog surfaces, hands the measurement
packet to FieldSig, and rejects retired handoff forms.
