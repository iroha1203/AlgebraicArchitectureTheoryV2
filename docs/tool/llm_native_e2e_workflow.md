# LLM-native ArchMap / ArchSig E2E Workflow

This document fixes the end-to-end workflow required by the LLM-native
ArchMap / LawPolicy / ArchSig redesign. It is an implementation transcript,
not a new theory document.

## Flow

```text
source artifacts
  -> supplied archmap-observation-map-v0
  -> selected law-policy-v0
  -> archsig-analysis-packet-v0
  -> llm-interpretation-packet.json
  -> operation-support-estimate-v0
```

The first three artifacts are ArchSig-owned. The final
`operation-support-estimate-v0` is FieldSig-owned and reads the ArchSig
analysis packet as bounded local AAT state.

## Command Transcript

Run the ArchSig workflow:

```bash
mkdir -p .lake/llm-native-e2e/archsig .lake/llm-native-e2e/fieldsig

cargo run --manifest-path tools/archsig/Cargo.toml -- llm-native-workflow \
  --archmap tools/archsig/tests/fixtures/minimal/archmap.json \
  --law-policy tools/archsig/tests/fixtures/minimal/law_policy.json \
  --out-dir .lake/llm-native-e2e/archsig
```

Expected ArchSig outputs:

```text
.lake/llm-native-e2e/archsig/archmap-validation.json
.lake/llm-native-e2e/archsig/law-policy-validation.json
.lake/llm-native-e2e/archsig/archsig-analysis-packet.json
.lake/llm-native-e2e/archsig/archsig-analysis-validation.json
.lake/llm-native-e2e/archsig/llm-interpretation-packet.json
```

The LLM interpretation packet is byte-for-byte the same structured analysis
packet:

```bash
cmp \
  .lake/llm-native-e2e/archsig/archsig-analysis-packet.json \
  .lake/llm-native-e2e/archsig/llm-interpretation-packet.json
```

Project the ArchSig analysis packet into FieldSig:

```bash
cargo run --manifest-path tools/fieldsig/Cargo.toml -- archsig-analysis-sft-input \
  --analysis-packet .lake/llm-native-e2e/archsig/archsig-analysis-packet.json \
  --out .lake/llm-native-e2e/fieldsig/operation-support-estimate.json
```

The output must be `operation-support-estimate-v0` with
`descriptorRef.artifactKind = "archsig-analysis-packet"`.

## Regression Guardrails

The E2E flow must preserve these boundaries:

- ArchMap remains law-independent source-grounded Atom observation evidence.
- LawPolicy is the selected law universe and witness-rule artifact.
- ArchSig computes law-relative obstruction circuits, signature axes, flatness
  readings, repair candidates, coverage gaps, and non-conclusions.
- `llm-interpretation-packet.json` is structured analysis input for an LLM, not
  a natural-language judgement, proof, or automatic repair instruction.
- FieldSig accepts `archsig-analysis-packet-v0` and rejects raw ArchMap JSON as
  the current handoff input.
- Coverage gaps are carried as unknown remainder; they are not rounded to
  absence, measured zero, or forecast truth.
- ArchSig does not emit AIR, Feature Report, theorem-check, AAT Observable
  Bundle, Sig0 adapter, PR governance, or signature-diff artifacts in the
  current E2E route.

## CI

`.github/workflows/lean.yml` contains the `llm-native ArchMap/ArchSig e2e` job.
The job runs the transcript above, validates key schema and boundary fields with
`jq`, rejects raw ArchMap handoff to FieldSig, and uploads
`.lake/llm-native-e2e` as an artifact.
