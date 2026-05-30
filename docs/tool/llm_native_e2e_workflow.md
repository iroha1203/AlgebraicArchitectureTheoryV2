# LLM-native ArchMap / ArchSig E2E Workflow

This document fixes the end-to-end workflow required by the LLM-native
ArchMap / interpretation profile / ArchSig redesign. It is an implementation
transcript, not a new theory document.

## Flow

```text
source artifacts
  -> supplied archmap-observation-map-v0
  -> selected interpretation profile (law-policy-v0 JSON)
  -> archsig-analysis-packet-v0
  -> llm-interpretation-packet.json
  -> operation-support-estimate-v0
```

The first three artifacts are ArchSig-owned. The final
`operation-support-estimate-v0` is FieldSig-owned and reads the ArchSig
analysis packet as bounded current AAT structural state.

## Command Transcript

Run the ArchSig workflow:

```bash
mkdir -p .lake/llm-native-e2e/archsig .lake/llm-native-e2e/fieldsig

cargo run --manifest-path tools/archsig/Cargo.toml -- llm-native-workflow \
  --archmap tools/archsig/tests/fixtures/minimal/archmap.json \
  --law-policy tools/archsig/tests/fixtures/minimal/law_policy.json \
  --out-dir .lake/llm-native-e2e/archsig
```

`north-star-workflow` is the equivalent visible command alias for the same
ArchSig-owned route.

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
- The interpretation profile is the selected LawUniverse, witness-rule,
  coverage, and exactness artifact. The current schema name is `law-policy-v0`.
- ArchSig computes AAT concept surfaces, architecture state, design pressure,
  change impact, law-relative obstruction circuits, signature axes, analytic
  representations, coupling/cohesion readings, design principle readings,
  transfer bridge review focus, structural reading review surface, current-state
  / evolution boundary, bounded judgements, repair candidates, operation deltas,
  coverage gaps, and non-conclusions.
- `llm-interpretation-packet.json` is structured analysis input for an LLM, not
  a natural-language judgement, proof, or automatic repair instruction.
- FieldSig accepts `archsig-analysis-packet-v0` as bounded current AAT
  structural state and rejects raw ArchMap JSON as the current handoff input.
  PR / diff / change-vector evolution remains FieldSig territory.
- Coverage gaps are carried as unknown remainder; they are not rounded to
  absence, measured zero, or forecast truth.
- ArchSig emits only the current ArchMap validation, profile validation,
  analysis packet, analysis validation, and LLM interpretation packet in the
  current E2E route. Pre-Atom artifacts are not compatibility outputs.

## CI

`.github/workflows/lean.yml` contains the `llm-native ArchMap/ArchSig e2e` job.
The job runs the transcript above, validates key schema and boundary fields with
`jq`, rejects raw ArchMap handoff to FieldSig, and uploads
`.lake/llm-native-e2e` as an artifact.
