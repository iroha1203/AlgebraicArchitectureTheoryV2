# ArchSig Analyze E2E Workflow

This document fixes the end-to-end workflow for ArchMap / interpretation
profile / ArchSig `analyze`. It is an implementation transcript, not a new
theory document.

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

Future PR review and longitudinal workflows should insert ArchMapStore before
ArchSig analysis:

```text
source artifacts
  -> language adapter / extractor / LLM reader / manual authoring
  -> ArchMapDelta / ArchMapCommit
  -> optional ArchMapSnapshot / ArchMapIndex
  -> ArchSig lightweight structural diagnosis
  -> FieldSig batch evolution monitoring
```

Raw diff is not an ArchSig PR-review input. The canonical semantic input is
ArchMap-level evidence.

## Command Transcript

Run the ArchSig workflow:

```bash
mkdir -p .lake/archsig-analyze-e2e/archsig .lake/archsig-analyze-e2e/fieldsig

cargo run --manifest-path tools/archsig/Cargo.toml -- analyze \
  --archmap tools/archsig/tests/fixtures/minimal/archmap.json \
  --law-policy tools/archsig/tests/fixtures/minimal/law_policy.json \
  --out-dir .lake/archsig-analyze-e2e/archsig
```

`llm-native-workflow` and `north-star-workflow` are compatibility aliases for
the same ArchSig-owned route. Use `analyze` in new scripts and CI.

Expected ArchSig outputs:

```text
.lake/archsig-analyze-e2e/archsig/archmap-validation.json
.lake/archsig-analyze-e2e/archsig/law-policy-validation.json
.lake/archsig-analyze-e2e/archsig/archsig-analysis-packet.json
.lake/archsig-analyze-e2e/archsig/archsig-analysis-detail-index.json
.lake/archsig-analyze-e2e/archsig/archsig-analysis-validation.json
.lake/archsig-analyze-e2e/archsig/llm-interpretation-packet.json
```

The analysis packet is compact-first. Large repeated string ref sets are
replaced by `archsig-detail-ref-v0` objects in the packet and stored through a
dictionary-backed `archsig-analysis-detail-index.json`. For large ArchMaps, run
the workflow with `cargo run --release`.

The LLM interpretation packet is the compact `llmInterpretationPacket` reading
surface from `archsig-analysis-packet.json`; it is intentionally not a
byte-for-byte copy of the full analysis packet.

Project the ArchSig analysis packet into FieldSig:

```bash
cargo run --manifest-path tools/fieldsig/Cargo.toml -- archsig-analysis-sft-input \
  --analysis-packet .lake/archsig-analyze-e2e/archsig/archsig-analysis-packet.json \
  --out .lake/archsig-analyze-e2e/fieldsig/operation-support-estimate.json
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
- Future ArchSig PR review mode reads base ArchMap, PR-local ArchMap delta,
  and LawPolicy as change-local structural evidence for CI. FieldSig reads
  ArchMapStore and ArchSig packet chains in batch for longitudinal evolution
  monitoring.
- The implemented lightweight `archsig pr-review` command takes
  base ArchMap, PR-local ArchMap delta, and LawPolicy as canonical inputs.
  Raw diff is not an ArchSig PR-review input.
- The implemented `archsig codebase-inspection` command takes latest
  `ArchMapSnapshot`, `ArchMapIndex`, an ArchSig packet, optional recent deltas,
  and optional LawPolicy provenance as the current-state diagnosis surface. It
  is separate from change-local PR review and from FieldSig evolution analysis.
- Coverage gaps are carried as unknown remainder; they are not rounded to
  absence, measured zero, or forecast truth.
- ArchSig emits only the current ArchMap validation, profile validation,
  analysis packet, analysis validation, and LLM interpretation packet in the
  current E2E route. Pre-Atom artifacts are not compatibility outputs.

## CI

`.github/workflows/lean.yml` contains the ArchSig analyze e2e job.
The job runs the transcript above, validates key schema and boundary fields with
`jq`, rejects raw ArchMap handoff to FieldSig, and uploads
`.lake/archsig-analyze-e2e` as an artifact.
