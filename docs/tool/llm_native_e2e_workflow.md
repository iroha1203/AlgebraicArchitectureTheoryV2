# ArchSig Analyze E2E Workflow

This document fixes the end-to-end workflow for ArchMap / interpretation
profile / ArchSig `analyze`. It is an implementation transcript, not a new
theory document.

## Flow

```text
source artifacts
  -> supplied archmap/v1
  -> selected law-policy/v1
  -> archsig-analysis-summary.json
  -> archsig-atom-viewer-data.json + fixed archsig-atom-viewer.html
  -> archsig-run-manifest.json
  -> optional archsig-analysis-packet/v1 raw artifacts
  -> operation-support-estimate-v0
```

The ArchMap, LawPolicy, summary, viewer data, manifest, and optional raw
analysis artifacts are ArchSig-owned. The final
`operation-support-estimate-v0` is FieldSig-owned and reads the ArchSig
analysis packet as bounded current AAT structural state only when raw artifacts
were explicitly emitted.

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
mkdir -p .tmp/archsig-analyze-e2e/archsig .tmp/archsig-analyze-e2e/fieldsig

cargo run --manifest-path tools/archsig/Cargo.toml -- analyze \
  --archmap tools/archsig/tests/fixtures/archmap_v1/archmap.json \
  --law-policy tools/archsig/tests/fixtures/archmap_v1/law_policy.json \
  --out-dir .tmp/archsig-analyze-e2e/archsig
```

`analyze` is the current ArchSig-owned route. Removed legacy workflow aliases
are not compatibility outputs for the v1 path.

Expected ArchSig outputs:

```text
.tmp/archsig-analyze-e2e/archsig/archmap-validation.json
.tmp/archsig-analyze-e2e/archsig/law-policy-validation.json
.tmp/archsig-analyze-e2e/archsig/archsig-analysis-validation.json
.tmp/archsig-analyze-e2e/archsig/archsig-analysis-summary.json
.tmp/archsig-analyze-e2e/archsig/archsig-atom-viewer-data.json
.tmp/archsig-analyze-e2e/archsig/archsig-run-manifest.json
```

Default `analyze` does not save the raw analysis packet, detail index, or LLM
interpretation packet. Read `archsig-analysis-summary.json` as the LLM first
surface and open the fixed release-bundled `archsig-atom-viewer.html` with
`archsig-atom-viewer-data.json` as the human first surface. The Viewer report
pane also reads the same-directory summary and manifest when available. Part IV
distance diagnosis is read from summary `distanceDiagnosis` and viewer report
pane diagnostic overlays first; raw packet distance rows are detail evidence,
not the primary human or LLM surface.

Use raw artifacts only when FieldSig handoff or detailed evidence lookup needs
the packet:

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- analyze \
  --archmap tools/archsig/tests/fixtures/archmap_v1/archmap.json \
  --law-policy tools/archsig/tests/fixtures/archmap_v1/law_policy.json \
  --out-dir .tmp/archsig-analyze-e2e/archsig-raw \
  --emit-raw-artifacts
```

Raw-mode ArchSig outputs also include:

```text
.tmp/archsig-analyze-e2e/archsig-raw/archsig-analysis-packet.json
.tmp/archsig-analyze-e2e/archsig-raw/archsig-analysis-detail-index.json
.tmp/archsig-analyze-e2e/archsig-raw/llm-interpretation-packet.json
```

The raw analysis packet is compact-first. Large repeated string ref sets are
replaced by `archsig-detail-ref-v0` objects in the packet and stored through a
dictionary-backed `archsig-analysis-detail-index.json`. The LLM interpretation
packet is the compact `llmInterpretationPacket` reading surface from the raw
analysis packet; it is intentionally not a byte-for-byte copy of the full
analysis packet. For large ArchMaps, run the workflow with `cargo run --release`.

Project the primary v0.4.0 ArchSig measurement packet into FieldSig:

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- analyze \
  --archmap tools/archsig/tests/fixtures/ag_measurement/archmap_v2_support_transfer.json \
  --law-policy tools/archsig/tests/fixtures/ag_measurement/law_policy_transfer.json \
  --out-dir .tmp/archsig-analyze-e2e/archsig-measurement

cargo run --manifest-path tools/fieldsig/Cargo.toml -- archsig-analysis-sft-input \
  --measurement-packet .tmp/archsig-analyze-e2e/archsig-measurement/archsig-measurement-packet.json \
  --out .tmp/archsig-analyze-e2e/fieldsig/operation-support-estimate-measurement.json
```

The output must be `operation-support-estimate-v0` with
`descriptorRef.artifactKind = "archsig-measurement-packet"`. FieldSig preserves
structural verdict rows, computed invariants, analytic readings, assumption
ledger refs, and non-conclusions as bounded current AG measurement state. It
does not promote raw ArchMap observations, analytic readings, theorem-candidate
readings, or assumed boundaries to forecast truth.

Legacy analysis packet compatibility handoff:

```bash
cargo run --manifest-path tools/fieldsig/Cargo.toml -- archsig-analysis-sft-input \
  --analysis-packet .tmp/archsig-analyze-e2e/archsig-raw/archsig-analysis-packet.json \
  --out .tmp/archsig-analyze-e2e/fieldsig/operation-support-estimate.json
```

The output must be `operation-support-estimate-v0` with
`descriptorRef.artifactKind = "archsig-analysis-packet"`. FieldSig preserves
v1 `generatedPacketRefs`, spectrum, homotopy, structural reading surface, typed
evaluator support refs, and evidence-boundary refs as bounded current state
coordinates.

Check the v1 raw packet against the FieldSig schema compatibility catalog:

```bash
cargo run --manifest-path tools/fieldsig/Cargo.toml -- schema-compatibility \
  --before .tmp/archsig-analyze-e2e/archsig-raw/archsig-analysis-packet.json \
  --after .tmp/archsig-analyze-e2e/archsig-raw/archsig-analysis-packet.json \
  --out .tmp/archsig-analyze-e2e/fieldsig/schema-compatibility-report.json
```

## Regression Guardrails

The E2E flow must preserve these boundaries:

- ArchMap remains law-independent source-grounded Atom observation evidence.
- LawPolicy v1 selects evaluator packs / explicit evaluator entries. It is not
  a witness DSL or Lean proof surface.
- ArchSig computes AAT concept surfaces, architecture state, design pressure,
  change impact, law-relative obstruction circuits, signature axes, analytic
  representations, coupling/cohesion readings, design principle readings,
  transfer bridge review focus, structural reading review surface, current-state
  / evolution boundary, bounded judgements, repair candidates, operation deltas,
  coverage gaps, and non-conclusions.
- `archsig-analysis-summary.json` is the LLM first reading surface. It is
  structured analysis input, not a natural-language judgement, proof, or
  automatic repair instruction. Its `distanceDiagnosis` section is the first
  Part IV distance surface for measured movement, unmeasured axes, safe margin,
  repair / curvature / homotopy distance, representation metric boundaries,
  and packet refs.
- `archsig-atom-viewer-data.json` plus fixed `archsig-atom-viewer.html` is the
  human visual/report surface. It is a bounded projection and does not parse
  raw packet detail in the browser. Diagnostic distance overlays are bounded
  Part IV evaluator projections; viewer layout distances are visual placement
  support, not ArchSig metrics.
- `llm-interpretation-packet.json` is emitted only in raw mode and remains a
  compact packet sub-surface, not a separate source of truth.
- FieldSig accepts `archsig-analysis-packet/v1` raw packets as bounded current
  AAT structural state and rejects raw ArchMap JSON as the current handoff
  input. PR / diff / change-vector evolution remains FieldSig territory.
- ArchSig PR review mode reads base ArchMap, optional head / intermediate path
  ArchMaps, PR-local ArchMap delta, and LawPolicy as change-local structural
  evidence for CI. FieldSig reads ArchMapStore and ArchSig packet chains in
  batch for longitudinal evolution monitoring.
- The implemented lightweight `archsig pr-review` command takes
  base ArchMap, optional head / intermediate path ArchMaps, PR-local ArchMap
  delta, and LawPolicy as canonical inputs. With head ArchMap, it emits PR
  drift, safe-change budget, and architecture navigation focus by internally
  generating base/path/head packets under the same LawPolicy. Raw diff is not an
  ArchSig PR-review input.
- The implemented `archsig codebase-inspection` command takes latest
  `ArchMapSnapshot`, `ArchMapIndex`, an ArchSig packet, optional recent deltas,
  and optional LawPolicy provenance as the current-state diagnosis surface. It
  is separate from change-local PR review and from FieldSig evolution analysis.
- Coverage gaps are carried as unknown remainder; they are not rounded to
  absence, measured zero, or forecast truth.
- `unmeasured`, `blocked`, `unavailable`, `incomparable`, and `infinite`
  Part IV distance values are not zeros. They stay tied to coverage blockers,
  `DistanceProfile`, and `DiagnosticScope`.
- ArchSig default `analyze` emits only the current validation reports, summary,
  Atom Viewer data, and run manifest. Raw packet, detail index, and LLM
  interpretation packet are opt-in through `--emit-raw-artifacts`.
  Pre-Atom artifacts are not compatibility outputs.

## CI

`.github/workflows/lean.yml` contains the ArchSig analyze e2e job.
The job runs default summary/viewer/manifest output checks, then a raw-artifact
handoff run for FieldSig. It validates key schema and boundary fields with
`jq`, rejects raw ArchMap handoff to FieldSig, and uploads
`.tmp/archsig-analyze-e2e` as an artifact.
