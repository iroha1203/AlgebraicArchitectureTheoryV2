# ArchSig Commands

`archsig` is the ArchMap v1 + LawPolicy v1 analysis tool. The current route is:

```text
archmap/v1
  + law-policy/v1
  -> normalized-archmap/v1
  -> typed-evaluator-results/v1
  -> archsig-architecture-distance/v1
  -> archsig-analysis-summary/v1
  -> archsig-atom-viewer-data-v1
  -> archsig-run-manifest-v1
```

ArchSig no longer exposes pre-Atom scan, projection, report, or legacy raw-diff
PR-review commands. Git history is the archive for those workflows. The
retained `pr-review` command reads ArchMap v1, PR-local ArchMapDelta refs, and
LawPolicy v1 typed evaluator state. Raw diff is not an ArchSig PR-review input.
FieldSig owns SFT forecast, IntentMap, operational feedback, governance, and
calibration commands under `tools/fieldsig`.

## Primary Workflow

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- analyze \
  --archmap tools/archsig/tests/fixtures/archmap_v1/archmap.json \
  --law-policy tools/archsig/tests/fixtures/archmap_v1/law_policy.json \
  --out-dir .archsig/analyze
```

Use `analyze` in new docs, scripts, and CI.

The command emits only:

- `archmap-validation.json`
- `law-policy-validation.json`
- `normalized-archmap.json`
- `typed-evaluator-results.json`
- `architecture-distance.json`
- `archsig-analysis-validation.json`
- `archsig-analysis-summary.json`
- `archsig-atom-viewer-data.json`
- `archsig-run-manifest.json`

`archsig-analysis-summary.json` is the LLM-readable compact reading surface. It
is conclusion-first and includes typed evaluator diagnosis, architecture
distance, `distanceDiagnosis`, action queue, and detail refs. Public summary /
viewer / LLM wording uses architecture distance naming; raw metadata may retain
source refs to the AAT mathematics documents.
`archsig-atom-viewer-data.json` is a bounded visual projection for the fixed
Atom Viewer app. It uses deterministic top-N priority selection for atom nodes
and molecule groups, emits bounded molecule-to-atom edges, limits labels and
source refs to count plus samples, carries bounded diagnostic distance overlays
separately from viewer layout distance inputs, and records omitted counts /
reasons.
`archsig-run-manifest.json` records generated and omitted artifacts. For large
ArchMaps, run `analyze` with `cargo run --release`.

The release bundle includes a fixed `archsig-atom-viewer.html`. The page loads
CDN Three.js, tries WebGPU first when the browser exposes it, falls back to
WebGL, and reads `archsig-atom-viewer-data.json` through a file picker,
drag-and-drop, or same-directory default fetch. It does not read the raw
analysis packet. Its report pane also reads same-directory
`archsig-analysis-summary.json` and `archsig-run-manifest.json` when available
to show the verdict, top findings, action queue, coverage boundaries,
distance diagnosis, validation status, generated / omitted artifacts, and
relative links to raw packet / detail-index files when raw artifacts were
emitted.

`--strict-distance` requires LawPolicy v1 to select a known `distanceProfileRef`
and rejects blocked / unknown / unmeasured typed or architecture distance
readings. LawPolicy v1 selects the profile ref only; it does not embed distance
weights, operation costs, or a distance DSL.

Raw evidence artifacts are opt-in:

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- analyze \
  --archmap tools/archsig/tests/fixtures/archmap_v1/archmap.json \
  --law-policy tools/archsig/tests/fixtures/archmap_v1/law_policy.json \
  --out-dir .archsig/analyze \
  --emit-raw-artifacts
```

This additionally writes:

- `archsig-analysis-packet.json`
- `archsig-analysis-detail-index.json`
- `llm-interpretation-packet.json`

`archsig-analysis-packet.json` is a raw evidence artifact for deeper lookup.
Current v1 does not expose a separate `analysis-summary` command; `analyze`
always writes `archsig-analysis-summary.json` directly. Read
`conclusion`, `typedEvaluatorDiagnosis`, `architectureDistance`,
`distanceDiagnosis`, and `actionQueue` first. The summary does not replace the
raw packet or validation reports.

## Codebase Inspection

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- codebase-inspection \
  --snapshot tools/archsig/tests/fixtures/inspection/archmap_snapshot.json \
  --index tools/archsig/tests/fixtures/inspection/archmap_index.json \
  --packet tools/archsig/tests/fixtures/coupon_rounding/archsig_analysis_packet.json \
  --law-policy tools/archsig/tests/fixtures/minimal/law_policy.json \
  --recent-delta tools/archsig/tests/fixtures/pr_review/archmap_delta.json \
  --out .archsig/inspection/archsig-codebase-inspection.json
```

`codebase-inspection` is the current-state ArchSig surface for architecture
health review. Its canonical inputs are the latest `archmap-snapshot-v0`,
`archmap-index-v0`, an `archsig-analysis-packet-v0`, optional recent
`archmap-delta-v0` window, and optional `law-policy-v0` provenance. The report
groups subsystem boundary cues, feature-like clusters, operation-like
relations, top boundary holonomy readings, top order-sensitive squares,
coverage / exactness boundaries, and next action cues. It separates this
current-state diagnosis from `pr-review`, which is change-local, and from
FieldSig, which owns PR / diff / change-vector evolution analysis, forecast,
governance, calibration, and longitudinal monitoring.

## Lightweight PR Review

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- pr-review \
  --base-archmap tools/archsig/tests/fixtures/archmap_v1/archmap.json \
  --after-archmap tools/archsig/tests/fixtures/archmap_v1/archmap_violation.json \
  --path-archmap tools/archsig/tests/fixtures/archmap_v1/archmap.json \
  --delta-archmap tools/archsig/tests/fixtures/pr_review/archmap_delta_v1_refs.json \
  --law-policy tools/archsig/tests/fixtures/archmap_v1/law_policy.json \
  --out .archsig/pr-review/archsig-pr-review.json
```

`pr-review` is the CI-friendly ArchSig surface for small PR review. Its
canonical inputs are base `archmap/v1`, optional head `archmap/v1`, optional
intermediate `archmap/v1` snapshots, PR-local `archmap-delta-v0`, and required
`law-policy/v1`. No LawPolicy, no ArchSig judgement. `pr-review` does not
accept raw diff, `archmap-commit-v0`, or base/head
`archsig-analysis-packet/v1` artifacts as inputs. The command internally
generates report-local v1 analysis snapshots and emits `v1Analysis`,
`deltaPacketRefIntersections`, and `prStructuralDiagnosis`: changed delta refs
matched to typed / derived packet refs, endpoint architecture-distance
movement, total path movement over supplied snapshots, hidden-excursion
boundary, safe-change budget, and structural reading refs. Optional
`--path-archmap` inputs may be supplied repeatedly to bound movement across
intermediate ArchMap snapshots; without them, hidden-excursion absence remains
blocked. Blocked / unknown / unmeasured support limits safe-change budget
instead of becoming measured zero. The report remains a bounded PR review
surface, not FieldSig longitudinal evolution analysis, merge approval, repair
safety, or incident forecast.

## Sharded ArchMap Authoring

Large ArchMaps may be drafted in a sharded authoring layout documented in
`tools/archsig/docs/sharded-archmap.md`:

```text
.archsig/archmap/
  manifest.json
  slices/
    authority.archmap-slice.json
    state.archmap-slice.json
    effects.archmap-slice.json
    providers.archmap-slice.json
    runtime.archmap-slice.json
```

The manifest schema is `archmap-shard-manifest-v0`. This is an authoring-side
layout, not a current analysis input. The primary sharding model is horizontal:
each `archmap-observation-slice-v0` file is a bounded observation slice over a
repository surface or sub-agent assignment. Bundle/export must produce a
monolithic `archmap-observation-map-v0` file before running:

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- archmap \
  --input .archsig/archmap/archmap.json \
  --out .archsig/analyze/archmap-validation.json
```

Current commands intentionally keep the analysis contract monolithic. A future
bundle/export command should validate slice paths, duplicate ids, dangling
cross-slice refs, required/optional slice policy, allowed cross-slice
references, and source refs before writing the exported ArchMap.

## Step Commands

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- archmap \
  --input tools/archsig/tests/fixtures/minimal/archmap.json \
  --out .archsig/analyze/archmap-validation.json

cargo run --manifest-path tools/archsig/Cargo.toml -- interpretation-profile \
  --input tools/archsig/tests/fixtures/minimal/law_policy.json \
  --out .archsig/analyze/law-policy-validation.json

cargo run --manifest-path tools/archsig/Cargo.toml -- aat-analysis \
  --archmap tools/archsig/tests/fixtures/minimal/archmap.json \
  --law-policy tools/archsig/tests/fixtures/minimal/law_policy.json \
  --out .archsig/analyze/archsig-analysis-packet.json \
  --validation-out .archsig/analyze/archsig-analysis-validation.json \
  --llm-interpretation-out .archsig/analyze/llm-interpretation-packet.json

cargo run --manifest-path tools/archsig/Cargo.toml -- analysis-summary \
  --packet .archsig/analyze/archsig-analysis-packet.json \
  --out .archsig/analyze/archsig-analysis-summary.json
```

`law-policy` / `interpretation-profile` validate the selected analysis profile.
The JSON schema name remains `law-policy-v0`, but ArchSig treats it as a
profile selecting LawUniverse, witness rules, axes, coverage, and exactness.
`law-policy --fixture` emits the canonical minimal profile fixture.

## ArchMap Generation Protocol

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- archmap-generate \
  --source-inventory tools/archsig/tests/fixtures/minimal/archmap_source_inventory.json \
  --prompt-pack tools/archsig/skills/archmap-creater/references/prompt-pack.md \
  --provider external-agent \
  --model-id unspecified \
  --out .archsig/analyze/archmap-generation-protocol.json
```

This command emits a bounded protocol for an external agent to produce
`archmap-observation-map-v0`. The protocol is provenance and boundary data; it
does not reconstruct private context or prove semantic correctness.

## Schema Catalog

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- schema-catalog \
  --out .archsig/schema/schema-version-catalog.json
```

The catalog contains only current ArchSig artifacts:

- `archmap`
- `archmap-validation-report`
- `law-policy`
- `law-policy-validation-report`
- `archsig-analysis-packet`
- `archsig-analysis-packet-validation-report`

Removed commands are not documented as active workflow variants. The CLI
allowlist is fixed by the tests and by `archsig --help`.
