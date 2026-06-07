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

The manifest schema is historical `archmap-shard-manifest-v0`. This is an
authoring-side layout, not a current analysis input. The primary sharding model
is horizontal: each slice is a bounded observation slice over a repository
surface or sub-agent assignment. Bundle/export must produce a monolithic
`archmap/v1` file before running:

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- archmap \
  --input .archsig/archmap/archmap.json \
  --out .archsig/analyze/archmap-validation.json
```

Current commands intentionally keep the analysis contract monolithic. A future
bundle/export command should validate slice paths, duplicate ids, dangling
cross-slice refs, required/optional slice policy, allowed cross-slice
references, and source refs before writing the exported ArchMap.

## Validation Commands

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- archmap \
  --input tools/archsig/tests/fixtures/archmap_v1/archmap.json \
  --out .archsig/analyze/archmap-validation.json

cargo run --manifest-path tools/archsig/Cargo.toml -- law-policy \
  --input tools/archsig/tests/fixtures/archmap_v1/law_policy.json \
  --out .archsig/analyze/law-policy-validation.json
```

`archmap` validates `archmap/v1`. `law-policy` validates `law-policy/v1`.
Standalone packet-builder, standalone summary, codebase-inspection, and
archmap-generation commands are removed runtime surfaces; use `analyze` and
the ArchSig skills instead.

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
