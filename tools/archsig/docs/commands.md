# ArchSig Commands

`archsig` is now the AAT analysis engine over ArchMap. The current route is:

```text
archmap-observation-map-v0
  + interpretation profile (law-policy-v0 JSON)
  -> archsig-analysis-packet-v0
  -> LLM interpretation
  -> FieldSig handoff
```

ArchSig no longer exposes pre-Atom scan, projection, report, or legacy raw-diff
PR-review commands. Git history is the archive for those workflows. The
retained `pr-review` command reads base ArchMap, PR-local ArchMap delta, and
LawPolicy. Raw diff is not an ArchSig PR-review input.
FieldSig owns SFT forecast, IntentMap, operational feedback, governance, and
calibration commands under `tools/fieldsig`.

## Primary Workflow

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- analyze \
  --archmap tools/archsig/tests/fixtures/minimal/archmap.json \
  --law-policy tools/archsig/tests/fixtures/minimal/law_policy.json \
  --out-dir .archsig/analyze
```

`llm-native-workflow` and `north-star-workflow` are visible compatibility
aliases for the same workflow. Use `analyze` in new docs, scripts, and CI:

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- llm-native-workflow \
  --archmap tools/archsig/tests/fixtures/minimal/archmap.json \
  --law-policy tools/archsig/tests/fixtures/minimal/law_policy.json \
  --out-dir .archsig/compat
```

The command emits only:

- `archmap-validation.json`
- `law-policy-validation.json`
- `archsig-analysis-validation.json`
- `archsig-analysis-summary.json`
- `archsig-atom-viewer-data.json`
- `archsig-run-manifest.json`

`archsig-analysis-summary.json` is the LLM-readable compact reading surface.
`archsig-atom-viewer-data.json` is a bounded visual projection for the fixed
Atom Viewer app. It uses deterministic top-N priority selection for atom nodes
and molecule groups, emits bounded molecule-to-atom edges, limits labels and
source refs to count plus samples, and records omitted counts / reasons.
`archsig-run-manifest.json` records generated and omitted artifacts. For large
ArchMaps, run `analyze` with `cargo run --release`.

Raw evidence artifacts are opt-in:

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- analyze \
  --archmap tools/archsig/tests/fixtures/minimal/archmap.json \
  --law-policy tools/archsig/tests/fixtures/minimal/law_policy.json \
  --out-dir .archsig/analyze \
  --emit-raw-artifacts
```

This additionally writes:

- `archsig-analysis-packet.json`
- `archsig-analysis-detail-index.json`
- `llm-interpretation-packet.json`

`archsig-analysis-packet.json` is compact-first when emitted: large repeated
string ref sets are replaced by `archsig-detail-ref-v0` objects with counts,
samples, and detail refs. Full ref sets are stored through a dictionary-backed
`archsig-analysis-detail-index.json`.

To emit a compact review summary from an existing packet, run:

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- analysis-summary \
  --packet .archsig/analyze/archsig-analysis-packet.json \
  --archmap-validation .archsig/analyze/archmap-validation.json \
  --law-policy-validation .archsig/analyze/law-policy-validation.json \
  --analysis-validation .archsig/analyze/archsig-analysis-validation.json \
  --out .archsig/analyze/archsig-analysis-summary.json
```

`summary` is a visible alias. The summary is a reading aid for human / LLM
review. Read `verdict`, `analysisUsefulness`, `qualityMeasurement`, and
`architectureInsightSummary` first. `analysisUsefulness` separates findings
usable now from claims still blocked by coverage gaps, so gap-qualified output
does not collapse into "nothing can be said." `architectureInsightSummary`
groups selected law-axis pressure, spectrum hotspots, coverage blockers, repair
candidates, and operation preconditions into a small structural review plan. Its
`insightCards` field turns the measured AAT surfaces into structural review
hypotheses with a claim, `whyItMatters`, AAT evidence refs, observed signals,
missing evidence, and next validation steps. `actionQueue` is intentionally
capped to representative AAT-computed items; use `detailRefs` and `detailIndex`
to inspect the full packet. The summary does not replace the full packet or
validation reports.

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
  --base-archmap tools/archsig/tests/fixtures/minimal/archmap.json \
  --delta-archmap tools/archsig/tests/fixtures/pr_review/archmap_delta.json \
  --law-policy tools/archsig/tests/fixtures/minimal/law_policy.json \
  --out .archsig/pr-review/archsig-pr-review.json
```

`pr-review` is the CI-friendly ArchSig surface for small PR review. Its
canonical inputs are base `archmap-observation-map-v0`, PR-local
`archmap-delta-v0`, and required `law-policy-v0`. No LawPolicy, no ArchSig
judgement. `pr-review` does not accept raw diff, `archmap-commit-v0`, or
base/head `archsig-analysis-packet-v0` artifacts as inputs. The report records
which base observations, source targets, LawPolicy laws, and selected axes the
PR-local delta touches. It is not FieldSig longitudinal evolution analysis.

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
