# ArchSig

`archsig` is the ArchMap -> ArchSig structural analysis CLI. The current
runtime has two explicit paths: the legacy v1 structural analysis path reads
supplied `archmap/v1` evidence and a selected `law-policy/v1` profile, while
the v0.4.0 AG measurement path reads `archmap/v2` plus a selected
`measurement-profile/v1` and emits `archsig-measurement-packet/v1`.

ArchSig is an LLM-native tool. The intended product interface is the bundled
LLM skills in `tools/archsig/skills`, not a human manually reading raw AAT
packet JSON. The CLI provides stable validation and analysis commands; the
skills author ArchMaps and LawPolicies, run the CLI, read summary / viewer /
manifest first, inspect raw packet refs only when needed, compare
high-priority findings with source evidence, and translate the result into
review or improvement language.

ArchSig's responsibility is bounded structural diagnosis over supplied
`ArchMap + LawPolicy`: it validates the input surfaces, builds AAT-oriented
reading families, and preserves the measurement basis for human / LLM review.
FieldSig owns forecast, governance, calibration, and operational feedback under
`tools/fieldsig`.

ArchSig's current primary workflow is complete-first authoring followed by v1
analysis:

1. Build the fullest source-grounded ArchMap the selected source universe
   supports, usually through `archmap-creater`.
2. Select a project-specific LawPolicy / interpretation profile, usually
   through `law-policy-creater`.
3. Run `analyze` through `archsig-reader` or directly through the CLI.
4. Let the skill read `archsig-analysis-summary.json`,
   `archsig-atom-viewer-data.json`, and `archsig-run-manifest.json` first,
   then inspect raw packet detail through `detailRefs` / `packetRefs` when
   source-level evidence is needed.

Coverage blockers such as `blockedByCoverageGap` are authoring repair targets
unless the evidence is genuinely private, unavailable, or out of scope. They
are not measured zeros.

## Product Surface

| Surface | Commands | Boundary |
| --- | --- | --- |
| ArchMap validation and authoring | `archmap` | ArchMap v1 records source-grounded Atom observations and explicit molecule candidates. Removed v0 helper fields such as `semanticObservations`, `projectionInfo`, `operationSquareEvidence`, `concernHints`, and `observationGaps` are not positive input. Complete-first authoring should collect source support and molecule candidates before handoff. ArchMap does not select laws or output obstruction circuits. |
| Interpretation profile | `law-policy` | LawPolicy v1 selects evaluator manifests, basis refs, selected laws, distance profile, and non-conclusions. It is an evaluator selector, not AAT itself. |
| ArchSig analysis | `analyze` | `analyze` is the primary workflow from ArchMap v1 + LawPolicy v1 to validation reports, normalized ArchMap, typed evaluator results, architecture distance, `archsig-analysis-summary.json`, `archsig-atom-viewer-data.json`, and `archsig-run-manifest.json`. Raw packet, detail index, and LLM interpretation artifacts are emitted only with `--emit-raw-artifacts`. |
| AG measurement | `analyze` | When `law-policy/v1` selects `measurementProfileRef` and the input is `archmap/v2`, `analyze` runs the v0.4.0 finite AG measurement path and emits `archsig-measurement-packet/v1`, conclusion-first summary, viewer data, and run manifest. This path is not backward-compatible with v1 ArchMap input, but the legacy v1 structural path remains a bounded compatibility runtime. |
| Lightweight PR review | `pr-review` | Reads base `archmap/v1`, optional head / intermediate `archmap/v1`, PR-local `archmap-delta-v0`, and required `law-policy/v1`. It does not accept raw diff, ArchMapCommit, or base/head analysis packets as PR-review inputs. It internally computes report-local v1 snapshots and emits delta packet intersections, architecture-distance movement, hidden-excursion boundary, safe-change budget, and structural review focus. |
| Schema | `schema-catalog` | The catalog lists the current ArchMap, LawPolicy, ArchSig analysis packet, and validation report artifacts. |

`archsig-analysis-packet/v1` includes the main ArchSig structural reading
families as derived output: generated law inputs, signature axes, generated
obstructions, generated repair targets, ACTS / spectrum readings,
`ArchitectureSpectrumReport`, homotopy / holonomy / Stokes readings,
`ArchitectureHomotopyReport`, structural reading families, replacement
registry / replacement evaluator results, bounded judgements, and LLM
interpretation refs. These are ArchSig outputs, not first-class ArchMap inputs.

`archsig-analysis-summary.json` is the preferred first reading surface. It
reports the conclusion, typed evaluator status, architecture distance,
`distanceDiagnosis`, dominant findings, action queue, measurement basis,
rich packet refs, and metadata. Blocked / unknown / unmeasured support is not
measured zero. The full evidence remains in `archsig-analysis-packet.json` only
when raw artifacts are emitted.

Large ArchMaps may be authored in shards for review and parallel generation,
but current commands consume the exported monolithic
`archmap/v1` artifact.

Pre-Atom and v0 packet-builder commands were removed instead of kept as
compatibility shims. `llm-native-workflow`, `north-star-workflow`,
`archsig-analysis`, `aat-analysis`, `analysis-summary`, `summary`,
`codebase-inspection`, and `archmap-generate` are not current runtime surfaces.
Git history is the archive for those workflows.

## Install From GitHub Release

Download ArchSig from the latest GitHub Release:

- <https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/releases/latest>

Choose the archive for your platform:

- `archsig-<tag>-linux-arm64.tar.gz`
- `archsig-<tag>-linux-x86_64.tar.gz`
- `archsig-<tag>-macos-universal.tar.gz`
- `archsig-<tag>-windows-x86_64.zip`

Use the ArchSig archive, not the repository source-code archive, when you want
the ready-to-run tool bundle. Each archive contains:

- the `archsig` executable
- the ArchSig README and command guide
- ArchView under `archview/` as the visualization layer
- the bundled LLM skills under `skills/`
- the repository license

After extracting the archive, put the `archsig` executable on `PATH` or set
`ARCHSIG_BIN` to its path. Then use the bundled `skills/` directory as the LLM
agent interface. For normal analysis, start from `archmap-creater`,
`law-policy-creater`, `archsig-reader`, or `archsig-pr-reviewer`; the skills
call the CLI and read the ArchSig output for the user.

## CLI Quick Start

Use the CLI directly for local smoke tests, scripted runs, CI, and skill
runtime calls. For user-facing analysis, prefer the skills below because they
carry the packet-reading and source-comparison workflow.

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- analyze \
  --archmap tools/archsig/tests/fixtures/archmap_v1/archmap.json \
  --law-policy tools/archsig/tests/fixtures/archmap_v1/law_policy.json \
  --out-dir .archsig/analyze
```

This writes:

- `.archsig/analyze/archmap-validation.json`
- `.archsig/analyze/law-policy-validation.json`
- `.archsig/analyze/normalized-archmap.json`
- `.archsig/analyze/typed-evaluator-results.json`
- `.archsig/analyze/architecture-distance.json`
- `.archsig/analyze/archsig-analysis-validation.json`
- `.archsig/analyze/archsig-analysis-summary.json`
- `.archsig/analyze/archsig-atom-viewer-data.json`
- `.archsig/analyze/archsig-run-manifest.json`

Use `archsig-analysis-summary.json` as the LLM-readable first pass and
`archsig-atom-viewer-data.json` with ArchView for human visual review. Viewer
data is bounded: atom nodes, molecule groups, edges, overlays, labels,
diagnostic distance projections, and source refs are priority-selected or
sampled, with omitted counts and reasons recorded. Viewer layout distance
inputs are visual placement support, not diagnostic metrics.
`archsig-run-manifest.json` records generated and omitted artifacts.

Release archives include `archview/archview.html` as the visualization layer.
Open it in a browser through a local HTTP server next to an
`archsig analyze` output directory, or copy it beside
`archsig-atom-viewer-data.json` so same-directory fetch can load the packet.
ArchView also supports file picker / drag-and-drop and sequence mode through
`archview-sequence/v1`. It uses CDN Three.js and projects measured AAT geometry
without creating new structural verdicts.

For large ArchMaps, prefer the optimized binary:

```bash
cargo run --release --manifest-path tools/archsig/Cargo.toml -- analyze \
  --archmap .archsig/hilda/archmap.json \
  --law-policy .archsig/hilda/hilda-law-policy.json \
  --out-dir .archsig/analyze
```

For FieldSig handoff or deep evidence lookup, emit raw artifacts explicitly:

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- analyze \
  --archmap tools/archsig/tests/fixtures/archmap_v1/archmap.json \
  --law-policy tools/archsig/tests/fixtures/archmap_v1/law_policy.json \
  --out-dir .archsig/analyze \
  --emit-raw-artifacts
```

This additionally writes:

- `.archsig/analyze/archsig-analysis-packet.json`
- `.archsig/analyze/archsig-analysis-detail-index.json`
- `.archsig/analyze/llm-interpretation-packet.json`

`archsig-analysis-packet.json` is the raw `archsig-analysis-packet/v1`
evidence store. The dictionary-backed `archsig-analysis-detail-index.json`
helps resolve compact `detailRefs` and packet refs without forcing summary /
viewer users to load the raw packet.

`llm-interpretation-packet.json` contains the compact
`llmInterpretationPacket` reading surface from the analysis packet. Treat it as
structured review evidence with explicit measurement bounds, not as a
standalone decision record or automatic repair instruction.

Calling `archsig` without a subcommand intentionally fails. The old implicit
scan-first path is no longer an ArchSig workflow.

## Skills

The `tools/archsig/skills` directory is the primary ArchSig product surface for
LLM agents. It is not an optional add-on. A released ArchSig bundle is expected
to work with the binary plus the skills directory; the skills do not require the
AAT mathematical docs, test fixtures, Cargo project, or Git history at runtime.

Use the skills whenever the task is to create an ArchMap, create a LawPolicy,
interpret an analysis packet, or review a PR. The raw packet remains the
evidence store, but the skills define the safe reading order and the translation
from AAT structural output into source-level review language.

| Skill | Purpose |
| --- | --- |
| `archmap-creater` | Create bounded `archmap/v1` artifacts from repository evidence. It keeps ArchMap as source-grounded Atom observations and explicit molecule candidates, not law-relative analysis or removed v0 helper fields. |
| `law-policy-creater` | Create project-specific `law-policy/v1` profiles from repository coding conventions, architecture rules, and user decisions. If docs do not define the evaluator universe, ask the user before selecting laws. |
| `archsig-reader` | Run an ArchMap with a selected LawPolicy, read summary / viewer report / manifest first, follow `distanceDiagnosis` detail refs only when needed, compare high-priority readings with source evidence, and propose bounded improvements. It does not silently use a generic LawPolicy as project analysis. |
| `archsig-pr-reviewer` | Derive PR-local `archmap-delta-v0` from the base branch diff, run `pr-review` with base ArchMap v1, optional head/path ArchMaps, and LawPolicy v1, read the changed code, and explain review focus in human code-review language. It stops if the base ArchMap or LawPolicy is missing. |

Typical use:

1. Use `archmap-creater` to produce or refine the ArchMap.
2. Use `law-policy-creater` to produce the selected LawPolicy for the target
   repository or subsystem.
3. Run `analyze`.
4. Use `archsig-reader` to interpret `archsig-analysis-summary.json`,
   `archsig-atom-viewer-data.json`, and `archsig-run-manifest.json` first, then
   compare selected detail refs with source evidence before proposing
   improvements.

For pull requests, use `archsig-pr-reviewer` after a base ArchMap and LawPolicy
exist. It derives the PR-local `archmap-delta-v0` from the base branch diff,
runs `pr-review`, then compares the report with source evidence before writing
human-facing review comments. It treats `archsig-pr-review-report-v1` as review
focus rather than an approval decision.

## Release Assets

ArchSig release assets are built by `.github/workflows/archsig-release.yml` when
a GitHub Release is published, or manually with `workflow_dispatch` for an
existing tag. The workflow uploads:

- `archsig-<tag>-linux-arm64.tar.gz`
- `archsig-<tag>-linux-x86_64.tar.gz`
- `archsig-<tag>-macos-universal.tar.gz`
- `archsig-<tag>-windows-x86_64.zip`
- `SHA256SUMS.txt`

Each binary archive contains the `archsig` executable, the repository license,
the ArchSig README / command guide, and the ArchSig skills directory.

Use version-only tags such as `v0.1.0` or prerelease tags such as
`v0.1.0-rc.1`. Do not include `archsig` in the tag name; asset names already
carry the `archsig-` prefix.

## Docs

- [Command Guide](docs/commands.md)
- [Artifacts And Boundaries](docs/artifacts-and-boundaries.md)
- [Sharded ArchMap Design](docs/sharded-archmap.md)

## Test

```bash
cargo test --manifest-path tools/archsig/Cargo.toml
```
