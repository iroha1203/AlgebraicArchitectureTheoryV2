# ArchSig

`archsig` is the ArchMap -> ArchSig structural analysis CLI. The current
runtime reads supplied `archmap/v0.5.2` evidence and selected
`law-policy/v0.5.2`, `law-equation-surface/v0.5.2`, and
`measurement-profile/v0.5.2` artifacts. Reproducible runs fix those three
policy components with `archsig-policy-bundle/v0.5.2`; the AG measurement path
emits `archsig-measurement-packet/v0.5.2`.

ArchSig is an LLM-native tool. The intended product interface is the bundled
LLM skills in `tools/archsig/skills`, not a human manually reading internal JSON.
The CLI provides stable validation and analysis commands; the skills author
ArchMaps and LawPolicies, run the CLI, read summary / viewer / manifest first,
compare high-priority findings with source evidence, and translate the result
into review or improvement language.

ArchSig's responsibility is bounded structural diagnosis over supplied
`ArchMap + LawPolicy + law-equation-surface + MeasurementProfile`: it validates the input surfaces, builds AAT-oriented
reading families, and preserves the measurement basis for human / LLM review.
For reproducible runs, `policy-bundle` fixes the three selected policy components with canonical fingerprints; the individual component flags are the equivalent direct-input form.
FieldSig owns forecast, governance, calibration, and operational feedback under
`tools/fieldsig`.

ArchSig's current primary workflow is complete-first authoring followed by
`analyze`:

1. Build the fullest source-grounded ArchMap the selected source universe
   supports, usually through `archmap-creater`.
2. Select a project-specific LawPolicy / interpretation profile, usually
   through `law-policy-creater`.
3. Run `analyze` through `archsig-reader` or directly through the CLI.
4. Let the skill read `archsig-analysis-summary.json`,
   `archsig-measurement-packet.json`, `archsig-atom-viewer-data.json`, and
   `archsig-run-manifest.json`, then compare selected findings with source
   evidence when source-level review is needed.

Coverage blockers such as `blockedByCoverageGap` are authoring repair targets
unless the evidence is genuinely private, unavailable, or out of scope. They
are not measured zeros.

## Product Surface

| Surface | Commands | Boundary |
| --- | --- | --- |
| ArchMap validation and authoring | `archmap` | ArchMap records source-grounded Atom observations over the finite-poset-site contract. Removed helper fields such as `semanticObservations`, `projectionInfo`, `operationSquareEvidence`, `concernHints`, and `observationGaps` are not positive input. Complete-first authoring should collect source support before handoff. ArchMap does not select laws or output obstruction circuits. |
| ArchMap authoring support | `scope-manifest`, `extraction-diff` | `scope-manifest` builds the deterministic authoring worklist (paths, hashes, approved globs) that ArchMap surveys start from. `extraction-diff` compares two survey passes' candidate packets by authoring atom-match-key; it leaves adoption adjudication to the integrator and never auto-adopts. |
| Interpretation profile | `law-policy` | LawPolicy selects evaluator manifests, explicit law / lawPair entries, basis refs, measurement profiles, and non-conclusions. It is an evaluator selector, not AAT itself. |
| Policy bundle | `policy-bundle` | Fixes LawPolicy, law-equation-surface, and MeasurementProfile references with canonical component fingerprints for one analyze run. |
| MeasurementProfile validation | `measurement-profile` | Validates a standalone `measurement-profile/v0.5.2` artifact, including finite bounds against evaluator registry hard caps. |
| RepairPlan validation | `repair-plan` | Validates the supplied `archsig-repair-plan/v0.5.2` SAGA input side. Faithfulness, true-sheaf, gluing, coefficient, and comparison slots are checked; generated conclusion tokens and still-reserved grounding fields fail closed. |
| AG measurement | `analyze` | When `law-policy/v0.5.2` selects `measurementProfileRef` and the input is finite-poset-site `archmap/v0.5.2`, `analyze` emits `archsig-measurement-packet/v0.5.2`, conclusion-first summary, insight report, viewer data, and run manifest. `ag.saga-descent` can additionally consume a checked RepairPlan via `--repair-plan`; without it the row is `not_computed` with `silence_by_design`. |
| Compare | `compare` | Compares two current `analyze` output directories and computes `archmap-diff/v0.5.2` plus `archsig-comparison-report/v0.5.2`. The diff is computed by ArchSig, not authored as a separate input artifact. |
| Gate | `gate` | Applies `archsig-gate-policy/v0.5.2` to a measurement packet and optional comparison report. This is the CI decision surface. |
| Schema | `schema-catalog` | The catalog lists current ArchMap, law-equation-surface, LawPolicy, policy-bundle, RepairPlan, measurement, gate, compare, manifest, and viewer artifacts. |

`archsig-analysis-summary.json` is the preferred first reading surface. It
reports the conclusion, structural verdict summary, dominant findings, action
queue, measurement basis, boundaries, and metadata. Blocked / unknown /
unmeasured / not-computed support is not measured zero.

Large ArchMaps may be authored in shards for review and parallel generation,
but current commands consume the exported monolithic
`archmap/v0.5.2` artifact.

Pre-Atom, v0 packet-builder, and v1 compatibility commands were removed instead
of kept as shims. `llm-native-workflow`, `north-star-workflow`,
`archsig-analysis`, `aat-analysis`, `analysis-summary`, `summary`,
`codebase-inspection`, and `archmap-generate` are not current runtime surfaces.
Git history is the archive for those workflows.

## Migration Surface

| Removed role | Current replacement |
| --- | --- |
| Legacy lightweight PR review command | `compare` for measurement comparison, followed by `gate` for CI policy. |
| Legacy strict distance flag | `gate` policy rules over measurement and comparison reports. |
| Raw handoff artifact | `archsig-measurement-packet.json` for FieldSig handoff. |
| Authored delta artifact | `compare` computes `archmap-diff/v0.5.2` from two run directories. |
| Legacy derived distance chain | Measurement packet, summary, insight report, viewer data, and run manifest. |

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
agent interface. For normal analysis, start from the ArchMap creator, LawPolicy
creator, ArchSig reader, or PR reviewer skill; use the RepairPlan creator when
a measured obstruction needs a SAGA repair route. The skills call the CLI and
read the ArchSig output for the user.

## CLI Quick Start

Use the CLI directly for local smoke tests, scripted runs, CI, and skill
runtime calls. For user-facing analysis, prefer the skills below because they
carry the packet-reading and source-comparison workflow.

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- analyze \
  --archmap tools/archsig/tests/fixtures/ag_measurement/archmap_v2.json \
  --law-policy tools/archsig/tests/fixtures/ag_measurement/law_policy_ag.json \
  --measurement-profile tools/archsig/tests/fixtures/ag_measurement/measurement_profile_ag.json \
  --law-surface tools/archsig/tests/fixtures/ag_measurement/law_surface_ag_v052.json \
  --out-dir .archsig/analyze
```

This writes:

- `.archsig/analyze/archmap-validation.json`
- `.archsig/analyze/law-policy-validation.json`
- `.archsig/analyze/law-surface-validation.json`
- `.archsig/analyze/normalized-archmap.json`
- `.archsig/analyze/archsig-analysis-validation.json`
- `.archsig/analyze/archsig-analysis-summary.json`
- `.archsig/analyze/archsig-measurement-packet.json`
- `.archsig/analyze/archsig-insight-report.json`
- `.archsig/analyze/archsig-insight-brief.md`
- `.archsig/analyze/archsig-atom-viewer-data.json`
- `.archsig/analyze/archsig-run-manifest.json`

When a policy bundle is supplied, the measurement packet and run manifest also
record `componentFingerprints` for the three selected policy components.

Use `archsig-analysis-summary.json` as the LLM-readable first pass and
`archsig-atom-viewer-data.json` with ArchView for human visual review. Viewer
data is bounded: atom nodes, context groups, edges, overlays, labels,
measurement projections, and source refs are priority-selected or sampled, with
omitted counts and reasons recorded. Viewer layout inputs are visual placement
support, not diagnostic metrics.
`archsig-run-manifest.json` records generated and omitted artifacts.

Release archives include `archview/archview.html` as the visualization layer.
Open it in a browser through a local HTTP server next to an
`archsig analyze` output directory, or copy it beside
`archsig-atom-viewer-data.json` so same-directory fetch can load the packet.
ArchView also supports file picker / drag-and-drop and sequence mode through
`archview-sequence/v0.5.2`. It uses CDN Three.js and projects measured AAT geometry
without creating new structural verdicts.

For a production-shaped, end-to-end demonstration — a realistic Rust service
whose PR passes every unit test in every build state yet introduces a
measured H1 gluing obstruction, gets blocked by `gate`, and passes again
after repair — run the one-cent drift example:

```bash
tools/archsig/examples/practical-rust-service/scripts/run_archsig_demo.sh
```

See `tools/archsig/examples/practical-rust-service/README.md` for the story,
the three build states, and the mismatch support to inspect.

Calling `archsig` without a subcommand intentionally fails. The old implicit
scan-first path is no longer an ArchSig workflow.

## Skills

The `tools/archsig/skills` directory is the primary ArchSig product surface for
LLM agents. It is not an optional add-on. A released ArchSig bundle is expected
to work with the binary plus the skills directory; the skills do not require the
AAT mathematical docs, test fixtures, Cargo project, or Git history at runtime.

Use the skills whenever the task is to create an ArchMap, create a LawPolicy,
interpret a measurement run, or review a PR. The skills define the safe reading
order and the translation from AAT structural output into source-level review
language.

| Skill | Purpose |
| --- | --- |
| `archmap-creater` | Create bounded `archmap/v0.5.2` artifacts from repository evidence. It keeps ArchMap as source-grounded Atom observations, not law-relative analysis or removed v0 helper fields. |
| `law-policy-creater` | Create project-specific `law-policy/v0.5.2` profiles from repository coding conventions, architecture rules, and user decisions. If docs do not define the evaluator universe, ask the user before selecting laws. |
| `archsig-reader` | Run an ArchMap with a selected policy bundle, read summary / viewer report / manifest first, compare high-priority readings with source evidence, and propose bounded improvements. It does not silently use a generic LawPolicy as project analysis. |
| `archsig-pr-reviewer` | Use `analyze`, `compare`, and `gate`, then read the changed code and explain review focus in human code-review language. It stops if the base measurement context is missing. |
| `repair-plan-creater` | Author `archsig-repair-plan/v0.5.2` artifacts for SAGA descent runs, validated through `repair-plan` and consumed through `analyze --repair-plan`. |

Typical use:

1. Use `archmap-creater` to produce or refine the ArchMap.
2. Use `law-policy-creater` to produce the selected LawPolicy for the target
   repository or subsystem.
3. Run `analyze`.
4. Use `archsig-reader` to interpret `archsig-analysis-summary.json`,
   `archsig-atom-viewer-data.json`, and `archsig-run-manifest.json` first, then
   compare selected detail refs with source evidence before proposing
   improvements.
5. When a measured obstruction needs a repair route, use `repair-plan-creater`
   to author `archsig-repair-plan/v0.5.2`, validate it with `repair-plan`, and
   re-run `analyze` with `--repair-plan`.

For pull requests, run current base and head measurements, compare the two run
directories, apply gate policy, then compare the report with source evidence
before writing human-facing review comments. The gate report is a policy check,
not a replacement for reading the changed code.

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

Use version-only tags such as `v0.5.2` or prerelease tags such as
`v0.5.2-rc.1`. Do not include `archsig` in the tag name; asset names already
carry the `archsig-` prefix.

## Docs

- [Command Guide](docs/commands.md)
- [Artifacts And Boundaries](docs/artifacts-and-boundaries.md)
- [Archived Sharded ArchMap Design](../../docs/archive/2026-07-05-archsig-v1-retirement/tools-archsig-docs/sharded-archmap.md)

## Test

```bash
cargo test --manifest-path tools/archsig/Cargo.toml
```
