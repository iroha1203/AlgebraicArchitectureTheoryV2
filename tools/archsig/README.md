# ArchSig

`archsig` is the ArchMap -> AAT analysis packet CLI. It reads supplied
`archmap-observation-map-v0` evidence and a selected interpretation profile
(`law-policy-v0` JSON) into a North Star `archsig-analysis-packet-v0` for LLM
and human review.

ArchSig is an LLM-native tool. The intended product interface is the bundled
LLM skills in `tools/archsig/skills`, not a human manually reading raw AAT
packet JSON. The CLI provides stable validation and packet-building commands;
the skills author ArchMaps and LawPolicies, run the CLI, read the structured
packet, compare high-priority findings with source evidence, and translate the
result into review or improvement language. This matters because raw AAT output
is dense and easy to misread without the skill-specific reading workflow.

ArchSig's responsibility is bounded structural diagnosis over supplied
`ArchMap + LawPolicy`: it validates the input surfaces, builds AAT-oriented
reading families, and preserves the measurement basis for human / LLM review.
FieldSig owns forecast, governance, calibration, and operational feedback under
`tools/fieldsig`.

ArchSig's current primary workflow is complete-first authoring followed by
analysis:

1. Build the fullest source-grounded ArchMap the selected source universe
   supports, usually through `archmap-creater`.
2. Select a project-specific LawPolicy / interpretation profile, usually
   through `law-policy-creater`.
3. Run `analyze` through `archsig-reader` or directly through the CLI.
4. Let the skill read `analysis-summary` first, then inspect packet detail
   through `detailRefs` / `packetRefs` when source-level evidence is needed.

Coverage blockers such as `blockedByCoverageGap` are authoring repair targets
unless the evidence is genuinely private, unavailable, or out of scope. They
are not measured zeros.

## Product Surface

| Surface | Commands | Boundary |
| --- | --- | --- |
| ArchMap validation and authoring | `archmap`, `archmap-generate` | ArchMap records source-grounded Atom observations, molecule observations, semantic readings, projection hints, concern hints, and gaps. Complete-first authoring should collect spectrum support, homotopy candidates, filler evidence, non-fillability witnesses, and targeted gaps before handoff. It does not select laws or output obstruction circuits. |
| Interpretation profile | `law-policy`, `interpretation-profile` | The profile selects the LawUniverse, witness rules, molecule patterns, obstruction circuit definitions, signature axes, coverage requirements, exactness assumptions, optional ACTS spectrum profile, optional homotopy measurement profile, and non-conclusions. It is not AAT itself. |
| ArchSig analysis | `analyze`, `llm-native-workflow`, `north-star-workflow`, `archsig-analysis`, `aat-analysis`, `analysis-summary`, `summary` | `analyze` is the primary workflow from ArchMap + LawPolicy to validation reports, `archsig-analysis-packet-v0`, and the LLM interpretation packet. `llm-native-workflow` and `north-star-workflow` remain compatibility aliases for the same workflow. `archsig-analysis` / `aat-analysis` build a packet from already validated inputs. `analysis-summary` emits the compact human / LLM reading surface from an existing packet. |
| Codebase inspection | `codebase-inspection` | Reads latest `archmap-snapshot-v0`, `archmap-index-v0`, optional recent deltas, optional LawPolicy provenance, and an `archsig-analysis-packet-v0` to produce current-state architectural diagnosis. It is not PR / diff evolution analysis or global safety. |
| Lightweight PR review | `pr-review` | Reads base `archmap-observation-map-v0`, PR-local `archmap-delta-v0`, and required `law-policy-v0`. It does not accept raw diff, ArchMapCommit, or base/head analysis packets as PR-review inputs. |
| Schema | `schema-catalog` | The catalog lists the current ArchMap, LawPolicy, ArchSig analysis packet, and validation report artifacts. |

`archsig-analysis-packet-v0` currently includes the main AAT structural reading
families: signature axes, obstruction circuits, workflow risk, spectral
readings, transfer bridges, ACTS curvature / transfer support,
`ArchitectureSpectrumReport`, Homotopy / Holonomy / Stokes readings,
`ArchitectureHomotopyReport`, AAT observation-axis readings, monodromy /
boundary holonomy readings, repair candidates, path / homotopy / diagram
readings, bounded judgements, and LLM interpretation. These are ArchSig outputs,
not first-class ArchMap outputs.

`analysis-summary` is the preferred first reading surface. It reports the
measured verdict, quality counts, measurement-status counts, dominant findings,
action queue, trend diagnosis, review support, compact section summaries,
detail index, measurement basis, and metadata. The full evidence remains in
`archsig-analysis-packet.json`.

Large ArchMaps may be authored in shards for review and parallel generation,
but current commands consume the exported monolithic
`archmap-observation-map-v0` artifact.

Pre-Atom ArchSig commands were removed instead of kept as compatibility shims.
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
- the bundled LLM skills under `skills/`
- the repository license

After extracting the archive, put the `archsig` executable on `PATH` or set
`ARCHSIG_BIN` to its path. Then use the bundled `skills/` directory as the LLM
agent interface. For normal analysis, start from `archmap-creater`,
`law-policy-creater`, `archsig-reader`, or `archsig-pr-reviewer`; the skills
call the CLI and read the AAT packet for the user.

## CLI Quick Start

Use the CLI directly for local smoke tests, scripted runs, CI, and skill
runtime calls. For user-facing analysis, prefer the skills below because they
carry the packet-reading and source-comparison workflow.

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- analyze \
  --archmap tools/archsig/tests/fixtures/minimal/archmap.json \
  --law-policy tools/archsig/tests/fixtures/minimal/law_policy.json \
  --out-dir .archsig/analyze
```

`llm-native-workflow` and `north-star-workflow` are compatibility aliases for
the same workflow. Use `analyze` in new docs, scripts, and CI.

This writes:

- `.archsig/analyze/archmap-validation.json`
- `.archsig/analyze/law-policy-validation.json`
- `.archsig/analyze/archsig-analysis-packet.json`
- `.archsig/analyze/archsig-analysis-detail-index.json`
- `.archsig/analyze/archsig-analysis-validation.json`
- `.archsig/analyze/llm-interpretation-packet.json`

`archsig-analysis-packet.json` is compact-first: large repeated string ref
sets are replaced by `archsig-detail-ref-v0` objects with counts, samples, and
detail refs. Full ref sets are stored through a dictionary-backed
`archsig-analysis-detail-index.json`.

For large ArchMaps, prefer the optimized binary:

```bash
cargo run --release --manifest-path tools/archsig/Cargo.toml -- analyze \
  --archmap .archsig/hilda/archmap.json \
  --law-policy .archsig/hilda/hilda-law-policy.json \
  --out-dir .archsig/analyze
```

`llm-interpretation-packet.json` contains the compact
`llmInterpretationPacket` reading surface from the analysis packet. Treat it as
structured review evidence with explicit measurement bounds, not as a
standalone decision record or automatic repair instruction.

To write the compact reading surface from those artifacts:

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- analysis-summary \
  --packet .archsig/analyze/archsig-analysis-packet.json \
  --archmap-validation .archsig/analyze/archmap-validation.json \
  --law-policy-validation .archsig/analyze/law-policy-validation.json \
  --analysis-validation .archsig/analyze/archsig-analysis-validation.json \
  --out .archsig/analyze/archsig-analysis-summary.json
```

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
| `archmap-creater` | Create bounded `archmap-observation-map-v0` artifacts from repository evidence. It keeps ArchMap as source-grounded Atom observations, molecule observations, semantic readings, concern hints, and gaps, not law-relative analysis. |
| `law-policy-creater` | Create project-specific `law-policy-v0` interpretation profiles from repository coding conventions, architecture rules, and user decisions. If docs do not define the law universe, ask the user before selecting laws. |
| `archsig-reader` | Run an ArchMap with a selected LawPolicy, read the `archsig-analysis-packet-v0`, compare high-priority readings with source evidence, and propose bounded improvements. It does not silently use a generic LawPolicy as project analysis. |
| `archsig-pr-reviewer` | Derive PR-local `archmap-delta-v0` from the base branch diff, run `pr-review` with base ArchMap and LawPolicy, read the changed code, and explain review focus in human code-review language. It stops if the base ArchMap or LawPolicy is missing. |

Typical use:

1. Use `archmap-creater` to produce or refine the ArchMap.
2. Use `law-policy-creater` to produce the selected LawPolicy for the target
   repository or subsystem.
3. Run `analyze`.
4. Use `archsig-reader` to interpret the packet and compare it with source
   evidence before proposing improvements.

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
