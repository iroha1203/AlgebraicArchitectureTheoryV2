# ArchSig

`archsig` is the ArchMap -> AAT analysis packet CLI. It reads supplied
`archmap-observation-map-v0` evidence and a selected interpretation profile
(`law-policy-v0` JSON) into a North Star `archsig-analysis-packet-v0` for LLM
and human review.

ArchSig is not a Lean prover, extractor-completeness claim, architecture
lawfulness oracle, merge approval system, or SFT forecast engine. FieldSig owns
forecast, governance, calibration, and operational feedback under
`tools/fieldsig`.

## Product Surface

| Surface | Commands | Boundary |
| --- | --- | --- |
| ArchMap validation | `archmap`, `archmap-generate` | ArchMap records source-grounded Atom observations and concern hints. It does not select laws or output obstruction circuits. |
| Interpretation profile | `law-policy`, `interpretation-profile` | The profile selects the LawUniverse, witness rules, signature axes, coverage requirements, exactness assumptions, and non-conclusions. It is not AAT itself. |
| ArchSig analysis | `archsig-analysis`, `aat-analysis`, `llm-native-workflow`, `north-star-workflow` | ArchSig combines ArchMap and the profile into AAT concept surfaces, architecture state, design pressure, change impact, analytic axes, semantic coupling/cohesion, workflow risk readings, design principle readings, bounded judgements, repair operation deltas, and an LLM interpretation packet. |
| Schema | `schema-catalog` | The catalog lists only the current LLM Atom ArchMap artifacts. |

Large ArchMaps may be authored in shards for review and parallel generation,
but current commands consume the exported monolithic
`archmap-observation-map-v0` artifact.

Pre-Atom ArchSig commands were removed instead of kept as compatibility shims.
Git history is the archive for those workflows.

## Quick Start

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- llm-native-workflow \
  --archmap tools/archsig/tests/fixtures/minimal/archmap.json \
  --law-policy tools/archsig/tests/fixtures/minimal/law_policy.json \
  --out-dir .archsig/llm-native
```

`north-star-workflow` is the same current workflow under the North Star name.

This writes:

- `.archsig/llm-native/archmap-validation.json`
- `.archsig/llm-native/law-policy-validation.json`
- `.archsig/llm-native/archsig-analysis-packet.json`
- `.archsig/llm-native/archsig-analysis-validation.json`
- `.archsig/llm-native/llm-interpretation-packet.json`

`llm-interpretation-packet.json` is the same structured packet written for LLM
reading. It is not a natural-language judgment, Lean proof, architecture truth,
merge approval, or automatic repair instruction.

Calling `archsig` without a subcommand intentionally fails. The old implicit
scan-first path is no longer an ArchSig workflow.

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
