# ArchSig

`archsig` is the ArchMap / LawPolicy / ArchSig analysis CLI. It is intentionally
small: the current surface is the LLM Atom ArchMap route from supplied
`archmap-observation-map-v0` evidence and selected `law-policy-v0` into an
`archsig-analysis-packet-v0`.

ArchSig is not a Lean prover, extractor-completeness claim, architecture
lawfulness oracle, merge approval system, or SFT forecast engine. FieldSig owns
forecast, governance, calibration, and operational feedback under
`tools/fieldsig`.

## Product Surface

| Surface | Commands | Boundary |
| --- | --- | --- |
| ArchMap validation | `archmap`, `archmap-generate` | ArchMap records source-grounded Atom observations and concern hints. It does not select laws or output obstruction circuits. |
| LawPolicy | `law-policy` | LawPolicy selects the law universe, witness rules, signature axes, coverage requirements, and non-conclusions. |
| ArchSig analysis | `archsig-analysis`, `llm-native-workflow` | ArchSig combines ArchMap and LawPolicy into law-relative molecule readings, obstruction circuits, signature axes, flatness readings, repair candidates, and LLM interpretation notes. |
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

This writes:

- `.archsig/llm-native/archmap-validation.json`
- `.archsig/llm-native/law-policy-validation.json`
- `.archsig/llm-native/archsig-analysis-packet.json`
- `.archsig/llm-native/archsig-analysis-validation.json`
- `.archsig/llm-native/llm-interpretation-packet.json`

`llm-interpretation-packet.json` is the same structured packet written for LLM
reading. It is not a natural-language judgment, Lean proof, or automatic repair
instruction.

Calling `archsig` without a subcommand intentionally fails. The old implicit
scan-first path is no longer an ArchSig workflow.

## Docs

- [Command Guide](docs/commands.md)
- [Artifacts And Boundaries](docs/artifacts-and-boundaries.md)
- [Sharded ArchMap Design](docs/sharded-archmap.md)

## Test

```bash
cargo test --manifest-path tools/archsig/Cargo.toml
```
