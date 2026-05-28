# ArchSig

`archsig` is an AAT structural review CLI. Its primary surface is the
LLM-native ArchMap / LawPolicy / ArchSig workflow: supplied
`archmap-observation-map-v0` evidence records source-grounded Atom
observations, a selected `law-policy-v0` defines the law universe and witness
rules, and ArchSig emits an `archsig-analysis-packet-v0` for LLM and human
review. Downstream AIR, theorem-check, Feature Report, and AAT Observable
Bundle artifacts are projected from that analysis packet.

ArchSig is not a Lean prover, extractor-completeness claim, architecture-lawfulness oracle, merge approval system, or SFT forecast engine. FieldSig owns SFT forecast, IntentMap, workflow evidence, operational feedback, dynamics, governance, and calibration under `tools/fieldsig`.

## Product Surface

| Surface | Current role | Boundary |
| --- | --- | --- |
| LLM-native analysis workflow | `llm-native-workflow`, `archmap`, `law-policy`, `archsig-analysis`, `validate-air`, `theorem-check`, `feature-report`, `aat-observable-bundle` | ArchMap is law-independent Atom observation evidence. LawPolicy selects the law universe. ArchSig owns law-relative molecule readings, obstruction circuits, signature axes, flatness readings, repair operation candidates, and LLM interpretation notes. |
| Legacy ArchMap projection workflow | `archmap-workflow`, `air-from-archmap` | Kept as a bounded compatibility review surface for older AIR/report consumers. It is not the current source of truth for LLM-native ArchSig analysis. |
| Bounded adapters | `adapter-scan` for Lean / Python import-graph Sig0 evidence, optional framework adapter evidence | Adapter output is an evidence supplier for conflict checks or legacy diff workflows; it retains `coverageBoundary`, `unsupportedConstructs`, `missingEvidence`, and `nonConclusions`, but it is not the ArchSig primary surface and does not produce a complete `ComponentUniverse`. |
| Revision comparison | `validate`, `snapshot`, `signature-diff` over explicit Sig0 adapter artifacts | Diff values must be read with measured / unmeasured boundaries and non-conclusions. |
| Review support | policy, law violation, policy decision, PR comment, PR quality analysis, schema compatibility | Tool output supports review; humans remain responsible for risk acceptance and product decisions. |

## Quick Start

Run the primary LLM-native analysis workflow:

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
- `.archsig/llm-native/air.json`
- `.archsig/llm-native/air-validation.json`
- `.archsig/llm-native/theorem-precondition-check.json`
- `.archsig/llm-native/feature-report.json`
- `.archsig/llm-native/aat-observable-bundle.json`
- `.archsig/llm-native/aat-observable-bundle-validation.json`

The analysis packet is the source of truth for downstream review artifacts.
`llm-interpretation-packet.json` is the same structured packet written for LLM
reading. It is not natural-language judgment, not a Lean proof, and not an
automatic repair instruction.

When language import-graph evidence is needed, run it explicitly as an adapter:

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- adapter-scan \
  --root tools/archsig/tests/fixtures/minimal \
  --policy tools/archsig/tests/fixtures/minimal/policy_measured_zero.json \
  --runtime-edges tools/archsig/tests/fixtures/minimal/runtime_edges.json \
  --out .archsig/adapter/sig0.json
```

Python adapter evidence is also explicit:

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- adapter-scan \
  --language python \
  --root path/to/repository \
  --source-root src \
  --package-root src \
  --out .archsig/adapter/python-sig0.json
```

Calling `archsig` without a subcommand intentionally fails. The old implicit scan-first path is no longer the default ArchSig workflow.

## Docs

- [Command Guide](docs/commands.md)
- [Artifacts And Boundaries](docs/artifacts-and-boundaries.md)
- [Operational Feedback](docs/operational-feedback.md)

`docs/tool/` is being rebuilt around the LLM-native ArchMap / LawPolicy /
ArchSig responsibility split. Older mixed tool documents are archived under
`docs/archive/2026-05-26-tool-docs-pre-archmap-primary/`.

## Codex Skills

`tools/archsig/skills/` contains AI-agent workflow bundles for ArchMap creation, PR artifact analysis, and AAT observable review. The skills read generated artifacts as bounded evidence and do not turn them into proof, forecast correctness, incident causality, global architecture truth, or automatic merge approval.

## Test

```bash
cargo test --manifest-path tools/archsig/Cargo.toml
```

If local incremental cache is broken:

```bash
CARGO_INCREMENTAL=0 cargo test --manifest-path tools/archsig/Cargo.toml
```
