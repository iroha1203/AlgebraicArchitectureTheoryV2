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
retained `pr-review` command reads ArchMapStore change artifacts and ArchSig
packets; raw diff is only an optional scoping hint.
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
- `archsig-analysis-packet.json`
- `archsig-analysis-validation.json`
- `llm-interpretation-packet.json`

`llm-interpretation-packet.json` is the same structured packet written for LLM
reading. It is not a natural-language judgement, Lean proof, architecture
lawfulness certificate, or automatic repair instruction.

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
review. It does not replace the full packet or validation reports.

## Lightweight PR Review

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- pr-review \
  --delta tools/archsig/tests/fixtures/pr_review/archmap_delta.json \
  --commit tools/archsig/tests/fixtures/pr_review/archmap_commit.json \
  --base-packet tools/archsig/tests/fixtures/minimal/archsig_analysis_packet.json \
  --head-packet tools/archsig/tests/fixtures/coupon_rounding/archsig_analysis_packet.json \
  --diff-hint tools/archsig/tests/fixtures/pr_review/raw_diff_hint.diff \
  --out .archsig/pr-review/archsig-pr-review.json
```

`pr-review` is the CI-friendly ArchSig surface for small PR review. Its
canonical inputs are `archmap-delta-v0`, `archmap-commit-v0`, and base/head
`archsig-analysis-packet-v0` artifacts. The optional `--diff-hint` path is
recorded as scope only; ArchSig does not parse raw diff as semantic, state,
effect, authority, or boundary evidence. The report summarizes measured
monodromy witnesses, operation-order sensitivity, boundary holonomy, missing
filler / lifting evidence, coverage gaps, and review focus. It is not a merge
safety decision and does not replace FieldSig PR / diff / change-vector
evolution analysis.

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
