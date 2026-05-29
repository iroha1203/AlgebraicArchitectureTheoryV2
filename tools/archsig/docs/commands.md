# ArchSig Commands

`archsig` is now the AAT analysis engine over ArchMap. The current route is:

```text
archmap-observation-map-v0
  + interpretation profile (law-policy-v0 JSON)
  -> archsig-analysis-packet-v0
  -> LLM interpretation
  -> FieldSig handoff
```

ArchSig no longer exposes pre-Atom scan, projection, report, or PR-review
commands. Git history is the archive for those workflows.
FieldSig owns SFT forecast, IntentMap, operational feedback, governance, and
calibration commands under `tools/fieldsig`.

## Primary Workflow

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- llm-native-workflow \
  --archmap tools/archsig/tests/fixtures/minimal/archmap.json \
  --law-policy tools/archsig/tests/fixtures/minimal/law_policy.json \
  --out-dir .archsig/llm-native
```

`north-star-workflow` is a visible alias for the same workflow:

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- north-star-workflow \
  --archmap tools/archsig/tests/fixtures/minimal/archmap.json \
  --law-policy tools/archsig/tests/fixtures/minimal/law_policy.json \
  --out-dir .archsig/north-star
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
  --out .archsig/llm-native/archmap-validation.json
```

Current commands intentionally keep the analysis contract monolithic. A future
bundle/export command should validate slice paths, duplicate ids, dangling
cross-slice refs, required/optional slice policy, allowed cross-slice
references, and source refs before writing the exported ArchMap.

## Step Commands

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- archmap \
  --input tools/archsig/tests/fixtures/minimal/archmap.json \
  --out .archsig/llm-native/archmap-validation.json

cargo run --manifest-path tools/archsig/Cargo.toml -- interpretation-profile \
  --input tools/archsig/tests/fixtures/minimal/law_policy.json \
  --out .archsig/llm-native/law-policy-validation.json

cargo run --manifest-path tools/archsig/Cargo.toml -- aat-analysis \
  --archmap tools/archsig/tests/fixtures/minimal/archmap.json \
  --law-policy tools/archsig/tests/fixtures/minimal/law_policy.json \
  --out .archsig/llm-native/archsig-analysis-packet.json \
  --validation-out .archsig/llm-native/archsig-analysis-validation.json \
  --llm-interpretation-out .archsig/llm-native/llm-interpretation-packet.json
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
  --out .archsig/llm-native/archmap-generation-protocol.json
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
