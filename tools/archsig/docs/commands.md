# ArchSig Commands

`archsig` is now a small LLM Atom ArchMap CLI. The current route is:

```text
archmap-observation-map-v0
  + law-policy-v0
  -> archsig-analysis-packet-v0
  -> FieldSig handoff
```

ArchSig no longer exposes the old Sig0 / AIR / Feature Report / theorem-check /
PR governance command surface. Git history is the archive for those workflows.
FieldSig owns SFT forecast, IntentMap, operational feedback, governance, and
calibration commands under `tools/fieldsig`.

## Primary Workflow

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- llm-native-workflow \
  --archmap tools/archsig/tests/fixtures/minimal/archmap.json \
  --law-policy tools/archsig/tests/fixtures/minimal/law_policy.json \
  --out-dir .archsig/llm-native
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

## Step Commands

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- archmap \
  --input tools/archsig/tests/fixtures/minimal/archmap.json \
  --out .archsig/llm-native/archmap-validation.json

cargo run --manifest-path tools/archsig/Cargo.toml -- law-policy \
  --input tools/archsig/tests/fixtures/minimal/law_policy.json \
  --out .archsig/llm-native/law-policy-validation.json

cargo run --manifest-path tools/archsig/Cargo.toml -- archsig-analysis \
  --archmap tools/archsig/tests/fixtures/minimal/archmap.json \
  --law-policy tools/archsig/tests/fixtures/minimal/law_policy.json \
  --out .archsig/llm-native/archsig-analysis-packet.json \
  --validation-out .archsig/llm-native/archsig-analysis-validation.json \
  --llm-interpretation-out .archsig/llm-native/llm-interpretation-packet.json
```

`law-policy --fixture` emits the canonical minimal `law-policy-v0` fixture.

## ArchMap Generation Protocol

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- archmap-generate \
  --source-inventory tools/archsig/tests/fixtures/minimal/archmap_source_inventory.json \
  --prompt-pack docs/tool/archmap_prompt_pack.md \
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

Removed commands include `adapter-scan`, `validate`, `snapshot`,
`signature-diff`, `air`, `air-from-archmap`, `validate-air`,
`feature-report`, `theorem-check`, `aat-observable-bundle`,
`archmap-workflow`, `architecture-policy`, `law-violation-report`,
`organization-policy`, `policy-decision`, `pr-comment`,
`baseline-suppression`, `pr-quality-analysis`, `report-artifacts`, and
`schema-compatibility`.
