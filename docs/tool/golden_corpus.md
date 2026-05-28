# LLM-Native Golden Corpus

The current ArchSig golden corpus is built around the LLM-native pipeline:

```text
ArchMap observation artifact
  + LawPolicy
  -> ArchSig analysis packet
  -> LLM interpretation / human review
```

## Positive Fixtures

- `tools/archsig/tests/fixtures/minimal/archmap.json`
- `tools/archsig/tests/fixtures/minimal/law_policy.json`
- `tools/archsig/tests/fixtures/minimal/archsig_analysis_packet.json`
- `tools/archsig/tests/fixtures/minimal/law_policy_layer_only.json`
- `tools/archsig/tests/fixtures/minimal/archsig_analysis_packet_layer_only.json`

The layer-only LawPolicy fixture reuses the same ArchMap and produces a
different ArchSig packet. This fixes the requirement that ArchMap remains
law-independent and can be reanalyzed under multiple selected LawPolicy
artifacts.

## Negative Fixtures

- `tools/archsig/tests/fixtures/minimal/archmap_invalid_concern_promoted.json`
- `tools/archsig/tests/fixtures/minimal/archmap_invalid_gap_measured_zero.json`

These fixtures lock the two main guardrails:

- `concernHints` are not obstruction circuits.
- `observationGaps` are not measured zero.

## FieldSig Handoff Fixtures

- `tools/fieldsig/tests/fixtures/minimal/llm_native_handoff/archmap.json`
- `tools/fieldsig/tests/fixtures/minimal/llm_native_handoff/law_policy.json`
- `tools/fieldsig/tests/fixtures/minimal/llm_native_handoff/law_policy_layer_only.json`
- `tools/fieldsig/tests/fixtures/minimal/llm_native_handoff/archsig_analysis_packet.json`
- `tools/fieldsig/tests/fixtures/minimal/llm_native_handoff/archsig_analysis_packet_layer_only.json`

These files are handoff fixtures. FieldSig wiring is handled in the dedicated
FieldSig issue; the fixtures exist here so the handoff target is stable. The
FieldSig test suite reads these files as JSON contract fixtures and locks their
schema versions, LawPolicy split, and concern/gap guardrails.
