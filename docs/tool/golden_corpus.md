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
- `tools/archsig/tests/fixtures/expressiveness/archmap_atom_observation_suite_v0.json`
- `tools/archsig/tests/fixtures/coupon_rounding/archmap.json`
- `tools/archsig/tests/fixtures/coupon_rounding/archsig_analysis_packet.json`

The layer-only LawPolicy fixture reuses the same ArchMap and produces a
different ArchSig packet. This fixes the requirement that ArchMap remains
law-independent and can be reanalyzed under multiple selected LawPolicy
artifacts.

The expressiveness fixture is now an Atom observation regression. It locks
`atomObservations`, `moleculeObservations`, `semanticObservations`,
`observationGaps`, `projectionInfo`, and `concernHints`. Pre-Atom ArchMap
root fields are rejected rather than carried as compatibility inputs.

The coupon / tax / rounding fixture is the minimal semantic monodromy and
boundary holonomy example. It records
`p = round(tax(discount(subtotal)))` and
`q = round(discount(tax(subtotal)))`, locks a positive semantic
`mu_x(sigma)` witness in the golden ArchSig packet, and keeps PaymentAmount /
ReceiptAmount evidence as fixture-local tooling validation rather than a proof
theorem or general payment-safety claim.

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

FieldSig's current handoff command reads the ArchSig analysis packet, not raw
ArchMap observations:

```text
archsig-analysis-packet-v0 -> operation-support-estimate-v0
```

The projection keeps obstruction circuits, signature axes, repair candidates,
structural review boundaries, current-state / evolution boundary, and coverage
gaps as bounded current AAT structural state. It does not promote raw ArchMap
observations to forecast truth.
