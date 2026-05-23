# Tooling Examples

この文書では、同じ coupon feature extension を使って AIR、witness、report、dynamics artifact の
読み方を揃える。

## Good extension

```text
before:
  OrderService -> PaymentPort
  PaymentAdapter implements PaymentPort

feature:
  Coupon calculation

after:
  OrderService -> CouponPort
  CouponService -> CouponPort
  CouponService -> PaymentPort
```

良い extension では、coupon behavior は declared interface を通って core と相互作用する。

AIR では次の claim が分かれる。

```text
embedding claim
feature view claim
interaction claim
static split claim
coverage claim
```

## Hidden interaction witness

悪い extension の例:

```text
CouponService -> PaymentAdapter.internalCache
```

witness:

```text
witnessId: coupon-hidden-payment-cache
layer: static
kind: hidden_interaction
extensionRole: interaction
extensionClassification: non_split
measurementBoundary: measuredNonzero
```

この witness は、static split failure と lifting failure の候補である。
runtime flatness や semantic flatness の結論ではない。

## Semantic witness

rounding order が変わる場合、semantic diagram は non-fillable になりうる。

```text
diagram:
  apply coupon then round
  ~
  round then apply coupon

observation:
  amount differs
```

semantic witness:

```text
witnessId: coupon-discount-rounding-order
layer: semantic
kind: nonfillability_witness
measurementBoundary: measuredNonzero
```

## Feature Extension Report reading

Report summary:

```text
splitStatus: non_split
introducedObstructionWitnesses:
  - coupon-hidden-payment-cache
  - coupon-discount-rounding-order
repairSuggestions:
  - introduce CouponPort
  - move cache access behind PaymentPort contract
  - define explicit coupon/payment semantic contract
nonConclusions:
  - runtime completeness
  - semantic completeness beyond selected diagrams
  - formal theorem discharge
```

## Dynamics reading

良い coupon example は seed attractor になる。
悪い coupon shortcut は、将来の feature addition を同じ hidden dependency へ誘導する
bad exemplar になる。

```text
good exemplar
  -> better operation support
  -> lower hidden interaction risk

bad exemplar
  -> shortcut basin
  -> repeated hidden interaction
```

この reading は empirical / tooling artifact として扱い、因果 theorem とは読まない。

## ArchMap supplied JSON flow

`tools/archsig/tests/fixtures/minimal/archmap.json` は、supplied JSON から ArchMap MVP flow を
検証する fixture である。

```text
archmap.json
  -> archmap-validation-report-v0
  -> aat-air-v0
  -> validate-air
  -> theorem-check
  -> feature-report
```

fixture は次を同時に表す。

- AAT concept: component、relation、signature axis、obstruction witness、law / policy boundary、flatness precondition。
- SOLID / Layered Architecture: SRP responsibility region、reason-to-change candidate、layer direction policy。
- Semantic structure: selected semantic diagram、semantic commutation claim、nonfillability witness。
- Boundary: measured semantic evidence、unmeasured runtime evidence、assumed policy boundary、private / unavailable context、conflict review cue。

`archmap.json` の `sourceInventoryRef` は、独立 fixture
`tools/archsig/tests/fixtures/minimal/archmap_source_inventory.json` を指す。この source inventory
artifact は LLM に渡した bounded review universe を再現するためのもので、included / excluded /
unavailable / private refs、hash、known blind spots、selection boundary を保持する。`archmap`
validation は、この artifact の欠落や `sourceUniverse` との不整合を architecture ground truth
判定ではなく `sourceInventoryChecks` の boundary finding として報告する。

`archmap` validation は、LLM-authored measured claim と formal/proved claim を混同しない。
`air-from-archmap` projection は、semantic measured zero と semantic unmeasured、missing evidence と
measured zero、conflict と resolved claim を混同しない。

## ArchMap expressiveness suite v0

`tools/archsig/tests/fixtures/expressiveness/archmap_expressiveness_suite_v0.json` は、
ArchMap が schema field の有無ではなく、AAT/SFT relevant な構造と boundary を loss-aware に
保持できるかを見る regression fixture である。source inventory は
`tools/archsig/tests/fixtures/expressiveness/archmap_source_inventory.json` に分離し、
included / excluded / unavailable / private / hash / blind spot を固定する。

suite v0 は次の case を一つの supplied JSON artifact に収める。

| Case | Expected boundary |
| --- | --- |
| `layered_policy_violation` | `LawPolicyPreservation` の supplied assumption。policy disagreement は review cue。 |
| `srp_responsibility_split` | SRP responsibility region を `LawPolicyPreservation` candidate として保持する。 |
| `contract_preservation` | selected contract observation を `SemanticDiagramPreservation` candidate として保持する。 |
| `semantic_commutation` | selected observation equivalence を `SemanticCommutationPreservation` candidate として保持する。 |
| `semantic_non_commutation` | selected non-commutation を `NonfillabilityWitnessPreservation` candidate として保持する。 |
| `event_sourcing_projection` | event replay / read-model projection を semantic diagram candidate として保持する。 |
| `saga_compensation` | missing compensation を nonfillability witness candidate として保持する。 |
| `runtime_static_disagreement` | runtime evidence unavailable を `CoverageExactnessBoundary` block として保持する。 |
| `framework_convention_boundary` | framework convention expansion を unmeasured coverage boundary として保持する。 |
| `dynamic_plugin_blind_spot` | private dynamic plugin registry を missing evidence / unmeasured boundary として保持する。 |

`cli_locks_archmap_expressiveness_suite_v0_boundaries` は `archmap` validation、
`air-from-archmap`、`validate-air`、`theorem-check`、`feature-report` を通し、
expected validation boundary、AIR semantic diagram / nonfillability witness、theorem-check checklist、
feature-report cue を固定する。suite pass は LLM accuracy、architecture lawfulness、semantic
preservation、Lean proof discharge を結論しない。
