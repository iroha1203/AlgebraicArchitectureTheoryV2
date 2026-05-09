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
