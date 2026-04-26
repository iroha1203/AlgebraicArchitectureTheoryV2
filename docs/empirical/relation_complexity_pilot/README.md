# relationComplexity pilot baseline

Lean status: `empirical hypothesis` / pilot validation.

Issue [#154](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/154)
の pilot として、Event Sourcing / Saga / CRUD を含む小さな commerce 状態遷移
sample を選び、`relationComplexity` の手動 baseline と
`archsig relation-complexity` の出力差分を記録した。

この pilot の目的は統計的結論ではない。`RelationComplexityObservation` の
counting rule v0 が、手動レビュー済み candidate から構成要素ベクトルを再現できるか、
また excluded evidence / unsupported framework / ambiguous candidate を primary count
から分離できるかを確認する。

## 対象

- repository: `aatv2/reference-commerce-state-transitions`
- revision: `pilot-2026-04-26`
- measurement root: `samples/commerce-state-transitions`
- language: TypeScript sample
- frameworks: `event-sourcing`, `saga`, `crud`
- workflow: `checkout-payment-fulfillment`
- component: `CommerceCheckout`

対象 workflow は、注文状態制約、在庫予約制約、Saga 補償、event log からの
read model projection、支払い retry と idempotency key を持つ小さな手動 sample
として扱う。これは実 repository からの完全抽出ではなく、rule set v0 の pilot
baseline である。

## 手動 baseline

[`baseline/commerce_state_transitions_manual_baseline.json`](baseline/commerce_state_transitions_manual_baseline.json)
に手動ラベルと count を保存した。

| component | manual count |
| --- | ---: |
| `constraints` | 2 |
| `compensations` | 2 |
| `projections` | 1 |
| `failureTransitions` | 3 |
| `idempotencyRequirements` | 2 |
| `relationComplexity` | 10 |

`relationComplexity` は構成要素の合計値として保存するが、解釈では各 component
を残す。Event Sourcing / Saga / CRUD の優劣を単一スコアで決めるものではない。

## extractor output との差分

入力 candidate は
[`candidates/commerce_state_transitions_candidates.json`](candidates/commerce_state_transitions_candidates.json)、
生成された observation は
[`observations/commerce_state_transitions_observation.json`](observations/commerce_state_transitions_observation.json)
に保存する。

| component | manual | extractor | delta |
| --- | ---: | ---: | ---: |
| `constraints` | 2 | 2 | 0 |
| `compensations` | 2 | 2 | 0 |
| `projections` | 1 | 1 | 0 |
| `failureTransitions` | 3 | 3 | 0 |
| `idempotencyRequirements` | 2 | 2 | 0 |
| `relationComplexity` | 10 | 10 | 0 |

この pilot では accepted evidence の count は手動 baseline と一致した。差分 0 は
「実 repository で完全抽出できる」という主張ではなく、review 済み candidate JSON に対して
rule set v0 の正規化と counting が意図どおり動くことを示す tooling-side observation
である。

## 除外 evidence と曖昧な候補

primary count から外した evidence は次の通り。

| id / path | handling | reason |
| --- | --- | --- |
| `generated-orm-unique-index` | excluded | `framework-generated` なので application-owned transition logic として数えない。 |
| `crud-field-format-validation` | excluded | CRUD field validation だが状態遷移分岐を増やさないため `false-positive` とした。 |
| `ambiguous-shipping-provider-hook` | review later | ownership が `unknown` のため primary count から外す。 |
| `src/checkout/CheckoutWorkflow.spec.ts` | excluded | test fixture。 |

unsupported framework の扱いは
[`candidates/unsupported_framework_probe.json`](candidates/unsupported_framework_probe.json)
と
[`observations/unsupported_framework_probe_observation.json`](observations/unsupported_framework_probe_observation.json)
で確認した。`vendor-workflow-x` は `relation-complexity-rules/v0` の supported
framework ではないため、candidate は `unsupported-framework:vendor-workflow-x`
として `excludedEvidence` に残り、count は 0 になる。

## Lean core への扱い

この pilot は `empirical hypothesis` / pilot validation であり、状態遷移構造を
Lean core に入れる判断はしない。現時点では `relationComplexity` を workflow-level
observation として保持し、repository-level value は観測の集約として扱う方針を維持する。

## 再生成手順

```bash
cargo run --quiet --manifest-path tools/archsig/Cargo.toml -- relation-complexity \
  --input docs/empirical/relation_complexity_pilot/candidates/commerce_state_transitions_candidates.json \
  --out docs/empirical/relation_complexity_pilot/observations/commerce_state_transitions_observation.json

cargo run --quiet --manifest-path tools/archsig/Cargo.toml -- relation-complexity \
  --input docs/empirical/relation_complexity_pilot/candidates/unsupported_framework_probe.json \
  --out docs/empirical/relation_complexity_pilot/observations/unsupported_framework_probe_observation.json
```

検証では、上記 2 つの observation 生成に加えて `cargo test` の
`relation_complexity` 関連 test を実行する。
