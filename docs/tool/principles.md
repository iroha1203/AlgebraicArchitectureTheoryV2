# Tooling Principles

Tooling の目的は、AAT の理論語彙を実用 artifact と workflow へ写すことである。
目的は「完全な architecture model を自動抽出すること」ではない。

## 一方向依存

依存方向は次に固定する。

```text
math theory
  -> Lean theorem / proof obligation
  -> tooling artifact
  -> empirical workflow
```

tool 側文書は `docs/aat/` の理論を参照してよい。逆向きに、理論本文が tool artifact の
存在、schema version、CI workflow、PR review workflow を前提にしてはいけない。

## Claim separation

tooling は claim level を分ける。

```text
formal claim
measured claim
empirical claim
hypothesis claim
```

formal claim は、該当する theorem package と precondition discharge に接続できる場合に限る。
measured claim は artifact と evidence に相対化される。empirical claim は dataset と
protocol に相対化される。hypothesis claim は検証前の研究仮説として扱う。

## Measurement boundary

tooling は zero と unknown を分ける。

```text
measuredZero
measuredNonzero
unmeasured
unavailable
private
notComparable
outOfScope
```

`unmeasured`、`unavailable`、`private`、`notComparable`、`outOfScope` を
`measuredZero` に丸めない。

## Non-conclusions

各 artifact は、少なくとも次を non-conclusion として保持できる必要がある。

```text
extractor completeness
runtime completeness
semantic completeness
Lean theorem discharge
formal claim promotion
incident reduction
causal effect
global architecture lawfulness
```

ある report が warning を出さないことは、architecture が lawful であることを意味しない。
ある axis が未評価であることは、axis が zero であることを意味しない。

## Tooling の価値

Tooling の価値は、結論を強くすることではなく、境界を明示して review 可能な artifact にする
ことである。

```text
source evidence
  -> measured axis
  -> claim boundary
  -> theorem precondition check
  -> report / decision / follow-up
```
