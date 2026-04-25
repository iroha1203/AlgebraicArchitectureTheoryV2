# 設計原則の分類

## 方針

本研究では、設計原則を「どの不変量を保証・保存・改善するか」で分類する。

SOLID は唯一の万能原理ではない。SOLID は局所的な契約・抽象・置換の健全性を与えるが、大域的な分解可能性や実行時収束性を単独では保証しない。

この文書の分類は、自然言語で語られる設計原則に対する唯一の正しい形式化ではない。本研究における操作的形式化である。

## 分類表

| 設計原則 / パターン | 圏論的・代数的意味 | 主に保証する不変量 | 層 |
| --- | --- | --- | --- |
| SRP | 対象の責務境界の単純化 | 局所凝集性 | 局所契約層 |
| OCP | 既存射を壊さない拡張 | 拡張安定性 | 局所契約層 |
| LSP | 観測関手で同値な実装の置換 | 置換可能性 | 局所契約層 |
| ISP | 射影の細分化 | インターフェース分離 | 局所契約層 |
| DIP | 抽象商への射影整合性 | 商の well-defined 性 | 局所契約層 |
| Layered Architecture | ranking 関数の存在 | 分解可能性 / 非循環性 | 大域構造層 |
| Clean Architecture | 内向き依存制約 | 境界保存 | 大域構造層 |
| Event Sourcing | イベント列を自由モノイドとして保持し、後段で関係式を追加 | 履歴再構成性 | 状態遷移代数層 |
| Saga | 弱い補償射の追加 | 局所回復性 | 状態遷移代数層 |
| CRUD | 状態上書き関係式の追加 | 操作単純性 / 履歴喪失 | 状態遷移代数層 |
| Circuit Breaker | 障害伝播射の遮断 | 障害局所性 | 実行時依存層 |
| Replicated Log | 条件付き順序合意 | 条件付き収束性 | 分散収束層 |

## 役割分担

### SOLID

SOLID は局所契約層の原則として扱う。

- SRP は、責務境界の過剰な混合を抑える。
- OCP は、既存構造を壊さない拡張を要求する。
- LSP は、内部構造ではなく観測可能な振る舞いの一致を要求する。
- ISP は、不要な依存を避けるために射影を細分化する。
- DIP は、具体実装から抽象商への射影が整合的であることを要求する。

ただし、これらは大域的な循環不在を直接保証しない。したがって、SOLID 風の局所条件を満たしても Decomposable が従うとは限らない。

### Layered / Clean Architecture

Layered Architecture と Clean Architecture は大域構造層の原則として扱う。

Layered Architecture は、依存グラフに ranking 関数を与えることで、依存方向を単調化する。これにより、循環を排除し、分解可能性の証人を与える。

Clean Architecture は、境界の内外を区別し、依存方向を内向きに制約する。これは境界保存の原則として扱う。

### Event Sourcing / Saga / CRUD

これらは状態遷移代数層の設計として扱う。

- Event Sourcing は履歴を自由モノイドとして保持し、状態を fold で再構成する。ただし、実システムでは冪等性、順序制約、projection、snapshot などの関係式が後から追加される。自由モノイド性は基盤ログの性質であり、派生モデル全体が無制約であるという意味ではない。
- Saga は前進射と補償射を対にし、局所回復性を追加する。ただし、補償射は一般に逆射ではない。`f ; compensate(f) = id` ではなく、`f ; compensate(f) ≈ acceptable_state` という弱い回復構造として扱う。
- CRUD は状態を直接上書きし、履歴を失う代わりに操作を単純化する。

この層では、関係式の複雑度、補償条件、履歴再構成性が主要な評価軸になる。

`relationComplexity` はまず empirical metric として扱う。初期設計では
`constraints`, `compensations`, `projections`, `failureTransitions`,
`idempotencyRequirements` の構成要素を保持し、派生的に合計値を見る。
詳細は [relation_complexity_design.md](design/relation_complexity_design.md) に置く。

### Circuit Breaker / Replicated Log

これらは実行時依存・分散収束層の設計として扱う。

Circuit Breaker は障害伝播を遮断し、障害局所性を改善する。

この評価対象は静的依存グラフではなく `RuntimeDependencyGraph` である。Lean core では runtime edge の存在だけを 0/1 graph として扱い、timeout budget, retry policy, failure mode, circuit breaker coverage などの metadata は extractor / empirical tooling 側に残す。

Replicated Log は quorum、failure model、network partition、availability などの前提条件の下で順序合意と収束性を保証する。収束性は無条件の性質ではなく、可用性や分断耐性との緊張を含む条件付き保証として扱う。

## SOLID 不完全性の位置づけ

重要な主張は次である。

```text
SOLID-style local contracts do not imply Decomposable(G)
SOLID-style local contracts and StrictLayered(G) imply Decomposable(G)
```

意味は次である。

- 本研究の操作的形式化における SOLID-style local contracts は局所健全性を担う。
- Layered は大域分解可能性を担う。
- 両者は競合するものではなく、異なる不変量を保証する。

この整理により、SOLID を万能視せず、設計原則の役割分担を明確にできる。

## LocalContract-style counterexample の形

2点循環 `A -> B`, `B -> A` は最小反例だが、それだけでは局所契約条件の真空充足に見える危険がある。したがって、Lean 実装では次のような非真空な循環例も用意する。

```text
Components:
  OrderService
  PaymentPort
  PaymentAdapter

Responsibilities:
  OrderService     : order orchestration
  PaymentPort      : payment abstraction
  PaymentAdapter   : concrete payment integration

Abstraction:
  PaymentAdapter projects to PaymentPort

Observation:
  PaymentAdapter and PaymentPort agree on the public payment behavior

Dependencies:
  OrderService   -> PaymentPort
  PaymentAdapter -> OrderService
```

ここに `PaymentPort -> PaymentAdapter` のような実装逆流を加えると、局所的には責務・抽象・観測関係を持つにもかかわらず、全体として循環が生じる。ただし、この例は DIP 違反に見える可能性があるため、完全な SOLID 充足反例とは呼ばない。位置づけは `LocalContract-style counterexample`、すなわち「非真空な局所契約データを持つ循環例」である。

## より強い SOLID 不完全性反例の候補

より強い反例では、抽象が具象へ依存する逆流を使わない。具象は抽象へ依存する向きを保ったまま、抽象層そのものが循環する例を使う。

```text
Components:
  OrderPort
  PaymentPort
  OrderAdapter
  PaymentAdapter

Abstraction:
  OrderAdapter   projects to OrderPort
  PaymentAdapter projects to PaymentPort

Dependencies:
  OrderPort      -> PaymentPort
  PaymentPort    -> OrderPort
  OrderAdapter   -> OrderPort
  PaymentAdapter -> PaymentPort
```

この例では、具象 `OrderAdapter` / `PaymentAdapter` は抽象 `OrderPort` / `PaymentPort` へ依存しており、具象への逆向き依存はない。それでも抽象層 `OrderPort <-> PaymentPort` が循環しているため、`Decomposable` は従わない。狙いは、DIP 風の依存方向を保っても、大域的な抽象層の循環を排除するには Layered などの別原則が必要であることを示すことである。

この段階では、旧 `AbstractCycleComponent` は完全な `DIPCompatible` 反例ではなく、`DIP-direction-only counterexample` として位置づける。より強い Lean 例では、`RespectsProjection`, `QuotientWellDefined`, `DIPCompatible`, `LSPCompatible` を満たしながら、抽象層循環により `¬ Decomposable` となる形を用意する。

`DIPCompatible` は、現行 Lean では単なる具象から抽象への依存方向制約ではなく、`ProjectionSound` と `RepresentativeStable` を合わせた strong operational formalization である。`StrongDIPCompatible` はこれに `ProjectionComplete` を加えた exact-projection refinement として扱う。したがって、DIP 系の局所契約が満たされることと、抽象層そのものが非循環・層化可能であることは別の不変量である。

この使い分けの詳細は [Projection soundness と exact projection の使い分け](design/projection_exact_soundness.md) に置く。Signature v1 の `projectionSoundnessViolation` は soundness-only metric であり、`StrongDIPCompatible` が要求する exact projection 全体を測るものではない。
