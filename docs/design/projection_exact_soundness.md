# Projection soundness と exact projection の使い分け

このメモは Issue #82 の設計整理である。`ProjectionSound` だけで十分な主張と、
`ProjectionExact` / `StrongDIPCompatible` が必要な主張を分ける。

## 方針

`ProjectionSound` は、具体依存が抽象グラフに漏れなく写ることを表す。したがって、
具象グラフから抽象グラフへの forward preservation を言う主張では soundness だけで
十分である。

`ProjectionComplete` は、抽象グラフ上の辺が何らかの具体依存に由来することを表す。
したがって、抽象グラフの辺を具体世界へ戻して読む主張や、抽象グラフに余分な辺が
ないことを要求する主張では completeness が必要である。

`ProjectionExact` は `ProjectionSound` と `ProjectionComplete` の組であり、
`StrongDIPCompatible` は `ProjectionExact` に `RepresentativeStable` を加えた
exact-projection refinement として扱う。現行 Lean の `DIPCompatible` は
`ProjectionSound` と `RepresentativeStable` を要求する strong operational
formalization であり、`StrongDIPCompatible` の別名ではない。

## soundness-only で扱う主張

次の主張は、抽象グラフに余分な辺が存在しても壊れない。

- 具体依存が抽象依存として表現されること。
- `ProjectionSound` なら `projectionSoundnessViolation = 0` になること。
- 測定 universe が concrete edge を閉じている場合に、violation 0 から
  `ProjectionSound` を復元すること。
- `mapReachable` のように、具象到達可能性を抽象到達可能性へ送る bridge。
- Signature v1 の `projectionSoundnessViolation` 軸。

`projectionSoundnessViolation` は soundness violation count であり、
`ProjectionComplete` の欠如は測らない。したがって、この軸は
`ProjectionExact` の代替ではなく、projection bridge の片側だけを測る
executable metric である。

## exact projection が必要な主張

次の主張では、抽象グラフ上の辺が具体依存に由来することを使うため、
`ProjectionComplete` または `ProjectionExact` が必要である。

- 抽象依存を具体依存 witness へ戻す主張。
- 抽象グラフが、具体依存から誘導される商グラフと同じ辺集合を持つという主張。
- 抽象グラフ上で見つかった循環や経路が、具体依存の witness を持つという主張。
- 「抽象グラフに余分な設計上の依存がない」という診断。
- `StrongDIPCompatible` から `DIPCompatible` へ降りる refinement の説明。
- `ProjectionExact` と `RepresentativeStable` の下で、選択代表の
  `ProjectedDeps` を abstract edge と同値に読む主張。

ただし、exact projection が成り立っても、抽象グラフ自体の非循環性や
`Decomposable` は従わない。抽象層の循環を排除するには Layered などの大域構造制約が
別途必要である。

## Lean theorem statement 候補

既存の Lean では次が証明済みである。

- `projectionSound_of_projectionExact`
- `projectionComplete_of_projectionExact`
- `dipCompatible_of_strongDIPCompatible`
- `projectionSoundnessViolation_eq_zero_of_projectionSound`
- `projectionSound_of_projectionSoundnessViolation_eq_zero`
- `projectedConcreteEdge_of_projectionComplete`
- `abstractEdge_iff_projectedConcreteEdge_of_projectionExact`
- `strongDIPCompatible_of_projectionExact_representativeStable`
- `quotientWellDefined_of_projectionExact_representativeStable`
- `projectedDeps_iff_abstractEdge_of_projectionExact_representativeStable`
- `projectedDeps_iff_abstractEdge_of_strongDIPCompatible`

Issue #107 では、次の片方向 witness theorem を追加した。

```text
ProjectionComplete G π GA ->
  GA.edge a b ->
  exists c d, π.expose c = a and π.expose d = b and G.edge c d
```

これは定義の展開補題であり、抽象辺を具体 witness へ戻す bridge の入口になる。

同じ Issue #107 では、次の exact projection edge-level bridge theorem も追加した。

```text
ProjectionExact G π GA ->
  GA.edge a b <->
    exists c d, π.expose c = a and π.expose d = b and G.edge c d
```

これは exact projection を「抽象辺集合と投影された具体辺集合の一致」として読む
bridge theorem である。

Issue #352 では、exact projection に representative stability を足した
quotient-level bridge を追加した。

```text
ProjectionExact G π GA ->
  RepresentativeStable G π ->
    ProjectedDeps G π c a <-> GA.edge (π.expose c) a
```

この theorem は、completeness で抽象辺の具体 witness を取り、representative stability
で witness 側の代表から選択代表 `c` へ dependency を移す。したがって
`ProjectionSound` だけから completeness や quotient exactness を推論するものではない。

抽象循環や抽象経路を具体 witness へ持ち上げる theorem は、上の edge-level bridge の
後続に置く。これは path / walk 側の構造を使うため、projection bridge だけの Issue には
混ぜない。

## Issue #82 の結論

Issue #82 では、`projectionSoundnessViolation` を soundness-only metric として固定し、
exact projection は抽象辺を具体依存由来として読むための refinement として分離する。
`DIPCompatible` と `StrongDIPCompatible` の使い分けは
[AAT v2 数学設計書の Design principle classification](../aat_v2_mathematical_design.md#41-design-principle-classification) と整合する。
