# 証明義務と実証仮説

## 方針

この文書は、Lean で証明する命題と、実データで検証する仮説を分離する。

Lean では、定義が明確で全称命題として扱える構造的事実を証明する。現実コードベースの品質や変更コストとの相関は、Lean の定理ではなく実証研究の仮説として扱う。

未証明の主張を `axiom` や `sorry` で隠蔽しない。証明できていない命題は、この文書に証明義務または実証仮説として残す。

## Lean status の区分

この文書では、研究上の主張を次の status に分ける。

- `proved`: Lean で証明済みの命題。
- `defined only`: Lean 上の定義や executable metric はあるが、対応する正当性定理が未完了のもの。
- `future proof obligation`: Lean で証明すべき未解決命題。
- `empirical hypothesis`: 実コードベースや運用データで検証する仮説。Lean proof のブロッカーではない。

design / tooling 系の Issue は、上の status を補助する作業として扱う。たとえば `ComponentUniverse` と `FiniteArchGraph` の役割分担は `defined only` から future theorem へ進むための設計課題であり、empirical extractor は Lean theorem ではなく測定 tooling 側の課題である。

Sig0 extractor CLI は [Issue #51](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/51)
で `tools/sig0-extractor/` に置く。これは Lean module import graph から
`ArchitectureSignature` v0 の入力 JSON を作る `empirical hypothesis` / tooling output
であり、`ComponentUniverse` の完全な witness を生成したとは主張しない。

GitHub Issue の状態、優先度、milestone は GitHub を source of truth とする。この文書では Issue の一覧表を複製せず、研究上の文脈に必要な箇所だけ Issue link を置く。

## Lean で証明する命題

現在 Lean に存在する主要な定義・定理の一覧は
[Lean 定義・定理索引](formal/lean_theorem_index.md) に分離する。
この節では、研究上の proof obligation と Lean status の位置づけを扱う。

## 基本 convention

依存辺の向きは次で固定する。

```text
edge c -> d means component c depends on component d.
```

`StrictLayered` は、依存先が必ず下位層に落ちることを意味する。

```text
StrictLayered G :=
  exists layer : C -> Nat,
  for every edge c -> d, layer d < layer c
```

初期実装では、`Decomposable` の定義を次に固定する。

```text
Decomposable G := StrictLayered G
```

`Acyclic`, `FinitePropagation`, `Nilpotent` などを最初から `Decomposable` の定義に混ぜない。まず単純な定義から始め、次の定理として接続を育てる。

- `StrictLayered -> Acyclic`: `proved`
- `StrictLayered -> FinitePropagation`: `proved`
- `Acyclic + finite vertices -> StrictLayered`: `proved`, [Issue #23](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/23)
- `Acyclic <-> WalkAcyclic`: `proved`
- `DAG <-> Nilpotent adjacency matrix`: `proved` for finite
  `ComponentUniverse` natural-number adjacency powers,
  [Issue #55](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/55)

### 1. 依存グラフから thin category が生成される

任意の依存グラフ `G` について、到達可能性 `Reachable G a b` を射とする thin category `ComponentCategory G` を構成する。

定義候補:

```text
ArchGraph C
Reachable G : C -> C -> Prop
ComponentCategory G
```

証明すること:

- `Reachable` の反射性
- `Reachable` の推移性
- 恒等射があること
- 合成があること
- 結合律
- 単位律
- Hom が `Prop` なので thin category であること

注意:

`ComponentCategory` は到達可能性を Hom にするため、経路数、経路長、walk の本数を保持しない。定量評価では別途 `Walk`, `Path`, adjacency matrix, 必要なら `FreeCategoryOfGraph` を導入する。

将来の定量評価のため、次の walk 側述語も用意する。

```text
HasClosedWalk G := exists c, exists w : Walk G c c, 0 < w.length
WalkAcyclic G := not HasClosedWalk G
```

Lean status:

- `proved`: `Acyclic -> WalkAcyclic`
- `proved`: `WalkAcyclic -> Acyclic`

### 2. 分解可能性の基礎定理

有限依存グラフについて、層化可能性、非循環性、有限伝播を接続する。

初期段階の Lean status:

- `defined only`: `Decomposable G := StrictLayered G`
- `proved`: `StrictLayered -> Acyclic`
- `proved`: `StrictLayered -> FinitePropagation`
- `proved`: Layered な4層例が `Decomposable` であること
- `proved`: 2点循環グラフが `Decomposable` でないこと
- `proved`: `ComponentUniverse.strictLayered_of_acyclic` and
  `FiniteArchGraph.strictLayered_of_acyclic` construct `StrictLayered` from a
  finite acyclic component universe

発展段階で検討すること:

- `DAG <-> Nilpotent adjacency matrix`: `proved` for finite
  `ComponentUniverse` natural-number adjacency powers,
  [Issue #55](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/55)
- `DAG -> rho(A) = 0`: [Issue #26](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/26)
- `cycle -> rho(A) > 0`: [Issue #26](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/26)

#### Matrix bridge 設計

Issue [#26](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/26)
では、adjacency matrix を `Decomposable` の定義へ混ぜず、有限
`ComponentUniverse` 上の bridge layer として導入する方針に固定する。

最初の Lean 側対象は、`ComponentUniverse.components` の添字を持つ 0/1
隣接行列である。行列の entry は辺の存在を表し、thin
`ComponentCategory` が忘れる walk 数や path 数を復元するための別構造として扱う。
測定 universe は full universe として始め、実コードベース抽出器の完全性は主張しない。

Lean で優先して証明する bridge theorem は次である。

- `Acyclic G` と有限 universe 上の DAG 条件の対応。
- DAG 条件から、十分大きい冪で 0 になる adjacency matrix nilpotence。
- adjacency matrix nilpotence から、非空閉 walk が存在しないこと。
- したがって有限 universe 上で `WalkAcyclic` / `Acyclic` と nilpotence が一致すること。

`A^k` の entry を長さ `k` の walk 数と読む定理は、`Walk` を長さ付きの
count-preserving object として使う。これは `Reachable` や
`ComponentCategory` の Hom からは出さない。

`rho(A)` などの spectral condition は、実数・複素数上の行列解析と
Perron-Frobenius 型の補題を要するため、初期 Lean bridge では証明対象にしない。
Issue [#55](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/55)
で、Lean 側には `NatMatrix`, `adjacencyMatrix`, `adjacencyPowerEntry`,
`AdjacencyNilpotent` を導入した。`adjacencyPowerEntry_pos_iff_walk_length`
により、`A^k` の entry が正であることと長さ `k` の walk の存在が一致する。
また `adjacencyNilpotent_iff_walkAcyclic` と
`adjacencyNilpotent_iff_acyclic` により、有限 `ComponentUniverse` 上では
adjacency nilpotence / `WalkAcyclic` / `Acyclic` が一致する。

Issue [#85](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/85)
では、`nilpotencyIndex` を matrix bridge 由来の executable extension axis
として固定した。Lean 側の `nilpotencyIndexOfFinite U` は
`List.range (U.components.length + 2)` の範囲で最初に `A^k = 0` となる power を
`some k` として返す。見つからない場合は `none` とし、これは非 DAG または
未成立を表す欠損値であって risk 0 ではない。`rho(A)` などの spectral claim は
この axis には混ぜない。

`adjacencyPowerZeroOnComponentsBool_iff_zero` により、executable zero test は
`ComponentUniverse.covers` の下で graph-level 全 0 条件と一致する。
`adjacencyPowerEntry_zero_at_acyclic_cutoff` は finite acyclic graph で
`A^(components.length + 1)` が 0 になることを証明し、
`nilpotencyIndexOfFinite_isSome_of_acyclic` は finite acyclic graph では
`nilpotencyIndexOfFinite` が必ず `some` になることを示す。
`ArchitectureSignature.v1OfComponentUniverseWithNilpotencyIndex` は、この値を
`ArchitectureSignatureV1.nilpotencyIndex` に埋める entry point である。

当面は次の status に分ける。

- `DAG <-> Nilpotent adjacency matrix`: `proved` for finite `ComponentUniverse`
  natural-number adjacency powers
- `nilpotencyIndex`: executable metric / proved acyclic bridge for finite
  `ComponentUniverse`
- `DAG -> rho(A) = 0`: `future proof obligation`, matrix bridge 後の解析的拡張
- `cycle -> rho(A) > 0`: `future proof obligation`, matrix bridge 後の解析的拡張
- spectral radius を変更波及や障害伝播の増幅指標として使う主張:
  `empirical hypothesis`

`Acyclic + finite vertices -> StrictLayered` は、`ComponentUniverse.sourceDepthLayer` を層関数として使い、有限 universe 上の bounded source depth が依存辺に沿って厳密に下がることとして証明する。有限グラフ表現は `ComponentUniverse` と `FiniteArchGraph` の二層に分ける。`ComponentUniverse` は proof-carrying measurement universe として list, `Nodup`, coverage, edge-closedness を保持する。`FiniteArchGraph` は `ArchGraph` と `ComponentUniverse` を束ねる薄い graph-plus-universe structure として、有限グラフ theorem statement の入口にする。この整理は [Issue #3](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/3) で扱う。

### 3. SOLID 不完全性定理

本研究の操作的形式化における SOLID-style local contracts を満たしても、
分解可能性は従わないことを反例で示す。これは自然言語としての SOLID 原則全体を
一意に形式化した主張ではない。

主張:

```text
SOLID-style local contracts do not imply Decomposable(G)
```

最小反例:

```text
A -> B
B -> A
```

注意:

真空充足に見えないように、非自明な抽象・責務・置換関係を持つ反例も別途用意する。

LocalContract-style counterexample の候補:

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
  PaymentAdapter and PaymentPort agree on public payment behavior

Dependencies:
  OrderService   -> PaymentPort
  PaymentAdapter -> OrderService
  PaymentPort    -> PaymentAdapter
```

この例は、責務・抽象・観測関係を持ちながら、抽象から実装への逆流によって循環を作る。ただし DIP 違反に見える可能性があるため、完全な SOLID 充足反例とは呼ばない。非真空な局所契約データを持つ循環例として使う。

より強い反例の候補:

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

この例では、具象から抽象への依存方向を保っている。それでも抽象層 `OrderPort <-> PaymentPort` が循環しているため、Decomposable は従わない。

### 4. Layered 補完定理

SOLID-style local contracts に、Layered の大域構造制約を追加すると
Decomposable が従うことを示す。

主張:

```text
SOLID-style local contracts and StrictLayered(G) -> Decomposable(G)
```

意味:

- SOLID-style local contracts は局所健全性を与える。
- Layered は大域分解可能性を与える。
- 両者は異なる不変量を保証する。

### 5. DIP は射影整合性である

関連 Issue: [#10](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/10)

DIP を、具体グラフから抽象グラフへの射影が整合することとして定義する。

定義候補:

```text
InterfaceProjection
ProjectedDeps
ProjectionSound
ProjectionComplete
ProjectionExact
RepresentativeStable
QuotientWellDefined
RespectsProjection
DIPCompatible
StrongDIPCompatible
```

主張:

```text
DIPCompatible =
  projection soundness
  and strong representative-stability
```

同じ抽象に写る実装は、抽象世界で同じ依存構造を誘導しなければならない。

用語:

- `ProjectionSound`: 具体依存が抽象依存として表現されること。
- `ProjectionComplete`: 抽象依存が何らかの具体依存に由来すること。
- `ProjectionExact`: `ProjectionSound ∧ ProjectionComplete`。
- `RepresentativeStable`: 同じ抽象に写る具体要素が同じ抽象 outgoing dependency predicate を誘導すること。
- `projectionSoundnessViolation`: 有限な測定 universe 上で、具象依存が抽象依存へ
  sound に写らない concrete edge を数える executable projection bridge metric。

現行 Lean 実装の `QuotientWellDefined` は、`RepresentativeStable` と同じ strong representative-stability 条件である。

現行 Lean 実装の `DIPCompatible` は、本研究における strong operational formalization として扱う。すなわち、単に「具象が抽象へ依存する」という方向制約ではなく、projection soundness と strong representative-stability を要求する。

`StrongDIPCompatible` は、`DIPCompatible` の別名ではなく exact-projection refinement として扱う。つまり、
`ProjectionSound` に加えて `ProjectionComplete` も要求し、抽象グラフ上の辺が何らかの具体依存に由来することまで固定する。

Lean status:

- `defined only`: `ProjectionSound`, `ProjectionComplete`, `ProjectionExact`,
  `RepresentativeStable`, `DIPCompatible`, `StrongDIPCompatible`,
  `projectionSoundnessViolationEdges`, `projectionSoundnessViolation`
- `proved`: `projectionSound_of_projectionExact`,
  `projectionComplete_of_projectionExact`,
  `dipCompatible_of_strongDIPCompatible`,
  `mem_projectionSoundnessViolationEdges_iff`,
  `projectionSoundnessViolation_eq_zero_of_projectionSound`,
  `projectionSound_of_projectionSoundnessViolation_eq_zero`

今後の proof obligation:

- exact projection が必要な場面と soundness だけで十分な場面を、設計原則分類と
  Signature v1 の projection bridge 軸で分ける。
- SOLID 不完全性反例では、DIP 風の依存方向や `DIPCompatible` を満たしても、
  抽象層の循環から `¬ Decomposable` が起こり得ることを Layered とは別軸として扱う。

### 6. LSP は観測関手による同値性である

関連 Issue: [#10](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/10)

LSP を、内部構造ではなく観測可能な振る舞いの一致として定式化する。

定義候補:

```text
Observation
ObservationFactorsThrough
ObservationallyEquivalent
ObservationallyDivergent
LSPCompatible
observationalDivergence
lspViolationCount
```

主張:

同じ抽象型に属する実装 `x, y` について、観測可能な振る舞いが同値であれば置換可能である。

特に、観測が抽象を通じて因子化するなら LSP が従う。

```text
ObservationFactorsThrough π O -> LSPCompatible π O
```

Lean status:

- `defined only`: `Observation`, `ObservationallyEquivalent`,
  `LSPCompatibleAt`, `LSPCompatible`, `ObservationFactorsThrough`,
  `ObservationallyDivergent`, `observationalDivergence`,
  `lspViolationPairs`, `lspViolationCount`
- `proved`: `lspAt_of_lsp`, `lspCompatibleAt_refl`,
  `lspObservation_symm`, `lspCompatible_of_observationFactorsThrough`,
  `mem_lspViolationPairs_iff`, `observationalDivergence_eq_zero_of_equivalent`,
  `observationallyEquivalent_of_observationalDivergence_eq_zero`,
  `lspViolationCount_eq_zero_of_lspCompatible`,
  `lspViolationCount_eq_zero_of_observationFactorsThrough`,
  `lspCompatible_of_lspViolationCount_eq_zero`

Issue [#65](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/65)
では、behavioral extension の最小 Lean bridge を追加した。counting unit は
有限な実装 list 上の ordered pair `(x, y)` である。
`observationalDivergence O x y` は pair-level な 0/1 metric として、観測値が
一致すれば 0、異なれば 1 を返す。`lspViolationCount π O implementations` は、
`π.expose x = π.expose y` で同じ抽象に写るにもかかわらず `O.observe x` と
`O.observe y` が異なる measured pair を数える。これは観測可能性の局所契約層を
測る behavioral extension であり、repository-level の empirical calibration や
重みづけは後続 tooling 側に分離する。

Lean では、`LSPCompatible` なら finite violation count が 0 になること、
`ObservationFactorsThrough` なら `LSPCompatible` を経由して violation count が
0 になることを証明済みである。また、測定 universe が同じ抽象に写る pair を
閉じている場合には、violation 0 から `LSPCompatible` が得られる。

今後の proof obligation:

- `ObservationFactorsThrough` と projection bridge の関係を、実装置換の局所契約層として整理する。
- `observationalDivergence` や `lspViolationCount` の repository-level 集約、
  重みづけ、閾値設計は empirical / extractor tooling 側で扱う。

### 7. Architecture Signature は半順序を持つ

関連 Issue: [#3](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/3), [#5](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5), [#6](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/6), [#7](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/7), [#8](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/8), [#11](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/11), [#24](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/24), [#25](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/25)

多軸評価ベクトルに成分ごとのリスク順序を入れる。各成分は、値が大きいほど構造的リスクが高いように正規化する。

定義候補:

```text
ArchitectureSignature
RiskLE
v0OfFinite
```

意味:

```text
Sig(A) <=risk Sig(B)
```

は、`A` が `B` よりすべての評価軸で悪くないことを表す。

単一スコアは中心に置かない。まずは多軸シグネチャと成分ごとの比較可能性を中心にする。

初期フィールドの注意:

- `hasCycle` は 0/1 の risk indicator として扱う。
- `sccMaxSize` は将来的に `sccExcessSize = sccMaxSize - 1` として正規化することを検討する。
- `maxDepth` は PR4 では bounded max depth であり、循環グラフ上の真の大域 depth ではない。循環リスクは `hasCycle` で別軸として扱う。
- `fanoutRisk : Nat` は v0 では `totalFanout` として扱う。Nat-valued average fanout は丸め落ちるため Signature 本体から外し、`maxFanout` は局所集中を表す将来軸として分離する。
- `nilpotencyIndex?` は v1 extension axis として `Option Nat` で保持し、matrix bridge の `nilpotencyIndexOfFinite` で測定できる場合だけ `some` にする。`none` は非 DAG または未評価を表し、risk 0 とは解釈しない。

Lean status:

`proved`:

- Componentwise risk order is reflexive, transitive, and antisymmetric.
- `reachesWithin_sound`, `edge_reachable_of_hasCycleBool`,
  `hasClosedWalk_of_hasCycleBool`, `reachesWithin_complete_of_walk`, and
  `hasCycleBool_complete_of_bounded_return_walk`.
- `Reachable.exists_path` constructs a `Path` / `SimpleWalk` representative
  from propositional reachability. If a leading edge would repeat a vertex, the
  construction keeps the simple suffix starting at that vertex.
- `ComponentUniverse.reachable_exists_bounded_path` shows that `Reachable G c d`
  over a finite `ComponentUniverse` has a `Path G c d` whose length is bounded
  by `components.length`. This resolves [Issue #6](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/6).
- `reachesWithin_complete_of_reachable_under_universe` connects propositional
  `Reachable G c d` to executable bounded search over
  `ComponentUniverse.components` with `components.length` fuel. This resolves
  [Issue #7](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/7).
- `hasCycleBool_complete_of_hasClosedWalk` and
  `hasCycleBool_correct_under_finite_universe` connect the executable cycle
  indicator with `HasClosedWalk` under a finite `ComponentUniverse`. This
  resolves [Issue #8](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/8).
- `walk_length_le_components_length_of_acyclic`,
  `maxDepthOfFinite_is_global_walk_depth_bound_of_acyclic`,
  `maxDepthOfFinite_le_of_global_walk_depth_bound`, and
  `maxDepthOfFinite_correct_of_acyclic` show that, under an acyclic finite
  `ComponentUniverse`, executable `maxDepthOfFinite` is the least upper bound
  of all concrete dependency-walk lengths. This resolves
  [Issue #24](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/24).
- `MutuallyReachable` is proved reflexive, symmetric, and transitive.
  `sccSizeAt_eq_mutualReachableClassSize_under_universe` and
  `sccMaxSizeOfFinite_eq_max_mutualReachableClassSize_under_universe` show
  that, under a finite `ComponentUniverse`, executable bounded SCC-size
  metrics coincide with graph-level mutual-reachability class sizes. This
  resolves [Issue #25](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/25).

`defined only`:

- Executable v0 metrics over a supplied finite component list:
  `hasCycleBool`, bounded SCC size, bounded max depth, total-fanout
  `fanoutRisk`, boundary violation count, abstraction violation count, and
  `v0OfFinite`.
- `ComponentUniverse` packages the executable component list with `Nodup`,
  coverage, and edge-closedness assumptions. The current `ComponentUniverse` is
  a full universe, so edge-closedness follows from coverage. It remains an
  explicit field to leave room for future closed measurement sub-universes.
- `FiniteArchGraph` is a thin bundle of an `ArchGraph` and its
  `ComponentUniverse`. It does not replace raw list metrics or
  `ComponentUniverse`; it provides a stable graph-plus-universe entry point for
  future finite-graph theorem statements. `ComponentUniverse.full` records the
  full-universe case where `edgeClosed` follows from `covers`. This resolves
  [Issue #3](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/3)
  at the design/definition level.
- `SimpleWalk` packages a `Walk` with `walk.vertices.Nodup`, and `Path` is
  currently an alias for `SimpleWalk`. This resolves
  [Issue #5](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5)
  at the definition level: `Walk` remains the length/count-preserving object,
  while `Path` / `SimpleWalk` marks the no-repeated-vertices representative
  needed for future path-shortening.
- `ComponentUniverse` is still a proof-carrying measurement universe, not a
  parser or extractor for real codebases. `FiniteArchGraph` is only the bundled
  Lean representation of a graph with such a universe.
- `averageFanoutOfFinite : Nat` remains only as a legacy derived executable
  metric. Signature v0 uses `fanoutRiskOfFinite = totalFanout`, resolving the
  design decision tracked by
  [Issue #11](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/11).
- `measuredDependencyEdges` lists the dependency pairs measured by the supplied
  finite component list. `fanoutRiskOfFinite_eq_measuredDependencyEdges_length`
  and
  `fanoutRiskOfFinite_eq_measuredDependencyEdges_length_under_universe` prove
  that Signature v0 `fanoutRisk` is exactly the number of measured dependency
  edges. This resolves
  [Issue #64](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/64).
- `measuredDependencyEdgesFromSource` lists the measured dependency pairs for a
  fixed source component. `fanout_eq_measuredDependencyEdgesFromSource_length`
  proves that per-component `fanout` is exactly the number of such source-fixed
  measured edges.

#### Signature v1 軸設計

Issue [#32](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/32)
では、v1 を v0 の単純な置き換えではなく、v0 の安定軸を含む多軸診断として扱う。

v0 に残す軸:

- `hasCycle`
- `sccMaxSize`
- `maxDepth`
- `fanoutRisk = totalFanout`
- `boundaryViolationCount`
- `abstractionViolationCount`

Issue [#52](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/52)
では、extractor output と empirical dataset における未評価 metric の扱いを
`metricStatus` として固定した。Lean の `ArchitectureSignature` に渡すため
placeholder 0 を置く場合でも、`metricStatus.measured = false` の軸は欠損値であり、
違反なしや risk 0 とは解釈しない。この規約の Lean status は
`empirical hypothesis` / design decision であり、Lean theorem ではない。

Issue [#53](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/53)
では、`signatureBefore` / `signatureAfter` の差分を
`SignatureIntVector` 上の `deltaSignatureSigned = after - before` として固定した。
正の値は risk 増加、負の値は risk 減少を表し、改善分を `Nat` subtraction で
0 に丸めない。`riskIncrease` / `riskDecrease` は signed delta から作る派生値であり、
PR-level delta は repository 全体の before / after signature 差分として扱う。
component-level contribution は説明用の補助データであり、大域軸を含むため
単純和が PR-level delta と一致することは要求しない。この規約の Lean status は
`empirical hypothesis` / design decision であり、Lean theorem ではない。

Issue [#54](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/54)
では、`RelationComplexityObservation` を workflow-level JSON record として扱い、
repository-level の `relationComplexity` は workflow observation の集約から作る
派生値として固定した。counting unit は evidence item, workflow observation,
component aggregate, repository aggregate に分ける。1 つの evidence item が複数の
構成要素に該当する場合は複数 tag を保持し、各 tag の count に寄与させる。
framework-generated behavior は初期 metric から除外し、application-owned または
application-configured behavior だけを counting candidate とする。per workflow,
per component, per KLOC などの正規化は raw count を置き換えない将来の派生指標として扱う。
この規約の Lean status は `empirical hypothesis` / tooling design であり、
Lean theorem ではない。

v1 core に追加・正規化する候補:

- `sccExcessSize = sccMaxSize - 1`: 非循環 singleton SCC を 0 risk として扱うための循環リスク軸。
- `weightedSccRisk`: SCC の大きさや重要度を重みづけする将来の executable metric。
- `maxFanout`: 局所的な依存集中を表す executable metric。
- `reachableConeSize`: 変更波及の到達範囲を表す executable metric。
- `projectionSoundnessViolation`: 抽象射影に反する具体依存を数える projection bridge 軸。

Issue [#63](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/63)
では、v1 core の最小 Lean 定義を v0 signature の派生 executable metric として
固定した。`ArchitectureSignature` v0 record は変更せず、有限な測定 universe
`components : List C` 上で次の counting rule を使う。

- `sccExcessSizeOfFinite G components = sccMaxSizeOfFinite G components - 1`。
  Nat subtraction により、空 universe や singleton SCC は 0 risk に丸められる。
- `maxFanoutOfFinite G components` は、各 component の `fanout G components c`
  の最大値である。これは v0 `fanoutRiskOfFinite = totalFanout` を置き換えず、
  局所的な依存集中だけを測る。
- `reachableConeSizeAt G components c` は、bounded reachability で `c` から到達
  できる component のうち `c` 自身を除いた数である。
  `reachableConeSizeOfFinite G components` はその最大値である。辺の向きは既存の
  `maxDepthOfFinite` と同じく `edge c d` means `c` depends on `d` に従う。

Issue [#87](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/87)
では、Lean 側の v1 output schema を `ArchitectureSignatureV1Core` と
`ArchitectureSignatureV1` に分けて固定した。`ArchitectureSignatureV1Core` は
v0 signature を内側に持ち、`sccExcessSize`, `maxFanout`,
`reachableConeSize` を現在 Lean で測定できる v1 core 派生軸として保持する。
`ArchitectureSignatureV1` は core に加えて、`weightedSccRisk`,
`projectionSoundnessViolation`, `lspViolationCount`, `nilpotencyIndex`,
`runtimePropagation`, `relationComplexity`, `empiricalChangeCost` を
`Option Nat` として保持する。`none` は未評価を意味し、risk 0 とは解釈しない。
`v1CoreOfFinite` と `v1OfFinite` は finite component list からこの schema を
構成する executable entry point である。

Issue [#84](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/84)
では、`weightedSccRisk` の Lean 側 counting rule を固定した。入力は
`weight : C -> Nat` であり、`weightedSccRiskOfFinite G components weight` は
測定 universe 上の各 component について
`weight c * (sccSizeAt G components c - 1)` を合計する。Nat subtraction により
singleton SCC は 0 risk になり、component importance など重みの抽出根拠や
calibration は empirical / extractor tooling 側に残す。Lean では
`v1OfFiniteWithWeightedSccRisk` により、重みが明示的に渡された場合だけ
`ArchitectureSignatureV1.weightedSccRisk` を `some` で埋める。

Issue [#62](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/62)
では、projection bridge の最小 Lean 定義を追加した。`projectionSoundnessViolation`
は `components : List C` に現れる concrete edge `(c, d)` のうち、
`GA.edge (π.expose c) (π.expose d)` が成り立たないものを数える。これは
soundness 側だけを測るため、`ProjectionComplete` まで要求する exact projection
とは分けて扱う。Lean では、`ProjectionSound` なら violation が 0 になること、
また測定 universe が concrete edge を閉じている場合には violation 0 から
`ProjectionSound` が得られることを証明済みである。

Issue [#65](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/65)
では、behavioral extension の最小 Lean bridge を追加した。`observationalDivergence`
は measured pair ごとの観測差分を 0/1 で数え、`lspViolationCount` は有限な実装
list 上で同じ抽象に写るが観測が異なる ordered pair を数える。
`ObservationFactorsThrough` や `LSPCompatible` が成り立つ場合に violation count が
0 になる theorem は証明済みである。repository-level の集約、重み、実コード抽出の
完全性は Lean theorem ではなく empirical / extractor tooling 側の課題として残す。

Issue [#71](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/71)
では、`sccExcessSizeOfFinite` と graph-level mutual-reachability class size
の接続を追加した。有限 universe 下で、`sccExcessSizeOfFinite` は
相互到達 class size 最大値から 1 を引いた値と一致する。さらに
`sccMaxSizeOfFinite <= 1` なら excess は 0 であることを theorem として
特徴づけ、空 universe や singleton SCC は Nat subtraction により 0 risk に
丸められることを明確にした。

Issue [#72](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/72)
では、`reachableConeSizeAt` / `reachableConeSizeOfFinite` と graph-level strict
reachable cone の接続を追加した。有限 universe 下で、bounded search による
`reachableConeSizeAt` は source 自身を除く `Reachable` cone のサイズと一致し、
`reachableConeSizeOfFinite` は component ごとの strict reachable cone size の
最大値と一致する。

Issue [#74](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/74)
では、`maxFanoutOfFinite` と source ごとの measured dependency edges の接続を
追加した。`measuredDependencyEdgesFromSource` により source 固定の測定依存辺を
定義し、`maxFanoutOfFinite` は component ごとの source-fixed measured edge count
の最大値であることを証明済みである。これにより、v0 `fanoutRiskOfFinite` は
全 measured dependency edges 数、v1 core `maxFanoutOfFinite` は source ごとの
局所集中の最大値として区別される。

v1 core 派生 metric のうち `sccExcessSizeOfFinite`,
`reachableConeSizeOfFinite`, `maxFanoutOfFinite` の graph-level bridge は
証明済みである。

Lean status の区分:

| 軸 | 扱い | Lean status |
| --- | --- | --- |
| `sccExcessSize` | 有限 universe 上の計算として定義済み。graph-level mutual-reachability class size 最大値との bridge を証明済み | `defined only` / `proved` |
| `reachableConeSize` | 有限 universe 上の計算として定義済み。graph-level strict reachable cone size 最大値との bridge を証明済み | `defined only` / `proved` |
| `maxFanout` | 有限 universe 上の計算として定義済み。source ごとの measured dependency edges との bridge を証明済み | `defined only` / `proved` |
| `ArchitectureSignatureV1Core`, `ArchitectureSignatureV1` | v0 を内側に含む v1 output schema。未評価 extension axis は `Option Nat` で保持する | `defined only` |
| `weightedSccRisk` | `weight : C -> Nat` を入力し、各 component の重み付き SCC excess を合計する executable metric。重みの由来は empirical / extractor tooling 側に残す | `defined only` / `proved` |
| `projectionSoundnessViolation` | 具象依存が抽象依存へ sound に写らない measured edge を数える | `defined only` / `proved` |
| `observationalDivergence`, `lspViolationCount` | 観測差分と measured LSP violation pair を数える behavioral extension | `defined only` / `proved` |
| `nilpotencyIndex` | finite `ComponentUniverse` 上で最初の zero adjacency power を探す executable metric。acyclic graph では `some` になる bridge を証明済み | `defined only` / `proved` |
| `rho(A)` | 行列解析上の伝播増幅指標として扱う | `future proof obligation` / `empirical hypothesis` |
| `runtimePropagation` | 実行時依存抽出に依存する | `empirical hypothesis` |
| `relationComplexity` | 状態遷移代数層の設計に依存する | `empirical hypothesis` |
| `empiricalChangeCost` | 実データで検証する目的変数 | `empirical hypothesis` |

後続 Issue への分割:

- adjacency matrix と `rho(A)` の解析的拡張は
  [#26](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/26)
  で扱う。
- 静的依存と実行時依存の分離は
  [#33](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/33)
  で扱う。
- 実コードベースからの Sig0 / v1 core 抽出 tooling は
  [#34](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/34)
  で扱う。最小 Sig0 extractor の v0 設計は
  [sig0_extractor_design.md](design/sig0_extractor_design.md)
  に分離する。
- 実証プロトコルと empirical cost 軸は
  [#35](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/35)
  で扱う。初期 protocol は
  [empirical_protocol.md](design/empirical_protocol.md)
  に分離する。
- `relationComplexity` は
  [#36](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/36)
  で扱う。初期設計は
  [relation_complexity_design.md](design/relation_complexity_design.md)
  に分離する。

Bridge theorem naming policy:

- Use `*_sound` for executable Boolean evidence implying graph-level
  propositions.
  Example: `reachesWithin_sound`.
- Use `*_of_hasCycleBool` for facts extracted from a true executable cycle
  indicator.
  Examples: `edge_reachable_of_hasCycleBool`,
  `hasClosedWalk_of_hasCycleBool`.
- Use `*_complete_of_walk` for bounded completeness from an explicit `Walk`
  and an explicit fuel bound.
  Example: `reachesWithin_complete_of_walk`.
- Use `*_complete_of_reachable_under_universe` for completeness from
  propositional `Reachable` under a `ComponentUniverse`, where the fuel is fixed
  to `components.length`.
  Example: `reachesWithin_complete_of_reachable_under_universe`.
- Use `*_complete_of_bounded_return_walk` for the older bounded cycle bridge
  that starts from one generating edge and an explicit bounded return walk.
  Example: `hasCycleBool_complete_of_bounded_return_walk`.
- Use `*_complete_of_hasClosedWalk` when a graph-level closed-walk proposition
  implies an executable Boolean result under a finite universe.
  Example: `hasCycleBool_complete_of_hasClosedWalk`.
- Use `*_correct_under_finite_universe` for final iff-style correctness
  theorems under `ComponentUniverse`.
  Example: `hasCycleBool_correct_under_finite_universe`.

This resolves Issue #4 at the naming-policy level. The current Lean theorem
names already follow this convention, so no Lean rename is needed.

## 実証研究で検証する仮説

Lean status: `empirical hypothesis`. この節の仮説は実コードベースや運用データで検証する対象であり、Lean proof のブロッカーではない。

Issue [#35](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/35)
では、最初の pilot study 用に仮説を 4 個に絞り、必要データ、測定方法、
除外条件、extractor tooling と data analysis の前提分離を
[empirical_protocol.md](design/empirical_protocol.md) に固定する。

### 1. 変更波及との相関

仮説:

```text
Sig(A) の悪化は、変更ファイル数や変更モジュール数の増加と相関する。
```

測定候補:

- pull request ごとの変更ファイル数
- 変更されたコンポーネント数
- 変更前後の依存距離

### 2. SCC サイズと障害修正時間

仮説:

```text
sccMaxSize が大きいほど、障害修正時間が長くなる。
```

測定候補:

- issue の open から close までの時間
- hotfix の変更範囲
- rollback の有無

### 3. fanout とレビューコスト

仮説:

```text
fanoutRisk または最大 fanout が大きいほど、レビューコストが増える。
```

測定候補:

- review comment 数
- review round 数
- approve までの時間

### 4. 境界違反と将来の変更波及

仮説:

```text
boundaryViolationCount が大きいほど、将来の変更波及が大きくなる。
```

測定候補:

- 境界違反を含むモジュールの将来変更頻度
- 関連 issue 数
- 依存先/依存元への同時変更率

### 5. 関係式複雑度と運用リスク

仮説:

```text
relationComplexity が高いほど、補償失敗・整合性違反・障害復旧コストが増える。
```

初期定義案:

```text
relationComplexity =
  constraints
  + compensations
  + projections
  + failureTransitions
  + idempotencyRequirements
```

Issue [#36](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/36)
では、この軸をまず Lean core ではなく empirical metric として扱う方針に固定する。
初期 metric は `constraints`, `compensations`, `projections`,
`failureTransitions`, `idempotencyRequirements` の構成要素を保持し、
派生値として合計を計算する。詳細は
[relation_complexity_design.md](design/relation_complexity_design.md) を参照する。

## 未解決課題

### SOLID の形式化は一意ではない

SOLID は自然言語の設計原則なので、唯一の正しい形式化を主張しない。

本研究では、依存グラフ・射影・観測関手に基づく操作的形式化を与える。

### 静的依存と実行時依存を分ける

Issue [#33](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/33)
では、静的依存と実行時依存を同じ `ArchGraph` に潰さず、別 role として扱う方針に固定する。

Lean status: `defined only` / design decision.

Lean core では、まず最低2種類のグラフを `ArchGraph` の role alias として持つ。

```text
StaticDependencyGraph C := ArchGraph C
RuntimeDependencyGraph C := ArchGraph C
ArchitectureDependencyGraphs C =
  { static  : StaticDependencyGraph C
    runtime : RuntimeDependencyGraph C }
```

`ArchGraph` を再利用する理由は、静的・実行時のどちらも 0/1 の依存辺だけを見れば `Walk`, `Reachable`, `Path`, finite metrics を共有できるからである。ただし、共有するのは graph theory API だけであり、Signature 上の意味は混同しない。

静的依存の例:

- import
- type reference
- inheritance
- package dependency

静的依存グラフは、Layered / Clean Architecture, DIP, boundary violation, projection soundness など、構造的な制約と設計境界の評価に使う。`Decomposable` や `StrictLayered` の対象は、明示しない限りこの静的依存グラフである。

実行時依存の例:

- RPC
- message queue
- shared database
- distributed transaction
- external SaaS
- timeout propagation

実行時依存グラフは、Circuit Breaker, timeout propagation, runtime fanout, failure propagation radius など、運用時の結合と障害伝播の評価に使う。Lean core の `RuntimeDependencyGraph` は当面 0/1 edge の存在だけを表す。edge label, weight, failure mode, timeout budget, retry policy, circuit breaker coverage などは extractor / empirical tooling 側の metadata として保持し、対応する projection が固まった後で Lean 定義へ橋渡しする。

責務境界:

- Lean 側: `StaticDependencyGraph`, `RuntimeDependencyGraph`, `ArchitectureDependencyGraphs` を定義し、0/1 graph として言える構造的命題だけを theorem 化する。
- extractor / empirical 側: import, type reference, RPC, queue, shared database, timeout propagation などの抽出規則と edge metadata を管理する。
- Signature 側: v0 の静的構造軸を維持し、`runtimePropagation` は v1 以降の empirical extension として分離する。

後続 Issue 候補:

- runtime edge metadata と 0/1 `RuntimeDependencyGraph` への projection を設計する。
- Circuit Breaker coverage を runtime propagation radius の低減として測る executable metric を設計する。
- `runtimeFanout` / `runtimePropagationRadius` と障害修正コストの実証プロトコルを設計する。

### 解析的指標は発展課題として扱う

スペクトル半径、最近極、形式的ゼータ関数、discounted propagation resolvent は重要だが、初期実装では中心に置かない。

まずは `hasCycle`, `sccMaxSize`, `maxDepth`, `fanoutRisk`, `boundaryViolationCount`, `abstractionViolationCount` のような、抽出・説明・検証が容易な指標を優先する。

なお、これらの定量指標には thin category だけでは不足する情報がある。経路数・経路長・walk 数を扱う場合は、`Reachable` ではなく `Walk`, `Path`, adjacency matrix, または `FreeCategoryOfGraph` 側で定義する。
