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

## GitHub Issues 索引

| Issue | State | Milestone | Lean status | 関連セクション | 内容 |
| --- | --- | --- | --- | --- | --- |
| [#3](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/3) | open | 1. Finite Universe Bridge | `defined only` / design decided | [7. Architecture Signature は半順序を持つ](#7-architecture-signature-は半順序を持つ) | `ComponentUniverse` と `FiniteArchGraph` の役割分担を整理する。 |
| [#4](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/4) | closed | 1. Finite Universe Bridge | `proved` / resolved naming | [Bridge theorem naming policy](#bridge-theorem-naming-policy) | bridge theorem の命名方針を整理する。 |
| [#5](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5) | closed | 2. Path and Reachability Correctness | `defined only` / resolved definition | [7. Architecture Signature は半順序を持つ](#7-architecture-signature-は半順序を持つ) | `Path` / `SimpleWalk` を導入する。 |
| [#6](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/6) | closed | 2. Path and Reachability Correctness | `proved` | [7. Architecture Signature は半順序を持つ](#7-architecture-signature-は半順序を持つ) | 有限 universe 上で reachable なら bounded path があることを証明する。 |
| [#7](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/7) | closed | 2. Path and Reachability Correctness | `proved` | [7. Architecture Signature は半順序を持つ](#7-architecture-signature-は半順序を持つ) | `reachesWithin_complete_of_reachable_under_universe` を証明する。 |
| [#8](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/8) | closed | 3. Cycle, SCC and Depth Correctness | `proved` | [7. Architecture Signature は半順序を持つ](#7-architecture-signature-は半順序を持つ) | `hasCycleBool` と `HasClosedWalk` の有限 universe 上の同値を証明する。 |
| [#9](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/9) | open | 1. Finite Universe Bridge | docs index | [GitHub Issues 索引](#github-issues-索引) | この文書を GitHub Issues への索引として更新する。 |
| [#10](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/10) | open | 6. Projection / Observation Invariants | `defined only` / design | [5. DIP は射影整合性である](#5-dip-は射影整合性である), [6. LSP は観測関手による同値性である](#6-lsp-は観測関手による同値性である) | `DIPCompatible` と `StrongDIPCompatible` の役割分担を整理する。 |
| [#11](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/11) | closed | 4. Signature v0 Stabilization | `defined only` / design decided | [7. Architecture Signature は半順序を持つ](#7-architecture-signature-は半順序を持つ), [fanout とレビューコスト](#3-fanout-とレビューコスト) | `fanoutRisk = totalFanout` として v0 の fanout 軸を安定化する。 |
| [#23](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/23) | closed | 5. Layering Equivalence | `proved` | [2. 分解可能性の基礎定理](#2-分解可能性の基礎定理) | 有限非循環グラフから `StrictLayered` を構成する。 |
| [#24](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/24) | closed | 3. Cycle, SCC and Depth Correctness | `proved` | [7. Architecture Signature は半順序を持つ](#7-architecture-signature-は半順序を持つ) | acyclic finite graph 上の `maxDepth` correctness を証明する。 |
| [#25](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/25) | closed | 3. Cycle, SCC and Depth Correctness | `proved` | [7. Architecture Signature は半順序を持つ](#7-architecture-signature-は半順序を持つ) | SCC サイズ指標と相互到達可能性の同値類を接続する。 |
| [#26](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/26) | open | 7. Path and Matrix Foundations | `future proof obligation` / design | [2. 分解可能性の基礎定理](#2-分解可能性の基礎定理), [解析的指標は発展課題として扱う](#解析的指標は発展課題として扱う) | adjacency matrix と DAG / nilpotence / spectral bridge を設計する。 |
| [#32](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/32) | open | 4. Signature v0 Stabilization | `defined only` / design decided | [7. Architecture Signature は半順序を持つ](#7-architecture-signature-は半順序を持つ), [Signature v1 軸設計](#signature-v1-軸設計) | ArchitectureSignature v1 の軸構成を整理する。 |

## Lean で証明する命題

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
- `DAG <-> Nilpotent adjacency matrix`: `future proof obligation`, [Issue #26](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/26)

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

- `DAG <-> Nilpotent adjacency matrix`: [Issue #26](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/26)
- `DAG -> rho(A) = 0`: [Issue #26](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/26)
- `cycle -> rho(A) > 0`: [Issue #26](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/26)

`Acyclic + finite vertices -> StrictLayered` は、`ComponentUniverse.sourceDepthLayer` を層関数として使い、有限 universe 上の bounded source depth が依存辺に沿って厳密に下がることとして証明する。有限グラフ表現は `ComponentUniverse` と `FiniteArchGraph` の二層に分ける。`ComponentUniverse` は proof-carrying measurement universe として list, `Nodup`, coverage, edge-closedness を保持する。`FiniteArchGraph` は `ArchGraph` と `ComponentUniverse` を束ねる薄い graph-plus-universe structure として、有限グラフ theorem statement の入口にする。この整理は [Issue #3](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/3) で扱う。

### 3. SOLID 不完全性定理

SOLID 風の局所制約を満たしても、分解可能性は従わないことを反例で示す。

主張:

```text
SOLID(G) does not imply Decomposable(G)
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

SOLID の局所健全性に、Layered の大域構造制約を追加すると Decomposable が従うことを示す。

主張:

```text
SOLID(G) and StrictLayered(G) -> Decomposable(G)
```

意味:

- SOLID は局所健全性を与える。
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

現行 Lean 実装の `QuotientWellDefined` は、`RepresentativeStable` と同じ strong representative-stability 条件である。

現行 Lean 実装の `DIPCompatible` は、本研究における strong operational formalization として扱う。すなわち、単に「具象が抽象へ依存する」という方向制約ではなく、projection soundness と strong representative-stability を要求する。

### 6. LSP は観測関手による同値性である

関連 Issue: [#10](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/10)

LSP を、内部構造ではなく観測可能な振る舞いの一致として定式化する。

定義候補:

```text
Observation
ObservationFactorsThrough
ObservationallyEquivalent
LSPCompatible
```

主張:

同じ抽象型に属する実装 `x, y` について、観測可能な振る舞いが同値であれば置換可能である。

特に、観測が抽象を通じて因子化するなら LSP が従う。

```text
ObservationFactorsThrough π O -> LSPCompatible π O
```

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
- `nilpotencyIndex?` は初期 Lean 実装には入れず、adjacency matrix 導入後の発展指標として扱う。

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

`future proof obligation`:

- Prove graph-level correctness facts for `fanoutRiskOfFinite` under a finite
  `ComponentUniverse`, such as equivalence with the number of measured
  dependency edges.

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

v1 core に追加・正規化する候補:

- `sccExcessSize = sccMaxSize - 1`: 非循環 singleton SCC を 0 risk として扱うための循環リスク軸。
- `weightedSccRisk`: SCC の大きさや重要度を重みづけする将来の executable metric。
- `maxFanout`: 局所的な依存集中を表す executable metric。
- `reachableConeSize`: 変更波及の到達範囲を表す executable metric。
- `projectionSoundnessViolation`: 抽象射影に反する具体依存を数える projection bridge 軸。

Lean status の区分:

| 軸 | 扱い | Lean status |
| --- | --- | --- |
| `sccExcessSize`, `maxFanout`, `reachableConeSize` | 有限 universe 上の計算として定義し、graph-level facts は theorem として証明する | `defined only` -> `future proof obligation` |
| `weightedSccRisk` | 重み関数つき executable metric として設計する | `defined only` |
| `nilpotencyIndex` | adjacency matrix 導入後に DAG / 層化 / 冪零性と接続する | `future proof obligation` |
| `rho(A)` | 行列解析上の伝播増幅指標として扱う | `future proof obligation` / `empirical hypothesis` |
| `runtimePropagation` | 実行時依存抽出に依存する | `empirical hypothesis` |
| `relationComplexity` | 状態遷移代数層の設計に依存する | `empirical hypothesis` |
| `empiricalChangeCost` | 実データで検証する目的変数 | `empirical hypothesis` |

後続 Issue への分割:

- adjacency matrix, `nilpotencyIndex`, `rho(A)` は
  [#26](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/26)
  で扱う。
- 静的依存と実行時依存の分離は
  [#33](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/33)
  で扱う。
- 実コードベースからの Sig0 / v1 core 抽出 tooling は
  [#34](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/34)
  で扱う。
- 実証プロトコルと empirical cost 軸は
  [#35](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/35)
  で扱う。
- `relationComplexity` は
  [#36](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/36)
  で扱う。

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

この定義はまだ固定しない。実証可能性と Lean 側の扱いやすさを見て調整する。

## 未解決課題

### SOLID の形式化は一意ではない

SOLID は自然言語の設計原則なので、唯一の正しい形式化を主張しない。

本研究では、依存グラフ・射影・観測関手に基づく操作的形式化を与える。

### 静的依存と実行時依存を分ける

最低2種類のグラフが必要である。

```text
G_static
G_runtime
```

静的依存の例:

- import
- type reference
- inheritance
- package dependency

実行時依存の例:

- RPC
- message queue
- shared database
- distributed transaction
- external SaaS
- timeout propagation

### 解析的指標は発展課題として扱う

スペクトル半径、最近極、形式的ゼータ関数、discounted propagation resolvent は重要だが、初期実装では中心に置かない。

まずは `hasCycle`, `sccMaxSize`, `maxDepth`, `fanoutRisk`, `boundaryViolationCount`, `abstractionViolationCount` のような、抽出・説明・検証が容易な指標を優先する。

なお、これらの定量指標には thin category だけでは不足する情報がある。経路数・経路長・walk 数を扱う場合は、`Reachable` ではなく `Walk`, `Path`, adjacency matrix, または `FreeCategoryOfGraph` 側で定義する。
