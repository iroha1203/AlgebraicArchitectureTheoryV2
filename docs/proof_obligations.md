# 証明義務と実証仮説

## 方針

この文書は、Lean で証明する命題と、実データで検証する仮説を分離する。

Lean では、定義が明確で全称命題として扱える構造的事実を証明する。現実コードベースの品質や変更コストとの相関は、Lean の定理ではなく実証研究の仮説として扱う。

未証明の主張を `axiom` や `sorry` で隠蔽しない。証明できていない命題は、この文書に証明義務または実証仮説として残す。

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

- `StrictLayered -> Acyclic`
- `StrictLayered -> FinitePropagation`
- `Acyclic + finite vertices -> StrictLayered`
- `Acyclic <-> WalkAcyclic`
- `DAG <-> Nilpotent adjacency matrix`

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

証明義務:

- `Acyclic -> WalkAcyclic`
- `WalkAcyclic -> Acyclic`

### 2. 分解可能性の基礎定理

有限依存グラフについて、層化可能性、非循環性、有限伝播を接続する。

初期段階で証明すること:

- `Decomposable G := StrictLayered G`
- `StrictLayered -> Acyclic`
- `StrictLayered -> FinitePropagation`
- Layered な4層例が `Decomposable` であること
- 2点循環グラフが `Decomposable` でないこと

発展段階で検討すること:

- `Acyclic + finite vertices -> StrictLayered`
- `DAG <-> Nilpotent adjacency matrix`
- `DAG -> rho(A) = 0`
- `cycle -> rho(A) > 0`

`Acyclic + finite vertices -> StrictLayered` に進むには、有限で計算可能なグラフ表現が必要になる。次フェーズでは `[Fintype C]`, `[DecidableEq C]`, `DecidableRel G.edge`、または専用の `FiniteArchGraph` を導入する。

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
- `averageFanout : Nat` は初期の粗い足場であり、Nat 除算で丸められる。PR4 以降で `fanoutRisk = totalFanout` または `maxFanout` への置き換えを検討する。
- `nilpotencyIndex?` は初期 Lean 実装には入れず、adjacency matrix 導入後の発展指標として扱う。

Lean status:

- Proved: componentwise risk order is reflexive, transitive, and antisymmetric.
- Defined: executable v0 metrics over a supplied finite component list:
  `hasCycleBool`, bounded SCC size, bounded max depth, Nat-valued average fanout,
  boundary violation count, abstraction violation count, and `v0OfFinite`.
- Defined: `ComponentUniverse` packages the executable component list with
  `Nodup`, coverage, and edge-closedness assumptions.
- Note: the current `ComponentUniverse` is a full universe, so edge-closedness
  follows from coverage. It remains an explicit field to leave room for future
  closed measurement sub-universes.
- Proved: `reachesWithin_sound`, `edge_reachable_of_hasCycleBool`,
  `hasClosedWalk_of_hasCycleBool`, `reachesWithin_complete_of_walk`, and
  `hasCycleBool_complete_of_bounded_return_walk`.
- Defined: `SimpleWalk` packages a `Walk` with `walk.vertices.Nodup`, and
  `Path` is currently an alias for `SimpleWalk`. This resolves Issue #5 at the
  definition level: `Walk` remains the length/count-preserving object, while
  `Path` / `SimpleWalk` marks the no-repeated-vertices representative needed
  for future path-shortening.
- Defined only: `ComponentUniverse` is still a proof-carrying measurement
  universe, not a parser or extractor for real codebases.
- Future proof obligation: connect SCC-size counts to equivalence classes of
  mutual `Reachable`, and decide whether `FiniteArchGraph` should become a
  bundled graph-plus-universe structure.
- Future proof obligation: prove
  `reachesWithin_complete_of_reachable_under_universe`,
  `hasCycleBool ↔ HasClosedWalk` under a finite universe, and max-depth
  correctness on acyclic finite graphs.
- Future proof obligation: prove a path-shortening theorem from arbitrary
  `Walk` / `Reachable` evidence to a bounded `Path` under a finite
  `ComponentUniverse`, with the length bound tied to `components.length`.

## 実証研究で検証する仮説

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
averageFanout または最大 fanout が大きいほど、レビューコストが増える。
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

まずは `hasCycle`, `sccMaxSize`, `maxDepth`, `averageFanout`, `boundaryViolationCount`, `abstractionViolationCount` のような、抽出・説明・検証が容易な指標を優先する。

なお、これらの定量指標には thin category だけでは不足する情報がある。経路数・経路長・walk 数を扱う場合は、`Reachable` ではなく `Walk`, `Path`, adjacency matrix, または `FreeCategoryOfGraph` 側で定義する。
