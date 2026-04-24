# 代数的アーキテクチャ論 v2 概要

## 中心主張

代数的アーキテクチャ論 v2 は、ソフトウェア設計原則を経験則ではなく、アーキテクチャ不変量を保存・改善する操作として分類する研究である。

中心主張は次である。

> 設計原則は、アーキテクチャ不変量を保存・改善する操作である。  
> アーキテクチャ品質は、それらの不変量の破れを多軸シグネチャとして定量評価できる。

この主張により、設計議論を「よい/悪い」という経験的評価から、「どの不変量を保存しているか」「どの不変量が破れているか」「その破れがどの程度か」という検証可能な形へ移す。

## v2 の目的

v2 の目的は、既存 Part1 から Part7 の成果を、分類理論・証明理論・評価理論の三層へ整理し直すことである。

1. 分類理論: 設計原則を、保証するアーキテクチャ不変量ごとに分類する。
2. 証明理論: 分解可能性、層化可能性、非循環性、冪零性、有限影響伝播の対応を明確にする。
3. 評価理論: 不変量の破れを Architecture Signature として多軸評価する。

この再構成では、スペクトル半径やゼータ関数を最初から中心に置かない。まずはグラフ理論的・操作的に意味が明確な指標を定義し、その発展として解析的指標を接続する。

## 三層構造

### 第I層: 構文的構造

コードベースを数学的対象へ写す層である。

| ソフトウェア上の対象 | 数学的表現 |
| --- | --- |
| モジュール / コンポーネント | 頂点 |
| 依存関係 | 有向辺 |
| 依存経路 | path / walk |
| 到達可能性 | thin category の射 |
| 抽象化 | 商 / 射影 |
| 設計変換 | 関手 |
| イベント列 | 自由モノイド |
| 補償・制約 | 関係式 |

ここでは `ArchGraph`, `Reachable`, `ComponentCategory`, `Projection`, `Observation` などを基礎概念として扱う。

依存辺の向きは次で固定する。

```text
edge c -> d means component c depends on component d.
```

層化の向きもこの convention に合わせる。

```text
StrictLayered G :=
  exists layer : C -> Nat,
  for every edge c -> d, layer d < layer c
```

つまり、依存する側 `c` は上位層、依存される側 `d` は下位層に置く。

`ComponentCategory` は `Reachable : C -> C -> Prop` を Hom にする薄い圏である。この圏は「到達可能かどうか」を表現できるが、複数経路の本数、経路長、walk の本数を失う。したがって、定量評価では thin category とは別に、`Walk`, `Path`, adjacency matrix, 必要に応じて `FreeCategoryOfGraph` を扱う。

### 第II層: 設計原則の分類

設計原則を「どの不変量を保証するか」で分類する。

SOLID は万能原理として扱わない。SOLID は局所的な契約・抽象・置換の健全性を与えるが、大域的な分解可能性を単独では保証しない。

役割分担は次のように整理する。

- SOLID: 局所契約層
- Layered / Clean Architecture: 大域構造層
- Event Sourcing / Saga / CRUD: 状態遷移代数層
- Circuit Breaker / Replicated Log: 実行時依存・分散収束層

### 第III層: 定量評価

アーキテクチャ品質は単一スコアではなく、多軸シグネチャとして評価する。

Architecture Signature の順序は、リスク順序として定義する。各成分は値が大きいほど構造的リスクが高くなるように正規化する。

初期シグネチャ `Sig0(A)` は次のような軸を持つ。

```text
Sig0(A) =
  < hasCycle,
    sccMaxSize,
    maxDepth,
    averageFanout,
    boundaryViolationCount,
    abstractionViolationCount >
```

`hasCycle` は 0/1 のリスク指標として扱う。`nilpotencyIndex?` は初期 Lean 版の `ArchitectureSignature` にはまだ入れず、adjacency matrix 導入後の発展指標として扱う。

`sccMaxSize` は初期指標として残すが、将来的には非循環成分を 0 risk にするため `sccExcessSize = sccMaxSize - 1` への正規化を検討する。`averageFanout : Nat` は初期の粗い足場であり、PR4 以降で `fanoutRisk` または `maxFanout` への改名を検討する。

Lean PR4 では、有限な component list を測定 universe とする executable v0 metrics を定義する。これは実コードベース抽出器の完全性を主張するものではない。抽出された component list の重複排除・完全性、および SCC 計算との正当性接続は、将来の有限グラフ表現で扱う。

発展シグネチャ `Sig1(A)` では、解析的・実証的な軸を追加する。

```text
Sig1(A) =
  < rho(A),
    poleRadius,
    weightedSccRisk,
    relationComplexity,
    runtimePropagation,
    empiricalChangeCost >
```

単一スコア化は補助的な集約に留める。研究の中心は、多軸シグネチャ間のリスク順序と、各軸がどの不変量の破れを表すかの説明に置く。

## 圏論を使う理由

分解可能性や循環検出だけなら、グラフ理論で十分である。v2 ではこの点を明確にする。

圏論を使う理由は、次の概念を同じ言語で扱えるからである。

- 依存経路
- 抽象化
- 商
- 関手
- 観測
- 置換
- 構造保存

したがって立場は次である。

> DAG 判定はグラフ理論でよい。  
> しかし設計原則全体の分類には、抽象化・商・関手・観測・置換を統一できる圏論が効く。

## Lean と実証の分担

Lean では、定義が明確で全称命題として扱える部分を証明する。

- 到達可能性の反射性・推移性
- 依存グラフから thin category が生成されること
- `StrictLayered -> Acyclic`
- `StrictLayered -> FinitePropagation`
- 初期定義 `Decomposable G := StrictLayered G` の下で、層化例が Decomposable であること
- SOLID 風局所条件だけでは Decomposable が従わない反例
- Layered 条件が Decomposable を与えること

実証研究では、現実コードベースから抽出したシグネチャと運用データの関係を検証する。

- `Sig(A)` と変更ファイル数の相関
- SCC サイズと障害修正時間の相関
- fanout とレビューコストの相関
- 境界違反と将来の変更波及の相関

この分担により、Lean で証明できる数学的事実と、現実データで反証可能な仮説を混同しない。
