# 研究の最終ゴール

## 一文で言うと

代数的アーキテクチャ論 V2 の最終ゴールは、次の状態に到達することである。

> ソフトウェアアーキテクチャを依存・抽象・観測・状態遷移・実行時依存の複数グラフまたは代数構造として表現し、設計原則をそれらの不変量保存操作として分類し、不変量の破れを `ArchitectureSignature` として定量評価し、さらに実コードベース上で変更コスト・障害修正コストとの関係を検証できる理論とツールを作る。

より短く言えば、目的は次である。

> アーキテクチャレビューを「感想」から「診断」に変える理論を作る。

この診断は万能の単一スコアではない。何を守りたいのか、すなわち分解可能性、置換可能性、履歴再構成性、障害局所性、分散収束性、変更容易性などのどの不変量を重視するのかを明確にし、その不変量がどれだけ守られているかを多軸で測る。

## 完成形

全フェーズを完走したとき、この研究は次の三つを接続する。

1. アーキテクチャの健康診断理論
2. Lean で保証された形式的土台
3. 実コードから測れる評価ツール

単に「圏論でソフトウェア設計を説明する」ことが目的ではない。最終的には、次の問いに答えられる状態を目指す。

- この設計原則は、どの不変量を守るのか。
- このコードベースでは、どの不変量がどれだけ破れているのか。
- その破れは、変更波及・障害修正・レビューコストとどの程度関係するのか。

これは V2 の中心主張の完成形である。

> 設計原則は、アーキテクチャ不変量を保存・改善する操作である。
>
> 品質は、不変量の破れを多軸シグネチャとして評価する。

## 四つの成果物

### 1. 設計原則の分類表

SOLID、Layered Architecture、Clean Architecture、Event Sourcing、Saga、CRUD、Circuit Breaker、Replicated Log などを、単なるパターン名ではなく、次の観点で整理する。

- 何を保証するか。
- どの不変量を守るか。
- どのリスクを下げるか。
- 何は保証しないか。

完成時には、たとえば次のように言える状態を目指す。

- SOLID は局所的な抽象・責務・置換の健全性を保証する。
- Layered Architecture は大域的な分解可能性を保証する。
- Event Sourcing は履歴再構成性を与えるが、関係式複雑度を増やし得る。
- Saga は局所回復性を与えるが、補償射は一般に逆射ではない。
- Circuit Breaker は実行時障害伝播を遮断する。
- Replicated Log は前提条件のもとで収束性を保証する。

重要なのは、SOLID を万能原理にしないことである。設計原則を好みではなく、保証する不変量の違いとして語れるようにする。

### 2. Lean で保証された形式的中核

完成時には、少なくとも次の対応が Lean 側で整理されていることを目指す。

```text
StrictLayered
↔ Acyclic
↔ WalkAcyclic
↔ FinitePropagation
↔ Nilpotent adjacency matrix
```

ただし、`Decomposable G := StrictLayered G` という定義方針は維持する。`Acyclic`, `FinitePropagation`, `Nilpotent` などを定義に混ぜず、後から定理として接続する。

完成時の意味は次である。

```text
Layered Architecture は、
依存グラフに ranking 関数を与えることで、
循環を排除し、
影響伝播を有限段で止め、
隣接行列の冪零性に対応する。
```

言い換えると、レイヤードアーキテクチャは依存行列を冪零化する設計原則として理解できる。

### 3. 安定した Architecture Signature

完成時の `ArchitectureSignature` は、初期の足場ではなく、実コードから抽出できる多軸評価ベクトルになる。

最終形の候補は次のような構造である。

```text
Sig(A) =
  < DecompositionRisk,
    PropagationRisk,
    BoundaryRisk,
    AbstractionRisk,
    BehavioralRisk,
    StateTransitionRisk,
    RuntimeRisk,
    EmpiricalCost >
```

単一スコア化は、経営報告やランキングの補助としてはあり得る。しかし研究の中心ではない。中心は、次を説明できることである。

- どの軸が悪化したか。
- どの不変量が破れているか。
- どの設計原則で改善できるか。

### 4. 実コードからの抽出と実証研究

最終的には、GitHub リポジトリやコードベースを入力として、次のような構造を抽出し、`ArchitectureSignature` を計算できる状態を目指す。

- 依存グラフ
- 抽象射影
- 観測可能な振る舞い
- 境界違反
- SCC
- fanout
- depth
- runtime dependency
- state transition relation

さらに、実証研究として次の関係を検証する。

- signature の悪化と変更ファイル数の増加
- SCC サイズと障害修正時間
- fanout とレビューコスト
- 境界違反と将来の変更波及
- relation complexity と運用リスク

これらは Lean の定理ではなく、実データで検証する仮説として扱う。

## 評価軸

完成時の定量評価は、少なくとも次の軸を持つ。

| 軸 | 評価する問い | 代表的な指標 |
| --- | --- | --- |
| 分解可能性・循環リスク | この構造は層化可能か。循環依存はどれだけ危険か。 | `hasCycle`, `sccExcessSize`, `weightedSccRisk`, `nilpotencyIndex` |
| 変更波及・依存伝播 | 変更はどれだけ広がるか。依存伝播は増幅するか。 | `maxDepth`, `maxFanout`, `totalFanout`, `reachableConeSize`, `rho(A)` |
| 境界・レイヤー違反 | レイヤーやドメイン境界を破っていないか。 | `layerViolationCount`, `boundaryViolationCount`, `forbiddenDependencyCount` |
| 抽象化・DIP 整合性 | 具体依存が抽象グラフに整合して写っているか。 | `projectionSoundnessViolation`, `projectionCompletenessGap`, `representativeStabilityViolation` |
| LSP・観測可能性 | 実装を差し替えても観測可能な振る舞いが保たれるか。 | `observationalDivergence`, `lspViolationCount`, `behavioralDistance` |
| 状態遷移・関係式複雑度 | 補償・制約・失敗パスが複雑すぎないか。 | `relationComplexity`, `compensationCount`, `failureTransitionCount` |
| 実行時依存・障害伝播 | 障害はどこまで伝播するか。実行時に隠れた密結合がないか。 | `runtimeFanout`, `runtimePropagationRadius`, `circuitBreakerCoverage` |
| 分散収束・ログ整合性 | 分散状態は前提条件のもとで収束するか。 | `consensusPreconditionRisk`, `divergenceWindow`, `replicationLagRisk` |
| 実証的コスト | 指標は実際の変更・障害コストと関係するか。 | `empiricalChangeCost`, `reviewCost`, `incidentRepairCost` |

Signature v1 では、これらを一度にすべて Lean 構造へ入れない。まず v0 の安定軸を保持し、分解可能性・依存伝播・境界・抽象化の executable metric を v1 core とする。`nilpotencyIndex` と `rho(A)` は adjacency matrix bridge の後続軸、`relationComplexity`, `runtimePropagation`, `empiricalChangeCost` は empirical extraction と実証プロトコル側の軸として分離する。

adjacency matrix bridge では、有限 `ComponentUniverse` 上の 0/1 隣接行列を使い、DAG / `WalkAcyclic` / nilpotence の対応を Lean theorem として育てる。`rho(A)` は同じ行列表現から来る伝播増幅の候補軸だが、初期 bridge では解析的・実証的拡張に分離する。

## 利用イメージ

完成時には、設計改善の前後を次のように比較できる。

```text
Architecture Signature before:
  hasCycle                  = 1
  sccExcessSize             = 14
  maxDepth                  = 9
  fanoutRisk                = 37
  boundaryViolationCount    = 22
  abstractionViolationCount = 8
  relationComplexity        = 41
  runtimePropagationRadius  = 5

Architecture Signature after:
  hasCycle                  = 0
  sccExcessSize             = 0
  maxDepth                  = 6
  fanoutRisk                = 21
  boundaryViolationCount    = 5
  abstractionViolationCount = 2
  relationComplexity        = 38
  runtimePropagationRadius  = 3
```

このとき、単に「リファクタリングで良くなった」とは言わない。

- 循環依存が消えた。
- SCC が分解された。
- 最大依存深度が下がった。
- 境界違反が減った。
- 抽象化違反が減った。
- ただし `relationComplexity` はあまり下がっていないので、状態遷移設計にはまだ改善余地がある。

このように、改善の効果を「どの不変量が改善したか」で説明できるようにする。

## 分担

この研究では、Lean で証明することと、実データで検証することを分ける。

- Lean で証明するもの:
  - 到達可能性、walk、path、層化、非循環性、有限伝播、射影、観測などの構造的命題。
  - `StrictLayered`, `Acyclic`, `WalkAcyclic`, `FinitePropagation`, adjacency matrix nilpotence の対応。

- 実証研究で検証するもの:
  - signature の悪化と変更コストの相関。
  - SCC や fanout とレビュー・障害修正コストの相関。
  - 境界違反や関係式複雑度が将来の変更波及や運用リスクに与える影響。

この分担により、形式証明、設計原則の分類、定量評価、実証研究を一本につなげる。
