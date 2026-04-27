# 研究の最終ゴール

## 一文で言うと

代数的アーキテクチャ論 V2 の最終ゴールは、次の状態に到達することである。

> **アーキテクチャ零曲率定理**を中心定理として、
> 設計の破れを有限な阻害証人として提示できる診断理論を作る。

ここでいうアーキテクチャ零曲率定理は、完成時に次の形で定式化することを目指す。

```text
有限な法則宇宙と完全被覆の下で、
アーキテクチャが法則健全であることは、
要求法則族に対する有限な阻害証人が存在しないこと、
すなわち ArchitectureSignature の要求阻害軸がすべて零であることと同値である。
```

Lean 側では、この主張を最初から数値的な曲率として定義しない。
まず witness 型、bad predicate、測定候補 list、violation count からなる
generic witness-count kernel と、有限測定 universe 上の零カウント橋渡しとして育てる。
現在の Lean proved package では、current law-universe policy 下の
**static structural core の QED** として、selected required axes の零性と
matrix diagnostics を `ArchitectureZeroCurvatureTheoremPackage` として束ねる。
この QED が指す中心命題は
`ArchitectureLawful X ↔ RequiredSignatureAxesZero (ArchitectureLawModel.signatureOf X)`
および `ArchitectureLawful X ↔ ArchitectureZeroCurvatureTheoremPackage X` である。
runtime metrics と一般数値 curvature は、この package には含めないが、
数学的コアの将来拡張として Lean 証明対象にできる。runtime 側では 0/1
`RuntimeDependencyGraph` が与えられた後の zero metric / obstruction absence bridge、
数値 curvature 側では `curvature = 0 <-> DiagramCommutes` bridge を狙う。
一方、実コード extractor の完全性と empirical hypotheses は、中心定理そのものではなく、
実用・検証・実証研究の層に残す。

この中心定理候補の上で、より広い最終ゴールは次である。

> ソフトウェアアーキテクチャを依存・抽象・観測・状態遷移・実行時依存の複数グラフまたは代数構造として表現し、設計原則をそれらの不変量を保存・改善する変換クラスを誘導するものとして分類し、不変量の破れを `ArchitectureSignature` として定量評価し、さらに実コードベース上で変更コスト・障害修正コストとの関係を検証できる理論とツールを作る。

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

> 設計原則は、アーキテクチャ不変量を保存・改善する変換クラスを誘導する。
>
> 品質は、不変量の破れを多軸シグネチャとして評価する。
>
> 診断とは、要求法則族に対する阻害証人を特定し、その座標表示として
> `ArchitectureSignature` を読むことである。

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

この対応は無条件の同値として主張しない。`Acyclic -> StrictLayered`,
`Acyclic -> FinitePropagation`, adjacency matrix の nilpotence との対応は、
有限 `ComponentUniverse` などの適切な有限性仮定の下で整理する。

ただし、`Decomposable G := StrictLayered G` という定義方針は維持する。`Acyclic`, `FinitePropagation`, `Nilpotent` などを定義に混ぜず、後から定理として接続する。

完成時の意味は次である。

```text
Layered Architecture は、
依存グラフに ranking 関数を与えることで、
循環を排除し、
影響伝播を有限段で止め、
隣接行列の冪零性に対応する。
```

言い換えると、レイヤードアーキテクチャは、依存行列を冪零化する方向の設計変換を誘導する原則として理解できる。

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

- 静的依存グラフ
- 実行時依存グラフ
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
最初の pilot study では [Signature 実証プロトコル](design/empirical_protocol.md) に従い、
対象 repository、期間、before / after signature、PR / issue / incident metadata、
除外条件を固定してから分析する。

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
| 実行時依存・障害伝播 | 障害はどこまで伝播するか。実行時に隠れた密結合がないか。 | `runtimeFanout`, `runtimeExposureRadius`, `runtimeBlastRadius`, `circuitBreakerCoverage` |
| 分散収束・ログ整合性 | 分散状態は前提条件のもとで収束するか。 | `consensusPreconditionRisk`, `divergenceWindow`, `replicationLagRisk` |
| 実証的コスト | 指標は実際の変更・障害コストと関係するか。 | `empiricalChangeCost`, `reviewCost`, `incidentRepairCost` |

Signature v1 では、これらを一度にすべて Lean 構造へ入れない。まず v0 の安定軸を保持し、分解可能性・依存伝播・境界・抽象化の executable metric を v1 core とする。`nilpotencyIndex` と `rho(A)` は adjacency matrix bridge の後続軸であり、`rho(A)` については finite DAG から 0、finite closed walk から正になる構造的 bridge を証明済みである。`runtimePropagation` は 0/1 `RuntimeDependencyGraph` 上の outgoing exposure radius から始め、既存名は `runtimeExposureRadius` の互換名として扱う。障害源から影響を受け得る範囲を測る `runtimeBlastRadius` は reverse reachability 由来の empirical / tooling 側 metric として分離する。`relationComplexity`, `empiricalChangeCost`, runtime metadata の解釈は empirical extraction と実証プロトコル側の軸として分離する。`relationComplexity` は状態遷移代数層の構成要素ベクトルとして観測し、単一スコアだけで設計を評価しない。

静的依存と実行時依存は別 graph role として抽出する。Lean core の初期形は `StaticDependencyGraph` と `RuntimeDependencyGraph` をどちらも `ArchGraph` の 0/1 edge として扱い、runtime edge の label, weight, failure mode, timeout budget, retry policy, circuit breaker coverage は empirical tooling 側に置く。

adjacency matrix bridge では、有限 `ComponentUniverse` 上の 0/1 隣接行列を使い、DAG / `WalkAcyclic` / nilpotence の対応を Lean theorem として育てる。`rho(A)` は同じ行列表現から来る伝播増幅の候補軸だが、Lean 側では finite DAG で `rho(A)=0`、finite closed walk で `rho(A)>0` になる構造的事実だけを扱い、実証上の増幅解釈は分離する。

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
  runtimeExposureRadius     = 5
  runtimeBlastRadius        = 8

Architecture Signature after:
  hasCycle                  = 0
  sccExcessSize             = 0
  maxDepth                  = 6
  fanoutRisk                = 21
  boundaryViolationCount    = 5
  abstractionViolationCount = 2
  relationComplexity        = 38
  runtimeExposureRadius     = 3
  runtimeBlastRadius        = 4
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

## 完成時のコンピューターサイエンスにおける位置付け

完成時のこの研究は、ソフトウェアアーキテクチャの設計原則を、形式的に定義された
不変量と実コード上の測定可能なリスク指標へ翻訳する研究基盤として位置付けられる。

狙いは、既存のコンピューターサイエンスを置き換える大理論を作ることではない。
むしろ、次の領域を接続することで、アーキテクチャ設計をより検査可能な対象にする。

| 領域 | この研究での役割 |
| --- | --- |
| Formal Methods | 依存グラフ、到達可能性、層化、有限 universe、Signature v0 の構造的性質を Lean で証明する。 |
| Software Architecture | 設計原則を、どの不変量を保存・改善する変換クラスを誘導するかで分類する。 |
| Empirical Software Engineering | Signature と変更波及、レビューコスト、障害修正コストの関係を実データで検証する。 |
| Program Analysis / Tooling | import graph、依存グラフ、実行時依存、状態遷移の候補を実コードから抽出する。 |

中心的な貢献は、設計原則の自然言語的な説明を、そのまま Lean theorem に押し込むことではない。
Lean で証明できる構造的事実と、実コードベース上で検証する empirical hypothesis を分けた上で、
両者を `ArchitectureSignature` という多軸診断で接続することである。

このため、完成時の位置付けは次のようになる。

- 設計原則の形式的分類:
  SOLID, Layered Architecture, Clean Architecture, Event Sourcing, Saga, CRUD,
  Circuit Breaker などを、それぞれが守る不変量と守らない不変量で説明する。
- Architecture Signature:
  アーキテクチャ品質を単一スコアではなく、循環、SCC、fanout、境界違反、抽象化違反、
  状態遷移複雑度、実行時伝播などの多軸リスクベクトルとして扱う。
- 形式証明と実証研究の橋渡し:
  `StrictLayered -> Acyclic` のような構造的命題は Lean で証明し、
  `sccMaxSize` と障害修正時間の関係のような品質仮説は実証研究で検証する。

実務的には、アーキテクチャレビューを「経験的な感想」から「どの不変量が破れているかの診断」へ近づける。
教育的には、設計原則を「何を保証するか」「何は保証しないか」で教える教材になる。
研究的には、形式手法、ソフトウェアアーキテクチャ、実証ソフトウェア工学を接続する境界領域の成果を目指す。

長期的には、AI code review や architecture diagnosis tooling に対して、
何を測るべきか、どの主張は証明済みで、どの主張は実証仮説なのかを区別する評価軸を提供できる。
