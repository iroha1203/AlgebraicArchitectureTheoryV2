# Paper-ready research note outline

Lean status: `docs synthesis` / `research exposition`.

この文書は、代数的アーキテクチャ論 v2 の現時点の成果を外部説明用の
technical note / paper outline として圧縮する。目的は、新しい Lean 定理を主張する
ことではなく、Lean で証明済みの構造的事実、executable metric として定義済みの軸、
実データで検証する empirical hypothesis を読み手が混同しない形で接続することである。

## Abstract

本研究は、ソフトウェア設計原則を経験則や好みではなく、アーキテクチャ不変量を
保存・改善する操作として整理する。依存、抽象、観測、状態遷移、実行時依存を
それぞれ graph または代数構造として扱い、どの不変量が保たれ、どの不変量が破れて
いるかを `ArchitectureSignature` という多軸診断で記録する。

中心主張は次である。

```text
設計原則は、アーキテクチャ不変量を保存・改善する操作である。
アーキテクチャ品質は、不変量の破れを多軸シグネチャとして評価する。
```

この主張は単一スコアの品質評価ではない。たとえば循環依存、SCC excess、fanout、
境界違反、抽象化違反、観測可能な振る舞いの不一致、状態遷移複雑度、実行時障害伝播は
異なる不変量の破れであり、同じ数値へ早期に潰すと設計上の診断情報を失う。

Lean 側では、`ArchGraph`, `Reachable`, `StrictLayered`, `Decomposable`,
`ComponentCategory`, `ComponentUniverse`, `ArchitectureSignature` などを用いて、
有限 universe 上で扱える構造的事実を証明する。実コードベースからの抽出と、signature
と変更・レビュー・障害修正コストの相関は Lean theorem ではなく empirical hypothesis
として扱う。

## 1. Problem statement

アーキテクチャレビューでは、しばしば「依存が複雑」「責務が混ざっている」「境界が弱い」
「運用時に障害が広がる」といった評価が行われる。しかし、これらの評価は同じ種類の
リスクではない。循環依存の破れ、抽象化の破れ、LSP 的な観測可能性の破れ、状態遷移の
複雑化、runtime dependency の増幅は、それぞれ異なる構造を見ている。

本研究の問いは次の三つである。

1. 設計原則は、どのアーキテクチャ不変量を保存・改善する操作として説明できるか。
2. その不変量の破れを、実コードベース上で測れる多軸 signature として表現できるか。
3. signature の変化は、変更波及、レビューコスト、障害修正コストと関係するか。

ここで重要なのは、1 と 2 の一部は形式的に証明できるが、3 は実データ上の仮説である
という分離である。Lean は「有限 graph 上でこの executable metric はこの graph-level
property と一致する」といった構造的事実を証明する。Lean は「現実の変更コストが必ず
増える」といった経験的主張を証明しない。

## 2. Core representation

基本対象は component 間の依存 graph である。

```text
edge c -> d means component c depends on component d.
```

この向きに合わせて、strict layering は依存先が必ず下位層に落ちることとして定義する。

```text
StrictLayered G :=
  exists layer : C -> Nat,
  for every edge c -> d, layer d < layer c
```

現在の `Decomposable` は意図的に小さく保つ。

```text
Decomposable G := StrictLayered G
```

`Acyclic`, `FinitePropagation`, adjacency matrix nilpotence, spectral condition を
`Decomposable` の定義へ混ぜない。これらは別 theorem または bridge layer として接続する。
この方針により、分解可能性の定義と、そこから導ける構造的性質を分けて説明できる。

到達可能性 `Reachable G a b` は反射推移閉包であり、`ComponentCategory G` はこれを
Hom にする thin category である。thin category は「到達可能かどうか」を保持するが、
path count、walk length、walk の本数を忘れる。したがって定量評価では、thin category
とは別に `Walk`, `Path`, finite metrics, adjacency matrix を扱う。

## 3. What is proved in Lean

現時点の Lean core は、次のような構造的事実を持つ。

| 領域 | 代表的な Lean object / theorem | Lean status |
| --- | --- | --- |
| graph and reachability | `ArchGraph`, `Reachable`, `Reachable.trans`, `Reachable.exists_path` | `defined only` / `proved` |
| layering | `StrictLayered`, `Acyclic`, `WalkAcyclic`, `FinitePropagation` | `defined only` / `proved bridge` |
| decomposition | `Decomposable G := StrictLayered G`, `decomposable_acyclic`, `decomposable_finitePropagation` | `defined only` / `proved` |
| thin category | `ComponentCategory`, `componentCategory_thin` | `defined only` / `proved` |
| finite universe | `ComponentUniverse`, `FiniteArchGraph`, bounded reachability correctness | `defined only` / `proved` |
| v0 / v1 metrics | `ArchitectureSignature`, `ArchitectureSignatureV1Core`, `ArchitectureSignatureV1` | `defined only` with proved metric bridges |
| projection | `ProjectionSound`, `ProjectionComplete`, `ProjectionExact`, finite violation count bridges | `defined only` / `proved` |
| observation | `ObservationFactorsThrough`, `LSPCompatible`, `lspViolationCount` bridges | `defined only` / `proved` |
| matrix bridge | adjacency powers, nilpotence, `nilpotencyIndex`, spectral radius structural bridge | `defined only` / `proved` |

重要な接続は次である。

```text
StrictLayered -> Acyclic
StrictLayered -> FinitePropagation
Acyclic <-> WalkAcyclic
Acyclic + finite ComponentUniverse -> StrictLayered
finite DAG <-> adjacency matrix nilpotence
finite DAG -> rho(A) = 0
finite closed walk -> rho(A) > 0
```

これらは無条件の現実コード品質 claim ではない。有限 universe、測定対象 list、
edge closure、coverage などの前提を明示した graph-level theorem である。

## 4. Architecture Signature

`ArchitectureSignature` は、アーキテクチャ品質を単一数値へ潰すためのものではなく、
不変量の破れを多軸で読むための診断ベクトルである。

v0 互換軸は次の 6 軸である。

```text
Sig0(A) =
  < hasCycle,
    sccMaxSize,
    maxDepth,
    fanoutRisk,
    boundaryViolationCount,
    abstractionViolationCount >
```

v1 では、v0 の安定軸を保持しながら、Lean core で測れる派生軸と empirical extension
axis を分ける。

| 軸 | 意味 | Lean status |
| --- | --- | --- |
| `sccExcessSize` | singleton SCC を 0 risk とする循環リスク | executable metric / proved bridge |
| `weightedSccRisk` | component weight を入力にした SCC excess contribution | executable metric / proved local properties |
| `maxFanout` | source ごとの依存集中 | executable metric / proved bridge |
| `reachableConeSize` | 変更波及の到達範囲 | executable metric / proved bridge |
| `projectionSoundnessViolation` | 具象依存が抽象依存へ sound に写らない数 | executable metric / proved bridge |
| `lspViolationCount` | 同じ抽象に写る実装 pair の観測差分 | executable metric / proved bridge |
| `nilpotencyIndex` | finite adjacency matrix が 0 になる最初の power | executable metric / proved acyclic bridge |
| `runtimePropagation` | 0/1 runtime graph 上の propagation radius | executable metric / empirical interpretation |
| `relationComplexity` | 状態遷移代数層の構成要素ベクトル | empirical hypothesis |
| `empiricalChangeCost` | PR / issue / incident metadata 由来の目的変数 | empirical hypothesis |

`ArchitectureSignatureV1` の optional extension axis では `Option Nat.none` を
未評価として扱う。`none` や dataset schema の `null` は risk 0 ではない。これは
extractor output の `metricStatus.<axis>.measured = false` と同じ規約であり、
未測定を「違反なし」と誤読しないための設計である。

## 5. Projection and observation

抽象化や DIP 的な構造は、具象 component から抽象 component への
`InterfaceProjection` として扱う。Projection bridge は、具象依存が抽象依存へ sound に
写るかを扱う。`projectionSoundnessViolation` は finite universe 上で、測定対象 concrete
edge のうち abstract edge として表現できないものを数える。

Observation bridge は別の不変量を扱う。`Observation` は実装を観測値へ写し、
`ObservationFactorsThrough` は観測が抽象射影を通って factor することを表す。
この条件から `LSPCompatible` が得られ、finite universe 上では `lspViolationCount = 0`
を導ける。

この二つは同じ projection を共有できるが、同じ主張ではない。

```text
Projection bridge: concrete dependency is soundly represented abstractly.
Observation bridge: observable behavior is stable through abstraction.
```

局所置換契約 `LocalReplacementContract` は、projection soundness と observation
factorization を束ねる。Lean では、この bundle から projection soundness violation
count と LSP violation count が同時に 0 になる theorem を持つ。一方で、repository-level
の重みづけ、severity、将来変更への影響は empirical 側の分析に残す。

## 6. Matrix bridge and propagation

Adjacency matrix bridge は、thin `ComponentCategory` が忘れる walk count と walk length
を扱うための別層である。有限 `ComponentUniverse` 上で 0/1 adjacency matrix を作り、
`A^k` の entry を長さ `k` の walk の存在や本数と接続する。

この bridge の役割は、`Decomposable` の定義を変えることではない。

```text
Decomposable = StrictLayered
Matrix bridge = finite graph facts about walks and adjacency powers
```

Lean では、有限 universe 上で adjacency nilpotence と `WalkAcyclic` / `Acyclic` の対応を
証明済みである。また `nilpotencyIndexOfFinite` は、最初に `A^k = 0` となる power を
`Option Nat` として返す executable axis である。`some k` は測定できた値、`none` は
非 DAG または未成立を表す欠損的な値であり、risk 0 ではない。

Spectral radius `rho(A)` は mathlib-backed な解析的拡張である。Lean では finite DAG で
`rho(A)=0`、有限閉 walk がある場合に `rho(A)>0` となる構造的 bridge を証明済みである。
ただし、`rho(A)` が現実の変更波及や障害伝播コストをどの程度説明するかは empirical
hypothesis である。

## 7. Design principle classification

設計原則は万能な善悪判断ではなく、どの不変量を保存・改善するかで分類する。

| 層 | 代表例 | 主に扱う不変量 |
| --- | --- | --- |
| 局所契約層 | SOLID, DIP, LSP | 抽象化整合性、観測可能な置換可能性 |
| 大域構造層 | Layered Architecture, Clean Architecture | 層化可能性、非循環性、有限伝播、境界分離 |
| 状態遷移代数層 | Event Sourcing, Saga, CRUD | 履歴再構成性、補償、制約、失敗遷移 |
| 実行時依存・分散収束層 | Circuit Breaker, Replicated Log | runtime propagation、障害局所性、収束前提 |

この分類では SOLID を万能原理として扱わない。SOLID は局所的な契約や置換可能性を
改善し得るが、それだけでは大域的な `Decomposable` は従わない。Layered / Clean
Architecture は大域構造層の不変量を扱う。Event Sourcing や Saga は状態遷移代数層の
構造を増やすため、履歴再構成性や局所回復性を与えつつ、relation complexity を増やす
可能性がある。Circuit Breaker は runtime dependency graph 上の障害伝播を遮断するが、
静的依存 graph の層化そのものを保証するわけではない。

## 8. Empirical extraction and dataset

実コードベースからの抽出は、Lean proof とは別の tooling 層で扱う。

`sig0-extractor` は Lean source file と import 文から component list と import edge を
抽出し、v0 signature 入力になる JSON を生成する。これは `ComponentUniverse` の完全な
証明 witness ではない。extractor は測定データを作る外部 tool であり、Lean 側の
`ComponentUniverse` は proof-carrying measurement universe として残る。

Empirical dataset では、PR 単位で before / after signature、signed delta、PR metadata、
issue / incident metadata、metric status を記録する。

```text
EmpiricalSignatureDatasetV0 =
  repository
  pullRequest
  signatureBefore
  signatureAfter
  deltaSignatureSigned
  metricDeltaStatus
  prMetrics
  issueIncidentLinks
  analysisMetadata
```

`deltaSignatureSigned` は `Nat` subtraction ではなく `Int` 差分である。改善による負の
差分を 0 に丸めない。また before / after のどちらかで未評価の軸は delta を欠損値にし、
0 として扱わない。

pilot study で検証する仮説は、最初に検証しやすい primary analysis と、
追加データが必要な exploratory analysis に分ける。H1 は同じ PR 内の
signature delta と changed files の同時決定性を避けるため、pre-change risk を見る
H1a と、将来観測窓を見る H1b に分ける。

| ID | tier | 仮説 | 主な説明変数 | 主な目的変数 |
| --- | --- | --- | --- | --- |
| H1a | primary | PR 前の Signature risk は変更波及の増加と相関する | pre-change `reachableConeSize`, `maxDepth`, `fanoutRisk`, `sccExcessSize` | changed files, changed lines, changed components |
| H1b | exploratory | PR 前後の Signature delta は将来 co-change / repair scope と相関する | `deltaSignatureSigned`, risk increase / decrease vectors | future co-change, future repair scope |
| H2 | exploratory | SCC / cycle risk が大きい領域では障害修正コストが増える | `hasCycle`, `sccExcessSize` | repair time, hotfix size |
| H3 | primary | fanout risk が高い変更はレビューコストが増える | pre-change `fanoutRisk`, `maxFanout` | review comments, review rounds, approval time |
| H4 | exploratory | 境界違反と relation complexity は将来リスクと相関する | `boundaryViolationCount`, `relationComplexity` components | future co-change, incident count |
| H5 | exploratory | runtime propagation が大きい領域では incident scope が広がる | `runtimePropagation`, `runtimeFanout` | affected components, repair time |

これらは Lean proof のブロッカーではない。反証可能な empirical hypothesis として、
対象 repository、対象 PR、除外条件、欠損値規約を固定した上で検証する。
最初の technical note では、H1a/H3 の primary analysis に必要な dataset と欠損値規約の
再現性、小規模 pilot の記述統計、効果量、外れ値を報告する。H1b/H2/H4/H5 は、
incident data、future window、boundary policy、relation complexity rule set、
runtime evidence が揃う場合だけ exploratory analysis とし、因果効果や repository 一般化は
主張しない。

## 9. Contributions

この研究の貢献は、自然言語の設計原則をそのまま Lean theorem に押し込むことではない。
貢献は、形式証明できる構造的事実と、実データで検証する仮説を分離し、それらを
`ArchitectureSignature` という多軸診断で接続する点にある。

具体的には次を提供する。

1. 設計原則を、保存・改善する不変量の違いとして分類する枠組み。
2. `Decomposable := StrictLayered` を小さく保ち、acyclicity、finite propagation、
   matrix nilpotence、spectral facts を theorem / bridge として接続する Lean core。
3. finite universe 上の executable metric と graph-level property の対応を証明する
   `ComponentUniverse` ベースの測定基盤。
4. projection soundness と observation / LSP を分けて扱う局所契約層。
5. Signature v0 / v1 を、未評価と risk 0 を混同しない多軸 schema として整理する方針。
6. extractor output、dataset schema、pilot protocol を通じて empirical validation へ
   接続する実証研究の入口。

## 10. Suggested paper structure

最初の paper-ready draft は、次の構成にできる。

1. Introduction: アーキテクチャレビューを感想から診断へ移す問題設定。
2. Architecture invariants: 依存、抽象、観測、状態遷移、runtime dependency の分離。
3. Formal core in Lean: `ArchGraph`, `Reachable`, `StrictLayered`, `Decomposable`,
   `ComponentCategory`, `ComponentUniverse`。
4. Decomposition and propagation: acyclicity、finite propagation、matrix nilpotence、
   `rho(A)` bridge。
5. Architecture Signature: v0 / v1 axes、risk order、`Option Nat` と欠損値規約。
6. Projection and observation: DIP / LSP / local replacement contract の位置づけ。
7. Empirical protocol: extractor、dataset、before / after signature、primary H1a/H3 と
   exploratory H1b/H2/H4/H5。
8. Threats to validity: component 粒度、policy 未指定、external dependency、runtime
   evidence、repository selection。
9. Related work: formal methods, software architecture metrics, empirical software
   engineering, program analysis。
10. Conclusion: 設計原則を不変量保存操作として扱い、品質を多軸 signature として診断する。

## 11. Current boundaries

現時点で主張しないことも明確にしておく。

- `ArchitectureSignature` は単一スコアではない。
- `sig0-extractor` は Lean の `ComponentUniverse` 証明 witness を生成しない。
- `ComponentCategory` は thin category であり、path count や walk length を保持しない。
- `runtimePropagation`, `relationComplexity`, `empiricalChangeCost` は Lean の全称定理ではない。
- `rho(A)` の structural bridge は証明済みだが、現実のコスト解釈は empirical hypothesis である。
- SOLID は局所契約層であり、大域的な `Decomposable` を単独では保証しない。

この境界を保つことで、Lean proof、executable tooling、empirical validation の責務を
混同せずに、研究の中心主張を paper-ready な形へ整理できる。
