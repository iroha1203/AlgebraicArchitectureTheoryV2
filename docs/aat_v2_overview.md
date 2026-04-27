# 代数的アーキテクチャ論 v2 概要

## 中心主張

代数的アーキテクチャ論 v2 は、ソフトウェア設計原則を経験則ではなく、アーキテクチャ不変量を保存・改善する変換クラスを誘導するものとして分類する研究である。

中心に置く定理候補は次である。

```text
アーキテクチャ零曲率定理

有限な法則宇宙と完全被覆の下で、
アーキテクチャが法則健全であることは、
要求法則族に対する有限な阻害証人が存在しないこと、
すなわち ArchitectureSignature の要求阻害軸がすべて零であることと同値である。
```

ここで「零曲率」は、初期 Lean 形式化では数値的な差分ではなく、
要求された law family に対する阻害証人が存在しないことを表す。
可換図式の非可換性はその重要な特殊例であり、依存閉路、projection violation、
LSP violation、状態遷移 law の破れ、effect leakage などは、
それぞれの witness family として扱う。

現在 Lean で **static structural core の QED** と呼ぶ範囲は、
current law-universe policy 下の
`ArchitectureLawful X ↔ RequiredSignatureAxesZero (ArchitectureLawModel.signatureOf X)`
および `ArchitectureLawful X ↔ ArchitectureZeroCurvatureTheoremPackage X` である。
この required law は closed-walk acyclicity、projection soundness、LSP compatibility、
boundary policy soundness、abstraction policy soundness の五つに限る。
state/effect laws は derived / separate bridge として扱い、runtime metrics、
empirical hypotheses、一般数値 curvature、実コード extractor の完全性は
この QED に含めない。runtime metrics と一般数値 curvature は将来の数学的コア拡張、
extractor completeness と empirical hypotheses は実用・実証層として分ける。

この定理候補を支える基本主張は次である。

> 設計原則は、アーキテクチャ不変量を保存・改善する変換クラスを誘導する。
> アーキテクチャ品質は、それらの不変量の破れを多軸シグネチャとして定量評価できる。

この主張により、設計議論を「よい/悪い」という経験的評価から、「どの不変量を保存・改善する変換を選んでいるか」「どの不変量が破れているか」「その破れがどの程度か」という検証可能な形へ移す。

最終的な完成像は、アーキテクチャレビューを「感想」から「診断」に変える理論とツールである。すなわち、設計原則が守る不変量、コードベース上で破れている不変量、その破れと変更波及・障害修正・レビューコストの関係を説明できる状態を目指す。詳細は [研究の最終ゴール](research_goal.md) にまとめる。

## v2 の目的

v2 の目的は、既存 Part1 から Part7 の成果を、法則・証人理論、分類理論、証明理論、評価理論へ整理し直すことである。

1. 法則・証人理論: 法則宇宙、要求法則族、阻害証人、完全被覆、零カウント橋渡しを定義する。
2. 分類理論: 設計原則を、誘導する変換クラスと保証するアーキテクチャ不変量ごとに分類する。
3. 証明理論: 分解可能性、層化可能性、非循環性、冪零性、有限影響伝播の対応を明確にする。
4. 評価理論: 不変量の破れを Architecture Signature として多軸評価する。

この再構成では、スペクトル半径やゼータ関数を最初から中心に置かない。まずはグラフ理論的・操作的に意味が明確な指標を定義し、その発展として解析的指標を接続する。

## 四層構造

### 第0層: 法則・証人

アーキテクチャ零曲率定理のための中核層である。

ここでは、設計原則をすぐに数値指標へ落とさず、次を分けて扱う。

- 法則宇宙: どの law family を考えるか。
- 要求法則族: そのアーキテクチャに要求される law は何か。
- 阻害証人: 要求 law の破れを示す有限 witness は何か。
- 完全被覆: 測定候補が要求法則族を漏れなく覆っているか。
- 零カウント橋渡し: finite violation count が 0 であることを、測定済み witness の不在へ接続する。

可換図式の非可換性はこの層の重要な特殊例であるが、唯一の witness 形式ではない。
閉 walk、projection violation、LSP violation などは、それぞれの witness 型として扱う。

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

設計原則を「どの不変量を保証する変換クラスを誘導するか」で分類する。

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
    fanoutRisk,
    boundaryViolationCount,
    abstractionViolationCount >
```

`hasCycle` は 0/1 のリスク指標として扱う。`nilpotencyIndex?` は v1 extension axis として `Option Nat` で保持し、matrix bridge の `nilpotencyIndexOfFinite` で測定できる場合だけ `some` にする。

`maxDepth` は初期 Lean 実装では bounded max depth として扱う。循環グラフ上の真の大域 depth ではなく、有限 universe による fuel-bounded measurement である。循環リスクは `hasCycle` の別軸で扱う。

`sccMaxSize` は v0 互換の説明用指標として残すが、v1 core では非循環 singleton SCC を 0 risk にするため `sccExcessSize = sccMaxSize - 1` へ正規化する。`fanoutRisk : Nat` は v0 では `totalFanout` として定義し、疎なグラフでも測定 universe 内に依存辺があれば 0 に丸め落ちないようにする。`maxFanout` は局所集中を表す v1 core 軸、`reachableConeSize` は変更波及の到達範囲を表す v1 core 軸として追加済みである。

Lean 側では、有限な component list を測定 universe とする executable v0 metrics と、その list に `Nodup`, coverage, edge-closedness を持たせる `ComponentUniverse` を定義済みである。bounded reachability と `Walk` / `Reachable` の bridge、cycle indicator correctness、SCC count と相互到達可能性 class size の bridge、v1 core 派生 metric の主要 bridge は証明済みである。現在の `ComponentUniverse` は full universe なので edge-closedness は coverage から導けるが、将来 closed measurement sub-universe を扱う余地を残すため明示フィールドとして保持する。これは実コードベース抽出器の完全性を主張するものではない。

発展シグネチャ `Sig1(A)` では、解析的・実証的な軸を追加する。

```text
Sig1(A) =
  < decompositionRisk,
    propagationRisk,
    boundaryRisk,
    abstractionRisk,
    behavioralRisk,
    stateTransitionRisk,
    runtimeRisk,
    empiricalCost >
```

v1 は v0 を置き換える巨大な単一構造ではなく、v0 の安定軸を内側に含む多軸診断として設計する。まず `hasCycle`, `sccMaxSize`, `maxDepth`, `fanoutRisk`, `boundaryViolationCount`, `abstractionViolationCount` は v0 互換の executable metric として残す。その上で、次の順序で拡張する。

| 段階 | 軸 | 代表指標 | Lean status |
| --- | --- | --- | --- |
| v1 core | 分解可能性・循環リスク | `sccExcessSize`, `weightedSccRisk` | executable metric / proved bridge for `sccExcessSize` |
| v1 core | 変更波及・依存伝播 | `maxFanout`, `reachableConeSize`, `fanoutRisk = totalFanout` | executable metric / proved bridge for `maxFanout` and `reachableConeSize` |
| matrix bridge | 行列的伝播 | `nilpotencyIndex`, `rho(A)` | executable / proved bridge for `nilpotencyIndex`; proved `DAG -> rho(A)=0`; proved cycle positivity |
| projection bridge | 境界・抽象化 | `boundaryViolationCount`, `abstractionViolationCount`, `projectionSoundnessViolation` | executable metric / proved bridge |
| behavioral extension | 観測可能性 | `observationalDivergence`, `lspViolationCount` | executable metric / proved bridge |
| runtime / empirical extension | 実行時依存・状態遷移・実証コスト | `runtimePropagation`, `relationComplexity`, `empiricalChangeCost` | executable runtime radius; future runtime zero bridge; empirical hypothesis for cost correlation |

Lean 側の v1 output schema は、v0 互換軸を含む `ArchitectureSignatureV1Core` と、
未評価の発展軸を `Option Nat` で保持する `ArchitectureSignatureV1` に分ける。
`none` は未評価を意味し、risk 0 とは解釈しない。これにより、Lean で測定済みの
core axis と、extractor / empirical tooling 側で後から埋める extension axis を
同じ schema 上で区別できる。
この後半戦の統合方針は
[ArchitectureSignature v1 後半戦まとめ](design/signature_v1_wrapup.md)
に分離する。

`sccMaxSize` は v0 互換の説明用指標として残し、v1 の循環リスクでは `sccExcessSizeOfFinite = sccMaxSizeOfFinite - 1` を優先する。Lean では finite universe 下で `sccExcessSizeOfFinite` が graph-level mutual-reachability class size 最大値から 1 を引いた値と一致することを証明済みである。`weightedSccRiskOfFinite` は `weight : C -> Nat` を入力として、各 component の `weight c * (sccSizeAt G components c - 1)` を合計する executable metric である。重みの由来や calibration は empirical / extractor tooling 側に残し、Lean core では counting rule だけを扱う。

`fanoutRisk` は #11 の設計判断に従い `totalFanout` として残す。`maxFanoutOfFinite` は局所的な依存集中、`reachableConeSizeOfFinite` は変更波及の到達範囲を表す別軸として扱う。これらは v0 record を置き換えるのではなく、有限な測定 universe 上の v1 core 派生 metric として追加する。Lean では finite universe 下で `maxFanoutOfFinite` が source ごとの measured dependency edges 数の最大値と一致し、`reachableConeSizeOfFinite` が source 自身を除く graph-level reachable cone size の最大値と一致することを証明済みである。

`observationalDivergence` は measured pair ごとの観測差分を 0/1 で扱う。
`lspViolationCount` は、同じ抽象に写る実装 pair のうち観測値が異なるものを、
有限な実装 universe 上で数える behavioral extension である。Lean では
`ObservationFactorsThrough` / `LSPCompatible` から violation count 0 を得る
bridge を証明し、repository-level の重みづけや empirical calibration は tooling
側に残す。

Projection bridge と observation bridge は同じ `InterfaceProjection` を共有できるが、
保証する不変量は異なる。前者は具象依存が抽象依存へ sound に写ること、後者は観測が
抽象を通じて因子化することを扱う。実装置換の局所契約層では
`LocalReplacementContract G π GA O` として両者を束ねて読む。Lean ではこの bundle から
`projectionSoundnessViolation = 0` と `lspViolationCount = 0` を同時に得る
packaging theorem を証明済みである。集約や重みづけは empirical / extractor tooling 側へ残す。詳細は
[Observation bridge と projection bridge の関係](design/observation_projection_bridge.md)
に置く。

`nilpotencyIndex` と `rho(A)` は adjacency matrix bridge 軸である。`nilpotencyIndex` は finite `ComponentUniverse` 上で最初に `A^k = 0` となる power を探す executable extension axis として扱う。見つかった場合は `some k`、見つからない場合は `none` とし、未評価・非 DAG を risk 0 と混同しない。Lean では finite acyclic graph でこの axis が `some` になることを証明済みである。`rho(A)` は mathlib-backed な解析的拡張として分離し、finite acyclic graph では `rho(A)=0`、finite closed walk がある場合は `rho(A)>0` になることを証明済みである。変更コスト・障害伝播増幅との相関は後続の実証課題に残す。

adjacency matrix は、有限 `ComponentUniverse` 上の 0/1 行列として導入する。これは `Decomposable` の定義ではなく、`Walk` / DAG / nilpotence を接続する bridge layer である。`A^k` の entry を長さ `k` の walk 数として読む議論は、到達可能性を Hom にする thin `ComponentCategory` ではなく、長さと本数を保持する `Walk` 側で扱う。`rho(A)` は `Complex` 係数の mathlib `Matrix` へ持ち上げた解析的拡張であり、現時点では構造的 theorem と empirical claim を混同しない。

`runtimePropagation`, `relationComplexity`, `empiricalChangeCost` は static structural core の QED には含めない。`runtimePropagation` の初期 Lean metric は、0/1 `RuntimeDependencyGraph` 上の `runtimeExposureRadius` として `reachableConeSizeOfFinite` を再利用する。この 0/1 graph が与えられた後の zero metric と runtime obstruction absence の bridge は、将来の数学的コア拡張として Lean 証明対象にできる。一方、runtime edge metadata から 0/1 graph への projection rule、実コード extractor の完全性、incident scope / 障害修正コストとの相関は tooling / empirical protocol 側の課題として残す。既存名 `runtimePropagationRadius` / `runtimePropagation` は exposure 側の互換名であり、障害源から影響を受け得る範囲を測る `runtimeBlastRadius` は reverse reachability 由来の別 metric として分ける。Circuit Breaker coverage は raw `runtimePropagation` に混ぜず、未保護 edge から作る `unprotectedRuntimePropagationRadius` / `unprotectedRuntimeBlastRadius` と coverage ratio の policy-aware extension として分離する。`relationComplexity` の初期設計では、状態遷移代数層の `constraints`, `compensations`, `projections`, `failureTransitions`, `idempotencyRequirements` を構成要素として保持し、合計値は派生指標として扱う。

静的依存と実行時依存は、Lean core では `StaticDependencyGraph C := ArchGraph C` と `RuntimeDependencyGraph C := ArchGraph C` の role alias として分ける。`ArchitectureDependencyGraphs C` は `static` と `runtime` を同時に保持する薄い構造である。既存の `Walk` / `Reachable` / finite metrics はどちらの graph にも再利用できるが、`Decomposable`, Layered / Clean Architecture, boundary violation は静的依存側、Circuit Breaker や failure propagation は実行時依存側の軸として扱う。実行時 edge の label, weight, failure mode, timeout budget, retry policy, circuit breaker coverage は extractor / empirical tooling 側に残し、Lean の初期定義には混ぜない。

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

実コードベースから `Sig0` 入力を抽出する最小 tooling の対象範囲と
責務境界は、[ArchSig v0 設計](design/archsig_design.md)で扱う。
Signature と変更・レビュー・障害コストを結合する pilot study の protocol は
[Signature 実証プロトコル](design/empirical_protocol.md)で扱う。

この分担により、Lean で証明できる数学的事実と、現実データで反証可能な仮説を混同しない。
