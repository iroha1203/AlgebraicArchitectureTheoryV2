# runtimePropagation 設計

`runtimePropagation` は Signature v1 の empirical extension 軸であり、実行時依存と
障害伝播の広がりを表す。静的な import / type reference から作る構造軸とは分け、
`RuntimeDependencyGraph` 上の 0/1 edge と、extractor が保持する runtime metadata
の二層で扱う。

## 最小 metric

初期 Lean metric は `runtimeExposureRadius` とする。既存の
`runtimePropagationRadius` / `runtimePropagation` は互換名として残すが、意味は
exposure radius に固定する。計算規則は
`RuntimeDependencyGraph` 上の
`ArchitectureSignature.runtimePropagationOfFinite G components` であり、既存の
`reachableConeSizeOfFinite G components` を再利用する。

この値は、測定 universe 内で、ある component から runtime edge に沿って到達できる
異なる component 数の最大値である。辺の向きは既存 convention と同じく
`edge c d` means `c depends on d` で読む。runtime graph では、これは `c` の実行時
呼び出しや通信が依存する相手へどれだけ広がるかを表す。したがって、この軸は
「障害源 `d` が壊れたときに `d` に依存する component がどれだけ影響を受けるか」
という blast radius ではない。

H5 の incident scope 解釈では、runtime 到達方向を次の 2 つに分ける。

- `runtimeExposureRadius`: `edge c d` の向きに沿う到達範囲。component `c` が直接・間接に
  依存する runtime resource / service の広がりを測る。Lean 側の
  `runtimePropagationOfFinite` と `ArchitectureSignatureV1.runtimePropagation` はこの値を
  埋める。
- `runtimeBlastRadius`: runtime edge を逆向きに読んだ到達範囲。component `d` が障害源に
  なったとき、直接・間接に `d` へ依存して影響を受け得る component の広がりを測る。
  `ArchGraph.reverse` は concrete graph operation kernel として Lean core にあるが、
  v0 の `ArchitectureSignatureV1.runtimePropagation` には blast radius field を追加しない。
  blast radius は reverse runtime graph または incoming reachability 由来の別 metric として
  dataset / analysis metadata 側で扱う。

この決定により、既存の `runtimePropagation` は legacy alias として
`runtimeExposureRadius` を指す。blast radius を分析したい場合は
`runtimeBlastRadius` を別 metric として dataset / analysis metadata に保持し、
`runtimePropagation` を blast radius と読み替えない。

`runtimeFanout` は同じ 0/1 runtime graph 上で `maxFanoutOfFinite` を再利用できるが、
最初の `ArchitectureSignatureV1.runtimePropagation` entry point には入れない。
`runtimeFanout` は局所集中、`runtimeExposureRadius` は outgoing exposure、
`runtimeBlastRadius` は incoming failure impact を測る別軸候補として残す。
Issue #126 では、`runtimeFanout` を v1 extension axis へ追加せず、実証分析用の
派生値として dataset / analysis metadata 側に保持する方針に固定した。

## Signature への埋め込み

Lean 側では
`ArchitectureSignature.v1OfFiniteWithRuntimePropagation static runtime components ...`
を runtime 軸の entry point とする。

- v1 core は `static : StaticDependencyGraph C` から計算する。
- `runtimePropagation` は legacy alias として `runtimeExposureRadius` を表し、
  `runtime : RuntimeDependencyGraph C` から
  `some (runtimePropagationOfFinite runtime components)` として埋める。
- `runtimeBlastRadius` は `ArchitectureSignatureV1` の field には追加しない。必要な場合は
  empirical dataset の `analysisMetadata.runtimeMetrics` に、reverse runtime graph 由来の
  派生 metric として保存する。
- runtime graph が未抽出の場合は既存の `v1OfFinite` を使い、`runtimePropagation = none`
  のままにする。

`none` は未評価を意味し、runtime risk 0 ではない。`some 0` は、測定済みの runtime
graph において、測定 universe 内の `source != target` な runtime reachable cone が
空であることを表す。これは単に「runtime edge がない」と読むより弱く、自己辺や
測定 universe 外の runtime evidence とは区別する。

## Lean proof roadmap

runtime metrics のうち、数学的コアとして Lean 証明を狙う範囲は、0/1
`RuntimeDependencyGraph` が既に与えられている場合の zero metric bridge である。
実コード extractor が完全な runtime graph を生成することや、runtime 指標が incident
scope / repair cost を説明することは、この theorem の外に置く。

Issue #237 で証明した最初の bridge は次である。

```text
runtimePropagationOfFinite runtime components = 0
  <-> NoRuntimeExposureObstruction runtime components
```

`NoRuntimeExposureObstruction` は、まず executable metric と同じ
`reachesWithin runtime components components.length` ベースの measured / bounded
obstruction として定義する。obstruction witness は
`source ∈ components`, `target ∈ components`, `source != target` と、
bounded search が到達を検出したことを持つ `(source, target)` pair にする。

semantic `Reachable runtime source target` ベースの obstruction として述べたい場合は、
`ComponentUniverse` coverage / edge-closure の下で `reachesWithin` と `Reachable` を
接続する bridge theorem を別途使う。既存の finite bridge と同様に、executable
metric の zero theorem と semantic graph theorem を同一視しない。

Circuit Breaker など policy-aware な指標は、raw graph の theorem を置き換えず、
別入力の graph に対する同型の theorem として追加する。

```text
unprotectedRuntimeExposureRadius unprotectedRuntimeGraph components = 0
  <-> NoUnprotectedRuntimeExposureObstruction unprotectedRuntimeGraph components
```

blast radius は runtime edge を逆向きに読んだ派生値であるため、Lean 化する場合は
extractor の暗黙処理ではなく、edge reversal function または reverse runtime graph を
明示的な入力にする。その場合の theorem も、reverse graph 上の reachable cone zero
bridge として扱う。

この runtime theorem package は、static structural core の QED に直接混ぜない。
まず `ArchitectureRuntimeZeroCurvaturePackage` のような独立 package として、
runtime obstruction / runtime metric zero bridge を育てる。

## required-law 境界

static structural core の QED では、runtime / empirical 系の軸を selected required law
axis へ追加しない。Lean 側の full law universe policy では `runtimePropagation` は
`diagnosticAxis`、`relationComplexity` と `empiricalChangeCost` は `empiricalAxis`
である。runtime metrics の zero bridge は、将来の数学的コア拡張として
static package とは別に扱う。したがって、`ArchitectureLawful` や
`RequiredSignatureAxesZero` の成立条件として `runtimePropagation = some 0` を
要求しない。

境界は次のように読む。

| 対象 | zero-curvature theorem での分類 | Lean status |
| --- | --- | --- |
| `runtimePropagation` / `runtimeExposureRadius` | 0/1 `RuntimeDependencyGraph` 上で測定できる diagnostic axis。static required zero-law axis ではない。zero metric と runtime obstruction absence の bridge は future proof obligation | `defined only` / `future proof obligation` |
| `runtimeBlastRadius` | reverse reachability 由来の tooling / analysis metric。Lean core field には入れない | `empirical hypothesis` |
| `runtimeFanout` | runtime graph 上の局所集中を測る analysis-derived metric。v1 field には追加しない | `empirical hypothesis` |
| `circuitBreakerCoverageRatio` | measured runtime pair に対する policy-aware coverage 指標 | `empirical hypothesis` |
| `unprotectedRuntimeExposureRadius`, `unprotectedRuntimeBlastRadius` | coverage policy を反映した派生 runtime metric | `empirical hypothesis` |
| incident scope / repair time / hotfix size との関係 | H5 empirical protocol で検証する反証可能な仮説 | `empirical hypothesis` |

この分類により、runtime graph が未抽出で `runtimePropagation = none` の場合でも、
selected required law theorem の証明義務は増えない。runtime evidence がある場合は
diagnostic として `some n` を記録できるが、`some 0` は「測定済み 0」であって
全体 lawfulness の追加条件ではない。

## Extractor 境界

extractor / empirical tooling 側は、次の情報を保持する。

- runtime edge の抽出根拠: RPC, queue publish / subscribe, shared database,
  external SaaS, distributed transaction, timeout propagation など。
- edge metadata: label, weight, failure mode, timeout budget, retry policy,
  circuit breaker coverage, confidence, evidence location。
- metadata から 0/1 `RuntimeDependencyGraph` へ落とす projection rule。

Lean core に渡す 0/1 projection の初期規則は、実行時通信または共有 runtime resource
への依存を示す evidence が 1 件以上ある component pair を edge として立てることにする。
metadata の重み、failure mode、timeout budget、retry policy はこの 0/1 edge の存在へは
畳み込むが、Lean theorem の前提にはしない。

ArchSig の `runtime-edge-projection-v0` はこの初期規則を実装する。
`--runtime-edges` に `runtime-edge-evidence-v0` JSON を渡すと、raw metadata を
`runtimeEdgeEvidence` に保存し、unique component pair ごとに `kind = "runtime"` の
edge を `runtimeDependencyGraph.edges` へ出力する。runtime evidence 入力がない場合は
`runtimeDependencyGraph` 自体を省略し、dataset 側の `runtimePropagation` は未評価の
`null` として扱う。入力済み graph の edge が空であることと未抽出は区別する。

## Circuit Breaker coverage の扱い

Circuit Breaker coverage は初期 `runtimePropagationRadius` には直接混ぜない。
`runtimePropagationOfFinite` は、測定済み 0/1 `RuntimeDependencyGraph` 上の到達範囲を
そのまま返す raw metric として固定する。Circuit Breaker による障害伝播低減は、
extractor / empirical tooling 側で作る policy-aware extension として扱う。

v0 の policy-aware metric では、runtime edge pair を次の状態に正規化する。

- `protected`: 対象 failure mode に対して Circuit Breaker, timeout fail-fast,
  fallback, bulkhead などの遮断 policy が evidence として確認できる。
- `unprotected`: 対象 failure mode に対する遮断 policy がない、または明示的に無効である。
- `partial`: edge の一部の failure mode または一部の呼び出し経路だけが保護されている。
- `unknown`: metadata が不足して coverage を判定できない。

raw `runtimeDependencyGraph` は、coverage の有無にかかわらず runtime evidence がある
component pair をすべて含める。policy-aware 評価では、この raw graph とは別に
`unprotectedRuntimeGraph` を投影する。保守的な v0 規則では、`unprotected`, `partial`,
`unknown` の evidence を持つ pair を未保護 edge として残し、`protected` と判定できる
pair だけを除外する。`unknown` を 0 risk に丸めないため、未評価 coverage は未保護側へ
倒す。

counting rule は次の 2 つに分ける。

- `circuitBreakerCoverageRatio = protectedPairCount / measuredRuntimePairCount`。
  分母は coverage 判定が走った runtime pair 数であり、runtime graph 未抽出の場合は
  metric 全体を未評価にする。
- `unprotectedRuntimeExposureRadius` は `unprotectedRuntimeGraph` 上の
  reachable cone size として計算する。これは raw `runtimePropagation` を置き換えず、
  Circuit Breaker policy を反映した別 extension axis として読む。既存名
  `unprotectedRuntimePropagationRadius` は exposure 側の互換名として扱う。
- `unprotectedRuntimeBlastRadius` は同じ未保護 graph を逆向きに読んだ到達範囲として
  tooling / analysis 側で派生させる。policy-aware H5 で incident scope を説明する場合は、
  root cause component が分かる範囲で blast 側を優先する。

Lean 側で証明済みまたは定義済みと言えるのは、0/1 graph を渡したときの
`runtimePropagationOfFinite` の graph-level な計算規則までである。Circuit Breaker
coverage が実際の障害範囲、修正時間、incident count を下げるという主張は
empirical hypothesis であり、pilot dataset と empirical protocol 側で検証する。

## 実証プロトコルへの接続

Issue #126 では、`runtimeFanout` / `runtimePropagationRadius` と incident / repair cost
の関係を Lean theorem ではなく empirical hypothesis として検証する protocol に固定した。
Issue #163 では、この `runtimePropagationRadius` を exposure radius として読み、
incident scope には reverse reachability 由来の blast radius を分けて使う設計に更新した。
詳細は [Signature 実証プロトコル](empirical_protocol.md) の H5 に置く。

protocol 上の説明変数は次の種類に分ける。

- `runtimePropagation` / `runtimeExposureRadius`: raw 0/1 `RuntimeDependencyGraph` 上の
  outgoing exposure radius。
- `runtimeBlastRadius`: raw 0/1 `RuntimeDependencyGraph` を逆向きに読んだ incoming
  blast radius。
- `runtimeFanout`: 同じ runtime graph 上の局所集中を測る分析用派生値。
- `unprotectedRuntimeExposureRadius` / `unprotectedRuntimePropagationRadius`:
  Circuit Breaker coverage を反映した exposure 側の policy-aware extension。
- `unprotectedRuntimeBlastRadius`: Circuit Breaker coverage を反映した blast 側の
  policy-aware extension。
- `circuitBreakerCoverageRatio`: 測定済み runtime pair に対する protected pair の比率。

目的変数は incident scope, repair time, rollback, hotfix size とする。観測窓は
30 / 90 / 180 日を標準にし、repository size, team size, incident severity,
deployment frequency, extractor version, policy version を交絡要因として残す。
incident の root cause component が特定できる場合は blast radius を incident scope の
主説明変数候補にし、affected component 側の外部依存 exposure を調べる場合は
exposure radius を使う。root cause が不明な場合は、affected component ごとの
exposure / blast の最大値と欠損理由を分けて記録する。

欠損値規約は raw metric と policy-aware metric で共通して、未抽出を risk 0 として
扱わない。runtime evidence が未指定なら `runtimePropagation = none` / dataset 側
`null` とする。runtime evidence 入力済みで edge set が空なら測定済みの `some 0` に
なるが、`some 0` の意味は edge set empty に限らず、測定 universe 内の
`source != target` な runtime reachable cone が空であることである。
coverage metadata が不足している edge は `unknown` として扱い、policy-aware v0 では
保守的に `unprotectedRuntimeGraph` 側に残す。

## Lean status

- `runtimePropagationOfFinite`: exposure radius として `defined only`
- `v1OfFiniteWithRuntimePropagation`: `defined only`
- `NoRuntimeExposureObstruction`: measured / bounded obstruction predicate として `defined only`
- `NoSemanticRuntimeExposureObstruction`: `Reachable` ベースの semantic obstruction predicate として `defined only`
- `runtimePropagationOfFinite_eq_zero_iff_noRuntimeExposureObstruction`: `proved`
- `noRuntimeExposureObstruction_iff_noSemanticRuntimeExposureObstruction_under_universe`: `proved`
- `runtimePropagationOfFinite_eq_zero_iff_noSemanticRuntimeExposureObstruction_under_universe`: `proved`
- `v1OfFiniteWithRuntimePropagation_runtimePropagation_eq_some_zero_iff_noSemanticRuntimeExposureObstruction_under_universe`: `proved`
- `runtimeBlastRadius`: tooling / analysis-derived metric / `empirical hypothesis`
- runtime edge metadata から 0/1 graph への projection rule:
  `runtime-edge-projection-v0` tooling implementation / `empirical hypothesis`
- `unprotectedRuntimeExposureRadius`, `unprotectedRuntimeBlastRadius`,
  `circuitBreakerCoverageRatio`:
  policy-aware extension design / `empirical hypothesis`
- `runtimeFanout` と incident / repair cost の関係:
  analysis-derived metric / `empirical hypothesis`
- Circuit Breaker coverage が障害修正コストや障害範囲を下げる主張:
  `empirical hypothesis`
