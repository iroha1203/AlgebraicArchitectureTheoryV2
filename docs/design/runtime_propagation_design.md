# runtimePropagation 設計

`runtimePropagation` は Signature v1 の empirical extension 軸であり、実行時依存と
障害伝播の広がりを表す。静的な import / type reference から作る構造軸とは分け、
`RuntimeDependencyGraph` 上の 0/1 edge と、extractor が保持する runtime metadata
の二層で扱う。

## 最小 metric

初期 Lean metric は `runtimePropagationRadius` とする。計算規則は
`RuntimeDependencyGraph` 上の
`ArchitectureSignature.runtimePropagationOfFinite G components` であり、既存の
`reachableConeSizeOfFinite G components` を再利用する。

この値は、測定 universe 内で、ある component から runtime edge に沿って到達できる
異なる component 数の最大値である。辺の向きは既存 convention と同じく
`edge c d` means `c depends on d` で読む。runtime graph では、これは `c` の実行時
呼び出しや通信が依存する相手へどれだけ広がるかを表す。

`runtimeFanout` は同じ 0/1 runtime graph 上で `maxFanoutOfFinite` を再利用できるが、
最初の `ArchitectureSignatureV1.runtimePropagation` entry point には入れない。
`runtimeFanout` は局所集中、`runtimePropagationRadius` は到達範囲を測る別軸候補として
残す。

## Signature への埋め込み

Lean 側では
`ArchitectureSignature.v1OfFiniteWithRuntimePropagation static runtime components ...`
を runtime 軸の entry point とする。

- v1 core は `static : StaticDependencyGraph C` から計算する。
- `runtimePropagation` は `runtime : RuntimeDependencyGraph C` から
  `some (runtimePropagationOfFinite runtime components)` として埋める。
- runtime graph が未抽出の場合は既存の `v1OfFinite` を使い、`runtimePropagation = none`
  のままにする。

`none` は未評価を意味し、runtime risk 0 ではない。`some 0` は、測定済みの runtime
graph において runtime edge の到達範囲が空であることを表す。

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

`sig0-extractor` の `runtime-edge-projection-v0` はこの初期規則を実装する。
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
- `unprotectedRuntimePropagationRadius` は `unprotectedRuntimeGraph` 上の
  reachable cone size として計算する。これは raw `runtimePropagation` を置き換えず、
  Circuit Breaker policy を反映した別 extension axis として読む。

Lean 側で証明済みまたは定義済みと言えるのは、0/1 graph を渡したときの
`runtimePropagationOfFinite` の graph-level な計算規則までである。Circuit Breaker
coverage が実際の障害範囲、修正時間、incident count を下げるという主張は
empirical hypothesis であり、pilot dataset と empirical protocol 側で検証する。

## Lean status

- `runtimePropagationOfFinite`: `defined only`
- `v1OfFiniteWithRuntimePropagation`: `defined only`
- runtime edge metadata から 0/1 graph への projection rule:
  `runtime-edge-projection-v0` tooling implementation / `empirical hypothesis`
- `unprotectedRuntimePropagationRadius`, `circuitBreakerCoverageRatio`:
  policy-aware extension design / `empirical hypothesis`
- Circuit Breaker coverage が障害修正コストや障害範囲を下げる主張:
  `empirical hypothesis`
