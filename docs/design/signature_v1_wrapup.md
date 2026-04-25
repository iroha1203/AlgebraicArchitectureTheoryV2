# ArchitectureSignature v1 後半戦まとめ

このメモは Issue #83 の完了条件を整理するための wrap-up である。
Signature v1 は v0 の置き換えではなく、v0 の安定軸を内側に含む多軸診断として扱う。

## v1 schema の固定方針

Lean 側の出力 schema は、次の 2 層に分ける。

- `ArchitectureSignatureV1Core`: v0 signature と、Lean core で直接測定できる v1 派生軸を保持する。
- `ArchitectureSignatureV1`: core に加えて、未評価または tooling / empirical 側で埋める extension axis を `Option Nat` で保持する。

`Option Nat` の `none` は未評価を表し、risk 0 とは解釈しない。
この規約は extractor output の `metricStatus.measured = false` と同じ意味を持つ。

## 軸構成

| 軸 | Lean 側の扱い | Lean status |
| --- | --- | --- |
| v0 互換軸 | `ArchitectureSignature` として保持する | `defined only` / `proved` |
| `sccExcessSize` | `sccMaxSizeOfFinite - 1` として計算し、mutual-reachability class size 最大値との bridge を証明済み | `defined only` / `proved` |
| `maxFanout` | source ごとの measured dependency edges 数の最大値として計算する | `defined only` / `proved` |
| `reachableConeSize` | strict reachable cone size の最大値として計算する | `defined only` / `proved` |
| `weightedSccRisk` | 明示的な `weight : C -> Nat` が渡された場合だけ extension axis を埋める | `defined only` / `proved` |
| `projectionSoundnessViolation` | projection bridge の measured soundness violation count として扱い、exact projection とは分離する | `defined only` / `proved` |
| `lspViolationCount` | behavioral extension の measured pair count として扱う | `defined only` / `proved` |
| `nilpotencyIndex` | finite `ComponentUniverse` 上の matrix bridge entry point から埋める | `defined only` / `proved` |
| `runtimePropagation` | 0/1 `RuntimeDependencyGraph` 上の propagation radius として計算する | `defined only` / `empirical hypothesis` |
| `relationComplexity` | workflow observation から作る empirical extension として扱う | `empirical hypothesis` |
| `empiricalChangeCost` | 実データ検証の目的変数として扱う | `empirical hypothesis` |

## 子 Issue の反映

| Issue | 決定内容 | 反映先 |
| --- | --- | --- |
| #87 | `ArchitectureSignatureV1Core` / `ArchitectureSignatureV1` の 2 層 schema に固定する | `Formal/Arch/Signature.lean`, `docs/proof_obligations.md`, `docs/aat_v2_overview.md` |
| #84 | `weightedSccRisk` は component weight を入力にした SCC excess contribution の合計とする | `Formal/Arch/Signature.lean`, `docs/proof_obligations.md`, `docs/aat_v2_overview.md` |
| #85 | `nilpotencyIndex` は matrix bridge 由来の optional extension axis とし、`rho(A)` とは分離する | `Formal/Arch/Matrix.lean`, `docs/proof_obligations.md`, `docs/aat_v2_overview.md` |
| #86 | `runtimePropagation` は初期 metric を `runtimePropagationRadius` に固定し、runtime metadata は tooling 側に残す | `Formal/Arch/Signature.lean`, `docs/design/runtime_propagation_design.md`, `docs/proof_obligations.md` |

## 残る境界

次の主張は Signature v1 schema には場所を持つが、Lean core の全称定理としてはまだ扱わない。

- `rho(A)` のうち `DAG -> rho(A)=0` と cycle positivity は spectral bridge
  で証明済みだが、empirical cost interpretation は後続課題とする。
- `projectionSoundnessViolation` は soundness-only metric であり、`ProjectionComplete`
  の欠如や exact projection gap は別 refinement として扱う。
- runtime edge metadata, timeout budget, retry policy, circuit breaker coverage は extractor / empirical tooling 側に残す。
- `relationComplexity` と `empiricalChangeCost` は実証プロトコル上の観測・目的変数として扱う。

これにより、v1 は「測定済みの 0」と「未評価」を混同せず、Lean proof と empirical validation の責務境界を保ったまま拡張できる。
