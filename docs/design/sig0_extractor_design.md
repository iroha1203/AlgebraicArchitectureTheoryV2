# Sig0 extractor v0 設計

Lean status: `empirical hypothesis` / tooling design.

この文書は Issue [#34](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/34)
の設計メモである。目的は、実コードベースから `ArchitectureSignature`
v0 の入力になる静的依存グラフと有限な測定 universe を抽出する最小
tooling の責務を固定することである。

ここでいう extractor は Lean の `ComponentUniverse` を生成する証明器ではない。
extractor は現実コードベースから測定用データを作る外部 tooling であり、Lean
側の `ComponentUniverse` は proof-carrying measurement universe として残す。
抽出規則の完全性や実コードベースとの一致は Lean theorem ではなく、検査可能な
実装仕様と実証研究の対象として扱う。

## v0 の対象範囲

最初の対象は Lean repository とする。理由は、既存の `lakefile.toml`,
`lean-toolchain`, `Formal.lean`, `Formal/Arch` の import 構造を使って、
実コード抽出と Lean 側の責務境界を同じ repository 内で検査できるからである。

component 粒度は file/module とする。

- component id は Lean module 名、または repository root からの相対 file path
  に正規化する。
- package 粒度は v0 では粗すぎるため対象外にする。
- declaration 粒度は import graph だけでは安定して取れないため v0 では扱わない。
- `Main.lean`, `Formal.lean`, `Formal/Arch/*.lean` は測定対象にできるが、docs や
  workflow は静的依存グラフの component には含めない。

最小 extractor の入力は repository checkout である。初期実装では、Lean toolchain
や lake build artifact に依存せず、source file と import 文から静的依存辺を抽出する。

## 入出力形式

v0 tooling は JSON Lines ではなく、差分レビューしやすい単一 JSON document を出力する。
schema は明示的に versioned にする。

```json
{
  "schemaVersion": "sig0-extractor-v0",
  "root": ".",
  "componentKind": "lean-module",
  "components": [
    {
      "id": "Formal.Arch.Signature",
      "path": "Formal/Arch/Signature.lean"
    }
  ],
  "edges": [
    {
      "source": "Formal.Arch.Finite",
      "target": "Formal.Arch.Signature",
      "kind": "import",
      "evidence": "import Formal.Arch.Signature"
    }
  ],
  "policies": {
    "boundaryAllowed": [],
    "abstractionAllowed": []
  },
  "signature": {
    "hasCycle": 0,
    "sccMaxSize": 1,
    "maxDepth": 0,
    "fanoutRisk": 0,
    "boundaryViolationCount": 0,
    "abstractionViolationCount": 0
  },
  "metricStatus": {
    "boundaryViolationCount": {
      "measured": false,
      "reason": "policy file not provided"
    },
    "abstractionViolationCount": {
      "measured": false,
      "reason": "policy file not provided"
    }
  }
}
```

edge の向きは `source` が依存元、`target` が依存先である。たとえば
`Formal.Arch.Finite` が `Formal.Arch.Signature` を import する場合、
`Formal.Arch.Finite -> Formal.Arch.Signature` と記録する。この向きは
`ArchGraph.edge source target` と合わせる。

`policies.boundaryAllowed` と `policies.abstractionAllowed` は v0 では空でもよい。
ポリシーが未定義の場合、Lean の `ArchitectureSignature` へ渡す placeholder として
対応する violation count に 0 を入れてもよいが、empirical dataset では
`metricStatus` に `measured: false` と理由を必ず記録し、違反なしとは解釈しない。
分析側では `measured: false` の軸を欠損値として扱う。将来の v1 core では、層や
境界の設定 file から policy を読む。

### `metricStatus` の最小 schema

`metricStatus` は、`signature` の各軸について、その値が実測値か placeholder かを
区別する metadata である。`signature` は Lean の `ArchitectureSignature` や既存の
集計表へ渡すために `Nat` 値を保持するが、値の解釈は `metricStatus` と合わせて行う。

各 metric status entry は次を持つ。

| field | 型 | 必須 | 意味 |
| --- | --- | --- | --- |
| `measured` | boolean | yes | true なら extractor が当該軸を測定した。false なら値は欠損扱いである。 |
| `reason` | string | false の場合 yes | 未評価の理由。例: `policy file not provided`, `rule set not implemented`。 |
| `source` | string | no | 測定に使った policy file, rule set, algorithm version など。 |

規約は次の通り。

- `measured: true` の軸では、`signature` の値を観測値として扱う。
- `measured: false` の軸では、`signature` の値が 0 でも「違反なし」と読まない。
- policy 未指定の `boundaryViolationCount` / `abstractionViolationCount` は、
  Lean input 用の placeholder として `signature` に 0 を置き、
  `metricStatus` には `measured: false` と理由を置く。
- `metricStatus` に entry がない軸は、後方互換のため `measured: true` と推定せず、
  schema violation または legacy data として明示的に扱う。

boundary / abstraction policy が未指定の場合の最小例:

```json
{
  "policies": {
    "boundaryAllowed": [],
    "abstractionAllowed": []
  },
  "signature": {
    "boundaryViolationCount": 0,
    "abstractionViolationCount": 0
  },
  "metricStatus": {
    "boundaryViolationCount": {
      "measured": false,
      "reason": "policy file not provided"
    },
    "abstractionViolationCount": {
      "measured": false,
      "reason": "policy file not provided"
    }
  }
}
```

## v0 signature の抽出軸

最小 extractor が計算する軸は、現行 `ArchitectureSignature` v0 に対応する 6 軸に限る。

| 軸 | v0 tooling での扱い | Lean status |
| --- | --- | --- |
| `hasCycle` | import graph の SCC から 0/1 risk として計算する | `empirical hypothesis` / tooling output |
| `sccMaxSize` | import graph の最大 SCC サイズとして計算する | `empirical hypothesis` / tooling output |
| `maxDepth` | finite source graph 上の fuel-bounded depth として計算する | `empirical hypothesis` / tooling output |
| `fanoutRisk` | `totalFanout` として計算する。Lean v0 の fanout field へ写す正式な extractor 側名称として扱う。 | `empirical hypothesis` / tooling output |
| `boundaryViolationCount` | policy 未指定なら placeholder 0 と `measured: false` metadata を出す | `empirical hypothesis` / tooling output |
| `abstractionViolationCount` | policy 未指定なら placeholder 0 と `measured: false` metadata を出す | `empirical hypothesis` / tooling output |

`fanoutRisk` は #11 の設計判断に従い `totalFanout` として扱う。古い docs や Lean API に
`averageFanout` 由来の名前が残る場合でも、extractor v0 の出力では `fanoutRisk` を
正規の列名にし、必要なら Lean 側 field との mapping を adapter で明示する。

`nilpotencyIndex`, `rho(A)`, `runtimePropagation`, `relationComplexity`,
`empiricalChangeCost` は v0 extractor の対象外である。これらは matrix bridge、
runtime dependency extraction、state transition algebra、実証プロトコルの後続課題に
分離する。

Lean import graph は extractor 開発と責務境界の検査には適しているが、通常は循環
import を許さないため、cycle / SCC risk の empirical validation には検出力が低い。
H2 系の実証では、将来 non-Lean repository、runtime dependency graph、または
synthetic fixture を追加する。

## Lean との責務境界

責務境界は次で固定する。

- extractor 側: source files を読み、component list, dependency edges, evidence,
  optional policy evaluation, executable signature values を出力する。
- Lean 側: `ArchGraph`, `ArchitectureSignature`, `ComponentUniverse`,
  `FiniteArchGraph` について、明示された有限 universe 上で言える構造的事実を証明する。
- docs / empirical 側: extractor output と変更コスト、レビューコスト、障害修正コスト
  との関係を仮説として検証する。

extractor output を Lean の `ComponentUniverse` として扱うには、少なくとも
duplicate-free component list, edge closure, coverage などの証明または検査済み証跡が
別途必要である。v0 tooling はこの証明を生成しない。したがって、extractor が
`ComponentUniverse` の完全な witness を作ったとは主張しない。

## 後続 Issue への分割

この設計から、後続実装は次の単位に分けられる。

- Lean module import graph を抽出し、component / edge JSON を出力する CLI を作る。
- JSON output から `hasCycle`, `sccMaxSize`, `maxDepth`, `fanoutRisk` を計算する。
- boundary / abstraction policy file の最小 schema を設計し、violation count を出す。
- extractor output と `ComponentUniverse` の責務境界を検査する validation report を出す。
- 複数 repository に対する signature 時系列と PR metadata を結合する実証 protocol を作る。

これらは Lean proof の進行をブロックしない。tooling の正確性は、golden fixture,
snapshot test, 実コード上の再現性で確認し、Lean theorem としては主張しない。
