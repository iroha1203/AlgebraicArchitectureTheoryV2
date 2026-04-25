# Signature 実証プロトコル

Lean status: `empirical hypothesis` / protocol design.

この文書は Issue [#35](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/35)
の設計メモである。目的は、`ArchitectureSignature` と変更波及、レビューコスト、
障害修正コストの関係を検証するための最初の pilot study を開始できる状態にすることである。

ここで扱う関係は Lean theorem ではない。Lean は有限 universe 上の graph-level
facts を証明し、現実コードベース上の品質・コストとの関係は反証可能な empirical
hypothesis として扱う。

## 対象範囲

最初の pilot study では、測定対象を次のように絞る。

| 項目 | 初期設定 |
| --- | --- |
| repository | 1 から 3 個の GitHub repository |
| 期間 | 直近 6 から 12 か月 |
| component 粒度 | file / module |
| signature 粒度 | PR merge commit の before / after |
| コスト粒度 | PR, issue, incident 単位 |
| 除外対象 | bot-only PR, vendored code, generated code, formatting-only PR |

pilot では完全な一般化を目標にしない。抽出規則と分析手順を固定し、再現可能な
小規模データセットを作ることを優先する。

## 検証する仮説

初期 protocol では、仮説を次の 4 個に絞る。

| ID | 仮説 | 主な説明変数 | 主な目的変数 |
| --- | --- | --- | --- |
| H1 | Signature の悪化は変更波及の増加と相関する。 | `deltaSignatureSigned`, `reachableConeSize`, `maxDepth` | changed files, changed components |
| H2 | SCC / cycle risk が大きい領域では障害修正コストが増える。 | `hasCycle`, `sccMaxSize`, `sccExcessSize` | issue close time, hotfix size, rollback |
| H3 | fanout risk が高い変更はレビューコストが増える。 | `fanoutRisk`, `maxFanout` | review comments, review rounds, approval time |
| H4 | 境界違反と relation complexity は将来の変更・運用リスクと相関する。 | `boundaryViolationCount`, `relationComplexity` | future co-change, incident count, repair time |

`relationComplexity` は [relationComplexity 設計](relation_complexity_design.md)
に従い、構成要素ベクトルと派生合計値を分けて記録する。単一スコアだけで設計の
良し悪しを判断しない。

## 必要データ

### PR データ

PR ごとに次を記録する。

- PR number, author, created / merged timestamp
- base commit, head commit, merge commit
- changed files, changed lines, changed components
- review comment count, review thread count, review round count
- first review time, approval time, merge time
- labels, linked issue, linked incident
- bot-generated かどうか

### Issue / incident データ

issue または incident ごとに次を記録する。

- issue / incident id
- opened / closed timestamp
- severity, label, affected component
- linked PR / hotfix PR
- rollback の有無
- reopen の有無
- repair scope: changed files, changed components

### Signature データ

PR または分析対象 commit ごとに次を記録する。

- `signatureBefore`
- `signatureAfter`
- `deltaSignatureSigned : SignatureIntVector`, where each component is
  `signatureAfter - signatureBefore` over `Int`
- optional `riskIncrease` / `riskDecrease` vectors derived from the signed delta
- component-level signature contribution
- extractor version, rule set version, policy version
- 未評価軸とその理由

PR metadata と Signature before / after を結合した dataset record の最小 schema は
[empirical dataset v0 schema](empirical_dataset_schema.md) に分離する。この protocol
では分析手順を扱い、dataset schema 文書では列名、欠損値、比較可能性の規約を固定する。

`signatureBefore` は PR base commit、`signatureAfter` は PR head または merge commit
で計算する。merge commit の有無で結果が変わる場合は、その差分を metadata に残す。
`deltaSignatureSigned` は `Nat` subtraction ではなく符号付き差分として扱う。
改善による負の差分を 0 に丸めない。

#### SignatureIntVector と signed delta

Lean 側の `ArchitectureSignature` v0 は各軸を `Nat` として保持する。一方、
empirical dataset では差分を改善・悪化の両方向で扱うため、同じ軸集合を
`Int` に写した `SignatureIntVector` を使う。

最小 schema:

```text
SignatureIntVector =
  hasCycle: Int
  sccMaxSize: Int
  maxDepth: Int
  fanoutRisk: Int
  boundaryViolationCount: Int
  abstractionViolationCount: Int
```

変換規約:

- `ArchitectureSignature` から `SignatureIntVector` への変換は、各 `Nat` 軸を
  同名の `Int` 軸へ埋め込むだけであり、正規化や重みづけを行わない。
- `deltaSignatureSigned = signatureAfterInt - signatureBeforeInt` と定義する。
- 正の値は risk の増加、負の値は risk の減少、0 は当該軸の変化なしを表す。
- `hasCycle` は `0` または `1` の risk indicator として扱うため、
  `-1`, `0`, `1` の delta だけを持つ。
- before / after のどちらかで `metricStatus.<axis>.measured = false` の軸は、
  `deltaSignatureSigned.<axis>` を欠損値として扱い、0 に丸めない。

`riskIncrease` と `riskDecrease` は保存必須の一次データではなく、
`deltaSignatureSigned` から作る派生値として扱う。

```text
riskIncrease.axis = max(deltaSignatureSigned.axis, 0)
riskDecrease.axis = max(-deltaSignatureSigned.axis, 0)
```

この派生により、改善分を失わずに、悪化方向だけを見る分析と改善方向だけを見る
分析を同じ signed delta から再現できる。保存する場合も、source of truth は
`signatureBefore`, `signatureAfter`, `metricStatus`, `deltaSignatureSigned` とする。

component-level signature contribution は、PR 内の changed component ごとに
`SignatureIntVector` と同じ軸集合で記録する補助データである。PR-level delta は
repository 全体の before / after signature 差分であり、component-level contribution
の単純和と一致することは要求しない。SCC や reachability のような大域軸では、
1 つの component の変更が複数 component の risk を同時に変えるためである。
component-level contribution は原因候補の説明や感度分析に使い、H1 から H4 の
主要分析では PR-level `deltaSignatureSigned` を使う。

#### 未評価 metric と欠損値

extractor output は、Lean 側の `ArchitectureSignature` に合わせるため
`signature` の各軸を `Nat` 値として出す。一方、empirical dataset では
`metricStatus` を必ず保持し、0 と未評価を分離する。

最小 schema:

| field | 型 | 意味 |
| --- | --- | --- |
| `metricStatus.<axis>.measured` | boolean | 当該軸を extractor が測定したか。 |
| `metricStatus.<axis>.reason` | string | `measured: false` の理由。 |
| `metricStatus.<axis>.source` | string, optional | policy file, rule set, extractor algorithm などの測定根拠。 |

分析方針:

- `measured: false` の軸は欠損値として扱い、違反なしやリスク 0 として集計しない。
- `deltaSignatureSigned` は、before / after の両方で `measured: true` の軸だけを
  主要分析に使う。
- before / after の片側だけが未評価の場合、その軸の delta は欠損値として扱い、
  欠損理由を sensitivity analysis 用 metadata に残す。
- policy 未指定で `boundaryViolationCount = 0` または
  `abstractionViolationCount = 0` が出ている場合、その 0 は Lean input 用
  placeholder であり、H4 の境界違反分析には入れない。
- 欠損率が仮説ごとの分析対象の大半を占める場合、その仮説は pilot では
  exploratory analysis として報告する。

boundary / abstraction policy 未指定時の記録例:

```json
{
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

## 測定方法

### H1: Signature と変更波及

必要データ:

- PR の changed files / changed components
- PR 前後の `deltaSignatureSigned`
- 変更された component からの `reachableConeSize`

測定方法:

- PR ごとに before / after signature を計算する。
- 変更 component から到達できる component 数を測る。
- `deltaSignatureSigned` と変更範囲の順位相関を見る。

除外条件:

- formatting-only PR
- dependency lockfile だけの更新
- repository 全体の機械的 rename

### H2: SCC / cycle risk と障害修正

必要データ:

- issue / incident の open から close までの時間
- hotfix PR の changed files / changed components
- affected component 周辺の `hasCycle`, `sccMaxSize`, `sccExcessSize`

測定方法:

- incident 発生時点に近い commit の signature を使う。
- affected component が属する SCC と global SCC risk を分けて記録する。
- repair time と hotfix scope の分布を cycle risk の有無で比較する。

除外条件:

- 外部サービス障害だけでコード修正がない incident
- duplicate issue
- severity や affected component が記録されていない issue

### H3: fanout とレビューコスト

必要データ:

- PR の review comment count
- review round count
- approval time
- 変更 component の `fanoutRisk`, `maxFanout`

測定方法:

- PR 単位でレビューコストを集計する。
- 変更 component 周辺の fanout 指標とレビューコストの相関を見る。
- PR size を交絡要因として別列に残す。

除外条件:

- auto-merge のみで人間レビューがない PR
- generated code が大半の PR
- review policy が期間中に大きく変わった repository segment

### H4: 境界違反・関係式複雑度と将来リスク

必要データ:

- `boundaryViolationCount`
- `relationComplexity` の構成要素ベクトル
- 対象 component の将来 co-change 回数
- 関連 incident / bug issue 数

測定方法:

- PR merge 後の観測窓を 30 / 90 / 180 日で切る。
- 境界違反を含む component と含まない component の将来 co-change を比較する。
- `relationComplexity` は構成要素別に分析し、派生合計値だけに潰さない。

除外条件:

- policy file が未定義で boundary violation が未評価の repository
- relation complexity extractor rule set が対象 framework に未対応の場合
- 観測窓内に repository が archive された場合

## 前提の分離

extractor tooling 側の前提:

- source checkout から component, dependency edge, policy violation, signature を出力する。
- extractor version と rule set version をすべての出力に含める。
- 抽出できない軸は 0 に丸めず、`unmeasured` と理由を metadata に残す。
- 実コードベース抽出器が Lean の `ComponentUniverse` の完全な witness を生成したとは主張しない。

data analysis 側の前提:

- 相関を Lean theorem として扱わない。
- repository size, PR size, team size, review policy, seasonality を交絡要因として記録する。
- 効果量、信頼区間、外れ値を報告し、単一の有意差だけで結論にしない。
- repository 間比較では、言語・framework・開発プロセスの違いを metadata として保持する。
- `metricStatus.measured = false` の軸は欠損値として扱い、placeholder 0 を
  risk 0 または違反なしとして集計しない。

## 記述ルール

実証結果を書くときは、次の区別を守る。

- Lean で証明済み: `proved`
- Lean 上の定義や executable metric のみ: `defined only`
- 将来 Lean で証明する命題: `future proof obligation`
- 実コードや運用データで検証する仮説: `empirical hypothesis`

たとえば、`StrictLayered -> Acyclic` は Lean 側の構造的事実として扱える。一方、
`sccMaxSize が大きいほど障害修正時間が長い` は empirical hypothesis であり、
データにより支持・反証される。

## Pilot study 手順

1. 対象 repository と期間を決める。
2. extractor version と policy version を固定する。
3. PR / issue / incident データを取得する。
4. PR base / head または merge commit で signature before / after を計算する。
5. H1 から H4 の分析テーブルを作る。
6. 除外対象と未評価軸を記録する。
7. 仮説ごとに効果量、外れ値、次の extractor 改善点をまとめる。

pilot の完了条件は、強い結論を出すことではなく、再現可能なデータセットと分析手順を
得ることである。
