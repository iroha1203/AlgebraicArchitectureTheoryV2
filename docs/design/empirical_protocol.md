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

`signatureBefore` は PR base commit、`signatureAfter` は PR head または merge commit
で計算する。merge commit の有無で結果が変わる場合は、その差分を metadata に残す。
`deltaSignatureSigned` は `Nat` subtraction ではなく符号付き差分として扱う。
改善による負の差分を 0 に丸めない。

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
