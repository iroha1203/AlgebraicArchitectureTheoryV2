# lean4-samples empirical pilot

Lean status: `empirical hypothesis` / pilot validation.

Issue [#135](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/135)
の pilot として、外部 repository
[`leanprover-community/lean4-samples`](https://github.com/leanprover-community/lean4-samples)
に `sig0-extractor` と empirical dataset v0 schema を適用した。

この pilot の目的は強い統計的結論ではなく、実 repository の PR metadata と
before / after signature を結合した record が再現可能に作れるか、また
`metricStatus.measured = false` と risk 0 を混同しない欠損規約が保たれるかを
確認することである。

## 対象

- repository: `leanprover-community/lean4-samples`
- default branch: `main`
- component kind: Lean module source file
- after commit role: PR `head`
- policy file: 未指定
- runtime edge evidence: 未指定

対象 PR は、Lean source を含む merged PR から連続する 5 件を選んだ。

| PR | title | base | head | changed files | + | - |
| --- | --- | --- | --- | ---: | ---: | ---: |
| [#10](https://github.com/leanprover-community/lean4-samples/pull/10) | List Comprehension example of syntax extension. | `4785ec2` | `5ad4128` | 6 | 447 | 0 |
| [#11](https://github.com/leanprover-community/lean4-samples/pull/11) | natural number game content for lean4 | `f5069cf` | `ac27f7b` | 30 | 2288 | 1 |
| [#12](https://github.com/leanprover-community/lean4-samples/pull/12) | Add multiplication world. | `b2cec40` | `1c924c7` | 26 | 547 | 60 |
| [#13](https://github.com/leanprover-community/lean4-samples/pull/13) | Add more to natural numbers | `864463d` | `7139621` | 50 | 1816 | 61 |
| [#15](https://github.com/leanprover-community/lean4-samples/pull/15) | Add AdvancedPropositionWorld and AdvancedAdditionWorld. | `f3fcf37` | `47b244a` | 48 | 1356 | 60 |

## 生成物の扱い

pilot では 5 件の `schemaVersion = "empirical-signature-dataset-v0"` record を
生成した。ただし raw Sig0 output と dataset JSON は機械生成物であり、PR には
含めない。生成先の `metadata/`, `sig0/`, `records/` はこの directory の
`.gitignore` で除外する。

この README には、対象 PR、測定サマリ、欠損値の扱い、再生成手順だけを残す。
必要になった場合は下の手順で同じ形の JSON を再生成する。

## Signature summary

| PR | fanout before | fanout after | fanout delta | maxFanout before | maxFanout after | reachable before | reachable after |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| #10 | 9 | 11 | 2 | 1 | 1 | 1 | 1 |
| #11 | 11 | 40 | 29 | 1 | 6 | 1 | 6 |
| #12 | 40 | 77 | 37 | 6 | 6 | 6 | 6 |
| #13 | 77 | 127 | 50 | 6 | 6 | 6 | 6 |
| #15 | 127 | 244 | 117 | 6 | 13 | 6 | 13 |

全 record で `hasCycle = 0`, `sccMaxSize = 1`, `sccExcessSize = 0` だった。
これは対象 repository の Lean import graph がこの sample 範囲では DAG として抽出
されたことを示す tooling-side observation であり、Lean theorem ではない。

## 解釈と次の測定対象

今回の pilot で、import graph 由来の `fanoutRisk`, `maxFanout`,
`reachableConeSize` は実 repository の PR 前後で変化を拾えることを確認できた。
一方、`lean4-samples` は tutorial / sample 集であり、fanout の増加は設計悪化という
より教材コンテンツ追加を反映している。そのため、この pilot の数値は
「extractor と dataset schema が現実入力で動くこと」の検証として扱い、品質との
相関を主張しない。

意味のある実証指標へ進めるには、実アプリケーション repository で、boundary policy
や runtime edge evidence を含む record を作る必要がある。特に Python 対応は次の
展開として有望である。Python repository では web backend, CLI, data pipeline,
ML tooling など対象母集団が広く、PR metadata や issue / incident metadata も
取得しやすい。

最小の Python pilot は、`componentKind = "python-module"` として `*.py` を scan し、
標準 `ast` parser で `import` / `from ... import ...` を抽出するところから始める。
package root を指定して local module edge と external dependency edge を分ければ、
既存 dataset schema を大きく変えずに `fanoutRisk`, `maxFanout`,
`reachableConeSize`, `hasCycle`, `sccMaxSize` を比較できる。

ただし Python では dynamic import, plugin loading, framework convention,
generated code, migration, notebook などが交絡要因になる。したがって初期段階では、
静的 import graph を core metric として測り、Django / FastAPI / Celery /
SQLAlchemy などの runtime / relation evidence は別 input として段階的に追加する。
この分離により、測定済み 0 と未評価を混同しない現在の `metricStatus` 規約を
Python pilot にも維持できる。

## 欠損値の確認

この pilot では policy file と runtime edge evidence を与えていない。そのため、
`boundaryViolationCount` と `abstractionViolationCount` の signature 値は placeholder
として 0 になるが、各 record の
`signatureBefore.metricStatus.<axis>.measured` と
`signatureAfter.metricStatus.<axis>.measured` は `false` であり、理由は
`policy file not provided` である。

同様に `runtimePropagation` は `null` で、`metricStatus.runtimePropagation.measured`
は `false`、理由は `runtime dependency graph not provided` である。
このため `deltaSignatureSigned.boundaryViolationCount`,
`deltaSignatureSigned.abstractionViolationCount`, `deltaSignatureSigned.runtimePropagation`
はすべて `null` になり、測定済み 0 と未評価を混同していない。

`analysisMetadata.runtimeMetrics.runtimeGraphMeasured` も `false` として記録した。

## Validation report observation

raw Sig0 output に `sig0-extractor validate --universe-mode local-only` を適用した際、
以前は一部 record で `edge-endpoint-resolved` と `edge-closure-local` が fail した。
代表例は次である。

```text
CSVParser.Main -> CSVParser
ListComprehension.Main -> ListComprehension
```

Issue [#149](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/149) で、
`Foo/Main.lean` が root module `Foo` を import する sample layout では、`Foo` を
source file component として自動補完せず、`local-only` universe 外の synthetic module
root target として warning に分類する方針に固定した。validation summary が `fail` の
snapshot は H1-H5 の主要分析から除外し、`warn` の snapshot は stratification または
sensitivity analysis の対象として dataset に取り込める。

## 実行手順

外部 repository を `/tmp/aatv2-lean4-samples` に clone し、各 PR の base / head を
checkout して次の形で生成した。

```bash
mkdir -p docs/empirical/lean4_samples_pilot/metadata \
  docs/empirical/lean4_samples_pilot/sig0 \
  docs/empirical/lean4_samples_pilot/records

cargo run --quiet --manifest-path tools/sig0-extractor/Cargo.toml -- \
  --root /tmp/aatv2-lean4-samples \
  --out docs/empirical/lean4_samples_pilot/sig0/pr-10-before.json

cargo run --quiet --manifest-path tools/sig0-extractor/Cargo.toml -- dataset \
  --before docs/empirical/lean4_samples_pilot/sig0/pr-10-before.json \
  --after docs/empirical/lean4_samples_pilot/sig0/pr-10-after.json \
  --pr-metadata docs/empirical/lean4_samples_pilot/metadata/pr-10.json \
  --after-role head \
  --out docs/empirical/lean4_samples_pilot/records/pr-10.json
```

PR metadata は GitHub API の PR detail と files API から作成した。
`metadata/pr-*.json` は repository / pullRequest / prMetrics /
issueIncidentLinks / analysisMetadata を持つ empirical dataset input JSON である。

## Pilot で見つかった不足

- PR metadata から dataset input JSON を作る手順は
  [#146](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/146)
  で `sig0-extractor pr-metadata` として repository-local tooling に移した。
- 外部 repository 用の boundary / abstraction policy と runtime edge evidence が
  まだないため、H4 / H5 の pilot record としては欠損が多い。
  Follow-up: [#147](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/147)
- `lean4-samples` は multi-project repository であり、`lakefile.lean` も `.lean`
  component として扱われる。repository root と subproject root の測定単位、
  build config を component とするかの設計判断が必要である。
  Follow-up: [#148](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/148)
- `Foo/Main.lean` から `Foo` を import する layout の module root target は
  [#149](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/149) で
  synthetic module root target として warning に分類する方針に固定した。

## 結論

`sig0-extractor` と empirical dataset v0 schema は、外部の小規模 Lean repository
に対して少なくとも 5 件の before / after signature record を生成できた。
欠損値規約も維持され、policy / runtime 未指定の placeholder 0 は
`metricStatus.measured = false` と `deltaSignatureSigned = null` によって
risk 0 から分離された。
