# ArchSig Artifacts And Boundaries

この文書は `archsig` が出す主要 artifact と読み方の境界をまとめる。

Lean status: `empirical hypothesis` / tooling output.

## Primary Artifacts

| 出力 | schemaVersion | 用途 |
| --- | --- | --- |
| Sig0 output | `archsig-sig0-v0` | 単一 revision の component、edge、signature、metric status。 |
| Validation report | `component-universe-validation-report-v0` | Sig0 output の duplicate、edge closure、policy status などの検査結果。 |
| Snapshot | `signature-snapshot-store-v0` | repository revision ごとの保存用 signature record。 |
| Diff report | `signature-diff-report-v0` | before / after の悪化軸、改善軸、未評価軸、evidence diff、PR attribution candidate。 |
| AIR | `aat-air-v0` | Signature artifact layer を claim / evidence / coverage / extension boundary へ正規化した中間表現。 |
| AIR validation report | `aat-air-validation-report-v0` | AIR の dangling refs、claim boundary、measured evidence traceability の検査結果。 |
| Theorem precondition check report | `theorem-precondition-check-report-v0` | AIR claim が `FORMAL_PROVED` へ昇格できるかの検査結果。 |
| Feature Extension Report | `feature-extension-report-v0` | PR review 用 static report。split status、witness、coverage gap、theorem precondition checks を持つ。 |
| Policy decision report | `policy-decision-report-v0` | organization policy に基づく pass / warn / fail / advisory decision。 |
| PR comment summary | `pr-comment-summary-v0` | Feature Extension Report と policy decision を GitHub Checks / PR comment 向け Markdown に整形する。 |
| Baseline suppression report | `baseline-suppression-report-v0` | baseline/current report の差分、suppression / accepted risk metadata を保持する。 |

## Policy / Registry / Schema Artifacts

| 出力 | schemaVersion | 用途 |
| --- | --- | --- |
| Organization policy validation report | `organization-policy-validation-report-v0` | warn / fail / advisory policy と formal claim promotion boundary を検査する。 |
| Law policy template registry validation report | `law-policy-template-registry-validation-report-v0` | policy template registry の boundary refs と non-conclusions を検査する。 |
| Custom rule plugin registry validation report | `custom-rule-plugin-registry-validation-report-v0` | custom rule plugin registry の theorem refs と claim boundary を検査する。 |
| Measurement unit registry validation report | `measurement-unit-registry-validation-report-v0` | measurement unit selection と evidence adapter boundary を検査する。 |
| Repair rule registry validation report | `repair-rule-registry-validation-report-v0` | repair rule registry の selected obstruction boundary と advisory non-conclusions を検査する。 |
| Synthesis constraint validation report | `synthesis-constraint-validation-report-v0` | synthesis candidate / no-solution boundary と solver completeness non-conclusion を検査する。 |
| No-solution certificate validation report | `no-solution-certificate-validation-report-v0` | valid certificate claim refs と finite candidate universe boundary を検査する。 |
| Schema compatibility report | `schema-compatibility-check-report-v0` | schema migration / compatibility の field mapping、non-conclusions、coverage / exactness boundary を検査する。 |
| Detectable values / reported axes catalog | `detectable-values-reported-axes-catalog-v0` | reported axes と detectable values の catalog。 |

## Dataset Artifacts

| 出力 | schemaVersion | 用途 |
| --- | --- | --- |
| Dataset record | `empirical-signature-dataset-v0` | PR metadata と before / after signature を結合した実証研究用 record。 |
| PR history dataset | `pr-history-dataset-v0` | GitHub PR metadata と artifact refs を履歴 record として保存する。 |
| Feature extension dataset | `feature-extension-dataset-v0` | PR history と Feature Extension Report / theorem check を join する。 |
| Outcome linkage dataset | `outcome-linkage-dataset-v0` | feature extension dataset と rollback / incident / MTTR などの outcome observation を join する。 |

## Operational Feedback Artifacts

| 出力 | schemaVersion | 用途 |
| --- | --- | --- |
| Report outcome daily ledger | `report-outcome-daily-ledger-v0` | outcome linkage dataset と architecture drift ledger を daily aggregation window で join する。 |
| Calibration review record | `calibration-review-record-v0` | false positive / false negative review と metric calibration input を保存する。 |
| Team threshold policy | `team-threshold-policy-v0` | team-specific threshold tuning と CI mode policy を保存する。 |
| Ownership boundary monitor | `ownership-boundary-monitor-v0` | ownership scope と boundary erosion signal を operational observation として保存する。 |
| Repair adoption record | `repair-adoption-record-v0` | repair suggestion の adopted / rejected / deferred decision と follow-up outcome refs を保存する。 |
| Incident correlation monitor | `incident-correlation-monitor-v0` | incident / rollback / MTTR correlation、confounder、missing / private data boundary を保存する。 |
| Hypothesis refresh cycle | `hypothesis-refresh-cycle-v0` | empirical hypothesis の retained / rejected / proposed update を versioned research tracking として保存する。 |

## Measurement Boundary

`archsig` は測定済み 0 と未評価を分ける。

- `metricStatus.<axis>.measured = true`: 測定済み。
- `metricStatus.<axis>.measured = false`: 未評価。signature 値が placeholder 0 でも risk 0 と読まない。
- optional axis の `null`: 未評価、またはこの入力では比較不能。
- `deltaSignatureSigned.<axis> = null`: before / after のどちらかが未評価、または値が `null`。
- `measurementBoundary = measuredZero`: 測定され、値が 0。
- `measurementBoundary = measuredNonzero`: 測定され、値が非 0。
- `measurementBoundary = unmeasured`: 測定されていない。
- `measurementBoundary = outOfScope`: その artifact / universe では対象外。

AI agent は `signature` の値だけで判断せず、`metricStatus`, `metricDeltaStatus`,
`unmeasuredAxes`, `coverageGaps`, `nonConclusions` を併読する。

## Claim Boundary

`theorem-check` は tooling evidence と Lean theorem claim を分離する。

- `FORMAL_PROVED`: `claimLevel = formal`, `claimClassification = proved`, registry 登録済み theorem refs、かつ missing preconditions がない claim。
- `MEASURED_WITNESS`: tooling evidence として測定された witness。formal proof claim へ自動昇格しない。
- `BLOCKED_FORMAL_CLAIM`: formal/proved claim だが theorem bridge precondition が足りない claim。

Python import graph、runtime edge evidence、policy violation count、B10 operational feedback は
tooling evidence であり、Lean `ComponentUniverse` bridge precondition なしに formal theorem claim へ読まない。

## Diagnostics

単一 revision の構造診断:

| 診断 | 主に見る field | 高い、または増えた場合に言えること | 注意 |
| --- | --- | --- | --- |
| 静的依存の循環検出 | `signature.hasCycle`, `signature.sccMaxSize`, `sccExcessSize` | import graph に循環がある。 | runtime dependency や動的依存の非循環性までは言わない。 |
| SCC リスク | `sccMaxSize`, `sccExcessSize`, `weightedSccRisk` | 大きい SCC は変更波及候補になる。 | `weightedSccRisk` は重み入力がある場合だけ測れる。 |
| 依存深度 | `maxDepth` | 依存 chain が深い。 | 循環リスクは `hasCycle` / SCC 軸で別に読む。 |
| fanout / 依存集中 | `fanoutRisk`, `maxFanout` | 依存辺総数や局所的な結合点候補が増えた。 | fanout 増加は常に悪ではない。 |
| 到達 cone | `reachableConeSize` | 変更理解や影響確認の範囲が広がる候補。 | edge 方向は `source depends on target`。 |
| boundary violation | `boundaryViolationCount`, `policyViolations[]` | 意図した layer / domain boundary が破られている候補。 | policy 未指定なら placeholder 0 でも違反なしとは読まない。 |
| abstraction violation | `abstractionViolationCount`, `policyViolations[]` | abstraction boundary の破れ候補。 | Lean の `ProjectionSound` witness そのものではない。 |
| runtime exposure | `runtimePropagation`, `runtimeDependencyGraph`, `runtimeEdgeEvidence[]` | runtime evidence 上の exposure radius が大きい。 | runtime edge evidence を渡した場合だけ測定済み。 |
| relation complexity | `relationComplexity`, `counts.*`, `excludedEvidence[]` | 状態遷移設計や運用リスクの review 対象候補。 | candidate evidence からの observation。 |

before / after の差分診断:

| 診断 | 主に見る field | 言えること | 注意 |
| --- | --- | --- | --- |
| before / after 差分 | `worsenedAxes`, `improvedAxes`, `unchangedAxes`, `deltaSignatureSigned` | どの signature axis が悪化、改善、維持されたか。 | 未評価軸は `null`。 |
| 未評価 / 比較不能軸 | `metricStatus`, `metricDeltaStatus`, `unmeasuredAxes` | 測定されていない、または比較できない軸。 | 未評価理由を併読する。 |
| evidence diff | `evidenceDiff.componentDelta`, `evidenceDiff.edgeDelta`, `evidenceDiff.policyViolationDelta` | 悪化軸の具体的な調査入口。 | raw evidence diff は `--before-sig0` / `--after-sig0` が必要。 |
| PR attribution candidate | `attribution.candidates[]` | どの PR が悪化軸に関係しそうか。 | 因果証明ではない。confidence は調査優先度。 |

## Non-Conclusions

`archsig` output は次を結論しない。

- 任意 repository から完全な architecture model を抽出できる。
- extractor output が Lean `ComponentUniverse` と同一である。
- policy pass や schema compatibility pass が architecture lawfulness を示す。
- migration pass が semantic preservation を示す。
- measured witness が Lean theorem proof である。
- report warning が incident / rollback / MTTR を引き起こした。
- Architecture Signature が単一スコアで品質順位を与える。
