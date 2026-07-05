# FieldSig Artifacts And Boundaries

この文書は `fieldsig` が出す主要 SFT / operational artifact と読み方の境界をまとめる。

Lean status: `empirical hypothesis` / tooling output.

## Product surface grouping

Artifact は次の surface ごとに読む。surface が違っても、測定境界、claim boundary、
non-conclusions を落とさない。

| Surface | Artifact families | Boundary |
| --- | --- | --- |
| ArchSig handoff | `archsig-measurement-packet/v1` から生成する `operation-support-estimate-v0`。 | ArchSig measurement packet を current AG measurement state として読む。raw ArchMap observation、PR diff analysis、forecast truth、causal proof ではない。 |
| Adapter / review refs | Sig0、validation report、snapshot、signature diff、AIR、Feature Extension Report、AAT Observable Bundle。 | historical / bounded review refs として読めるが、FieldSig の現行 handoff source of truth ではない。 |
| FieldSig SFT | ArtifactDescriptor、OperationSupportEstimate、ForecastConeSkeleton、ConsequenceEnvelope、ForecastCalibrationHook と validation report。 | bounded forecast report projection であり、point prediction、causal proof、forecast correctness ではない。 |
| FieldSig Operational | PR history dataset、feature extension dataset、outcome linkage、daily ledger、calibration、threshold、ownership、repair adoption、incident correlation、hypothesis refresh。 | empirical / operational feedback であり、correlation を causal theorem にしない。 |

## Primary Artifacts

| 出力 | schemaVersion | 用途 |
| --- | --- | --- |
| Sig0 output | `archsig-sig0-v0` | 単一 revision の component、edge、signature、metric status。 |
| Validation report | `component-universe-validation-report-v0` | Sig0 output の duplicate、edge closure、policy status などの検査結果。 |
| Snapshot | `signature-snapshot-store-v0` | repository revision ごとの保存用 signature record。 |
| Diff report | `signature-diff-report-v0` | before / after の悪化軸、改善軸、未評価軸、evidence diff、PR attribution candidate。 |
| AIR | `aat-air-v0` | Signature artifact layer を claim / evidence / coverage / extension boundary へ正規化した中間表現。 |
| ArchSig measurement packet | `archsig-measurement-packet/v1` | FieldSig の現行 ArchSig handoff。structural verdict、computed invariants、analytic readings、assumption ledger、non-conclusions を bounded SFT input として読む。 |
| ArchSig analysis packet | `archsig-analysis-packet/v1` | Legacy compatibility handoff。typed evaluator / obstruction / signature / repair / structural review refs を bounded SFT input として読むが、v0.4.0 の primary handoff ではない。 |
| ArchMap validation report | `archmap-validation-report-v0` | ArchMap の source refs、claim boundary、semantic coverage、conflict、formal promotion guardrail、atomic observation checks / summary の検査結果。 |
| AIR validation report | `aat-air-validation-report-v0` | AIR の dangling refs、claim boundary、measured evidence traceability の検査結果。 |
| Theorem precondition check report | `theorem-precondition-check-report-v0` | AIR claim が `FORMAL_PROVED` へ昇格できるかの検査結果。 |
| Feature Extension Report | `feature-extension-report-v0` | PR review 用 static report。split status、witness、coverage gap、theorem precondition checks を持つ。 |
| AAT Observable Bundle | `aat-observable-bundle-v0` | AAT concept mapping、selected universe、witness catalog、operation candidates、theorem boundary、review actions、responsibility boundary を束ねる。 |
| Policy decision report | `policy-decision-report-v0` | organization policy に基づく pass / warn / fail / advisory decision。 |
| PR comment summary | `pr-comment-summary-v0` | Feature Extension Report と policy decision を GitHub Checks / PR comment 向け Markdown に整形する。 |
| Baseline suppression report | `baseline-suppression-report-v0` | baseline/current report の差分、suppression / accepted risk metadata を保持する。 |

## Policy / Registry / Schema Artifacts

| 出力 | schemaVersion | 用途 |
| --- | --- | --- |
| Organization policy validation report | `organization-policy-validation-report-v0` | warn / fail / advisory policy と formal claim promotion boundary を検査する。 |
| Law policy template registry validation report | `law-policy-template-registry-validation-report-v0` | policy template registry の boundary refs と non-conclusions を検査する。 |
| Architecture policy | `architecture-policy-v0` | project-local adopted laws、layer selectors、allowed / forbidden dependency、exception、SRP taxonomy を保持する。 |
| Architecture policy validation report | `architecture-policy-validation-report-v0` | law-aware policy の selector / SRP evidence boundary / non-conclusions を検査する。 |
| Law violation report | `law-violation-report-v0` | Layered Architecture の deterministic violation、allowed exception、unmeasured selector、SRP review cue を分ける。 |
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

## SFT Forecasting Input Artifacts

| 出力 | schemaVersion | 用途 |
| --- | --- | --- |
| ArtifactDescriptor | `artifact-descriptor-v0` | PRD / Spec / Issue / AI proposal の source refs、action class candidates、scope、missing evidence、measurement boundary、forecast non-conclusions を保持する。 |
| ArtifactDescriptor validation report | `artifact-descriptor-validation-report-v0` | descriptor が theorem claim、ground truth architecture object、causal forecast に昇格していないことを検査する。 |
| IntentMap | `intentmap-v0` | PRD / Epic / Spec の requirement、operation、workflow、state transition、acceptance、non-goal、ambiguity、missing decision を source refs と LLM provenance 付きで保持する。 |
| IntentMap validation report | `intentmap-validation-report-v0` | source refs、claim classification、confidence boundary、missing decision / ambiguity / missing evidence、non-conclusions を検査する。 |
| AlignmentMap | `intent-archmap-alignment-v0` | IntentMap item と ArchMap item の対応、preserves / forgets、unaligned / unsupported / ambiguous boundary、missing evidence を保持する。 |
| AlignmentMap validation report | `intent-archmap-alignment-validation-report-v0` | IntentMap refs と ArchMap refs の dangling reference、alignment kind、measured zero への丸め、non-conclusions を検査する。 |
| OperationSupportEstimate | `operation-support-estimate-v0` | descriptor refs、candidate operation families、ArchSig analysis refs、obstruction / signature / repair support refs、coverage gaps、policy constraints、support disposition、governance action refs、known forbidden support、unknown remainder、confidence / evidence boundary を保持する。 |
| OperationSupportEstimate validation report | `operation-support-estimate-validation-report-v0` | unknown support と measured zero の混同、global policy safety / future trajectory safety への昇格を検査する。 |
| ForecastConeSkeleton | `forecast-cone-skeleton-v0` | finite support refs、bounded horizon、path class candidates、gluing evidence、governance interventions、typed boundary failures、forecast boundary、unknown remainder を保持する。 |
| ForecastConeSkeleton validation report | `forecast-cone-skeleton-validation-report-v0` | probability claim、unmeasured axis の safe 扱い、support / horizon refs 欠落を検査する。 |
| ConsequenceEnvelope | `consequence-envelope-report-v0` | affected regions、signature axes、axis delta ranges、obstruction candidates、missing / theorem boundary items、typed boundary failures、reviewer actions、review / CI recommendation を保持する。 |
| ConsequenceEnvelope validation report | `consequence-envelope-report-validation-report-v0` | source refs、measurement boundary、forecast non-conclusions、unknown remainder の欠落を検査する。 |
| SFT review summary | `sft-review-summary-v0` | opened futures、closed futures、boundary failures、next actions、evidence refs、boundary refs、LLM judgement contract を保持する。 |
| SFT review summary validation report | `sft-review-summary-validation-report-v0` | status、evidence refs、boundary refs、forbidden readings、non-conclusions を検査する。 |
| ForecastCalibrationHook | `forecast-calibration-hook-v0` | forecast item refs と observed PR / review / CI / outcome refs、B10 / B11 artifact boundary を対応付ける。 |
| ForecastCalibrationHook validation report | `forecast-calibration-hook-validation-report-v0` | matched / unmatched / unavailable / private / notComparable を measured zero と混同していないことを検査する。 |
| IntentCalibrationRecord | `intent-calibration-record-v0` | IntentMap item、forecast item、observed implementation artifact、missing decision status、forecast usefulness feedback を対応付ける。 |
| PR Quality Analysis | `pr-quality-analysis-report-v0` | PR diff / repository evidence から作られた ArchMap 系 artifact を review cue として読む。merge approval ではない。 |
| AI Proposal Governance | `ai-proposal-governance-v0` | AI proposal の prompt / policy boundary、support taxonomy、shortcut witness、review / CI mediation、posterior field update を保持する。 |
| AI Proposal Governance validation report | `ai-proposal-governance-validation-report-v0` | support category、shortcut witness、review / CI / posterior boundary、AI safety / forecast correctness / lawfulness non-conclusions を検査する。 |
| Lifecycle Decision Report | planned `lifecycle-decision-report-v0` | repair / migration / contraction / deletion の selected inputs、field capacity impact、runtime / ownership boundary、non-conclusions を保持する将来候補。 |

`archsig-analysis-sft-input` は `archsig-measurement-packet/v1` を
`operation-support-estimate-v0` へ射影する現行 handoff command である。structural verdict、
computed invariants、analytic readings、assumption ledger、non-conclusions は bounded refs /
unknown remainder として残る。analytic readings や theorem-candidate readings は structural verdict
へ変換しない。これは certified universal atoms、zero curvature proof、PR diff analysis、
forecast correctness、future outcome probability ではない。`archsig-analysis-packet/v1` は
legacy bounded compatibility input としてのみ読む。
`archmap-sft-input` は legacy bounded projection であり、raw ArchMap observation を forecast truth へ
昇格してはならない。

`artifact-descriptor-v0` は B12 SFT forecasting MVP の最初の入力正規化 artifact である。
後段では `operation-support-estimate-v0`、`forecast-cone-skeleton-v0`、
`consequence-envelope-report-v0`、`sft-review-summary-v0`、`forecast-calibration-hook-v0`
が境界を引き継ぐ。
これらは probability、causal prediction、global safety、forecast correctness、Lean theorem
claim を生成しない。missing evidence、unsupported constructs、forecast non-conclusions は
後段 artifact に引き継ぐ境界として読む。

PRD v3 の planning forecast では、PRD-only forecast を意味のある forecast として扱わず、
`intentmap-v0` と `intent-archmap-alignment-v0` を先に作る。LLM は semantic extraction と
artifact reading を担当し、ArchSig は schema validation と deterministic projection を担当する。
`intent-forecast` は AlignmentMap から `operation-support-estimate-v0`、`forecast-cone-skeleton-v0`、
`consequence-envelope-report-v0` を生成するが、implementation impact、forecast correctness、
future outcome probability、quality ranking、incident causality を結論しない。missing decision、
ambiguous intent、unaligned / unsupported intent、missing evidence は planning boundary として残す。

`forecast-calibration-hook-v0` は `docs/tool/sft_calibration_benchmark.md` の protocol で読む。
hook は forecast item refs と observed refs の対応を保存するだけであり、forecast quality を
自動判定しない。review mediation と AI shortcut detection は別 benchmark として集計し、
private / unavailable / missing data は non-conclusion boundary として残す。

`sft-forecast` は Markdown PRD / Spec / Issue / AI proposal、GitHub Issue JSON、
AI proposal JSON から
`artifact-descriptor-v0`、`operation-support-estimate-v0`、
`forecast-cone-skeleton-v0`、`consequence-envelope-report-v0`、
`sft-review-summary-v0` と各 validation report を
同じ出力 directory に生成する end-to-end command である。command の成功は bounded
tooling pipeline の validation 成功であり、extractor completeness、forecast correctness、
causal prediction、Lean theorem claim への昇格を意味しない。

GitHub Issue JSON / AI proposal JSON adapter は supplied JSON artifact の正規化であり、
GitHub API からの authenticated fetch、private project fields の復元、AI model
evaluation、human review acceptance、runtime extraction を行わない。これらは
missing evidence / unavailable evidence boundary として後段 artifact に渡す。

AI proposal governance は `docs/tool/ai_proposal_governance.md` の protocol で読む。
`ai-proposal-governance-v0` は `artifact-descriptor-v0` から生成できる reviewer-facing
projection であり、`operation-support-estimate-v0`、`consequence-envelope-report-v0`、
`forecast-calibration-hook-v0` と B10 / B11 operational artifact の refs を保持する。
prompt / policy boundary、allowed / conditionallyAllowed / forbidden / unknown / outOfScope
support、shortcut witness、review / CI mediation、posterior field update を接続するが、
AI policy compliance、review pass、CI pass、schema validation pass を architecture lawfulness
や forecast correctness に昇格しない。

Lifecycle decision report は将来 artifact 候補であり、現時点では schema / validator / CLI を
持たない。入力は ArchitectureSignature trajectory、`ConsequenceEnvelope` family、runtime /
incident evidence refs、ownership / staffing boundary、repair / migration support refs に限定して
読む。出力は intervention comparison であり、repair、migration、contraction、deletion を
market success、human intention、staffing availability、project management recommendation として
rank しない。実装時は selected inputs、excluded inputs、private / unavailable evidence、
unknown remainder、calibration refs、non-conclusions を report に残す。

`consequence-envelope-report-v0` は `forecast-cone-skeleton-v0` からの
loss-aware report projection として読む。一つ以上の bounded cone skeleton から、
path class candidates、affected regions、comparable signature axes、axis delta ranges、
obstruction candidates、missing / theorem boundary items、typed boundary failures、
reviewer actions、review / CI recommendation をまとめる。projection 後も `unknownRemainder`、measurement boundary、forecast
non-conclusions を保持する必要がある。envelope report は projection 元の cone family を
一意復元しないし、probability、causal proof、calibrated forecast correctness を主張しない。

`sft-review-summary-v0` は `consequence-envelope-report-v0` から reviewer / LLM judgement
入力へ寄せた deterministic projection である。opened futures / closed futures /
boundary failures / next actions は evidence refs と boundary refs を必ず持つ。LLM が返す
judgement はこの summary を根拠にするが、tool は LLM provider 呼び出し、merge approval、
probability claim、Lean theorem promotion を行わない。

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

## AAT Observable Bundle

`aat-observable-bundle-v0` は AAT の主要概念を ArchSig artifact として追跡する共通 bundle である。
`sourceRefs`、`selectedUniverse`、`conceptMappings`、`observedAxes`、`witnessCatalog`、
`operationCandidates`、`theoremBoundaries`、`reviewActions`、`llmReviewSurface`、
`responsibilityBoundary` を持つ。validation は schema version、source refs、concept coverage、
measurement status、witness / theorem boundary の review action refs、deterministic / LLM /
human / formal proof の責務分離を検査する。

この bundle は #1161 の law-aware review artifact を AAT concept coverage へ接続する。
Layered / SRP / policy / PR quality の evidence は、`ObstructionWitness`、`TheoremBoundary`、
`ArchitectureOperation`、`Projection / Observation` などの AAT-facing field に再配置される。
`private`、`unavailable`、`unsupported`、`dynamicBlindSpot`、`outOfScope` は first-class
boundary であり、measured zero へ丸めない。

`reviewActions` は raw `nonConclusions` を evidence gap、non-finding、blocked formal claim、
review guardrail、next evidence へ翻訳する。これは LLM Review Skill と human reviewer の
作業 surface であり、validation pass、LLM judgment、review action の存在はいずれも
Lean theorem proof、extractor completeness、merge approval ではない。

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
| Layered law violation | `law-violation-report-v0.deterministicViolations[]`, `policyViolations[]` | resolved layer selector と measured import edge に対する deterministic forbidden dependency。 | selector 未解決、dynamic import、framework convention は unmeasured。policy pass は architecture lawfulness proof ではない。 |
| SRP review cue | `signatureAxes[]`, `repairCandidates[]`, `law-violation-report-v0.srpCues[]` | LLM Review Skill が probable violation / acceptable orchestrator / unmeasured を判断するための semantic evidence。 | tool 単独で SRP violation を断定しない。 |
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
- SRP cue が tool-only violation を示す。
- migration pass が semantic preservation を示す。
- measured witness が Lean theorem proof である。
- report warning が incident / rollback / MTTR を引き起こした。
- Architecture Signature が単一スコアで品質順位を与える。
