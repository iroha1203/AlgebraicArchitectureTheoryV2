# ArchMap v1 Output Replacement Gap Ledger

この台帳は、`docs/tool/archmap_minimal_observation_contract_prd.md` の
output replacement 要求を、現在の ArchSig v1 実装・tests・docs と照合する。

目的は、ArchMap v1 移行を「input schema が通る」ではなく、
`normalized ArchMap + LawPolicy selector + evaluator registry + evidence contract +
typed evaluator result` から ArchSig の output surface を再生成できる状態まで
戻すことである。

## Scope

対象 Issue:

- Parent: [#1835](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/1835)
- This ledger: [#1841](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/1841)

対象 PRD:

- `docs/tool/archmap_minimal_observation_contract_prd.md`

現在の実装 evidence:

- `tools/archsig/src/main.rs` の v1 `analyze` は
  `normalize_archmap_v1 -> evaluate_typed_v1 -> build_architecture_distance_v1 ->
  build_typed_analysis_packet_v1` を実行する。
- `tools/archsig/src/typed_evaluator.rs` の `build_typed_analysis_packet_v1` は、
  `typedEvaluatorResults`, `typedEvaluatorDiagnosis`, `architectureDistance`,
  `distanceDiagnosis`, `positiveBoundedConclusions`, `detailRefs` を出す。
- 現在の practical example の v1 raw packet には
  `architectureSpectrumReport`, `architectureHomotopyReport`,
  `structuralReadingReviewSurface` は含まれない。

## Status Vocabulary

| Status | Meaning |
| --- | --- |
| done | 現在の v1 実装・tests・docs が PRD 要求を満たす。 |
| partial | 一部は実装済みだが、PRD の acceptance には不足がある。 |
| missing | 実装または test が存在せず、PRD 要求を満たさない。 |
| docs drift | docs が current runtime と矛盾する、または未完了 gap を完了済みに見せる。 |
| blocked-by-design | 後続 Issue で design / registry / schema を先に固定する必要がある。 |

## Implementation Gap Ledger

| PRD lines | Requirement | Current evidence | Status | Tracking issue |
| --- | --- | --- | --- | --- |
| 449-462 | v1 `analyze` は validation、normalization、typed evaluator の後に `analysis packet / summary / viewer / distanceDiagnosis` を作る。 | `main.rs` は v1 artifact chain を実行している。summary / viewer / distanceDiagnosis は出るが、packet は thin v1 packet で rich output refs を持たない。 | partial | #1845, #1843 |
| 465-471 | ArchSig は source 補完、label-only positive、missing-as-zero、未入力 molecule 推測、obstruction / square / holonomy / risk の input 化をしない。 | v1 schema は removed root fields を拒否し、typed evaluator は normalized atoms / molecules だけを読む。 | partial | #1837, #1843 |
| 473-490 | Normalizer registry は AtomKind / Axis mapping、valence template、generated molecule criteria、blockedForNormalization criteria を公開する。 | `NormalizedArchMapV1` はあるが、registry manifest として外部化された normalizer contract は薄い。composition / required port が positive evaluator basis の条件として十分に固定されていない。 | partial | #1841, #1837 |
| 503-516 | removed v0 fields は replacement registry によって evaluator output へ置換する。削除 field を単に無視するだけでは acceptance 不合格。 | `build_typed_analysis_packet_v1` の non-conclusion は v0 helper fields を読まないと明記するが、replacement registry と replacement output refs は未実装。 | missing | #1837 |
| 507 | `semanticObservations` は `semantic` atom、`semantic.interpretation@1` normalizer、semantic evaluator basis refs へ置換する。 | `semantic` atom kind は存在するが、`semantic.interpretation@1` replacement evaluator と basis refs は確認できない。 | missing | #1837, #1843 |
| 508 | `projectionInfo` は normalized atoms 上の `projection.reading@1` evaluator output とする。 | v1 packet に `observationProjectionReadings` / projection replacement refs はない。 | missing | #1837, #1836 |
| 509 | `operationSquareEvidence` は normalized relations / molecule candidates から square / commutation / holonomy evaluator readings として出す。 | v1 packet に `operationSquareCandidates`, `pathHomotopyDiagramReadings`, `homotopyHolonomyReadings`, `architectureHomotopyReport` はない。 | missing | #1837, #1839 |
| 510 | `concernHints` は diagnostic input ではなく、concern-only artifact は measured result を作らない。 | v1 removed fields rejection はあるが、concern-only negative fixture と replacement policy の coverage は未十分。 | partial | #1837, #1843 |
| 511 | `observationGaps` は authored gap ではなく evaluator requirements と atoms から missing evidence として生成する。 | typed evaluator は missing support を `blocked` にするが、rich missing-evidence / coverage-gap output は戻っていない。 | partial | #1837, #1845 |
| 512 | `nonConclusions` は schema / manifest / analysis output が運ぶ。prose は blocker / safe result を作らない。 | v1 packet / summary は non-conclusions を持つが、manifest / replacement registry と結びついた boundary output は未十分。 | partial | #1837, #1845 |
| 518-534 | validation failure 時は raw packet / summary / viewer を出さず、stale success artifact を今回 run の成功 artifact として読ませない。 | validation / preflight failure では `remove_analyze_success_artifacts` が呼ばれる。一方で `--strict-distance` failure は現状 summary / viewer / manifest を書いた後に非ゼロ終了するため、failure class ごとの artifact policy が test で固定されていない。 | partial | #1843 |
| 536-552 | implementation plan は normalizer registry、removed field replacement registry、packet replacement、distance replacement、v1 golden corpus、FieldSig handoff を要求する。 | input model、validation、normalization、typed evaluator、basic architecture distance はある。replacement registry、rich packet replacement、FieldSig v1 handoff、v1 golden corpus が未完了。 | partial | #1837, #1840, #1838, #1839, #1836, #1842, #1843 |
| 579-587 | evaluator registry manifest は required atom / molecule shape、scope rule、missing blocker、pass / violation criteria、distance contribution、summary / detail output refs、negative fixtures を持つ。 | static registry は `solid@1` と layering evaluator を持つが、replacement evaluators、spectrum / homotopy / structural evaluators、packet refs は不足。 | partial | #1837, #1840 |
| 589-596 | typed evaluator pipeline は first-class statuses を持ち、missing を zero にしない。 | `TypedEvaluatorResultV1` は `measuredPass`, `measuredViolation`, `blocked` を扱う。`unknown` / `unmeasured` の first-class generation は限定的。 | partial | #1837, #1843 |
| 598-604 | packet / distance / summary は v0 `signatureAxes` / `obstructionCircuits` 前提から typed evaluator result + derived packet refs 前提へ置換する。 | v1 packet は typed evaluator result と architecture distance を埋めるが、derived obstruction / signature refs はない。 | missing | #1840 |
| 600-602 | `analysis/distance/*` は `part4DistanceProfile` ではなく evaluator registry distance contribution と typed evaluator result から計算する。 | `architecture-distance/v1` は atom / configuration / signature / operation distance を出すが、curvature / homotopy / representation distance は戻っていない。 | partial | #1838, #1839, #1843 |
| 603-604 | summary / viewer / detail index は typed evaluator result と derived packet refs 前提へ置換する。 | summary / viewer / detail index は出るが、spectrum / homotopy / structural refs を持たない。 | partial | #1845 |
| 610-614 | v1 path を追加し、minimal / practical / SOLID / negative / golden packet を v1 で作り直す。 | minimal / practical / archmap_v1 fixtures はあるが、output replacement golden corpus ではない。 | partial | #1843 |
| 616-674 | acceptance criteria 全体。 | ArchMap input boundary と basic v1 chain は満たす。output replacement, rich v1 packet, FieldSig handoff, docs / skills / website sync は未完了。 | partial | #1835 children |

## Output Surface Gap Ledger

| Surface | v0 rich packet evidence | Current v1 runtime state | Gap classification | Tracking issue |
| --- | --- | --- | --- | --- |
| generated law inputs | v0 packet has `generatedLawInputs`. | v1 packet has only typed evaluator result entries and detail refs. | implementation gap | #1840 |
| obstruction circuits / generated obstructions | v0 packet has `obstructionCircuits` and `generatedObstructions`. | v1 packet has no derived obstruction surface. | implementation gap | #1840 |
| signature axes | v0 packet has `signatureAxes`. | v1 distance has signature distance readings, but packet lacks law-axis refs equivalent to derived signature output. | implementation gap | #1840 |
| generated repair targets | v0 packet has `generatedRepairTargets` / repair candidates. | v1 packet has no repair target surface. | implementation gap | #1840, #1836 |
| ArchitectureSpectrumReport | v0 fixture locks `architectureSpectrumReport`. | v1 practical packet does not include it. | implementation gap | #1838 |
| ACTS curvature / transfer readings | v0 packet has curvature support / transfer / mass readings. | v1 architecture distance has no curvature family. | implementation gap | #1838 |
| ArchitectureHomotopyReport | v0 fixture locks `architectureHomotopyReport`. | v1 practical packet does not include it. | implementation gap | #1839 |
| homotopy / holonomy / Stokes readings | v0 packet has path pairs, loops, fillers, holonomy, Stokes, homotopy distance. | v1 packet has no homotopy family. | implementation gap | #1839 |
| structuralReadingReviewSurface | v0 packet has structural review surface and many cross-reading summaries. | v1 packet has no structural reading surface. | implementation gap | #1836 |
| summary rich reading | v0 summary docs describe qualityMeasurement, trendDiagnosis, reviewSupport, hotspots, holes, action queue. | v1 summary is conclusion-first but mostly typed evaluator + distance. | implementation gap | #1845 |
| viewer overlays | v0 viewer docs include report panes / overlays for rich packet refs. | v1 viewer data is bounded to typed atom / molecule / distance overlays. | implementation gap | #1845 |
| FieldSig handoff | docs historically use `archsig-analysis-packet-v0` as bounded current AAT structural state. | v1 raw packet is not equivalent and FieldSig compatibility is not proven. | integration gap | #1842 |
| PR review structural diagnosis | v0 PR review had base/head packet, path movement, safe budget. | v1 `pr-review` is typed evaluator status over base + delta. | implementation gap | #1846 |

## Test And Fixture Gap Ledger

| Test obligation | Current evidence | Status | Tracking issue |
| --- | --- | --- | --- |
| unknown atom kind / unknown predicate / unresolved source ref fail before analysis | v1 CLI tests exist. | done | closed #1812 |
| valid ArchMap atoms normalize | v1 normalized ArchMap tests exist. | done | closed #1813 |
| removed-field-only fixture does not become measured result | v1 legacy root field rejection exists, but replacement-specific negative corpus is incomplete. | partial | #1837, #1843 |
| label-only atom does not become measured result | not enough evidence in current v1 golden corpus. | missing | #1843 |
| no molecule membership means no generated molecule candidate | basic checks exist, but positive basis / required port coverage is incomplete. | partial | #1843 |
| incompatible molecule or missing required port blocks positive result | `archmap_blocked_molecule` exists, but output replacement acceptance does not cover all rich surfaces. | partial | #1843 |
| evaluator missing support becomes `unknown` / `unmeasured` / `blocked`, not measured zero | blocked exists; unknown / unmeasured coverage is thin. | partial | #1837, #1843 |
| stale success artifact suppression | validation / preflight failure の stale artifact suppression はある。一方で `--strict-distance` failure は summary / viewer / manifest を書いた後に非ゼロ終了するため、failure class ごとの artifact policy と tests が不足している。 | partial | #1843 |
| positive fixture carries evaluator basis refs | typed result has basis refs, but rich derived output refs are missing. | partial | #1840, #1843 |
| v1 golden packet replaces v0 packet equality | no rich v1 golden packet corpus yet. | missing | #1843 |
| FieldSig handoff validates v1 raw packet | not proven. | missing | #1842 |

## Docs Drift Ledger

| Document | Current state | Drift | Tracking issue |
| --- | --- | --- | --- |
| `docs/tool/README.md` | Correctly states current v1 thin route and marks `ArchitectureSpectrumReport` / `ArchitectureHomotopyReport` as legacy packet reading families. | It is accurate for current runtime, but it can obscure that PRD output replacement is still incomplete. | #1841, #1844 |
| `docs/tool/archsig_analysis_packet.md` | Starts with current v1 chain, then documents legacy rich packet and desired rich reading surfaces. | Needs a clear split between current v1 runtime, legacy v0 evidence, and required v1 output replacement target. | #1844 |
| `tools/archsig/README.md` | Still introduces ArchSig as `archmap-observation-map-v0` + `law-policy-v0` -> `archsig-analysis-packet-v0`, and lists removed commands as current product surface. | Contradicts current `docs/tool/README.md` and current CLI. | #1844 |
| `tools/archsig/docs/commands.md` | Starts with current v1 route, but later sections still describe legacy command/input surfaces. | Needs pruning or legacy labeling after v1 output contract is fixed. | #1844 |
| ACTS / Homotopy validation docs | Document v0 rich fixtures as implemented. | They remain valid historical evidence, but do not prove v1 runtime output replacement. | #1844, #1838, #1839 |
| website / skills | Need verification against current v1 output once replacement surfaces are restored. | Potential docs / UX drift. | #1844, #1845 |

## Closed Issues That Are Not Sufficient Evidence

The following closed issues provide useful partial implementation evidence, but do
not prove #1835 completion:

| Closed issue | What it appears to cover | Why it is insufficient for #1835 |
| --- | --- | --- |
| #1811 | ArchMap v1 Atom-to-AAT contract epic. | Closed before output replacement gaps were re-audited against PRD acceptance. |
| #1812 | v1 input model / validation. | Covers input boundary, not rich output replacement. |
| #1813 | normalizer registry / NormalizedArchMap. | Covers normalized artifact, not replacement registry / rich packet refs. |
| #1814 | LawPolicy v1 evaluator registry / policy pack. | Current registry is thin and lacks replacement / spectrum / homotopy / structural evaluators. |
| #1815 | typed evaluator pipeline. | Covers basic typed status pipeline, not derived output surfaces. |
| #1816 | packet / distance / summary typed replacement. | Current packet remains thin; PRD replacement refs are missing. |
| #1817 | CLI / fixtures / docs migration. | Current docs still drift and fixtures do not prove rich v1 output replacement. |
| #1826-#1833 | architecture distance and summary clarity follow-up. | Adds basic distance and conclusion-first summary, but not spectrum / homotopy / structural output replacement. |

## Dependency Order

1. #1841: keep this ledger current.
2. #1837: implement replacement registry. This unlocks the rest.
3. #1840: restore derived obstruction / signature / generated packet refs.
4. #1838 and #1839: restore spectrum and homotopy families.
5. #1836: restore cross-surface structural reading.
6. #1845: synchronize summary / viewer / detail index / LLM packet with restored rich refs.
7. #1842: prove FieldSig handoff over v1 raw packet.
8. #1846: update PR review to use output replacement structural diagnosis.
9. #1843: lock v1 golden corpus and strict tests across all restored surfaces.
10. #1844: synchronize docs / skills / website after implementation surfaces settle.

## Non-Goals

- Do not put obstruction, signature, distance, homotopy, risk, projection, or
  evidence gap back into ArchMap primary JSON.
- Do not reintroduce v0 dual reader, compatibility shim, or packet equality as
  the completion target.
- Do not read source repository during `analyze` to fill missing ArchMap facts.
- Do not treat spectrum zero, homotopy fillability, or structural reading as
  Lean proof, global architecture truth, future incident prediction, or repair
  safety.

## Completion Evidence Required For #1835

#1835 can be closed only after current evidence proves all of the following:

- v1 `analyze --emit-raw-artifacts` produces a rich v1 packet with derived
  obstruction, signature, spectrum, homotopy, structural reading, summary /
  viewer / LLM refs, and FieldSig handoff support.
- Each rich surface is derived from normalized ArchMap + LawPolicy selector +
  evaluator registry + evidence contract + typed evaluator results, not from
  removed v0 input fields.
- Negative fixtures prove label-only, removed-field-only, concern-only,
  schema-only, missing support, and blocked molecule cases do not become
  measured results.
- v1 golden corpus replaces v0 packet equality as the current completion
  evidence.
- docs / skills / website describe the same current v1 output contract as the
  implementation and tests.
