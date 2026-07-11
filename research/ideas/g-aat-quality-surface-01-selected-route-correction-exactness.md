---
status: picked
goal: G-aat-quality-surface-01
candidate_type: closure
capability_category: obstruction / repair-potential / certificate-transport / traceability / quality-surface
expected_base_score: 70
expected_evidence_multiplier: 2.0
expected_final_score: 140
evidence_stage: proved-in-research
rival_advantage: ADL / conformance checker can detect route mismatch, but this result proves that selected branch hitting is equivalent to empty protected route support and source-ref exact visualization for the corrected endpoint route.
origin: G-aat-quality-surface-01-cycle44
tags: [quality-surface, route-defect-support, exact-visualization, repair-hitting]
created: 2026-06-21
cycle: 44
lean: proved-in-research
---

# Selected route correction exactness theorem

## 主張

Cycle 43 の selected protected-component correction を off-selected flatness と合成すると、corrected visible route endpoint について、全 selected route-defect branch を hit すること、protected route support が空になること、source-ref exact visualization が回復することが同値になる。all-branch correction は exact visualization を回復し、obligation-only correction は storage repair branch を miss するため exactness を回復しない。

## 候補種別

`closure`

## 依拠

- `research/lean/ResearchLean/QualitySurface/SelectedRouteDefectSupportHitting.lean`
- `research/lean/ResearchLean/QualitySurface/RouteDefectSupport.lean`
- `research/lean/ResearchLean/QualitySurface/ExactVisualizationCriterionMinimality.lean`
- `research/lean/ResearchLean/QualitySurface/VisibleRepairTransportCommutator.lean`

## 非自明性

Cycle 43 は selected branch agreement に留まっていた。Cycle 44 は Cycle 38 の off-storage flatness と Cycle 42 の exact visualization criterion を合成し、selected branch hitting が corrected endpoint route 全体の protected support empty と source-ref exact visualization に一致することを証明する。単なる Bool hitting の言い換えではなく、selected correction theorem を route-support exactness theorem へ上げる。

## 数学的興味

visible tuple surface が固定されたまま、repair frontier は selected branch hitting の有無で source-ref exactness の回復 / 非回復に分かれる。これにより、support-local repair theorem が exact visualization criterion と同じ finite certificate geometry の中で接続される。

## GOAL への前進

この候補は `obstruction`、`repair-potential`、`certificate-transport`、`traceability`、`quality-surface` を前進させ、selected defect support と exact visualization restoration を一つの iff theorem に圧縮する。

## ライバルに対する有効性

ADL / conformance checker は mismatch component や route inconsistency を表示できるが、どの selected support branches を hit すれば protected route support が空になり source-ref exact visualization が回復するかを証明対象として固定しない。この結果は検出から repair-exactness criterion へ進む AAT 側の差分を与える。

## SCORE 見込み

- `score_reason`: Cycle 43 の明示的 open question を閉じ、Cycle 38/42/43 を exactness restoration iff theorem として合成する closure。G2 では研究価値 / repo 全体価値 / rival 比較が base 80、厳密性が base 70 だったため、保守的に base 70、Lean proof が未完証明なしなら multiplier 2.0。
- `dullness_risk`: Cycle 43 の近接系に見える危険がある。off-selected flatness と Cycle 42 criterion を明示的に使い、branch hit から protected route support empty / exact visualization まで到達する点を差分にする。
- `proof_or_evidence_plan`: `correctedVisibleRoute_supportEmpty_iff_hits`、`correctedVisibleRoute_exactVisualization_iff_hits`、`allRouteDefectCorrection_sourceRefExactVisualization`、`obligationOnlyCorrection_not_sourceRefExactVisualization` を Lean で証明した。

## CS / SWE への帰結

loss-aware quality view が route defect branch を表示するだけでなく、selected branch hitting が exact visualization restoration の criterion であることを説明できる。これは tooling 実装 claim ではなく、finite selected witness 上の repair-exactness theorem である。

## 証明・根拠の見込み

Lean file: `research/lean/ResearchLean/QualitySurface/SelectedRouteCorrectionExactness.lean`

Planned / proved declarations:

- `correctedVisibleRoute_supportSurface_equivalent`
- `correctedVisibleRoute_tupleVisible`
- `correctedVisibleRoute_supportEmpty_of_hits`
- `hits_every_selectedRouteDefectSupport_of_correctedSupportEmpty`
- `correctedVisibleRoute_supportEmpty_iff_hits`
- `correctedVisibleRoute_exactVisualization_iff_hits`
- `allRouteDefectCorrection_supportEmpty`
- `allRouteDefectCorrection_sourceRefExactVisualization`
- `obligationOnlyCorrection_not_supportEmpty`
- `obligationOnlyCorrection_not_sourceRefExactVisualization`
- `selectedRouteCorrectionExactness_package`

Verification:

- `lake env lean research/lean/ResearchLean/QualitySurface/SelectedRouteCorrectionExactness.lean`: pass
- `lake build ResearchLean`: pass
- `#print axioms` for all listed declarations: all `does not depend on any axioms`
- forbidden-token scan on the Cycle 44 Lean/card files: no matches

Boundary:

- selected finite source-ref packet route 上の theorem であり、global correction planner、canonical runtime patch、source extraction completeness、ArchMap correctness、whole-codebase quality は主張しない。
- exact visualization は supplied packet-to-tuple bridge と selected endpoint route に相対化される。

## 審判メモ

- 厳密性: accept / base 70。Cycle 42 / 43 の合成成分が大きいが、off-selected flatness を埋めて `RouteDefectSupportEmpty` と `SourceRefExactVisualization` へ上げる差分はある。
- 研究価値: accept / base 80。selected branch hitting、protected route support empty、source-ref exact visualization restoration を iff に圧縮する点を評価。
- repo 全体価値: accept / base 80。Research / Lean の成果として PR 価値があり、Tooling / Website には将来の loss-aware visualization surface として接続可能。
- ライバル比較: accept / base 80。route mismatch detection を越えて、repair-exactness criterion を finite certificate geometry として固定する点を評価。
- G3 公理監査: clean。listed declarations はすべて公理依存なしで、evidence multiplier x2.0 が許可された。
- G3 形式化品質監査: pass。`correctedVisibleRoute_supportEmpty_iff_hits` と `correctedVisibleRoute_exactVisualization_iff_hits` が candidate claim と対応し、global correction planner / tooling 実装 claim に越境していないことが確認された。

## 関連

- Cycle 38: `Route defect support calculus for selected repair/transport endpoints`
- Cycle 42: `Exact-visualization criterion and four-law selected minimality matrix`
- Cycle 43: `Selected route defect support hitting theorem`

## 進捗ログ

- 2026-06-21: Cycle 44 候補として作成。Lean 単体チェックと `lake build ResearchLean` は pass。
- 2026-06-21: G2 は accept。G3 で網羅的 `#print axioms` と形式化品質監査が pass。
