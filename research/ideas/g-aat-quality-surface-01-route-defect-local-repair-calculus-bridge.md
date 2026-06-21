---
status: picked
goal: G-aat-quality-surface-01
candidate_type: bridge
capability_category: obstruction / repair-potential / certificate-transport / traceability / invariance / quality-surface
expected_base_score: 70
expected_evidence_multiplier: 2.0
expected_final_score: 140
evidence_stage: proved-in-research
rival_advantage: ADL / conformance checker can report selected route failures, but this bridge proves that selected route correction is an instance of a local repair support calculus and that local support elimination is equivalent to source-ref exact visualization restoration for the selected endpoint route.
origin: G-aat-quality-surface-01-cycle46
tags: [quality-surface, support-calculus, repair-hitting, exact-visualization, route-defect]
created: 2026-06-21
cycle: 46
lean: proved-in-research
---

# Route-defect local repair calculus bridge

## 主張

Cycle 43 / 44 の selected route-defect correction は、Cycle 1 の `LocalRepairSupportCalculus` の具体例として読める。selected route defect の singleton branch support family を local repair support calculus に埋め込むと、repair support が local calculus で obstruction を eliminate すること、selected packet correction が全 branch を hit すること、corrected endpoint route が source-ref exact visualization を回復することが同値になる。

## 候補種別

`bridge`

## 依拠

- `Formal/AG/Research/QualitySurface/SupportHitting.lean`
- `Formal/AG/Research/QualitySurface/SelectedRouteDefectSupportHitting.lean`
- `Formal/AG/Research/QualitySurface/SelectedRouteCorrectionExactness.lean`
- `Formal/AG/Research/QualitySurface/ExactVisualizationCriterionMinimality.lean`

## 非自明性

Cycle 43 / 44 は selected route branch と selected correction の有限 theorem だった。Cycle 46 は同じ witness を、汎用 `LocalRepairSupportCalculus` の support family / after-repair family / elimination predicate へ持ち上げる。これにより、abstract support-local repair theorem と source-ref exact visualization criterion が同じ selected endpoint route で接続される。

## 数学的興味

support-local repair theorem は単なる repair heuristic ではなく、route-level exactness restoration の証明原理として働く。selected branch を singleton support family として読むことで、missed branch survival、local support elimination、all-branch hitting、source-ref exactness が同一の support calculus に並ぶ。

## GOAL への前進

この候補は `obstruction`、`repair-potential`、`certificate-transport`、`traceability`、`invariance`、`quality-surface` を前進させ、atom-support repair calculus と selected route exactness theorem の間に再利用可能な橋を作る。

## ライバルに対する有効性

ADL / conformance checker は route mismatch や component defect を検出できるが、それを local support calculus の elimination theorem と source-ref exact visualization restoration criterion に同時に接続しない。この bridge は、検出結果を support family、repair support、exactness restoration の三層で読むための Lean-checked adapter になる。

## SCORE 見込み

- `score_reason`: Cycle 1 の abstract support theorem と Cycle 43/44 の selected route exactness theorem を接続し、support-local repair theorem を route-level exactness restoration へ transport する bridge。単なる package ではなく、local repair calculus instance、support-hit equivalence、exact visualization iff local repair eliminates を持つ。G2 B/C/D は base 75、A は revise 後 base 70 だったため、singleton selected family の限界を見て保守的に base 70、multiplier 2.0。
- `dullness_risk`: selected branch が singleton support なので、形式化が既存 theorem の言い換えに見える危険がある。`selectedRouteEliminates` を hits や packet elimination の別名ではなく `selectedRouteAfterRepair` の空性として定義し、そこから `LocalRepairSupportCalculus` の generic theorem で missed support obstruction を導くことで bridge として区別する。
- `proof_or_evidence_plan`: `SelectedRouteObstruction`、`branchSingletonSupport`、`selectedRouteLocalRepairCalculus`、`routeCorrectionSupport_hits_branch_iff`、`sourceRefRouteCorrection_supportEliminates_iff_packetEliminates`、`correctedRoute_exactVisualization_iff_localRepairEliminates`、`missedRouteBranch_obstructs_exactVisualization` を Lean で証明した。

## CS / SWE への帰結

route mismatch を「違反の有無」だけでなく、local support family と repair support に変換して exact visualization restoration と同値に扱える。これは tooling 実装 claim ではなく、selected finite source-ref endpoint route 上の formal adapter theorem である。

## 証明・根拠の見込み

Lean file: `Formal/AG/Research/QualitySurface/RouteDefectLocalRepairCalculusBridge.lean`

Planned / proved declarations:

- `SelectedRouteObstruction`
- `branchSingletonSupport`
- `selectedRouteLocalRepairCalculus`
- `routeCorrectionSupport`
- `routeCorrectionSupport_hits_branch_iff`
- `selectedRouteLocalRepair_eliminates_iff_hits`
- `sourceRefRouteCorrection_supportEliminates_iff_packetEliminates`
- `correctedRoute_exactVisualization_iff_localRepairEliminates`
- `missedRouteBranch_obstructs_exactVisualization`
- `routeDefectLocalRepairCalculusBridge_package`

Verification:

- `lake env lean Formal/AG/Research/QualitySurface/RouteDefectLocalRepairCalculusBridge.lean`: pass
- `lake build FormalAGResearch`: pass
- `#print axioms` for reported declarations: first support/adapter declarations have no 公理依存; theorem declarations using the `Set`-based local repair calculus depend only on standard `propext`, `Classical.choice`, and `Quot.sound`.
- Forbidden-token scan over the Cycle 46 Lean/card files: no matches.
- G3 公理監査: pass。`sorryAx` and nonstandard axioms are absent; standard axioms come from the existing `Set`-based `LocalRepairSupportCalculus` theorem path.
- G3 Lean 形式化品質監査: pass。`selectedRouteEliminates` is after-repair family emptiness, not a circular alias for hits or packet elimination.

Boundary:

- selected finite source-ref endpoint route、selected route defect atom / branch vocabulary、selected correction semantics に相対化する。
- global repair planner、canonical runtime patch、source extraction completeness、ArchMap correctness、whole-codebase quality、全 route family の complete coverage は主張しない。

## 審判メモ

- 厳密性: revise / base 70。方向と boundary は妥当だが、`Eliminates` を hits や packet elimination として定義すると循環的になる危険がある。実装では `selectedRouteEliminates` を after-repair family の空性として定義し、この revise を解消した。
- 研究価値: accept / base 75。Cycle 1 の support calculus と Cycle 43/44 の route exactness theorem をつなぐ theorem bridge として有効。
- repo 全体価値: accept / base 75。Research / Lean / paper seed に自然に接続し、protected math docs や tooling claim へ越境しない。
- ライバル比較: accept / base 75。ADL / conformance checker の route mismatch detection を、local support elimination、all-branch hitting、exact visualization restoration の同値へ持ち上げる。
- G3 公理監査: pass。標準公理依存は `Set` support calculus の generic theorem 経路に由来し、候補固有の未証明公理や `sorryAx` はない。x2.0 multiplier 可。
- G3 形式化品質監査: pass。selected finite endpoint route の bridge theorem として候補主張に対応し、global repair planner や tooling correctness へ越境していない。

## 関連

- Cycle 1: `Minimal-support hitting theorem for local repair`
- Cycle 43: `Selected route defect support hitting theorem`
- Cycle 44: `Selected route correction exactness theorem`
- Cycle 45: `Loss-aware commutator atlas adequacy`

## 進捗ログ

- 2026-06-21: Cycle 46 候補として作成。
- 2026-06-21: G2 A の revise を反映し、`Eliminates` を after-repair family の空性として定義する Lean 実装を追加。Lean 単体チェックは pass。
- 2026-06-21: `lake build FormalAGResearch`、公理監査、形式化品質監査は pass。SCORE 見込みを保守的に base 70 / final 140 へ同期。
