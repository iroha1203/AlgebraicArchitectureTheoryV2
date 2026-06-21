---
status: picked
goal: G-aat-quality-surface-01
candidate_type: orientation / heterogeneous-interaction
capability_category: profile-curvature / certificate-transport / obstruction / repair-potential / traceability / quality-surface
expected_base_score: 80
expected_evidence_multiplier: 2.0
expected_final_score: 160
evidence_stage: proved-in-research
rival_advantage: ADL / conformance tools can list per-route exactness and cross-route constraints, but this candidate turns support / trace / repair-frontier bridge failure into an obstruction certificate tied to interaction exactness.
origin: cycle-57
tags: [quality-surface, heterogeneous-route, interaction, curvature]
created: 2026-06-21
cycle: 57
lean: Formal/AG/Research/QualitySurface/HeterogeneousRouteInteraction.lean
---

# Heterogeneous route bridge obstruction

## 主張

selected correction route の local exactness と、finite scan route-family の local exactness を別々に満たしても、
support / trace / repair-frontier からなる cross-route bridge certificate が落ちれば heterogeneous interaction exactness は成り立たない。
したがって heterogeneous route family の exact locus は、local exactness の product だけでは読めない。

## 候補種別

`orientation`

## 依拠

- Cycle 48: parametrized selected correction system
- Cycle 53-56: finite route-family exact locus、finite scan、ordered first-failing selector

## 非自明性

Cycle 52-56 は homogeneous staged route family と scan surface を扱った。
本候補は selected correction route と route-family scan という異なる exactness notion を同じ state に載せ、
local exactness product と cross-route bridge obstruction certificate を分離する。

## 数学的興味

Quality Surface 上の route family は、per-route green status の product だけではない。
別 route の correction / scan surface を接続する bridge certificate の trace handoff component が落ちると、
local exactness は保たれていても interaction cell は obstructed になる。

## GOAL への前進

heterogeneous route interaction frontier を開き、certificate transport と obstruction を product exactness から分離する。

## ライバルに対する有効性

ADL / conformance checker は route ごとの pass/fail や cross-route constraint violation を表示できるが、
AAT 側ではその failure を support / trace / repair-frontier component を持つ bridge obstruction certificate として
interaction exactness に接続する。

## SCORE 見込み

- `score_reason`: homogeneous route-family scan から heterogeneous interaction exactness へ進み、product-locus view を有限 witness で壊す。ただし bridge certificate はまだ supplied evidence contract であり derived invariant ではないため、G2 revise 後は base 80 を見込む。
- `dullness_risk`: bridge law を任意 Bool として置くだけなら dull。revise により support / trace / repair-frontier component を持つ bridge certificate と obstruction object にした。
- `proof_or_evidence_plan`: Lean で heterogeneous state、selected local exactness、scan local exactness、bridge certificate、bridge obstruction、interaction exactness、product-local-exact but not interaction-exact witness、bridge-aligned positive witness を証明する。

## CS / SWE への帰結

複数 route の dashboard がすべて green でも、route 間の handoff / bridge law が落ちれば interaction としては exact でない、という certificate-level explanation を持てる。
ただし bridge law は supplied evidence contract であり、runtime repair synthesis や source extraction completeness は主張しない。

## 証明・根拠の見込み

Lean file `HeterogeneousRouteInteraction.lean` に置く。
主要 declaration は `heterogeneousProductExact_not_interactionExact`、
`heterogeneousInteractionExact_implies_productLocalExact`、
`bridgeObstruction_obstructs_interactionExact`、
`heterogeneousInteractionExact_implies_bridgeAligned`、
`bridgeAlignedInteractionState_interactionExact`、
`sameLocalProduct_differentInteractionExactness`、
`heterogeneousRouteInteraction_package`。

## 審判メモ

- 厳密性: accept after one revise; base 80. First G2 A rejected the naked Bool bridge as too definitional. Revised to a support / trace / repair-frontier `BridgeCertificate` with explicit `BridgeObstruction`.
- 研究価値: accept; base 80. Product-local-exactness と heterogeneous interaction exactness の分離は frontier を進めるが、bridge はまだ supplied contract なので base 90 ではない。
- repo 全体価値: accept; base 80. Future tooling / website surface として有効だが、bridge law は supplied evidence contract として扱う必要がある。
- ライバル比較: accept after one revise; base 80. First G2 D noted that ADL can also express cross-route constraints. Revised to make the advantage the certificate-bearing bridge obstruction, not merely an extra Boolean check.
- G3: `lake env lean` and `lake build FormalAGResearch` pass. `BridgeCertificate` / `BridgeObstruction` / concrete trace obstruction are axiom-free; package and local exactness witnesses inherit standard `propext` / `Quot.sound` from imported exactness infrastructure.
- genius: not eligible. All G2 judges treated this as a normal orientation / obstruction result, not a 1000-point breakthrough.

## 関連

- `Formal/AG/Research/QualitySurface/ParametrizedSelectedCorrectionSystem.lean`
- `Formal/AG/Research/QualitySurface/OrderedScanFirstFailingSlot.lean`

## 進捗ログ

- 2026-06-21: cycle 57 candidate picked for G2/G3.
