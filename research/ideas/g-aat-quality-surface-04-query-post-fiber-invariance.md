---
status: picked
goal: G-aat-quality-surface-04
candidate_type: target-support
capability_category: finite-query-current-shadow / post-fiber-invariance / anti-weakening
expected_base_score: 42
expected_evidence_multiplier: 2.0
expected_final_score: 84
score_note: Gives an exact observation-level criterion for finite query-generated current-shadow factorization and subsumes the coordinate and reading-insensitive routes as sufficient conditions.
evidence_stage: proved-in-research
rival_advantage: Replaces ad hoc finite query factorization assumptions with an exact post-map invariance condition over current-shadow fibers.
genius_potential: false
genius_target: not-applicable
genius_support_role: not-applicable
target_theorem: Universal Semantic Repair Obstruction Tower Theorem
target_support_node: finite query post-map fiber invariance criterion
target_progress: support-node
proof_obligation_delta: Characterizes observation-level current-shadow extensionality of finite query-generated observations by post-map invariance over query-reading fibers at each current shadow.
target_completion_role: not-completion; semantic soundness still does not imply post-fiber invariance for arbitrary semantic observations.
material_premises: QueryPostInvariantOnCurrentShadowFibers for arbitrary post-map factorization
premise_discharge_status: exact criterion proved; semantic-soundness extraction not discharged
new_material_premise: no hidden premise; `QueryPostInvariantOnCurrentShadowFibers` is an explicit undischarged condition equivalent to generated observation shadow-extensionality
anti_weakening_verdict: pass as support-node; fail if treated as arbitrary semantic observation factorization
origin: G-04 Cycle 28
tags: [target-theorem, target-support, finite-query, current-shadow, fiber-invariance]
created: 2026-06-25
cycle: 28
lean: research/lean/ResearchLean/AG/QualitySurface/SemanticRepairFiniteQueryPostFiberInvariance.lean
---

# Query Post Fiber Invariance

## 主張

finite query-generated observation が current canonical shadow で factor することは、`post` が同じ current shadow 上で実現可能な query-reading fiber を区別しないことと同値である。

これは Cycle 26 の query-coordinate route と Cycle 27 の reading-insensitive route を統合する exact observation-level criterion である。

## 候補種別

`target-support`

## 依拠

- `SemanticRepairFiniteQueryCurrentShadowCoordinates.lean`: query-coordinate sufficient route
- `SemanticRepairFiniteQueryReadingInsensitive.lean`: reading-insensitive sufficient route
- `SemanticRepairFiniteQueryObservation.lean`: finite query-generated observation package

## 非自明性

query vector 自身の extensionality と observation-level factorization は同じではない。post-map が current-shadow fiber 上で readings の違いを潰す場合だけ、generated observation は current shadow へ落ちる。本候補はその条件を exact iff として切る。

## 数学的興味

finite query factorization の残 premise を、coordinate completeness でも total reading-insensitivity でもなく、current-shadow fiber 上の post-map invariance として抽出する。これは semantic soundness extraction の次の target を明確にする。

## GOAL への前進

G-04 の finite-query representation boundary を、観測レベルで必要十分な不変性条件に置き換える。まだ semantic soundness からこの不変性を出していないため completion ではないが、残 premise が exact になる。

## ライバルに対する有効性

bounded diagnostic / ADL query が current shadow へ落ちるかどうかを、query coordinate の全保存ではなく post-map の fiber invariance で判定できる。これにより過剰な coordinate preservation 要求と無根拠な arbitrary observation factorization の両方を避けられる。

## SCORE 見込み

- `score_reason`: observation-level current-shadow factorization の exact iff を与え、過去2 cycle の sufficient routes を同じ criterion に吸収する。
- `dullness_risk`: semantic soundness から post-fiber invariance を導くわけではなく、arbitrary semantic observation factorization は未完。
- `proof_or_evidence_plan`: realizable query-reading fiber、post-fiber invariance、observation-level iff、finite query package factorization、coordinate / reading-insensitive sufficient routes を Lean に追加する。

## Target Theorem 寄与

- `target_theorem`: Universal Semantic Repair Obstruction Tower Theorem
- `target_support_node`: finite query post-map fiber invariance criterion
- `target_progress`: support-node
- `proof_obligation_delta`: finite query-generated observation factorization is exactly post-map invariance on current-shadow query-reading fibers.
- `target_completion_role`: not-completion; semantic soundness -> post-fiber invariance remains open.

## CS / SWE への帰結

diagnostic query が source trace を読んでも、最終 readout が same-current-shadow fiber 上で不変なら current shadow analysis に落ちる。逆に post-map が fiber 上の readings を区別するなら current shadow だけでは不足する。

## 証明・根拠の見込み

Lean file `SemanticRepairFiniteQueryPostFiberInvariance.lean` は次を定義・証明する。

- `QueryReadingsRealizableAtCurrentShadow` (definition)
- `QueryPostInvariantOnCurrentShadowFibers` (definition)
- `queryReadingsRealizableAtCurrentShadow_self`
- `queryTraceGeneratedObservation_shadowExtensional_of_postInvariantOnCurrentShadowFibers`
- `postInvariantOnCurrentShadowFibers_of_queryTraceGeneratedObservation_shadowExtensional`
- `queryTraceGeneratedObservation_shadowExtensional_iff_postInvariantOnCurrentShadowFibers`
- `finiteTraceQueryObservation_shadowExtensional_iff_postInvariantOnCurrentShadowFibers`
- `finiteTraceQueryObservation_eq_canonicalShadowFactor_of_postInvariantOnCurrentShadowFibers`
- `postInvariantOnCurrentShadowFibers_of_queryCoordinateCurrentShadowExtensional`
- `postInvariantOnCurrentShadowFibers_of_queryReadingsInsensitive`

## 審判メモ

- 厳密性: exact iff は finite query-generated observation に限定する。
- 研究価値: 残 premise を hidden factorization assumption ではなく fiber invariance として露出する。
- repo 全体価値: report と tracking issue では `support-node` として扱い、target completion とは書かない。

## 関連

- `g-aat-quality-surface-04-finite-query-current-shadow-coordinates.md`
- `g-aat-quality-surface-04-query-reading-insensitive-boundary.md`
- `SemanticRepairFiniteQueryPostFiberInvariance.lean`

## 進捗ログ

- 2026-06-25: Cycle 28 として finite query post-map fiber invariance criterion を追加。
