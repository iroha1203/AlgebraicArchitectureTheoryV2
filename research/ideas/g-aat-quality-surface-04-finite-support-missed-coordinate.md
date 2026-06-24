---
status: picked
goal: G-aat-quality-surface-04
candidate_type: target-refinement
capability_category: finite-trace-support-boundary / missed-coordinate-separation / anti-weakening
expected_base_score: 48
expected_evidence_multiplier: 2.0
expected_final_score: 96
evidence_stage: proved-in-research
rival_advantage: Prevents finite support trace shadows from being misread as complete trace capture by fixing a concrete omitted-coordinate separation witness.
genius_potential: false
genius_target: not-applicable
genius_support_role: not-applicable
target_theorem: Universal Semantic Repair Obstruction Tower Theorem
target_support_node: finite trace-probe representation boundary
target_progress: target-refined
proof_obligation_delta: Proves a generic same-support-shadow separation theorem and a concrete Bool witness showing that support `[false]` cannot factor an observation of the omitted `true` trace coordinate.
target_completion_role: checkpoint only; does not prove full trace incompleteness, arbitrary support incompleteness, or finite probe completeness.
origin: G-04 Cycle 17
tags: [target-theorem, target-refinement, finite-shadow, trace-support, missed-coordinate]
created: 2026-06-25
cycle: 17
lean: Formal/AG/Research/QualitySurface/SemanticRepairFiniteSupportSeparation.lean
---

# Finite Support Missed Coordinate Boundary

## 主張

finite support trace shadow は、その support が読まない source-trace coordinate を一般には保持しない。具体的には、`Bool` atom 上で support `[false]` を固定すると、`true` 座標だけを変えた二つの tower は同じ support trace shadow を持つが、`true` 座標を読む observation はそれらを分離する。したがってその observation は support trace shadow を通じて factor できない。

## 候補種別

`target-refinement`

## 依拠

- `SemanticRepairFiniteTraceSupport.lean`: finite support trace shadow
- `SemanticRepairTraceProbeShadow.lean`: trace-probe shadow factorization boundary
- `SemanticRepairTargetCompletion.lean`: representative tower and canonical shadow

## 非自明性

Cycle 16 は finite support trace shadow を導入した。本候補は、その support shadow を full trace completeness と読んではいけないことを concrete witness と generic no-factor theorem で固定する。これは target theorem completion ではなく、anti-weakening boundary の refinement である。

## 数学的興味

finite support は projection であり、projection が落とした coordinate に依存する observation は同一 support shadow 上で値を分離しうる。本候補は、support list が何を読まないかを theorem-level に露出させる。

## GOAL への前進

G-04 の finite probe completeness / admissible observation theorem について、finite support shadow だけでは omitted coordinate observation を扱えないことを明示し、次に必要な support completeness certificate または admissible observation restriction を具体化する。

## ライバルに対する有効性

source reference / trace token を持つ tooling は、どの coordinate が support に含まれていないかを明示しなければならない。本候補は、support 外 coordinate を落とす診断の限界を AAT 側の theorem として固定する。

## SCORE 見込み

- `score_reason`: finite support trace shadow の過大解釈を防ぐ missed-coordinate witness と no-factorization theorem を Lean に固定する。
- `dullness_risk`: witness は小さいが、Cycle 16 refinement の claim boundary を fail-closed に保つ価値がある。
- `proof_or_evidence_plan`: `SemanticRepairFiniteSupportSeparation.lean` で generic no-factor theorem、Bool missed-coordinate pair、support shadow equality、observation separation、no factorization を証明する。

## Target Theorem 寄与

- `target_theorem`: Universal Semantic Repair Obstruction Tower Theorem
- `target_support_node`: finite trace-probe representation boundary
- `target_progress`: target-refined
- `proof_obligation_delta`: fixed finite witness that omitted support coordinates can block support-shadow factorization.
- `target_completion_role`: checkpoint only; target theorem completion still requires finite support/probe completeness or a non-circular admissible observation theorem.

## CS / SWE への帰結

finite support trace diagnostics は、support 外の provenance / trace coordinate を見落とす。tooling 側で support completeness を主張するなら、別の certificate が必要である。

## 証明・根拠の見込み

Lean file `SemanticRepairFiniteSupportSeparation.lean` は次を証明する。

- `no_supportTraceShadowFactor_of_sameShadow_observation_ne`
- `boolFalseOnlyTraceSupport`
- `boolTraceBaseTower`
- `boolTraceMissedTrueTower`
- `boolMissedTraceObservation`
- `bool_missedTrue_same_supportTraceShadow`
- `boolMissedTraceObservation_separates_pair`
- `boolMissedTraceObservation_no_supportTraceShadowFactor`
- `bool_missedTrue_same_currentShadow`

## 審判メモ

- 厳密性: T1 は Bool missed-coordinate witness を有効と判定したが、任意 support / 任意 omitted coordinate へ一般化しないよう警告した。
- 研究価値: finite support trace shadow の過大解釈を防ぐ refinement として採択する。
- repo 全体価値: report と tracking issue では `target-refined` として扱い、full trace incompleteness や target completion とは書かない。

## 関連

- `g-aat-quality-surface-04-finite-trace-support.md`
- `SemanticRepairFiniteTraceSupport.lean`

## 進捗ログ

- 2026-06-25: T1 で `target-refinement` として採択し、Lean witness を追加。
