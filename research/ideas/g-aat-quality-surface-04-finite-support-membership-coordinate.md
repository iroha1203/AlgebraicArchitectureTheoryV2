---
status: picked
goal: G-aat-quality-surface-04
candidate_type: target-support
capability_category: finite-trace-support / membership-coordinate-factorization / anti-weakening
expected_base_score: 32
expected_evidence_multiplier: 2.0
expected_final_score: 64
evidence_stage: proved-in-research
rival_advantage: Separates the positive finite-support guarantee from unsupported completeness claims: listed coordinates factor, unlisted coordinates still require extra evidence.
genius_potential: false
genius_target: not-applicable
genius_support_role: not-applicable
target_theorem: Universal Semantic Repair Obstruction Tower Theorem
target_support_node: finite-computable-shadow / source-trace support boundary
target_progress: support-node
proof_obligation_delta: Proves that a source-trace coordinate explicitly present in the finite support list factors through the finite-support trace shadow, and records the Cycle 17 `false` coordinate positive witness.
target_completion_role: not-completion; positive finite-support boundary support lemma.
origin: G-04 Cycle 18
tags: [target-theorem, target-support, finite-shadow, trace-support, membership]
created: 2026-06-25
cycle: 18
lean: research/lean/ResearchLean/QualitySurface/SemanticRepairFiniteSupportMembership.lean
---

# Finite Support Membership Coordinate Factorization

## 主張

finite support trace shadow は、support list に明示的に含まれる source-trace coordinate については factorization を与える。つまり `atom ∈ support` なら、`T.sourceTraceToken atom` は `canonicalSupportTraceProbeTowerLayerShadow support T` を通じて factor する。

## 候補種別

`target-support`

## 依拠

- `SemanticRepairFiniteTraceSupport.lean`: support trace vector と finite-support trace shadow
- `SemanticRepairFiniteSupportSeparation.lean`: support 外 coordinate の missed-coordinate boundary

## 非自明性

Cycle 17 は support 外 coordinate が落ちうることを示した。本候補はその正側を閉じる。support 内 coordinate は読めるが、support 外 coordinate、任意 observation、full trace adequacy までは主張しない。

## 数学的興味

finite support trace shadow を projection として読むと、projection の像に含まれる coordinate は recoverable であり、projection 外の coordinate は追加 certificate なしには recoverable でない。本候補はこの membership-local recovery を theorem として固定する。

## GOAL への前進

G-04 の finite computable shadow adequacy / source-trace support boundary について、support list が保証する最小の positive property を明示し、Cycle 17 の missed-coordinate obstruction と対にする。

## ライバルに対する有効性

source-reference support list を使う tooling は、support に含めた coordinate については trace reading を保持できる。本候補はその保証を AAT 側の theorem に落とし、support completeness や runtime extraction を別問題として残す。

## SCORE 見込み

- `score_reason`: small but useful support-node。Cycle 17 の negative boundary と対になる positive membership factorization を Lean に固定する。
- `dullness_risk`: theorem は structural recursion で小さい。full adequacy への寄与は限定的。
- `proof_or_evidence_plan`: `SemanticRepairFiniteSupportMembership.lean` で membership-local coordinate factorization、same-shadow extensional theorem、Cycle 17 `false` coordinate witness を証明する。

## Target Theorem 寄与

- `target_theorem`: Universal Semantic Repair Obstruction Tower Theorem
- `target_support_node`: finite-computable-shadow / source-trace support boundary
- `target_progress`: support-node
- `proof_obligation_delta`: listed source-trace coordinates factor through the finite-support trace shadow.
- `target_completion_role`: not-completion; finite support/probe completeness and admissible-observation theorem remain open.

## CS / SWE への帰結

finite support trace diagnostics は、support に含めた source coordinate については保証を持てる。ただし support をどう選ぶか、support が complete か、runtime source extraction が正しいかは別 certificate の責務である。

## 証明・根拠の見込み

Lean file `SemanticRepairFiniteSupportMembership.lean` は次を証明する。

- `sourceTraceCoordinateObservation`
- `supportTraceShadowTail`
- `supportTraceShadowTail_cons`
- `sourceTraceCoordinate_factors_through_supportTraceProbeShadow`
- `sourceTraceCoordinateObservation_factors_through_supportTraceShadow_of_mem`
- `sourceTraceCoordinate_same_of_same_supportTraceProbeShadow`
- `false_mem_boolFalseOnlyTraceSupport`
- `boolFalseTraceObservation_factors_through_boolFalseOnlySupport`
- `boolFalseTraceObservation_same_on_missedTrue_pair`

## 審判メモ

- 厳密性: T1 は Lean feasible と判定。`DecidableEq Atom`、`NoDup support`、minimality は不要。
- 研究価値: positive half として有用だが小さいため、`target-support` / low score に留める。
- repo 全体価値: report と tracking issue では `support-node` として扱い、target completion とは書かない。

## 関連

- `g-aat-quality-surface-04-finite-trace-support.md`
- `g-aat-quality-surface-04-finite-support-missed-coordinate.md`
- `SemanticRepairFiniteTraceSupport.lean`
- `SemanticRepairFiniteSupportSeparation.lean`

## 進捗ログ

- 2026-06-25: T1 で `target-support` として採択し、Lean membership-local factorization を追加。
