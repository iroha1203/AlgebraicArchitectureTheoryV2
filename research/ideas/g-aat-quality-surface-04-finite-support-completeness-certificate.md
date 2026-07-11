---
status: picked
goal: G-aat-quality-surface-04
candidate_type: target-support
capability_category: finite-trace-support-completeness / explicit-certificate / anti-weakening
expected_base_score: 42
expected_evidence_multiplier: 2.0
expected_final_score: 84
evidence_stage: proved-in-research
rival_advantage: Makes support completeness an explicit certificate rather than silently treating finite support as complete trace capture.
genius_potential: false
genius_target: not-applicable
genius_support_role: not-applicable
target_theorem: Universal Semantic Repair Obstruction Tower Theorem
target_support_node: finite-computable-shadow / source-trace support completeness certificate
target_progress: support-node
proof_obligation_delta: Defines `FiniteSupportComplete support := ∀ atom, atom ∈ support` and proves that every source-trace coordinate factors through the finite-support trace shadow under that visible certificate.
target_completion_role: not-completion; explicit finite-support completeness certificate for source-trace coordinates only.
origin: G-04 Cycle 19
tags: [target-theorem, target-support, finite-shadow, trace-support, completeness-certificate]
created: 2026-06-25
cycle: 19
lean: research/lean/ResearchLean/QualitySurface/SemanticRepairFiniteSupportCompleteness.lean
---

# Finite Support Completeness Certificate

## 主張

`FiniteSupportComplete support := ∀ atom, atom ∈ support` を明示 certificate として置くと、任意の source-trace coordinate `T.sourceTraceToken atom` は `canonicalSupportTraceProbeTowerLayerShadow support T` を通じて factor する。さらに、同じ complete support shadow を持つ二つの tower は、source-trace token の各 coordinate で pointwise に一致する。

## 候補種別

`target-support`

## 依拠

- `SemanticRepairFiniteSupportMembership.lean`: membership-local coordinate factorization
- `SemanticRepairFiniteSupportSeparation.lean`: support 外 coordinate の missed-coordinate boundary

## 非自明性

Cycle 18 は `atom ∈ support` という局所前提で coordinate factorization を示した。本候補は、その membership 証拠を `∀ atom, atom ∈ support` の explicit certificate にまとめる。support completeness を shadow や theorem package に隠さず、可視 premise として扱う。

## 数学的興味

finite support trace shadow の adequacy は、support が complete であるという証明と分離される。本候補は、complete support certificate がある場合に限って source-trace coordinate 全体を pointwise に読む theorem surface を与える。

## GOAL への前進

G-04 の finite computable shadow adequacy blocker について、support completeness certificate が何を放電し、何を放電しないかを Lean theorem として固定する。

## ライバルに対する有効性

source-reference support list を使う tooling は、support が全 source coordinate を覆うことを別 certificate として示す必要がある。本候補はその certificate の最小 theorem surface を固定する。

## SCORE 見込み

- `score_reason`: Cycle 18 membership theorem を explicit completeness certificate に持ち上げ、support completeness を hidden assumption にしない。
- `dullness_risk`: arbitrary observation adequacy ではなく source-trace coordinate pointwise theorem に限定される。
- `proof_or_evidence_plan`: `FiniteSupportComplete`、complete-support coordinate factorization、same-shadow pointwise extensionality、Bool complete support witness を Lean に追加する。

## Target Theorem 寄与

- `target_theorem`: Universal Semantic Repair Obstruction Tower Theorem
- `target_support_node`: finite-computable-shadow / source-trace support completeness certificate
- `target_progress`: support-node
- `proof_obligation_delta`: complete finite support gives pointwise source-trace coordinate factorization through support shadow.
- `target_completion_role`: not-completion; arbitrary observation factorization and admissible-observation theorem remain open.

## CS / SWE への帰結

finite support trace diagnostics が full trace capture を主張するには、support list が全 source coordinate を覆うことを明示的に証明する必要がある。本候補はその明示的 certificate がある場合の保証だけを theorem 化する。

## 証明・根拠の見込み

Lean file `SemanticRepairFiniteSupportCompleteness.lean` は次を証明する。

- `FiniteSupportComplete`
- `sourceTraceCoordinate_factors_through_completeSupportTraceShadow`
- `sourceTraceCoordinates_same_of_same_completeSupportTraceShadow`
- `boolCompleteTraceSupport`
- `boolCompleteTraceSupport_complete`
- `boolTrueTraceObservation_factors_through_completeBoolSupport`
- `bool_missedTrue_completeSupportShadow_readings_ne`
- `boolTrueTrace_same_of_same_completeBoolSupportShadow`

## 審判メモ

- 厳密性: complete support は theorem premise として明示し、shadow field や certificate field に隠さない。
- 研究価値: Cycle 17/18 の negative/positive boundary を、explicit completeness certificate として整理する support-node。
- repo 全体価値: report と tracking issue では `support-node` として扱い、target completion とは書かない。

## 関連

- `g-aat-quality-surface-04-finite-support-membership-coordinate.md`
- `g-aat-quality-surface-04-finite-support-missed-coordinate.md`
- `SemanticRepairFiniteSupportMembership.lean`
- `SemanticRepairFiniteSupportSeparation.lean`

## 進捗ログ

- 2026-06-25: Cycle 19 として explicit complete support certificate theorem を追加。
