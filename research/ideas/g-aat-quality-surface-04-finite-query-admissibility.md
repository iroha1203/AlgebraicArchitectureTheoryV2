---
status: picked
goal: G-aat-quality-surface-04
candidate_type: target-support
capability_category: finite-query-admissibility / query-supported-factorization / anti-weakening
expected_base_score: 40
expected_evidence_multiplier: 2.0
expected_final_score: 80
evidence_stage: proved-in-research
rival_advantage: Replaces vague admissible observation claims with an explicit finite-query support condition.
genius_potential: false
genius_target: not-applicable
genius_support_role: not-applicable
target_theorem: Universal Semantic Repair Obstruction Tower Theorem
target_support_node: non-circular admissible finite trace-query observation boundary
target_progress: support-node
proof_obligation_delta: Defines `QuerySupportedBy support query` and proves that supported finite trace-query vectors and generated observations factor through the finite-support trace shadow.
target_completion_role: not-completion; finite query-generated observations only, not arbitrary semantic observations.
origin: G-04 Cycle 20
tags: [target-theorem, target-support, finite-shadow, trace-support, admissible-query]
created: 2026-06-25
cycle: 20
lean: Formal/AG/Research/QualitySurface/SemanticRepairFiniteQueryAdmissibility.lean
---

# Finite Query Admissibility

## 主張

finite trace query `query` が support list に含まれる coordinate だけを読む、つまり `QuerySupportedBy support query := ∀ atom, atom ∈ query -> atom ∈ support` を満たすなら、`supportTraceVector query T.sourceTraceToken` は `canonicalSupportTraceProbeTowerLayerShadow support T` を通じて factor する。さらに current four-bit layer と query vector から生成される observation も同じ support shadow を通じて factor する。

## 候補種別

`target-support`

## 依拠

- `SemanticRepairFiniteSupportMembership.lean`: membership-local coordinate factorization
- `SemanticRepairFiniteSupportCompleteness.lean`: explicit complete support certificate

## 非自明性

Cycle 19 は support が全 atom を含む場合の pointwise source-trace coordinate factorization を示した。本候補は、observation が読む finite query を明示し、その query が support に含まれる場合だけ factorization を許す。これは arbitrary observation factorization ではなく、non-circular admissible finite query class の前段である。

## 数学的興味

admissibility を「support shadow がたまたま十分」と読むのではなく、observation が読む finite query と support の包含関係として明示する。これにより、factorization theorem の対象クラスが theorem statement 上で確認できる。

## GOAL への前進

G-04 の admissible observation / representation adequacy blocker について、finite query-generated observation という小さな admissible class を Lean で固定する。full semantic admissibility は残す。

## ライバルに対する有効性

source-reference support list を使う tooling は、各 diagnostic が読む query を support に対して監査できる。本候補はその bounded diagnostic claim を AAT 側の factorization theorem として表現する。

## SCORE 見込み

- `score_reason`: Cycle 18/19 の coordinate factorization を finite query-generated observation class へ持ち上げ、admissibility を explicit subset condition にする。
- `dullness_risk`: query-generated observations に限定され、arbitrary semantic observation theorem ではない。
- `proof_or_evidence_plan`: `QuerySupportedBy`、query vector factorization、query-generated observation factorization、Bool complete support witness を Lean に追加する。

## Target Theorem 寄与

- `target_theorem`: Universal Semantic Repair Obstruction Tower Theorem
- `target_support_node`: non-circular admissible finite trace-query observation boundary
- `target_progress`: support-node
- `proof_obligation_delta`: finite trace-query generated observations factor through support shadow under explicit query-support premise.
- `target_completion_role`: not-completion; arbitrary semantic observation factorization remains open.

## CS / SWE への帰結

finite trace diagnostics は、診断が読む query と support manifest の包含関係を示せば bounded factorization を持つ。この theorem は query manifest / source support manifest の責務境界を明確にする。

## 証明・根拠の見込み

Lean file `SemanticRepairFiniteQueryAdmissibility.lean` は次を証明する。

- `QuerySupportedBy`
- `queryTraceVector_factors_through_supportTraceShadow`
- `queryTraceGeneratedObservation_factors_through_supportTraceShadow`
- `boolTrueTraceQuery`
- `boolTrueTraceQuery_supportedBy_completeBoolSupport`
- `boolTrueTraceQuery_factors_through_completeBoolSupport`
- `boolTrueTraceQueryGeneratedObservation_factors`

## 審判メモ

- 厳密性: query support は theorem premise として明示する。support completeness や admissibility を hidden field にしない。
- 研究価値: arbitrary admissible observation theorem ではないが、non-circular finite query class を theorem 化する support-node。
- repo 全体価値: report と tracking issue では `support-node` として扱い、target completion とは書かない。

## 関連

- `g-aat-quality-surface-04-finite-support-membership-coordinate.md`
- `g-aat-quality-surface-04-finite-support-completeness-certificate.md`
- `SemanticRepairFiniteSupportMembership.lean`
- `SemanticRepairFiniteSupportCompleteness.lean`

## 進捗ログ

- 2026-06-25: Cycle 20 として finite query admissibility theorem を追加。
