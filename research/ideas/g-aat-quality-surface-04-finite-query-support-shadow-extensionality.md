---
status: picked
goal: G-aat-quality-surface-04
candidate_type: target-support
capability_category: finite-query-admissibility / support-shadow-extensionality / anti-weakening
expected_base_score: 30
expected_evidence_multiplier: 2.0
expected_final_score: 60
evidence_stage: proved-in-research
rival_advantage: Turns finite query factorization into explicit support-shadow extensionality without broadening to arbitrary semantic observations.
genius_potential: false
genius_target: not-applicable
genius_support_role: not-applicable
target_theorem: Universal Semantic Repair Obstruction Tower Theorem
target_support_node: finite query admissibility / support-shadow extensionality bridge
target_progress: support-node
proof_obligation_delta: Proves that supported finite trace-query vectors and query-generated observations are `SupportTraceShadowExtensional support`.
target_completion_role: not-completion; support-shadow extensionality bridge only.
origin: G-04 Cycle 21
tags: [target-theorem, target-support, finite-shadow, trace-support, extensionality]
created: 2026-06-25
cycle: 21
lean: research/lean/ResearchLean/AG/QualitySurface/SemanticRepairFiniteQueryExtensionality.lean
---

# Finite Query Support-Shadow Extensionality

## 主張

`QuerySupportedBy support query` の下で、finite query vector と query-generated observation は `SupportTraceShadowExtensional support` である。すなわち、同じ finite-support trace shadow を持つ二つの tower は、supported query vector と、それから生成される observation で一致する。

## 候補種別

`target-support`

## 依拠

- `SemanticRepairFiniteTraceSupport.lean`: `SupportTraceShadowExtensional` と factorization から extensionality への theorem
- `SemanticRepairFiniteQueryAdmissibility.lean`: supported query vector / generated observation factorization

## 非自明性

Cycle 20 は supported finite query observation が support shadow を通じて factor することを示した。本候補は、その結果を extensionality interface に接続する。増分は小さいが、admissible finite query class が support-shadow extensionality を満たすことを theorem 名で明示する。

## 数学的興味

factorization と extensionality の対応を、finite query class に対して固定する。これにより、同じ support trace shadow 上では supported finite query diagnostics が安定であることを直接使える。

## GOAL への前進

G-04 の admissible observation / representation adequacy blocker について、finite query-generated observation が support trace shadow に対して extensional であることを明示する。ただし canonical all-layer shadow への extensionality ではない。

## ライバルに対する有効性

bounded diagnostics は、query が support に含まれる限り、support trace shadow に対して安定である。本候補はその安定性を AAT 側の extensionality theorem として固定する。

## SCORE 見込み

- `score_reason`: Cycle 20 の factorization result を Cycle 16 の extensionality interface に接続する直接 corollary。
- `dullness_risk`: 数学的本体は Cycle 20 で済んでおり、本候補は bridge theorem に近い。
- `proof_or_evidence_plan`: `SupportTraceShadowExtensional` theorem、same-shadow corollary、Bool complete support witness を Lean に追加する。

## Target Theorem 寄与

- `target_theorem`: Universal Semantic Repair Obstruction Tower Theorem
- `target_support_node`: finite query admissibility / support-shadow extensionality bridge
- `target_progress`: support-node
- `proof_obligation_delta`: supported finite query-generated observations are support-shadow extensional.
- `target_completion_role`: not-completion; canonical all-layer shadow extensionality and arbitrary semantic observation theorem remain open.

## CS / SWE への帰結

finite query diagnostics は、query manifest が support manifest に含まれる限り、support shadow 上で安定する。これは bounded diagnostic の reproducibility property であり、whole-codebase quality や unrestricted semantic adequacy ではない。

## 証明・根拠の見込み

Lean file `SemanticRepairFiniteQueryExtensionality.lean` は次を証明する。

- `queryTraceVector_supportTraceShadowExtensional`
- `queryTraceGeneratedObservation_supportTraceShadowExtensional`
- `queryTraceVector_same_of_same_supportTraceShadow`
- `queryTraceGeneratedObservation_same_of_same_supportTraceShadow`
- `boolTrueTraceQueryGeneratedObservation_supportTraceShadowExtensional`

## 審判メモ

- 厳密性: extensionality は `SupportTraceShadowExtensional support` に限定し、canonical all-layer `ShadowExtensionalTowerObservation` とは書かない。
- 研究価値: small bridge theorem。Cycle 20 より低い SCORE にする。
- repo 全体価値: report と tracking issue では `support-node` として扱い、target completion とは書かない。

## 関連

- `g-aat-quality-surface-04-finite-query-admissibility.md`
- `SemanticRepairFiniteTraceSupport.lean`
- `SemanticRepairFiniteQueryAdmissibility.lean`

## 進捗ログ

- 2026-06-25: Cycle 21 として finite query support-shadow extensionality theorem を追加。
