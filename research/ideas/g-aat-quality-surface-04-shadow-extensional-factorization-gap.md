---
status: picked
goal: G-aat-quality-surface-04
candidate_type: target-refinement
capability_category: shadow-extensionality / assignment-factorization / target-surface / representation-adequacy / anti-weakening
expected_base_score: 68
expected_evidence_multiplier: 2.0
expected_final_score: 136
evidence_stage: proved-in-research
rival_advantage: ADL, static analyzers, conformance checkers, metric dashboards, and unlimited-context AI review can emit finite observations, but this candidate proves that canonical finite-shadow factorization requires shadow-extensionality and isolates representation adequacy as the remaining semantic assignment blocker.
genius_potential: no
genius_target: none
genius_support_role: not-applicable
target_theorem: Universal Semantic Repair Obstruction Tower Theorem
target_support_node: target-surface shadow-extensional assignment factorization and necessary-condition theorem
target_progress: target-proof-checkpoint-candidate
proof_obligation_delta: Introduces `ShadowExtensionalObstructionAssignment`, target-surface finite-shadow readings, target-surface factorization for shadow-extensional observations, and `shadowExtensional_of_factorization` as the necessary condition for any canonical finite-shadow factorization claim.
target_completion_role: checkpoint candidate; semantic soundness implying shadow-extensionality, full representation adequacy, cover/site/profile-law functoriality, and T6 `$math-lean-review` remain open.
origin: G-04
parent_tracking_issue: 2482
tags: [quality-surface, semantic-repair, target-factorization, shadow-extensionality, representation-adequacy]
created: 2026-06-25
cycle: 12
lean: proved-in-research
---

# Shadow-Extensional Factorization Gap

## 主張

Cycle 12 は、`Obs(A)` の canonical finite shadow を通る factorization を target surface 上で切り出す。同時に、canonical finite shadow を通る factorization が成立するなら observation は `ShadowExtensionalTowerObservation` でなければならない、という必要条件を Lean theorem として固定する。

これは「任意の semantic repair-gluing assignment が無条件に factor する」という主張ではない。`ShadowExtensionalObstructionAssignment` の `shadow_extensional` は visible material premise であり、full target completion では semantic soundness からこの extensionality を導くか、tower / observation 側を豊かにする必要がある。

## 候補種別

`target-refinement` / `target-obstruction`

## 依拠

- `Formal/AG/Research/QualitySurface/SemanticRepairUniversalShadow.lean`
- `Formal/AG/Research/QualitySurface/SemanticRepairTargetCompletion.lean`
- `Formal/AG/Research/QualitySurface/SemanticRepairTargetSurface.lean`
- `Formal/AG/Research/QualitySurface/SemanticRepairTargetFactorization.lean`

## 非自明性

既存 theorem は shadow-extensional finite observations の universal factorization を持っていたが、G-04 の未完 node は「arbitrary sound semantic repair-gluing assignment」が本当にその extensionality を満たすかを曖昧に残していた。この candidate は、factorization claim の必要条件を theorem として固定し、残タスクを semantic soundness -> shadow-extensionality / representation adequacy へ鋭く分解する。

## GOAL への前進

`SemanticRepairTargetFactorization.lean` に `ShadowExtensionalObstructionAssignment`、`targetSurfaceLayerShadow`、`targetSurfaceAssignmentReads`、`targetSurfaceAssignment_factors_through_ObsA_shadow`、`shadowExtensional_of_factorization`、`targetSurfaceShadowExtensionalObservation_universalFactorization`、`targetSurfaceShadowExtensionalAssignment_package` を追加する。

## SCORE 見込み

- `score_reason`: arbitrary assignment blocker を「shadow-extensionality / representation adequacy が必要」という theorem-level gap に変換する target-refinement checkpoint。
- `dullness_risk`: 新しい unrestricted universality theorem ではなく、既存 finite-shadow factorization の target-surface specialization と必要条件の整理であるため、score は Cycle 11 より低め。
- `proof_or_evidence_plan`: focused Lean、`Formal.AG.Research` / `FormalAGResearch` / full `lake build`、reported declaration の `#print axioms`、placeholder scan、T2/T4 anti-weakening review を通す。
- `score_audit`: T4 confirm as checkpoint: base 68、evidence multiplier 2.0、penalty 0、final 136。

## Target Theorem 寄与

- `target_theorem`: `Universal Semantic Repair Obstruction Tower Theorem`
- `target_support_node`: target-surface shadow-extensional assignment factorization and necessary-condition theorem
- `target_progress`: `target-proof-checkpoint-candidate`
- `proof_obligation_delta`: target surface `A` と finite certificates から作る `Obs(A)` の canonical finite shadow に対し、shadow-extensional assignment の factorization と factorization 可能性の必要条件を固定する。
- `target_completion_role`: T6 `$math-lean-review` が `No major findings` を出すまでは completion ではない。

## Material Premises

- `shadow_extensional`: visible material premise. It does not assert global coherence, tower vanish, effective descent, or target equivalence, but full target completion must discharge it from semantic soundness / representation adequacy.
- finite/small `Obs(A)`: still the finite target surface from Cycle 11.
- `UniversalSemanticRepairTargetCertificates`: finite boundary semantic closure and finite repair-list completeness only.
- finite computability boundary: `[DecidableEq Choice]`, `[DecidableEq Coherence]`, local `effectiveRepair` decidability, finite repair-order completeness.

## Anti-Weakening Verdict

`target-proof-checkpoint-candidate`。The candidate does not claim arbitrary semantic assignment universality. It proves target-surface factorization only for shadow-extensional observations and records shadow-extensionality as a necessary condition for any canonical finite-shadow factorization.

## Planned Theorem Names

- `ShadowExtensionalObstructionAssignment`
- `targetSurfaceLayerShadow`
- `shadowExtensionalAssignmentFactor`
- `shadowExtensionalAssignment_factors`
- `targetSurfaceAssignmentReads`
- `targetSurfaceAssignment_factors_through_ObsA_shadow`
- `shadowExtensional_of_factorization`
- `targetSurfaceShadowExtensionalObservation_universalFactorization`
- `targetSurfaceShadowExtensionalAssignment_package`

## Claim Boundary

finite/small target surface, finite certificates, canonical finite all-layer shadow, and shadow-extensional observations. This does not claim arbitrary semantic assignment factorization, full representation adequacy, cover/site/profile-law functoriality, true sheaf object-level universality, runtime extraction completeness, ArchMap correctness, repair synthesis completeness, or whole-codebase quality.

## Math Lean Review Scope

- GOAL claim: `research/GOALS.md` G-04 target theorem and material premise ledger.
- Candidate Lean declarations: `Formal.AG.Research.QualitySurface.SemanticRepairTargetFactorization.ShadowExtensionalObstructionAssignment`, `Formal.AG.Research.QualitySurface.SemanticRepairTargetFactorization.shadowExtensional_of_factorization`, `Formal.AG.Research.QualitySurface.SemanticRepairTargetFactorization.targetSurfaceShadowExtensionalObservation_universalFactorization`.
- Relevant files: `SemanticRepairUniversalShadow.lean`, `SemanticRepairTargetCompletion.lean`, `SemanticRepairTargetSurface.lean`, `SemanticRepairTargetFactorization.lean`.

## 証明・根拠の見込み

The Lean proof composes:

- `targetSurfaceLayerShadow`
- `shadowExtensionalObservation_factors`
- `shadowExtensionalObservation_universalFactorization`
- `canonicalTowerLayerShadow`
- `Obs_A_ofFiniteCertificates`
- `shadowExtensional_of_factorization`

## 審判メモ

- T1 obstruction: unrestricted arbitrary sound assignment factorization は不可。shadow-extensionality gap を theorem として記録すべき。
- T2 A: checkpoint accept、target-proved reject。`Obs(A)` そのものではなく `Obs(A)` の canonical finite shadow を通すと明記すべき。
- T2 B: checkpoint accept、base 68 / final 136 推奨。
- T2 C: material premise / anti-weakening は checkpoint pass。
- T2 D: checkpoint accept、base 64 / final 128 推奨。

## 関連

- `g-aat-quality-surface-04-target-srta-surface.md`
- `g-aat-quality-surface-04-sheaf-torsor-stack-integrated-completion.md`
- `g-aat-quality-surface-04-exact-finite-shadow-target-completion.md`

## 進捗ログ

- 2026-06-25: Added `SemanticRepairTargetFactorization.lean` with first-class shadow-extensional assignments, target-surface factorization, and the necessary condition `shadowExtensional_of_factorization`.
