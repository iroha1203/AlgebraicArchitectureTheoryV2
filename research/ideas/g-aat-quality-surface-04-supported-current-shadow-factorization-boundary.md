---
status: picked
goal: G-aat-quality-surface-04
candidate_type: target-support
capability_category: finite-query-representation / supported-current-shadow-factorization / support-determinacy / anti-weakening
expected_base_score: 44
expected_evidence_multiplier: 2.0
expected_final_score: 88
evidence_stage: proved-in-research
rival_advantage: support membership, query-reading recovery, and current-shadow descent adequacy are separated as theorem-level conditions rather than dashboard-style finite evidence.
genius_potential: false
genius_target: none
genius_support_role: not-applicable
target_theorem: Universal Semantic Repair Obstruction Tower Theorem
target_support_node: support-level current-shadow determinacy restricts to supported finite queries and yields current-shadow factorization only under a visible determinacy certificate
target_progress: support-node
proof_obligation_delta: Adds a reusable Lean bridge from `CurrentShadowDeterminesSupportTraceShadow support` and `QuerySupportedBy support query` to query-coordinate extensionality, query determinacy, and finite-query current-shadow factorization.
target_completion_role: support theorem package only; not target theorem completion
origin: T1-cycle43
tags: [target-theorem-loop, G-04, finite-query-representation, anti-weakening]
created: 2026-06-25
cycle: 43
lean: research/lean/ResearchLean/AG/QualitySurface/SemanticRepairFiniteQuerySupportedCurrentShadowFactorization.lean
---

# Supported Current-Shadow Factorization Boundary

## 主張

`CurrentShadowDeterminesSupportTraceShadow support` が visible theorem data として与えられ、`query` が `QuerySupportedBy support query` を満たすなら、support-level current-shadow determinacy は `query` に制限され、`QueryTraceCoordinatesCurrentShadowExtensional query` と `CurrentShadowDeterminesTraceQuery query` を与える。したがって raw query readings、finite query-generated observations、represented finite-query observations は current shadow に factor する。

この主張は `CurrentShadowDeterminesSupportTraceShadow support` 自体を discharge しない。support membership と query-reading recovery は current-shadow adequacy ではない。

## 候補種別

`target-support`

## 依拠

- `SemanticRepairFiniteQueryAdmissibility.lean`: `QuerySupportedBy`
- `SemanticRepairFiniteQueryCanonicalBridge.lean`: `CurrentShadowDeterminesSupportTraceShadow` / `CurrentShadowDeterminesTraceQuery`
- `SemanticRepairCurrentShadowCoordinateObligations.lean`: support determinacy と coordinate obligation の同値
- `SemanticRepairFiniteQueryRepresentationCoordinateExtraction.lean`: query-coordinate obligation から current-shadow factorization
- `SemanticRepairFiniteQueryRepresentationRecoveredFactorization.lean`: visible recovery 下の exact current-shadow criterion

## 非自明性

これは新しい hidden field を足すのではなく、既存の support-level determinacy premise を supported query に制限する proof-DAG edge を明示する。`QuerySupportedBy` だけでは current-shadow factorization は得られず、Cycle 42 の Bool complete-support recovery/no-current-factor witness がその弱化を防ぐ。

## 数学的興味

finite output が query readings を recover することと、それが current canonical shadow を通る descent/factorization を持つことを分離する。support に含まれることは local evidence であり、current-shadow adequacy になるには別の determinacy certificate が必要である。

## GOAL への前進

finite computable shadow / representation adequacy node で、support-level current-shadow determinacy を supported finite queries へ渡す reusable bridge を Lean に固定する。

## ライバルに対する有効性

ADL、静的解析、metric dashboard は「support に入っている」「readings が recover できる」ことを示せても、それが current canonical shadow を通る factorization かどうかを theorem-level に分離しにくい。この候補はその差を visible premise と axiom-free Lean theorem として固定する。

## SCORE 見込み

- `score_reason`: Cycle 37/38/42 の proof surface を接続し、supported finite query package で毎回 query-coordinate extensionality を仮定する圧力を減らす。ただし support determinacy 自体は未放電なので base は控えめ。
- `dullness_risk`: 既存 theorem の合成に近い。report では proof-DAG edge と anti-weakening boundary として扱い、target completion と呼ばない。
- `proof_or_evidence_plan`: 新規 Lean file、reported declarations の `#print axioms`、`ResearchLean` build、placeholder / hidden Unicode / local path scan。

## Target Theorem 寄与

- `target_theorem`: Universal Semantic Repair Obstruction Tower Theorem
- `target_support_node`: supported finite query current-shadow factorization boundary
- `target_progress`: support-node
- `proof_obligation_delta`: `CurrentShadowDeterminesSupportTraceShadow support` + `QuerySupportedBy support query` から query-coordinate extensionality、query determinacy、raw/represented finite-query current-shadow factorization を導く。
- `target_completion_role`: support theorem package only. `CurrentShadowDeterminesSupportTraceShadow support`、semantic soundness、arbitrary representation adequacy、finite shadow adequacy、global repair coherence、obstruction vanish は not discharged。

## CS / SWE への帰結

finite evidence pipeline で support membership や decoder recovery が得られても、それだけでは current-shadow descent adequacy ではない。current-shadow factorization を主張するには、support-level determinacy または query-coordinate criterion を別途可視化する必要がある。

## 証明・根拠の見込み

Lean では `coordinateCurrentShadowExtensional_of_currentShadowDeterminesSupportTraceShadow` と `QuerySupportedBy` を合成して query-coordinate extensionality を得る。その後、既存の `currentShadowDeterminesTraceQuery_of_queryCoordinateCurrentShadowExtensional` と `representedFiniteTraceQueryObservation_currentShadowFactor_of_queryCoordinateCurrentShadowExtensional` へ渡す。

Planned / proved declarations:

- `queryCoordinateCurrentShadowExtensional_of_currentShadowDeterminesSupportTraceShadow_of_querySupportedBy`
- `currentShadowDeterminesTraceQuery_of_currentShadowDeterminesSupportTraceShadow_of_querySupportedBy`
- `queryTraceReadings_currentShadowFactor_iff_queryCoordinateCurrentShadowExtensional`
- `supportedQueryTraceReadings_currentShadowFactor_of_currentShadowDeterminesSupportTraceShadow`
- `supportedQueryGeneratedObservation_currentShadowFactor_of_currentShadowDeterminesSupportTraceShadow`
- `representedSupportedFiniteTraceQueryObservation_currentShadowFactor_of_currentShadowDeterminesSupportTraceShadow`
- `representedFiniteTraceQueryObservation_queryCoordinateCurrentShadowExtensional_of_currentShadowDeterminesSupportTraceShadow`
- `supportTraceShadowRepresentation_currentShadowFactor_iff_currentShadowDeterminesSupportTraceShadow`

## Target Loop Audit Fields

- `material_premises`: `CurrentShadowDeterminesSupportTraceShadow support` remains visible-undischarged. `QuerySupportedBy support query` is finite input geometry / query admissibility, not semantic soundness or representation adequacy.
- `premise_discharge_plan`: future work must derive support determinacy or query-coordinate extensionality from semantic soundness / representation adequacy / finite certificate without circularity.
- `anti_weakening_verdict`: pass as target-support; reject as target-proof or target theorem completion.
- `claim_boundary`: finite query-generated observations and represented finite-query observations only; no arbitrary site, runtime extraction, ArchMap validation, global semantic repair coherence, obstruction vanish, or universal tower completion.
- `statement_strength_audit`: conclusion is current-shadow factorization under visible support determinacy, not unconditional representation adequacy.
- `dependency_plan`: import `SemanticRepairFiniteQueryRepresentationRecoveredFactorization` and reuse existing finite-query representation bridge theorems.
- `math_lean_review_scope`: if this ever contributes to target completion, reviewers must check that support determinacy is not hidden in representation, typeclass, certificate, or opaque membership.

## 審判メモ

- 厳密性: T2 A accepted as target-support/checkpoint; no semantic soundness or representation adequacy overclaim if the determinacy premise remains visible.
- 研究価値: T2 B accepted with base 44; useful proof-DAG edge, but not a new target theorem layer.
- repo 全体価値: T2 D accepted with positive rival delta as a theorem-level separation between recovery and adequacy.
- ライバル比較: support/recovery evidence from ADL/static analysis/dashboard is weaker than current-shadow factorization; this theorem names the missing certificate.

## 関連

- `research/ideas/g-aat-quality-surface-04-support-shadow-recovery-discharge.md`
- `research/ideas/g-aat-quality-surface-04-recovered-current-shadow-factorization-criterion.md`

## 進捗ログ

- 2026-06-25: Cycle 43 で picked。Lean file と report 同期済み。
