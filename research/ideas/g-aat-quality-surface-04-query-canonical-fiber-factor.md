---
status: picked
goal: G-aat-quality-surface-04
candidate_type: target-support
capability_category: finite-query-current-shadow / explicit-fiber-factor / anti-weakening
expected_base_score: 39
expected_evidence_multiplier: 2.0
expected_final_score: 78
score_note: Makes the Cycle 28 post-fiber invariance criterion constructive by defining the canonical query-post factor and its pointwise uniqueness on realized fibers.
evidence_stage: proved-in-research
rival_advantage: Replaces existential or opaque current-shadow factorization with an explicit representative-induced factor for finite query-generated observations.
genius_potential: false
genius_target: not-applicable
genius_support_role: not-applicable
target_theorem: Universal Semantic Repair Obstruction Tower Theorem
target_support_node: explicit finite query post-fiber factor
target_progress: support-node
proof_obligation_delta: Constructs the canonical current-shadow factor induced by a finite query post-map under `QueryPostInvariantOnCurrentShadowFibers`, and proves pointwise uniqueness among factors agreeing on realized fibers.
target_completion_role: not-completion; post-fiber invariance remains a visible undischarged premise.
material_premises: QueryPostInvariantOnCurrentShadowFibers for arbitrary post-map factorization
premise_discharge_status: factor constructed from the premise; semantic-soundness extraction not discharged
new_material_premise: no hidden premise; uses the explicit Cycle 28 fiber-invariance premise
anti_weakening_verdict: pass as support-node; fail if treated as semantic soundness extraction
origin: G-04 Cycle 29
tags: [target-theorem, target-support, finite-query, current-shadow, explicit-factor]
created: 2026-06-25
cycle: 29
lean: Formal/AG/Research/QualitySurface/SemanticRepairFiniteQueryFiberFactor.lean
---

# Query Canonical Fiber Factor

## 主張

`QueryPostInvariantOnCurrentShadowFibers` のもとで、finite query-generated observation の current-shadow factor は明示的に構成できる。current shadow ごとに canonical representative tower を選び、その query readings に `post` を適用する factor が canonical factor である。

## 候補種別

`target-support`

## 依拠

- `SemanticRepairFiniteQueryPostFiberInvariance.lean`: post-fiber invariance exact criterion
- `SemanticRepairTargetCompletion.lean`: `representativeTowerOfShadow`
- `SemanticRepairFiniteQueryObservation.lean`: finite query-generated observation package

## 非自明性

Cycle 28 は exact criterion を出したが、factor の中身はまだ `canonicalShadowFactor` へ委譲されていた。本候補は finite query post-map から直接 factor を構成し、realized fibers 上での点ごとの一意性を証明する。

## 数学的興味

current-shadow factorization を「存在する」から「representative-induced factor として計算できる」へ移す。これにより semantic soundness extraction の次の仕事は、factor の存在ではなく post-fiber invariance の放電に集中する。

## GOAL への前進

G-04 の finite-query factorization boundary を構成的にする。target completion ではないが、finite query-generated observation の factorization package が明示的になり、hidden factor premise をさらに減らす。

## ライバルに対する有効性

bounded diagnostic / ADL query が current shadow へ落ちるとき、どの factor で落ちるのかを代表 tower により定義できる。これは opaque factorization claim より検査可能な theorem boundary である。

## SCORE 見込み

- `score_reason`: exact criterion に対して explicit factor と pointwise uniqueness を与え、factorization package を構成的にする。
- `dullness_risk`: post-fiber invariance 自体は未放電であり、semantic soundness extraction ではない。
- `proof_or_evidence_plan`: representative-induced factor、realizable representative proof、factorization theorem、pointwise uniqueness、package theorem を Lean に追加する。

## Target Theorem 寄与

- `target_theorem`: Universal Semantic Repair Obstruction Tower Theorem
- `target_support_node`: explicit finite query post-fiber factor
- `target_progress`: support-node
- `proof_obligation_delta`: post-fiber invariance premiseから canonical query-post factor を構成し、一意性を証明する。
- `target_completion_role`: not-completion; semantic soundness -> post-fiber invariance remains open.

## CS / SWE への帰結

diagnostic query が current shadow に落ちる場合、representative run 上の query readings を使って factor を実装レベルに近い形で読むことができる。fiber invariance がなければこの factor は正当化されない。

## 証明・根拠の見込み

Lean file `SemanticRepairFiniteQueryFiberFactor.lean` は次を定義・証明する。

- `canonicalQueryPostFiberFactor` (definition)
- `queryReadingsRealizableAtCurrentShadow_representative`
- `post_eq_canonicalQueryPostFiberFactor_of_postInvariant`
- `queryTraceGeneratedObservation_eq_canonicalQueryPostFiberFactor_of_postInvariant`
- `finiteTraceQueryObservation_eq_canonicalQueryPostFiberFactor_of_postInvariant`
- `canonicalQueryPostFiberFactor_pointwise_unique`
- `queryTraceGeneratedObservation_explicitFiberFactorization`

## 審判メモ

- 厳密性: factor construction は finite query-generated observation に限定し、post-fiber invariance を仮定として明示する。
- 研究価値: exact criterion の factor を constructive にし、次の未放電 premise をさらに局所化する。
- repo 全体価値: report と tracking issue では `support-node` として扱い、target completion とは書かない。

## 関連

- `g-aat-quality-surface-04-query-post-fiber-invariance.md`
- `SemanticRepairFiniteQueryPostFiberInvariance.lean`

## 進捗ログ

- 2026-06-25: Cycle 29 として canonical query-post fiber factor theorem を追加。
