---
status: picked
goal: G-sft-conway-01
exploration_role: g6-frontier / coherent-family-morphism-naturality
candidate_type: bridge
capability_category: common-refinement, coherent-family, selected-naturality, conway-obstruction
expected_base_score: 35
expected_evidence_multiplier: 2.0
expected_final_score: 70
evidence_stage: proved-in-research
lean: proved-in-research
cycle: 13
score_reason: Cycle 12 の coherent family interface に strict fork-preserving selected family morphism を追加し、reindex / subfamily に沿った coherent support と vanishing の pullback を Lean theorem として固定する。arbitrary-cover naturality でも新 obstruction でもないため base 35。
mathematical_interest: one shared `CommonRefinementSpan` からの coherent support が、selected family の reindexing / subfamily selection で保存されることを明示する。
goal_advancement: common-refinement family provenance を selected morphism layer まで上げ、arbitrary naturality を主張せずに保存則を固定する。
dullness_risk: morphism は fork equality を保存する selected reindex/subfamily map であり、新 obstruction は検出しない。
proof_or_evidence_plan: `research/lean/ResearchLean/AG/SFT/ConwayCoherentFamilyMorphism.lean` に `SupportForkFamilyMorphism`, support pullback, vanishing pullback, naturality failure impossibility, package theorem を置く。
planned_theorem_names: SupportForkFamilyMorphism, SupportForkFamilyMorphism.pullbackSupport, coherentCommonRefinementSupport_pullback, coherentGlobalCommonRefinement_vanishes_pullback, SupportForkFamily.reindex, SupportForkFamily.subfamily, no_coherentFamilyMorphismNaturalityFailure, selectedCoherentFamilyMorphismPackage
rival_advantage: owner mismatch dashboard can show mismatch, but this candidate records selected provenance preservation under family morphisms.
visible_projection: selected family morphism, reindexing, subfamily, coherent support pullback.
protected_structure: SupportForkFamily, CoherentCommonRefinementSupport, CommonRefinementSpan.
exactness_or_minimality_claim: selected coherent global/common-refinement vanishing pulls back along selected family morphisms.
nonfaithfulness_or_failure_mode: no full arbitrary-cover naturality is claimed; naturality is limited to fork-preserving selected family morphisms.
previous_cycle_delta: strengthens Cycle 12 family coherence from existence of one shared span to preservation under selected reindex/subfamily maps.
genius_potential: no
genius_target: not-applicable
genius_support_role: not-applicable
target_theorem: not-applicable
target_support_node: not-applicable
target_progress: not-applicable
proof_obligation_delta: not-applicable
target_completion_role: not-applicable
origin: G-sft-conway-01
tags: [sft, conway, common-refinement, coherent-family, selected-naturality]
created: 2026-07-04
---

# Coherent family morphism naturality

## 主張

Cycle 12 の `SupportForkFamily` に対して、fork equality を保存する strict selected family morphism を導入する。
target family に coherent common-refinement support があれば、source family は同じ shared
`CommonRefinementSpan` を使って coherent support を引き戻せる。したがって coherent
global/common-refinement vanishing も reindex / subfamily map に沿って pullback する。

## 非自明性

これは arbitrary-cover naturality ではない。morphism は strict fork-preserving selected fork family の reindexing / subfamily
selection を表す有限の保存写像に限る。価値は、Cycle 12 の coherent family support が単なる存在主張ではなく、
選択済み family map に沿う保存則を持つことを Lean theorem として固定する点にある。

## GOAL への前進

Conway 対応の common-refinement provenance を family-level existence から selected morphism-level
preservation へ一段上げる。今後の arbitrary cover naturality blocker を述べる基準線になる。

## SCORE 見込み

- `score_reason`: strict fork-preserving selected morphism layer と pullback theorem により base 35。
- `dullness_risk`: fork equality を保存する map に限るため新 obstruction ではない。
- `proof_or_evidence_plan`: `lake env lean research/lean/ResearchLean/AG/SFT/ConwayCoherentFamilyMorphism.lean`、
  `lake build ResearchLean.AG`、`#print axioms` で検証する。

## Lean evidence

- `research/lean/ResearchLean/AG/SFT/ConwayCoherentFamilyMorphism.lean`
- `ResearchLean.AG.SFT.ConwayTwoTopology.SupportForkFamilyMorphism`
- `ResearchLean.AG.SFT.ConwayTwoTopology.SupportForkFamilyMorphism.id`
- `ResearchLean.AG.SFT.ConwayTwoTopology.SupportForkFamilyMorphism.comp`
- `ResearchLean.AG.SFT.ConwayTwoTopology.SupportForkFamilyMorphism.pullbackSupport`
- `ResearchLean.AG.SFT.ConwayTwoTopology.coherentCommonRefinementSupport_pullback`
- `ResearchLean.AG.SFT.ConwayTwoTopology.coherentGlobalCommonRefinement_vanishes_pullback`
- `ResearchLean.AG.SFT.ConwayTwoTopology.SupportForkFamily.reindex`
- `ResearchLean.AG.SFT.ConwayTwoTopology.SupportForkFamily.reindexMorphism`
- `ResearchLean.AG.SFT.ConwayTwoTopology.SupportForkFamily.subfamily`
- `ResearchLean.AG.SFT.ConwayTwoTopology.SupportForkFamily.subfamilyInclusion`
- `ResearchLean.AG.SFT.ConwayTwoTopology.no_coherentFamilyMorphismNaturalityFailure`
- `ResearchLean.AG.SFT.ConwayTwoTopology.selectedCoherentFamilyMorphismPackage`

## 審判メモ

- 厳密性: pass。Lean statement は strict fork-preserving selected morphism の範囲に限定されている。
- 研究価値: base 35。selected naturality layer は有用だが、再index/subfamily transport に近く新 obstruction ではない。
- repo 全体価値: coherent family interface の保存則を明示し、arbitrary naturality blocker の前段になる。
- ライバル比較: owner mismatch 可視化だけでなく、support provenance の selected family morphism 保存を保存する。

## 進捗ログ

- 2026-07-04: 作成。`lake env lean research/lean/ResearchLean/AG/SFT/ConwayCoherentFamilyMorphism.lean`、
  module build、`lake build ResearchLean.AG`、full `lake build` が通過。G2 二審判 pass だが score を
  base 35 / final +70 に減額。
