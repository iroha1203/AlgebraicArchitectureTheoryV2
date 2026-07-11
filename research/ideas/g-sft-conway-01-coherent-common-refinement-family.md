---
status: picked
goal: G-sft-conway-01
exploration_role: g6-frontier / coherent-common-refinement-family
candidate_type: bridge
capability_category: common-refinement, coherent-family, global-boundary, conway-obstruction
expected_base_score: 50
expected_evidence_multiplier: 2.0
expected_final_score: 100
evidence_stage: proved-in-research
lean: proved-in-research
cycle: 12
score_reason: fork ごとの singleton support ではなく、one shared `CommonRefinementSpan` から fork family 全体へ support を選ぶ coherent interface を追加する。新 obstruction ではなく、global zero-cochain からの構成は直接的なので base 50。
mathematical_interest: global zero-cochain が communication-indexed shared refinement span を作り、任意の selected fork family に coherent common-refinement support を供給する。
goal_advancement: common-refinement provenance を single fork から family-level coherence へ上げる。
dullness_risk: vanishing criterion は communication compatibility と同値であり、新 obstruction ではない。
proof_or_evidence_plan: `research/lean/ResearchLean/AG/SFT/ConwayCoherentCommonRefinementFamily.lean` に `SupportForkFamily`, `CoherentCommonRefinementSupport`, zero-cochain-to-family support, family vanishing iff compatibility, finite package を置く。
planned_theorem_names: SupportForkFamily, CoherentCommonRefinementSupport, coherentCommonRefinementSupport_implies_eachForkSupport, CommunicationZeroCochain.toCoherentCommonRefinementSupport, communicationZeroCochain_coherentCommonRefinementSupport, familyCoherentGlobalCommonRefinement_vanishes_iff_compatible, selectedCoherentCommonRefinementFamilyPackage
rival_advantage: owner mismatch dashboard can show mismatch, but this candidate records coherent family-level provenance from a shared refinement span.
visible_projection: fork family, shared common-refinement span, global zero-cochain, coherent support.
protected_structure: CommonRefinementSpan, CommunicationZeroCochain, SupportForkFamily, selected support forks.
exactness_or_minimality_claim: family-level coherent global/common-refinement vanishing is equivalent to communication-cover compatibility.
nonfaithfulness_or_failure_mode: coherent family support still does not create a new obstruction beyond global compatibility.
previous_cycle_delta: moves beyond Cycle 11's conjunction package by adding a new family-level structure.
rival_stress_test: rival must represent whether support provenance is chosen coherently from one shared refinement span, not only per fork.
genius_potential: no
genius_target: not-applicable
genius_support_role: not-applicable
target_theorem: not-applicable
target_support_node: not-applicable
target_progress: not-applicable
proof_obligation_delta: not-applicable
target_completion_role: not-applicable
origin: G-sft-conway-01
tags: [sft, conway, common-refinement, coherent-family, global-boundary]
created: 2026-07-04
---

# Coherent common-refinement family

## 主張

fork ごとの singleton common-refinement support ではなく、one shared `CommonRefinementSpan` から selected fork
family 全体へ support block を選ぶ構造を導入する。global zero-cochain は communication-indexed shared span を
作り、任意の selected fork family に coherent common-refinement support を供給する。

## 非自明性

この cycle は新 obstruction ではない。価値は、common-refinement provenance を single fork から family-level
coherence へ上げ、arbitrary cover naturality / comparison map failure を述べる前段の interface を固定する点にある。

## GOAL への前進

Conway 対応の receiver chain で、common-refinement support を fork family に渡す構造を追加する。
次 frontier は、この coherent family interface で local support は選べるが shared span が存在しない状況を探すこと。

## SCORE 見込み

- `score_reason`: 新しい family-level structure と zero-cochain construction により base 50。
- `dullness_risk`: family vanishing は compatibility と同値であり、新 obstruction ではない。
- `proof_or_evidence_plan`: `focused Lean check: ResearchLean/AG/SFT/ConwayCoherentCommonRefinementFamily.lean`、
  `旧Research aggregate build`、`#print axioms` で検証する。

## Lean evidence

- `research/lean/ResearchLean/AG/SFT/ConwayCoherentCommonRefinementFamily.lean`
- `ResearchLean.AG.SFT.ConwayTwoTopology.SupportForkFamily`
- `ResearchLean.AG.SFT.ConwayTwoTopology.CoherentCommonRefinementSupport`
- `ResearchLean.AG.SFT.ConwayTwoTopology.coherentCommonRefinementSupport_implies_eachForkSupport`
- `ResearchLean.AG.SFT.ConwayTwoTopology.CommunicationZeroCochain.toCoherentCommonRefinementSupport`
- `ResearchLean.AG.SFT.ConwayTwoTopology.communicationZeroCochain_coherentCommonRefinementSupport`
- `ResearchLean.AG.SFT.ConwayTwoTopology.familyCoherentGlobalCommonRefinement_vanishes_iff_compatible`
- `ResearchLean.AG.SFT.ConwayTwoTopology.selectedCoherentCommonRefinementFamilyPackage`

## 審判メモ

- 厳密性: pass。shared `CommonRefinementSpan` から family 全体へ support を選ぶ構造は Lean theorem。
- 研究価値: base 50。family-level interface は新しいが、vanishing criterion は compatibility と同値。
- repo 全体価値: arbitrary cover naturality / comparison map failure の前段 interface として有用。
- ライバル比較: owner mismatch 可視化だけでなく、support provenance が shared span から coherent に選ばれるかを保存する。

## 進捗ログ

- 2026-07-04: 作成。`focused Lean check: ResearchLean/AG/SFT/ConwayCoherentCommonRefinementFamily.lean`、
  module build、`旧Research aggregate build`、full `lake build` が通過。G2 二審判 pass、final score +100。
