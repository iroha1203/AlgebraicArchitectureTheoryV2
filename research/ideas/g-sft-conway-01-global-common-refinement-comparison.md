---
status: picked
goal: G-sft-conway-01
exploration_role: g6-frontier / global-common-refinement-comparison
candidate_type: bridge
capability_category: global-boundary, common-refinement, finite-coefficient, conway-obstruction
expected_base_score: 55
expected_evidence_multiplier: 2.0
expected_final_score: 110
evidence_stage: proved-in-research
lean: proved-in-research
cycle: 10
score_reason: Cycle 5 の global zero-cochain boundary と Cycle 9 の common-refinement support provenance を比較し、combined receiver が global-boundary receiver と同値であることを証明する。新 obstruction ではないので base 55。
mathematical_interest: global zero-cochain が every selected fork に common-refinement support を供給することを固定する。
goal_advancement: support provenance と global exactness の比較層を追加し、common-refinement exactness failure を探す次段の基準を作る。
dullness_risk: combined receiver は global-boundary receiver と同値であり、検出力を増やさない。
proof_or_evidence_plan: `research/lean/ResearchLean/AG/SFT/ConwayGlobalCommonRefinementComparison.lean` に zero-cochain-to-common-refinement support, combined vanishing iff compatibility, receiver equivalence, finite example package を置く。
planned_theorem_names: CommunicationZeroCochain.toCommonRefinementSupport, communicationZeroCochain_commonRefinementSupport, SupportForkDefectVanishesModuloGlobalCommonRefinement, globalCommonRefinement_vanishes_iff_compatible, globalCommonRefinement_implies_commonRefinementOwnerPotential, GlobalCommonRefinementReceiver, globalCommonRefinementReceiver_iff_globalBoundaryReceiver, selectedGlobalCommonRefinementComparisonPackage
rival_advantage: owner mismatch dashboard can show mismatch, but this candidate records that global compatibility already carries common-refinement support provenance.
visible_projection: global zero-cochain, common-refinement support, compatibility, global-boundary receiver.
protected_structure: CommunicationZeroCochain, CommonRefinementSupportsFork, selected support fork, global-boundary receiver.
exactness_or_minimality_claim: combined global/common-refinement vanishing is equivalent to communication-cover compatibility at the selected finite level.
nonfaithfulness_or_failure_mode: common-refinement provenance does not strengthen the global-boundary obstruction by itself.
previous_cycle_delta: compares Cycle 9 common-refinement provenance with Cycle 5 global zero-cochain boundary.
rival_stress_test: rival must distinguish local mismatch visualization from the theorem that global compatibility supplies common-refinement provenance for every selected fork.
genius_potential: no
genius_target: not-applicable
genius_support_role: not-applicable
target_theorem: not-applicable
target_support_node: not-applicable
target_progress: not-applicable
proof_obligation_delta: not-applicable
target_completion_role: not-applicable
origin: G-sft-conway-01
tags: [sft, conway, global-boundary, common-refinement, support-receiver]
created: 2026-07-04
---

# Global/common-refinement comparison

## 主張

Cycle 5 の global zero-cochain は、任意の selected fork に対して common-refinement support を供給する。
したがって、global boundary absorption と common-refinement support provenance を同時に要求する combined
vanishing は、selected finite level では communication-cover compatibility と同値である。

## 非自明性

この cycle は新 obstruction ではない。価値は、common-refinement support provenance が global zero-cochain
boundary とどう関係するかを明示し、次に common-refinement exactness failure を探すための基準を固定する点にある。

## GOAL への前進

Conway 対応の receiver chain で、global exactness と common-refinement provenance の比較層を追加する。
次 frontier は、この同値では捕まらない arbitrary cover naturality / comparison map failure を分離する theorem である。

## SCORE 見込み

- `score_reason`: global-boundary receiver と同値な comparison bridge として base 55。
- `dullness_risk`: 検出力は Cycle 5 global-boundary receiver を越えない。
- `proof_or_evidence_plan`: `lake env lean research/lean/ResearchLean/AG/SFT/ConwayGlobalCommonRefinementComparison.lean`、
  `lake build ResearchLean.AG`、`#print axioms` で検証する。

## Lean evidence

- `research/lean/ResearchLean/AG/SFT/ConwayGlobalCommonRefinementComparison.lean`
- `ResearchLean.AG.SFT.ConwayTwoTopology.CommunicationZeroCochain.toCommonRefinementSupport`
- `ResearchLean.AG.SFT.ConwayTwoTopology.communicationZeroCochain_commonRefinementSupport`
- `ResearchLean.AG.SFT.ConwayTwoTopology.globalCommonRefinement_vanishes_iff_compatible`
- `ResearchLean.AG.SFT.ConwayTwoTopology.globalCommonRefinement_implies_commonRefinementOwnerPotential`
- `ResearchLean.AG.SFT.ConwayTwoTopology.globalCommonRefinementReceiver_iff_globalBoundaryReceiver`
- `ResearchLean.AG.SFT.ConwayTwoTopology.mismatchedSupportFork_notGlobalCommonRefinementVanishes`
- `ResearchLean.AG.SFT.ConwayTwoTopology.selectedGlobalCommonRefinementComparisonPackage`

## 審判メモ

- 厳密性: pass。global-boundary exactness と common-refinement provenance の比較は Lean theorem。
- 研究価値: base 55。新 obstruction ではなく、Cycle 5 / Cycle 9 の比較 bridge。
- repo 全体価値: common-refinement exactness / naturality / comparison map failure を探す基準線として有用。
- ライバル比較: owner mismatch 可視化だけでなく、global compatibility が every selected fork に common-refinement provenance を供給することを保存する。

## 進捗ログ

- 2026-07-04: 作成。`lake env lean research/lean/ResearchLean/AG/SFT/ConwayGlobalCommonRefinementComparison.lean`、
  module build、`lake build ResearchLean.AG`、full `lake build` が通過。G2 二審判 pass、final score +110。
