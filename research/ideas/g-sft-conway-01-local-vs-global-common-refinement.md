---
status: picked
goal: G-sft-conway-01
exploration_role: g6-frontier / local-vs-global-common-refinement
candidate_type: negative-bridge
capability_category: local-potential, global-boundary, common-refinement, conway-obstruction
expected_base_score: 40
expected_evidence_multiplier: 2.0
expected_final_score: 80
evidence_stage: proved-in-research
lean: proved-in-research
cycle: 11
score_reason: Cycle 7 の local owner-potential absorption と Cycle 10 の global/common-refinement receiver を分離する finite theorem package。既存 theorem の conjunction package に近く、新 receiver ではないため base 40。
mathematical_interest: local additive exactness が global compatibility plus common-refinement provenance を含意しないことを canonical mismatch で固定する。
goal_advancement: Conway receiver chain の中で local additive boundary の弱さと global/common constraints の必要性を接続する。
dullness_risk: canonical mismatched fork の既存事実を比較 package として組み合わせるため、過大評価しない。
proof_or_evidence_plan: `research/lean/ResearchLean/AG/SFT/ConwayLocalVsGlobalCommonRefinement.lean` に local-vs-global/common separation, support/common/global receivers, compatible zero package を置く。
planned_theorem_names: localOwnerPotential_absorbs_but_globalCommonRefinement_detects, localOwnerPotential_absorbs_but_commonRefinementOwnerPotential_detects, mismatchedLocalPotential_separatedBySupportAndGlobalCommonReceivers, compatibleAtlas_noLocalGlobalCommonSeparationReceivers, selectedLocalVsGlobalCommonRefinementPackage
rival_advantage: owner mismatch dashboard can show mismatch, but this candidate separates local additive absorption from global/common-refinement compatibility as a Lean theorem package.
visible_projection: owner potential, global/common-refinement receiver, common-refinement owner-potential receiver, canonical mismatch.
protected_structure: mismatchedSupportFork, OwnerPotential, GlobalCommonRefinementReceiver, CommonRefinementOwnerPotentialReceiver.
exactness_or_minimality_claim: local owner-potential vanishing is strictly weaker than the combined global/common-refinement predicate on the selected finite example.
nonfaithfulness_or_failure_mode: local additive exactness alone is nonfaithful to Conway compatibility.
previous_cycle_delta: uses Cycle 10 combined receiver to sharpen Cycle 7's local/global separation.
rival_stress_test: rival must not count local additive absorption as resolving Conway compatibility.
genius_potential: no
genius_target: not-applicable
genius_support_role: not-applicable
target_theorem: not-applicable
target_support_node: not-applicable
target_progress: not-applicable
proof_obligation_delta: not-applicable
target_completion_role: not-applicable
origin: G-sft-conway-01
tags: [sft, conway, local-potential, global-boundary, common-refinement]
created: 2026-07-04
---

# Local vs global/common-refinement separation

## 主張

canonical mismatched fork は local owner-potential boundary では吸収される。しかし、combined
global/common-refinement vanishing と common-refinement constrained owner-potential vanishing では消えない。

## 非自明性

この cycle は新 receiver を導入しない。価値は、Cycle 7 の local additive weakness と Cycle 10 の
global/common-refinement comparison を直接つなぎ、local exactness を Conway compatibility と誤読しては
いけない境界を Lean theorem として固定する点にある。

## GOAL への前進

Conway 対応の receiver chain で、local additive boundary、support constraint、common-refinement provenance、
global compatibility の階層を明確にする。次 frontier は selected finite example から arbitrary cover naturality
や comparison map failure へ移すこと。

## SCORE 見込み

- `score_reason`: 既存 receiver の分離 bridge として base 40。
- `dullness_risk`: canonical mismatch の既存定理を接続する package なので、新 obstruction として扱わない。
- `proof_or_evidence_plan`: `lake env lean research/lean/ResearchLean/AG/SFT/ConwayLocalVsGlobalCommonRefinement.lean`、
  `lake build ResearchLean.AG`、`#print axioms` で検証する。

## Lean evidence

- `research/lean/ResearchLean/AG/SFT/ConwayLocalVsGlobalCommonRefinement.lean`
- `ResearchLean.AG.SFT.ConwayTwoTopology.localOwnerPotential_absorbs_but_globalCommonRefinement_detects`
- `ResearchLean.AG.SFT.ConwayTwoTopology.localOwnerPotential_absorbs_but_commonRefinementOwnerPotential_detects`
- `ResearchLean.AG.SFT.ConwayTwoTopology.mismatchedLocalPotential_separatedBySupportAndGlobalCommonReceivers`
- `ResearchLean.AG.SFT.ConwayTwoTopology.compatibleAtlas_noLocalGlobalCommonSeparationReceivers`
- `ResearchLean.AG.SFT.ConwayTwoTopology.selectedLocalVsGlobalCommonRefinementPackage`

## 審判メモ

- 厳密性: pass。local absorption と global/common-refinement detection の分離は Lean theorem。
- 研究価値: base 40。既存 theorem の named comparison package に近く、新 receiver ではない。
- repo 全体価値: local additive exactness を Conway compatibility と誤読しない境界として有用。
- ライバル比較: owner mismatch 可視化だけでなく、local absorption と global/common constraints の分離を保存する。

## 進捗ログ

- 2026-07-04: 作成。`lake env lean research/lean/ResearchLean/AG/SFT/ConwayLocalVsGlobalCommonRefinement.lean`、
  module build、`lake build ResearchLean.AG`、full `lake build` が通過。G2 二審判 pass、final score +80。
