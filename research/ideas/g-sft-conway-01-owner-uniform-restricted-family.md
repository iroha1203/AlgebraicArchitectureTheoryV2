---
status: picked
goal: G-sft-conway-01
exploration_role: g6-frontier / owner-uniform-restricted-family
candidate_type: negative-bridge
capability_category: common-refinement, coherent-family, restricted-span, conway-obstruction
expected_base_score: 60
expected_evidence_multiplier: 2.0
expected_final_score: 120
evidence_stage: proved-in-research
lean: proved-in-research
cycle: 15
score_reason: Cycle 14 の Sigma assembly で潰れた local/shared gap を、owner-uniform coherent family support という restricted span vocabulary で復活させる。finite atlas で forkwise local support はあるが owner-uniform coherent support はないことを証明するため base 60。
mathematical_interest: unrestricted `CommonRefinementSpan` では消える obstruction が、shared owner coherence を課すと有限例で再出現する。
goal_advancement: coherent common-refinement family interface に restricted local/shared separation witness を追加する。
dullness_risk: restriction は owner-uniformity に限られ、arbitrary cover naturality や sheaf gluing ではない。
proof_or_evidence_plan: `research/lean/ResearchLean/AG/SFT/ConwayRestrictedCoherentFamily.lean` に owner-uniform support、finite restricted atlas、local support theorem、not owner-uniform theorem、receiver package を置く。
planned_theorem_names: OwnerUniformCoherentCommonRefinementSupport, ownerUniformSupport_implies_coherentSupport, restrictedTwoForkFamily_localSupport, restrictedTwoForkFamily_notOwnerUniformCoherent, OwnerUniformLocalButNotCoherentReceiver, restrictedTwoForkFamily_ownerUniformReceiver, selectedRestrictedCoherentFamilyPackage
rival_advantage: owner mismatch dashboard can show local ownership splits, but this theorem isolates the exact restricted coherence condition under which local support fails to glue.
visible_projection: owner-uniform coherent support, local fork support, finite two-fork separation, restricted-span receiver.
protected_structure: CommonRefinementSpan, SupportForkFamily, ForkFamilyHasLocalCommonRefinementSupport, CoherentCommonRefinementSupport.
exactness_or_minimality_claim: owner-uniform support implies ordinary coherent support, but forkwise local support does not imply owner-uniform support.
nonfaithfulness_or_failure_mode: local fork supports are nonfaithful to owner-uniform family coherence.
previous_cycle_delta: repairs Cycle 14's too-flexible Sigma assembly by adding one concrete restricted-span coherence condition.
genius_potential: no
genius_target: not-applicable
genius_support_role: not-applicable
target_theorem: not-applicable
target_support_node: not-applicable
target_progress: not-applicable
proof_obligation_delta: not-applicable
target_completion_role: not-applicable
origin: G-sft-conway-01
tags: [sft, conway, common-refinement, coherent-family, restricted-span]
created: 2026-07-04
---

# Owner-uniform restricted family

## 主張

Cycle 14 では unrestricted `CommonRefinementSpan` が forkwise local support を Sigma-indexed shared span へ
常に assemble できることを示した。Cycle 15 では、family 内の selected refinement blocks が同じ
ownership vertex へ refine しなければならない `OwnerUniformCoherentCommonRefinementSupport` を導入する。

この owner-uniform restriction の下では、finite two-fork family において forkwise local support はあるが
owner-uniform coherent support は存在しない。

## 非自明性

これは arbitrary cover naturality ではない。制約は「shared owner coherence」に限られる。
しかし Cycle 14 で消えた local/shared gap を、現 vocabulary 上の具体的な制約として復活させる点に価値がある。

## GOAL への前進

Conway common-refinement family chain に restricted local/shared separation witness を追加する。local fork support だけでは
family-level owner-uniform coherence を保証しないことを Lean theorem として固定する。

## SCORE 見込み

- `score_reason`: 新しい owner-uniform support interface と finite separation theorem により base 60。
- `dullness_risk`: 制約は owner-uniformity に限定され、true sheaf gluing ではない。
- `proof_or_evidence_plan`: `cd research/lean && lake env lean ResearchLean/AG/SFT/ConwayRestrictedCoherentFamily.lean`、
  `旧Research aggregate build`、`#print axioms` で検証する。

## Lean evidence

- `research/lean/ResearchLean/AG/SFT/ConwayRestrictedCoherentFamily.lean`
- `ResearchLean.AG.SFT.ConwayTwoTopology.OwnerUniformCoherentCommonRefinementSupport`
- `ResearchLean.AG.SFT.ConwayTwoTopology.OwnerUniformCoherentCommonRefinementSupport.sharedOwner_supports`
- `ResearchLean.AG.SFT.ConwayTwoTopology.ownerUniformSupport_implies_coherentSupport`
- `ResearchLean.AG.SFT.ConwayTwoTopology.restrictedTwoForkFamily_localSupport`
- `ResearchLean.AG.SFT.ConwayTwoTopology.restrictedTwoForkFamily_notOwnerUniformCoherent`
- `ResearchLean.AG.SFT.ConwayTwoTopology.OwnerUniformLocalButNotCoherentReceiver`
- `ResearchLean.AG.SFT.ConwayTwoTopology.restrictedTwoForkFamily_ownerUniformReceiver`
- `ResearchLean.AG.SFT.ConwayTwoTopology.selectedRestrictedCoherentFamilyPackage`

## 審判メモ

- 厳密性: pass。finite two-fork family で local support と owner-uniform coherent support の分離を Lean theorem 化済み。
- 研究価値: base 60。restricted coherence を入れて初めて local/shared gap が現れる。
- repo 全体価値: common-refinement family interface の次の non-selected / restricted-span frontier になる。
- ライバル比較: mismatch 可視化ではなく、local support と owner-uniform family coherence の分離を theorem として保存する。

## 進捗ログ

- 2026-07-04: 作成。`cd research/lean && lake env lean ResearchLean/AG/SFT/ConwayRestrictedCoherentFamily.lean`、
  module build、`旧Research aggregate build`、full `lake build` が通過。G2 二審判 pass、final score +120。
  core owner-uniform support theorem は axiom-free、finite package は `propext` / `Classical.choice` に依存。
