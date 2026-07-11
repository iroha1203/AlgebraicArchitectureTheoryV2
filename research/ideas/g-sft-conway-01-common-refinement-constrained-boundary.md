---
status: picked
goal: G-sft-conway-01
exploration_role: g6-frontier / common-refinement-constrained-boundary
candidate_type: bridge
capability_category: common-refinement-boundary, finite-coefficient, support-receiver, conway-obstruction
expected_base_score: 55
expected_evidence_multiplier: 2.0
expected_final_score: 110
evidence_stage: proved-in-research
lean: proved-in-research
cycle: 9
score_reason: Cycle 8 の support constraint を `CommonRefinementSpan` vocabulary に移し、common-refinement constrained owner-potential receiver が support receiver と同値であることを証明する。新 obstruction ではなく support receiver の common-refinement 表現なので base 55。
mathematical_interest: common-refinement block が fork の communication block 全体を覆うことを selected support condition として固定する。
goal_advancement: support predicate を common-refinement data に移し、後続の comparison theorem / common-refinement exactness の足場を作る。
dullness_risk: `ForkHasSingleOwnerSupport` と同値であり、新しい obstruction 条件ではない。
proof_or_evidence_plan: `research/lean/ResearchLean/AG/SFT/ConwayCommonRefinementBoundary.lean` に common-refinement support, single-owner support equivalence, constrained receiver equivalence, finite example package を置く。
planned_theorem_names: CommonRefinementSupportsFork, commonRefinementSupportsFork_iff_singleOwnerSupport, SupportForkDefectVanishesModuloCommonRefinementOwnerPotential, commonRefinementOwnerPotential_vanishes_iff_singleOwnerSupport, CommonRefinementOwnerPotentialReceiver, commonRefinementOwnerPotentialReceiver_iff_supportReceiver, mismatchedSupportFork_notCommonRefinementOwnerPotentialVanishes, selectedCommonRefinementOwnerPotentialPackage
rival_advantage: owner mismatch dashboard can show mismatch, but this candidate records whether the support condition has common-refinement provenance.
visible_projection: common-refinement span, fork communication block coverage, support receiver, owner-potential absorption.
protected_structure: CommonRefinementSpan, selected support fork, communication block coverage, owner support.
exactness_or_minimality_claim: common-refinement constrained owner-potential vanishing is equivalent to single-owner support under decidable owner equality.
nonfaithfulness_or_failure_mode: common-refinement provenance does not create a new obstruction by itself; it recovers the support receiver.
previous_cycle_delta: replaces Cycle 8's direct support predicate with explicit common-refinement support data.
rival_stress_test: rival must preserve whether compatibility is witnessed by common-refinement data, not just by endpoint mismatch.
genius_potential: no
genius_target: not-applicable
genius_support_role: not-applicable
target_theorem: not-applicable
target_support_node: not-applicable
target_progress: not-applicable
proof_obligation_delta: not-applicable
target_completion_role: not-applicable
origin: G-sft-conway-01
tags: [sft, conway, common-refinement, support-receiver, boundary]
created: 2026-07-04
---

# Common-refinement constrained boundary

## 主張

Cycle 8 の support constraint を `CommonRefinementSpan` vocabulary に移す。common-refinement block が
fork の communication block 全体を覆い、ownership block へ refine するなら single-owner support が得られる。
逆に single-owner support から singleton common-refinement support を構成できる。

## 非自明性

この cycle は新しい obstruction 条件ではない。価値は、support receiver を common-refinement data へ移し、
後続で common-refinement exactness / comparison theorem を述べるための provenance を固定する点にある。

## GOAL への前進

Conway 対応の receiver chain に common-refinement layer を追加する。次 frontier は、この common-refinement
support を global zero-cochain や comparison functor failure と比較する theorem である。

## SCORE 見込み

- `score_reason`: support receiver の common-refinement 表現として base 55。
- `dullness_risk`: single-owner support との同値なので、過大評価しない。
- `proof_or_evidence_plan`: `lake env lean research/lean/ResearchLean/AG/SFT/ConwayCommonRefinementBoundary.lean`、
  `lake build FormalAGResearch`、`#print axioms` で検証する。

## Lean evidence

- `research/lean/ResearchLean/AG/SFT/ConwayCommonRefinementBoundary.lean`
- `ResearchLean.AG.SFT.ConwayTwoTopology.CommonRefinementSupportsFork.toSingleOwnerSupport`
- `ResearchLean.AG.SFT.ConwayTwoTopology.CommonRefinementSupportsFork.ofSingleOwnerSupport`
- `ResearchLean.AG.SFT.ConwayTwoTopology.commonRefinementSupportsFork_iff_singleOwnerSupport`
- `ResearchLean.AG.SFT.ConwayTwoTopology.commonRefinementOwnerPotential_vanishes_iff_singleOwnerSupport`
- `ResearchLean.AG.SFT.ConwayTwoTopology.commonRefinementOwnerPotentialReceiver_iff_supportReceiver`
- `ResearchLean.AG.SFT.ConwayTwoTopology.mismatchedSupportFork_notCommonRefinementOwnerPotentialVanishes`
- `ResearchLean.AG.SFT.ConwayTwoTopology.selectedCommonRefinementOwnerPotentialPackage`

## 審判メモ

- 厳密性: pass。`CommonRefinementSupportsFork ↔ ForkHasSingleOwnerSupport` と receiver equivalence は Lean theorem。
- 研究価値: base 55。support receiver の common-refinement provenance 化であり、新 obstruction ではない。
- repo 全体価値: 後続の common-refinement exactness / comparison theorem の足場として有用。
- ライバル比較: owner mismatch 可視化だけでなく、support condition が common-refinement data で witness されるかを保存する。

## 進捗ログ

- 2026-07-04: 作成。`lake env lean research/lean/ResearchLean/AG/SFT/ConwayCommonRefinementBoundary.lean`、
  `lake build FormalAGResearch`、full `lake build` が通過。G2 二審判 pass、final score +110。
