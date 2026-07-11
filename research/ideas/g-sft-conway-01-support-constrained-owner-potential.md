---
status: picked
goal: G-sft-conway-01
exploration_role: g6-frontier / support-constrained-additive-boundary
candidate_type: bridge
capability_category: constrained-owner-potential, finite-coefficient, support-receiver, local-exactness, conway-obstruction
expected_base_score: 55
expected_evidence_multiplier: 2.0
expected_final_score: 110
evidence_stage: proved-in-research
lean: proved-in-research
cycle: 8
score_reason: Cycle 7 の unconstrained local owner-potential boundary の弱さに support constraint を戻し、decidable owner equality の下で constrained additive receiver が support receiver と同値になることを証明する。support receiver の最小修復的な再構成に近いため base 55 に抑える。
mathematical_interest: endpoint-separating owner potential は local additive absorption を与えるが、support constraint を併せると Conway mismatch を再び検出する。
goal_advancement: local additive endpoint boundary と support/global compatibility の関係を整理し、次の common-refinement constrained boundary へ渡す。
dullness_risk: support-constrained vanishing は `ForkHasSingleOwnerSupport` と同値であり、新しい obstruction 条件ではない。
proof_or_evidence_plan: `research/lean/ResearchLean/AG/SFT/ConwayConstrainedOwnerPotentialBoundary.lean` に support-constrained vanishing, endpoint-separating potential, receiver equivalence, finite example package を置く。
planned_theorem_names: SupportForkDefectVanishesModuloSupportConstrainedOwnerPotential, endpointSeparatingOwnerPotential, endpointSeparatingOwnerPotential_boundary_eq_defect, ownerPotentialBoundary_vanishes_of_decidableOwners, supportConstrainedOwnerPotential_vanishes_iff_singleOwnerSupport, SupportConstrainedOwnerPotentialReceiver, supportConstrainedOwnerPotentialReceiver_iff_supportReceiver, mismatchedSupportFork_notSupportConstrainedOwnerPotentialVanishes, selectedSupportConstrainedOwnerPotentialPackage
rival_advantage: owner mismatch dashboard can show mismatch, but this candidate distinguishes unconstrained local additive exactness from support-constrained exactness.
visible_projection: support fork, endpoint potential, support constraint, constrained receiver.
protected_structure: owner endpoint difference, single-owner support, support receiver, finite zero/nonzero examples.
exactness_or_minimality_claim: under decidable owner equality, support-constrained owner-potential vanishing is equivalent to single-owner support.
nonfaithfulness_or_failure_mode: unconstrained owner-potential exactness is nonfaithful, but support-constrained owner-potential exactness recovers the support receiver.
previous_cycle_delta: repairs Cycle 7's local additive weakness by adding the support constraint and proving receiver equivalence.
rival_stress_test: rival must preserve whether additive endpoint exactness is constrained by support compatibility.
genius_potential: no
genius_target: not-applicable
genius_support_role: not-applicable
target_theorem: not-applicable
target_support_node: not-applicable
target_progress: not-applicable
proof_obligation_delta: not-applicable
target_completion_role: not-applicable
origin: G-sft-conway-01
tags: [sft, conway, owner-potential, support-constraint, boundary]
created: 2026-07-04
---

# Support-constrained owner potential boundary

## 主張

Cycle 7 の local additive owner-potential boundary に single-owner support constraint を戻す。
`DecidableEq OwnerIdx` の下で endpoint-separating potential は任意 fork の local additive absorption を与え、
support-constrained vanishing は `ForkHasSingleOwnerSupport` と同値になる。

## 非自明性

unconstrained local additive boundary は canonical mismatch を吸収してしまった。support constraint を併せると、
同じ endpoint-potential vocabulary でも support receiver と同じ mismatch 検出を回復する。

## GOAL への前進

local additive exactness と support compatibility の関係を Lean 上で分離した。
次 frontier は support constraint を common-refinement / global compatibility constraint へ持ち上げること。

## SCORE 見込み

- `score_reason`: Cycle 7 の失敗を補正する constrained bridge だが、新 obstruction ではないため base 55。
- `dullness_risk`: support receiver と同値なので、過大評価しない。
- `proof_or_evidence_plan`: `lake env lean research/lean/ResearchLean/AG/SFT/ConwayConstrainedOwnerPotentialBoundary.lean`、
  `lake build FormalAGResearch`、`#print axioms` で検証する。

## Lean evidence

- `research/lean/ResearchLean/AG/SFT/ConwayConstrainedOwnerPotentialBoundary.lean`
- `ResearchLean.AG.SFT.ConwayTwoTopology.endpointSeparatingOwnerPotential_boundary_eq_defect`
- `ResearchLean.AG.SFT.ConwayTwoTopology.ownerPotentialBoundary_vanishes_of_decidableOwners`
- `ResearchLean.AG.SFT.ConwayTwoTopology.supportConstrainedOwnerPotential_vanishes_iff_singleOwnerSupport`
- `ResearchLean.AG.SFT.ConwayTwoTopology.supportConstrainedOwnerPotentialReceiver_iff_supportReceiver`
- `ResearchLean.AG.SFT.ConwayTwoTopology.mismatchedSupportFork_notSupportConstrainedOwnerPotentialVanishes`
- `ResearchLean.AG.SFT.ConwayTwoTopology.selectedSupportConstrainedOwnerPotentialPackage`

## 審判メモ

- 厳密性: accept, base 60。bounded selected theorem として blocking finding はない。
- 研究価値: revise, base 55。Cycle 7 failure の最小修復条件として有用だが、新 obstruction ではなく support receiver に戻る。
- repo 全体価値: accept/revise, base 55。次 frontier の common-refinement constraint へ渡す bridge として扱う。
- ライバル比較: revise, base 55。support constraint の有無は保存するが、rival separation は限定的。

## 進捗ログ

- 2026-07-04: 作成。`lake env lean research/lean/ResearchLean/AG/SFT/ConwayConstrainedOwnerPotentialBoundary.lean`、
  `lake build ResearchLean.AG.SFT.ConwayConstrainedOwnerPotentialBoundary`、`lake build FormalAGResearch`、full `lake build` が通過。
  G2/G3 後、score を base 55 / final 110 に修正。
