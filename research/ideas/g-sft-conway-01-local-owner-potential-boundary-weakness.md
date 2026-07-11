---
status: picked
goal: G-sft-conway-01
exploration_role: g6-frontier / local-additive-boundary-weakness
candidate_type: negative-bridge
capability_category: owner-potential-boundary, finite-coefficient, local-exactness, conway-obstruction, finite-witness
expected_base_score: 60
expected_evidence_multiplier: 2.0
expected_final_score: 120
evidence_stage: proved-in-research
lean: proved-in-research
cycle: 7
score_reason: Cycle 6 後の open frontier だった additive boundary 候補を、local finite endpoint-potential boundary として置く。ただし結果は positive receiver ではなく、unconstrained local additive boundary が canonical mismatch を吸収してしまうという弱さの証明なので、中程度 score に抑える。
mathematical_interest: owner potential の endpoint difference という additive boundary が、support/global compatibility を無視すると Conway mismatch を消してしまうことを Lean theorem として固定する。
goal_advancement: local additive exactness と Conway obstruction receiver を分離し、次 cycle で必要な global/common-refinement constraint を明確化する。true `C0 -> C1` complex はまだ主張しない。
dullness_risk: mismatched finite example 上の local computationであり、一般 theorem や true cohomology ではない。positive obstruction receiver ではなく boundary candidate の失敗整理である。
proof_or_evidence_plan: `research/lean/ResearchLean/AG/SFT/ConwayOwnerPotentialBoundary.lean` に owner potential, additive boundary, mismatched local absorption, owner-choice/global receiver との分離 theorem を置く。
planned_theorem_names: OwnerPotential, SupportForkOwnerPotentialBoundary, SupportForkDefectVanishesModuloOwnerPotentialBoundary, ownerPotentialBoundary_absorbs_of_endpointDifference, mismatchedOwnerPotential, mismatchedOwnerPotential_boundary_eq_defect, mismatchedSupportFork_ownerPotentialBoundaryVanishes, localOwnerPotential_absorbs_but_ownerChoiceReceiver_detects, localOwnerPotential_absorbs_but_globalBoundary_detects, selectedOwnerPotentialBoundaryPackage
rival_advantage: owner mismatch dashboard can show endpoint mismatch. This candidate proves that a naive local additive potential can erase the selected defect, so a rival must distinguish local algebraic separation from support/global compatibility.
visible_projection: owner potential, support fork endpoints, endpoint difference, local absorption, global/support receiver nonabsorption.
protected_structure: canonical mismatched fork, endpoint owner potentials, owner-choice receiver, global zero-cochain receiver.
exactness_or_minimality_claim: local owner-potential boundary absorption is too weak for the Conway receiver because it absorbs the canonical mismatch while support/global receivers still detect it.
nonfaithfulness_or_failure_mode: local additive owner-potential exactness is nonfaithful to support/global compatibility.
previous_cycle_delta: upgrades Cycle 6 from a predicate-driven owner-choice branch to a local finite `ConwayZ2` endpoint-difference boundary, then proves that this additive boundary is insufficient by itself.
rival_stress_test: rival must not equate local additive exactness with Conway compatibility; it must preserve support/global constraints.
genius_potential: no
genius_target: not-applicable
genius_support_role: not-applicable
target_theorem: not-applicable
target_support_node: not-applicable
target_progress: not-applicable
proof_obligation_delta: not-applicable
target_completion_role: not-applicable
origin: G-sft-conway-01
tags: [sft, conway, owner-potential, boundary, nonfaithfulness]
created: 2026-07-04
---

# Local owner-potential boundary weakness

## 主張

`OwnerPotential : OwnerIdx -> ConwayZ2` を local finite endpoint-potential data とし、support fork の boundary を
right owner potential minus left owner potential として定義する。この local additive boundary は
canonical mismatched fork の selected defect を吸収できる。

## 非自明性

これは positive receiver ではなく、local additive exactness の弱さを示す。canonical mismatch は
local owner-potential boundary では消えるが、owner-choice/support receiver と global zero-cochain receiver は
なお mismatch を検出する。

## GOAL への前進

Conway 対応に必要な境界条件を sharpen する。単に local additive endpoint boundary を置くだけでは足りず、
support/global compatibility または common-refinement constraint が必要であることを Lean 証拠として残す。

## SCORE 見込み

- `score_reason`: additive local boundary とその failure-mode を固定するが、canonical finite fork 上の negative bridge なので base 60。
- `dullness_risk`: finite example 上の negative bridge なので、過大評価しない。
- `proof_or_evidence_plan`: `lake env lean research/lean/ResearchLean/AG/SFT/ConwayOwnerPotentialBoundary.lean`、
  `lake build FormalAGResearch`、`#print axioms` で検証する。

## Lean evidence

- `research/lean/ResearchLean/AG/SFT/ConwayOwnerPotentialBoundary.lean`
- `ResearchLean.AG.SFT.ConwayTwoTopology.OwnerPotential`
- `ResearchLean.AG.SFT.ConwayTwoTopology.SupportForkOwnerPotentialBoundary`
- `ResearchLean.AG.SFT.ConwayTwoTopology.ownerPotentialBoundary_absorbs_of_endpointDifference`
- `ResearchLean.AG.SFT.ConwayTwoTopology.mismatchedOwnerPotential_boundary_eq_defect`
- `ResearchLean.AG.SFT.ConwayTwoTopology.mismatchedSupportFork_ownerPotentialBoundaryVanishes`
- `ResearchLean.AG.SFT.ConwayTwoTopology.localOwnerPotential_absorbs_but_ownerChoiceReceiver_detects`
- `ResearchLean.AG.SFT.ConwayTwoTopology.localOwnerPotential_absorbs_but_globalBoundary_detects`
- `ResearchLean.AG.SFT.ConwayTwoTopology.selectedOwnerPotentialBoundaryPackage`

## 審判メモ

- 厳密性: revise, base 60。bounded claim として blocking finding はないが、true `C0 -> C1` complex ではなく canonical finite fork 上の negative bridge。
- 研究価値: accept/revise, base 60-65。local additive exactness の弱さを明確にする価値はあるが、一般 theorem ではない。
- repo 全体価値: accept/revise, base 60。次 frontier の制約を明確化する research-surface 価値がある。
- ライバル比較: revise, base 55-60。local additive exactness と support/global compatibility の非忠実性は示すが、finite theorem package に留まる。

## 進捗ログ

- 2026-07-04: 作成。`lake env lean research/lean/ResearchLean/AG/SFT/ConwayOwnerPotentialBoundary.lean`、
  `lake build ResearchLean.AG.SFT.ConwayOwnerPotentialBoundary`、`lake build FormalAGResearch`、full `lake build` が通過。
  G2/G3 後、score を base 60 / final 120 に修正。
