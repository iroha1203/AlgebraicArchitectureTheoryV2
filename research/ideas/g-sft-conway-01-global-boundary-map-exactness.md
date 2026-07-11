---
status: picked
goal: G-sft-conway-01
exploration_role: g6-frontier / boundary-map-exactness
candidate_type: bridge
capability_category: global-boundary-map, finite-coefficient, support-receiver, conway-obstruction, finite-witness
expected_base_score: 60
expected_evidence_multiplier: 2.0
expected_final_score: 120
evidence_stage: proved-in-research
lean: proved-in-research
cycle: 5
score_reason: Cycle 4 の fork-local generator provenance から、global communication zero-cochain と selected `C0 -> C1` boundary map の exactness statement へ進める。boundary map は zero-cochain data を使わない selected defect gate に留まるため、score は中程度に抑える。
mathematical_interest: communication block ごとの owner support 選択を degree-zero cochain として固定し、その存在が selected support-fork defect の global boundary absorption と同値であることを Lean theorem にする。
goal_advancement: independent boundary map へ向けた最初の global exactness package。fork-local generator ではなく atlas 全体の zero-cochain existence を obstruction の消滅条件にする。
dullness_risk: `CommunicationZeroCochain` は `CommunicationCoverCompatible` と同値であり、selected boundary map はまだ finite defect への map に限定される。full quotient object、true sheaf cohomology、functorial comparison は主張しない。
proof_or_evidence_plan: `research/lean/ResearchLean/AG/SFT/ConwayBoundaryMap.lean` に global zero-cochain、boundary map、vanishing iff compatibility、generator-boundary factorization、finite example package を置く。
planned_theorem_names: CommunicationZeroCochain, communicationZeroCochain_nonempty_iff_compatible, SupportForkGlobalBoundaryMap, SupportForkDefectVanishesModuloGlobalBoundary, globalBoundary_vanishes_iff_compatible, globalBoundary_absorbs_defect, globalBoundary_absorbs_into_generatorBoundary, GlobalBoundaryReceiver, compatible_no_globalBoundaryReceiver, mismatchedSupportFork_notGlobalBoundaryVanishes, mismatchedAtlas_globalBoundaryReceiver, selectedGlobalBoundaryMapPackage
rival_advantage: owner mismatch dashboard can display inconsistency. This candidate records the stronger zero condition as global owner-support cochain exactness and proves the mismatched fork survives when no such cochain exists.
visible_projection: selected support fork, global communication zero-cochain, selected boundary map, global-boundary receiver.
protected_structure: communication cover, ownership cover, global owner support choice, support-fork defect.
exactness_or_minimality_claim: selected support-fork defect is absorbed by the global boundary map iff the communication cover is compatible with ownership. No full chain complex or sheaf cohomology exactness is claimed.
nonfaithfulness_or_failure_mode: deriving ownership from communication still creates a global zero-cochain by construction, while the independent mismatched atlas has no global zero-cochain.
previous_cycle_delta: upgrades Cycle 4's fork-local explicit generator witness to an atlas-level degree-zero cochain and a selected boundary exactness theorem.
rival_stress_test: rival must preserve not only local owner mismatch but also whether one global owner-support cochain absorbs all selected support-fork defects.
genius_potential: no
genius_target: not-applicable
genius_support_role: not-applicable
target_theorem: not-applicable
target_support_node: not-applicable
target_progress: not-applicable
proof_obligation_delta: not-applicable
target_completion_role: not-applicable
origin: G-sft-conway-01
tags: [sft, conway, boundary-map, exactness, zmod2, support-receiver]
created: 2026-07-04
---

# Global boundary map exactness

## 主張

Cycle 4 の fork-local boundary generator を、atlas 全体の
`CommunicationZeroCochain` と selected `SupportForkGlobalBoundaryMap` に持ち上げる。
support-fork defect が global boundary map で吸収されることは、communication cover が
ownership cover に compatible であることと同値である。

## 非自明性

`CommunicationZeroCochain` は単なる fork-local witness ではなく、全 communication block に
一貫して owner support を選ぶ data である。mismatched atlas ではこの global zero-cochain が存在せず、
canonical support fork は global boundary map で消えない。

## GOAL への前進

Conway 対応を「mismatch witness」から selected boundary exactness へ一段進める。
ただし、ここでの exactness は有限 selected vocabulary の範囲であり、full sheaf `H^1` ではない。

## SCORE 見込み

- `score_reason`: fork-local generator から global cochain exactness へ進むが、map は selected defect gate に留まるため base 60。
- `dullness_risk`: compatibility との同値なので過大評価しない。
- `proof_or_evidence_plan`: `lake env lean research/lean/ResearchLean/AG/SFT/ConwayBoundaryMap.lean`、
  `lake build ResearchLean.AG`、`#print axioms` で検証する。

## Lean evidence

- `research/lean/ResearchLean/AG/SFT/ConwayBoundaryMap.lean`
- `ResearchLean.AG.SFT.ConwayTwoTopology.CommunicationZeroCochain`
- `ResearchLean.AG.SFT.ConwayTwoTopology.communicationZeroCochain_nonempty_iff_compatible`
- `ResearchLean.AG.SFT.ConwayTwoTopology.SupportForkGlobalBoundaryMap`
- `ResearchLean.AG.SFT.ConwayTwoTopology.SupportForkDefectVanishesModuloGlobalBoundary`
- `ResearchLean.AG.SFT.ConwayTwoTopology.globalBoundary_vanishes_iff_compatible`
- `ResearchLean.AG.SFT.ConwayTwoTopology.globalBoundary_absorbs_defect`
- `ResearchLean.AG.SFT.ConwayTwoTopology.globalBoundary_absorbs_into_generatorBoundary`
- `ResearchLean.AG.SFT.ConwayTwoTopology.GlobalBoundaryReceiver`
- `ResearchLean.AG.SFT.ConwayTwoTopology.compatible_no_globalBoundaryReceiver`
- `ResearchLean.AG.SFT.ConwayTwoTopology.mismatchedSupportFork_notGlobalBoundaryVanishes`
- `ResearchLean.AG.SFT.ConwayTwoTopology.mismatchedAtlas_globalBoundaryReceiver`
- `ResearchLean.AG.SFT.ConwayTwoTopology.selectedGlobalBoundaryMapPackage`

## 審判メモ

- 厳密性: revise, base 60。bounded theorem として blocking finding はないが、`SupportForkGlobalBoundaryMap` は zero-cochain を使わず selected defect を返す。
- 研究価値: revise, base 60。global owner-support cochain は有用な frontier だが、独立 additive boundary には届かない。
- repo 全体価値: accept/revise, base 60。SFT research surface への橋として妥当だが、claim boundary を保つ。
- ライバル比較: revise, base 55-60。rival separation は local mismatch から global cochain gate へ進むが、まだ theorem packaging 寄り。

## 進捗ログ

- 2026-07-04: 作成。`lake env lean research/lean/ResearchLean/AG/SFT/ConwayBoundaryMap.lean`、
  `lake build ResearchLean.AG.SFT.ConwayBoundaryMap`、`lake build ResearchLean.AG` が通過。
  G2/G3 後、score を base 60 / final 120 に修正。
