---
status: picked
goal: G-sft-conway-01
exploration_role: g6-frontier / owner-choice-boundary
candidate_type: bridge
capability_category: owner-choice-boundary, finite-coefficient, support-receiver, conway-obstruction, finite-witness
expected_base_score: 60
expected_evidence_multiplier: 2.0
expected_final_score: 120
evidence_stage: proved-in-research
lean: proved-in-research
cycle: 6
score_reason: Cycle 5 の selected boundary map が zero-cochain value を使わない弱点を、owner choice を実際に読む boundary evaluation で改善する。ただし receiver は single-owner support と同値なので、score は中程度に抑える。
mathematical_interest: 任意 owner choice を degree-zero data とし、その選択 owner が fork の communication block を support する場合だけ selected defect を吸収する finite boundary evaluation を置く。
goal_advancement: global zero-cochain exactness と support receiver の間に、degree-zero value を実際に使う boundary evaluation layer を固定する。
dullness_risk: `SupportForkDefect` は still selected constant defect であり、owner-choice boundary absorption は `ForkHasSingleOwnerSupport` と同値。Cycle 2 receiver の再包装に近い面がある。
proof_or_evidence_plan: `research/lean/ResearchLean/AG/SFT/ConwayOwnerChoiceBoundary.lean` に owner choice, owner-choice boundary evaluation, absorption iff chosen-owner support, vanishing iff single-owner support, receiver equivalence, finite example package を置く。
planned_theorem_names: CommunicationOwnerChoice, OwnerChoiceSupportsFork, SupportForkOwnerChoiceBoundary, SupportForkDefectVanishesModuloOwnerChoiceBoundary, ownerChoiceBoundary_absorbs_iff_supportsFork, ownerChoiceBoundary_vanishes_iff_singleOwnerSupport, zeroCochain_ownerChoiceBoundary_absorbs, OwnerChoiceBoundaryReceiver, ownerChoiceBoundaryReceiver_iff_supportReceiver, compatible_no_ownerChoiceBoundaryReceiver, mismatchedSupportFork_notOwnerChoiceBoundaryVanishes, mismatchedAtlas_ownerChoiceBoundaryReceiver, selectedOwnerChoiceBoundaryPackage
rival_advantage: owner mismatch dashboard can show the mismatch. This candidate records whether a selected owner choice actually absorbs the support-fork defect, preserving the degree-zero value used in the boundary computation.
visible_projection: selected owner choice, support fork, chosen-owner support predicate, owner-choice boundary value.
protected_structure: owner choice value, communication block support, selected defect, support receiver equivalence.
exactness_or_minimality_claim: owner-choice boundary absorption is equivalent to single-owner support for the selected fork. No full cochain complex, functoriality, or sheaf `H^1` is claimed.
nonfaithfulness_or_failure_mode: mismatched split ownership has no owner choice that absorbs the canonical all-communication support fork.
previous_cycle_delta: fixes Cycle 5's immediate weakness by making boundary evaluation depend on degree-zero owner-choice data.
rival_stress_test: rival must preserve not just mismatch existence but whether a named owner choice supports and absorbs the selected fork defect.
genius_potential: no
genius_target: not-applicable
genius_support_role: not-applicable
target_theorem: not-applicable
target_support_node: not-applicable
target_progress: not-applicable
proof_obligation_delta: not-applicable
target_completion_role: not-applicable
origin: G-sft-conway-01
tags: [sft, conway, owner-choice, boundary-evaluation, zmod2]
created: 2026-07-04
---

# Owner-choice boundary evaluation

## 主張

Cycle 5 の global boundary map は zero-cochain value を使わなかった。Cycle 6 では
`CommunicationOwnerChoice` を置き、選ばれた owner が support fork の communication block を支える場合だけ
`SupportForkDefect` を吸収する selected boundary evaluation を定義する。

## 非自明性

boundary value は `OwnerChoiceSupportsFork choice fork` を読む。したがって、吸収判定は
degree-zero owner choice の値に依存する。ただし、存在量化した absorption は `ForkHasSingleOwnerSupport` と同値なので、
full complex ではなく finite receiver layer に留まる。

## GOAL への前進

Conway 対応の obstruction receiver を、少なくとも degree-zero owner choice を参照する boundary evaluation へ進める。
次 frontier は、support fork ごとの selected evaluation から global / additive / common-refinement aware な
`C0 -> C1` へ進めること。

## SCORE 見込み

- `score_reason`: Cycle 5 の直接弱点を改善するが、single-owner support との同値に留まるため base 60。
- `dullness_risk`: single-owner support との同値なので、過大評価しない。
- `proof_or_evidence_plan`: `cd research/lean && lake env lean ResearchLean/AG/SFT/ConwayOwnerChoiceBoundary.lean`、
  `旧Research aggregate build`、`#print axioms` で検証する。

## Lean evidence

- `research/lean/ResearchLean/AG/SFT/ConwayOwnerChoiceBoundary.lean`
- `ResearchLean.AG.SFT.ConwayTwoTopology.CommunicationOwnerChoice`
- `ResearchLean.AG.SFT.ConwayTwoTopology.OwnerChoiceSupportsFork`
- `ResearchLean.AG.SFT.ConwayTwoTopology.SupportForkOwnerChoiceBoundary`
- `ResearchLean.AG.SFT.ConwayTwoTopology.ownerChoiceBoundary_absorbs_iff_supportsFork`
- `ResearchLean.AG.SFT.ConwayTwoTopology.ownerChoiceBoundary_vanishes_iff_singleOwnerSupport`
- `ResearchLean.AG.SFT.ConwayTwoTopology.zeroCochain_ownerChoiceBoundary_absorbs`
- `ResearchLean.AG.SFT.ConwayTwoTopology.ownerChoiceBoundaryReceiver_iff_supportReceiver`
- `ResearchLean.AG.SFT.ConwayTwoTopology.mismatchedSupportFork_notOwnerChoiceBoundaryVanishes`
- `ResearchLean.AG.SFT.ConwayTwoTopology.selectedOwnerChoiceBoundaryPackage`

## 審判メモ

- 厳密性: revise, base 60。bounded finite theorem として blocking finding はないが、存在量化した absorption は `ForkHasSingleOwnerSupport` と完全同値。
- 研究価値: revise, base 60。Cycle 5 の value-insensitivity は改善するが、新しい obstruction receiver ではない。
- repo 全体価値: accept/revise, base 60。次 frontier への layer として妥当だが、claim boundary を保つ。
- ライバル比較: revise, base 55-60。chosen owner value の吸収判定は保存するが、rival separation はまだ theorem packaging 寄り。

## 進捗ログ

- 2026-07-04: 作成。`cd research/lean && lake env lean ResearchLean/AG/SFT/ConwayOwnerChoiceBoundary.lean`、
  `cd research/lean && lake build ResearchLean.AG.SFT.ConwayOwnerChoiceBoundary`、`旧Research aggregate build`、full `lake build` が通過。
  G2/G3 後、score を base 60 / final 120 に修正。
