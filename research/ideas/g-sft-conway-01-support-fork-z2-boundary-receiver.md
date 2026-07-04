---
status: picked
goal: G-sft-conway-01
exploration_role: obstruction / unifier / adversarial convergence
candidate_type: bridge
capability_category: boundary-quotient-receiver, finite-coefficient, support-receiver, conway-obstruction, finite-witness
expected_base_score: 55
expected_evidence_multiplier: 2.0
expected_final_score: 110
evidence_stage: proved-in-research
lean: proved-in-research
cycle: 3
score_reason: Cycle 2 receiver の selected finite coefficient rephrasing として、`ZMod 2` defect と boundary subgroup membership を固定する。functional ownership certificate で単なる Prop wrapper は部分的に越えるが、defect は定数で boundary subgroup は receiver predicate-driven なので低めの bridge score に留める。
mathematical_interest: Conway 障害を、単一 owner support で吸収できる boundary subgroup の外に残る selected defect として読む。
goal_advancement: support receiver を selected finite coefficient boundary-membership vocabulary へ移す。`CommonRefinementSpan` exactness、独立 boundary map、full quotient object、comparison functor failure は未固定のまま残す。
dullness_risk: `SupportNerveObstructionReceiver` の単なる Prop ラップに落ちる危険がある。`SupportForkDefect : ZMod 2`、`SupportForkBoundarySubgroup : AddSubgroup ConwayZ2`、`functionalFork_nonzeroClass` を根拠にする。
proof_or_evidence_plan: `Formal/AG/Research/SFT/ConwayBoundaryQuotient.lean` に selected `ZMod 2` defect、boundary subgroup、vanishing iff single-owner support、functional ownership non-boundary certificate、finite example package を置く。
planned_theorem_names: ConwayZ2, SupportForkDefect, SupportForkBoundarySubgroup, SupportForkDefectVanishesModuloBoundary, SupportForkNonzeroClass, supportForkDefect_nonzero, supportForkDefect_vanishes_iff_singleOwnerSupport, supportForkNonzeroClass_iff_noSingleOwnerSupport, BoundaryQuotientReceiver, boundaryQuotientReceiver_iff_supportReceiver, OwnershipFunctional, functionalFork_nonzeroClass, functionalFork_boundaryQuotientReceiver, mismatchedAtlas_ownershipFunctional, mismatchedSupportFork, mismatchedSupportFork_nonzeroClass, mismatchedAtlas_boundaryQuotientReceiver, compatible_no_boundaryQuotientReceiver, selectedBoundaryQuotientReceiverPackage
rival_advantage: owner mismatch dashboard は receiver を表示できる。この candidate の差分は、selected `ZMod 2` defect と predicate-driven boundary subgroup membership を Lean theorem package として保存する点に限定する。
visible_projection: selected support fork, `ZMod 2` defect, selected single-owner boundary subgroup.
protected_structure: independent communication/ownership cover data, support fork endpoints, functional ownership certificate, selected boundary membership.
exactness_or_minimality_claim: `BoundaryQuotientReceiver atlas ↔ SupportNerveObstructionReceiver atlas` at the selected receiver level. true sheaf cohomology, full `H^1`, arbitrary cover naturality, and comparison functor failure are not claimed.
nonfaithfulness_or_failure_mode: if a single owner supports the communication block, the selected defect vanishes modulo the boundary subgroup; without such support, the defect survives.
previous_cycle_delta: Cycle 2 receiver vocabulary is rephrased as selected finite coefficient boundary membership, plus a functional ownership non-boundary certificate.
rival_stress_test: rival can mark owner mismatch, but must also show whether the selected `1 : ZMod 2` defect lies in the selected boundary subgroup.
genius_potential: no
genius_target: not-applicable
genius_support_role: not-applicable
target_theorem: not-applicable
target_support_node: not-applicable
target_progress: not-applicable
proof_obligation_delta: not-applicable
target_completion_role: not-applicable
origin: G-sft-conway-01
tags: [sft, conway, boundary-quotient, zmod2, support-receiver]
created: 2026-07-04
---

# Support fork Z2 boundary receiver

## 主張

Cycle 2 の `SupportNerveFork` を selected degree-one cochain として読み、各 fork に
`SupportForkDefect fork = (1 : ZMod 2)` を割り当てる。単一 owner support が存在する場合は
selected boundary subgroup を `⊤`、存在しない場合は `⊥` とし、defect がその subgroup に入らないことを
nonzero boundary-quotient class として読む。

## 候補種別

`bridge`

## 依拠

- `research/GOALS.md` の `G-sft-conway-01`
- Cycle 2 report: `research/reports/G-sft-conway-01.md`
- Lean evidence: `Formal/AG/Research/SFT/ConwaySupportReceiver.lean`

## 非自明性

`BoundaryQuotientReceiver` 自体は selected receiver level で `SupportNerveObstructionReceiver` と同値だが、
Cycle 3 では `SupportForkDefect : ZMod 2` と `SupportForkBoundarySubgroup : AddSubgroup ConwayZ2` を明示し、
functional ownership から canonical mismatched fork の non-boundary class を導く。

## GOAL への前進

support receiver の住む場所を、selected finite coefficient の boundary membership として固定する。
これは true sheaf `H^1` や独立 boundary map ではなく、Cycle 2 receiver の finite coefficient rephrasing である。

## ライバルに対する有効性

Team Topologies、CODEOWNERS / org-network dashboard、AI review は owner mismatch を見つけられる。
この artifact は、selected defect が predicate-driven boundary subgroup に吸収されるかを Lean theorem として保存する点に限定して差分を持つ。

## SCORE 見込み

- `score_reason`: selected `ZMod 2` defect と boundary subgroup membership により、Cycle 2 receiver を finite coefficient vocabulary へ移すため base 55。
- `dullness_risk`: full `H^1` や full quotient object を過大主張しない。selected boundary membership と finite examples に限定する。
- `proof_or_evidence_plan`: `lake env lean Formal/AG/Research/SFT/ConwayBoundaryQuotient.lean`、`lake build FormalAGResearch`、`#print axioms` で検証する。

## 証明・根拠の見込み

Lean file:

- `Formal/AG/Research/SFT/ConwayBoundaryQuotient.lean`

Lean declarations:

- `Formal.AG.Research.SFT.ConwayTwoTopology.SupportForkDefect`
- `Formal.AG.Research.SFT.ConwayTwoTopology.SupportForkBoundarySubgroup`
- `Formal.AG.Research.SFT.ConwayTwoTopology.SupportForkDefectVanishesModuloBoundary`
- `Formal.AG.Research.SFT.ConwayTwoTopology.supportForkDefect_nonzero`
- `Formal.AG.Research.SFT.ConwayTwoTopology.supportForkDefect_vanishes_iff_singleOwnerSupport`
- `Formal.AG.Research.SFT.ConwayTwoTopology.supportForkNonzeroClass_iff_noSingleOwnerSupport`
- `Formal.AG.Research.SFT.ConwayTwoTopology.boundaryQuotientReceiver_iff_supportReceiver`
- `Formal.AG.Research.SFT.ConwayTwoTopology.functionalFork_nonzeroClass`
- `Formal.AG.Research.SFT.ConwayTwoTopology.mismatchedAtlas_ownershipFunctional`
- `Formal.AG.Research.SFT.ConwayTwoTopology.mismatchedSupportFork_nonzeroClass`
- `Formal.AG.Research.SFT.ConwayTwoTopology.mismatchedAtlas_boundaryQuotientReceiver`
- `Formal.AG.Research.SFT.ConwayTwoTopology.selectedBoundaryQuotientReceiverPackage`

## 審判メモ

- 厳密性: G3 は pass。claim は selected finite receiver に限定する。
- 研究価値: G2 B は revise / base 60、G2 D adversarial は revise / base 45-50。defect は定数で boundary subgroup は predicate-driven だが、functional ownership certificate で完全な Prop wrapper は部分的に越える。確定 base は 55。
- repo 全体価値: SFT 第V部 Conway 対応の boundary vocabulary として有用。ただし true quotient object / boundary map / sheaf `H^1` ではない。
- ライバル比較: rival に対する差分は selected `ZMod 2` defect の boundary subgroup membership theorem package に限定する。

## 関連

G1 obstruction / adversarial は finite `C^1/B^1`-style receiver を推奨した。closer はより小さい communication-shadow nonreflection を提案したが、Cycle 3 では score frontier を進めるため boundary receiver を picked とする。

## 進捗ログ

- 2026-07-04: 作成。`lake env lean Formal/AG/Research/SFT/ConwayBoundaryQuotient.lean` と
  `lake build Formal.AG.Research.SFT.ConwayBoundaryQuotient` が通過。`#print axioms` では
  `propext`, `Classical.choice`, `Quot.sound` 依存。G2/G3 後、score を base 55 / final 110 に修正。
