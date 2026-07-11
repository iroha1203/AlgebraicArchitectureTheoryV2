---
status: picked
goal: G-sft-conway-01
exploration_role: closer
candidate_type: obstruction
capability_category:
  - non-selected-span-family
  - selector-obstruction
  - restricted-span
  - conway-obstruction
expected_base_score: 60
expected_evidence_multiplier: 2.0
expected_final_score: 120
evidence_stage: proved-in-research
rival_advantage: CODEOWNERS / org-network analysis can list local owners, but not prove that explicit forkwise span choices fail to glue to one owner-uniform selector.
genius_potential: no
genius_target: not-applicable
genius_support_role: not-applicable
origin: G-sft-conway-01 Cycle 18
tags: [conway, owner-uniform, selector, restricted-span]
created: 2026-07-04
---

# Owner-uniform span selector obstruction

## 主張

Cycle 14 の unrestricted Sigma assembly と Cycle 15/16 の owner-uniform failure の差を、selected finite span-selector
obstruction として固定する。restricted two-fork family では、各 fork に対する explicit common-refinement span
selector は存在するが、それらを一つの shared owner に揃える owner-uniform selector は存在しない。

これは finite selected selector witness であり、canonical selector、arbitrary non-selected span functoriality、
arbitrary-cover naturality、true sheaf `H^1` は主張しない。

## 候補種別

`obstruction`

## 依拠

- `research/lean/ResearchLean/AG/SFT/ConwayCoherentFamilyExactness.lean`
- `research/lean/ResearchLean/AG/SFT/ConwayRestrictedCoherentFamily.lean`
- `research/lean/ResearchLean/AG/SFT/ConwayOwnerUniformSubfamilyDescent.lean`
- `research/lean/ResearchLean/AG/SFT/ConwayOwnerUniformSpanSelector.lean`

## 非自明性

`ForkwiseCommonRefinementSpanSelector` は各 fork の `CommonRefinementSupportsFork` を explicit witness として保持する。
`OwnerUniformSpanSelector` はそこに shared owner と各 selected refinement block がその owner を refine する条件を追加する。
この差により、local span choice の存在と owner-uniform global selector の存在を分離する。

## GOAL への前進

non-selected span family frontier に、overclaim しない finite selected witness を追加する。Cycle 18 の成果は、
「局所 span は選べるが、owner-uniform shared-owner selector には貼れない」という obstruction である。

## SCORE 見込み

- `score_reason`: Cycle 15/16 の owner-uniform failure を selector vocabulary へ上げ、local span choices と shared-owner gluing failure を同じ restricted finite family 上で分離する。
- `dullness_risk`: selector が `OwnerUniformCoherentCommonRefinementSupport` の別名になると base 45-50 に落ちる。explicit forkwise selector、shared-owner field、concrete restricted two-fork witness が必要。
- `proof_or_evidence_plan`: `ForkwiseCommonRefinementSpanSelector`、`OwnerUniformSpanSelector`、`OwnerUniformSpanSelectorObstruction` を定義し、restricted two-fork family の concrete forkwise selector と no owner-uniform selector、singleton subfamilies の owner-uniform selectors を証明した。
- `threshold_fit`: Cycle 18 は Issue #2962 の残り 150 に対して +120 見込みで、threshold 到達には次 cycle が必要である。

## Target Theorem 寄与

- `target_theorem`: not-applicable
- `target_support_node`: not-applicable
- `target_progress`: not-applicable
- `proof_obligation_delta`: not-applicable
- `target_completion_role`: not-applicable

## 証明・根拠

Lean で次を証明した。

- `ForkwiseCommonRefinementSpanSelector`
- `forkwiseSpanSelector_nonempty_iff_localSupport`
- `OwnerUniformSpanSelector`
- `OwnerUniformSpanSelector.toOwnerUniformSupport`
- `ownerUniformSpanSelector_nonempty_iff_support`
- `OwnerUniformSpanSelectorObstruction`
- `restrictedApiFork_commonRefinementSupport`
- `restrictedDbFork_commonRefinementSupport`
- `restrictedTwoForkFamily_forkwiseSpanSelectable`
- `restrictedTwoForkFamily_noOwnerUniformSpanSelector`
- `restrictedTwoForkFamily_ownerUniformSpanSelectorObstruction`
- `restrictedSingletonSubfamilies_ownerUniformSpanSelector`
- `selectedOwnerUniformSpanSelectorObstructionPackage`

## 審判メモ

- 厳密性: pass。`lake env lean`、module build、`FormalAGResearch`、full `lake build` が通過。
- 研究価値: revise accept。G2 は base 55/60/60 を推奨し、保守的に base 60 へ丸める。
- repo 全体価値: pass。restricted local span selection と owner-uniform global selector failure を分離した。
- ライバル比較: pass。local owner listing ではなく、explicit forkwise selector が global owner-uniform selector に glue しない theorem を返す。

## 関連

- `research/ideas/g-sft-conway-01-owner-uniform-restricted-family.md`
- `research/ideas/g-sft-conway-01-owner-uniform-subfamily-descent.md`
- `research/ideas/g-sft-conway-01-owner-uniform-family-quotient.md`

## 進捗ログ

- 2026-07-04: Cycle 18 候補として作成し、Lean 証明を追加。
- 2026-07-04: axiom audit は `sorryAx` なし。core selector structures は axiom-free、restricted finite witness package は `propext` のみに依存。
