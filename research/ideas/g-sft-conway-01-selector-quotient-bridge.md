---
status: picked
goal: G-sft-conway-01
exploration_role: unifier
candidate_type: bridge
capability_category:
  - selector-obstruction
  - finite-quotient-shadow
  - presentation-comparison
  - conway-obstruction
expected_base_score: 30
expected_evidence_multiplier: 2.0
expected_final_score: 60
evidence_stage: proved-in-research
rival_advantage: CODEOWNERS / org-network analysis can list local owner choices, but not prove that selected span-selector obstruction and quotient-style nonzero class are the same finite boundary.
genius_potential: no
genius_target: not-applicable
genius_support_role: not-applicable
origin: G-sft-conway-01 Cycle 19
tags: [conway, owner-uniform, selector, quotient, bridge]
created: 2026-07-04
---

# Owner-uniform selector / quotient bridge

## 主張

Cycle 17 の selected owner-uniform quotient-style receiver と Cycle 18 の selected span-selector obstruction を比較する。
selected finite vocabulary では、`OwnerUniformSpanSelector` の存在は `OwnerUniformFamilyClassVanishes` と同値であり、
`OwnerUniformSpanSelectorObstruction` は `ForkwiseCommonRefinementSpanSelectable` と
`OwnerUniformFamilyNonzeroClass` の conjunction と同値である。

これは selected finite presentation comparison であり、true quotient object、canonical selector、
arbitrary-cover naturality、true sheaf `H^1` は主張しない。

## 候補種別

`bridge`

## 依拠

- `research/lean/ResearchLean/AG/SFT/ConwayOwnerUniformFamilyQuotient.lean`
- `research/lean/ResearchLean/AG/SFT/ConwayOwnerUniformSpanSelector.lean`
- `research/lean/ResearchLean/AG/SFT/ConwayOwnerUniformSelectorQuotientBridge.lean`

## 非自明性

Cycle 17 と Cycle 18 は同じ owner-uniform support boundary を別々の presentation で読んでいた。
この bridge は、selector existence と quotient-style class vanishing が同じ有限境界を検出することを
theorem として固定し、forkwise selector だけでは quotient nonzero を消せないことを同じ statement 上で示す。

## GOAL への前進

selector obstruction と finite quotient shadow の間の比較面を追加し、Conway local/global boundary を
複数 presentation 間で移動できるようにする。

## SCORE 見込み

- `score_reason`: Cycle 17 の quotient-style receiver と Cycle 18 の selector obstruction を exact bridge に圧縮し、同じ selected finite obstruction の二表示として扱えるようにする。
- `dullness_risk`: 既存 iff の合成に近いため base は 30 に抑える。価値は新しい大型構造ではなく、presentation comparison と threshold closure にある。
- `proof_or_evidence_plan`: `ownerUniformSpanSelector_nonempty_iff_support` と `ownerUniformFamilyClass_vanishes_iff_support` を合成し、restricted two-fork family と singleton subfamilies の comparison package を Lean で証明した。
- `threshold_fit`: Cycle 18 後の 1970/2000 に対して +60 見込みで、active threshold を超える。

## Target Theorem 寄与

- `target_theorem`: not-applicable
- `target_support_node`: not-applicable
- `target_progress`: not-applicable
- `proof_obligation_delta`: not-applicable
- `target_completion_role`: not-applicable

## 証明・根拠

Lean で次を証明した。

- `ownerUniformSpanSelector_nonempty_iff_familyClassVanishes`
- `ownerUniformFamilyClassVanishes_of_spanSelector`
- `ownerUniformSpanSelector_of_familyClassVanishes`
- `ownerUniformFamilyNonzeroClass_iff_noSpanSelector`
- `ownerUniformSpanSelectorObstruction_iff_forkwiseSelectable_and_nonzeroClass`
- `ownerUniformFamilyNonzeroClass_of_spanSelectorObstruction`
- `ownerUniformSpanSelectorObstruction_of_forkwiseSelectable_nonzeroClass`
- `restrictedTwoForkFamily_spanSelectorObstruction_iff_familyClassNonzero`
- `restrictedTwoForkFamily_spanSelectorObstruction_implies_familyClassNonzero`
- `restrictedTwoForkFamily_familyClassNonzero_implies_spanSelectorObstruction`
- `restrictedSingletonSubfamilies_spanSelector_and_familyClassVanishes`
- `selectedOwnerUniformSelectorQuotientBridgePackage`

## 審判メモ

- 厳密性: accept。claim boundary は selected finite presentation comparison に限定。base 30 / final 60。
- 研究価値: accept。大型構造ではないが、Cycle 17/18 の独立成果を同じ obstruction として圧縮する。
- repo 全体価値: accept。SFT Conway research surface の quotient / selector interface を接続する。
- ライバル比較: accept。local owner listing ではなく、selector obstruction と quotient nonzero の同値を theorem として返す。

## 関連

- `research/ideas/g-sft-conway-01-owner-uniform-family-quotient.md`
- `research/ideas/g-sft-conway-01-owner-uniform-span-selector.md`

## 進捗ログ

- 2026-07-04: Cycle 19 候補として作成し、Lean bridge を追加。
- 2026-07-04: G2 A/B/C/D は全員 accept、base 30 / final 60。対象 Lean、module build、`旧Research aggregate`、full `lake build`、axiom audit は pass。
