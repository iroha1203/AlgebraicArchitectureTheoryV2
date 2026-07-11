---
status: picked
goal: G-aat-quality-surface-01
exploration_role: criterion
candidate_type: genius-support / viewer-criterion / projection-nonfaithfulness
capability_category: semantic-obstruction / projection-nonfaithfulness / repair-coherence / certificate-transport / quality-surface
expected_base_score: 65
expected_evidence_multiplier: 2.0
expected_final_score: 130
evidence_stage: proved-in-research
rival_advantage: Component-only readings can hide residual-alias gaps, while semantic-fiber-aware readings preserve actual residual atom identity and therefore reflect semantic repair closure.
origin: cycle-82
tags: [quality-surface, semantic-repair, semantic-fiber, viewer-criterion, projection-nonfaithfulness, genius-support]
created: 2026-06-22
cycle: 82
lean: proved-in-research
---

# Semantic-fiber-aware viewer criterion

## 主張

component-only semantic reading は、semantic support を protected component projection まで落とす。
semantic-fiber-aware reading は、support を semantic atom level で保持する。

Lean 上で、semantic-fiber-aware reading は semantic repair closure を反映する。
一方、Cycle 81 の residual alias gap がある selected witness では、component-only reading は complete support と surface support を同一視するが、semantic repair closure は反映できない。

## 候補種別

`genius-support` / `viewer-criterion` / `projection-nonfaithfulness`

## 依拠

- Cycle 78: refined semantic repair atom と component projection。
- Cycle 81: `ResidualAliasGap` による component-projection closure nonfaithfulness。

## 非自明性

Cycle 81 は residual alias gap の obstruction criterion を与えた。
Cycle 82 はそれを reading / viewer criterion に変換し、どの reading surface が semantic repair closure を反映できるかを分ける。

重要なのは、これは実 UI の claim ではない点である。
Lean 上の reading predicate として、component-only reading と semantic-fiber-aware reading を分ける。

## 数学的興味

semantic repair closure は actual residual atom identity に依存する。
component support だけを保持する reading では alias atom と actual residual atom が同じ component row に潰れる。
semantic-fiber-aware reading は atom-level support equivalence を保持するため、closure を反映できる。

## GOAL への前進

open genius target `Semantic repair-gluing obstruction theorem for finite atom-supported quality atlases` に対して、semantic residual fiber を保持する reading surface が closure reflection に十分であることを切り出す。
これは parametric obstruction theorem ではないが、semantic repair-gluing obstruction を tooling / visualization surface に落とすための finite reading criterion である。

## ライバルに対する有効性

component dashboard や component-projected AI-review summary は component row coverage を表示できる。
しかし actual residual atom と alias atom を同じ row に潰す限り、semantic repair closure を certify できない。
semantic-fiber-aware reading はこの gap を回避する十分な reading surface を示す。

## SCORE 見込み

- `score_reason`: residual alias obstruction を viewer / reading criterion に転換し、component-only reading の不忠実性と semantic-fiber-aware reading の positive reflection を Lean で固定する。
- `dullness_risk`: 実装/UI ではなく Lean predicate の reading criterion であり、Cycle 81 の応用に近い。価値は positive/negative pair と viewer boundary にある。
- `proof_or_evidence_plan`: `SemanticFiberAwareViewerCriterion.lean` で component-only reading、semantic-fiber-aware reading、positive reflection theorem、alias-gap no-go theorem、selected witness package を証明する。

## CS / SWE への帰結

viewer / dashboard は component row の green status だけでは selected alias-gap witness の semantic repair closure を伝えられない。
semantic residual atom identity を保持する drill-down / fiber-aware reading は、この witness で失われる closure information を保つ十分な surface である。

## 証明・根拠

Lean 証拠は `research/lean/ResearchLean/AG/QualitySurface/SemanticFiberAwareViewerCriterion.lean` に固定した。

- `ComponentOnlySemanticReading`
- `SemanticFiberAwareReading`
- `semanticFiberAwareReading_reflects_semanticRepairClosed`
- `not_semanticFiberAwareReading_of_residualAliasGap`
- `componentOnlyReading_not_reflect_semanticRepairClosed_of_aliasGap`
- `residualAliasGap_obstructs_componentOnlyViewerReflection`
- `selected_componentOnlyReading_complete_surface`
- `selected_not_semanticFiberAwareReading_complete_surface`
- `selected_componentOnlyReading_not_reflects_semanticClosure`
- `selected_componentOnlyViewerReflection_fails`
- `semanticFiberAwareViewerCriterion_package`

G3 実績:

- `cd research/lean && lake env lean ResearchLean/AG/QualitySurface/SemanticFiberAwareViewerCriterion.lean`: pass。
- `cd research/lean && lake build ResearchLean`: pass。
- axiom probe: generic reading/reflection lemmas は axiom-free。selected component-only no-go / package は標準 `propext` のみ。`sorryAx`、custom axiom、`Classical.choice`、`unsafe` はない。

## 審判メモ

- 厳密性: accept / base 70 / genius support。positive theorem は強い pointwise support equivalence を仮定する十分条件であり、最小性は未証明。
- 研究価値: accept / base 65 / genius support。Cycle 81 の residual alias obstruction を reading / viewer criterion に変換する有効な follow-up。
- repo 全体価値: accept / base 65。viewer wording は safe だが、Cycle 81 の再包装に近い。
- ライバル比較: accept / base 75 / genius support。component-only dashboard / component-projected AI review との差分は明確。
- G4 SCORE 監査: confirm / base 65 / multiplier 2.0 / penalty 0 / final +130。total 11098 -> 11228。genius は support node であり unlock ではない。

## 追加 required fields

- `mathematical_interest`: semantic-fiber-aware reading is a sufficient reading surface for semantic repair closure reflection, while component-only reading fails on residual alias gaps.
- `goal_advancement`: semantic repair-gluing obstruction の viewer / reading boundary を Lean-proved finite criterion として追加する。
- `planned_theorem_names`: `semanticFiberAwareReading_reflects_semanticRepairClosed`, `componentOnlyReading_not_reflect_semanticRepairClosed_of_aliasGap`, `semanticFiberAwareViewerCriterion_package`
- `visible_projection`: component-only semantic reading。
- `protected_structure`: semantic atom support equivalence, actual residual atom identity, residual alias gap。
- `exactness_or_minimality_claim`: semantic-fiber-aware reading reflects semantic repair closure; component-only reading does not in the selected alias witness。
- `nonfaithfulness_or_failure_mode`: component row coverage hides actual residual atom absence behind an alias atom。
- `previous_cycle_delta`: Cycle 81 residual alias obstruction から viewer / reading criterion へ進める。
- `rival_stress_test`: component-only dashboards cannot certify semantic repair closure unless semantic atom identity is retained。
- `genius_potential`: support node
- `genius_target`: Semantic repair-gluing obstruction theorem for finite atom-supported quality atlases
- `genius_support_role`: finite reading criterion for exposing semantic residual fibers in quality-surface visualization。

## 関連

- `research/ideas/g-aat-quality-surface-01-semantic-residual-alias-nonfaithfulness.md`
- `research/ideas/g-aat-quality-surface-01-visible-local-semantic-gluing-obstruction.md`
- `research/ideas/g-aat-quality-surface-01-semantic-support-projection-kernel.md`

## 進捗ログ

- 2026-06-22: G1 viewer criterion candidate として semantic-fiber-aware viewer criterion を提示し、Cycle 82 picked とした。
- 2026-06-22: Lean 証拠を `SemanticFiberAwareViewerCriterion.lean` に固定し、単体 `lake env lean`、`cd research/lean && lake build ResearchLean`、axiom probe が通った。
