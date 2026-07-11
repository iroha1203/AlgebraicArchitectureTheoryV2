---
status: picked
goal: G-aat-quality-surface-01
exploration_role: closer / unifier
candidate_type: genius-support / exact-kernel / viewer-criterion / projection-nonfaithfulness
capability_category: semantic-obstruction / projection-nonfaithfulness / repair-coherence / certificate-transport / quality-surface
expected_base_score: 75
expected_evidence_multiplier: 2.0
expected_final_score: 150
evidence_stage: proved-in-research
rival_advantage: Residual atom identity, not full atom-level equivalence and not component row equality, is the exact cover-relative information needed to reflect semantic repair closure.
origin: cycle-83
tags: [quality-surface, semantic-repair, residual-aware-reading, component-faithfulness, projection-nonfaithfulness, genius-support]
created: 2026-06-22
cycle: 83
lean: proved-in-research
---

# Semantic residual component faithfulness

## 主張

`SemanticRepairClosed` を、cover-relative な residual atom 上の support 保存として読む。
source support が semantic repair closed なら、target support が semantic repair closed であることは、
source と target が residual atom 上で同じ support status を持つことと同値である。

さらに、component projection しか保持しない reading については、semantic repair closure を
`ResidualComponentCoveredSupport` と `ResidualComponentFaithfulSupport` に分解する。
component coverage だけでは alias atom で residual component を覆ってしまうため足りない。
actual residual atom に戻る faithfulness が必要である。

## 候補種別

`genius-support` / `exact-kernel` / `viewer-criterion` / `projection-nonfaithfulness`

## 依拠

- Cycle 78: `SemanticRepairClosed`、`ResidualFiberSingleton`、selected refined semantic atom split。
- Cycle 81: `ResidualAliasGap`。
- Cycle 82: component-only reading と semantic-fiber-aware reading の positive / negative criterion。

## 非自明性

Cycle 82 は atom-level support equivalence が semantic repair closure reflection に十分であることを示したが、
その条件は trace atom のような cover 非 residual atom まで保持するため、この selected cover では過剰である。
Cycle 83 は closure に本当に必要な情報を residual atom 上の support equivalence として切り出し、
同時に component-only reading が失うものを component coverage と faithfulness の差として分解する。

## 数学的興味

semantic repair closure は「support が residual atom を hit する」述語である。
したがって reading の最小核は full semantic fiber ではなく、選んだ cover の residual subfiber である。
component projection は residual component coverage までは運ぶが、alias atom から actual residual atom へ戻る
faithfulness を持たない限り closure を反映しない。

## GOAL への前進

open genius target `Semantic repair-gluing obstruction theorem for finite atom-supported quality atlases` に対し、
semantic repair closure reflection の exact cover-relative reading condition と component-level factorization を Lean で固定する。
これは selected finite atlas obstruction を、viewer / reading が保持すべき semantic residual information の定理へ押し上げる。

## ライバルに対する有効性

ADL、component dashboard、conformance checker、component-projected AI review は component row coverage を保持できる。
しかし component row equality は residual component coverage だけを保証し、actual residual atom の support は保証しない。
AAT 側では、closure reflection に必要十分な residual atom identity と、component-only surface に欠ける faithfulness を theorem として分けられる。

## SCORE 見込み

- `score_reason`: Cycle 82 の十分条件を exact cover-relative condition へ鋭化し、Cycle 81 の alias gap を residual-component faithfulness failure として分類する。
- `dullness_risk`: 定義展開に近い部分がある。価値は `SemanticRepairClosed` の正確 reading kernel、component coverage / faithfulness 分解、semantic-fiber-aware より弱い selected witness を同時に固定した点にある。
- `proof_or_evidence_plan`: `SemanticResidualComponentFaithfulness.lean` で residual-aware reading、closure iff theorem、component coverage / faithfulness decomposition、selected surface failure、repair-frontier-only strictness witness、theorem package を証明する。

## CS / SWE への帰結

viewer / dashboard は semantic atom を全部表示しなくてもよいが、選んだ cover の residual atom status は保持する必要がある。
component row が green でも、actual residual obligation atom を alias atom で代替しているだけなら semantic repair closure は certified にならない。

## 証明・根拠

Lean 証拠は `research/lean/ResearchLean/AG/QualitySurface/SemanticResidualComponentFaithfulness.lean` に固定した。

- `ResidualAtomAwareReading`
- `residualAtomAwareReading_reflects_semanticRepairClosed`
- `residualAtomAwareReading_iff_target_semanticRepairClosed_of_source_closed`
- `semanticFiberAwareReading_implies_residualAtomAwareReading`
- `residualAliasGap_obstructs_residualAtomAwareReading`
- `ResidualComponentCoveredSupport`
- `ResidualComponentFaithfulSupport`
- `semanticRepairClosed_iff_residualComponentCovered_and_faithful`
- `residualFiberSingleton_implies_residualComponentFaithfulSupport`
- `sameComponentProjection_transfers_residualComponentCoverage`
- `componentProjection_reflects_semanticRepairClosed_of_residualComponentFaithful`
- `residualAliasGap_obstructs_residualComponentFaithfulSupport`
- `surfaceRepairSupport_residualComponentCovered`
- `surfaceRepairSupport_componentCovered_not_faithful`
- `surfaceRepairSupport_componentCoverage_without_semanticClosure`
- `repairFrontierOnlySupport`
- `complete_and_repairFrontierOnly_residualAtomAwareReading`
- `selected_residualAtomAwareReading_not_semanticFiberAware`
- `completeRepairSupport_closed_decomposes_as_componentCoverage_and_faithfulness`
- `semanticResidualComponentFaithfulness_package`

G3 実績:

- `focused Lean check: ResearchLean/AG/QualitySurface/SemanticResidualComponentFaithfulness.lean`: pass。
- `Research package build`: pass。
- `lake build`: pass。既存の `Formal/Arch/Extension/FeatureExtensionExamples.lean` linter warning のみ。
- axiom probe: generic theorem 群は axiom-free。selected witness / package は標準 `propext` のみ。`sorryAx`、custom axiom、`Classical.choice`、`unsafe` はない。
- `axiom|admit|sorry|unsafe` scan: 対象 Lean には該当なし。

## 審判メモ

- 厳密性: accept / base 65 / genius no。claim boundary は守るが、中心の iff と分解は定義展開に近い。`minimality` は絶対最小ではなく cover-relative exact kernel として書くべき。
- 研究価値: accept / base 80 / genius no。Cycle 82 の十分条件を exact cover-relative residual atom kernel へ鋭化し、open genius target の support node になる。
- repo 全体価値: accept / base 80 / genius no。Research Lean に閉じ、将来の paper / loss-aware viewer criterion へ接続できる。UI correctness や source extraction completeness は主張しない。
- ライバル比較: accept / base 85 / genius no。component-projected rival surface と actual residual atom identity / faithfulness の差分が明確。
- G4 SCORE 監査: reduce / base 75 / multiplier 2.0 / penalty 0 / final +150。total 11228 -> 11378。genius は support node であり unlock ではない。中心定理に定義展開に近い部分があるため、期待値 160 から減点した。

## 追加 required fields

- `mathematical_interest`: semantic repair closure の exact cover-relative reading kernel を residual atom support equivalence として切り出す。
- `goal_advancement`: semantic repair-gluing obstruction theorem の viewer / reading boundary を exact condition と component-faithfulness 分解へ進める。
- `planned_theorem_names`: `residualAtomAwareReading_iff_target_semanticRepairClosed_of_source_closed`, `semanticRepairClosed_iff_residualComponentCovered_and_faithful`, `semanticResidualComponentFaithfulness_package`
- `visible_projection`: component-only semantic reading / residual component coverage。
- `protected_structure`: residual atom identity, residual subfiber support, residual-component faithfulness。
- `exactness_or_minimality_claim`: closed source に対し、target closure は residual atom-aware reading と同値。semantic-fiber-aware reading は十分だが selected cover では過剰。全 residual atom の削除不能性や絶対最小性は主張しない。
- `nonfaithfulness_or_failure_mode`: target covers residual component through alias atom while missing actual residual atom。
- `previous_cycle_delta`: Cycle 82 の semantic-fiber-aware sufficient condition を exact residual-aware condition と component-faithfulness factorization へ鋭化する。
- `rival_stress_test`: component row equality can preserve residual component coverage but cannot certify residual atom support without faithfulness。
- `genius_potential`: support node
- `genius_target`: Semantic repair-gluing obstruction theorem for finite atom-supported quality atlases
- `genius_support_role`: exact residual-reading kernel and component-faithfulness decomposition for the open finite semantic repair-gluing obstruction target。

## 関連

- `research/ideas/g-aat-quality-surface-01-semantic-fiber-aware-viewer-criterion.md`
- `research/ideas/g-aat-quality-surface-01-semantic-residual-alias-nonfaithfulness.md`
- `research/ideas/g-aat-quality-surface-01-semantic-support-projection-kernel.md`

## 進捗ログ

- 2026-06-22: G1 closer / unifier candidate として picked。
- 2026-06-22: Lean 証拠を `SemanticResidualComponentFaithfulness.lean` に固定し、単体 `lake env lean` と `Research package build` が通った。
- 2026-06-22: G4 SCORE 監査で base 75 / final +150 に確定した。
