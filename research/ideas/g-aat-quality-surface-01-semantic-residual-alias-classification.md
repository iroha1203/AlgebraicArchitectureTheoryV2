---
status: picked
goal: G-aat-quality-surface-01
exploration_role: closer / unifier / obstruction
candidate_type: genius-support / classification / projection-nonfaithfulness
capability_category: semantic-obstruction / projection-nonfaithfulness / repair-coherence / certificate-transport / quality-surface
expected_base_score: 65
expected_evidence_multiplier: 2.0
expected_final_score: 130
evidence_stage: proved-in-research
rival_advantage: Under the same component projection, an explicit missed semantic residual is exactly a residual alias gap, so component row equality classifies the alias failure mode rather than merely showing a selected counterexample.
origin: cycle-84
tags: [quality-surface, semantic-repair, residual-alias, classification, projection-nonfaithfulness, genius-support]
created: 2026-06-22
cycle: 84
lean: proved-in-research
---

# Semantic residual alias classification

## 主張

same component projection の下では、`ResidualAliasGap` は明示的な `MissedSemanticResidual` と同値である。
source support が actual residual atom を持ち、target support がその residual atom を欠くなら、same component projection によって target support は同じ component を何らかの alias atom で覆っていなければならない。

これは Cycle 81 の residual-alias sufficient obstruction を、constructive な missed-residual normal form へ閉じる分類 theorem である。
`¬ SemanticRepairClosed` から存在 witness を取り出す古典化は行わず、明示的 missed residual witness に相対化して分類する。

## 候補種別

`genius-support` / `classification` / `projection-nonfaithfulness`

## 依拠

- Cycle 81: `ResidualAliasGap` と component-projection closure nonfaithfulness。
- Cycle 83: missed actual residual atom と residual-component faithfulness failure の境界。

## 非自明性

Cycle 81 は residual alias gap が semantic repair closure を壊す十分条件だった。
Cycle 84 は、same component projection の仮定下では、actual residual atom が target で missed される positive witness がそのまま alias gap を生成することを示す。
これにより、component row が同じなのに closure が壊れる失敗は、単なる selected witness ではなく missed residual normal form として読める。

## 数学的興味

component projection は source の residual component support を target の component support へ運ぶ。
target が actual residual atom を欠く場合、その component support は必ず別の target-supported atom、すなわち alias atom として現れる。
この normal form は、component projection が失う情報を「残差 atom の identity」へ正確に圧縮する。

## GOAL への前進

open genius target `Semantic repair-gluing obstruction theorem for finite atom-supported quality atlases` に対し、
semantic repair-gluing obstruction の component-projection failure mode を alias gap / missed residual の constructive classification として固定する。

## ライバルに対する有効性

ADL、conformance checker、dashboard、component-projected AI review は component row coverage を保持できる。
しかし same component row の下で actual residual atom が missed されると、target row coverage は alias atom による coverage として分類される。
AAT はこの alias failure mode を theorem として固定できる。

## SCORE 見込み

- `score_reason`: Cycle 81 の sufficient obstruction と Cycle 83 の residual faithfulness boundary を、same component projection 下の missed-residual classification に閉じる。
- `dullness_risk`: Cycle 81 / 83 にかなり近い support lemma。価値は selected counterexample ではなく constructive normal form にした点にある。
- `proof_or_evidence_plan`: `SemanticResidualAliasClassification.lean` で `MissedSemanticResidual`、alias gap iff theorem、target closure obstruction、selected witness package を証明する。

## CS / SWE への帰結

component row が green でも actual residual atom が missed されていれば、green は alias atom による coverage である。
viewer / review surface は、その alias coverage と actual residual obligation の mismatch を residual-level witness として表示する必要がある。

## 証明・根拠

Lean 証拠は `research/lean/ResearchLean/AG/QualitySurface/SemanticResidualAliasClassification.lean` に固定した。

- `MissedSemanticResidual`
- `missedSemanticResidual_of_residualAliasGap`
- `residualAliasGap_of_missedSemanticResidual_of_sameComponentProjection`
- `residualAliasGap_iff_missedSemanticResidual_of_sameComponentProjection`
- `missedSemanticResidual_obstructs_target_semanticRepairClosed`
- `target_semanticRepairClosed_obstructs_missedSemanticResidual`
- `semanticRepairClosed_nonfaithful_of_missedResidual`
- `aliasAtom_ne_residual_of_residualAliasGap`
- `selected_missedRepairFrontierResidual`
- `selected_residualAliasGap_iff_missedResidual`
- `selected_missedResidual_obstructs_surfaceClosure`
- `selected_semanticRepairClosed_nonfaithful_of_missedResidual`
- `selected_aliasAtom_ne_residual`
- `semanticResidualAliasClassification_package`

G3 実績:

- `focused Lean check: ResearchLean/AG/QualitySurface/SemanticResidualAliasClassification.lean`: pass。
- `Research module build: ResearchLean.AG.QualitySurface.SemanticResidualAliasClassification`: pass。
- `Research package build`: pass。
- `lake build`: pass。既存の `Formal/Arch/Extension/FeatureExtensionExamples.lean` linter warning のみ。
- axiom probe: generic theorem 群は axiom-free。selected witness / package は標準 `propext` のみ。`sorryAx`、custom axiom、`Classical.choice`、`unsafe` はない。
- `git diff --check`: pass。
- hidden / bidirectional Unicode scan: pass。
- local path scan: pass。

## 審判メモ

- 厳密性: accept / base 60 / genius no。claim boundary は守るが、`ResidualAliasGap` 定義と same component projection の存在量化に近い。
- 研究価値: accept / base 75 / genius no。Cycle 81 sufficient obstruction と Cycle 83 faithfulness boundary を missed-residual normal form に圧縮する support node。
- repo 全体価値: accept / base 70 / genius no。Research / paper seed / future bounded viewer vocabulary へ接続するが、tooling runtime 価値はまだ間接的。
- ライバル比較: accept / base 80 / genius no。component-projected rival surface では actual residual atom と alias atom の identity 差を復元できないことを分類できる。
- G4 SCORE 監査: reduce / base 65 / multiplier 2.0 / penalty 0 / final +130。total 11378 -> 11508。genius は support node であり unlock ではない。中心の iff は有用だが、`ResidualAliasGap` 定義と same component projection から alias witness を取り出す構造に近いため減点した。

## 追加 required fields

- `mathematical_interest`: same component projection の下で missed residual と residual alias gap が一致する constructive normal form。
- `goal_advancement`: semantic repair-gluing obstruction target の projection failure mode を分類 theorem として固定する。
- `planned_theorem_names`: `residualAliasGap_iff_missedSemanticResidual_of_sameComponentProjection`, `semanticRepairClosed_nonfaithful_of_missedResidual`, `semanticResidualAliasClassification_package`
- `visible_projection`: same component projection。
- `protected_structure`: actual residual atom, missed residual witness, alias atom, semantic repair closure。
- `exactness_or_minimality_claim`: same component projection と explicit missed residual witness に相対化した alias-gap classification。bare `¬ SemanticRepairClosed` から witness を抽出する主張はしない。
- `nonfaithfulness_or_failure_mode`: component row coverage is realized by an alias atom while the actual residual atom is absent。
- `previous_cycle_delta`: Cycle 83 の residual-component faithfulness failure を alias-gap normal form へ閉じる。
- `rival_stress_test`: component row equality cannot distinguish actual residual support from alias coverage。
- `genius_potential`: support node
- `genius_target`: Semantic repair-gluing obstruction theorem for finite atom-supported quality atlases
- `genius_support_role`: constructive normal form for component-projection semantic repair failure。

## 関連

- `research/ideas/g-aat-quality-surface-01-semantic-residual-component-faithfulness.md`
- `research/ideas/g-aat-quality-surface-01-semantic-residual-alias-nonfaithfulness.md`
- `research/ideas/g-aat-quality-surface-01-semantic-fiber-aware-viewer-criterion.md`

## 進捗ログ

- 2026-06-22: G1 closer / unifier / obstruction candidate として picked。
- 2026-06-22: Lean 証拠を `SemanticResidualAliasClassification.lean` に固定し、単体 `lake env lean` が通った。
- 2026-06-22: G4 SCORE 監査で base 65 / final +130 に確定した。
