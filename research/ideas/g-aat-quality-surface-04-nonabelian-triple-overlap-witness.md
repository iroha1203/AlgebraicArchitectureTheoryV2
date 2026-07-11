---
status: picked
goal: G-aat-quality-surface-04
exploration_role: obstruction / unifier
candidate_type: target-support
capability_category: nonabelian-transition / higher-triple-overlap / layer-independence / anti-weakening
expected_base_score: 88
expected_evidence_multiplier: 2.0
expected_final_score: 176
evidence_stage: proved-in-research
rival_advantage: ADL, static analysis, conformance checkers, metric dashboards, and AI review can detect local transition disagreements, but this candidate proves how noncommuting repair-choice transitions and triple-overlap defects obstruct the finite semantic repair obstruction tower beyond first-layer H1.
genius_potential: no
genius_target: none
genius_support_role: not-applicable
target_theorem: Universal Semantic Repair Obstruction Tower Theorem
target_support_node: nonabelian torsor transition and higher triple-overlap witness
target_progress: support-node
proof_obligation_delta: Adds finite nonabelian repair-choice transition and triple-overlap defect witnesses showing that first-layer H1 vanishing alone does not imply tower vanishing or global semantic repair coherence.
target_completion_role: checkpoint support; not target completion by itself.
origin: G-04
tracking_issue: 2488
parent_tracking_issue: 2482
tags: [quality-surface, semantic-repair, obstruction-tower, nonabelian, higher-coherence, target-support]
created: 2026-06-24
cycle: 4
lean: proved-in-research
---

# Nonabelian Triple-Overlap Witness

## 主張

finite/small obstruction tower の後続層を Bool token のまま放置せず、有限 repair-choice transition layer を別に定義し、非可換な selected pair と triple-overlap coherence defect を Lean で固定する。

`TransitionLayerSoundness` は一方向の soundness bridge だけを持つ。すなわち tower token が vanish するなら対応する selected transition law は coherent である、という形に限定する。`ObstructionTowerVanishes`、`GlobalSemanticRepairCoherent`、target equivalence、nonabelian cohomology completion、stack effectiveness は field に入れない。

## 候補種別

`target-support`

## 依拠

- Cycle 1: `SemanticRepairObstructionTower.lean`
- Cycle 2: `SemanticRepairAdequacyDischarge.lean`
- Cycle 3: `SemanticRepairTowerFunctoriality.lean`
- G1 obstruction / unifier の nonabelian transition / triple-overlap witness proposal。

## 非自明性

Cycle 1/2 では nonabelian / higher / stack layer は finite Bool token と identity discharge に留まった。この候補は、first-layer `H1Vanishes` が成立しても、repair-choice pair が非可換で triple-overlap coherence defect が残る小 tower を構成し、global coherence が出ないことを theorem にする。

## 数学的興味

semantic repair gluing obstruction tower は abelian `H1` だけではない。choice twisting と higher coherence failure を separate layer として読み、first-layer boundary と後続層の独立性を有限 witness として固定する。

## GOAL への前進

G6 残 blocker の `richer nonabelian torsor transition law` と `higher triple-overlap witness` を finite/small checkpoint として減らす。ただし full nonabelian cohomology、arbitrary higher stack、true sheaf `H1`、concrete ArchSig finite shadow connection はまだ残る。

## ライバルに対する有効性

局所 transition disagreement は多くの analyzer でも検出できる。しかし、その disagreement が first-layer `H1` boundary とは別に tower vanish / global coherence を妨げる層としてどう現れるかを、anti-weakening を守って theorem 化する点が AAT 側の差分である。

## SCORE 見込み

- `score_reason`: G-04 の nonabelian / higher blocker を直接減らす。Lean proof / axiom audit / formalization quality audit が clean なら base 90 / x2.0 を期待する。
- `dullness_risk`: Bool token の名前替えだけなら低得点。selected finite noncommuting transition layer、triple-overlap defect、first-layer H1 vanishing but no tower/global witness を同時に固定する必要がある。
- `proof_or_evidence_plan`: `RepairChoiceToken`、`FiniteRepairChoiceTransitionLayer`、`TransitionLayerSoundness` を定義し、noncommuting pair と triple-overlap defect が torsor / higher token vanish を阻害する theorem、さらに selected finite tower witness を Lean で証明する。
- `planned_theorem_names`: `RepairChoiceToken`, `FiniteRepairChoiceTransitionLayer`, `TransitionLayerSoundness`, `noncommuting_obstructs_nonabelianTorsorTrivial`, `tripleOverlapDefect_obstructs_higherCoherenceVanishes`, `noncommuting_obstructs_globalRepairCoherent`, `tripleOverlapDefect_obstructs_globalRepairCoherent`, `selectedTransitionLayer_pairNoncommuting`, `selectedTransitionLayer_tripleOverlapDefect`, `selectedTransitionDefectTower_h1Vanishes`, `selectedTransitionDefectTower_not_obstructionTowerVanishes`, `selectedTransitionDefectTower_not_globalCoherent`, `h1Vanishes_not_enough_for_globalCoherent_due_transitionDefect`, `finiteNonabelianTripleOverlap_package`

## Target Theorem 寄与

- `target_theorem`: `Universal Semantic Repair Obstruction Tower Theorem`
- `target_support_node`: nonabelian torsor transition and higher triple-overlap witness
- `target_progress`: `support-node`
- `proof_obligation_delta`: first-layer `H1` vanishing と後続 nonabelian/higher layers の独立性を finite witness として証明する。
- `target_completion_role`: checkpoint support; full target completion には true sheaf `H1`、concrete finite shadow connection、G6 completion audit が残る。

## 証明・根拠

Lean file: `research/lean/ResearchLean/QualitySurface/SemanticRepairNonabelianTriple.lean`

`RepairChoiceToken` は `left`, `right`, `leftRight`, `rightLeft` を持ち、`left ∘ right = leftRight` かつ `right ∘ left = rightLeft` となる有限 composition table を持つ。selected layer は `g01 = left`, `g12 = right`, `g02 = rightLeft` とし、pair noncommuting と triple-overlap defect を同時に持つ。

selected tower は `H1Vanishes` を満たすが、`torsorObstruction = true`、`higherObstruction = true` として、`ObstructionTowerVanishes` と `GlobalSemanticRepairCoherent` を満たさない。これは full nonabelian cohomology ではなく、finite tower token が richer transition witness を必要とすることの support-node である。

## 審判メモ

- SCORE 監査: G4 は reduce / base_score 88 / evidence_multiplier 2.0 / penalty 0 / final_score 176 / support-node と判定。selected witness の `TransitionLayerSoundness` が obstructed tower 上では一部 vacuous に成立するため、90 から 88 へ下げて記録する。
- 厳密性: G2 A は accept / base_score 85 / support-node。`TransitionLayerSoundness` は one-way bridge に限定され、tower vanishing / global coherence / target equivalence / full nonabelian cohomology を field 化していないと判定。ただし selected witness の bridge が obstructed tower 上では vacuous に立つ点を過大評価しないこと。
- 厳密性対応: 初回 axiom audit で selected transition layer に `propext` が出たため、`FiniteRepairChoiceTransitionLayer` を type-parameterized structure にし、`repairChoiceCompose` を全ケース明示の finite composition table に修正した。修正後 `.tmp/g04_nonabelian_triple_axioms.lean` は全対象 axiom-free。
- 研究価値: G2 B は accept / base_score 90 / support-node。true nonabelian `H^1` / `H^2` / stacky descent ではないため 95 以上ではないが、G-04 の nonabelian torsor obstruction / higher obstruction blocker を直接進めると判定。
- repo 全体価値: G2 C は accept / base_score 88 / support-node。G-01 の holonomy / commutator 系で積んできた有限 witness による hidden obstruction 分離を、G-04 tower の後続層へ自然に接続するものと判定。
- ライバル比較: G2 D は accept / base_score 85 / support-node。local disagreement detection の言い換えではなく、first-layer `H1Vanishes` と独立に tower vanish / global coherence を妨げる後続層として theorem 化している点を評価。ただし `h1Vanishes_not_enough_for_globalCoherent_due_transitionDefect` を中心証拠にし、単なる noncommuting detection として過大評価しないこと。

## 関連

- Cycle 1 candidate: `g-aat-quality-surface-04-finite-semantic-repair-obstruction-tower-package.md`
- Cycle 2 candidate: `g-aat-quality-surface-04-finite-layered-repair-certificate-discharge.md`
- Cycle 3 candidate: `g-aat-quality-surface-04-layered-repair-tower-functoriality.md`

## 進捗ログ

- 2026-06-24: Cycle 3 merge 後、nonabelian / higher blocker に対応する candidate として作成。
- 2026-06-24: Lean evidence として `SemanticRepairNonabelianTriple.lean` を追加し、candidate を picked / proved-in-research に更新。
- 2026-06-24: `.tmp/g04_nonabelian_triple_axioms.lean` で reported declarations の `#print axioms` を確認し、全対象が `does not depend on any axioms` であることを確認。
