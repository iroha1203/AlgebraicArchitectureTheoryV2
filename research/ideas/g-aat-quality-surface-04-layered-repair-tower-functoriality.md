---
status: picked
goal: G-aat-quality-surface-04
exploration_role: closer / unifier
candidate_type: target-support
capability_category: functoriality / cover-refinement / site-morphism / profile-law-transport / anti-weakening
expected_base_score: 90
expected_evidence_multiplier: 2.0
expected_final_score: 180
evidence_stage: proved-in-research
rival_advantage: ADL, static analysis, conformance checkers, metric dashboards, and AI review can compare local artifacts across versions, but this candidate proves which finite obstruction-tower data are transported by an explicit morphism and which reflection claims require separate lift certificates.
genius_potential: no
genius_target: none
genius_support_role: not-applicable
target_theorem: Universal Semantic Repair Obstruction Tower Theorem
target_support_node: finite/small obstruction tower functoriality theorem
target_progress: support-node
proof_obligation_delta: Adds a finite tower morphism and prism transport surface for cover-refinement / site-morphism / profile-law functoriality without hiding tower vanishing or global coherence in the morphism fields.
target_completion_role: checkpoint support; not target completion by itself.
origin: G-04
tracking_issue: 2486
parent_tracking_issue: 2482
tags: [quality-surface, semantic-repair, obstruction-tower, functoriality, target-support]
created: 2026-06-24
cycle: 3
lean: proved-in-research
---

# Layered Repair Tower Functoriality

## 主張

`FiniteSemanticRepairObstructionTower` の finite/small target boundary に対し、`C0/C1/C2` の写像、`delta0/delta1` 可換性、selected residual 保存、有限 shadow 保存、boundary primitive lift だけを持つ `FiniteObstructionTowerMorphism` を定義する。

その morphism から、`H1Vanishes` の保存、明示 lift certificate の下での `H1Vanishes` reflection、`H1Nonzero` の transport、`LayeredRepairDischargePrism` の transport、prism 版 `ObstructionTowerVanishes` / `GlobalSemanticRepairCoherent` の preservation を証明する。morphism field には `ObstructionTowerVanishes`、`GlobalSemanticRepairCoherent`、`H1Vanishes` reflection、torsor triviality、stack effectiveness、target equivalence を入れない。

## 候補種別

`target-support`

## 依拠

- Cycle 1: `SemanticRepairObstructionTower.lean`
- Cycle 2: `SemanticRepairAdequacyDischarge.lean`
- transport references: `SemanticResidualTransportNaturality.lean`, `SemanticResidualIndexedTransport.lean`, `SemanticResidualAtlasMorphism.lean`
- GOAL `G-aat-quality-surface-04` の functoriality blocker / anti-weakening rule。

## 非自明性

Cycle 1/2 は single finite tower 上で target-boundary theorem と material premise discharge を与えたが、cover-refinement、site-morphism、profile-law change で tower data がどう運ばれるかは未証明のままだった。この候補は、functoriality を「自然に保存される」という説明で済ませず、cochain-level map と boundary lift certificate に分解する。

## 数学的興味

obstruction tower が本当に幾何的対象なら、対象ごとの theorem だけでなく、cover や reading の変更に対する transport law が必要になる。ここでは finite/small boundary に限定し、`H1` boundary と discharge prism の functoriality を Lean theorem として固定する。

## GOAL への前進

G6 残 blocker の `cover-refinement / site-morphism / profile-law functoriality theorem` を直接減らす。ただし true sheaf `H1`、richer nonabelian / higher witness、concrete ArchSig finite shadow connection はまだ残る。

## ライバルに対する有効性

ADL や static analysis は artifact 間の mapping や diff を扱えるが、その mapping が obstruction class、boundary witness、material premise discharge をどう保存・反射するかまでは証明しない。この候補は、version/profile/cover change を finite tower morphism として監査可能にする。

## SCORE 見込み

- `score_reason`: G-04 functoriality blocker を直接減らし、Cycle 1/2 の theorem surface を transport 可能にする。Lean proof / axiom audit / formalization quality audit が clean なら base 90 / x2.0 を期待する。
- `dullness_risk`: morphism field に `ObstructionTowerVanishes`、`GlobalSemanticRepairCoherent`、`H1Vanishes` reflection、target equivalence を入れると失格。単なる identity map theorem だけなら低得点。
- `proof_or_evidence_plan`: `FiniteObstructionTowerMorphism`、`BoundaryLiftCertificate`、`DischargePrismTransport` を定義し、`h1Vanishes_of_towerMorphism`, `h1Vanishes_reflects_of_boundaryLift`, `h1Nonzero_transport_of_boundaryLift`, `dischargePrism_transport`, `globalRepairCoherent_transport_of_dischargePrism` を Lean で証明する。G2 A の指摘に従い、reflection は morphism field ではなく target boundary primitive の source lift certificate としてだけ置く。
- `planned_theorem_names`: `FiniteObstructionTowerMorphism`, `cechZ1_of_towerMorphism`, `cechB1_of_towerMorphism`, `h1Vanishes_of_towerMorphism`, `finiteShadowTrivial_of_towerMorphism`, `obstructionTowerVanishes_transport_of_morphism`, `BoundaryLiftCertificate`, `h1Vanishes_reflects_of_boundaryLift`, `h1Nonzero_transport_of_boundaryLift`, `no_globalRepairCoherent_transport_of_boundaryLift`, `DischargePrismTransport`, `boundaryLiftCertificate_of_dischargePrismTransport`, `dischargePrism_transport`, `layeredAdequacy_transport_of_dischargePrism`, `globalRepairCoherent_transport_of_dischargePrism`, `layeredRepairTowerFunctoriality_package`

## Target Theorem 寄与

- `target_theorem`: `Universal Semantic Repair Obstruction Tower Theorem`
- `target_support_node`: finite/small obstruction tower functoriality theorem
- `target_progress`: `support-node`
- `proof_obligation_delta`: finite target-boundary tower を cover-refinement / site-morphism / profile-law transport の対象にする。
- `target_completion_role`: checkpoint support; G6 が target-proved と判定するにはこの functoriality だけでは足りない。

## 証明・根拠の見込み

Lean では true sheaf functoriality や arbitrary site morphism は主張しない。finite tower の carrier map と commuting square を明示し、boundary reflection は別 certificate に切り出す。

Morphism に入れてよい field:

- `mapC0`, `mapC1`, `mapC2`
- `map_delta0`, `map_delta1`
- `map_residual`
- `finiteShadow_preserves_false`
- nonabelian / higher / stack token preservation in the forward direction

別 certificate として切る field:

- target boundary primitive の source lift
- coverage / faithfulness / semantic closure の transport for discharge prism
- `BoundaryLiftCertificate` は `H1Vanishes U -> H1Vanishes T` を field にせず、target boundary primitive の source primitive lift と source boundary proof だけを持つ。
- `DischargePrismTransport` は target coverage / target faithfulness / local semantic closure bridge と、それらを source prism から運ぶ witness だけを持つ。

入れてはいけない field:

- `GlobalSemanticRepairCoherent`
- `ObstructionTowerVanishes`
- `H1Vanishes`
- target equivalence
- finite-shadow reflection/completeness
- ArchMap correctness / runtime extraction completeness
- semantic closure reflection as a global statement
- `FiniteShadowTrivial -> H1Vanishes`

## 審判メモ

- 厳密性: G2 A は revise。`BoundaryLiftCertificate` が `H1` reflection を field として隠さず、target boundary primitive の source lift と source boundary proof だけを持つこと、`DischargePrismTransport` が coverage / faithfulness / local closure transport に限定されることを要求した。
- 厳密性対応: Lean 実装案では `FiniteObstructionTowerMorphism` に vanish / global coherence / target equivalence を入れず、`BoundaryLiftCertificate.lift_boundary` は target boundary primitive の source lift だけを返す。`DischargePrismTransport` は target coverage / faithfulness / local bridge と source prism からの transport witness だけを持つ。
- 厳密性再審判: G2 A 再審判は accept / base_score 90 / target_progress support-node。`map_c2Zero` は `CechZ1` transport 用の zero compatibility であり、結論相当 premise ではないと判定した。
- 研究価値: G2 B は accept / base_score 90 / support-node。単なる forward preservation だけなら減点だが、boundary lift reflection、nonzero transport、prism transport、tower/global surface transport まで証明するなら G-04 functoriality blocker を実質的に減らす。
- repo 全体価値: G2 C は accept / base_score 90 / support-node。Cycle 1/2 の finite tower と discharge prism を transport/refinement 系へ接続する自然な次手と判定。
- ライバル比較: G2 D は accept / base_score 88 / support-node。artifact mapping との差分は、保存される tower data と別 certificate を要する reflection claim を theorem surface に分解する点にある。

## 関連

- Cycle 1 candidate: `g-aat-quality-surface-04-finite-semantic-repair-obstruction-tower-package.md`
- Cycle 2 candidate: `g-aat-quality-surface-04-finite-layered-repair-certificate-discharge.md`
- G1 closer / unifier は functoriality を第一候補として推奨した。
- G1 obstruction / wildcard は reflection を分離しない functoriality claim の危険を指摘した。

## 進捗ログ

- 2026-06-24: Cycle 2 merge 後、残 blocker の functoriality に対応する候補として作成。
- 2026-06-24: G2 A revise を受け、`BoundaryLiftCertificate` と `DischargePrismTransport` の field 粒度を明記。
- 2026-06-24: Lean evidence として `SemanticRepairTowerFunctoriality.lean` を追加し、candidate を picked / proved-in-research に更新。
- 2026-06-24: `.tmp/g04_functoriality_axioms.lean` で reported declarations の `#print axioms` を確認し、全対象が `does not depend on any axioms` であることを確認。
