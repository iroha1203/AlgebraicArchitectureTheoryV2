---
status: picked
goal: G-aat-quality-surface-01
candidate_type: orientation
capability_category: certificate-transport / quality-surface / traceability
expected_base_score: 55
expected_evidence_multiplier: 2.0
expected_final_score: 110
evidence_stage: proved-in-research
origin: cycle-39
tags: [quality-surface, repair-transport, visible-law, exact-visualization]
created: 2026-06-20
cycle: 39
lean: proved-in-research
---

# Visible-law deletion separates protected zero holonomy from source-ref exact visualization

## 主張

選ばれた finite source-ref repair/transport square において、support、missing locus、repair frontier、source-ref table、obligation、action naturality は flat で、route endpoint の packet holonomy defect は空であるにもかかわらず、transport が visible surface preservation law を落とすと、route endpoint は visible packet / tuple surface で分岐し、source-ref exact visualization は成立しない。

この主張は、supplied finite packet、declared storage repair action、explicit packet update、packet-to-tuple bridge に相対化される。canonical transport、canonical repair planning、source extraction completeness、ArchMap correctness、実コード全体の品質判定は結論しない。

## 候補種別

`orientation`

## 依拠

- `research/lean/ResearchLean/QualitySurface/LawfulRepairTransportCommutator.lean`
- `research/lean/ResearchLean/QualitySurface/SourceRefExactVisualization.lean`
- `research/lean/ResearchLean/QualitySurface/RouteDefectSupport.lean`
- Cycle 37: table-law deletion cell
- Cycle 38: route defect support calculus

## 非自明性

これまでの route counterexample は、visible surface が flat に見えても protected holonomy defect が残る方向を示していた。この候補は逆向きに、protected data は完全に zero holonomy でも visible law を削るだけで source-ref exact visualization が壊れることを示す。したがって source-ref exact visualization は protected zero holonomy だけでも、visible commutation だけでも足りず、二つの law が独立に必要である。

## 数学的興味

source-ref exact visualization の条件を「visible equivalence」と「protected zero holonomy」の直積的な要件として分解し、その片側を削った有限 witness を与える。Cycle 37/38 が protected defect support を局在させたのに対し、この候補は defect support が空でも exact visualization が失敗する visible-law cell を固定する。

## GOAL への前進

lawful repair/transport criterion minimality matrix の visible-law deletion cell を埋め、Quality Surface の loss-aware visualization において visible law と protected route support を別々の保証として表示すべき理由を増やす。

## SCORE 見込み

- `score_reason`: lawful criterion の必要性を一セル進め、protected-zero / visible-defect という未カバーの反対向き failure mode を Lean-proved finite witness として固定する。G2 三審判は accept し、base は 55 / 65 / 60 に分かれたため、保守的に base 55 を採用する。
- `dullness_risk`: `SourceRefExactVisualization` の定義展開だけに落ちる危険がある。packet update の非 visible law、non-visible transport laws、action naturality、zero packet holonomy、visible non-equivalence、not exact visualization を同じ selected route square で束ねる必要がある。
- `proof_or_evidence_plan`: 完了。source-ref table に応じて visible scalar だけを変える packet update `visibleLawSensitiveTransport` を定義した。partial packet は visible scalar 1 へ、storage repair 後の full packet は visible scalar 0 へ送る。protected fields はそのまま保存する。storage repair action との二 route endpoints は protected data で一致するが visible scalar が異なることを Lean で証明した。

## CS / SWE への帰結

repair/transport report で protected route support が空であることは、可視化上の exactness までは保証しない。表示や dashboard が visible scalar を別の transport law で再計算する場合、protected drill-down は flat でも route square は source-ref exact visualization ではない。

## 証明・根拠の見込み

Lean 証拠は `research/lean/ResearchLean/QualitySurface/VisibleLawDeletionProtectedZero.lean` に置いた。主要 declaration は次の通り。

- `visibleLawSensitiveTransport`
- `visibleLawRoute_nonVisibleTransportLaws`
- `visibleLawRoute_selfActionNaturality`
- `visibleLawRoute_not_preservesVisibleSurface`
- `visibleLawRoute_not_lawfulSquare`
- `visibleLawRoute_repairThenTransportPacket`
- `visibleLawRoute_transportThenRepairPacket`
- `visibleLawRoute_noPacketHolonomy`
- `visibleLawRoute_emptyDefectSupport`
- `visibleLawRoute_tupleZeroHolonomy`
- `visibleLawRoute_not_visiblePacketSurface`
- `visibleLawRoute_not_visibleTupleSurface`
- `visibleLawRoute_not_sourceRefExactVisualization`
- `visibleLawDeletionProtectedZero_package`

Verification:

- `lake env lean research/lean/ResearchLean/QualitySurface/VisibleLawDeletionProtectedZero.lean`: pass
- `lake build ResearchLean`: pass
- `.tmp/visible_law_deletion_axioms.lean`: all listed definitions and theorem declarations do not depend on any axioms
- G3 axiom audit: pass after clarifying that `research/lean/ResearchLean` is the allowed research sandbox; no non-research `Formal/AG` proper file was edited.
- G3 formalization-quality audit: pass. The audit confirmed that the statement matches the selected finite witness claim, is neither too weak nor too strong, keeps non-visible transport laws/action naturality/zero packet holonomy/empty support/visible failure in the same route square, and avoids global minimality or whole-codebase claims.

## 審判メモ

- 厳密性: accept。base 55。exactness failure 自体は既存 iff に近いため base 70 は高すぎるが、同じ selected square で non-visible laws、action naturality、zero holonomy、visible non-equivalence を束ねるなら採用可能。
- 研究価値: accept。base 65。protected zero holonomy と visible surface preservation の独立性を反対向き witness として埋める点を評価。
- repo 全体価値: accept。base 60。lawful criterion minimality matrix と loss-aware visualization の根拠として価値があるが、小セル補充に留まる危険を明記する必要あり。

## 関連

- `g-aat-quality-surface-01-route-defect-support-calculus.md`
- `g-aat-quality-surface-01-transport-table-law-route-localization.md`

## 進捗ログ

- 2026-06-20: Cycle 39 候補として作成。
- 2026-06-20: G2 三審判 accept。Lean 証拠を `VisibleLawDeletionProtectedZero.lean` に固定し、候補カードを picked / proved-in-research に同期。
