---
status: picked
goal: G-aat-quality-surface-01
candidate_type: unification
capability_category: obstruction / repair-potential / certificate-transport / traceability / quality-surface / computability
expected_base_score: 70
expected_evidence_multiplier: 2.0
expected_final_score: 140
evidence_stage: proved-in-research
rival_advantage: ADL / conformance checker can detect individual route mismatches, but this atlas proves a finite diagnosis table where exactness, visible-law loss, protected-support loss, and all-hit restoration are separated by Lean-checked predicates.
origin: G-aat-quality-surface-01-cycle45
tags: [quality-surface, commutator-atlas, exact-visualization, repair-hitting, loss-aware]
created: 2026-06-21
cycle: 45
lean: proved-in-research
---

# Loss-aware commutator atlas adequacy

## 主張

selected repair/transport commutator witnesses を loss-aware atlas としてまとめると、各 atlas cell について source-ref exactness は visible tuple flatness と empty protected route support の同時成立に等しい。さらに atlas は visible-law loss、protected-support loss、all-hit exact restoration の三種の witness を持つ。

## 候補種別

`unification`

## 依拠

- `research/lean/ResearchLean/AG/QualitySurface/ExactVisualizationCriterionMinimality.lean`
- `research/lean/ResearchLean/AG/QualitySurface/VisibleLawDeletionProtectedZero.lean`
- `research/lean/ResearchLean/AG/QualitySurface/SelectedRouteDefectSupportHitting.lean`
- `research/lean/ResearchLean/AG/QualitySurface/SelectedRouteCorrectionExactness.lean`
- `research/lean/ResearchLean/AG/QualitySurface/RouteDefectSupport.lean`

## 非自明性

これまでの cycle は個別 route / correction の theorem だった。Cycle 45 はそれらを一つの finite atlas に入れ、visible flatness、protected support empty、source-ref exactness の三 reading predicate で診断する。単なる結果一覧ではなく、atlas 内では exactness iff visible-and-empty が全 cell に対して成り立ち、visible-law loss / protected-support loss / restored exactness の各 mode が witness される。

## 数学的興味

exact visualization failure は一枚岩ではない。visible law が壊れて protected support は空の cell、visible は flat だが protected support が残る cell、all-hit correction で exactness が回復する cell が同じ criterion 上に並ぶ。これは Quality Surface を loss-aware atlas として読むための最小 finite model になる。

## GOAL への前進

この候補は `obstruction`、`repair-potential`、`certificate-transport`、`traceability`、`quality-surface`、`computability` を前進させ、route-level theorem 群を診断可能な finite atlas に統一する。

## ライバルに対する有効性

ADL / conformance checker は route mismatch、component defect、CI gate を出せるが、visible loss と protected-support loss と exact restoration を同じ formal criterion の atlas cell として区別しない。この atlas は、どの reading が失敗し、どの correction が exactness を回復するかを finite theorem package として示す。

## SCORE 見込み

- `score_reason`: Cycle 38/39/42/43/44 を一つの loss-aware atlas に統合し、individual theorem から diagnostic table へ上げる unification。G2 では研究価値 / repo 全体価値 / rival 比較が base 85、厳密性が base 70 だったため、既存 theorem 群の package 化リスクを見て保守的に base 70、Lean proof が未完証明なしなら multiplier 2.0。
- `dullness_risk`: 既存 theorem の package 化に見える危険がある。`atlasCell_exact_iff_visible_empty` を全 cell に対する criterion とし、三種の loss/restoration mode を witness することで単なる列挙から分離する。
- `proof_or_evidence_plan`: `LossAwareAtlasCell`、`CellVisibleTupleFlat`、`CellProtectedRouteSupportEmpty`、`CellSourceRefExact`、`atlasCell_exact_iff_visible_empty`、`lossAwareAtlas_has_all_modes`、`lossAwareCommutatorAtlasAdequacy_package` を Lean で証明した。

## CS / SWE への帰結

loss-aware view は mismatch を一つの赤信号として表示するだけでなく、visible law failure、protected support failure、exact restoration を分けて説明できる。これは tooling 実装 claim ではなく、finite selected witness 上の atlas adequacy theorem である。

## 証明・根拠の見込み

Lean file: `research/lean/ResearchLean/AG/QualitySurface/LossAwareCommutatorAtlas.lean`

Planned / proved declarations:

- `LossAwareAtlasCell`
- `CellVisibleTupleFlat`
- `CellProtectedRouteSupportEmpty`
- `CellSourceRefExact`
- `atlasCell_exact_iff_visible_empty`
- `atlasCell_not_exact_of_not_visible`
- `atlasCell_not_exact_of_not_empty`
- `visibleLawDeletion_is_visibleLawLoss`
- `tableLawDeletion_is_protectedSupportLoss`
- `visibleRepairTransport_is_protectedSupportLoss`
- `allHitCorrection_is_exactRestoration`
- `obligationOnlyCorrection_is_protectedSupportLoss`
- `lossAwareAtlas_has_all_modes`
- `lossAwareCommutatorAtlasAdequacy_package`

Verification:

- `focused Lean check: ResearchLean/AG/QualitySurface/LossAwareCommutatorAtlas.lean`: pass
- `Research package build`: pass
- `#print axioms` for the reported theorem declarations: all reported theorem declarations have no 公理依存.
- Forbidden-token scan over the Cycle 45 Lean/card files: no matches.
- G3 公理監査: pass。reported declarations は clean で、`Formal/AG` 本体は参照のみ。
- G3 Lean 形式化品質監査: pass。finite selected atlas の theorem として、visible tuple flatness、protected route support、source-ref exactness の三 predicate と三 mode witness が候補主張に対応している。

Boundary:

- selected finite source-ref packet route / correction atlas 上の theorem であり、complete diagnostic coverage for all codebases、global repair planning、source extraction completeness、ArchMap correctness、whole-codebase quality は主張しない。
- atlas cell は supplied finite witnesses に相対化され、runtime tooling surface の実装済み claim ではない。

## 審判メモ

- 厳密性: accept / base 70。claim boundary は守られているが、中核の iff は既存 criterion の cell-wise case split なので base 90 は強すぎる。
- 研究価値: accept / base 85。既存 cycle 群を finite atlas の診断表へ圧縮し、paper の loss-aware commutator atlas 節として有効。
- repo 全体価値: accept / base 85。Research / Lean の成果として PR 価値があり、Tooling / Website には将来の loss-aware readout surface として接続可能。
- ライバル比較: accept / base 85。ADL / conformance checker の mismatch detection を越えて、visible loss / protected-support loss / exact restoration を atlas cell として区別する点を評価。
- G3 公理監査: pass。`atlasCell_exact_iff_visible_empty`、mode witness、package theorem まで clean。
- G3 形式化品質監査: pass。主張は selected finite source-ref packet route / correction atlas に限定され、tooling 実装や global diagnostic coverage へ越境していない。

## 関連

- Cycle 39: `Visible-law deletion protected-zero cell`
- Cycle 42: `Exact-visualization criterion and four-law selected minimality matrix`
- Cycle 43: `Selected route defect support hitting theorem`
- Cycle 44: `Selected route correction exactness theorem`

## 進捗ログ

- 2026-06-21: Cycle 45 候補として作成。Lean 単体チェックと `Research package build` は pass。
- 2026-06-21: G2 で base 70 / multiplier 2.0 に修正。G3 公理監査と Lean 形式化品質監査は pass。
