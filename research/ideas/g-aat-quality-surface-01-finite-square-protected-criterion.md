---
status: picked
goal: G-aat-quality-surface-01
candidate_type: unification
capability_category: profile-curvature / certificate-transport / ridge-fold / invariance
expected_base_score: 70
expected_evidence_multiplier: 2.0
expected_final_score: 140
evidence_stage: proved-in-research
origin: G-aat-quality-surface-01-cycle-12
tags: [profile-curvature, finite-square, reading, protected-invariant]
created: 2026-06-20
cycle: 12
lean: Formal/AG/Research/QualitySurface/FiniteSquareCriterion.lean
---

# Arbitrary finite square protected-invariant curvature criterion

## 主張

任意の有限 profile square endpoint pair に対して、二つの typed path composite が visible reading では同値だが、
chosen protected invariant では分岐するなら、その square はその protected invariant に関して reading-curved である。
逆に、visible reading が protected invariant に faithful な square では、その invariant の path holonomy
discrepancy は起きない。

さらに、この criterion が cycle 7 の `TraceCurvature` finite square を instance として読むことを Lean で示す。

## 候補種別

`unification`

## 依拠

- `research/GOALS.md` の `G-aat-quality-surface-01`。
- cycle 3 の `ProfileCurvature.lean`。
- cycle 7 の `TraceCurvature.lean`。
- cycle 8 の `ReadingAdequacy.lean`。
- cycle 10 の `ProfileGridHolonomy.lean`。
- cycle 11 の `ProfileTupleIntegration.lean`。

## 非自明性

既存の finite witness を増やすのではなく、profile curvature を
`visible reading agreement + protected invariant discrepancy` の criterion として切り出す。
ただし theorem 自体が定義展開にならないように、generic endpoint-pair / path-composite framework、
faithfulness obstruction、既存 trace-curvature witness への instance 化を同じ Lean file で示す。

## 数学的興味

Quality Surface 上の curvature は、単なる path の違いではなく、選んだ reading がどの protected invariant に
faithful でないかとして読める。この形にすると、support antichain、trace missing locus、repair frontier、
tuple protected data を同じ criterion で扱える。

## GOAL への前進

任意有限 square criterion frontier を進め、cycle 3/7/10 の witness を report / paper で使える判定形式へ整理する。

## SCORE 見込み

- `score_reason`: witness から criterion への移行で profile-curvature / certificate-transport / ridge-fold / invariance を統合するため。ただし G2 A/C は定義展開 risk を指摘したため、expected base は 70 に下げる。
- `dullness_risk`: `Curved := discrepancy` と定義して即証明するだけなら低 SCORE。typed path composite framework、faithful reading では discrepancy が起きない方向、cycle 7 trace-curvature witness が criterion を満たす instance theorem が必要。
- `proof_or_evidence_plan`: `Formal/AG/Research/QualitySurface/FiniteSquareCriterion.lean` に generic finite square endpoint pair、reading、protected invariant、faithfulness、curvature criterion を置く。cycle 7 の trace-curvature endpoint pair を instance として証明する。可能なら repair frontier instance も入れる。

## CS / SWE への帰結

visible endpoint surface が flat に見えても、protected invariant の path discrepancy があれば、quality surface は
その reading に関して curved と判断する必要がある。これは tooling の endpoint-only view を full certificate
geometry と誤読しないための有限判定基準になる。ただし source extraction completeness、global flatness、
実コード全体の品質判定は主張しない。

## 証明・根拠の見込み

Lean では、generic square を「同じ target profile に入る二つの typed path composite endpoint」として相対化した。
reading `R` と protected invariant equivalence `SameInvariant` を受け取り、
`R.Equivalent left right` と `¬ SameInvariant left right` から reading-level curvature を得る。
また `FaithfulToInvariant R SameInvariant` があればその discrepancy は不可能であることを示した。
最後に `TraceCurvature.lawThenCover TraceCurvature.seedAt` と
`TraceCurvature.coverThenLaw TraceCurvature.seedAt` を instance として入れ、
trace missing locus / repair frontier discrepancy が criterion を満たすことを証明した。

Lean declarations:

- `finiteSquare_curvature_of_visible_agreement_protected_discrepancy`
- `finiteSquare_no_holonomy_of_faithful_reading`
- `finiteSquare_not_faithful_of_curvature`
- `finiteSquare_curvature_of_square_visible_protected_discrepancy`
- `finiteSquare_no_holonomy_of_square_faithful_reading`
- `traceCurvature_endpointPairOfSquare`
- `traceCurvature_instantiates_traceMissingCriterion`
- `traceCurvature_instantiates_repairFrontierCriterion`
- `same_trace_surface_but_finiteSquareCriterion_curved`

visible_projection: scalar / verdict / support agreement.

protected_structure: trace missing locus, repair frontier, support antichain, tuple protected data.

exactness_or_minimality_claim: criterion is exact relative to the chosen reading and protected invariant.

nonfaithfulness_or_failure_mode: visible reading can be flat while protected invariant has path discrepancy.

previous_cycle_delta: cycle 11 の tuple endpoint witness から、再び finite profile square の criterion へ戻し、静的 tuple integration ではなく path curvature 判定を進める。

## 審判メモ

- 厳密性: G2 A は `revise`。現状の `Curved := visible agreement + protected discrepancy` は定義展開に近すぎるため、typed endpoint/path-composite framework、faithful no-holonomy theorem、trace missing / repair frontier instance が必須。
- 研究価値: G2 B は `accept`、base 75。surprise は中程度だが compression / leverage / paper section potential は高い。
- repo 全体価値: G2 C は `revise`、base 70。任意有限 square criterion frontier には合うが、wrapper 化を避けるため reusable finite-square API と cycle 7 instance が必要。
- G3 axiom / formalization audit: pass。9 declaration は axiom-free。形式化品質監査も、generic `FiniteSquare` と typed edge transport 追加後に pass。
- G4 SCORE audit: `confirm`。base 70、multiplier 2.0、penalty 0、final 140。generic finite-square/path-composite framework が wrapper risk を十分に下げたが、criterion-by-definition に近い面もあるため 70 を超えては評価しない。

## 証拠

- Lean file: `Formal/AG/Research/QualitySurface/FiniteSquareCriterion.lean`
- Evidence stage: `proved-in-research`
- Build target: `lake env lean Formal/AG/Research/QualitySurface/FiniteSquareCriterion.lean`
- Main theorem: `FiniteSquareCriterion.same_trace_surface_but_finiteSquareCriterion_curved`
- Axiom summary: `finiteSquare_curvature_of_visible_agreement_protected_discrepancy`、`finiteSquare_no_holonomy_of_faithful_reading`、`finiteSquare_not_faithful_of_curvature`、`finiteSquare_curvature_of_square_visible_protected_discrepancy`、`finiteSquare_no_holonomy_of_square_faithful_reading`、`traceCurvature_endpointPairOfSquare`、`traceCurvature_instantiates_traceMissingCriterion`、`traceCurvature_instantiates_repairFrontierCriterion`、`same_trace_surface_but_finiteSquareCriterion_curved` は `#print axioms` でいずれも axiom-free。
- Formalization summary: `SquareEdgeTransport`、`FiniteSquare`、`endpointPairOfSquare` が四頂点、四つの typed edge transport、seed、二つの path composite endpoint を generic square data として保持する。`traceCurvatureSquare` と `traceCurvature_endpointPairOfSquare` により cycle 7 witness は generic square framework の instance として読める。

## 関連

- `research/ideas/g-aat-quality-surface-01-profile-curvature-detector.md`
- `research/ideas/g-aat-quality-surface-01-trace-curvature-detector.md`
- `research/ideas/g-aat-quality-surface-01-profile-grid-holonomy.md`
- `research/ideas/g-aat-quality-surface-01-profile-tuple-integration.md`

## 進捗ログ

- 2026-06-20: Cycle 12 G1 候補として作成。
- 2026-06-20: G2 A/C の `revise` を受け、expected score を 70 x 2.0 = 140 に下げ、typed endpoint/path-composite framework、faithful no-holonomy theorem、cycle 7 trace-curvature instance を必要証拠として明確化。
- 2026-06-20: `Formal/AG/Research/QualitySurface/FiniteSquareCriterion.lean` で generic endpoint pair、selected reading / protected invariant、faithful no-holonomy theorem、cycle 7 trace missing / repair frontier instance を追加。
- 2026-06-20: G3 形式化監査の `revise` を受け、generic `FiniteSquare`、`SquareEdgeTransport`、`endpointPairOfSquare`、square-level curvature / no-holonomy theorem、cycle 7 trace square の generic square instance を追加。
- 2026-06-20: G3 再監査で axiom audit / formalization quality audit がいずれも pass。
- 2026-06-20: G4 SCORE 監査で base 70、evidence multiplier 2.0、final SCORE 140 に確定。
