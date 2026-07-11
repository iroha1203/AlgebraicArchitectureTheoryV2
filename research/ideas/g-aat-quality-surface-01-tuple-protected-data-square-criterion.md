---
status: picked
goal: G-aat-quality-surface-01
candidate_type: unification
capability_category: quality-surface/profile-curvature/certificate-transport/traceability/repair-potential
expected_base_score: 40
expected_evidence_multiplier: 2.0
expected_final_score: 80
evidence_stage: proved-in-research
origin: G-aat-quality-surface-01-cycle18
tags:
  - finite-square
  - profile-tuple
  - protected-data
created: 2026-06-20
cycle: 18
lean: proved
---

# Tuple protected-data finite-square criterion instance

## 主張

Cycle 11 の profile-typed certificate tuple witness は、Cycle 12 の generic
`FiniteSquareCriterion` における selected finite square instance として読める。
visible reading を tuple surface `(sigma, nu, selectedSupport)` に限定し、protected invariant
を tuple protected data `(omega, repairFrontier, traceField)` に取ると、二つの endpoint は
visible には flat だが protected data では curved である。

主張は finite supplied endpoint pair、explicit selected square、underlying
`ProfileGridHolonomy` path transport と互換な tuple edge transport、selected reading、
selected protected invariant に相対化する。canonical global tuple transport、任意 profile
grid の flatness、source extraction completeness、ArchMap correctness、実コード全体の
traceability、全 repair semantics は結論しない。

## 候補種別

`unification`

## 依拠

- `research/lean/ResearchLean/AG/QualitySurface/ProfileTupleIntegration.lean`
- `research/lean/ResearchLean/AG/QualitySurface/FiniteSquareCriterion.lean`
- `endpointTuple_visibleAgreement`
- `endpointTuple_protectedData_diff`
- `same_surface_but_profile_tuple_diff`
- `finiteSquare_curvature_of_visible_agreement_protected_discrepancy`

## 非自明性

Cycle 11 は endpoint tuple の visible surface と protected tuple data の分離を固定した。
Cycle 12 は selected finite-square reading criterion を与え、Cycle 15 は support / repair
invariant をそこへ載せた。この候補は central tuple
`Cert_A(p) = (sigma_p, omega_p, S_p, R_p, nu_p, T_p)` 自体を protected invariant として
criterion に載せる。

単なる既存定理の名前替えにしないため、明示的な finite square、underlying grid certificate
transport と互換な typed tuple edge transport、endpoint-pair agreement、visible-flatness、
`omega` / `repairFrontier` / `traceField` の各 protected discrepancy、generic criterion
instance、visible faithfulness no-go を一つの theorem package として固定する。

## 数学的興味

Quality Surface の中心 tuple のうち、display されやすい visible surface と、repair / trace /
obligation を担う protected data の差を、finite-square reading curvature として読む。これにより
profile tuple integration と finite-square criterion の間に、trace-specific でも support-antichain
specific でもない tuple-level bridge ができる。

## GOAL への前進

quality-surface / profile-curvature / certificate-transport / traceability / repair-potential を
central certificate tuple の protected-data curvature として統合する。

## SCORE 見込み

- `score_reason`: G2-B/C は accept base 45。ただし G2-A が immediate corollary risk と arbitrary square risk を指摘したため、revised candidate は base 40 / final 80 に下げる。
- `dullness_risk`: medium-high。既存 endpoint witness を criterion で包むだけなら dull。underlying grid transport と互換な explicit typed square、endpoint agreement、tuple protected-data reading、component-wise discrepancy、nonfaithfulness theorem package まで必要。
- `proof_or_evidence_plan`: `TupleProtectedDataSquareCriterion.lean` に selected tuple square、underlying `ProfileGridHolonomy` transport compatibility、endpoint-pair agreement、tuple visible/protected reading、`omega` / `repairFrontier` / `traceField` discrepancy、finite-square criterion instance、visible faithfulness no-go、theorem package を置いた。

## CS / SWE への帰結

tuple surface が同じに見える quality display でも、obligation、repair frontier、trace field が異なる
場合、同じ UI / report row として扱うと repair-relevant data を失う。この結論は supplied finite
tuple witness に相対化され、tooling completeness や global code quality は主張しない。

## 証明・根拠の見込み

Lean proof は `research/lean/ResearchLean/AG/QualitySurface/TupleProtectedDataSquareCriterion.lean` に閉じる。

主要 theorem / declaration:

- `TupleProtectedEndpoint`
- `tupleLawFirstTransport`
- `tupleLawFirstEndpointTransport`
- `tupleCoverFirstTransport`
- `tupleCoverFirstEndpointTransport`
- `tupleProtectedDataSquare`
- `tupleProtectedDataEndpointPair`
- `tupleProtectedData_endpointPairOfSquare`
- `tupleProtectedData_square_gridCompatible`
- `SameTupleVisibleSurfaceReading`
- `SameTupleProtectedDataInvariant`
- `tupleProtectedDataSquareReading`
- `tupleProtectedData_visibleFlat`
- `tupleProtectedData_square_visibleFlat`
- `tupleProtectedData_omega_discrepancy`
- `tupleProtectedData_repairFrontier_discrepancy`
- `tupleProtectedData_traceField_discrepancy`
- `tupleProtectedData_discrepancy`
- `tupleProtectedData_square_discrepancy`
- `tupleProtectedData_instantiates_finiteSquareCriterion`
- `tupleProtectedData_no_visibleFaithfulness`
- `same_tuple_surface_but_protectedDataSquare_curved`

検証:

- `lake env lean research/lean/ResearchLean/AG/QualitySurface/TupleProtectedDataSquareCriterion.lean` pass。
- `lake build ResearchLean` pass。
- `lake env lean .tmp/tuple_protected_data_square_axioms.lean` pass。
- reported declaration はすべて `does not depend on any axioms`。
- changed-file scan で hidden / bidirectional Unicode と local path は no matches。

## 審判メモ

- 厳密性: G2-A は revise、base 40。arbitrary / constant square では弱すぎるため、underlying `ProfileGridHolonomy` path transport compatibility、endpointPairOfSquare agreement、component-wise protected discrepancy、visible faithfulness no-go を要求。
- 研究価値: G2-B は accept、base 45。ただし新しい witness ではなく既存 Cycle 11/12 の統合なので base 55 は高すぎる。
- repo 全体価値: G2-C は accept、base 45。Lean / paper surface には有効だが、grid-level flatness や lossy tuple transport obstruction より射程が狭いため過大評価しない。

## 関連

- `research/ideas/g-aat-quality-surface-01-profile-tuple-integration.md`
- `research/ideas/g-aat-quality-surface-01-finite-square-protected-criterion.md`
- `research/ideas/g-aat-quality-surface-01-support-antichain-square-criterion.md`
- `research/reports/G-aat-quality-surface-01.md`

## G2 revise log

- G2-A: 初回 revise、base 40。arbitrary / constant square では弱すぎるため、underlying `ProfileGridHolonomy` path transport compatibility、endpointPairOfSquare agreement、component-wise protected discrepancy、visible faithfulness no-go を要求。カード修正後 accept、base 40。
- G2-B: accept、base 45。ただし新しい witness ではなく既存 Cycle 11 / 12 の統合なので base 55 は高すぎる。
- G2-C: accept、base 45。Lean / paper surface には有効だが、grid-level flatness や lossy tuple transport obstruction より射程が狭いため過大評価しない。

## G3 監査

- `TupleProtectedDataSquareCriterion.lean` は selected tuple square、underlying grid transport compatibility、endpointPairOfSquare agreement、visible flatness、component-wise protected discrepancy、ReadingCurved instance、visible faithfulness no-go を証明する。
- G3 axiom audit: pass。target Lean、`ResearchLean`、axiom harness は pass。reported declaration はすべて axiom-free。
- G3 formalization quality audit: pass。statement は revised candidate の強さと一致し、global tuple transport、global flatness、ArchMap correctness、source completeness は encoding していない。

## 進捗ログ

- 2026-06-20: Cycle 18 candidate card 作成。
- 2026-06-20: G2-A revise を反映し、base 40 / final 80 に下げ、underlying grid transport compatibility と component-wise discrepancy を required evidence に追加。
- 2026-06-20: `TupleProtectedDataSquareCriterion.lean` added and verified locally.
