---
status: picked
goal: G-aat-quality-surface-01
candidate_type: closure
capability_category: profile-curvature/atom-supported-quality-geometry/repair-potential/invariance
expected_base_score: 40
expected_evidence_multiplier: 2.0
expected_final_score: 80
evidence_stage: proved-in-research
origin: G-aat-quality-surface-01-cycle15
tags:
  - finite-square
  - support-antichain
  - repair-hitting
created: 2026-06-20
cycle: 15
lean: proved
---

# Support antichain finite-square curvature instance

## 主張

Cycle 3 の profile-curvature square は、Cycle 12 の generic
`FiniteSquareCriterion` の support-antichain / repair-hitting instance として読める。
visible reading を scalar / verdict に限定し、protected invariant を selected support
family と repair hitting requirement に取ると、visible には flat でも protected data は
curved である。

主張は finite supplied square、selected reading、selected invariant に相対化する。新しい
finite square witness、generic finite-square criterion、global flatness、global no-holonomy、
source extraction completeness、ArchMap correctness、全 repair semantics は主張しない。

## 候補種別

`closure`

## 依拠

- `research/lean/ResearchLean/QualitySurface/ProfileCurvature.lean`
- `research/lean/ResearchLean/QualitySurface/FiniteSquareCriterion.lean`
- `supportFamily_path_ne`
- `repairHittingNumber_path_ne`
- `finiteSquare_curvature_of_visible_agreement_protected_discrepancy`

## 非自明性

Cycle 3 は concrete witness、Cycle 12 は generic criterion と trace instances を与えた。
この候補は support family / repair hitting requirement を protected invariant として
criterion に載せ、trace 以外の atom-supported repair geometry も generic criterion の
正規 instance であることを固定する。

## 数学的興味

Quality Surface の scalar/verdict view が support antichain と repair potential を隠すことを、
finite square curvature の selected invariant として読む。新現象ではなく、criterion 節を
support-repair frontier へ閉じる整理である。

## GOAL への前進

profile-curvature / atom-supported-quality-geometry / repair-potential を generic finite-square
criterion と接続する。

## SCORE 見込み

- `score_reason`: G2-A/B は base 45 cap、G2-C は base 40 妥当と判定。Cycle 3/12 の bridge instance なので base 40 / final 80 とする。
- `dullness_risk`: medium-high。既存 witness と existing criterion の instance 化であり、新しい witness ではない。
- `proof_or_evidence_plan`: `SupportAntichainSquareCriterion.lean` に `profileCurvatureSquare`、visible/protected reading、nonempty antichain evidence、support/repair discrepancy、generic criterion instance、旧 `CurvatureCell` への bridge theorem を置く。

## CS / SWE への帰結

Quality Surface の finite-square view で、scalar/verdict だけでは support family と repair hitting
requirement を復元できないことを、trace-missing とは別の repair-potential invariant として表示できる。

## 証明・根拠の見込み

Lean proof は `research/lean/ResearchLean/QualitySurface/SupportAntichainSquareCriterion.lean` に閉じる。

主要 theorem:

- `profileCurvatureSquare`
- `profileCurvature_endpointPairOfSquare`
- `supportRepairSquareReading`
- `profileCurvature_supportRepair_visibleFlat`
- `lawFirst_supportFamily_nonempty_antichain`
- `coverFirst_supportFamily_nonempty_antichain`
- `profileCurvature_supportFamily_discrepancy`
- `profileCurvature_repairHitting_discrepancy`
- `profileCurvature_instantiates_supportAntichainCriterion`
- `profileCurvature_no_visibleFaithfulness_for_supportRepair`
- `profileCurvature_readingCurved_implies_curvatureCell`
- `same_scalar_verdict_but_supportAntichainSquare_curved`

## 審判メモ

- 厳密性: `lake env lean` と axiom harness は pass。reported theorem は axiom-free。
- 研究価値: closure / instance。G2-C に従い base 40 とする。
- repo 全体価値: `research/lean/ResearchLean` と `research/` に閉じる。保護された数学本文、tooling schema、`Formal/AG` 本体は編集しない。

## 関連

- `research/ideas/g-aat-quality-surface-01-profile-curvature-detector.md`
- `research/ideas/g-aat-quality-surface-01-finite-square-protected-criterion.md`
- `research/reports/G-aat-quality-surface-01.md`

## G2 revise log

- G2-A: accept, base 45。visible scalar/verdict と protected support/repair を明示すれば許容。
- G2-B: revise-to-accept, cap 45。旧 `CurvatureCell` との bridge があれば base 50 まで許容だが、過大評価は避ける。
- G2-C: accept, base 40 妥当。Cycle 3/12 の connection closure なので 50+ は高すぎる。

## 進捗ログ

- 2026-06-20: Cycle 15 candidate picked.
- 2026-06-20: `SupportAntichainSquareCriterion.lean` added.
- 2026-06-20: `lake env lean research/lean/ResearchLean/QualitySurface/SupportAntichainSquareCriterion.lean` pass.
- 2026-06-20: `lake build ResearchLean` pass.
- 2026-06-20: `lake env lean .tmp/support_antichain_square_axioms.lean` pass; reported theorem package is axiom-free.
