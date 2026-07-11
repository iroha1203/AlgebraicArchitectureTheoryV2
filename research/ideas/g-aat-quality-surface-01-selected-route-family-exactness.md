---
status: picked
goal: G-aat-quality-surface-01
candidate_type: closure / unification
capability_category: certificate-transport / obstruction / repair-potential / traceability / quality-surface
expected_base_score: 80
expected_evidence_multiplier: 2.0
expected_final_score: 160
evidence_stage: proved-in-research
rival_advantage: ADL / conformance checker can list route mismatches, but this criterion proves that source-ref exactness of a selected route family is equivalent to visible flatness plus empty protected support, and under a localization cover to agreement on all selected branches.
origin: G-aat-quality-surface-01-cycle47
tags: [quality-surface, selected-route-family, exact-visualization, localization-cover, support]
created: 2026-06-21
cycle: 47
lean: proved-in-research
---

# Selected route family exactness criterion

## 主張

選ばれた source-ref route family 全体について、family source-ref exactness は各 route の visible tuple flatness と empty protected route support の同時成立に等しい。さらに、selected branch localization が protected route support を cover するなら、empty protected support は全 localized branch agreement に同値であり、family exactness は visible flatness と localized branch agreement に同値になる。

## 候補種別

`closure / unification`

## 依拠

- `research/lean/ResearchLean/AG/QualitySurface/ExactVisualizationCriterionMinimality.lean`
- `research/lean/ResearchLean/AG/QualitySurface/LossAwareCommutatorAtlas.lean`
- `research/lean/ResearchLean/AG/QualitySurface/RouteDefectSupport.lean`
- `research/lean/ResearchLean/AG/QualitySurface/SelectedRouteCorrectionExactness.lean`

## 非自明性

Cycle 44 は単一 corrected route の exactness criterion、Cycle 45 は具体的な finite atlas table だった。Cycle 47 は route index と selected branch localization cover を分離し、family-level exactness を visible / protected / localized branch agreement の三層で読む criterion に上げる。単なる `∀ route` ではなく、localized branch cover がある場合に protected support empty を selected branch agreement に変換する点が差分である。

## 数学的興味

route atlas や commutator diagram の exactness は、個別 route の pass/fail ではなく family-level vanishing theorem として読める。localized branch cover は、抽象的な protected support empty を、検査可能な selected branch agreement へ変換する。

## GOAL への前進

この候補は `certificate-transport`、`obstruction`、`repair-potential`、`traceability`、`quality-surface` を前進させ、selected route family の exactness と localized support defect reading を結ぶ。

## ライバルに対する有効性

ADL / conformance checker は route mismatch や view inconsistency を列挙できるが、route family exactness を visible flatness と selected branch localization cover による branch agreement criterion として証明しない。この criterion は、route mismatch list を family-level certificate geometry と support-local reading へ持ち上げる。

## SCORE 見込み

- `score_reason`: Next Frontier の `arbitrary selected route family exactness criterion` を直接進める。generic family criterion と localization-cover theorem、Cycle 45 の loss-aware atlas instantiation に加え、concrete selected correction singleton family の localization cover witness と exact / non-exact witnesses を持つ。
- `dullness_risk`: pointwise theorem だけだと Cycle 42 criterion の `∀ index` 包装になる危険がある。localized branch cover theorem、loss-aware atlas instantiation、concrete correction-family localization cover、full atlas non-exact / all-hit singleton exact / obligation-only non-exact の witness を含めて回避する。
- `proof_or_evidence_plan`: `FamilySourceRefExact`、`FamilyVisibleTupleFlat`、`FamilyProtectedRouteSupportEmpty`、`FamilySupportLocalized`、`FamilyLocalizedBranchesAgree` を定義し、family-level exactness と localized branch agreement criterion を Lean で証明した。さらに `CorrectedRouteFamilyIndex`、`correctedRouteFamily_supportLocalized`、`correctedRouteFamily_exact_iff_visible_localizedBranches`、exact / non-exact concrete correction family witness を追加した。

## CS / SWE への帰結

route mismatch list を、family exactness criterion と localized branch agreement の表へ変換できる。これは tooling 実装 claim ではなく、selected finite source-ref route family と localization cover に相対化された theorem である。

## 証明・根拠の見込み

Lean file: `research/lean/ResearchLean/AG/QualitySurface/SelectedRouteFamilyExactness.lean`

Proved declarations:

- `FamilyVisibleTupleFlat`
- `FamilyProtectedRouteSupportEmpty`
- `FamilySourceRefExact`
- `familySourceRefExact_iff_visible_empty`
- `FamilyLocalizedBranchesAgree`
- `FamilySupportLocalized`
- `familyProtectedSupportEmpty_iff_localizedBranches`
- `familySourceRefExact_iff_visible_localizedBranches`
- `lossAwareAtlas_familyCriterion`
- `lossAwareAtlas_not_familySourceRefExact`
- `exactRestorationSubfamily_sourceRefExact`
- `CorrectedRouteFamilyIndex`
- `correctedRouteFamilyLeft`
- `correctedRouteFamilyRight`
- `correctedRouteFamilyBranchComponent`
- `correctedRouteFamily_supportLocalized`
- `correctedRouteFamily_exact_iff_visible_localizedBranches`
- `allRouteDefectCorrection_familySourceRefExact`
- `obligationOnlyCorrection_family_not_sourceRefExact`
- `selectedRouteFamilyExactness_package`

Boundary:

- supplied finite source-ref route family、selected branch localization cover、explicit packet-to-tuple bridge に相対化する。
- complete diagnostic coverage for all codebases、ArchMap correctness、source extraction completeness、global repair planning、whole-codebase quality は主張しない。

## 審判メモ

- 厳密性: A は初回 revise、concrete selected correction singleton family と localization cover witness 追加後に accept/base80。B/C/D は base80 accept。
- 研究価値: selected route family exactness を visible flatness / protected support / localized branch agreement の criterion として固定する。
- repo 全体価値: Cycle 42/44/45/46 の exact visualization、selected correction、loss-aware atlas、local repair calculus bridge を family-level theorem へ接続する。
- ライバル比較: ADL / conformance checker は route mismatch list を出せるが、family-level exactness と selected branch localization cover の同値 theorem は出さない。

## Verification

- `lake env lean research/lean/ResearchLean/AG/QualitySurface/SelectedRouteFamilyExactness.lean`: pass
- `lake build ResearchLean`: pass
- forbidden-token scan for `sorry` / `admit` / `axiom` / `unsafe` / broad autoImplicit setting: pass
- `.tmp/selected_route_family_exactness_axioms.lean`: pass
  - axiom-free: `familySourceRefExact_iff_visible_empty`, `lossAwareAtlas_familyCriterion`, `lossAwareAtlas_not_familySourceRefExact`, `exactRestorationSubfamily_sourceRefExact`, `correctedRouteFamily_supportLocalized`, `allRouteDefectCorrection_familySourceRefExact`, `obligationOnlyCorrection_family_not_sourceRefExact`
  - standard axioms only: `familyProtectedSupportEmpty_iff_localizedBranches`, `familySourceRefExact_iff_visible_localizedBranches`, `correctedRouteFamily_exact_iff_visible_localizedBranches`, `selectedRouteFamilyExactness_package` depend only on `propext`, `Classical.choice`, `Quot.sound`
- G3 independent audit: pass; blocking findings none

## 関連

- Cycle 42: `Exact-visualization criterion and four-law selected minimality matrix`
- Cycle 44: `Selected route correction exactness theorem`
- Cycle 45: `Loss-aware commutator atlas adequacy`
- Cycle 46: `Route-defect local repair calculus bridge`

## 進捗ログ

- 2026-06-21: Cycle 47 候補として作成。
- 2026-06-21: Lean 証明を追加し、初回 G2 指摘に対応して concrete selected correction singleton family の localization cover witness を追加。
