---
status: picked
goal: G-aat-quality-surface-01
candidate_type: localization / closure
capability_category: obstruction / certificate-transport / repair-potential / traceability / invariance / quality-surface
expected_base_score: 70
expected_evidence_multiplier: 2.0
expected_final_score: 140
evidence_stage: proved-in-research
rival_advantage: ADL / conformance checker can report component mismatches, but this theorem packages selected support-defect localization as a generic certificate with branch-level exactness and obstruction criteria.
origin: G-aat-quality-surface-01-cycle51
tags: [quality-surface, support-defect, localization, branch-obstruction, exactness]
created: 2026-06-21
cycle: 51
lean: proved-in-research
---

# Selected support-defect localization

## 主張

selected branch localization が protected route defects を cover するなら、empty protected support は全 localized branch agreement に同値であり、source-ref exactness は visible tuple flatness と localized branch agreement に同値になる。さらに localized branch defect は source-ref exactness を阻む。generic theorem を visible route と corrected selected route の concrete localization に instantiation する。

## 候補種別

`localization / closure`

## 依拠

- `research/lean/ResearchLean/AG/QualitySurface/SelectedRouteFamilyExactness.lean`
- `research/lean/ResearchLean/AG/QualitySurface/ParametrizedAtlasTransition.lean`

## 非自明性

Cycle 47 は family-level localization cover を持った。Cycle 51 は route-level localization certificate を `RouteSupportLocalization` として切り出し、empty support criterion、exactness criterion、branch-level obstruction theorem を generic に固定する。さらに visible route と corrected route の concrete localization を与えるため、単なる Cycle 47 の `∀ index` 再掲ではない。

## 数学的興味

support defect は「どの protected component が壊れたか」ではなく、「どの localized selected branch が exactness を阻むか」として読むことができる。localized branch defect が exactness obstruction になる定理により、branch-level obstruction geometry が route-level exactness criterion に接続される。

## GOAL への前進

この候補は `obstruction`、`certificate-transport`、`repair-potential`、`traceability`、`invariance`、`quality-surface` を前進させる。Next Frontier の `generic selected support-defect localization` を直接埋める。

## ライバルに対する有効性

ADL / conformance checker は component mismatch を列挙できるが、その mismatch を selected branch localization certificate として束ね、branch defect が exactness obstruction になることを theorem として与えない。

## SCORE 見込み

- `score_reason`: generic `RouteSupportLocalization`、empty support iff localized branch agreement、source-ref exact iff visible plus localized branch agreement、branch-defect obstruction theorem、visible/corrected route instances を持つ。ただし中核 criterion は Cycle 47 の family localization と近いため、G2 の厳しめ判定に合わせて base70 とする。
- `dullness_risk`: Cycle 47 の family theorem の再掲に留まる危険がある。route-level certificate structure、branch-level obstruction theorem、visible route instance、corrected route instance を含めて回避する。
- `proof_or_evidence_plan`: Lean file `SelectedSupportDefectLocalization.lean` で proved-in-research。G2/G3/G4 監査後に report と Issue score を同期する。

## CS / SWE への帰結

diagnostic report の component mismatch は、selected branch localization certificate として読める。branch-level defect は exactness obstruction として扱えるため、repair planning ではなく obstruction explanation surface の theorem になる。

## 証明・根拠

Lean file: `research/lean/ResearchLean/AG/QualitySurface/SelectedSupportDefectLocalization.lean`

Proved declarations:

- `RouteSupportLocalization`
- `RouteLocalizationBranchesAgree`
- `LocalizedBranchDefect`
- `routeSupportEmpty_iff_localizedBranches`
- `sourceRefExact_iff_visible_localizedBranches`
- `localizedBranchDefect_obstructs_sourceRefExact`
- `visibleRouteSupportLocalization`
- `visibleRoute_exact_iff_visible_localizedBranches`
- `visibleRoute_obligation_localizedDefect`
- `visibleRoute_obligationDefect_obstructs_sourceRefExact`
- `correctedRouteSupportLocalization`
- `correctedRoute_exact_iff_visible_localizedBranches`
- `allRouteDefectCorrection_localizedBranchesAgree`
- `obligationOnlyCorrection_storageRepair_localizedDefect`
- `obligationOnlyCorrection_localizedDefect_obstructs_sourceRefExact`
- `selectedSupportDefectLocalization_package`

Boundary:

- supplied source-ref packets、selected protected components、explicit source-ref packet bridge に相対化する。
- source extraction completeness、ArchMap correctness、global repair planning、runtime patch synthesis、whole-codebase quality は主張しない。

## 審判メモ

- 厳密性: A/C/D は accept/base80。B は accept/base70 とし、Cycle 47 の family localization と近いため G4/report は base70 に同期すべきと判定。採用する base は 70。
- 研究価値: Cycle 47 を置き換えるのではなく、route-level localization certificate と branch-level obstruction theorem として切り出す。
- repo 全体価値: visible route / corrected route の concrete localization instances を追加し、component mismatch を selected branch obstruction として読めるようにする。
- ライバル比較: ADL / conformance checker との差分は、component mismatch list を selected branch localization certificate と exactness obstruction theorem に持ち上げる点に限定する。

## Verification

- `focused Lean check: ResearchLean/AG/QualitySurface/SelectedSupportDefectLocalization.lean`: pass
- `Research package build`: pass
- forbidden-token scan for `sorry` / `admit` / `axiom` / `unsafe` / broad autoImplicit setting: pass
- `.tmp/selected_support_defect_localization_axioms.lean`: pass
  - axiom-free: `localizedBranchDefect_obstructs_sourceRefExact`, `visibleRoute_obligation_localizedDefect`, `visibleRoute_obligationDefect_obstructs_sourceRefExact`, `allRouteDefectCorrection_localizedBranchesAgree`, `obligationOnlyCorrection_storageRepair_localizedDefect`, `obligationOnlyCorrection_localizedDefect_obstructs_sourceRefExact`
  - standard axioms only: generic cover criterion and package declarations depend only on `propext`, `Classical.choice`, `Quot.sound`
- G3 independent audit: pass; blocking findings none

## 関連

- Cycle 47: `Selected route family exactness criterion`
- Cycle 50: `Parametrized atlas transition theorem`

## 進捗ログ

- 2026-06-21: Cycle 51 候補として作成し、Lean 証明を追加。
