---
status: picked
goal: G-aat-quality-surface-01
candidate_type: closure / parametrization
capability_category: repair-potential / obstruction / certificate-transport / traceability / invariance / quality-surface
expected_base_score: 70
expected_evidence_multiplier: 2.0
expected_final_score: 140
evidence_stage: proved-in-research
rival_advantage: ADL / conformance checker can report route violations and possible fixes, but this theorem proves exactness monotonicity and upward-closed exact loci for parametrized selected correction systems.
origin: G-aat-quality-surface-01-cycle48
tags: [quality-surface, selected-correction, parametrized-system, monotonicity, exact-locus]
created: 2026-06-21
cycle: 48
lean: proved-in-research
---

# Parametrized selected correction system

## 主張

selected route correction を parameterized system として読み、correction order を「hit した selected atom が失われない」順序として定義する。この順序に沿って selected branch hitting と source-ref exactness は monotone であり、monotone correction system の exact locus は upward-closed になる。具体例として `uncorrected -> obligationOnly -> allBranches` の三段階 schedule を置き、exact locus が `allBranches` のみであることを証明する。

## 候補種別

`closure / parametrization`

## 依拠

- `research/lean/ResearchLean/QualitySurface/SelectedRouteDefectSupportHitting.lean`
- `research/lean/ResearchLean/QualitySurface/SelectedRouteCorrectionExactness.lean`
- `research/lean/ResearchLean/QualitySurface/SelectedRouteFamilyExactness.lean`

## 非自明性

Cycle 44 は単一 correction の exactness iff all branch hitting を証明し、Cycle 47 は correction family exactness を localized branch agreement へ上げた。Cycle 48 は correction を parameterized system として扱い、hit-set order による monotonicity と upward-closed exact locus を theorem として固定する。三段階 schedule により、partial repair が visible surface を保っても exact locus には入らないことを具体的に示す。

## 数学的興味

quality surface 上の repair trajectory は、単なる fix list ではなく、selected atom hit-set による順序付き family として扱える。exact locus が upward-closed であることは、repair-potential を order-theoretic certificate geometry として読むための核になる。

## GOAL への前進

この候補は `repair-potential`、`obstruction`、`certificate-transport`、`traceability`、`invariance`、`quality-surface` を前進させる。特に Next Frontier の `parametrized selected correction system` を直接埋める。

## ライバルに対する有効性

ADL / conformance checker は violation と fix candidate を列挙できるが、修正 parameter の順序上で exactness が upward-closed になることや、partial correction と all-hit correction の exact locus の分離を theorem として与えない。

## SCORE 見込み

- `score_reason`: Next Frontier の `parametrized selected correction system` を直接進め、generic correction order、system exactness criterion、monotone exact-locus theorem、concrete three-stage schedule witness を Lean で持つ。ただし Cycle 44 の exactness iff all-branch hitting から自然に出る構造でもあるため、G2 の厳しめ判定に合わせて base70 とする。
- `dullness_risk`: 単なる `∀ parameter` 包装なら弱い。`CorrectionLe`、`MonotoneCorrectionSystem`、`monotoneCorrectionSystem_exact_upwardClosed`、`stagedCorrection_exact_iff_allBranches` を追加して、order-theoretic structure と concrete exact locus を固定する。
- `proof_or_evidence_plan`: Lean file `ParametrizedSelectedCorrectionSystem.lean` で proved-in-research。G2/G3/G4 監査後に report と Issue score を同期する。

## CS / SWE への帰結

repair pipeline の stage や policy parameter を、選択された defect atom の hit-set order として読むと、exactness restoration は upward-closed な safe region になる。ただしこれは tooling 実装 claim ではなく、選ばれた route-defect atom vocabulary と correction semantics に相対化された theorem である。

## 証明・根拠

Lean file: `research/lean/ResearchLean/QualitySurface/ParametrizedSelectedCorrectionSystem.lean`

Proved declarations:

- `CorrectionLe`
- `CorrectionHitsAllBranches`
- `CorrectionSourceRefExact`
- `correctionLe_refl`
- `correctionLe_trans`
- `correctionSourceRefExact_iff_hitsAllBranches`
- `correctionHitsAllBranches_monotone`
- `correctionSourceRefExact_monotone`
- `CorrectionSystem`
- `SystemExactAt`
- `SystemHitsAllBranches`
- `SystemSourceRefExact`
- `systemSourceRefExact_iff_hitsAllBranches`
- `MonotoneCorrectionSystem`
- `monotoneCorrectionSystem_exact_upwardClosed`
- `RepairStage`
- `stagedCorrection`
- `stagedCorrectionSystem`
- `StageLe`
- `stagedCorrectionSystem_monotone`
- `stagedCorrection_uncorrected_not_exact`
- `stagedCorrection_obligationOnly_not_exact`
- `stagedCorrection_allBranches_exact`
- `stagedCorrection_exact_iff_allBranches`
- `stagedCorrectionSystem_not_sourceRefExact`
- `stagedCorrectionSystem_exactAt_iff_allBranches`
- `parametrizedSelectedCorrectionSystem_package`

Boundary:

- selected route-defect atom vocabulary、selected correction semantics、explicit source-ref packet bridge に相対化する。
- global repair planner、runtime patch synthesis、source extraction completeness、ArchMap correctness、whole-codebase quality は主張しない。

## 審判メモ

- 厳密性: A/C/D は accept/base80。B は accept/base70 とし、Cycle 44 から自然に出る構造なので G4/report は base70 に同期すべきと判定。採用する base は 70。
- 研究価値: selected correction を単発 repair から hit-set order 上の repair trajectory として読む構造を追加する。
- repo 全体価値: Cycle 44/47 の exactness theorem を monotone correction system と staged exact locus に接続する。
- ライバル比較: ADL / conformance checker との差分は global repair planning ではなく、hit-set order 上の exactness monotonicity と upward-closed exact locus に限定する。

## Verification

- `lake env lean research/lean/ResearchLean/QualitySurface/ParametrizedSelectedCorrectionSystem.lean`: pass
- `lake build ResearchLean`: pass
- forbidden-token scan for `sorry` / `admit` / `axiom` / `unsafe` / broad autoImplicit setting: pass
- `.tmp/parametrized_selected_correction_system_axioms.lean`: pass
  - axiom-free: `correctionLe_refl`, `correctionLe_trans`, `correctionSourceRefExact_iff_hitsAllBranches`, `correctionHitsAllBranches_monotone`, `correctionSourceRefExact_monotone`, `systemSourceRefExact_iff_hitsAllBranches`, `monotoneCorrectionSystem_exact_upwardClosed`
  - standard axioms only: concrete staged schedule witnesses and package depend only on `propext` / `Quot.sound`
- G3 independent audit: pass; blocking findings none

## 関連

- Cycle 43: `Selected route-defect support hitting`
- Cycle 44: `Selected route correction exactness theorem`
- Cycle 46: `Route-defect local repair calculus bridge`
- Cycle 47: `Selected route family exactness criterion`

## 進捗ログ

- 2026-06-21: Cycle 48 候補として作成し、Lean 証明を追加。
