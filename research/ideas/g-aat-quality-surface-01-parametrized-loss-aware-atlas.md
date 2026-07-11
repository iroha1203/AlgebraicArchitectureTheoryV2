---
status: picked
goal: G-aat-quality-surface-01
candidate_type: closure / atlas-parametrization
capability_category: certificate-transport / obstruction / repair-potential / traceability / invariance / quality-surface
expected_base_score: 70
expected_evidence_multiplier: 2.0
expected_final_score: 140
evidence_stage: proved-in-research
rival_advantage: ADL / conformance checker can list violations and fixes, but this atlas proves that staged correction cells keep visible flatness while support-empty / exact / exact-restoration loci occur exactly at the all-branches stage.
origin: G-aat-quality-surface-01-cycle49
tags: [quality-surface, loss-aware-atlas, staged-correction, exact-locus, protected-support]
created: 2026-06-21
cycle: 49
lean: proved-in-research
---

# Parametrized loss-aware atlas

## 主張

Cycle 45 の loss-aware atlas と Cycle 48 の staged selected correction system を結合し、baseline loss cells と staged correction cells を同じ finite atlas に入れる。staged correction cells では visible tuple flatness は全 stage で保たれ、protected support empty、source-ref exactness、exact restoration は `allBranches` stage でのみ成立する。

## 候補種別

`closure / atlas-parametrization`

## 依拠

- `research/lean/ResearchLean/QualitySurface/LossAwareCommutatorAtlas.lean`
- `research/lean/ResearchLean/QualitySurface/ParametrizedSelectedCorrectionSystem.lean`

## 非自明性

Cycle 45 は static な loss-aware atlas、Cycle 48 は staged correction system を証明した。Cycle 49 は両者を合わせ、loss-aware atlas の cell type 自体を baseline / staged correction の和として拡張する。特に staged cell の exactness locus だけでなく、protected support empty locus と exact restoration locus も `allBranches` に一致することを固定する。

## 数学的興味

Quality Surface の atlas は、単一 snapshot の loss classification だけでなく、repair stage parameter に沿って exact locus がどこで開くかを読める。visible layer が一定でも protected support と exactness が stage によって分岐するため、loss-aware geometry と repair trajectory が同じ finite atlas 上で接続される。

## GOAL への前進

この候補は `certificate-transport`、`obstruction`、`repair-potential`、`traceability`、`invariance`、`quality-surface` を前進させる。Next Frontier の `parametrized loss-aware commutator atlas` を直接進める。

## ライバルに対する有効性

ADL / conformance checker は violation と fix candidate を列挙できるが、visible flatness が一定の staged correction cells で protected support empty / source-ref exact / exact restoration の locus が一致することを theorem として与えない。

## SCORE 見込み

- `score_reason`: Next Frontier の `parametrized loss-aware atlas` を直接進め、baseline loss cells と staged correction cells の finite atlas、exactness criterion、stage exact/support/restoration locus、mode witnesses を Lean で持つ。ただし Cycle 45 と Cycle 48 の合成色も強いため、G2 の厳しめ判定に合わせて base70 とする。
- `dullness_risk`: Cycle 45 と Cycle 48 の単純な合成だけだと弱い。`ParametrizedLossAwareCell` を新しい atlas cell type として定義し、staged cells の support-empty / exact / exact-restoration loci がすべて `allBranches` に一致する theorem を追加して差分を作る。
- `proof_or_evidence_plan`: Lean file `ParametrizedLossAwareAtlas.lean` で proved-in-research。G2/G3/G4 監査後に report と Issue score を同期する。

## CS / SWE への帰結

repair stage UI や diagnostic table は、visible pass/fail だけではなく、protected support と exact restoration locus を同じ atlas 上で示せる。ただしこれは tooling 実装 claim ではなく、selected staged correction semantics と baseline loss-aware cells に相対化された theorem である。

## 証明・根拠

Lean file: `research/lean/ResearchLean/QualitySurface/ParametrizedLossAwareAtlas.lean`

Proved declarations:

- `ParametrizedLossAwareCell`
- `ParamCellVisibleTupleFlat`
- `ParamCellProtectedRouteSupportEmpty`
- `ParamCellSourceRefExact`
- `paramCell_exact_iff_visible_empty`
- `stagedCell_visibleTupleFlat`
- `stagedCell_supportEmpty_iff_allBranches`
- `stagedCell_sourceRefExact_iff_allBranches`
- `ParamVisibleLawLossCell`
- `ParamProtectedSupportLossCell`
- `ParamExactRestorationCell`
- `baseline_visibleLawDeletion_is_visibleLawLoss`
- `baseline_tableLawDeletion_is_protectedSupportLoss`
- `stagedCell_protectedSupportLoss_of_not_allBranches`
- `stagedCell_allBranches_is_exactRestoration`
- `stagedCell_exactRestoration_iff_allBranches`
- `parametrizedLossAwareAtlas_has_all_modes`
- `parametrizedLossAwareAtlas_package`

Boundary:

- selected route-defect atom vocabulary、staged selected correction semantics、baseline loss-aware cells、explicit source-ref packet bridge に相対化する。
- global repair planner、runtime patch synthesis、source extraction completeness、ArchMap correctness、whole-codebase quality は主張しない。

## 審判メモ

- 厳密性: A/C/D は accept/base80。B は accept/base70 とし、Cycle 45/48 の合成に近いので G4/report は base70 に下げるべきと判定。採用する base は 70。
- 研究価値: baseline loss cells と staged correction cells を一つの finite atlas type に入れ、staged support-empty / exact / restoration locus を `allBranches` に一致させる。
- repo 全体価値: Cycle 45 の atlas と Cycle 48 の staged correction system を、parametrized atlas の theorem package に接続する。
- ライバル比較: ADL / conformance checker との差分は、visible flatness が一定でも protected support / exact restoration locus を theorem 化する点に限定する。

## Verification

- `lake env lean research/lean/ResearchLean/QualitySurface/ParametrizedLossAwareAtlas.lean`: pass
- `lake build ResearchLean`: pass
- forbidden-token scan for `sorry` / `admit` / `axiom` / `unsafe` / broad autoImplicit setting: pass
- `.tmp/parametrized_loss_aware_atlas_axioms.lean`: pass
  - axiom-free: `paramCell_exact_iff_visible_empty`, `stagedCell_visibleTupleFlat`, `baseline_visibleLawDeletion_is_visibleLawLoss`, `baseline_tableLawDeletion_is_protectedSupportLoss`
  - standard axioms only: staged locus/mode/package declarations depend only on `propext` / `Quot.sound`
- G3 independent audit: pass; blocking findings none

## 関連

- Cycle 45: `Loss-aware commutator atlas adequacy`
- Cycle 48: `Parametrized selected correction system`

## 進捗ログ

- 2026-06-21: Cycle 49 候補として作成し、Lean 証明を追加。
