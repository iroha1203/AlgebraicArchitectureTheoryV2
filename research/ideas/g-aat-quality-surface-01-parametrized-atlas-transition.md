---
status: picked
goal: G-aat-quality-surface-01
candidate_type: transition / closure
capability_category: certificate-transport / repair-potential / obstruction / traceability / invariance / quality-surface
expected_base_score: 70
expected_evidence_multiplier: 2.0
expected_final_score: 140
evidence_stage: proved-in-research
rival_advantage: ADL / conformance checker can list staged violations and fixes, but this theorem proves transition-level non-regression and loss-to-restoration crossing inside the parametrized atlas.
origin: G-aat-quality-surface-01-cycle50
tags: [quality-surface, atlas-transition, staged-correction, exact-locus, protected-support]
created: 2026-06-21
cycle: 50
lean: proved-in-research
---

# Parametrized atlas transition theorem

## 主張

Cycle 49 の parametrized loss-aware atlas に stage transition を入れる。concrete staged correction relation に沿って source-ref exactness、protected-support emptiness、exact restoration は upward-closed であり、exact cell から protected-support loss cell へは遷移しない。さらに `allBranches` より前の stage は、`allBranches` へ遷移すると protected-support loss から exact restoration へ移る。

## 候補種別

`transition / closure`

## 依拠

- `research/lean/ResearchLean/AG/QualitySurface/ParametrizedSelectedCorrectionSystem.lean`
- `research/lean/ResearchLean/AG/QualitySurface/ParametrizedLossAwareAtlas.lean`

## 非自明性

Cycle 49 は stage ごとの atlas cell classification を固定した。Cycle 50 はその分類を transition-level に上げ、StageLe に沿う upward-closed 性質と loss-to-restoration crossing を theorem として束ねる。単なる locus 表ではなく、stage transition が exactness を後退させないことを明示する。

## 数学的興味

Quality Surface の repair trajectory は、点ごとの分類表だけでなく、transition に沿った non-regression / restoration crossing として読める。exactness と protected-support emptiness が upward-closed であることは、repair frontier を順序付き certificate transport として扱うための局所モデルになる。

## GOAL への前進

この候補は `certificate-transport`、`repair-potential`、`obstruction`、`traceability`、`invariance`、`quality-surface` を前進させる。Cycle 49 の open question だった parametrized atlas transition のうち、concrete `StageAtlasTransition` relation を進める。

## ライバルに対する有効性

ADL / conformance checker は staged violations と fixes を列挙できるが、exactness / support-empty / restoration の transition-level upward closure や、pre-all stage から all-branches stage への protected-loss-to-restoration crossing を theorem として与えない。

## SCORE 見込み

- `score_reason`: parametrized atlas transition relation を進め、visible invariance、exact/support/restoration upward closure、no exact-to-loss regression、loss-to-restoration crossing witness を Lean で持つ。ただし Cycle 49 の locus theorem と concrete `StageLe` から自然に出る closure でもあるため、G2 判定に合わせて base70 とする。
- `dullness_risk`: Cycle 49 の locus theorem を言い換えるだけだと弱い。transition relation `StageAtlasTransition`、non-regression theorem、loss-to-restoration transition witness を追加して transition-level の内容にする。
- `proof_or_evidence_plan`: Lean file `ParametrizedAtlasTransition.lean` で proved-in-research。G2/G3/G4 監査後に report と Issue score を同期する。

## CS / SWE への帰結

repair stage view では、現在の cell classification だけでなく、stage transition が exactness を後退させないかを検査できる。ただしこれは tooling 実装 claim ではなく、concrete staged correction relation と finite parametrized atlas に相対化された theorem である。

## 証明・根拠

Lean file: `research/lean/ResearchLean/AG/QualitySurface/ParametrizedAtlasTransition.lean`

Proved declarations:

- `StageAtlasCell`
- `StageAtlasTransition`
- `stageAtlasCell_visibleInvariant`
- `stageTransition_sourceRefExact_upwardClosed`
- `stageTransition_supportEmpty_upwardClosed`
- `stageTransition_exactRestoration_upwardClosed`
- `stageTransition_no_exact_to_protectedSupportLoss`
- `StageLossToRestorationTransition`
- `stageTransition_to_allBranches_of_not_allBranches`
- `preAllStage_to_allBranches_lossToRestoration`
- `obligationOnly_to_allBranches_lossToRestoration`
- `uncorrected_to_allBranches_lossToRestoration`
- `parametrizedAtlasTransition_package`

Boundary:

- concrete staged selected correction relation、finite parametrized loss-aware atlas に相対化する。
- arbitrary atlas transition maps、baseline cell との transition、global repair planner、runtime patch synthesis、source extraction completeness、ArchMap correctness、whole-codebase quality は主張しない。

## 審判メモ

- 厳密性: A は accept/base80。B/D/C は content accept だが base70 同期を要求。採用する base は 70。
- 研究価値: Cycle 49 の staged locus theorem を concrete transition relation 上の upward closure / non-regression / loss-to-restoration crossing へ上げる。
- repo 全体価値: parametrized atlas の cell-wise classification に transition-level reading を追加する。
- ライバル比較: ADL / conformance checker との差分は、concrete `StageAtlasTransition` 上の non-regression と pre-all-to-allBranches crossing に限定する。

## Verification

- `focused Lean check: ResearchLean/AG/QualitySurface/ParametrizedAtlasTransition.lean`: pass
- `Research package build`: pass
- forbidden-token scan for `sorry` / `admit` / `axiom` / `unsafe` / broad autoImplicit setting: pass
- `.tmp/parametrized_atlas_transition_axioms.lean`: pass
  - axiom-free: `stageAtlasCell_visibleInvariant`
  - standard axioms only: transition upward-closure / crossing / package declarations depend only on `propext` / `Quot.sound`
- G3 independent audit: pass; blocking findings none

## 関連

- Cycle 48: `Parametrized selected correction system`
- Cycle 49: `Parametrized loss-aware atlas`

## 進捗ログ

- 2026-06-21: Cycle 50 候補として作成し、Lean 証明を追加。
