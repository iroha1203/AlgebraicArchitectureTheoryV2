---
status: picked
goal: G-aat-quality-surface-01
candidate_type: multi-route / closure
capability_category: repair-potential / obstruction / certificate-transport / traceability / invariance / quality-surface
expected_base_score: 70
expected_evidence_multiplier: 2.0
expected_final_score: 140
evidence_stage: proved-in-research
rival_advantage: ADL / conformance checker can mark individual routes as fixed, but this theorem proves that family exactness for a non-singleton staged correction system requires every route slot to reach all-branches.
origin: G-aat-quality-surface-01-cycle52
tags: [quality-surface, multi-route, correction-system, exact-locus, family-exactness]
created: 2026-06-21
cycle: 52
lean: proved-in-research
---

# Multi-route correction system

## 主張

二つの selected route slot を持つ staged correction family を定義する。この non-singleton family は、両 slot が `allBranches` stage にあるとき、かつそのときに限って family source-ref exact である。componentwise stage order に沿って family exactness は upward-closed であり、片方の route が exact でも mixed family 全体は exact ではない。

## 候補種別

`multi-route / closure`

## 依拠

- `research/lean/ResearchLean/AG/QualitySurface/SelectedRouteFamilyExactness.lean`
- `research/lean/ResearchLean/AG/QualitySurface/ParametrizedSelectedCorrectionSystem.lean`
- `research/lean/ResearchLean/AG/QualitySurface/SelectedSupportDefectLocalization.lean`

## 非自明性

Cycle 48 は単一 staged correction system、Cycle 51 は route-level localization を扱った。Cycle 52 は route slot を二つに増やし、family exactness が各 slot の exactness の合成であるだけでなく、全 slot が all-hit stage に到達する必要があることを finite non-singleton witness として示す。mixed pair は「一つの route が exact」という局所成功が family exactness には足りないことを固定する。

## 数学的興味

quality surface の repair trajectory は、単一 route の exactness ではなく selected route family 全体の exactness locus として読む必要がある。componentwise stage order で exactness が upward-closed になることは、multi-route repair frontier を certificate geometry として扱う最小モデルになる。

## GOAL への前進

この候補は `repair-potential`、`obstruction`、`certificate-transport`、`traceability`、`invariance`、`quality-surface` を前進させる。Next Frontier の `multi-route non-singleton correction systems` を直接進める。

## ライバルに対する有効性

ADL / conformance checker は route ごとの violation / fixed 状態を表示できるが、non-singleton family exactness がすべての route slot の all-hit stage を要求する theorem としては与えない。

## SCORE 見込み

- `score_reason`: non-singleton route family、family exactness iff both slots all-branches、componentwise upward closure、mixed pair counterexample を Lean で持つ。ただし同じ staged correction route schema を二つの slot に置いた finite witness で、任意 finite non-singleton theorem までは出ていないため、G2 判定に合わせて base70 とする。
- `dullness_risk`: 単に `∀ slot` の包装だと弱い。`StagePairLe`、`pairFamilySourceRefExact_upwardClosed`、`mixedPair_primary_sourceRefExact`、`mixedPair_not_familySourceRefExact` を含め、局所 exact と family exact の分離を入れる。
- `proof_or_evidence_plan`: Lean file `MultiRouteCorrectionSystem.lean` で proved-in-research。G2/G3/G4 監査後に report と Issue score を同期する。

## CS / SWE への帰結

multi-route repair dashboard では、一つの route が exact でも family exact とは限らない。全 selected route slot が required correction stage に到達したときだけ family exactness が成立する、という certificate-level gate になる。

## 証明・根拠

Lean file: `research/lean/ResearchLean/AG/QualitySurface/MultiRouteCorrectionSystem.lean`

Proved declarations:

- `RouteSlot`
- `StagePair`
- `StagePair.stage`
- `pairFamilyLeft`
- `pairFamilyRight`
- `PairFamilySourceRefExact`
- `PairAllBranches`
- `pairFamilySourceRefExact_iff_allBranches`
- `StagePairLe`
- `stageLe_allBranches_right`
- `pairFamilySourceRefExact_upwardClosed`
- `allBranchesPair`
- `mixedPair`
- `allBranchesPair_sourceRefExact`
- `mixedPair_primary_sourceRefExact`
- `mixedPair_secondary_protectedSupportLoss`
- `mixedPair_not_familySourceRefExact`
- `multiRouteCorrectionSystem_package`

Boundary:

- selected two-slot route family、staged selected correction semantics、explicit source-ref packet bridge に相対化する。
- 異種 route 間の相互作用、arbitrary multi-route planners、runtime patch synthesis、source extraction completeness、ArchMap correctness、whole-codebase quality は主張しない。

## 審判メモ

- 厳密性: A/C は accept/base80。B は accept/base70、D は score 同期 revise/base70。採用する base は 70。
- 研究価値: 同じ staged correction route schema を二つの slot に置いた non-singleton family exactness witness として扱う。
- repo 全体価値: single-route exactness と family exactnessを分離し、mixed pair により局所 exact では family exact にならないことを固定する。
- ライバル比較: ADL / conformance checker との差分は per-route fixed 表示ではなく certificate-level family exactness gate を theorem 化する点に限定する。

## Verification

- `lake env lean research/lean/ResearchLean/AG/QualitySurface/MultiRouteCorrectionSystem.lean`: pass
- `lake build ResearchLean`: pass
- forbidden-token scan for `sorry` / `admit` / `axiom` / `unsafe` / broad autoImplicit setting: pass
- `.tmp/multi_route_correction_system_axioms.lean`: pass
  - standard axioms only: package and supporting declarations depend only on `propext` / `Quot.sound`
- G3 independent audit: pass; blocking findings none

## 関連

- Cycle 48: `Parametrized selected correction system`
- Cycle 51: `Selected support-defect localization`

## 進捗ログ

- 2026-06-21: Cycle 52 候補として作成し、Lean 証明を追加。
