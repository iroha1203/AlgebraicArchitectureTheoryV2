---
status: picked
goal: G-aat-quality-surface-01
candidate_type: family-exact-locus / closure
capability_category: repair-potential / obstruction / certificate-transport / traceability / invariance / quality-surface
expected_base_score: 70
expected_evidence_multiplier: 2.0
expected_final_score: 140
evidence_stage: proved-in-research
rival_advantage: ADL / conformance checker can show per-route fixed status, but this theorem proves the exact locus and failing-slot obstruction for arbitrary staged route-slot families.
origin: G-aat-quality-surface-01-cycle53
tags: [quality-surface, route-family, exact-locus, failing-slot, staged-correction]
created: 2026-06-21
cycle: 53
lean: proved-in-research
---

# Finite route-family exact locus

## 主張

任意の route slot family `Slot -> RepairStage` について、family source-ref exactness はすべての slot が `allBranches` stage にあることと同値である。pointwise stage order に沿って family exactness は upward-closed であり、任意の failing slot は family exactness を阻む。Cycle 52 の mixed pair はこの arbitrary family theorem の concrete instance になる。

## 候補種別

`family-exact-locus / closure`

## 依拠

- `research/lean/ResearchLean/AG/QualitySurface/MultiRouteCorrectionSystem.lean`
- `research/lean/ResearchLean/AG/QualitySurface/SelectedRouteFamilyExactness.lean`

## 非自明性

Cycle 52 は two-slot finite witness だった。Cycle 53 は route slot type を任意にし、exact locus、pointwise upward closure、failing-slot obstruction を一括して証明する。これにより non-singleton の finite witness から arbitrary staged route-slot family の theorem へ進む。

## 数学的興味

family exactness は slot ごとの exactness を単に眺めるのではなく、全 slot の stage assignment が `allBranches` fiber に入る exact locus として読める。failing slot theorem は、family exactness failure を局所化するための次の minimality theorem の土台になる。

## GOAL への前進

この候補は `repair-potential`、`obstruction`、`certificate-transport`、`traceability`、`invariance`、`quality-surface` を前進させる。Cycle 52 の open question だった arbitrary finite non-singleton family exact locus を直接進める。

## ライバルに対する有効性

ADL / conformance checker は route ごとの fixed status を表示できるが、arbitrary staged route-slot family の exact locus と failing-slot obstruction theorem は与えない。

## SCORE 見込み

- `score_reason`: arbitrary route-slot assignment、exact locus iff all slots all-branches、pointwise upward closure、failing-slot obstruction、mixed assignment instance を Lean で持つ。ただし既存 staged correction exactness と `FamilySourceRefExact` の pointwise 性から自然に出る面も強いため、G2 の厳しめ判定に合わせて base70 とする。
- `dullness_risk`: Cycle 52 の two-slot theorem の単純拡張に見える危険がある。任意 `Slot`、pointwise order、failing-slot obstruction theorem を加え、次の minimal failing slot theorem への接続を作る。
- `proof_or_evidence_plan`: Lean file `FiniteRouteFamilyExactLocus.lean` で proved-in-research。G2/G3/G4 監査後に report と Issue score を同期する。

## CS / SWE への帰結

route family repair status は、per-route green check の一覧ではなく、全 slot が required correction stage に入ったかを判定する exact locus になる。任意の failing slot は family exactness failure の witness になる。

## 証明・根拠

Lean file: `research/lean/ResearchLean/AG/QualitySurface/FiniteRouteFamilyExactLocus.lean`

Proved declarations:

- `StageAssignment`
- `assignmentFamilyLeft`
- `assignmentFamilyRight`
- `AssignmentFamilySourceRefExact`
- `AssignmentAllBranches`
- `assignmentFamilySourceRefExact_iff_allBranches`
- `AssignmentLe`
- `assignmentFamilySourceRefExact_upwardClosed`
- `failingSlot_obstructs_assignmentFamilyExact`
- `mixedRouteSlotAssignment`
- `mixedRouteSlotAssignment_primary_sourceRefExact`
- `mixedRouteSlotAssignment_secondary_fails`
- `mixedRouteSlotAssignment_not_familyExact`
- `finiteRouteFamilyExactLocus_package`

Boundary:

- supplied route slots、staged selected correction semantics、explicit source-ref packet bridge に相対化する。Lean statement は `Slot : Type u` 全般であり、finite family を含むが finite enumeration / computable scan は主張しない。
- arbitrary repair planner、runtime patch synthesis、source extraction completeness、ArchMap correctness、whole-codebase quality は主張しない。

## 審判メモ

- 厳密性: A/B/C は accept/base80。D は content accept だが score 同期 revise/base70。採用する base は 70。
- 研究価値: Cycle 52 の two-slot witness を `Slot -> RepairStage` の general family exact locus へ上げる。
- repo 全体価値: failing slot が family exactness failure の witness になる theorem を追加する。
- ライバル比較: ADL / conformance checker との差分は per-route fixed status ではなく family exact locus と failing-slot obstruction theorem に限定する。

## Verification

- `cd research/lean && lake env lean ResearchLean/AG/QualitySurface/FiniteRouteFamilyExactLocus.lean`: pass
- `cd research/lean && lake build ResearchLean`: pass
- forbidden-token scan for `sorry` / `admit` / `axiom` / `unsafe` / broad autoImplicit setting: pass
- `.tmp/finite_route_family_exact_locus_axioms.lean`: pass
  - axiom-free: `mixedRouteSlotAssignment_secondary_fails`
  - standard axioms only: exact-locus / upward-closure / failing-slot declarations and package depend only on `propext` / `Quot.sound`
- G3 independent audit: pass; blocking findings none

## 関連

- Cycle 52: `Multi-route correction system`

## 進捗ログ

- 2026-06-21: Cycle 53 候補として作成し、Lean 証明を追加。
