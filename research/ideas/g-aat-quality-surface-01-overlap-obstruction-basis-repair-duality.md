---
status: picked
goal: G-aat-quality-surface-01
candidate_type: computability / unification
capability_category: obstruction / computability / repair-potential / traceability / minimality / quality-surface / certificate-transport
expected_base_score: 86
expected_evidence_multiplier: 2.0
expected_final_score: 172
evidence_stage: proved-in-research
rival_advantage: ADL and conformance tools can list overlap mismatches, but they do not usually distinguish irredundant protected overlap branches from redundant failure displays, nor prove the declared repair support that must hit them.
origin: research-loop-cycle-66
tags: [quality-surface, handoff, cech, obstruction-basis, repair-transversal, minimality]
created: 2026-06-21
cycle: 66
lean: proved-in-research
---

# Finite overlap obstruction basis and repair-transversal duality

## 主張

For a finite Cech-style handoff cover, an overlap obstruction basis is a
component-indexed protected support predicate that is both sound and complete
for the cover's full overlap component support.  It is not merely a nonempty
certificate for the same global-failure boolean: hitting the basis must imply
hitting the whole overlap support.  In a component-complete declared repair
regime, clearing the overlap is equivalent to hitting every basis component.
A selected singleton basis is irredundant when dropping its listed component
destroys support generation on the same selected deletion cover.

The claim is relative to selected finite source-ref handoff atlases, supplied
finite chart and overlap data, bounded handoff laws, finite `BridgeComponent`
vocabulary, and declared component-level repair predicates.  It does not assert
canonical global minimality, runtime repair synthesis, source extraction
completeness, ArchMap correctness, arbitrary route enumeration, global sheaf
completeness, or whole-codebase quality.

## 候補種別

`computability` / `unification`

## 依拠

- `research/lean/ResearchLean/AG/QualitySurface/HandoffCechExactness.lean`
- `research/lean/ResearchLean/AG/QualitySurface/HandoffRepairTransversal.lean`
- `research/lean/ResearchLean/AG/QualitySurface/SourceRefHandoffComponentSupport.lean`
- Cycle 63-65 の component support、repair transversal、Cech overlap exactness。

## 非自明性

Cycle 65 gives nonempty overlap support and repair transversality for a fixed
cover.  This candidate asks which protected overlap components are an
irredundant basis for the overlap support and repair obligation, and proves
that component-complete declared repair clears the cover exactly when it hits
that basis.  It is not a raw failure list, a first-failure selector, or a
predicate that only preserves the same nonempty/global-failure boolean.

## 数学的興味

The result turns overlap obstruction into a finite hypergraph-like certificate:
irredundant support branches and declared repair transversals become dual
readings of the same protected local-to-global obstruction.

## GOAL への前進

It makes Cech overlap obstruction computable and repair-relevant.  A future
report or viewer can show not just that a hidden overlap obstruction exists,
but which protected branch is indispensable and which declared repair support
must hit it.

## ライバルに対する有効性

ADL / conformance surfaces can expose cross-view mismatches.  This candidate
adds an AAT-specific theorem package: irredundant protected basis elements,
proper-sub-basis residual failure, and a component-complete repair hitting
criterion.  That is stronger than mismatch count or view-local green/red status.

## SCORE 見込み

- `score_reason`: High computability/unification value.  The result combines
  Cycle 63 component support, Cycle 64 repair transversal, and Cycle 65 Cech
  overlap exactness into an irredundant overlap basis theorem.
- `dullness_risk`: Medium-high unless the Lean evidence includes strong
  support generation, soundness, irredundancy, and deletion/residual witness.
  A supplied support list renamed as `basis`, or a basis that only preserves
  nonempty/global-failure status, would be too weak.
- `proof_or_evidence_plan`: Define `OverlapObstructionBasis`, basis generation,
  basis soundness, irredundancy by failure of generation after deleting a
  listed component, and basis transversality.  Prove empty basis iff global
  exactness under local exactness, declared repair clearance iff hitting every
  basis component under component completeness, and singleton irredundant bases
  for the selected support / trace / repair-frontier deletion overlap covers.
  Add a visible one-component display nonfaithfulness witness.
- `G2_actual_score_band`: A accepted after revise at 82; B accepted at 88;
  C accepted at 86; D accepted at 86.  The synchronized expected base score is
  86 before G4 SCORE audit.

## CS / SWE への帰結

A drill-down surface can distinguish a redundant mismatch list from an
irredundant overlap obstruction basis.  Repair guidance can then target the
protected branch that actually controls global exactness, without claiming
runtime repair synthesis.

## 証明・根拠の見込み

Lean declarations:

- `OverlapBasisSound`
- `OverlapBasisGenerates`
- `OverlapObstructionBasis`
- `OverlapBasisIrredundant`
- `OverlapBasisTransversal`
- `HandoffCechBasisCompleteRepairPlan`
- `overlapBasis_iff_overlapSupport`
- `overlapBasis_empty_iff_globalExact_of_local`
- `overlapBasisTransversal_iff_fullOverlapTransversal`
- `declaredClearance_iff_hitsEveryOverlapBasis_of_componentComplete`
- `supportOverlapBasis`
- `traceOverlapBasis`
- `repairFrontierOverlapBasis`
- `supportOverlapBasis_drop_not_generates`
- `traceOverlapBasis_drop_not_generates`
- `repairFrontierOverlapBasis_drop_not_generates`
- `supportOverlapBasis_irredundant`
- `traceOverlapBasis_irredundant`
- `repairFrontierOverlapBasis_irredundant`
- `oneComponentOverlapBasisShape_not_faithful_to_overlapBasis`
- `overlapObstructionBasisRepairDuality_package`

Lean evidence stage: `proved-in-research` in
`research/lean/ResearchLean/AG/QualitySurface/OverlapObstructionBasis.lean`, imported by
`research/lean/ResearchLean.lean`.

G3 checks:

- `lake env lean research/lean/ResearchLean/AG/QualitySurface/OverlapObstructionBasis.lean`: pass.
- `lake build ResearchLean.AG.QualitySurface.OverlapObstructionBasis`: pass.
- `lake build ResearchLean`: pass.
- `lake build`: pass; existing unrelated linter warnings remain in
  `Formal/Arch/Extension/FeatureExtensionExamples.lean`.
- `lake env lean .tmp/overlap_obstruction_basis_axioms.lean`: pass.
- `rg -n "\\b(axiom|admit|sorry|unsafe)\\b"` on this candidate's changed Research
  files: no matches.

Axiom audit summary:

- Core basis/repair-duality declarations
  (`OverlapBasisSound`, `OverlapBasisGenerates`, `OverlapObstructionBasis`,
  `OverlapBasisIrredundant`, `OverlapBasisTransversal`,
  `HandoffCechBasisCompleteRepairPlan`, `overlapBasis_iff_overlapSupport`,
  `overlapBasisTransversal_iff_fullOverlapTransversal`,
  `declaredClearance_iff_hitsEveryOverlapBasis_of_componentComplete`) have no
  axioms.
- `propext` remains in empty-basis/global-exactness, singleton basis,
  drop-not-generates, irredundancy, and visible nonfaithfulness witnesses.
- `Quot.sound` remains in local/global exactness obstruction witnesses and the
  package theorem through existing local exactness machinery, not through the
  core basis-generation or component-complete repair argument.

Formalization quality audit summary: pass.  The Lean statements use
support-level soundness/completeness rather than preserving only the
nonempty/global-failure boolean; irredundancy is same-cover deletion failure;
repair clearance iff basis hitting is explicitly relative to component-complete
declared repair plans.

## 追加メタデータ

```text
planned_theorem_names:
  OverlapObstructionBasis
  overlapBasis_empty_iff_globalExact_of_local
  declaredClearance_iff_hitsEveryOverlapBasis_of_componentComplete
  supportOverlapBasis_irredundant
  traceOverlapBasis_irredundant
  repairFrontierOverlapBasis_irredundant
  oneComponentOverlapBasisShape_not_faithful_to_overlapBasis
  overlapObstructionBasisRepairDuality_package
visible_projection:
  visible one-component overlap-basis display that forgets protected component identity
protected_structure:
  irredundant overlap component basis, source-ref handoff component identity, declared repair support
exactness_or_minimality_claim:
  strong basis support equivalence controls global exactness under local exactness; component-complete declared repair clearance is equivalent to hitting every basis component; selected singleton bases are irredundant because dropping the listed component destroys support generation on the same selected cover
nonfaithfulness_or_failure_mode:
  visible one-component display does not recover protected overlap basis identity or the selected cover carrying the irredundant repair obligation
previous_cycle_delta:
  Cycle 65 fixed Cech overlap support and exactness; this cycle turns overlap support into an irredundant basis and repair-transversal duality theorem.
genius_potential:
  no
genius_target:
  none
genius_support_role:
  none
```

## 審判メモ

- 厳密性:
  - revise resolved: generation is strengthened to support-level soundness and completeness, not merely nonempty/global-failure equivalence; singleton irredundancy is restricted to selected deletion covers.
  - accept after revise, base 82, genius no. Required evidence was support-level generation, same-cover deletion/drop residual witness, component-complete repair iff basis hitting, empty basis iff global exactness under local exactness, and visible nonfaithfulness.
- 研究価値:
  - accept, base 88, genius no. The result compresses Cycle 63 component support, Cycle 64 repair transversal, and Cycle 65 Cech exactness into a basis/duality theorem package.
- repo 全体価値:
  - accept, base 86, genius no. Strong AAT/Lean/Research value; future ArchView/ArchSig drill-down value remains a bounded future surface.
- ライバル比較:
  - accept, base 86, genius no. The AAT delta is irredundant protected basis, deletion/residual witness, and exact repair hitting semantics beyond an ADL mismatch list.

## 関連

- `research/ideas/g-aat-quality-surface-01-finite-cech-handoff-obstruction-exactness.md`
- `research/ideas/g-aat-quality-surface-01-component-support-transversal-handoff-repairs.md`
- `research/reports/G-aat-quality-surface-01.md`

## 進捗ログ

- 2026-06-21: Cycle 66 G1 候補 pool から作成。
- 2026-06-21: G2 revise を受け、basis generation を support-level soundness/completeness へ強化。
- 2026-06-21: G3 Lean 証拠を `OverlapObstructionBasis.lean` として固定し、axiom / formalization quality audit を pass。
