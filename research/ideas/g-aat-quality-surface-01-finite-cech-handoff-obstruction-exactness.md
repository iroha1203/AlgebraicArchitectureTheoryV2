---
status: picked
goal: G-aat-quality-surface-01
candidate_type: bridge
capability_category: obstruction / certificate-transport / traceability / quality-surface / computability / invariance / repair-potential
expected_base_score: 84
expected_evidence_multiplier: 2.0
expected_final_score: 168
evidence_stage: proved-in-research
rival_advantage: ADL can compare local views and constraints, but it does not usually provide a local-chart exactness plus overlap cocycle obstruction theorem with source-ref repair support.
origin: research-loop-cycle-65
tags: [quality-surface, handoff, cech, obstruction, exactness, repair-transversal]
created: 2026-06-21
cycle: 65
lean: proved-in-research
---

# Finite Cech-style handoff obstruction exactness package

## 主張

A finite handoff cover is not just another name for one handoff atlas: it
bundles a finite family of chart atlases together with a separate overlap
cocycle atlas.  Global handoff interaction exactness is defined as local chart
interaction exactness plus vanishing of the overlap cocycle support.  The main
claim is the non-circular exactness criterion that this global predicate is
equivalent to local chart exactness together with empty protected overlap
obstruction support, plus a finite witness where every chart is interaction
exact but the overlap cocycle obstructs global exactness.  Under
component-complete declared repair, global repair clearance is equivalent to
hitting the overlap component support.

The claim is relative to selected finite source-ref handoff atlases, supplied
finite chart and overlap data, bounded handoff laws, finite `BridgeComponent`
vocabulary, and declared component-level repair predicates.  It does not assert
source extraction completeness, ArchMap correctness, runtime repair synthesis,
arbitrary route enumeration, global sheaf completeness, or whole-codebase
quality.

## 候補種別

`bridge`

## 依拠

- `research/lean/ResearchLean/QualitySurface/SourceRefHandoffHolonomyCorrespondence.lean`
- `research/lean/ResearchLean/QualitySurface/SourceRefHandoffObstructionLocus.lean`
- `research/lean/ResearchLean/QualitySurface/SourceRefHandoffComponentSupport.lean`
- `research/lean/ResearchLean/QualitySurface/HandoffRepairTransversal.lean`
- Cycle 60-64 の handoff atlas、obstruction locus、component support、repair transversal 系列。

## 非自明性

This is not another ordered scan or first-failure display.  It lifts the
source-ref handoff obstruction locus to finite local/global exactness data:
local charts may be green while overlap cocycle support still obstructs global
handoff interaction exactness.  The protected overlap support then controls
both exactness and declared repair obligations.

## 数学的興味

The candidate gives a finite Cech-style reading of handoff obstruction.  The
new object is the separation between chart atlases and an overlap cocycle
atlas.  It connects local exactness, overlap cocycle support, obstruction locus
emptiness, and repair transversality in one theorem package without moving
outside the bounded source-ref handoff regime.

## GOAL への前進

It strengthens the Quality Surface as a certificate geometry rather than a
dashboard: a local chart surface can look exact, while the protected overlap
cocycle contains the actual obstruction and repair necessity.

## ライバルに対する有効性

ADL and conformance tools can compare declared views and list view-level
mismatches.  This candidate adds a theorem-level local-to-global boundary:
which hidden overlap support prevents global exactness, and which protected
components a declared repair must hit.  That is a stronger repair/obstruction
object than local conformance status or raw violation count.

## SCORE 見込み

- `score_reason`: High bridge value.  The result compresses handoff holonomy,
  local/global exactness, traceability, computability, and repair support into a
  finite certificate package aligned with the GOAL's certificate diagram and
  paper-seed phase boundary.  G2 revised the expected base score from 92 to 88
  because the value depends on proving that the cover/overlap object is not a
  shallow rename of existing atlas iff theorems.  After G2-A and G2-C both
  returned base 82 and G2-B/G2-D returned base 88, the synchronized expected
  base is set to 84 pending G4 audit.
- `dullness_risk`: Medium-high unless the Lean evidence includes the explicit
  chart/overlap separation.  It would be dull if it only renamed an atlas as a
  cover or defined overlap support as the global obstruction complement.  The
  proof must include local-chart green / global-overlap failure, exact iff,
  protected obstruction support, and repair-transversal extraction.
- `proof_or_evidence_plan`: Define a finite `HandoffCechCover` with chart
  atlases and a separate overlap cocycle atlas.  Define local exactness as
  interaction exactness on every chart and define overlap support directly from
  the overlap cocycle atlas, not as the complement of global exactness.  Define
  global exactness as local exactness plus overlap holonomy vanishing.  Prove
  the exact iff against empty overlap component support, nonempty support iff
  global exactness failure under local exactness, and component-complete repair
  clearance iff the declared repair hits the overlap component support.  Add a
  finite witness where all local charts are exact but the overlap cocycle
  obstructs global exactness.

## CS / SWE への帰結

A system can pass local view checks while failing at hidden overlap handoff
interfaces.  The theorem identifies the protected overlap component support
that must be exposed in a drill-down or repair workflow; a green local dashboard
is not a faithful global certificate unless the overlap cocycle support is
empty.

## 証明・根拠の見込み

Planned Lean declarations:

- `HandoffCechCover`
- `HandoffCechLocalExact`
- `HandoffCechGlobalExact`
- `HandoffCechOverlapSupport`
- `HandoffCechOverlapSupportEmpty`
- `HandoffCechRepairObligation`
- `handoffCech_globalExact_iff_localExact_and_overlapSupportEmpty`
- `handoffCech_overlapSupport_nonempty_iff_notGlobalExact_of_local`
- `handoffCech_repairObligation_iff_overlapRepairTransversal_of_componentComplete`
- `locallyExact_not_faithful_without_overlapCocycle`
- `handoffCechExactness_package`

Actual Lean evidence stage: `proved-in-research`.

Implemented in:

- `research/lean/ResearchLean/QualitySurface/HandoffCechExactness.lean`
- aggregate import: `research/lean/ResearchLean.lean`

Implemented Lean declarations:

- `HandoffCechCover`
- `HandoffCechLocalExact`
- `HandoffCechOverlapHolonomyVanishes`
- `HandoffCechGlobalExact`
- `HandoffCechOverlapSupport`
- `HandoffCechOverlapSupportNonempty`
- `HandoffCechOverlapSupportEmpty`
- `handoffCech_overlapSupportEmpty_iff_holonomyVanishes`
- `handoffComponentSupport_nonempty_iff_not_holonomyVanishes`
- `handoffCech_globalExact_iff_localExact_and_overlapSupportEmpty`
- `handoffCech_overlapSupport_nonempty_iff_notGlobalExact_of_local`
- `HandoffCechRepairObligation`
- `HandoffCechOverlapRepairTransversal`
- `handoffCech_repairObligation_iff_overlapRepairTransversal_of_componentComplete`
- `locallyExactOverlapObstructedCover`
- `locallyExactOverlapObstructedCover_localExact`
- `locallyExactOverlapObstructedCover_overlapSupportNonempty`
- `locallyExactOverlapObstructedCover_notGlobalExact`
- `locallyExact_not_faithful_without_overlapCocycle`
- `handoffCechExactness_package`

Build evidence:

- `lake env lean research/lean/ResearchLean/QualitySurface/HandoffCechExactness.lean`: pass
- `lake env lean research/lean/ResearchLean.lean`: pass
- `lake build ResearchLean`: pass
- target scan for `axiom|admit|sorry|unsafe`: no matches
- `#print axioms`: core definitions, overlap support definitions, repair
  obligation definitions, repair equivalence, and `locallyExactOverlapObstructedCover`
  are `Quot.sound`-free; iff/support exactness declarations use standard
  `propext`; nonempty local-green witness declarations and the package use
  standard `propext` plus `Quot.sound` inherited from the existing
  `alignedSourceRefHandoffAtlas_interactionExact` proof.  No `sorryAx`, custom
  axiom, `Classical.choice`, or `unsafe`.
- `git diff --check`: pass

Witness boundary:

- `locallyExactOverlapObstructedCover` uses a nonempty chart list containing
  `alignedSourceRefHandoffAtlas`, a nonempty exact source-ref handoff chart,
  together with a distinct support-law deletion overlap cocycle.  Thus the
  local chart surface is genuinely green while the separate overlap cocycle
  obstructs global exactness.  This stronger nonempty chart witness imports the
  standard `Quot.sound` dependency from the existing aligned chart exactness
  proof; G3 accepted this with disclosure, and G4 must audit whether the
  evidence still deserves `x2.0`.

G2 revise requirements:

- `HandoffCechCover` must contain chart atlases and a distinct overlap cocycle
  atlas; it must not be a shallow alias of `SourceRefHandoffAtlas`.
- `HandoffCechOverlapSupport` must be defined from the overlap cocycle atlas,
  not from `Not HandoffCechGlobalExact`.
- The finite witness must prove that each chart is interaction exact while the
  overlap cocycle support is nonempty and global exactness fails.
- The repair statement must be component-complete and declared-predicate based,
  not an automatic runtime repair claim.

## 追加メタデータ

```text
planned_theorem_names:
  HandoffCechCover
  handoffCech_globalExact_iff_localExact_and_overlapSupportEmpty
  handoffCech_overlapSupport_nonempty_iff_notGlobalExact_of_local
  handoffCech_repairObligation_iff_overlapRepairTransversal_of_componentComplete
  locallyExact_not_faithful_without_overlapCocycle
  handoffCechExactness_package
visible_projection:
  all local charts green / pairwise visible conformance / no local chart failure
protected_structure:
  overlap-indexed source-ref handoff obstruction support and component repair transversal
exactness_or_minimality_claim:
  global exactness iff local exactness plus empty protected overlap support; under component completeness, declared overlap repair clearance iff repair support hits overlap support
nonfaithfulness_or_failure_mode:
  locally exact chart surfaces are not faithful to global handoff exactness when the overlap cocycle support is hidden
previous_cycle_delta:
  Cycle 60-64 built loop-level handoff holonomy, order-independent locus, component support, and repair transversals; this cycle lifts them to a finite local-to-global exactness package.
genius_potential:
  no
genius_target:
  none
genius_support_role:
  none
```

## 審判メモ

- 厳密性: initial revise, base 68.  Required explicit chart/overlap separation,
  overlap support not defined as complement of global exactness, finite
  local-green/global-failing witness, and component-complete declared repair
  iff.  After one revision, accepted with base 82 and `genius_eligibility: no`.
- 研究価値: accept, base 88, `genius_eligibility: no`.  Strong compression of
  local chart exactness, hidden overlap obstruction, and repair necessity into
  a finite local-to-global obstruction geometry.
- repo 全体価値: accept, base 82, `genius_eligibility: no`.  Useful for Lean,
  Research, paper/website surface, and tooling drill-down rationale, but score
  should stay below 92 because Cycle 60-64 already provide much of the local
  exactness/locus/transversal substrate.
- ライバル比較: accept, base 88, `genius_eligibility: no`.  The correct ADL
  comparison is not that ADL cannot handle views, but that AAT preserves overlap
  failure as atom-supported obstruction plus source-ref trace plus repair
  transversal.
- G4 SCORE 監査: confirm, base 84, evidence multiplier 2.0, penalty 0,
  final score 168.  The running total becomes 8658/10000 and
  `proved-in-research` artifacts become 65.  The nonempty local-green witness
  imports standard `Quot.sound` from existing aligned chart exactness, but G4
  confirmed `x2.0` because the dependency is disclosed and localized, and the
  core cover/support/repair definitions remain `Quot.sound`-free.

## 関連

- `research/reports/G-aat-quality-surface-01.md`
- `research/ideas/g-aat-quality-surface-01-component-support-transversal-handoff-repairs.md`
- `research/ideas/g-aat-quality-surface-01-source-ref-handoff-component-support-bitset.md`

## 進捗ログ

- 2026-06-21: Cycle 65 G1 候補 pool から作成。
- 2026-06-21: G2-A revise を一巡だけ反映し、G2 四審判 accept。
- 2026-06-21: `HandoffCechExactness.lean` で Lean 証拠を固定。
- 2026-06-21: G3 形式化品質 revise に応じて witness を非空 exact chart
  `alignedSourceRefHandoffAtlas` に強化。
- 2026-06-21: G4 SCORE 監査で +168 を confirm。
