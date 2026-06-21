import Formal.AG.Research.QualitySurface.HandoffRepairTransversal

/-!
Cycle 65 evidence for `G-aat-quality-surface-01`.

This file packages a finite Cech-style handoff cover.  A cover has chart
atlases and a separate overlap cocycle atlas; global exactness is local chart
interaction exactness plus overlap holonomy vanishing.  The overlap component
support is read directly from the overlap cocycle atlas, not from failure of
global exactness.

The claim is relative to selected finite source-ref handoff atlases, supplied
chart and overlap data, bounded handoff laws, the finite `BridgeComponent`
vocabulary, and declared component-level repair predicates.  It does not assert
source extraction completeness, ArchMap correctness, runtime repair synthesis,
arbitrary route enumeration, global sheaf completeness, or whole-codebase
quality.
-/

namespace Formal.AG.Research
namespace QualitySurface
namespace HandoffCechExactness

open HeterogeneousRouteInteraction
open HeterogeneousRouteInteraction.BridgeComponent
open SourceRefHandoffBridge
open SourceRefHandoffHolonomyCorrespondence
open SourceRefHandoffObstructionLocus
open SourceRefHandoffComponentSupport
open HandoffRepairTransversalTheorem

/-! ## Finite chart/overlap handoff covers -/

/--
A finite Cech-style handoff cover.

The chart atlases and overlap cocycle atlas are intentionally separate fields.
This prevents the cover from being a shallow alias for one
`SourceRefHandoffAtlas`.
-/
structure HandoffCechCover where
  charts : List SourceRefHandoffAtlas
  overlapCocycle : SourceRefHandoffAtlas

/-- Every chart atlas is already interaction exact. -/
def HandoffCechLocalExact
    (cover : HandoffCechCover) : Prop :=
  forall chart, chart ∈ cover.charts -> HandoffAtlasInteractionExact chart

/-- The overlap cocycle has no handoff holonomy. -/
def HandoffCechOverlapHolonomyVanishes
    (cover : HandoffCechCover) : Prop :=
  HandoffAtlasHolonomyVanishes cover.overlapCocycle

/-- Global exactness is local chart exactness plus overlap cocycle vanishing. -/
def HandoffCechGlobalExact
    (cover : HandoffCechCover) : Prop :=
  HandoffCechLocalExact cover /\
    HandoffCechOverlapHolonomyVanishes cover

/-- Protected component support of the overlap cocycle. -/
def HandoffCechOverlapSupport
    (cover : HandoffCechCover)
    (component : BridgeComponent) : Prop :=
  HandoffComponentSupport cover.overlapCocycle component

/-- The overlap cocycle has some protected component support. -/
def HandoffCechOverlapSupportNonempty
    (cover : HandoffCechCover) : Prop :=
  exists component, HandoffCechOverlapSupport cover component

/-- The overlap cocycle has no protected component support. -/
def HandoffCechOverlapSupportEmpty
    (cover : HandoffCechCover) : Prop :=
  Not (HandoffCechOverlapSupportNonempty cover)

/-- Empty overlap support is exactly overlap holonomy vanishing. -/
theorem handoffCech_overlapSupportEmpty_iff_holonomyVanishes
    (cover : HandoffCechCover) :
    HandoffCechOverlapSupportEmpty cover <->
      HandoffCechOverlapHolonomyVanishes cover := by
  exact handoffComponentSupport_empty_iff_holonomyVanishes
    cover.overlapCocycle

/-- Nonempty component support is exactly nonvanishing handoff holonomy. -/
theorem handoffComponentSupport_nonempty_iff_not_holonomyVanishes
    (atlas : SourceRefHandoffAtlas) :
    HandoffComponentSupportNonempty atlas <->
      Not (HandoffAtlasHolonomyVanishes atlas) :=
  (handoffComponentSupport_nonempty_iff_locusNonempty atlas).trans
    (handoffObstructionLocus_nonempty_iff_not_holonomyVanishes atlas)

/-- Global exactness is local chart exactness plus empty overlap support. -/
theorem handoffCech_globalExact_iff_localExact_and_overlapSupportEmpty
    (cover : HandoffCechCover) :
    HandoffCechGlobalExact cover <->
      HandoffCechLocalExact cover /\
        HandoffCechOverlapSupportEmpty cover := by
  constructor
  · intro hglobal
    exact
      ⟨hglobal.1,
        (handoffCech_overlapSupportEmpty_iff_holonomyVanishes cover).mpr
          hglobal.2⟩
  · intro hpair
    exact
      ⟨hpair.1,
        (handoffCech_overlapSupportEmpty_iff_holonomyVanishes cover).mp
          hpair.2⟩

/--
Under local chart exactness, a nonempty overlap support is exactly failure of
global handoff exactness.
-/
theorem handoffCech_overlapSupport_nonempty_iff_notGlobalExact_of_local
    {cover : HandoffCechCover}
    (hlocal : HandoffCechLocalExact cover) :
    HandoffCechOverlapSupportNonempty cover <->
      Not (HandoffCechGlobalExact cover) := by
  constructor
  · intro hsupport hglobal
    have hnotVanish :
        Not (HandoffAtlasHolonomyVanishes cover.overlapCocycle) :=
      (handoffComponentSupport_nonempty_iff_not_holonomyVanishes
        cover.overlapCocycle).mp hsupport
    exact hnotVanish hglobal.2
  · intro hnotGlobal
    apply
      (handoffComponentSupport_nonempty_iff_not_holonomyVanishes
        cover.overlapCocycle).mpr
    intro hvanish
    exact hnotGlobal ⟨hlocal, hvanish⟩

/-! ## Declared repair obligations for overlap cocycles -/

/-- Declared repair clearance of all overlap component support. -/
def HandoffCechRepairObligation
    (cover : HandoffCechCover)
    (plan : HandoffRepairPlan) : Prop :=
  DeclaredHandoffRepairClears cover.overlapCocycle plan

/-- The declared repair support hits every overlap component support. -/
def HandoffCechOverlapRepairTransversal
    (cover : HandoffCechCover)
    (support : HandoffRepairSupport) : Prop :=
  HandoffRepairTransversal cover.overlapCocycle support

/--
For component-complete declared repair plans, overlap repair clearance is
exactly overlap repair transversality.
-/
theorem handoffCech_repairObligation_iff_overlapRepairTransversal_of_componentComplete
    {cover : HandoffCechCover}
    {plan : HandoffRepairPlan}
    (hcomplete :
      ComponentCompleteHandoffRepairPlan cover.overlapCocycle plan) :
    HandoffCechRepairObligation cover plan <->
      HandoffCechOverlapRepairTransversal cover plan.touched :=
  declaredClearance_iff_hitsEvery_of_componentComplete hcomplete

/-! ## A local-green / overlap-obstructed finite witness -/

/--
A cover whose only chart is interaction exact but whose separate overlap
cocycle has a support-law deletion obstruction.
-/
def locallyExactOverlapObstructedCover : HandoffCechCover where
  charts := [alignedSourceRefHandoffAtlas]
  overlapCocycle := supportLawDeletionAtlas

/-- Every chart in the witness cover is interaction exact. -/
theorem locallyExactOverlapObstructedCover_localExact :
    HandoffCechLocalExact locallyExactOverlapObstructedCover := by
  intro chart hmem
  simp [locallyExactOverlapObstructedCover] at hmem
  subst chart
  exact alignedSourceRefHandoffAtlas_interactionExact

/-- The witness cover has protected support in its overlap cocycle. -/
theorem locallyExactOverlapObstructedCover_overlapSupportNonempty :
    HandoffCechOverlapSupportNonempty
      locallyExactOverlapObstructedCover :=
  ⟨BridgeComponent.support, supportLawDeletion_componentSupport⟩

/-- The witness cover is not globally exact. -/
theorem locallyExactOverlapObstructedCover_notGlobalExact :
    Not (HandoffCechGlobalExact locallyExactOverlapObstructedCover) :=
  (handoffCech_overlapSupport_nonempty_iff_notGlobalExact_of_local
    locallyExactOverlapObstructedCover_localExact).mp
      locallyExactOverlapObstructedCover_overlapSupportNonempty

/--
Local chart exactness is not faithful to global handoff exactness unless the
overlap cocycle support is also exposed.
-/
theorem locallyExact_not_faithful_without_overlapCocycle :
    HandoffCechLocalExact locallyExactOverlapObstructedCover /\
      HandoffCechOverlapSupportNonempty locallyExactOverlapObstructedCover /\
      Not (HandoffCechGlobalExact locallyExactOverlapObstructedCover) :=
  ⟨locallyExactOverlapObstructedCover_localExact,
    locallyExactOverlapObstructedCover_overlapSupportNonempty,
    locallyExactOverlapObstructedCover_notGlobalExact⟩

/-! ## Theorem package -/

/--
Cycle-65 theorem package: a finite Cech-style handoff cover separates local
chart exactness from overlap cocycle support.  Global exactness is equivalent
to local exactness plus empty overlap support, and component-complete declared
repair clears the overlap exactly when its support is an overlap repair
transversal.  There is a finite witness with exact local charts and obstructed
overlap cocycle support.
-/
theorem handoffCechExactness_package :
    (forall cover,
      HandoffCechOverlapSupportEmpty cover <->
        HandoffCechOverlapHolonomyVanishes cover) /\
      (forall cover,
        HandoffCechGlobalExact cover <->
          HandoffCechLocalExact cover /\
            HandoffCechOverlapSupportEmpty cover) /\
      (forall {cover},
        HandoffCechLocalExact cover ->
          (HandoffCechOverlapSupportNonempty cover <->
            Not (HandoffCechGlobalExact cover))) /\
      (forall {cover} {plan : HandoffRepairPlan},
        ComponentCompleteHandoffRepairPlan cover.overlapCocycle plan ->
          (HandoffCechRepairObligation cover plan <->
            HandoffCechOverlapRepairTransversal cover plan.touched)) /\
      HandoffCechLocalExact locallyExactOverlapObstructedCover /\
      HandoffCechOverlapSupportNonempty
        locallyExactOverlapObstructedCover /\
      Not (HandoffCechGlobalExact
        locallyExactOverlapObstructedCover) := by
  exact
    ⟨handoffCech_overlapSupportEmpty_iff_holonomyVanishes,
      handoffCech_globalExact_iff_localExact_and_overlapSupportEmpty,
      fun {cover} hlocal =>
        handoffCech_overlapSupport_nonempty_iff_notGlobalExact_of_local
          (cover := cover) hlocal,
      fun {cover} {plan} hcomplete =>
        handoffCech_repairObligation_iff_overlapRepairTransversal_of_componentComplete
          (cover := cover) (plan := plan) hcomplete,
      locallyExactOverlapObstructedCover_localExact,
      locallyExactOverlapObstructedCover_overlapSupportNonempty,
      locallyExactOverlapObstructedCover_notGlobalExact⟩

end HandoffCechExactness
end QualitySurface
end Formal.AG.Research
