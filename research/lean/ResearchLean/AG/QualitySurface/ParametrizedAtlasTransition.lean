import ResearchLean.AG.QualitySurface.ParametrizedLossAwareAtlas

/-!
Cycle 50 evidence for `G-aat-quality-surface-01`.

This file adds transition maps to the parametrized loss-aware atlas.  Along the
concrete staged correction relation, source-ref exactness, protected-support
emptiness, and exact restoration are upward closed.  Any pre-all stage can
transition to the all-branches stage, crossing from protected-support loss to
exact restoration without changing visible tuple flatness.

The claim is relative to the concrete staged selected correction relation and
the finite parametrized loss-aware atlas.  It does not assert arbitrary atlas
transition maps, global repair planning, runtime patch synthesis, source
extraction completeness, ArchMap correctness, or whole-codebase quality.
-/

namespace ResearchLean.AG
namespace QualitySurface
namespace ParametrizedAtlasTransition

open ParametrizedSelectedCorrectionSystem
open ParametrizedLossAwareAtlas
open ParametrizedLossAwareCell
open RepairStage

/-! ## Stage transitions inside the parametrized atlas -/

/-- The staged atlas cell at a repair stage. -/
def StageAtlasCell (stage : RepairStage) : ParametrizedLossAwareCell :=
  stagedCorrectionCell stage

/-- The concrete transition relation between staged atlas cells. -/
def StageAtlasTransition (left right : RepairStage) : Prop :=
  StageLe left right

/-- Every staged atlas cell is visible-flat, independently of transition. -/
theorem stageAtlasCell_visibleInvariant
    (stage : RepairStage) :
    ParamCellVisibleTupleFlat (StageAtlasCell stage) :=
  stagedCell_visibleTupleFlat stage

/-- Source-ref exactness is upward closed along staged atlas transitions. -/
theorem stageTransition_sourceRefExact_upwardClosed
    {left right : RepairStage}
    (htransition : StageAtlasTransition left right)
    (hexact : ParamCellSourceRefExact (StageAtlasCell left)) :
    ParamCellSourceRefExact (StageAtlasCell right) := by
  have hleftAll :
      left = allBranches :=
    (stagedCell_sourceRefExact_iff_allBranches left).mp hexact
  subst hleftAll
  cases right with
  | uncorrected =>
      cases htransition
  | obligationOnly =>
      cases htransition
  | allBranches =>
      exact (stagedCell_sourceRefExact_iff_allBranches allBranches).mpr rfl

/-- Protected-support emptiness is upward closed along staged atlas transitions. -/
theorem stageTransition_supportEmpty_upwardClosed
    {left right : RepairStage}
    (htransition : StageAtlasTransition left right)
    (hempty : ParamCellProtectedRouteSupportEmpty (StageAtlasCell left)) :
    ParamCellProtectedRouteSupportEmpty (StageAtlasCell right) := by
  have hleftAll :
      left = allBranches :=
    (stagedCell_supportEmpty_iff_allBranches left).mp hempty
  subst hleftAll
  cases right with
  | uncorrected =>
      cases htransition
  | obligationOnly =>
      cases htransition
  | allBranches =>
      exact (stagedCell_supportEmpty_iff_allBranches allBranches).mpr rfl

/-- Exact restoration is upward closed along staged atlas transitions. -/
theorem stageTransition_exactRestoration_upwardClosed
    {left right : RepairStage}
    (htransition : StageAtlasTransition left right)
    (hrestored : ParamExactRestorationCell (StageAtlasCell left)) :
    ParamExactRestorationCell (StageAtlasCell right) := by
  have hleftAll :
      left = allBranches :=
    (stagedCell_exactRestoration_iff_allBranches left).mp hrestored
  subst hleftAll
  cases right with
  | uncorrected =>
      cases htransition
  | obligationOnly =>
      cases htransition
  | allBranches =>
      exact stagedCell_allBranches_is_exactRestoration

/-- Exact staged cells cannot transition to protected-support loss cells. -/
theorem stageTransition_no_exact_to_protectedSupportLoss
    {left right : RepairStage}
    (htransition : StageAtlasTransition left right)
    (hexact : ParamCellSourceRefExact (StageAtlasCell left)) :
    ¬ ParamProtectedSupportLossCell (StageAtlasCell right) := by
  intro hloss
  exact hloss.2.2
    (stageTransition_sourceRefExact_upwardClosed htransition hexact)

/-! ## Loss-to-restoration transitions -/

/-- A staged transition crosses from protected-support loss to exact restoration. -/
def StageLossToRestorationTransition
    (left right : RepairStage) : Prop :=
  StageAtlasTransition left right ∧
    ParamProtectedSupportLossCell (StageAtlasCell left) ∧
    ParamExactRestorationCell (StageAtlasCell right)

/-- Every pre-all stage transitions to all-branches. -/
theorem stageTransition_to_allBranches_of_not_allBranches
    {stage : RepairStage}
    (hstage : stage ≠ allBranches) :
    StageAtlasTransition stage allBranches := by
  cases stage with
  | uncorrected => trivial
  | obligationOnly => trivial
  | allBranches => exact False.elim (hstage rfl)

/--
Every pre-all staged cell can transition from protected-support loss to exact
restoration at all-branches.
-/
theorem preAllStage_to_allBranches_lossToRestoration
    {stage : RepairStage}
    (hstage : stage ≠ allBranches) :
    StageLossToRestorationTransition stage allBranches :=
  ⟨stageTransition_to_allBranches_of_not_allBranches hstage,
    stagedCell_protectedSupportLoss_of_not_allBranches hstage,
    stagedCell_allBranches_is_exactRestoration⟩

/-- The obligation-only stage crosses to exact restoration at all-branches. -/
theorem obligationOnly_to_allBranches_lossToRestoration :
    StageLossToRestorationTransition obligationOnly allBranches :=
  preAllStage_to_allBranches_lossToRestoration (by intro h; cases h)

/-- The uncorrected stage also crosses to exact restoration at all-branches. -/
theorem uncorrected_to_allBranches_lossToRestoration :
    StageLossToRestorationTransition uncorrected allBranches :=
  preAllStage_to_allBranches_lossToRestoration (by intro h; cases h)

/-! ## Theorem package -/

/--
Cycle-50 theorem package: stage transitions preserve visible flatness and make
source-ref exactness, protected-support emptiness, and exact restoration
upward closed.  Pre-all stages cross from protected-support loss to exact
restoration at all-branches.
-/
theorem parametrizedAtlasTransition_package :
    (∀ stage, ParamCellVisibleTupleFlat (StageAtlasCell stage)) ∧
    (∀ {left right},
      StageAtlasTransition left right ->
        ParamCellSourceRefExact (StageAtlasCell left) ->
          ParamCellSourceRefExact (StageAtlasCell right)) ∧
    (∀ {left right},
      StageAtlasTransition left right ->
        ParamCellProtectedRouteSupportEmpty (StageAtlasCell left) ->
          ParamCellProtectedRouteSupportEmpty (StageAtlasCell right)) ∧
    (∀ {left right},
      StageAtlasTransition left right ->
        ParamExactRestorationCell (StageAtlasCell left) ->
          ParamExactRestorationCell (StageAtlasCell right)) ∧
    (∀ {left right},
      StageAtlasTransition left right ->
        ParamCellSourceRefExact (StageAtlasCell left) ->
          ¬ ParamProtectedSupportLossCell (StageAtlasCell right)) ∧
    (∀ {stage},
      stage ≠ allBranches ->
        StageLossToRestorationTransition stage allBranches) ∧
    StageLossToRestorationTransition obligationOnly allBranches ∧
    StageLossToRestorationTransition uncorrected allBranches := by
  exact ⟨stageAtlasCell_visibleInvariant,
    fun htransition hexact =>
      stageTransition_sourceRefExact_upwardClosed htransition hexact,
    fun htransition hempty =>
      stageTransition_supportEmpty_upwardClosed htransition hempty,
    fun htransition hrestored =>
      stageTransition_exactRestoration_upwardClosed htransition hrestored,
    fun htransition hexact =>
      stageTransition_no_exact_to_protectedSupportLoss htransition hexact,
    fun hstage => preAllStage_to_allBranches_lossToRestoration hstage,
    obligationOnly_to_allBranches_lossToRestoration,
    uncorrected_to_allBranches_lossToRestoration⟩

end ParametrizedAtlasTransition
end QualitySurface
end ResearchLean.AG
