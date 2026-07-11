import ResearchLean.AG.QualitySurface.ParametrizedSelectedCorrectionSystem

/-!
Cycle 49 evidence for `G-aat-quality-surface-01`.

This file combines the loss-aware commutator atlas with the parametrized
selected correction system.  The atlas has baseline loss-aware cells and staged
correction cells.  For staged correction cells, visible tuple flatness is
constant while protected-support emptiness and source-ref exactness occur
exactly at the all-branches stage.

The claim is relative to the selected route-defect atom vocabulary, staged
selected correction semantics, the baseline loss-aware cells, and the explicit
source-ref packet bridge.  It does not assert global repair planning, runtime
patch synthesis, source extraction completeness, ArchMap correctness, or
whole-codebase quality.
-/

namespace ResearchLean.AG
namespace QualitySurface
namespace ParametrizedLossAwareAtlas

open CodebaseTracePacket
open SourceRefExactVisualizationCriterion
open RouteDefectSupportTheory
open ExactVisualizationCriterionMinimality
open SelectedRouteDefectSupportHitting
open SelectedRouteCorrectionExactness
open LossAwareCommutatorAtlas
open LossAwareAtlasCell
open ParametrizedSelectedCorrectionSystem
open RepairStage

/-! ## Parametrized loss-aware atlas cells -/

/-- A loss-aware atlas with baseline cells and staged selected correction cells. -/
inductive ParametrizedLossAwareCell where
  | baselineCell : LossAwareAtlasCell -> ParametrizedLossAwareCell
  | stagedCorrectionCell : RepairStage -> ParametrizedLossAwareCell
  deriving DecidableEq, Fintype

open ParametrizedLossAwareCell

/-- Visible tuple flatness of a parametrized loss-aware atlas cell. -/
def ParamCellVisibleTupleFlat : ParametrizedLossAwareCell -> Prop
  | baselineCell cell => CellVisibleTupleFlat cell
  | stagedCorrectionCell stage =>
      TupleVisibleVisualizationEquivalent
        SourceRefTupleBridge.endpointGridCertificate
        SourceRefTupleBridge.endpointGridCertificate
        (correctedVisibleRouteLeft (stagedCorrection stage)) visibleRouteRight

/-- Empty protected route support of a parametrized loss-aware atlas cell. -/
def ParamCellProtectedRouteSupportEmpty : ParametrizedLossAwareCell -> Prop
  | baselineCell cell => CellProtectedRouteSupportEmpty cell
  | stagedCorrectionCell stage =>
      RouteDefectSupportEmpty
        (correctedVisibleRouteLeft (stagedCorrection stage)) visibleRouteRight

/-- Source-ref exactness of a parametrized loss-aware atlas cell. -/
def ParamCellSourceRefExact : ParametrizedLossAwareCell -> Prop
  | baselineCell cell => CellSourceRefExact cell
  | stagedCorrectionCell stage =>
      CorrectionSourceRefExact (stagedCorrection stage)

/-! ## Parametrized exactness criterion -/

/-- Parametrized atlas exactness is visible flatness plus empty protected support. -/
theorem paramCell_exact_iff_visible_empty
    (cell : ParametrizedLossAwareCell) :
    ParamCellSourceRefExact cell ↔
      ParamCellVisibleTupleFlat cell ∧
        ParamCellProtectedRouteSupportEmpty cell := by
  cases cell with
  | baselineCell base =>
      exact atlasCell_exact_iff_visible_empty base
  | stagedCorrectionCell stage =>
      exact exactVisualization_iff_visible_emptyRouteSupport
        SourceRefTupleBridge.endpointGridCertificate
        SourceRefTupleBridge.endpointGridCertificate
        (correctedVisibleRouteLeft (stagedCorrection stage)) visibleRouteRight

/-- Every staged correction cell is visibly flat. -/
theorem stagedCell_visibleTupleFlat
    (stage : RepairStage) :
    ParamCellVisibleTupleFlat (stagedCorrectionCell stage) :=
  correctedVisibleRoute_tupleVisible (stagedCorrection stage)

/-- Staged correction cells have empty protected support exactly at all-branches. -/
theorem stagedCell_supportEmpty_iff_allBranches
    (stage : RepairStage) :
    ParamCellProtectedRouteSupportEmpty (stagedCorrectionCell stage) ↔
      stage = allBranches := by
  constructor
  · intro hempty
    have hhits :
        CorrectionHitsAllBranches (stagedCorrection stage) :=
      (correctedVisibleRoute_supportEmpty_iff_hits
        (stagedCorrection stage)).mp hempty
    have hexact :
        CorrectionSourceRefExact (stagedCorrection stage) :=
      (correctionSourceRefExact_iff_hitsAllBranches
        (stagedCorrection stage)).mpr hhits
    exact (stagedCorrection_exact_iff_allBranches stage).mp hexact
  · intro hstage
    subst hstage
    have hhits :
        CorrectionHitsAllBranches (stagedCorrection allBranches) :=
      (correctionSourceRefExact_iff_hitsAllBranches
        (stagedCorrection allBranches)).mp stagedCorrection_allBranches_exact
    exact (correctedVisibleRoute_supportEmpty_iff_hits
      (stagedCorrection allBranches)).mpr hhits

/-- Staged correction cells are source-ref exact exactly at all-branches. -/
theorem stagedCell_sourceRefExact_iff_allBranches
    (stage : RepairStage) :
    ParamCellSourceRefExact (stagedCorrectionCell stage) ↔
      stage = allBranches :=
  stagedCorrection_exact_iff_allBranches stage

/-! ## Parametrized loss modes -/

/-- A cell where protected support is empty but visible flatness fails. -/
def ParamVisibleLawLossCell (cell : ParametrizedLossAwareCell) : Prop :=
  ¬ ParamCellVisibleTupleFlat cell ∧
    ParamCellProtectedRouteSupportEmpty cell ∧
    ¬ ParamCellSourceRefExact cell

/-- A cell where visible flatness holds but protected support is nonempty. -/
def ParamProtectedSupportLossCell (cell : ParametrizedLossAwareCell) : Prop :=
  ParamCellVisibleTupleFlat cell ∧
    ¬ ParamCellProtectedRouteSupportEmpty cell ∧
    ¬ ParamCellSourceRefExact cell

/-- A cell where visible flatness and empty protected support restore exactness. -/
def ParamExactRestorationCell (cell : ParametrizedLossAwareCell) : Prop :=
  ParamCellVisibleTupleFlat cell ∧
    ParamCellProtectedRouteSupportEmpty cell ∧
    ParamCellSourceRefExact cell

/-- Baseline visible-law deletion remains a visible-law loss cell. -/
theorem baseline_visibleLawDeletion_is_visibleLawLoss :
    ParamVisibleLawLossCell (baselineCell visibleLawDeletionCell) :=
  visibleLawDeletion_is_visibleLawLoss

/-- Baseline table-law deletion remains a protected-support loss cell. -/
theorem baseline_tableLawDeletion_is_protectedSupportLoss :
    ParamProtectedSupportLossCell (baselineCell tableLawDeletionCell) :=
  tableLawDeletion_is_protectedSupportLoss

/-- A staged correction cell is protected-support loss before all branches are hit. -/
theorem stagedCell_protectedSupportLoss_of_not_allBranches
    {stage : RepairStage}
    (hstage : stage ≠ allBranches) :
    ParamProtectedSupportLossCell (stagedCorrectionCell stage) := by
  refine ⟨stagedCell_visibleTupleFlat stage, ?_, ?_⟩
  · intro hempty
    exact hstage ((stagedCell_supportEmpty_iff_allBranches stage).mp hempty)
  · intro hexact
    exact hstage ((stagedCell_sourceRefExact_iff_allBranches stage).mp hexact)

/-- The all-branches staged correction cell is an exact restoration cell. -/
theorem stagedCell_allBranches_is_exactRestoration :
    ParamExactRestorationCell (stagedCorrectionCell allBranches) :=
  ⟨stagedCell_visibleTupleFlat allBranches,
    (stagedCell_supportEmpty_iff_allBranches allBranches).mpr rfl,
    stagedCorrection_allBranches_exact⟩

/-- The staged exact-restoration locus is exactly the all-branches stage. -/
theorem stagedCell_exactRestoration_iff_allBranches
    (stage : RepairStage) :
    ParamExactRestorationCell (stagedCorrectionCell stage) ↔
      stage = allBranches := by
  constructor
  · intro hrestored
    exact (stagedCell_sourceRefExact_iff_allBranches stage).mp hrestored.2.2
  · intro hstage
    subst hstage
    exact stagedCell_allBranches_is_exactRestoration

/-- The parametrized atlas contains visible-law loss, protected-support loss, and exact restoration. -/
theorem parametrizedLossAwareAtlas_has_all_modes :
    (∃ cell, ParamVisibleLawLossCell cell) ∧
    (∃ cell, ParamProtectedSupportLossCell cell) ∧
    (∃ cell, ParamExactRestorationCell cell) :=
  ⟨⟨baselineCell visibleLawDeletionCell,
      baseline_visibleLawDeletion_is_visibleLawLoss⟩,
    ⟨stagedCorrectionCell obligationOnly,
      stagedCell_protectedSupportLoss_of_not_allBranches (by intro h; cases h)⟩,
    ⟨stagedCorrectionCell allBranches,
      stagedCell_allBranches_is_exactRestoration⟩⟩

/-! ## Theorem package -/

/--
Cycle-49 theorem package: the loss-aware atlas is parametrized by staged
selected correction cells.  Staged cells are visibly flat at every stage, and
their support-empty / exact / exact-restoration loci are exactly all-branches.
-/
theorem parametrizedLossAwareAtlas_package :
    (∀ cell,
      ParamCellSourceRefExact cell ↔
        ParamCellVisibleTupleFlat cell ∧
          ParamCellProtectedRouteSupportEmpty cell) ∧
    (∀ stage, ParamCellVisibleTupleFlat (stagedCorrectionCell stage)) ∧
    (∀ stage,
      ParamCellProtectedRouteSupportEmpty (stagedCorrectionCell stage) ↔
        stage = allBranches) ∧
    (∀ stage,
      ParamCellSourceRefExact (stagedCorrectionCell stage) ↔
        stage = allBranches) ∧
    (∀ {stage},
      stage ≠ allBranches ->
        ParamProtectedSupportLossCell (stagedCorrectionCell stage)) ∧
    ParamExactRestorationCell (stagedCorrectionCell allBranches) ∧
    (∀ stage,
      ParamExactRestorationCell (stagedCorrectionCell stage) ↔
        stage = allBranches) ∧
    ParamVisibleLawLossCell (baselineCell visibleLawDeletionCell) ∧
    ParamProtectedSupportLossCell (baselineCell tableLawDeletionCell) ∧
    (∃ cell, ParamVisibleLawLossCell cell) ∧
    (∃ cell, ParamProtectedSupportLossCell cell) ∧
    (∃ cell, ParamExactRestorationCell cell) := by
  exact ⟨paramCell_exact_iff_visible_empty,
    stagedCell_visibleTupleFlat,
    stagedCell_supportEmpty_iff_allBranches,
    stagedCell_sourceRefExact_iff_allBranches,
    by
      intro stage hstage
      exact stagedCell_protectedSupportLoss_of_not_allBranches hstage,
    stagedCell_allBranches_is_exactRestoration,
    stagedCell_exactRestoration_iff_allBranches,
    baseline_visibleLawDeletion_is_visibleLawLoss,
    baseline_tableLawDeletion_is_protectedSupportLoss,
    parametrizedLossAwareAtlas_has_all_modes.1,
    parametrizedLossAwareAtlas_has_all_modes.2.1,
    parametrizedLossAwareAtlas_has_all_modes.2.2⟩

end ParametrizedLossAwareAtlas
end QualitySurface
end ResearchLean.AG
