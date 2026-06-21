import Formal.AG.Research.QualitySurface.SelectedRouteCorrectionExactness
import Formal.AG.Research.QualitySurface.VisibleLawDeletionProtectedZero

/-!
Cycle 45 evidence for `G-aat-quality-surface-01`.

This file packages the selected commutator witnesses into a loss-aware atlas.
Each atlas cell is read through three predicates: visible tuple flatness, empty
protected route support, and source-ref exact visualization.  The atlas proves
that exactness is exactly visible flatness plus empty protected support, and it
exhibits finite witnesses for visible-law loss, protected-support loss, and
all-hit exact restoration.

The claim is relative to supplied finite source-ref packets, selected
repair/transport routes, selected correction vocabulary, and the explicit
packet-to-tuple bridge.  It does not assert complete diagnostic coverage for
all codebases, source extraction completeness, ArchMap correctness, global
repair planning, or whole-codebase quality.
-/

namespace Formal.AG.Research
namespace QualitySurface
namespace LossAwareCommutatorAtlas

open CodebaseTracePacket
open CodebaseTraceHolonomyPacket
open SourceRefExactVisualizationCriterion
open RouteDefectSupportTheory
open ExactVisualizationCriterionMinimality
open SelectedRouteDefectSupportHitting
open SelectedRouteCorrectionExactness

/-! ## Atlas cells and readings -/

/-- Selected commutator cells used by the loss-aware atlas. -/
inductive LossAwareAtlasCell where
  | visibleLawDeletionCell
  | tableLawDeletionCell
  | visibleRepairTransportCell
  | allHitCorrectionCell
  | obligationOnlyCorrectionCell
  deriving DecidableEq, Fintype

open LossAwareAtlasCell

/-- Visible tuple flatness of an atlas cell. -/
def CellVisibleTupleFlat : LossAwareAtlasCell -> Prop
  | visibleLawDeletionCell =>
      TupleVisibleVisualizationEquivalent
        SourceRefTupleBridge.endpointGridCertificate
        SourceRefTupleBridge.endpointGridCertificate
        VisibleLawDeletionProtectedZero.visibleLawRoute_repairThenTransportPacket
        VisibleLawDeletionProtectedZero.visibleLawRoute_transportThenRepairPacket
  | tableLawDeletionCell =>
      TupleVisibleVisualizationEquivalent
        SourceRefTupleBridge.endpointGridCertificate
        SourceRefTupleBridge.endpointGridCertificate
        tableRouteLeft tableRouteRight
  | visibleRepairTransportCell =>
      TupleVisibleVisualizationEquivalent
        SourceRefTupleBridge.endpointGridCertificate
        SourceRefTupleBridge.endpointGridCertificate
        visibleRouteLeft visibleRouteRight
  | allHitCorrectionCell =>
      TupleVisibleVisualizationEquivalent
        SourceRefTupleBridge.endpointGridCertificate
        SourceRefTupleBridge.endpointGridCertificate
        (correctedVisibleRouteLeft allRouteDefectCorrection) visibleRouteRight
  | obligationOnlyCorrectionCell =>
      TupleVisibleVisualizationEquivalent
        SourceRefTupleBridge.endpointGridCertificate
        SourceRefTupleBridge.endpointGridCertificate
        (correctedVisibleRouteLeft obligationOnlyCorrection) visibleRouteRight

/-- Empty protected route support of an atlas cell. -/
def CellProtectedRouteSupportEmpty : LossAwareAtlasCell -> Prop
  | visibleLawDeletionCell =>
      RouteDefectSupportEmpty
        VisibleLawDeletionProtectedZero.visibleLawRoute_repairThenTransportPacket
        VisibleLawDeletionProtectedZero.visibleLawRoute_transportThenRepairPacket
  | tableLawDeletionCell =>
      RouteDefectSupportEmpty tableRouteLeft tableRouteRight
  | visibleRepairTransportCell =>
      RouteDefectSupportEmpty visibleRouteLeft visibleRouteRight
  | allHitCorrectionCell =>
      RouteDefectSupportEmpty
        (correctedVisibleRouteLeft allRouteDefectCorrection) visibleRouteRight
  | obligationOnlyCorrectionCell =>
      RouteDefectSupportEmpty
        (correctedVisibleRouteLeft obligationOnlyCorrection) visibleRouteRight

/-- Source-ref exact visualization of an atlas cell. -/
def CellSourceRefExact : LossAwareAtlasCell -> Prop
  | visibleLawDeletionCell =>
      SourceRefExactVisualization
        SourceRefTupleBridge.endpointGridCertificate
        SourceRefTupleBridge.endpointGridCertificate
        VisibleLawDeletionProtectedZero.visibleLawRoute_repairThenTransportPacket
        VisibleLawDeletionProtectedZero.visibleLawRoute_transportThenRepairPacket
  | tableLawDeletionCell =>
      SourceRefExactVisualization
        SourceRefTupleBridge.endpointGridCertificate
        SourceRefTupleBridge.endpointGridCertificate
        tableRouteLeft tableRouteRight
  | visibleRepairTransportCell =>
      SourceRefExactVisualization
        SourceRefTupleBridge.endpointGridCertificate
        SourceRefTupleBridge.endpointGridCertificate
        visibleRouteLeft visibleRouteRight
  | allHitCorrectionCell =>
      SourceRefExactVisualization
        SourceRefTupleBridge.endpointGridCertificate
        SourceRefTupleBridge.endpointGridCertificate
        (correctedVisibleRouteLeft allRouteDefectCorrection) visibleRouteRight
  | obligationOnlyCorrectionCell =>
      SourceRefExactVisualization
        SourceRefTupleBridge.endpointGridCertificate
        SourceRefTupleBridge.endpointGridCertificate
        (correctedVisibleRouteLeft obligationOnlyCorrection) visibleRouteRight

/-! ## Atlas adequacy criterion -/

/--
Within the atlas, source-ref exactness is exactly visible tuple flatness plus
empty protected route support.
-/
theorem atlasCell_exact_iff_visible_empty
    (cell : LossAwareAtlasCell) :
    CellSourceRefExact cell ↔
      CellVisibleTupleFlat cell ∧ CellProtectedRouteSupportEmpty cell := by
  cases cell with
  | visibleLawDeletionCell =>
      exact exactVisualization_iff_visible_emptyRouteSupport
        SourceRefTupleBridge.endpointGridCertificate
        SourceRefTupleBridge.endpointGridCertificate
        VisibleLawDeletionProtectedZero.visibleLawRoute_repairThenTransportPacket
        VisibleLawDeletionProtectedZero.visibleLawRoute_transportThenRepairPacket
  | tableLawDeletionCell =>
      exact exactVisualization_iff_visible_emptyRouteSupport
        SourceRefTupleBridge.endpointGridCertificate
        SourceRefTupleBridge.endpointGridCertificate
        tableRouteLeft tableRouteRight
  | visibleRepairTransportCell =>
      exact exactVisualization_iff_visible_emptyRouteSupport
        SourceRefTupleBridge.endpointGridCertificate
        SourceRefTupleBridge.endpointGridCertificate
        visibleRouteLeft visibleRouteRight
  | allHitCorrectionCell =>
      exact exactVisualization_iff_visible_emptyRouteSupport
        SourceRefTupleBridge.endpointGridCertificate
        SourceRefTupleBridge.endpointGridCertificate
        (correctedVisibleRouteLeft allRouteDefectCorrection) visibleRouteRight
  | obligationOnlyCorrectionCell =>
      exact exactVisualization_iff_visible_emptyRouteSupport
        SourceRefTupleBridge.endpointGridCertificate
        SourceRefTupleBridge.endpointGridCertificate
        (correctedVisibleRouteLeft obligationOnlyCorrection) visibleRouteRight

/-- Missing visible flatness blocks exactness, even with empty protected support. -/
theorem atlasCell_not_exact_of_not_visible
    {cell : LossAwareAtlasCell}
    (hnotVisible : ¬ CellVisibleTupleFlat cell) :
    ¬ CellSourceRefExact cell := by
  intro hexact
  exact hnotVisible ((atlasCell_exact_iff_visible_empty cell).mp hexact).1

/-- Nonempty protected support blocks exactness, even when visible flatness holds. -/
theorem atlasCell_not_exact_of_not_empty
    {cell : LossAwareAtlasCell}
    (hnotEmpty : ¬ CellProtectedRouteSupportEmpty cell) :
    ¬ CellSourceRefExact cell := by
  intro hexact
  exact hnotEmpty ((atlasCell_exact_iff_visible_empty cell).mp hexact).2

/-! ## Witnessed atlas modes -/

/-- A cell where protected support is empty but visible flatness fails. -/
def VisibleLawLossCell (cell : LossAwareAtlasCell) : Prop :=
  ¬ CellVisibleTupleFlat cell ∧
    CellProtectedRouteSupportEmpty cell ∧
    ¬ CellSourceRefExact cell

/-- A cell where visible flatness holds but protected support is nonempty. -/
def ProtectedSupportLossCell (cell : LossAwareAtlasCell) : Prop :=
  CellVisibleTupleFlat cell ∧
    ¬ CellProtectedRouteSupportEmpty cell ∧
    ¬ CellSourceRefExact cell

/-- A cell where visible flatness and empty protected support restore exactness. -/
def ExactRestorationCell (cell : LossAwareAtlasCell) : Prop :=
  CellVisibleTupleFlat cell ∧
    CellProtectedRouteSupportEmpty cell ∧
    CellSourceRefExact cell

/-- The visible-law deletion cell witnesses visible-law loss. -/
theorem visibleLawDeletion_is_visibleLawLoss :
    VisibleLawLossCell visibleLawDeletionCell :=
  ⟨VisibleLawDeletionProtectedZero.visibleLawRoute_not_visibleTupleSurface,
    VisibleLawDeletionProtectedZero.visibleLawRoute_emptyDefectSupport,
    VisibleLawDeletionProtectedZero.visibleLawRoute_not_sourceRefExactVisualization⟩

/-- The table-law deletion cell witnesses protected-support loss. -/
theorem tableLawDeletion_is_protectedSupportLoss :
    ProtectedSupportLossCell tableLawDeletionCell :=
  ⟨TransportTableLawRouteLocalization.tokenSwapRoute_visibleTupleSurface,
    tableLawDeletion_not_emptyRouteSupport,
    TransportTableLawRouteLocalization.tokenSwapRoute_not_sourceRefExactVisualization⟩

/-- The visible repair/transport commutator is another protected-support loss cell. -/
theorem visibleRepairTransport_is_protectedSupportLoss :
    ProtectedSupportLossCell visibleRepairTransportCell := by
  refine ⟨VisibleRepairTransportCommutator.repairTransport_visibleTupleSurface_commutes,
    ?_, VisibleRepairTransportCommutator.repairTransport_not_sourceRefExactVisualization⟩
  intro hempty
  exact visibleRepairTransport_defectSupport_obligation
    (hempty SourceRefPacketProtectedComponent.obligation)

/-- The all-hit corrected route witnesses exact restoration. -/
theorem allHitCorrection_is_exactRestoration :
    ExactRestorationCell allHitCorrectionCell :=
  ⟨correctedVisibleRoute_tupleVisible allRouteDefectCorrection,
    allRouteDefectCorrection_supportEmpty,
    allRouteDefectCorrection_sourceRefExactVisualization⟩

/-- The obligation-only corrected route remains a protected-support loss cell. -/
theorem obligationOnlyCorrection_is_protectedSupportLoss :
    ProtectedSupportLossCell obligationOnlyCorrectionCell :=
  ⟨correctedVisibleRoute_tupleVisible obligationOnlyCorrection,
    obligationOnlyCorrection_not_supportEmpty,
    obligationOnlyCorrection_not_sourceRefExactVisualization⟩

/-- The atlas contains witnesses for visible loss, protected-support loss, and exact restoration. -/
theorem lossAwareAtlas_has_all_modes :
    (∃ cell, VisibleLawLossCell cell) ∧
    (∃ cell, ProtectedSupportLossCell cell) ∧
    (∃ cell, ExactRestorationCell cell) :=
  ⟨⟨visibleLawDeletionCell, visibleLawDeletion_is_visibleLawLoss⟩,
    ⟨tableLawDeletionCell, tableLawDeletion_is_protectedSupportLoss⟩,
    ⟨allHitCorrectionCell, allHitCorrection_is_exactRestoration⟩⟩

/-! ## Theorem package -/

/--
Cycle-45 theorem package: a finite loss-aware commutator atlas whose cells are
adequate for the exact-visualization criterion and which contains witnesses for
visible-law loss, protected-support loss, and all-hit exact restoration.
-/
theorem lossAwareCommutatorAtlasAdequacy_package :
    (∀ cell,
      CellSourceRefExact cell ↔
        CellVisibleTupleFlat cell ∧ CellProtectedRouteSupportEmpty cell) ∧
    (∀ {cell}, ¬ CellVisibleTupleFlat cell -> ¬ CellSourceRefExact cell) ∧
    (∀ {cell}, ¬ CellProtectedRouteSupportEmpty cell -> ¬ CellSourceRefExact cell) ∧
    VisibleLawLossCell visibleLawDeletionCell ∧
    ProtectedSupportLossCell tableLawDeletionCell ∧
    ProtectedSupportLossCell visibleRepairTransportCell ∧
    ExactRestorationCell allHitCorrectionCell ∧
    ProtectedSupportLossCell obligationOnlyCorrectionCell ∧
    (∃ cell, VisibleLawLossCell cell) ∧
    (∃ cell, ProtectedSupportLossCell cell) ∧
    (∃ cell, ExactRestorationCell cell) := by
  exact ⟨atlasCell_exact_iff_visible_empty,
    by
      intro cell hnotVisible
      exact atlasCell_not_exact_of_not_visible hnotVisible,
    by
      intro cell hnotEmpty
      exact atlasCell_not_exact_of_not_empty hnotEmpty,
    visibleLawDeletion_is_visibleLawLoss,
    tableLawDeletion_is_protectedSupportLoss,
    visibleRepairTransport_is_protectedSupportLoss,
    allHitCorrection_is_exactRestoration,
    obligationOnlyCorrection_is_protectedSupportLoss,
    lossAwareAtlas_has_all_modes.1,
    lossAwareAtlas_has_all_modes.2.1,
    lossAwareAtlas_has_all_modes.2.2⟩

end LossAwareCommutatorAtlas
end QualitySurface
end Formal.AG.Research
