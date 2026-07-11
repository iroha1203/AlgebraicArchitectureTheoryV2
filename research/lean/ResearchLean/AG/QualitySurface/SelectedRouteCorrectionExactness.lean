import ResearchLean.AG.QualitySurface.SelectedRouteDefectSupportHitting
import ResearchLean.AG.QualitySurface.ExactVisualizationCriterionMinimality

/-!
Cycle 44 evidence for `G-aat-quality-surface-01`.

This file closes the gap left by Cycle 43.  Cycle 43 showed that selected
protected-component correction is equivalent to hitting every selected
route-defect branch.  Here we add the off-selected flatness computation from
Cycle 38 and prove that hitting every selected branch is equivalent to empty
protected route support for the corrected endpoint route.  By the Cycle 42
criterion, the corrected endpoint route is source-ref exact precisely when the
selected route-defect family is hit.

The claim is relative to supplied finite source-ref packets, the selected
visible-flat route endpoints, and the selected protected component vocabulary.
It does not assert a global correction planner, canonical runtime patch,
source extraction completeness, ArchMap correctness, or whole-codebase quality.
-/

namespace ResearchLean.AG
namespace QualitySurface
namespace SelectedRouteCorrectionExactness

open CodebaseTracePacket
open CodebaseTraceHolonomyPacket
open SourceRefExactVisualizationCriterion
open RouteDefectSupportTheory
open SelectedRouteDefectSupportHitting
open ExactVisualizationCriterionMinimality
open RouteDefectBranch

/-! ## Visible surface of corrected endpoint routes -/

/-- Selected correction does not change the visible packet surface. -/
theorem correctedVisibleRoute_supportSurface_equivalent
    (correction : RouteDefectAtom -> Bool) :
    supportSurfaceReading.Equivalent
      (correctedVisibleRouteLeft correction) visibleRouteRight := by
  have hvisible :
      supportSurfaceReading.Equivalent visibleRouteLeft visibleRouteRight :=
    VisibleRepairTransportCommutator.repairTransport_visiblePacketSurface_commutes
  exact hvisible

/-- Selected correction preserves visible tuple equivalence with the right endpoint. -/
theorem correctedVisibleRoute_tupleVisible
    (correction : RouteDefectAtom -> Bool) :
    TupleVisibleVisualizationEquivalent
      SourceRefTupleBridge.endpointGridCertificate
      SourceRefTupleBridge.endpointGridCertificate
      (correctedVisibleRouteLeft correction) visibleRouteRight :=
  SourceRefTupleBridge.packet_supportSurface_projects_to_tuple_visible
    (correctedVisibleRoute_supportSurface_equivalent correction)

/-! ## Empty protected route support iff all selected branches are hit -/

/--
If a selected correction hits every selected branch, then the corrected endpoint
route has empty protected route support.  The selected coordinates are repaired
by copying the right endpoint, while off-storage repair/table coordinates stay
flat by the Cycle 38 exact support computation.
-/
theorem correctedVisibleRoute_supportEmpty_of_hits
    {correction : RouteDefectAtom -> Bool}
    (hhits : ∀ branch, CorrectionHitsRouteDefectBranch correction branch) :
    RouteDefectSupportEmpty
      (correctedVisibleRouteLeft correction) visibleRouteRight := by
  intro component
  cases component with
  | obligation =>
      exact (correctedBranchAgreement_iff_hits
        correction obligationBranch).mpr (hhits obligationBranch)
  | repairFrontier atom =>
      cases atom with
      | endpoint =>
          change
            (visibleRouteLeft.repairFrontier CodeAtom.endpoint ↔
              visibleRouteRight.repairFrontier CodeAtom.endpoint)
          dsimp [visibleRouteLeft, visibleRouteRight]
          rw [VisibleRepairTransportCommutator.repairThenTransportPacket_eq_partial,
            VisibleRepairTransportCommutator.transportThenRepairPacket_eq_storageRepair]
          constructor <;> intro hfrontier
          · cases hfrontier
          · rcases hfrontier with ⟨_hsupport, htable⟩
            cases htable
      | storage =>
          exact (correctedBranchAgreement_iff_hits
            correction storageRepairBranch).mpr (hhits storageRepairBranch)
      | worker =>
          change
            (visibleRouteLeft.repairFrontier CodeAtom.worker ↔
              visibleRouteRight.repairFrontier CodeAtom.worker)
          dsimp [visibleRouteLeft, visibleRouteRight]
          rw [VisibleRepairTransportCommutator.repairThenTransportPacket_eq_partial,
            VisibleRepairTransportCommutator.transportThenRepairPacket_eq_storageRepair]
          constructor <;> intro hfrontier
          · cases hfrontier
          · rcases hfrontier with ⟨_hsupport, htable⟩
            cases htable
  | sourceRefTable atom =>
      cases atom with
      | endpoint =>
          change
            visibleRouteLeft.sourceRefTable CodeAtom.endpoint =
              visibleRouteRight.sourceRefTable CodeAtom.endpoint
          dsimp [visibleRouteLeft, visibleRouteRight]
          rw [VisibleRepairTransportCommutator.repairThenTransportPacket_eq_partial,
            VisibleRepairTransportCommutator.transportThenRepairPacket_eq_storageRepair]
          rfl
      | storage =>
          exact (correctedBranchAgreement_iff_hits
            correction storageTableBranch).mpr (hhits storageTableBranch)
      | worker =>
          change
            visibleRouteLeft.sourceRefTable CodeAtom.worker =
              visibleRouteRight.sourceRefTable CodeAtom.worker
          dsimp [visibleRouteLeft, visibleRouteRight]
          rw [VisibleRepairTransportCommutator.repairThenTransportPacket_eq_partial,
            VisibleRepairTransportCommutator.transportThenRepairPacket_eq_storageRepair]
          rfl

/-- Empty protected route support of the corrected route forces every selected branch hit. -/
theorem hits_every_selectedRouteDefectSupport_of_correctedSupportEmpty
    {correction : RouteDefectAtom -> Bool}
    (hempty :
      RouteDefectSupportEmpty
        (correctedVisibleRouteLeft correction) visibleRouteRight) :
    ∀ branch, CorrectionHitsRouteDefectBranch correction branch := by
  intro branch
  exact (correctedBranchAgreement_iff_hits correction branch).mp
    (hempty (routeDefectAtomComponent (routeDefectBranchAtom branch)))

/-- Corrected endpoint route support is empty exactly when every selected branch is hit. -/
theorem correctedVisibleRoute_supportEmpty_iff_hits
    (correction : RouteDefectAtom -> Bool) :
    RouteDefectSupportEmpty
      (correctedVisibleRouteLeft correction) visibleRouteRight ↔
      ∀ branch, CorrectionHitsRouteDefectBranch correction branch := by
  constructor
  · exact hits_every_selectedRouteDefectSupport_of_correctedSupportEmpty
  · exact correctedVisibleRoute_supportEmpty_of_hits

/-! ## Exact visualization restored by all-hit selected correction -/

/--
The corrected endpoint route is source-ref exact exactly when every selected
route-defect branch is hit.
-/
theorem correctedVisibleRoute_exactVisualization_iff_hits
    (correction : RouteDefectAtom -> Bool) :
    SourceRefExactVisualization
      SourceRefTupleBridge.endpointGridCertificate
      SourceRefTupleBridge.endpointGridCertificate
      (correctedVisibleRouteLeft correction) visibleRouteRight ↔
      ∀ branch, CorrectionHitsRouteDefectBranch correction branch := by
  constructor
  · intro hexact
    have hempty :
        RouteDefectSupportEmpty
          (correctedVisibleRouteLeft correction) visibleRouteRight :=
      (exactVisualization_requires_visible_and_emptyRouteSupport
        SourceRefTupleBridge.endpointGridCertificate
        SourceRefTupleBridge.endpointGridCertificate
        hexact).2
    exact hits_every_selectedRouteDefectSupport_of_correctedSupportEmpty hempty
  · intro hhits
    exact visible_and_emptyRouteSupport_suffices_exactVisualization
      SourceRefTupleBridge.endpointGridCertificate
      SourceRefTupleBridge.endpointGridCertificate
      (correctedVisibleRoute_tupleVisible correction)
      (correctedVisibleRoute_supportEmpty_of_hits hhits)

/-- The all-branch correction empties protected route support. -/
theorem allRouteDefectCorrection_supportEmpty :
    RouteDefectSupportEmpty
      (correctedVisibleRouteLeft allRouteDefectCorrection) visibleRouteRight :=
  (correctedVisibleRoute_supportEmpty_iff_hits
    allRouteDefectCorrection).mpr
    allRouteDefectCorrection_hits_every_selectedRouteDefectSupport

/-- The all-branch correction restores source-ref exact visualization. -/
theorem allRouteDefectCorrection_sourceRefExactVisualization :
    SourceRefExactVisualization
      SourceRefTupleBridge.endpointGridCertificate
      SourceRefTupleBridge.endpointGridCertificate
      (correctedVisibleRouteLeft allRouteDefectCorrection) visibleRouteRight :=
  (correctedVisibleRoute_exactVisualization_iff_hits
    allRouteDefectCorrection).mpr
    allRouteDefectCorrection_hits_every_selectedRouteDefectSupport

/-- Obligation-only correction still leaves nonempty protected route support. -/
theorem obligationOnlyCorrection_not_supportEmpty :
    ¬ RouteDefectSupportEmpty
      (correctedVisibleRouteLeft obligationOnlyCorrection) visibleRouteRight := by
  intro hempty
  have hhits :=
    hits_every_selectedRouteDefectSupport_of_correctedSupportEmpty hempty
  exact obligationOnlyCorrection_misses_storageRepair
    (hhits storageRepairBranch)

/-- Obligation-only correction does not restore source-ref exact visualization. -/
theorem obligationOnlyCorrection_not_sourceRefExactVisualization :
    ¬ SourceRefExactVisualization
      SourceRefTupleBridge.endpointGridCertificate
      SourceRefTupleBridge.endpointGridCertificate
      (correctedVisibleRouteLeft obligationOnlyCorrection) visibleRouteRight := by
  intro hexact
  have hempty :
      RouteDefectSupportEmpty
        (correctedVisibleRouteLeft obligationOnlyCorrection) visibleRouteRight :=
    (exactVisualization_requires_visible_and_emptyRouteSupport
      SourceRefTupleBridge.endpointGridCertificate
      SourceRefTupleBridge.endpointGridCertificate
      hexact).2
  exact obligationOnlyCorrection_not_supportEmpty hempty

/-! ## Theorem package -/

/--
Cycle-44 theorem package: all-hit selected correction is equivalent to empty
protected route support and, because the visible tuple surface is fixed, to
source-ref exact visualization of the corrected endpoint route.
-/
theorem selectedRouteCorrectionExactness_package :
    (∀ correction,
      supportSurfaceReading.Equivalent
        (correctedVisibleRouteLeft correction) visibleRouteRight) ∧
    (∀ correction,
      TupleVisibleVisualizationEquivalent
        SourceRefTupleBridge.endpointGridCertificate
        SourceRefTupleBridge.endpointGridCertificate
        (correctedVisibleRouteLeft correction) visibleRouteRight) ∧
    (∀ correction,
      RouteDefectSupportEmpty
        (correctedVisibleRouteLeft correction) visibleRouteRight ↔
        ∀ branch, CorrectionHitsRouteDefectBranch correction branch) ∧
    (∀ correction,
      SourceRefExactVisualization
        SourceRefTupleBridge.endpointGridCertificate
        SourceRefTupleBridge.endpointGridCertificate
        (correctedVisibleRouteLeft correction) visibleRouteRight ↔
        ∀ branch, CorrectionHitsRouteDefectBranch correction branch) ∧
    RouteDefectSupportEmpty
      (correctedVisibleRouteLeft allRouteDefectCorrection) visibleRouteRight ∧
    SourceRefExactVisualization
      SourceRefTupleBridge.endpointGridCertificate
      SourceRefTupleBridge.endpointGridCertificate
      (correctedVisibleRouteLeft allRouteDefectCorrection) visibleRouteRight ∧
    ¬ RouteDefectSupportEmpty
      (correctedVisibleRouteLeft obligationOnlyCorrection) visibleRouteRight ∧
    ¬ SourceRefExactVisualization
      SourceRefTupleBridge.endpointGridCertificate
      SourceRefTupleBridge.endpointGridCertificate
      (correctedVisibleRouteLeft obligationOnlyCorrection) visibleRouteRight := by
  exact ⟨correctedVisibleRoute_supportSurface_equivalent,
    correctedVisibleRoute_tupleVisible,
    correctedVisibleRoute_supportEmpty_iff_hits,
    correctedVisibleRoute_exactVisualization_iff_hits,
    allRouteDefectCorrection_supportEmpty,
    allRouteDefectCorrection_sourceRefExactVisualization,
    obligationOnlyCorrection_not_supportEmpty,
    obligationOnlyCorrection_not_sourceRefExactVisualization⟩

end SelectedRouteCorrectionExactness
end QualitySurface
end ResearchLean.AG
