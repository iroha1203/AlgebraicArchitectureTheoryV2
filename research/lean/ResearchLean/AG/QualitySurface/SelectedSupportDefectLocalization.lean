import ResearchLean.AG.QualitySurface.ParametrizedAtlasTransition

/-!
Cycle 51 evidence for `G-aat-quality-surface-01`.

This file isolates selected support-defect localization as a generic
certificate.  A localization covers every protected route defect by selected
branches; under that cover, empty protected support is equivalent to agreement
on all localized branches, and source-ref exactness is visible flatness plus
localized branch agreement.  The generic criterion is instantiated for the
visible route and for corrected selected routes.

The claim is relative to supplied source-ref packets, selected protected
components, and the explicit source-ref packet bridge.  It does not assert
source extraction completeness, ArchMap correctness, global repair planning,
runtime patch synthesis, or whole-codebase quality.
-/

namespace ResearchLean.AG
namespace QualitySurface
namespace SelectedSupportDefectLocalization

open CodebaseTracePacket
open CodebaseTraceHolonomyPacket
open SourceRefExactVisualizationCriterion
open RouteDefectSupportTheory
open ExactVisualizationCriterionMinimality
open SelectedRouteDefectSupportHitting
open SelectedRouteCorrectionExactness
open SelectedRouteFamilyExactness
open RouteDefectAtom
open RouteDefectBranch
open CorrectedRouteFamilyIndex

/-! ## Generic route support localization -/

/-- A branch localization that covers every protected route defect. -/
structure RouteSupportLocalization
    (left right : SourceRefPacket) where
  Branch : Type
  branchComponent : Branch -> SourceRefPacketProtectedComponent
  covers :
    ∀ component,
      RouteDefectSupport left right component ->
        ∃ branch, branchComponent branch = component

/-- Agreement on every localized branch. -/
def RouteLocalizationBranchesAgree
    {left right : SourceRefPacket}
    (localization : RouteSupportLocalization left right) : Prop :=
  ∀ branch,
    RouteComponentAgreement
      left right (localization.branchComponent branch)

/-- A localized branch carries a protected route defect. -/
def LocalizedBranchDefect
    {left right : SourceRefPacket}
    (localization : RouteSupportLocalization left right)
    (branch : localization.Branch) : Prop :=
  RouteDefectSupport left right (localization.branchComponent branch)

/--
Under a support localization cover, empty protected support is equivalent to
agreement on every localized branch.
-/
theorem routeSupportEmpty_iff_localizedBranches
    {left right : SourceRefPacket}
    (localization : RouteSupportLocalization left right) :
    RouteDefectSupportEmpty left right ↔
      RouteLocalizationBranchesAgree localization := by
  constructor
  · intro hempty branch
    exact hempty (localization.branchComponent branch)
  · intro hagree component
    by_contra hcomponent
    rcases localization.covers component hcomponent with ⟨branch, hbranch⟩
    exact hcomponent (by
      simpa [hbranch] using hagree branch)

/--
With a support localization cover, source-ref exactness is visible flatness plus
agreement on every localized branch.
-/
theorem sourceRefExact_iff_visible_localizedBranches
    {left right : SourceRefPacket}
    (localization : RouteSupportLocalization left right) :
    SourceRefExactVisualization
        SourceRefTupleBridge.endpointGridCertificate
        SourceRefTupleBridge.endpointGridCertificate
        left right ↔
      TupleVisibleVisualizationEquivalent
          SourceRefTupleBridge.endpointGridCertificate
          SourceRefTupleBridge.endpointGridCertificate
          left right ∧
        RouteLocalizationBranchesAgree localization := by
  have hsupport := routeSupportEmpty_iff_localizedBranches localization
  constructor
  · intro hexact
    have hcriterion :=
      (exactVisualization_iff_visible_emptyRouteSupport
        SourceRefTupleBridge.endpointGridCertificate
        SourceRefTupleBridge.endpointGridCertificate
        left right).mp hexact
    exact ⟨hcriterion.1, hsupport.mp hcriterion.2⟩
  · intro hlocalized
    exact (exactVisualization_iff_visible_emptyRouteSupport
      SourceRefTupleBridge.endpointGridCertificate
      SourceRefTupleBridge.endpointGridCertificate
      left right).mpr
      ⟨hlocalized.1, hsupport.mpr hlocalized.2⟩

/-- Any localized branch defect obstructs source-ref exactness. -/
theorem localizedBranchDefect_obstructs_sourceRefExact
    {left right : SourceRefPacket}
    (localization : RouteSupportLocalization left right)
    (branch : localization.Branch)
    (hdefect : LocalizedBranchDefect localization branch) :
    ¬ SourceRefExactVisualization
      SourceRefTupleBridge.endpointGridCertificate
      SourceRefTupleBridge.endpointGridCertificate
      left right := by
  intro hexact
  have hempty :
      RouteDefectSupportEmpty left right :=
    (exactVisualization_requires_visible_and_emptyRouteSupport
      SourceRefTupleBridge.endpointGridCertificate
      SourceRefTupleBridge.endpointGridCertificate
      hexact).2
  exact hdefect (hempty (localization.branchComponent branch))

/-! ## Concrete visible-route localization -/

/-- Selected route-defect branches localize the visible repair/transport route support. -/
def visibleRouteSupportLocalization :
    RouteSupportLocalization visibleRouteLeft visibleRouteRight where
  Branch := RouteDefectBranch
  branchComponent := fun branch =>
    routeDefectAtomComponent (routeDefectBranchAtom branch)
  covers := by
    intro component hdefect
    cases component with
    | obligation =>
        exact ⟨obligationBranch, rfl⟩
    | repairFrontier atom =>
        cases atom with
        | endpoint =>
            exact False.elim
              ((visibleRepairTransport_noRepairFrontierDefect_offStorage
                CodeAtom.endpoint (by intro h; cases h)) hdefect)
        | storage =>
            exact ⟨storageRepairBranch, rfl⟩
        | worker =>
            exact False.elim
              ((visibleRepairTransport_noRepairFrontierDefect_offStorage
                CodeAtom.worker (by intro h; cases h)) hdefect)
    | sourceRefTable atom =>
        cases atom with
        | endpoint =>
            exact False.elim
              ((visibleRepairTransport_noTableDefect_offStorage
                CodeAtom.endpoint (by intro h; cases h)) hdefect)
        | storage =>
            exact ⟨storageTableBranch, rfl⟩
        | worker =>
            exact False.elim
              ((visibleRepairTransport_noTableDefect_offStorage
                CodeAtom.worker (by intro h; cases h)) hdefect)

/-- The visible route source-ref exactness criterion localized to selected branches. -/
theorem visibleRoute_exact_iff_visible_localizedBranches :
    SourceRefExactVisualization
        SourceRefTupleBridge.endpointGridCertificate
        SourceRefTupleBridge.endpointGridCertificate
        visibleRouteLeft visibleRouteRight ↔
      TupleVisibleVisualizationEquivalent
          SourceRefTupleBridge.endpointGridCertificate
          SourceRefTupleBridge.endpointGridCertificate
          visibleRouteLeft visibleRouteRight ∧
        RouteLocalizationBranchesAgree visibleRouteSupportLocalization :=
  sourceRefExact_iff_visible_localizedBranches
    visibleRouteSupportLocalization

/-- The obligation branch is a localized visible-route defect. -/
theorem visibleRoute_obligation_localizedDefect :
    LocalizedBranchDefect
      visibleRouteSupportLocalization obligationBranch :=
  visibleRepairTransport_defectSupport_obligation

/-- The visible route obligation localized defect obstructs source-ref exactness. -/
theorem visibleRoute_obligationDefect_obstructs_sourceRefExact :
    ¬ SourceRefExactVisualization
      SourceRefTupleBridge.endpointGridCertificate
      SourceRefTupleBridge.endpointGridCertificate
      visibleRouteLeft visibleRouteRight :=
  localizedBranchDefect_obstructs_sourceRefExact
    visibleRouteSupportLocalization obligationBranch
    visibleRoute_obligation_localizedDefect

/-! ## Concrete corrected-route localization -/

/-- Selected route-defect branches localize every corrected selected route. -/
def correctedRouteSupportLocalization
    (correction : RouteDefectAtom -> Bool) :
    RouteSupportLocalization
      (correctedVisibleRouteLeft correction) visibleRouteRight where
  Branch := RouteDefectBranch
  branchComponent := fun branch =>
    routeDefectAtomComponent (routeDefectBranchAtom branch)
  covers := by
    intro component hdefect
    simpa [correctedRouteFamilyLeft, correctedRouteFamilyRight,
      correctedRouteFamilyBranchComponent] using
      (correctedRouteFamily_supportLocalized
        correction corrected component hdefect)

/-- Corrected route exactness localized to selected route-defect branches. -/
theorem correctedRoute_exact_iff_visible_localizedBranches
    (correction : RouteDefectAtom -> Bool) :
    SourceRefExactVisualization
        SourceRefTupleBridge.endpointGridCertificate
        SourceRefTupleBridge.endpointGridCertificate
        (correctedVisibleRouteLeft correction) visibleRouteRight ↔
      TupleVisibleVisualizationEquivalent
          SourceRefTupleBridge.endpointGridCertificate
          SourceRefTupleBridge.endpointGridCertificate
          (correctedVisibleRouteLeft correction) visibleRouteRight ∧
        RouteLocalizationBranchesAgree
          (correctedRouteSupportLocalization correction) :=
  sourceRefExact_iff_visible_localizedBranches
    (correctedRouteSupportLocalization correction)

/-- The all-hit correction agrees on every localized selected branch. -/
theorem allRouteDefectCorrection_localizedBranchesAgree :
    RouteLocalizationBranchesAgree
      (correctedRouteSupportLocalization allRouteDefectCorrection) := by
  intro branch
  exact (correctedBranchAgreement_iff_hits
    allRouteDefectCorrection branch).mpr
    (allRouteDefectCorrection_hits_every_selectedRouteDefectSupport branch)

/-- The obligation-only correction has a localized storage-repair defect. -/
theorem obligationOnlyCorrection_storageRepair_localizedDefect :
    LocalizedBranchDefect
      (correctedRouteSupportLocalization obligationOnlyCorrection)
      storageRepairBranch := by
  intro hagree
  exact obligationOnlyCorrection_misses_storageRepair
    ((correctedBranchAgreement_iff_hits
      obligationOnlyCorrection storageRepairBranch).mp hagree)

/-- The localized storage-repair defect obstructs obligation-only exactness. -/
theorem obligationOnlyCorrection_localizedDefect_obstructs_sourceRefExact :
    ¬ SourceRefExactVisualization
      SourceRefTupleBridge.endpointGridCertificate
      SourceRefTupleBridge.endpointGridCertificate
      (correctedVisibleRouteLeft obligationOnlyCorrection) visibleRouteRight :=
  localizedBranchDefect_obstructs_sourceRefExact
    (correctedRouteSupportLocalization obligationOnlyCorrection)
    storageRepairBranch
    obligationOnlyCorrection_storageRepair_localizedDefect

/-! ## Theorem package -/

/--
Cycle-51 theorem package: selected support-defect localization gives a generic
route-level exactness criterion and branch-defect obstruction theorem, with
visible-route and corrected-route concrete instances.
-/
theorem selectedSupportDefectLocalization_package :
    (∀ {left right : SourceRefPacket}
      (localization : RouteSupportLocalization left right),
      RouteDefectSupportEmpty left right ↔
        RouteLocalizationBranchesAgree localization) ∧
    (∀ {left right : SourceRefPacket}
      (localization : RouteSupportLocalization left right),
      SourceRefExactVisualization
          SourceRefTupleBridge.endpointGridCertificate
          SourceRefTupleBridge.endpointGridCertificate
          left right ↔
        TupleVisibleVisualizationEquivalent
            SourceRefTupleBridge.endpointGridCertificate
            SourceRefTupleBridge.endpointGridCertificate
            left right ∧
          RouteLocalizationBranchesAgree localization) ∧
    (∀ {left right : SourceRefPacket}
      (localization : RouteSupportLocalization left right)
      (branch : localization.Branch),
      LocalizedBranchDefect localization branch ->
        ¬ SourceRefExactVisualization
          SourceRefTupleBridge.endpointGridCertificate
          SourceRefTupleBridge.endpointGridCertificate
          left right) ∧
    (SourceRefExactVisualization
        SourceRefTupleBridge.endpointGridCertificate
        SourceRefTupleBridge.endpointGridCertificate
        visibleRouteLeft visibleRouteRight ↔
      TupleVisibleVisualizationEquivalent
          SourceRefTupleBridge.endpointGridCertificate
          SourceRefTupleBridge.endpointGridCertificate
          visibleRouteLeft visibleRouteRight ∧
        RouteLocalizationBranchesAgree visibleRouteSupportLocalization) ∧
    LocalizedBranchDefect
      visibleRouteSupportLocalization obligationBranch ∧
    ¬ SourceRefExactVisualization
      SourceRefTupleBridge.endpointGridCertificate
      SourceRefTupleBridge.endpointGridCertificate
      visibleRouteLeft visibleRouteRight ∧
    (∀ correction,
      (SourceRefExactVisualization
          SourceRefTupleBridge.endpointGridCertificate
          SourceRefTupleBridge.endpointGridCertificate
          (correctedVisibleRouteLeft correction) visibleRouteRight ↔
        TupleVisibleVisualizationEquivalent
            SourceRefTupleBridge.endpointGridCertificate
            SourceRefTupleBridge.endpointGridCertificate
            (correctedVisibleRouteLeft correction) visibleRouteRight ∧
          RouteLocalizationBranchesAgree
            (correctedRouteSupportLocalization correction))) ∧
    RouteLocalizationBranchesAgree
      (correctedRouteSupportLocalization allRouteDefectCorrection) ∧
    LocalizedBranchDefect
      (correctedRouteSupportLocalization obligationOnlyCorrection)
      storageRepairBranch ∧
    ¬ SourceRefExactVisualization
      SourceRefTupleBridge.endpointGridCertificate
      SourceRefTupleBridge.endpointGridCertificate
      (correctedVisibleRouteLeft obligationOnlyCorrection) visibleRouteRight := by
  exact ⟨routeSupportEmpty_iff_localizedBranches,
    sourceRefExact_iff_visible_localizedBranches,
    fun localization branch hdefect =>
      localizedBranchDefect_obstructs_sourceRefExact
        localization branch hdefect,
    visibleRoute_exact_iff_visible_localizedBranches,
    visibleRoute_obligation_localizedDefect,
    visibleRoute_obligationDefect_obstructs_sourceRefExact,
    correctedRoute_exact_iff_visible_localizedBranches,
    allRouteDefectCorrection_localizedBranchesAgree,
    obligationOnlyCorrection_storageRepair_localizedDefect,
    obligationOnlyCorrection_localizedDefect_obstructs_sourceRefExact⟩

end SelectedSupportDefectLocalization
end QualitySurface
end ResearchLean.AG
