import ResearchLean.AG.QualitySurface.SupportHitting
import ResearchLean.AG.QualitySurface.SelectedRouteCorrectionExactness

/-!
Cycle 46 evidence for `G-aat-quality-surface-01`.

This file bridges the abstract local repair support calculus from Cycle 1 with
the selected route-defect correction theorem from Cycles 43/44.  The selected
route defect is read as a singleton support family in `LocalRepairSupportCalculus`;
under that reading, local support elimination, selected branch hitting, packet
correction elimination, and source-ref exact visualization restoration agree.

The claim is relative to the supplied finite source-ref endpoint route, selected
route-defect atom/branch vocabulary, selected correction semantics, and explicit
packet-to-tuple bridge.  It does not assert global repair planning, canonical
runtime patches, source extraction completeness, ArchMap correctness, or
whole-codebase quality.
-/

namespace ResearchLean.AG
namespace QualitySurface
namespace RouteDefectLocalRepairCalculusBridge

open CodebaseTracePacket
open SourceRefExactVisualizationCriterion
open RouteDefectSupportTheory
open SelectedRouteDefectSupportHitting
open SelectedRouteCorrectionExactness
open RouteDefectAtom
open RouteDefectBranch

/-! ## Selected route defect as a local repair support calculus -/

/-- The selected route defect obstruction class used by the bridge. -/
inductive SelectedRouteObstruction where
  | visibleRouteDefect
  deriving DecidableEq

open SelectedRouteObstruction

/-- Singleton support carried by a selected route-defect branch. -/
def branchSingletonSupport (branch : RouteDefectBranch) : Set RouteDefectAtom :=
  fun atom => atom = routeDefectBranchAtom branch

/-- The selected minimal support family for the visible route defect. -/
def selectedRouteMinSupport :
    SelectedRouteObstruction -> Set (Set RouteDefectAtom)
  | visibleRouteDefect =>
      fun support => ∃ branch, support = branchSingletonSupport branch

/-- A selected support remains after a local repair exactly when the repair misses it. -/
def selectedRouteAfterRepair
    (repairSupport : Set RouteDefectAtom)
    (obstruction : SelectedRouteObstruction) :
    Set (Set RouteDefectAtom) :=
  fun support =>
    selectedRouteMinSupport obstruction support ∧
      SupportDisjoint repairSupport support

/-- Local support elimination means no selected support remains after repair. -/
def selectedRouteEliminates
    (repairSupport : Set RouteDefectAtom)
    (obstruction : SelectedRouteObstruction) : Prop :=
  ∀ support, ¬ selectedRouteAfterRepair repairSupport obstruction support

/-- The selected route support family is nonempty. -/
theorem selectedRouteMinSupport_nonempty :
    ∀ obstruction : SelectedRouteObstruction,
      ∃ support : Set RouteDefectAtom,
        selectedRouteMinSupport obstruction support := by
  intro obstruction
  cases obstruction
  exact ⟨branchSingletonSupport obligationBranch, ⟨obligationBranch, rfl⟩⟩

/-- Singleton selected branch supports form an antichain. -/
theorem selectedRouteMinSupport_antichain
    {obstruction : SelectedRouteObstruction}
    {left right : Set RouteDefectAtom}
    (hleft : selectedRouteMinSupport obstruction left)
    (hright : selectedRouteMinSupport obstruction right)
    (hsub : ∀ atom, atom ∈ left -> atom ∈ right) :
    ∀ atom, atom ∈ right -> atom ∈ left := by
  cases obstruction
  rcases hleft with ⟨leftBranch, rfl⟩
  rcases hright with ⟨rightBranch, rfl⟩
  have hbranch :
      routeDefectBranchAtom leftBranch =
        routeDefectBranchAtom rightBranch := by
    exact hsub (routeDefectBranchAtom leftBranch) rfl
  intro atom hrightAtom
  exact hrightAtom.trans hbranch.symm

/-- The selected route defect is an instance of the generic local repair support calculus. -/
def selectedRouteLocalRepairCalculus :
    LocalRepairSupportCalculus RouteDefectAtom SelectedRouteObstruction where
  MinSupportFamily := selectedRouteMinSupport
  AfterRepairFamily := selectedRouteAfterRepair
  Eliminates := selectedRouteEliminates
  minSupportFamilyNonempty := selectedRouteMinSupport_nonempty
  minSupportFamilyAntichain := by
    intro obstruction left right hleft hright hsub
    exact selectedRouteMinSupport_antichain hleft hright hsub
  repairLocalOutside := by
    intro repairSupport obstruction support hsupport hmiss
    exact ⟨hsupport, hmiss⟩
  eliminates_no_afterSupport := by
    intro repairSupport obstruction support helim hafter
    exact helim support hafter

/-! ## Correction support and branch hitting -/

/-- The support touched by a selected route-defect correction. -/
def routeCorrectionSupport
    (correction : RouteDefectAtom -> Bool) : Set RouteDefectAtom :=
  fun atom => correction atom = true

/-- Support-level hitting of a singleton selected branch is exactly branch hitting. -/
theorem routeCorrectionSupport_hits_branch_iff
    (correction : RouteDefectAtom -> Bool)
    (branch : RouteDefectBranch) :
    SupportHits (routeCorrectionSupport correction)
      (branchSingletonSupport branch) ↔
      CorrectionHitsRouteDefectBranch correction branch := by
  constructor
  · intro hhit
    rcases hhit with ⟨atom, hrepair, hbranch⟩
    subst atom
    simpa [routeCorrectionSupport, CorrectionHitsRouteDefectBranch]
      using hrepair
  · intro hhit
    exact ⟨routeDefectBranchAtom branch,
      by
        simpa [routeCorrectionSupport, CorrectionHitsRouteDefectBranch]
          using hhit,
      rfl⟩

/--
Local support elimination in the selected route calculus is equivalent to
hitting every selected branch.
-/
theorem selectedRouteLocalRepair_eliminates_iff_hits
    (repairSupport : Set RouteDefectAtom) :
    selectedRouteLocalRepairCalculus.Eliminates
        repairSupport visibleRouteDefect ↔
      ∀ branch, SupportHits repairSupport (branchSingletonSupport branch) := by
  constructor
  · intro helim branch
    exact hits_every_minSupport_of_eliminates
      selectedRouteLocalRepairCalculus helim
      (branchSingletonSupport branch) ⟨branch, rfl⟩
  · intro hhits support hafter
    rcases hafter.1 with ⟨branch, rfl⟩
    rcases hhits branch with ⟨atom, hrepair, hbranch⟩
    exact hafter.2 atom hrepair hbranch

/--
For selected packet corrections, support-calculus elimination is equivalent to
packet-level elimination of the selected route defect.
-/
theorem sourceRefRouteCorrection_supportEliminates_iff_packetEliminates
    (correction : RouteDefectAtom -> Bool) :
    selectedRouteLocalRepairCalculus.Eliminates
        (routeCorrectionSupport correction) visibleRouteDefect ↔
      SourceRefRouteCorrectionEliminates correction := by
  constructor
  · intro helim branch
    have hhit : CorrectionHitsRouteDefectBranch correction branch :=
      (routeCorrectionSupport_hits_branch_iff correction branch).mp
      ((selectedRouteLocalRepair_eliminates_iff_hits
        (routeCorrectionSupport correction)).mp helim branch)
    exact (correctedBranchAgreement_iff_hits correction branch).mpr hhit
  · intro helim
    exact (selectedRouteLocalRepair_eliminates_iff_hits
      (routeCorrectionSupport correction)).mpr
      (fun branch =>
        (routeCorrectionSupport_hits_branch_iff correction branch).mpr
          ((sourceRefRouteCorrection_eliminates_iff_hits correction).mp
            helim branch))

/-! ## Exact visualization through local support elimination -/

/--
Corrected route source-ref exactness is equivalent to local repair support
elimination in the selected route calculus.
-/
theorem correctedRoute_exactVisualization_iff_localRepairEliminates
    (correction : RouteDefectAtom -> Bool) :
    SourceRefExactVisualization
        SourceRefTupleBridge.endpointGridCertificate
        SourceRefTupleBridge.endpointGridCertificate
        (correctedVisibleRouteLeft correction) visibleRouteRight ↔
      selectedRouteLocalRepairCalculus.Eliminates
        (routeCorrectionSupport correction) visibleRouteDefect := by
  constructor
  · intro hexact
    exact (selectedRouteLocalRepair_eliminates_iff_hits
      (routeCorrectionSupport correction)).mpr
      (fun branch =>
        (routeCorrectionSupport_hits_branch_iff correction branch).mpr
          ((correctedVisibleRoute_exactVisualization_iff_hits correction).mp
            hexact branch))
  · intro helim
    exact (correctedVisibleRoute_exactVisualization_iff_hits correction).mpr
      (fun branch =>
        (routeCorrectionSupport_hits_branch_iff correction branch).mp
          ((selectedRouteLocalRepair_eliminates_iff_hits
            (routeCorrectionSupport correction)).mp helim branch))

/-- A missed selected support obstructs source-ref exact visualization. -/
theorem missedRouteBranch_obstructs_exactVisualization
    (correction : RouteDefectAtom -> Bool)
    (branch : RouteDefectBranch)
    (hmiss : ¬ CorrectionHitsRouteDefectBranch correction branch) :
    ¬ SourceRefExactVisualization
      SourceRefTupleBridge.endpointGridCertificate
      SourceRefTupleBridge.endpointGridCertificate
      (correctedVisibleRouteLeft correction) visibleRouteRight := by
  have hdisjoint :
      SupportDisjoint
        (routeCorrectionSupport correction)
        (branchSingletonSupport branch) := by
    intro atom hrepair hbranch
    exact hmiss
      ((routeCorrectionSupport_hits_branch_iff correction branch).mp
        ⟨atom, hrepair, hbranch⟩)
  intro hexact
  have helim :=
    (correctedRoute_exactVisualization_iff_localRepairEliminates
      correction).mp hexact
  exact (missed_minSupport_survives
    selectedRouteLocalRepairCalculus
    (M := branchSingletonSupport branch)
    ⟨branch, rfl⟩ hdisjoint) helim

/-- All-branch correction eliminates the selected route defect in the local support calculus. -/
theorem allRouteDefectCorrection_localRepairEliminates :
    selectedRouteLocalRepairCalculus.Eliminates
      (routeCorrectionSupport allRouteDefectCorrection) visibleRouteDefect :=
  (correctedRoute_exactVisualization_iff_localRepairEliminates
    allRouteDefectCorrection).mp
    allRouteDefectCorrection_sourceRefExactVisualization

/-! ## Theorem package -/

/--
Cycle-46 theorem package: selected route correction is an instance of local
repair support calculus, and local support elimination is equivalent to
packet-level elimination and source-ref exact visualization restoration.
-/
theorem routeDefectLocalRepairCalculusBridge_package :
    (∀ branch,
      selectedRouteMinSupport visibleRouteDefect
        (branchSingletonSupport branch)) ∧
    (∀ correction branch,
      SupportHits (routeCorrectionSupport correction)
          (branchSingletonSupport branch) ↔
        CorrectionHitsRouteDefectBranch correction branch) ∧
    (∀ repairSupport,
      selectedRouteLocalRepairCalculus.Eliminates
          repairSupport visibleRouteDefect ↔
        ∀ branch, SupportHits repairSupport
          (branchSingletonSupport branch)) ∧
    (∀ correction,
      selectedRouteLocalRepairCalculus.Eliminates
          (routeCorrectionSupport correction) visibleRouteDefect ↔
        SourceRefRouteCorrectionEliminates correction) ∧
    (∀ correction,
      SourceRefExactVisualization
          SourceRefTupleBridge.endpointGridCertificate
          SourceRefTupleBridge.endpointGridCertificate
          (correctedVisibleRouteLeft correction) visibleRouteRight ↔
        selectedRouteLocalRepairCalculus.Eliminates
          (routeCorrectionSupport correction) visibleRouteDefect) ∧
    (∀ correction branch,
      ¬ CorrectionHitsRouteDefectBranch correction branch ->
        ¬ SourceRefExactVisualization
          SourceRefTupleBridge.endpointGridCertificate
          SourceRefTupleBridge.endpointGridCertificate
          (correctedVisibleRouteLeft correction) visibleRouteRight) ∧
    selectedRouteLocalRepairCalculus.Eliminates
      (routeCorrectionSupport allRouteDefectCorrection) visibleRouteDefect := by
  exact ⟨fun branch => ⟨branch, rfl⟩,
    routeCorrectionSupport_hits_branch_iff,
    selectedRouteLocalRepair_eliminates_iff_hits,
    sourceRefRouteCorrection_supportEliminates_iff_packetEliminates,
    correctedRoute_exactVisualization_iff_localRepairEliminates,
    missedRouteBranch_obstructs_exactVisualization,
    allRouteDefectCorrection_localRepairEliminates⟩

end RouteDefectLocalRepairCalculusBridge
end QualitySurface
end ResearchLean.AG
