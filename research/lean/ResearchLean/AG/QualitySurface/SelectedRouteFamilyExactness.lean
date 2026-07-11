import ResearchLean.AG.QualitySurface.LossAwareCommutatorAtlas

/-!
Cycle 47 evidence for `G-aat-quality-surface-01`.

This file lifts the selected route exactness criterion from a single endpoint
route to a finite selected route family.  A family is source-ref exact exactly
when every member is visibly flat and has empty protected route support.  If a
selected branch localization covers every protected route defect, then family
exactness is equivalent to visible flatness plus agreement on all localized
branches.

The claim is relative to supplied finite source-ref route families, selected
branch localization covers, and the explicit packet-to-tuple bridge.  It does
not assert complete diagnostic coverage for all codebases, ArchMap correctness,
source extraction completeness, global repair planning, or whole-codebase
quality.
-/

namespace ResearchLean.AG
namespace QualitySurface
namespace SelectedRouteFamilyExactness

open CodebaseTracePacket
open CodebaseTraceHolonomyPacket
open SourceRefExactVisualizationCriterion
open RouteDefectSupportTheory
open ExactVisualizationCriterionMinimality
open SelectedRouteDefectSupportHitting
open RouteDefectBranch
open SelectedRouteCorrectionExactness
open LossAwareCommutatorAtlas
open LossAwareAtlasCell

universe u v

/-! ## Family-level exactness criteria -/

/-- Visible tuple flatness for every route in a selected family. -/
def FamilyVisibleTupleFlat {ι : Type u}
    (left right : ι -> SourceRefPacket) : Prop :=
  ∀ index,
    TupleVisibleVisualizationEquivalent
      SourceRefTupleBridge.endpointGridCertificate
      SourceRefTupleBridge.endpointGridCertificate
      (left index) (right index)

/-- Empty protected route support for every route in a selected family. -/
def FamilyProtectedRouteSupportEmpty {ι : Type u}
    (left right : ι -> SourceRefPacket) : Prop :=
  ∀ index, RouteDefectSupportEmpty (left index) (right index)

/-- Source-ref exact visualization for every route in a selected family. -/
def FamilySourceRefExact {ι : Type u}
    (left right : ι -> SourceRefPacket) : Prop :=
  ∀ index,
    SourceRefExactVisualization
      SourceRefTupleBridge.endpointGridCertificate
      SourceRefTupleBridge.endpointGridCertificate
      (left index) (right index)

/--
Family-level source-ref exactness is exactly visible flatness plus empty
protected route support at every selected route.
-/
theorem familySourceRefExact_iff_visible_empty {ι : Type u}
    (left right : ι -> SourceRefPacket) :
    FamilySourceRefExact left right ↔
      FamilyVisibleTupleFlat left right ∧
        FamilyProtectedRouteSupportEmpty left right := by
  constructor
  · intro hexact
    exact ⟨fun index =>
        ((exactVisualization_iff_visible_emptyRouteSupport
          SourceRefTupleBridge.endpointGridCertificate
          SourceRefTupleBridge.endpointGridCertificate
          (left index) (right index)).mp (hexact index)).1,
      fun index =>
        ((exactVisualization_iff_visible_emptyRouteSupport
          SourceRefTupleBridge.endpointGridCertificate
          SourceRefTupleBridge.endpointGridCertificate
          (left index) (right index)).mp (hexact index)).2⟩
  · intro hvisibleEmpty index
    exact (exactVisualization_iff_visible_emptyRouteSupport
      SourceRefTupleBridge.endpointGridCertificate
      SourceRefTupleBridge.endpointGridCertificate
      (left index) (right index)).mpr
      ⟨hvisibleEmpty.1 index, hvisibleEmpty.2 index⟩

/-! ## Localized branch covers -/

/-- Agreement on all localized protected branches of a selected route family. -/
def FamilyLocalizedBranchesAgree {ι : Type u}
    (left right : ι -> SourceRefPacket)
    {Branch : ι -> Type v}
    (branchComponent :
      ∀ index, Branch index ->
        CodebaseTraceHolonomyPacket.SourceRefPacketProtectedComponent) :
    Prop :=
  ∀ index branch,
    RouteComponentAgreement
      (left index) (right index) (branchComponent index branch)

/--
A selected branch localization covers all protected route defects in the
family.
-/
def FamilySupportLocalized {ι : Type u}
    (left right : ι -> SourceRefPacket)
    {Branch : ι -> Type v}
    (branchComponent :
      ∀ index, Branch index ->
        CodebaseTraceHolonomyPacket.SourceRefPacketProtectedComponent) :
    Prop :=
  ∀ index component,
    RouteDefectSupport (left index) (right index) component ->
      ∃ branch, branchComponent index branch = component

/--
If localized branches cover all protected defects, then empty protected support
is equivalent to agreement on every localized branch.
-/
theorem familyProtectedSupportEmpty_iff_localizedBranches {ι : Type u}
    {Branch : ι -> Type v}
    (left right : ι -> SourceRefPacket)
    (branchComponent :
      ∀ index, Branch index ->
        CodebaseTraceHolonomyPacket.SourceRefPacketProtectedComponent)
    (hlocalized : FamilySupportLocalized left right branchComponent) :
    FamilyProtectedRouteSupportEmpty left right ↔
      FamilyLocalizedBranchesAgree left right branchComponent := by
  constructor
  · intro hempty index branch
    exact hempty index (branchComponent index branch)
  · intro hagree index component
    by_contra hcomponent
    rcases hlocalized index component hcomponent with ⟨branch, hbranch⟩
    exact hcomponent (by
      simpa [hbranch] using hagree index branch)

/--
With a selected branch localization cover, family source-ref exactness is
equivalent to visible flatness plus agreement on all localized branches.
-/
theorem familySourceRefExact_iff_visible_localizedBranches {ι : Type u}
    {Branch : ι -> Type v}
    (left right : ι -> SourceRefPacket)
    (branchComponent :
      ∀ index, Branch index ->
        CodebaseTraceHolonomyPacket.SourceRefPacketProtectedComponent)
    (hlocalized : FamilySupportLocalized left right branchComponent) :
    FamilySourceRefExact left right ↔
      FamilyVisibleTupleFlat left right ∧
        FamilyLocalizedBranchesAgree left right branchComponent := by
  have hsupport :=
    familyProtectedSupportEmpty_iff_localizedBranches
      left right branchComponent hlocalized
  constructor
  · intro hexact
    have hcriterion :=
      (familySourceRefExact_iff_visible_empty left right).mp hexact
    exact ⟨hcriterion.1, hsupport.mp hcriterion.2⟩
  · intro hlocalizedExact
    exact (familySourceRefExact_iff_visible_empty left right).mpr
      ⟨hlocalizedExact.1, hsupport.mpr hlocalizedExact.2⟩

/-! ## Loss-aware atlas as a selected route family -/

/-- Left endpoint packet of a loss-aware atlas cell. -/
def lossAwareAtlasLeft : LossAwareAtlasCell -> SourceRefPacket
  | visibleLawDeletionCell =>
      VisibleLawDeletionProtectedZero.visibleLawRoute_repairThenTransportPacket
  | tableLawDeletionCell => tableRouteLeft
  | visibleRepairTransportCell => visibleRouteLeft
  | allHitCorrectionCell =>
      correctedVisibleRouteLeft allRouteDefectCorrection
  | obligationOnlyCorrectionCell =>
      correctedVisibleRouteLeft obligationOnlyCorrection

/-- Right endpoint packet of a loss-aware atlas cell. -/
def lossAwareAtlasRight : LossAwareAtlasCell -> SourceRefPacket
  | visibleLawDeletionCell =>
      VisibleLawDeletionProtectedZero.visibleLawRoute_transportThenRepairPacket
  | tableLawDeletionCell => tableRouteRight
  | visibleRepairTransportCell => visibleRouteRight
  | allHitCorrectionCell => visibleRouteRight
  | obligationOnlyCorrectionCell => visibleRouteRight

/--
The loss-aware atlas instantiates the family-level exactness criterion.
-/
theorem lossAwareAtlas_familyCriterion :
    (∀ cell, CellSourceRefExact cell) ↔
      (∀ cell, CellVisibleTupleFlat cell) ∧
        (∀ cell, CellProtectedRouteSupportEmpty cell) := by
  constructor
  · intro hexact
    exact ⟨fun cell =>
        ((atlasCell_exact_iff_visible_empty cell).mp (hexact cell)).1,
      fun cell =>
        ((atlasCell_exact_iff_visible_empty cell).mp (hexact cell)).2⟩
  · intro hvisibleEmpty cell
    exact (atlasCell_exact_iff_visible_empty cell).mpr
      ⟨hvisibleEmpty.1 cell, hvisibleEmpty.2 cell⟩

/-- The full loss-aware atlas is not entirely source-ref exact. -/
theorem lossAwareAtlas_not_familySourceRefExact :
    ¬ FamilySourceRefExact lossAwareAtlasLeft lossAwareAtlasRight := by
  intro hfamily
  exact VisibleLawDeletionProtectedZero.visibleLawRoute_not_sourceRefExactVisualization
    (hfamily visibleLawDeletionCell)

/-! ## A positive exact-restoration subfamily -/

/-- A singleton family containing only the all-hit exact restoration route. -/
inductive ExactRestorationSubfamilyIndex where
  | restored
  deriving DecidableEq, Fintype

open ExactRestorationSubfamilyIndex

/-- Left endpoint of the exact-restoration singleton family. -/
def exactRestorationSubfamilyLeft :
    ExactRestorationSubfamilyIndex -> SourceRefPacket
  | restored => correctedVisibleRouteLeft allRouteDefectCorrection

/-- Right endpoint of the exact-restoration singleton family. -/
def exactRestorationSubfamilyRight :
    ExactRestorationSubfamilyIndex -> SourceRefPacket
  | restored => visibleRouteRight

/-- The all-hit singleton subfamily is source-ref exact. -/
theorem exactRestorationSubfamily_sourceRefExact :
    FamilySourceRefExact
      exactRestorationSubfamilyLeft exactRestorationSubfamilyRight := by
  intro index
  cases index
  exact allRouteDefectCorrection_sourceRefExactVisualization

/-! ## Concrete selected correction family with a localization cover -/

/-- A singleton family containing one corrected selected route. -/
inductive CorrectedRouteFamilyIndex where
  | corrected
  deriving DecidableEq, Fintype

open CorrectedRouteFamilyIndex

/-- Left endpoint of a singleton corrected route family. -/
def correctedRouteFamilyLeft
    (correction : RouteDefectAtom -> Bool) :
    CorrectedRouteFamilyIndex -> SourceRefPacket
  | corrected => correctedVisibleRouteLeft correction

/-- Right endpoint of a singleton corrected route family. -/
def correctedRouteFamilyRight :
    CorrectedRouteFamilyIndex -> SourceRefPacket
  | corrected => visibleRouteRight

/-- Selected branch component used to localize the corrected route family. -/
def correctedRouteFamilyBranchComponent
    (_index : CorrectedRouteFamilyIndex)
    (branch : RouteDefectBranch) :
    CodebaseTraceHolonomyPacket.SourceRefPacketProtectedComponent :=
  routeDefectAtomComponent (routeDefectBranchAtom branch)

/--
The selected route-defect branches cover every protected defect of the corrected
route family.  Off-selected repair-frontier and source-ref table coordinates are
flat by the selected route support computation.
-/
theorem correctedRouteFamily_supportLocalized
    (correction : RouteDefectAtom -> Bool) :
    FamilySupportLocalized
      (correctedRouteFamilyLeft correction)
      correctedRouteFamilyRight
      correctedRouteFamilyBranchComponent := by
  intro index component hdefect
  cases index
  cases component with
  | obligation =>
      exact ⟨obligationBranch, rfl⟩
  | repairFrontier atom =>
      cases atom with
      | endpoint =>
          have hagree :
              RouteComponentAgreement
                (correctedVisibleRouteLeft correction) visibleRouteRight
                (SourceRefPacketProtectedComponent.repairFrontier CodeAtom.endpoint) := by
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
          exact False.elim (hdefect hagree)
      | storage =>
          exact ⟨storageRepairBranch, rfl⟩
      | worker =>
          have hagree :
              RouteComponentAgreement
                (correctedVisibleRouteLeft correction) visibleRouteRight
                (SourceRefPacketProtectedComponent.repairFrontier CodeAtom.worker) := by
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
          exact False.elim (hdefect hagree)
  | sourceRefTable atom =>
      cases atom with
      | endpoint =>
          have hagree :
              RouteComponentAgreement
                (correctedVisibleRouteLeft correction) visibleRouteRight
                (SourceRefPacketProtectedComponent.sourceRefTable CodeAtom.endpoint) := by
            change
              visibleRouteLeft.sourceRefTable CodeAtom.endpoint =
                visibleRouteRight.sourceRefTable CodeAtom.endpoint
            dsimp [visibleRouteLeft, visibleRouteRight]
            rw [VisibleRepairTransportCommutator.repairThenTransportPacket_eq_partial,
              VisibleRepairTransportCommutator.transportThenRepairPacket_eq_storageRepair]
            rfl
          exact False.elim (hdefect hagree)
      | storage =>
          exact ⟨storageTableBranch, rfl⟩
      | worker =>
          have hagree :
              RouteComponentAgreement
                (correctedVisibleRouteLeft correction) visibleRouteRight
                (SourceRefPacketProtectedComponent.sourceRefTable CodeAtom.worker) := by
            change
              visibleRouteLeft.sourceRefTable CodeAtom.worker =
                visibleRouteRight.sourceRefTable CodeAtom.worker
            dsimp [visibleRouteLeft, visibleRouteRight]
            rw [VisibleRepairTransportCommutator.repairThenTransportPacket_eq_partial,
              VisibleRepairTransportCommutator.transportThenRepairPacket_eq_storageRepair]
            rfl
          exact False.elim (hdefect hagree)

/--
For the concrete selected correction family, source-ref exactness is equivalent
to visible flatness plus agreement on all selected localized branches.
-/
theorem correctedRouteFamily_exact_iff_visible_localizedBranches
    (correction : RouteDefectAtom -> Bool) :
    FamilySourceRefExact
        (correctedRouteFamilyLeft correction) correctedRouteFamilyRight ↔
      FamilyVisibleTupleFlat
          (correctedRouteFamilyLeft correction) correctedRouteFamilyRight ∧
        FamilyLocalizedBranchesAgree
          (correctedRouteFamilyLeft correction)
          correctedRouteFamilyRight
          correctedRouteFamilyBranchComponent :=
  familySourceRefExact_iff_visible_localizedBranches
    (correctedRouteFamilyLeft correction)
    correctedRouteFamilyRight
    correctedRouteFamilyBranchComponent
    (correctedRouteFamily_supportLocalized correction)

/-- The all-hit correction gives an exact concrete selected correction family. -/
theorem allRouteDefectCorrection_familySourceRefExact :
    FamilySourceRefExact
      (correctedRouteFamilyLeft allRouteDefectCorrection)
      correctedRouteFamilyRight := by
  intro index
  cases index
  exact allRouteDefectCorrection_sourceRefExactVisualization

/-- Obligation-only correction leaves the concrete selected correction family non-exact. -/
theorem obligationOnlyCorrection_family_not_sourceRefExact :
    ¬ FamilySourceRefExact
      (correctedRouteFamilyLeft obligationOnlyCorrection)
      correctedRouteFamilyRight := by
  intro hfamily
  exact obligationOnlyCorrection_not_sourceRefExactVisualization
    (hfamily corrected)

/-! ## Theorem package -/

/--
Cycle-47 theorem package: selected route family exactness is pointwise visible
flatness plus empty protected support; with a localized branch cover, empty
support can be read as agreement on all localized branches.  The loss-aware
atlas is an instance of the criterion and contains both a non-exact full family
and an exact all-hit singleton subfamily.
-/
theorem selectedRouteFamilyExactness_package :
    (∀ {ι : Type u} (left right : ι -> SourceRefPacket),
      FamilySourceRefExact left right ↔
        FamilyVisibleTupleFlat left right ∧
          FamilyProtectedRouteSupportEmpty left right) ∧
    (∀ {ι : Type u} {Branch : ι -> Type v}
      (left right : ι -> SourceRefPacket)
      (branchComponent :
        ∀ index, Branch index ->
          CodebaseTraceHolonomyPacket.SourceRefPacketProtectedComponent),
      FamilySupportLocalized left right branchComponent ->
        (FamilySourceRefExact left right ↔
          FamilyVisibleTupleFlat left right ∧
            FamilyLocalizedBranchesAgree left right branchComponent)) ∧
    ((∀ cell, CellSourceRefExact cell) ↔
      (∀ cell, CellVisibleTupleFlat cell) ∧
        (∀ cell, CellProtectedRouteSupportEmpty cell)) ∧
    ¬ FamilySourceRefExact lossAwareAtlasLeft lossAwareAtlasRight ∧
    FamilySourceRefExact
      exactRestorationSubfamilyLeft exactRestorationSubfamilyRight ∧
    (∀ correction,
      FamilySupportLocalized
        (correctedRouteFamilyLeft correction)
        correctedRouteFamilyRight
        correctedRouteFamilyBranchComponent) ∧
    (∀ correction,
      FamilySourceRefExact
          (correctedRouteFamilyLeft correction) correctedRouteFamilyRight ↔
        FamilyVisibleTupleFlat
            (correctedRouteFamilyLeft correction) correctedRouteFamilyRight ∧
          FamilyLocalizedBranchesAgree
            (correctedRouteFamilyLeft correction)
            correctedRouteFamilyRight
            correctedRouteFamilyBranchComponent) ∧
    FamilySourceRefExact
      (correctedRouteFamilyLeft allRouteDefectCorrection)
      correctedRouteFamilyRight ∧
    ¬ FamilySourceRefExact
      (correctedRouteFamilyLeft obligationOnlyCorrection)
      correctedRouteFamilyRight := by
  exact ⟨familySourceRefExact_iff_visible_empty,
    fun left right branchComponent hlocalized =>
      familySourceRefExact_iff_visible_localizedBranches
        left right branchComponent hlocalized,
    lossAwareAtlas_familyCriterion,
    lossAwareAtlas_not_familySourceRefExact,
    exactRestorationSubfamily_sourceRefExact,
    correctedRouteFamily_supportLocalized,
    correctedRouteFamily_exact_iff_visible_localizedBranches,
    allRouteDefectCorrection_familySourceRefExact,
    obligationOnlyCorrection_family_not_sourceRefExact⟩

end SelectedRouteFamilyExactness
end QualitySurface
end ResearchLean.AG
