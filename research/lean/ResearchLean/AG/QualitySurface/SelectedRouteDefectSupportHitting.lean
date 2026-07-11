import ResearchLean.AG.QualitySurface.RouteDefectSupport

/-!
Cycle 43 evidence for `G-aat-quality-surface-01`.

This file turns the selected endpoint route defect support from Cycle 38 into a
finite hitting calculus.  For the visible-flat repair/transport commutator from
Cycle 28, the protected endpoint defects are exactly the obligation, storage
repair-frontier, and storage source-ref table coordinates.  We read those
coordinates as a selected minimal route-defect support family and prove that an
selected protected-component correction must hit every selected branch.

The claim is relative to supplied finite source-ref packets, selected route
endpoints, and a selected defect-support atom vocabulary.  It does not assert a
global correction planner, canonical repair, source extraction completeness,
ArchMap correctness, or whole-codebase quality.
-/

namespace ResearchLean.AG
namespace QualitySurface
namespace SelectedRouteDefectSupportHitting

open CodebaseTracePacket
open CodebaseTraceHolonomyPacket
open RouteDefectSupportTheory

/-! ## Selected endpoint route-defect atoms -/

/-- Selected protected coordinates used to detect the visible-flat route defect. -/
inductive RouteDefectAtom where
  | obligation
  | storageRepair
  | storageTable
  deriving DecidableEq, Fintype

open RouteDefectAtom

/-- Embedding of selected route-defect atoms into protected packet components. -/
def routeDefectAtomComponent :
    RouteDefectAtom -> SourceRefPacketProtectedComponent
  | obligation => SourceRefPacketProtectedComponent.obligation
  | storageRepair => SourceRefPacketProtectedComponent.repairFrontier CodeAtom.storage
  | storageTable => SourceRefPacketProtectedComponent.sourceRefTable CodeAtom.storage

/-- Every selected atom is grounded in the Cycle 28 visible-flat endpoint route. -/
theorem visibleRoute_selectedRouteDefectSupport
    (atom : RouteDefectAtom) :
    RouteDefectSupport
      visibleRouteLeft visibleRouteRight
      (routeDefectAtomComponent atom) := by
  cases atom with
  | obligation => exact visibleRepairTransport_defectSupport_obligation
  | storageRepair => exact visibleRepairTransport_defectSupport_storageRepair
  | storageTable => exact visibleRepairTransport_defectSupport_storageTable

/--
The selected route defect support is exact: obligation, storage repair-frontier,
and storage table are defects, while off-storage repair/table coordinates are
flat.
-/
def VisibleRouteSelectedDefectSupportGrounded : Prop :=
    RouteDefectSupport
      visibleRouteLeft visibleRouteRight
      (routeDefectAtomComponent obligation) ∧
    RouteDefectSupport
      visibleRouteLeft visibleRouteRight
      (routeDefectAtomComponent storageRepair) ∧
    RouteDefectSupport
      visibleRouteLeft visibleRouteRight
      (routeDefectAtomComponent storageTable) ∧
    (∀ atom, atom ≠ CodeAtom.storage ->
      ¬ RouteDefectSupport
        visibleRouteLeft visibleRouteRight
        (SourceRefPacketProtectedComponent.repairFrontier atom)) ∧
    (∀ atom, atom ≠ CodeAtom.storage ->
      ¬ RouteDefectSupport
        visibleRouteLeft visibleRouteRight
        (SourceRefPacketProtectedComponent.sourceRefTable atom))

/-- The selected route support is grounded by the Cycle 38 exact support computation. -/
theorem visibleRoute_selectedDefectSupport_grounded :
    VisibleRouteSelectedDefectSupportGrounded :=
  ⟨visibleRepairTransport_defectSupport_obligation,
    visibleRepairTransport_defectSupport_storageRepair,
    visibleRepairTransport_defectSupport_storageTable,
    visibleRepairTransport_noRepairFrontierDefect_offStorage,
    visibleRepairTransport_noTableDefect_offStorage⟩

/-! ## Selected minimal route-defect branches -/

/-- Selected minimal support branches for the visible-flat route defect. -/
inductive RouteDefectBranch where
  | obligationBranch
  | storageRepairBranch
  | storageTableBranch
  deriving DecidableEq, Fintype

open RouteDefectBranch

/-- The selected atom carried by a minimal route-defect branch. -/
def routeDefectBranchAtom :
    RouteDefectBranch -> RouteDefectAtom
  | obligationBranch => obligation
  | storageRepairBranch => storageRepair
  | storageTableBranch => storageTable

/-- A branch is grounded when its selected route-defect atom appears at the endpoint route. -/
def RouteDefectBranchGrounded (branch : RouteDefectBranch) : Prop :=
  RouteDefectSupport
    visibleRouteLeft visibleRouteRight
    (routeDefectAtomComponent (routeDefectBranchAtom branch))

/-- The singleton selected support carried by a route-defect branch. -/
def RouteDefectBranchSupport
    (branch : RouteDefectBranch) : RouteDefectAtom -> Prop :=
  fun atom => atom = routeDefectBranchAtom branch

/--
A selected route-defect branch is minimal when its singleton support is
grounded and every nonempty sub-support of it contains that same atom.
-/
def IsSelectedMinimalRouteDefectBranch
    (branch : RouteDefectBranch) : Prop :=
  RouteDefectBranchGrounded branch ∧
    RouteDefectBranchSupport branch (routeDefectBranchAtom branch) ∧
    (∀ support : RouteDefectAtom -> Prop,
      (∀ atom, support atom -> RouteDefectBranchSupport branch atom) ->
        (∃ atom, support atom) ->
          ∀ atom, RouteDefectBranchSupport branch atom -> support atom)

/-- Every selected minimal route-defect branch is grounded. -/
theorem routeDefectBranch_grounded
    (branch : RouteDefectBranch) :
    RouteDefectBranchGrounded branch := by
  cases branch with
  | obligationBranch => exact visibleRepairTransport_defectSupport_obligation
  | storageRepairBranch => exact visibleRepairTransport_defectSupport_storageRepair
  | storageTableBranch => exact visibleRepairTransport_defectSupport_storageTable

/-- Every selected route-defect branch is a singleton minimal support branch. -/
theorem routeDefectBranch_selectedMinimal
    (branch : RouteDefectBranch) :
    IsSelectedMinimalRouteDefectBranch branch := by
  refine ⟨routeDefectBranch_grounded branch, rfl, ?_⟩
  intro support hsubset hnonempty atom hatom
  rcases hnonempty with ⟨witness, hwitness⟩
  have hwitness_eq : witness = routeDefectBranchAtom branch :=
    hsubset witness hwitness
  have hatom_eq : atom = routeDefectBranchAtom branch := hatom
  rw [hatom_eq, ← hwitness_eq]
  exact hwitness

/-- The selected route-defect family consists of minimal grounded branches. -/
theorem selectedRouteDefectSupportFamily_minimal :
    ∀ branch, IsSelectedMinimalRouteDefectBranch branch :=
  routeDefectBranch_selectedMinimal

/-- A correction hits a selected route-defect branch when it touches that branch's atom. -/
def CorrectionHitsRouteDefectBranch
    (correction : RouteDefectAtom -> Bool)
    (branch : RouteDefectBranch) : Prop :=
  correction (routeDefectBranchAtom branch) = true

/-- A selected branch remains after correction when it is grounded and missed. -/
def RouteDefectBranchRemainsAfterCorrection
    (correction : RouteDefectAtom -> Bool)
    (branch : RouteDefectBranch) : Prop :=
  RouteDefectBranchGrounded branch ∧
    ¬ CorrectionHitsRouteDefectBranch correction branch

/-- A correction eliminates the selected endpoint route defect when no selected branch remains. -/
def RouteDefectCorrectionEliminates
    (correction : RouteDefectAtom -> Bool) : Prop :=
  ∀ branch, ¬ RouteDefectBranchRemainsAfterCorrection correction branch

/-- A hit branch leaves no after-correction route defect on that branch. -/
theorem no_routeDefectAfterCorrection_of_hits
    {correction : RouteDefectAtom -> Bool}
    {branch : RouteDefectBranch}
    (hhit : CorrectionHitsRouteDefectBranch correction branch) :
    ¬ RouteDefectBranchRemainsAfterCorrection correction branch := by
  intro hafter
  exact hafter.2 hhit

/-- A missed grounded branch remains after correction. -/
theorem missed_routeDefectBranch_remains
    {correction : RouteDefectAtom -> Bool}
    {branch : RouteDefectBranch}
    (hmiss : ¬ CorrectionHitsRouteDefectBranch correction branch) :
    RouteDefectBranchRemainsAfterCorrection correction branch :=
  ⟨routeDefectBranch_grounded branch, hmiss⟩

/-- Any correction that eliminates the selected endpoint route defect hits every selected branch. -/
theorem hits_every_selectedRouteDefectSupport_of_eliminates
    {correction : RouteDefectAtom -> Bool}
    (helim : RouteDefectCorrectionEliminates correction) :
    ∀ branch, CorrectionHitsRouteDefectBranch correction branch := by
  intro branch
  cases branch with
  | obligationBranch =>
      cases h : correction obligation with
      | false =>
          have hmiss :
              ¬ CorrectionHitsRouteDefectBranch correction obligationBranch := by
            intro hhit
            change correction obligation = true at hhit
            rw [h] at hhit
            cases hhit
          exact False.elim
            (helim obligationBranch
              (missed_routeDefectBranch_remains hmiss))
      | true => exact h
  | storageRepairBranch =>
      cases h : correction storageRepair with
      | false =>
          have hmiss :
              ¬ CorrectionHitsRouteDefectBranch correction storageRepairBranch := by
            intro hhit
            change correction storageRepair = true at hhit
            rw [h] at hhit
            cases hhit
          exact False.elim
            (helim storageRepairBranch
              (missed_routeDefectBranch_remains hmiss))
      | true => exact h
  | storageTableBranch =>
      cases h : correction storageTable with
      | false =>
          have hmiss :
              ¬ CorrectionHitsRouteDefectBranch correction storageTableBranch := by
            intro hhit
            change correction storageTable = true at hhit
            rw [h] at hhit
            cases hhit
          exact False.elim
            (helim storageTableBranch
              (missed_routeDefectBranch_remains hmiss))
      | true => exact h

/-! ## Source-ref packet correction semantics -/

/--
Apply a selected correction to the left visible route endpoint by copying the
hit protected components from the right endpoint.  Off-selected coordinates
stay at the original left endpoint.
-/
def correctedVisibleRouteLeft
    (correction : RouteDefectAtom -> Bool) : SourceRefPacket where
  visibleScalarReading := visibleRouteLeft.visibleScalarReading
  verdict := visibleRouteLeft.verdict
  codeSupport := visibleRouteLeft.codeSupport
  obligation :=
    if correction obligation = true then
      visibleRouteRight.obligation
    else
      visibleRouteLeft.obligation
  repairFrontier := fun atom =>
    match atom with
    | CodeAtom.storage =>
        if correction storageRepair = true then
          visibleRouteRight.repairFrontier CodeAtom.storage
        else
          visibleRouteLeft.repairFrontier CodeAtom.storage
    | CodeAtom.endpoint => visibleRouteLeft.repairFrontier CodeAtom.endpoint
    | CodeAtom.worker => visibleRouteLeft.repairFrontier CodeAtom.worker
  sourceRefTable := fun atom =>
    match atom with
    | CodeAtom.storage =>
        if correction storageTable = true then
          visibleRouteRight.sourceRefTable CodeAtom.storage
        else
          visibleRouteLeft.sourceRefTable CodeAtom.storage
    | CodeAtom.endpoint => visibleRouteLeft.sourceRefTable CodeAtom.endpoint
    | CodeAtom.worker => visibleRouteLeft.sourceRefTable CodeAtom.worker

/-- A selected correction realizes a branch when the corrected packet agrees with the right endpoint there. -/
def CorrectionRealizesRouteDefectBranch
    (correction : RouteDefectAtom -> Bool)
    (branch : RouteDefectBranch) : Prop :=
  RouteComponentAgreement
    (correctedVisibleRouteLeft correction)
    visibleRouteRight
    (routeDefectAtomComponent (routeDefectBranchAtom branch))

/--
For the selected endpoint route defect, hitting a branch is exactly what makes
the corrected packet agree with the right endpoint on that branch's protected
component.
-/
theorem correctedBranchAgreement_iff_hits
    (correction : RouteDefectAtom -> Bool)
    (branch : RouteDefectBranch) :
    CorrectionRealizesRouteDefectBranch correction branch ↔
      CorrectionHitsRouteDefectBranch correction branch := by
  cases branch with
  | obligationBranch =>
      constructor
      · intro hagree
        change correction obligation = true
        cases h : correction obligation with
        | false =>
            have hcond : ¬ correction obligation = true := by
              intro htrue
              rw [h] at htrue
              cases htrue
            change
              (if correction obligation = true then
                  visibleRouteRight.obligation
                else
                  visibleRouteLeft.obligation) =
                visibleRouteRight.obligation at hagree
            rw [if_neg hcond] at hagree
            have hleft :
                RouteComponentAgreement
                  visibleRouteLeft visibleRouteRight
                  SourceRefPacketProtectedComponent.obligation := by
              exact hagree
            exact False.elim
              (visibleRepairTransport_defectSupport_obligation hleft)
        | true => rfl
      · intro hhit
        change correction obligation = true at hhit
        change
          (if correction obligation = true then
              visibleRouteRight.obligation
            else
              visibleRouteLeft.obligation) =
            visibleRouteRight.obligation
        rw [hhit]
        rfl
  | storageRepairBranch =>
      constructor
      · intro hagree
        change correction storageRepair = true
        cases h : correction storageRepair with
        | false =>
            have hcond : ¬ correction storageRepair = true := by
              intro htrue
              rw [h] at htrue
              cases htrue
            change
              ((if correction storageRepair = true then
                  visibleRouteRight.repairFrontier CodeAtom.storage
                else
                  visibleRouteLeft.repairFrontier CodeAtom.storage) ↔
                visibleRouteRight.repairFrontier CodeAtom.storage) at hagree
            rw [if_neg hcond] at hagree
            have hleft :
                RouteComponentAgreement
                  visibleRouteLeft visibleRouteRight
                  (SourceRefPacketProtectedComponent.repairFrontier CodeAtom.storage) := by
              exact hagree
            exact False.elim
              (visibleRepairTransport_defectSupport_storageRepair hleft)
        | true => rfl
      · intro hhit
        change correction storageRepair = true at hhit
        change
          ((if correction storageRepair = true then
              visibleRouteRight.repairFrontier CodeAtom.storage
            else
              visibleRouteLeft.repairFrontier CodeAtom.storage) ↔
            visibleRouteRight.repairFrontier CodeAtom.storage)
        rw [hhit]
        rfl
  | storageTableBranch =>
      constructor
      · intro hagree
        change correction storageTable = true
        cases h : correction storageTable with
        | false =>
            have hcond : ¬ correction storageTable = true := by
              intro htrue
              rw [h] at htrue
              cases htrue
            change
              (if correction storageTable = true then
                  visibleRouteRight.sourceRefTable CodeAtom.storage
                else
                  visibleRouteLeft.sourceRefTable CodeAtom.storage) =
                visibleRouteRight.sourceRefTable CodeAtom.storage at hagree
            rw [if_neg hcond] at hagree
            have hleft :
                RouteComponentAgreement
                  visibleRouteLeft visibleRouteRight
                  (SourceRefPacketProtectedComponent.sourceRefTable CodeAtom.storage) := by
              exact hagree
            exact False.elim
              (visibleRepairTransport_defectSupport_storageTable hleft)
        | true => rfl
      · intro hhit
        change correction storageTable = true at hhit
        change
          (if correction storageTable = true then
              visibleRouteRight.sourceRefTable CodeAtom.storage
            else
              visibleRouteLeft.sourceRefTable CodeAtom.storage) =
            visibleRouteRight.sourceRefTable CodeAtom.storage
        rw [hhit]
        rfl

/-- A packet-level selected correction eliminates the selected endpoint defect. -/
def SourceRefRouteCorrectionEliminates
    (correction : RouteDefectAtom -> Bool) : Prop :=
  ∀ branch, CorrectionRealizesRouteDefectBranch correction branch

/-- Packet-level elimination is equivalent to hitting every selected route-defect branch. -/
theorem sourceRefRouteCorrection_eliminates_iff_hits
    (correction : RouteDefectAtom -> Bool) :
    SourceRefRouteCorrectionEliminates correction ↔
      ∀ branch, CorrectionHitsRouteDefectBranch correction branch := by
  constructor
  · intro helim branch
    exact (correctedBranchAgreement_iff_hits correction branch).mp
      (helim branch)
  · intro hhits branch
    exact (correctedBranchAgreement_iff_hits correction branch).mpr
      (hhits branch)

/-- Any selected protected-component packet correction must hit every route-defect branch. -/
theorem sourceRefRouteCorrection_hits_every_of_eliminates
    {correction : RouteDefectAtom -> Bool}
    (helim : SourceRefRouteCorrectionEliminates correction) :
    ∀ branch, CorrectionHitsRouteDefectBranch correction branch :=
  (sourceRefRouteCorrection_eliminates_iff_hits correction).mp helim

/-! ## Finite witness computations -/

/-- The selected route-defect support family is nonempty. -/
theorem selectedRouteDefectSupportFamily_nonempty :
    ∃ branch : RouteDefectBranch, RouteDefectBranchGrounded branch :=
  ⟨obligationBranch, routeDefectBranch_grounded obligationBranch⟩

/-- The obligation branch and storage table branch are distinct. -/
theorem selectedRouteDefect_obligation_storageTable_distinct :
    obligationBranch ≠ storageTableBranch := by
  intro h
  cases h

/-- A correction that touches only the obligation branch. -/
def obligationOnlyCorrection : RouteDefectAtom -> Bool
  | obligation => true
  | storageRepair => false
  | storageTable => false

/-- A correction that touches every selected route-defect branch. -/
def allRouteDefectCorrection : RouteDefectAtom -> Bool
  | obligation => true
  | storageRepair => true
  | storageTable => true

/-- The obligation-only correction hits the obligation branch. -/
theorem obligationOnlyCorrection_hits_obligation :
    CorrectionHitsRouteDefectBranch obligationOnlyCorrection obligationBranch :=
  rfl

/-- The obligation-only correction misses the storage repair branch. -/
theorem obligationOnlyCorrection_misses_storageRepair :
    ¬ CorrectionHitsRouteDefectBranch obligationOnlyCorrection storageRepairBranch := by
  intro h
  cases h

/-- The obligation-only correction leaves the storage repair branch. -/
theorem obligationOnlyCorrection_storageRepair_remains :
    RouteDefectBranchRemainsAfterCorrection
      obligationOnlyCorrection storageRepairBranch :=
  missed_routeDefectBranch_remains
    obligationOnlyCorrection_misses_storageRepair

/-- A correction that hits only the obligation branch does not eliminate the selected route defect. -/
theorem obligationOnlyCorrection_does_not_eliminate :
    ¬ RouteDefectCorrectionEliminates obligationOnlyCorrection := by
  intro helim
  exact helim storageRepairBranch
    obligationOnlyCorrection_storageRepair_remains

/-- The all-branch correction eliminates the selected route defect. -/
theorem allRouteDefectCorrection_eliminates :
    RouteDefectCorrectionEliminates allRouteDefectCorrection := by
  intro branch
  cases branch with
  | obligationBranch => exact no_routeDefectAfterCorrection_of_hits rfl
  | storageRepairBranch => exact no_routeDefectAfterCorrection_of_hits rfl
  | storageTableBranch => exact no_routeDefectAfterCorrection_of_hits rfl

/-- The all-branch correction hits every selected route-defect branch. -/
theorem allRouteDefectCorrection_hits_every_selectedRouteDefectSupport :
    ∀ branch,
      CorrectionHitsRouteDefectBranch allRouteDefectCorrection branch :=
  hits_every_selectedRouteDefectSupport_of_eliminates
    allRouteDefectCorrection_eliminates

/-- The obligation-only packet correction does not eliminate the selected endpoint route defect. -/
theorem obligationOnly_packetCorrection_does_not_eliminate :
    ¬ SourceRefRouteCorrectionEliminates obligationOnlyCorrection := by
  intro helim
  have hhits :=
    sourceRefRouteCorrection_hits_every_of_eliminates helim
  exact obligationOnlyCorrection_misses_storageRepair
    (hhits storageRepairBranch)

/-- The all-branch packet correction eliminates the selected endpoint route defect. -/
theorem allRouteDefect_packetCorrection_eliminates :
    SourceRefRouteCorrectionEliminates allRouteDefectCorrection :=
  (sourceRefRouteCorrection_eliminates_iff_hits
    allRouteDefectCorrection).mpr
    allRouteDefectCorrection_hits_every_selectedRouteDefectSupport

/-! ## Theorem package -/

/--
Cycle-43 theorem package: the visible-flat route defect has a selected
three-branch support family, and eliminating that selected defect requires
hitting every selected branch.
-/
theorem selectedRouteDefectSupportHitting_package :
    VisibleRouteSelectedDefectSupportGrounded ∧
    supportSurfaceReading.Equivalent visibleRouteLeft visibleRouteRight ∧
    SourceRefExactVisualizationCriterion.LossyPacketToTupleVisualization
      SourceRefTupleBridge.endpointGridCertificate
      SourceRefTupleBridge.endpointGridCertificate
      visibleRouteLeft visibleRouteRight ∧
    ¬ SourceRefExactVisualizationCriterion.SourceRefExactVisualization
      SourceRefTupleBridge.endpointGridCertificate
      SourceRefTupleBridge.endpointGridCertificate
      visibleRouteLeft visibleRouteRight ∧
    (∃ branch : RouteDefectBranch, RouteDefectBranchGrounded branch) ∧
    (∀ branch, IsSelectedMinimalRouteDefectBranch branch) ∧
    obligationBranch ≠ storageTableBranch ∧
    CorrectionHitsRouteDefectBranch obligationOnlyCorrection obligationBranch ∧
    ¬ CorrectionHitsRouteDefectBranch obligationOnlyCorrection storageRepairBranch ∧
    RouteDefectBranchRemainsAfterCorrection
      obligationOnlyCorrection storageRepairBranch ∧
    ¬ RouteDefectCorrectionEliminates obligationOnlyCorrection ∧
    RouteDefectCorrectionEliminates allRouteDefectCorrection ∧
    (∀ branch,
      CorrectionHitsRouteDefectBranch allRouteDefectCorrection branch) ∧
    ¬ SourceRefRouteCorrectionEliminates obligationOnlyCorrection ∧
    SourceRefRouteCorrectionEliminates allRouteDefectCorrection ∧
    (∀ {correction : RouteDefectAtom -> Bool},
      SourceRefRouteCorrectionEliminates correction ->
        ∀ branch, CorrectionHitsRouteDefectBranch correction branch) := by
  exact ⟨visibleRoute_selectedDefectSupport_grounded,
    VisibleRepairTransportCommutator.repairTransport_visiblePacketSurface_commutes,
    VisibleRepairTransportCommutator.repairTransport_lossyPacketToTupleVisualization,
    VisibleRepairTransportCommutator.repairTransport_not_sourceRefExactVisualization,
    selectedRouteDefectSupportFamily_nonempty,
    selectedRouteDefectSupportFamily_minimal,
    selectedRouteDefect_obligation_storageTable_distinct,
    obligationOnlyCorrection_hits_obligation,
    obligationOnlyCorrection_misses_storageRepair,
    obligationOnlyCorrection_storageRepair_remains,
    obligationOnlyCorrection_does_not_eliminate,
    allRouteDefectCorrection_eliminates,
    allRouteDefectCorrection_hits_every_selectedRouteDefectSupport,
    obligationOnly_packetCorrection_does_not_eliminate,
    allRouteDefect_packetCorrection_eliminates,
    by
      intro correction helim branch
      exact sourceRefRouteCorrection_hits_every_of_eliminates helim branch⟩

end SelectedRouteDefectSupportHitting
end QualitySurface
end ResearchLean.AG
