import ResearchLean.AG.QualitySurface.OverlapObstructionBasis
import ResearchLean.AG.QualitySurface.RepairTransportHandoffObstructionBridge

/-!
Cycle 67 evidence for `G-aat-quality-surface-01`.

This file packages a selected repair/transport Cech commutator cell.  The
selected cell has a flat Cech path and a curved Cech path with the same visible
repair/transport endpoint surface and the same locally exact chart cover.  The
flat path has empty overlap support, while the curved path uses the selected
visible repair/transport handoff atlas as its overlap cocycle and carries an
exact nonempty Cech overlap basis.

The claim is relative to selected finite source-ref handoff covers, the visible
repair/transport endpoint witness, the finite `BridgeComponent` vocabulary, and
declared component-level repair predicates.  It does not assert canonical global
curvature, runtime repair synthesis, source extraction completeness, ArchMap
correctness, arbitrary route enumeration, global sheaf completeness, or
whole-codebase quality.
-/

namespace ResearchLean.AG
namespace QualitySurface
namespace RepairTransportCechCommutatorCurvature

open CodebaseTracePacket
open HeterogeneousRouteInteraction
open HeterogeneousRouteInteraction.BridgeComponent
open RouteDefectSupportTheory
open SourceRefHandoffBridge
open SourceRefHandoffHolonomyCorrespondence
open SourceRefHandoffObstructionLocus
open SourceRefHandoffComponentSupport
open HandoffRepairTransversalTheorem
open HandoffCechExactness
open HandoffCechOverlapBasis
open RepairTransportHandoffObstructionBridge

/-! ## Selected Cech paths for the repair/transport commutator -/

/--
A typed repair/transport Cech commutator cell.

The visible endpoints and their visible surface are part of the same object as
the flat and curved Cech paths.  The path fields are intentionally only covers:
exactness, basis, and repair-transversal claims are proved below rather than
stored as assumptions in the cell.
-/
structure RepairTransportCechCommutatorCell where
  leftEndpoint : SourceRefPacket
  rightEndpoint : SourceRefPacket
  visibleSurface : supportSurfaceReading.Equivalent leftEndpoint rightEndpoint
  flatPath : HandoffCechCover
  curvedPath : HandoffCechCover

/-- The flat Cech path uses the aligned source-ref handoff atlas as overlap. -/
def repairTransportFlatCechCover : HandoffCechCover where
  charts := [alignedSourceRefHandoffAtlas]
  overlapCocycle := alignedSourceRefHandoffAtlas

/--
The curved Cech path keeps the same local chart but uses the selected visible
repair/transport handoff atlas as overlap cocycle.
-/
def repairTransportCurvedCechCover : HandoffCechCover where
  charts := [alignedSourceRefHandoffAtlas]
  overlapCocycle := visibleRepairTransportHandoffBridge.toAtlas

/-- The selected repair/transport Cech commutator cell. -/
def selectedRepairTransportCechCommutatorCell :
    RepairTransportCechCommutatorCell where
  leftEndpoint := visibleRouteLeft
  rightEndpoint := visibleRouteRight
  visibleSurface :=
    VisibleRepairTransportCommutator.repairTransport_visiblePacketSurface_commutes
  flatPath := repairTransportFlatCechCover
  curvedPath := repairTransportCurvedCechCover

/--
The visible/local projection seen by the selected Cech cell: same visible
repair/transport endpoint surface, local exactness on both paths, and the same
chart cover.
-/
def SameVisibleLocalRepairTransportProjection
    (cell : RepairTransportCechCommutatorCell) : Prop :=
  supportSurfaceReading.Equivalent cell.leftEndpoint cell.rightEndpoint /\
    HandoffCechLocalExact cell.flatPath /\
    HandoffCechLocalExact cell.curvedPath /\
    cell.flatPath.charts = cell.curvedPath.charts

/-- The flat Cech path has locally exact charts. -/
theorem repairTransportFlatCechCover_localExact :
    HandoffCechLocalExact repairTransportFlatCechCover := by
  intro chart hmem
  simp [repairTransportFlatCechCover] at hmem
  subst chart
  exact alignedSourceRefHandoffAtlas_interactionExact

/-- The curved Cech path has the same locally exact chart cover. -/
theorem repairTransportCurvedCechCover_localExact :
    HandoffCechLocalExact repairTransportCurvedCechCover := by
  intro chart hmem
  simp [repairTransportCurvedCechCover] at hmem
  subst chart
  exact alignedSourceRefHandoffAtlas_interactionExact

/-- The selected flat and curved paths share their visible/local projection. -/
theorem repairTransport_paths_same_visibleLocal :
    SameVisibleLocalRepairTransportProjection
      selectedRepairTransportCechCommutatorCell := by
  refine
    ⟨selectedRepairTransportCechCommutatorCell.visibleSurface,
      repairTransportFlatCechCover_localExact,
      repairTransportCurvedCechCover_localExact,
      ?_⟩
  rfl

/-! ## Flat path: empty generated overlap support -/

/-- The flat path has empty protected overlap support. -/
theorem flatPath_overlapSupportEmpty :
    HandoffCechOverlapSupportEmpty
      selectedRepairTransportCechCommutatorCell.flatPath := by
  intro hnonempty
  rcases hnonempty with ⟨component, hsupport⟩
  have hempty :
      HandoffComponentSupportEmpty alignedSourceRefHandoffAtlas :=
    (handoffComponentSupport_empty_iff_locusEmpty
      alignedSourceRefHandoffAtlas).mpr
      alignedSourceRefHandoffAtlas_locusEmpty
  exact hempty
    ⟨component, by
      simpa [selectedRepairTransportCechCommutatorCell,
        repairTransportFlatCechCover, HandoffCechOverlapSupport]
        using hsupport⟩

/-- The empty predicate is an exact overlap basis for the flat path. -/
theorem flatPath_overlapBasis_empty :
    OverlapObstructionBasis
      selectedRepairTransportCechCommutatorCell.flatPath
      (fun _ : BridgeComponent => False) := by
  constructor
  · intro component hfalse
    cases hfalse
  · intro component hsupport
    exact False.elim
      (flatPath_overlapSupportEmpty ⟨component, hsupport⟩)

/-! ## Curved path: exact nonempty overlap basis -/

/--
The selected repair/transport curvature basis consists of the trace and
repair-frontier handoff components exposed by the visible-only commutator.
-/
def repairTransportCurvatureBasis
    (component : BridgeComponent) : Prop :=
  component = BridgeComponent.trace \/
    component = BridgeComponent.repairFrontier

/-- The trace component of the selected commutator is curved overlap support. -/
theorem curvedPath_traceOverlapSupport :
    HandoffCechOverlapSupport
      selectedRepairTransportCechCommutatorCell.curvedPath
      BridgeComponent.trace := by
  let point :=
    visibleRepairTransport_tableDefect_to_handoffTraceObstructionPoint
  exact ⟨point.loop, point.loop_mem, point.support⟩

/--
The repair-frontier component of the selected commutator is curved overlap
support.
-/
theorem curvedPath_repairFrontierOverlapSupport :
    HandoffCechOverlapSupport
      selectedRepairTransportCechCommutatorCell.curvedPath
      BridgeComponent.repairFrontier := by
  let point :=
    visibleRepairTransport_repairFrontier_to_handoffObstructionPoint
  exact ⟨point.loop, point.loop_mem, point.support⟩

/--
The curved path has an exact selected overlap basis: precisely the trace and
repair-frontier components of the visible repair/transport handoff overlap.
-/
theorem curvedPath_overlapBasis :
    OverlapObstructionBasis
      selectedRepairTransportCechCommutatorCell.curvedPath
      repairTransportCurvatureBasis := by
  constructor
  · intro component hbasis
    rcases hbasis with htrace | hrepair
    · subst component
      exact curvedPath_traceOverlapSupport
    · subst component
      exact curvedPath_repairFrontierOverlapSupport
  · intro component hsupport
    rcases hsupport with ⟨loop, hmem, hfailure⟩
    simp [selectedRepairTransportCechCommutatorCell,
      repairTransportCurvedCechCover,
      RepairTransportHandoffBridge.toAtlas] at hmem
    subst loop
    cases component with
    | support =>
        have hlaw :
            visibleRepairTransportHandoff.ComponentLaw
              BridgeComponent.support :=
          visibleRepairTransportHandoff.supportCertified_iff.mp rfl
        exact False.elim (hfailure hlaw)
    | trace =>
        exact Or.inl rfl
    | repairFrontier =>
        exact Or.inr rfl

/-- The curved path has nonempty overlap support generated by its exact basis. -/
theorem curvedPath_overlapBasis_nonempty :
    OverlapObstructionBasis
        selectedRepairTransportCechCommutatorCell.curvedPath
        repairTransportCurvatureBasis /\
      HandoffCechOverlapSupportNonempty
        selectedRepairTransportCechCommutatorCell.curvedPath := by
  exact
    ⟨curvedPath_overlapBasis,
      ⟨BridgeComponent.trace, curvedPath_traceOverlapSupport⟩⟩

/--
Under local chart exactness, the curved path's nonempty overlap basis obstructs
global handoff exactness.
-/
theorem curvedPath_notGlobalExact_of_local
    (hlocal :
      HandoffCechLocalExact
        selectedRepairTransportCechCommutatorCell.curvedPath) :
    Not (HandoffCechGlobalExact
      selectedRepairTransportCechCommutatorCell.curvedPath) :=
  (handoffCech_overlapSupport_nonempty_iff_notGlobalExact_of_local
    hlocal).mp
    curvedPath_overlapBasis_nonempty.2

/--
Component-complete declared repair clears the curved path exactly when it hits
the selected curvature basis.
-/
theorem curvedPath_declaredClearance_iff_hitsCurvatureBasis
    {plan : HandoffRepairPlan}
    (hcomplete :
      ComponentCompleteHandoffRepairPlan
        selectedRepairTransportCechCommutatorCell.curvedPath.overlapCocycle
        plan) :
    HandoffCechRepairObligation
        selectedRepairTransportCechCommutatorCell.curvedPath plan <->
      OverlapBasisTransversal repairTransportCurvatureBasis plan.touched :=
  declaredClearance_iff_hitsEveryOverlapBasis_of_componentComplete
    (cover := selectedRepairTransportCechCommutatorCell.curvedPath)
    (basis := repairTransportCurvatureBasis)
    (plan := plan)
    curvedPath_overlapBasis
    hcomplete

/-! ## Cech curvature package -/

/--
A repair/transport Cech commutator cell carries Cech curvature when its visible
local projection is shared, the flat path has empty overlap basis, and the
curved path has exact nonempty overlap basis that obstructs global exactness.
-/
def CommutatorCechCurvature
    (cell : RepairTransportCechCommutatorCell) : Prop :=
  SameVisibleLocalRepairTransportProjection cell /\
    OverlapObstructionBasis cell.flatPath (fun _ : BridgeComponent => False) /\
    OverlapObstructionBasis cell.curvedPath repairTransportCurvatureBasis /\
    HandoffCechOverlapSupportEmpty cell.flatPath /\
    HandoffCechOverlapSupportNonempty cell.curvedPath /\
    Not (HandoffCechGlobalExact cell.curvedPath) /\
    (forall {plan : HandoffRepairPlan},
      ComponentCompleteHandoffRepairPlan cell.curvedPath.overlapCocycle plan ->
        (HandoffCechRepairObligation cell.curvedPath plan <->
          OverlapBasisTransversal repairTransportCurvatureBasis plan.touched))

/-- The selected repair/transport Cech commutator cell carries Cech curvature. -/
theorem selectedRepairTransportCechCommutator_hasCurvature :
    CommutatorCechCurvature
      selectedRepairTransportCechCommutatorCell := by
  exact
    ⟨repairTransport_paths_same_visibleLocal,
      flatPath_overlapBasis_empty,
      curvedPath_overlapBasis,
      flatPath_overlapSupportEmpty,
      curvedPath_overlapBasis_nonempty.2,
      curvedPath_notGlobalExact_of_local
        repairTransportCurvedCechCover_localExact,
      fun {plan} hcomplete =>
        curvedPath_declaredClearance_iff_hitsCurvatureBasis
          (plan := plan) hcomplete⟩

/--
The shared visible/local repair-transport projection is not faithful to the
protected Cech overlap curvature: the selected cell has the same visible/local
surface on both paths, while its flat and curved paths separate empty overlap
support from nonempty exact overlap basis.
-/
theorem visibleRepairTransport_not_faithful_to_cechCurvature :
    SameVisibleLocalRepairTransportProjection
        selectedRepairTransportCechCommutatorCell /\
      HandoffCechOverlapSupportEmpty
        selectedRepairTransportCechCommutatorCell.flatPath /\
      OverlapObstructionBasis
        selectedRepairTransportCechCommutatorCell.flatPath
        (fun _ : BridgeComponent => False) /\
      OverlapObstructionBasis
        selectedRepairTransportCechCommutatorCell.curvedPath
        repairTransportCurvatureBasis /\
      HandoffCechOverlapSupportNonempty
        selectedRepairTransportCechCommutatorCell.curvedPath /\
      Not (HandoffCechGlobalExact
        selectedRepairTransportCechCommutatorCell.curvedPath) := by
  exact
    ⟨repairTransport_paths_same_visibleLocal,
      flatPath_overlapSupportEmpty,
      flatPath_overlapBasis_empty,
      curvedPath_overlapBasis,
      curvedPath_overlapBasis_nonempty.2,
      curvedPath_notGlobalExact_of_local
        repairTransportCurvedCechCover_localExact⟩

/--
Cycle-67 theorem package: a selected repair/transport Cech commutator cell has
the same visible/local projection on flat and curved paths, empty flat overlap
support, exact nonempty curved overlap basis, local-to-global exactness failure
on the curved path, and declared-repair clearance exactly when the repair plan
hits the curvature basis.
-/
theorem repairTransportCechCommutatorCurvature_package :
    SameVisibleLocalRepairTransportProjection
        selectedRepairTransportCechCommutatorCell /\
      OverlapObstructionBasis
        selectedRepairTransportCechCommutatorCell.flatPath
        (fun _ : BridgeComponent => False) /\
      OverlapObstructionBasis
        selectedRepairTransportCechCommutatorCell.curvedPath
        repairTransportCurvatureBasis /\
      HandoffCechOverlapSupportEmpty
        selectedRepairTransportCechCommutatorCell.flatPath /\
      HandoffCechOverlapSupportNonempty
        selectedRepairTransportCechCommutatorCell.curvedPath /\
      Not (HandoffCechGlobalExact
        selectedRepairTransportCechCommutatorCell.curvedPath) /\
      (forall {plan : HandoffRepairPlan},
        ComponentCompleteHandoffRepairPlan
            selectedRepairTransportCechCommutatorCell.curvedPath.overlapCocycle
            plan ->
          (HandoffCechRepairObligation
              selectedRepairTransportCechCommutatorCell.curvedPath plan <->
            OverlapBasisTransversal
              repairTransportCurvatureBasis plan.touched)) /\
      CommutatorCechCurvature
        selectedRepairTransportCechCommutatorCell := by
  exact
    ⟨repairTransport_paths_same_visibleLocal,
      flatPath_overlapBasis_empty,
      curvedPath_overlapBasis,
      flatPath_overlapSupportEmpty,
      curvedPath_overlapBasis_nonempty.2,
      curvedPath_notGlobalExact_of_local
        repairTransportCurvedCechCover_localExact,
      fun {plan} hcomplete =>
        curvedPath_declaredClearance_iff_hitsCurvatureBasis
          (plan := plan) hcomplete,
      selectedRepairTransportCechCommutator_hasCurvature⟩

end RepairTransportCechCommutatorCurvature
end QualitySurface
end ResearchLean.AG
