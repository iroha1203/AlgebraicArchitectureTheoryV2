import ResearchLean.AG.QualitySurface.OrderedScanFirstFailingSlot

/-!
Cycle 57 evidence for `G-aat-quality-surface-01`.

This file separates local route exactness from cross-route interaction
exactness.  The result is relative to a supplied heterogeneous state and a
declared bridge certificate with support, trace, and repair-frontier
components.  It does not synthesize repairs, validate ArchMap observations,
enumerate arbitrary route systems, or judge whole-codebase quality.
-/

namespace ResearchLean.AG
namespace QualitySurface
namespace HeterogeneousRouteInteraction

open SourceRefExactVisualizationCriterion
open ParametrizedSelectedCorrectionSystem
open MultiRouteCorrectionSystem
open FiniteRouteFamilyExactLocus
open FiniteRouteScan
open OrderedScanFirstFailingSlot
open RepairStage
open RouteSlot

/-! ## Heterogeneous route states -/

/-- Components of the supplied cross-route bridge certificate. -/
inductive BridgeComponent where
  | support
  | trace
  | repairFrontier
  deriving DecidableEq, Fintype

open BridgeComponent

/-- A supplied bridge certificate linking the heterogeneous route surfaces. -/
structure BridgeCertificate where
  supportPreserved : Bool
  tracePreserved : Bool
  repairFrontierPreserved : Bool
  deriving DecidableEq

/-- Read one component of the bridge certificate. -/
def BridgeCertificate.component
    (bridge : BridgeCertificate) : BridgeComponent -> Bool
  | support => bridge.supportPreserved
  | trace => bridge.tracePreserved
  | repairFrontier => bridge.repairFrontierPreserved

/-- The bridge certificate is fully aligned. -/
def BridgeCertificate.Aligned
    (bridge : BridgeCertificate) : Prop :=
  bridge.supportPreserved = true ∧
    bridge.tracePreserved = true ∧
    bridge.repairFrontierPreserved = true

/-- A concrete bridge obstruction certificate. -/
structure BridgeObstruction
    (bridge : BridgeCertificate) where
  component : BridgeComponent
  fails : bridge.component component = false

/-- A bridge has at least one explicit obstruction certificate. -/
def HasBridgeObstruction
    (bridge : BridgeCertificate) : Prop :=
  ∃ _obstruction : BridgeObstruction bridge, True

/--
A heterogeneous state carries two different local exactness surfaces:
one selected-correction route stage and one finite route-family scan
assignment.  `bridge` records the supplied cross-route bridge certificate.
-/
structure HeterogeneousRouteState where
  selectedStage : RepairStage
  scanAssignment : StageAssignment RouteSlot
  bridge : BridgeCertificate

/-- Local exactness of the selected correction route. -/
def SelectedRouteLocalExact
    (state : HeterogeneousRouteState) : Prop :=
  CorrectionSourceRefExact (stagedCorrection state.selectedStage)

/-- Local exactness of the finite scanned route-family surface. -/
def ScanRouteLocalExact
    (state : HeterogeneousRouteState) : Prop :=
  AssignmentFamilySourceRefExact state.scanAssignment

/-- Product of the two local exactness readings. -/
def ProductLocalExact
    (state : HeterogeneousRouteState) : Prop :=
  SelectedRouteLocalExact state ∧ ScanRouteLocalExact state

/-- The supplied cross-route bridge law is aligned. -/
def BridgeAligned
    (state : HeterogeneousRouteState) : Prop :=
  state.bridge.Aligned

/--
Heterogeneous interaction exactness: local exactness product plus the bridge
law.  This is intentionally stronger than per-route green status.
-/
def InteractionExact
    (state : HeterogeneousRouteState) : Prop :=
  ProductLocalExact state ∧ BridgeAligned state

/-! ## Concrete product-exact but interaction-obstructed witness -/

/-- Constant all-branches assignment for the scanned route-family surface. -/
def allBranchesScanAssignment : StageAssignment RouteSlot :=
  fun _slot => allBranches

/-- The all-branches scan assignment is locally exact. -/
theorem allBranchesScanAssignment_exact :
    AssignmentFamilySourceRefExact allBranchesScanAssignment :=
  (assignmentFamilySourceRefExact_iff_allBranches
    allBranchesScanAssignment).mpr (by
      intro slot
      rfl)

/-- A bridge certificate with a trace handoff obstruction. -/
def traceBrokenBridge : BridgeCertificate where
  supportPreserved := true
  tracePreserved := false
  repairFrontierPreserved := true

/-- The trace handoff component fails in `traceBrokenBridge`. -/
def traceBrokenBridgeObstruction :
    BridgeObstruction traceBrokenBridge where
  component := trace
  fails := rfl

/-- A fully aligned bridge certificate. -/
def alignedBridge : BridgeCertificate where
  supportPreserved := true
  tracePreserved := true
  repairFrontierPreserved := true

/-- A fully aligned bridge has no failed component. -/
theorem alignedBridge_aligned :
    alignedBridge.Aligned :=
  ⟨rfl, rfl, rfl⟩

/-- A bridge obstruction rules out bridge alignment. -/
theorem bridgeObstruction_not_aligned
    {bridge : BridgeCertificate}
    (obstruction : BridgeObstruction bridge) :
    ¬ bridge.Aligned := by
  intro haligned
  rcases obstruction with ⟨component, hfail⟩
  rcases haligned with ⟨hsupport, htrace, hrepair⟩
  cases component with
  | support =>
      simp [BridgeCertificate.component, hsupport] at hfail
  | trace =>
      simp [BridgeCertificate.component, htrace] at hfail
  | repairFrontier =>
      simp [BridgeCertificate.component, hrepair] at hfail

/-- A bridge obstruction rules out heterogeneous interaction exactness. -/
theorem bridgeObstruction_obstructs_interactionExact
    {state : HeterogeneousRouteState}
    (obstruction : BridgeObstruction state.bridge) :
    ¬ InteractionExact state := by
  intro hexact
  exact bridgeObstruction_not_aligned obstruction hexact.2

def productExactBridgeBrokenState : HeterogeneousRouteState where
  selectedStage := allBranches
  scanAssignment := allBranchesScanAssignment
  bridge := traceBrokenBridge

/-- The selected-correction local route is exact in the bridge-broken state. -/
theorem productExactBridgeBroken_selectedLocalExact :
    SelectedRouteLocalExact productExactBridgeBrokenState := by
  simpa [SelectedRouteLocalExact, productExactBridgeBrokenState]
    using stagedCorrection_allBranches_exact

/-- The scanned route-family local surface is exact in the bridge-broken state. -/
theorem productExactBridgeBroken_scanLocalExact :
    ScanRouteLocalExact productExactBridgeBrokenState := by
  simpa [ScanRouteLocalExact, productExactBridgeBrokenState]
    using allBranchesScanAssignment_exact

/-- The bridge-broken state satisfies the product of local exactness readings. -/
theorem productExactBridgeBroken_productLocalExact :
    ProductLocalExact productExactBridgeBrokenState :=
  ⟨productExactBridgeBroken_selectedLocalExact,
    productExactBridgeBroken_scanLocalExact⟩

/-- The bridge-broken state carries a trace handoff obstruction. -/
def productExactBridgeBroken_traceObstruction :
    BridgeObstruction productExactBridgeBrokenState.bridge :=
  traceBrokenBridgeObstruction

/-- The bridge-broken state does not satisfy the cross-route bridge law. -/
theorem productExactBridgeBroken_not_bridgeAligned :
    ¬ BridgeAligned productExactBridgeBrokenState :=
  bridgeObstruction_not_aligned productExactBridgeBroken_traceObstruction

/--
Per-route local exactness product does not imply heterogeneous interaction
exactness.
-/
theorem heterogeneousProductExact_not_interactionExact :
    ProductLocalExact productExactBridgeBrokenState ∧
      ¬ InteractionExact productExactBridgeBrokenState := by
  constructor
  · exact productExactBridgeBroken_productLocalExact
  · intro hinteraction
    exact productExactBridgeBroken_not_bridgeAligned hinteraction.2

/-! ## Positive bridge-aligned comparator -/

/-- Same local exactness surfaces, but with the cross-route bridge aligned. -/
def bridgeAlignedInteractionState : HeterogeneousRouteState where
  selectedStage := allBranches
  scanAssignment := allBranchesScanAssignment
  bridge := alignedBridge

/-- The bridge-aligned comparator is interaction exact. -/
theorem bridgeAlignedInteractionState_interactionExact :
    InteractionExact bridgeAlignedInteractionState := by
  constructor
  · constructor
    · simpa [SelectedRouteLocalExact, bridgeAlignedInteractionState]
        using stagedCorrection_allBranches_exact
    · simpa [ScanRouteLocalExact, bridgeAlignedInteractionState]
        using allBranchesScanAssignment_exact
  · exact alignedBridge_aligned

/-- Interaction exactness remembers the local exactness product. -/
theorem heterogeneousInteractionExact_implies_productLocalExact
    {state : HeterogeneousRouteState}
    (hexact : InteractionExact state) :
      ProductLocalExact state :=
  hexact.1

/-- Interaction exactness remembers the bridge law. -/
theorem heterogeneousInteractionExact_implies_bridgeAligned
    {state : HeterogeneousRouteState}
    (hexact : InteractionExact state) :
      BridgeAligned state :=
  hexact.2

/--
Two states can have the same local exactness product while differing on
heterogeneous interaction exactness.
-/
theorem sameLocalProduct_differentInteractionExactness :
    ProductLocalExact productExactBridgeBrokenState ∧
      ProductLocalExact bridgeAlignedInteractionState ∧
      HasBridgeObstruction productExactBridgeBrokenState.bridge ∧
      ¬ InteractionExact productExactBridgeBrokenState ∧
      InteractionExact bridgeAlignedInteractionState := by
  exact ⟨productExactBridgeBroken_productLocalExact,
    bridgeAlignedInteractionState_interactionExact.1,
    ⟨productExactBridgeBroken_traceObstruction, trivial⟩,
    heterogeneousProductExact_not_interactionExact.2,
    bridgeAlignedInteractionState_interactionExact⟩

/-! ## Theorem package -/

/--
Cycle-57 theorem package: heterogeneous interaction exactness strictly
strengthens the product of local route exactness surfaces by requiring a
cross-route bridge law.
-/
theorem heterogeneousRouteInteraction_package :
    ProductLocalExact productExactBridgeBrokenState ∧
      HasBridgeObstruction productExactBridgeBrokenState.bridge ∧
      ¬ InteractionExact productExactBridgeBrokenState ∧
      InteractionExact bridgeAlignedInteractionState ∧
      (∀ {state : HeterogeneousRouteState},
        InteractionExact state -> ProductLocalExact state) ∧
      (∀ {state : HeterogeneousRouteState},
        InteractionExact state -> BridgeAligned state) ∧
      (∀ {state : HeterogeneousRouteState},
        BridgeObstruction state.bridge -> ¬ InteractionExact state) ∧
      (ProductLocalExact productExactBridgeBrokenState ∧
        ProductLocalExact bridgeAlignedInteractionState ∧
        HasBridgeObstruction productExactBridgeBrokenState.bridge ∧
        ¬ InteractionExact productExactBridgeBrokenState ∧
        InteractionExact bridgeAlignedInteractionState) := by
  exact ⟨productExactBridgeBroken_productLocalExact,
    ⟨productExactBridgeBroken_traceObstruction, trivial⟩,
    heterogeneousProductExact_not_interactionExact.2,
    bridgeAlignedInteractionState_interactionExact,
    fun hexact => heterogeneousInteractionExact_implies_productLocalExact hexact,
    fun hexact => heterogeneousInteractionExact_implies_bridgeAligned hexact,
    fun obstruction =>
      bridgeObstruction_obstructs_interactionExact obstruction,
    sameLocalProduct_differentInteractionExactness⟩

end HeterogeneousRouteInteraction
end QualitySurface
end ResearchLean.AG
