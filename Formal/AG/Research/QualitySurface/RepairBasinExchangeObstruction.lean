import Formal.AG.Research.QualitySurface.RepairTransportCechCommutatorCurvature

/-!
Cycle 68 evidence for `G-aat-quality-surface-01`.

This file reads the selected repair/transport Cech commutator as a finite
repair/refinement basin exchange cell.  The repair basin is only a selected
finite overlap-basis / declared-clearance membership predicate for supplied
covers and repair plans.  It is not a runtime repair synthesis result, a
canonical refinement theorem, source extraction completeness, ArchMap
correctness, arbitrary route enumeration, global sheaf completeness, or a
whole-codebase quality claim.
-/

namespace Formal.AG.Research
namespace QualitySurface
namespace RepairBasinExchangeObstruction

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
open RepairTransportCechCommutatorCurvature

/-! ## A selected finite repair/refinement basin exchange cell -/

/--
A typed repair/refinement basin exchange cell.

The two path fields represent the selected finite `declared repair -> refine`
and `refine -> declared repair` readings.  The cell stores endpoints, visible
projection data, and the two covers only.  Exactness, bases, clearance, and
obstruction are proved below rather than assumed as fields.
-/
structure RepairRefinementBasinCell where
  leftEndpoint : SourceRefPacket
  rightEndpoint : SourceRefPacket
  visibleProjection : supportSurfaceReading.Equivalent leftEndpoint rightEndpoint
  coarsePath : HandoffCechCover
  refinedPath : HandoffCechCover

/--
The selected exchange cell.

The coarse path has trace overlap basis, while the refined path is the curved
path from the selected repair/transport Cech commutator and has trace plus
repair-frontier overlap basis.
-/
def selectedRepairRefinementBasinCell :
    RepairRefinementBasinCell where
  leftEndpoint := visibleRouteLeft
  rightEndpoint := visibleRouteRight
  visibleProjection :=
    VisibleRepairTransportCommutator.repairTransport_visiblePacketSurface_commutes
  coarsePath := traceOverlapBasisCover
  refinedPath := selectedRepairTransportCechCommutatorCell.curvedPath

/-- Same visible endpoint surface, local exactness on both paths, and same chart list. -/
def SameVisibleLocalRepairRefinementProjection
    (cell : RepairRefinementBasinCell) : Prop :=
  supportSurfaceReading.Equivalent cell.leftEndpoint cell.rightEndpoint /\
    HandoffCechLocalExact cell.coarsePath /\
    HandoffCechLocalExact cell.refinedPath /\
    cell.coarsePath.charts = cell.refinedPath.charts

/-- The selected coarse and refined paths share their visible/local projection. -/
theorem repairRefinement_paths_same_visibleLocal :
    SameVisibleLocalRepairRefinementProjection
      selectedRepairRefinementBasinCell := by
  refine
    ⟨selectedRepairRefinementBasinCell.visibleProjection,
      traceOverlapBasisCover_localExact,
      repairTransportCurvedCechCover_localExact,
      ?_⟩
  rfl

/-! ## Selected coarse and refined overlap bases -/

/-- The coarse repair basin is the selected trace overlap basis. -/
def repairRefinementCoarseBasis
    (component : BridgeComponent) : Prop :=
  singletonOverlapBasis BridgeComponent.trace component

/-- The refined repair basin is the selected trace / repair-frontier curvature basis. -/
def repairRefinementRefinedBasis
    (component : BridgeComponent) : Prop :=
  repairTransportCurvatureBasis component

/-- The union basis required for common coarse/refined clearance. -/
def repairRefinementUnionBasis
    (component : BridgeComponent) : Prop :=
  repairRefinementCoarseBasis component \/
    repairRefinementRefinedBasis component

/-- The selected coarse path has exact trace overlap basis. -/
theorem coarsePath_overlapBasis :
    OverlapObstructionBasis
      selectedRepairRefinementBasinCell.coarsePath
      repairRefinementCoarseBasis := by
  simpa [selectedRepairRefinementBasinCell, repairRefinementCoarseBasis]
    using traceOverlapBasis

/-- The selected refined path has exact trace / repair-frontier overlap basis. -/
theorem refinedPath_overlapBasis :
    OverlapObstructionBasis
      selectedRepairRefinementBasinCell.refinedPath
      repairRefinementRefinedBasis := by
  simpa [selectedRepairRefinementBasinCell, repairRefinementRefinedBasis]
    using curvedPath_overlapBasis

/--
Selected repair-basin membership: exact selected basis plus declared clearance
of that cover by the supplied plan.
-/
def RepairBasinMembership
    (cover : HandoffCechCover)
    (basis : BridgeComponent -> Prop)
    (plan : HandoffRepairPlan) : Prop :=
  OverlapObstructionBasis cover basis /\
    HandoffCechRepairObligation cover plan

/-- Common clearance of the coarse and refined basins by one plan. -/
def CommonRepairBasinClearance
    (cell : RepairRefinementBasinCell)
    (plan : HandoffRepairPlan) : Prop :=
  HandoffCechRepairObligation cell.coarsePath plan /\
    HandoffCechRepairObligation cell.refinedPath plan

/--
For component-complete repair plans, clearing both sides of the selected
exchange cell is equivalent to hitting the union of the selected bases.
-/
theorem commonClearance_iff_hits_unionBasis
    {plan : HandoffRepairPlan}
    (hcoarseComplete :
      ComponentCompleteHandoffRepairPlan
        selectedRepairRefinementBasinCell.coarsePath.overlapCocycle plan)
    (hrefinedComplete :
      ComponentCompleteHandoffRepairPlan
        selectedRepairRefinementBasinCell.refinedPath.overlapCocycle plan) :
    CommonRepairBasinClearance selectedRepairRefinementBasinCell plan <->
      OverlapBasisTransversal repairRefinementUnionBasis plan.touched := by
  constructor
  · intro hclear component hbasis
    rcases hbasis with hcoarse | hrefined
    · have hhit :
          OverlapBasisTransversal repairRefinementCoarseBasis
            plan.touched :=
        (declaredClearance_iff_hitsEveryOverlapBasis_of_componentComplete
          (cover := selectedRepairRefinementBasinCell.coarsePath)
          (basis := repairRefinementCoarseBasis)
          (plan := plan)
          coarsePath_overlapBasis
          hcoarseComplete).mp hclear.1
      exact hhit component hcoarse
    · have hhit :
          OverlapBasisTransversal repairRefinementRefinedBasis
            plan.touched :=
        (declaredClearance_iff_hitsEveryOverlapBasis_of_componentComplete
          (cover := selectedRepairRefinementBasinCell.refinedPath)
          (basis := repairRefinementRefinedBasis)
          (plan := plan)
          refinedPath_overlapBasis
          hrefinedComplete).mp hclear.2
      exact hhit component hrefined
  · intro hhit
    constructor
    · exact
        (declaredClearance_iff_hitsEveryOverlapBasis_of_componentComplete
          (cover := selectedRepairRefinementBasinCell.coarsePath)
          (basis := repairRefinementCoarseBasis)
          (plan := plan)
          coarsePath_overlapBasis
          hcoarseComplete).mpr
          (by
            intro component hbasis
            exact hhit component (Or.inl hbasis))
    · exact
        (declaredClearance_iff_hitsEveryOverlapBasis_of_componentComplete
          (cover := selectedRepairRefinementBasinCell.refinedPath)
          (basis := repairRefinementRefinedBasis)
          (plan := plan)
          refinedPath_overlapBasis
          hrefinedComplete).mpr
          (by
            intro component hbasis
            exact hhit component (Or.inr hbasis))

/--
If a component-complete plan hits the union basis, selected repair-basin
membership commutes across the coarse/refined exchange.
-/
theorem repairRefinement_basinMembership_commutes_of_compatible
    {plan : HandoffRepairPlan}
    (hcoarseComplete :
      ComponentCompleteHandoffRepairPlan
        selectedRepairRefinementBasinCell.coarsePath.overlapCocycle plan)
    (hrefinedComplete :
      ComponentCompleteHandoffRepairPlan
        selectedRepairRefinementBasinCell.refinedPath.overlapCocycle plan)
    (hhits :
      OverlapBasisTransversal repairRefinementUnionBasis plan.touched) :
    RepairBasinMembership selectedRepairRefinementBasinCell.coarsePath
        repairRefinementCoarseBasis plan /\
      RepairBasinMembership selectedRepairRefinementBasinCell.refinedPath
        repairRefinementRefinedBasis plan := by
  have hclear :
      CommonRepairBasinClearance selectedRepairRefinementBasinCell plan :=
    (commonClearance_iff_hits_unionBasis
      (plan := plan) hcoarseComplete hrefinedComplete).mpr hhits
  exact
    ⟨⟨coarsePath_overlapBasis, hclear.1⟩,
      ⟨refinedPath_overlapBasis, hclear.2⟩⟩

/-! ## A finite trace-only obstruction witness -/

/-- A declared repair plan that touches and clears only the trace component. -/
def traceOnlyRepairPlan : HandoffRepairPlan where
  touched := singletonRepairSupport BridgeComponent.trace
  clears := singletonRepairSupport BridgeComponent.trace
  clears_only_if_touched := by
    intro component hclear
    exact hclear

/-- The trace-only plan is component-complete for the selected coarse path. -/
theorem traceOnlyRepairPlan_componentComplete_coarse :
    ComponentCompleteHandoffRepairPlan
      selectedRepairRefinementBasinCell.coarsePath.overlapCocycle
      traceOnlyRepairPlan := by
  intro component _hsupport htouched
  exact htouched

/-- The trace-only plan is component-complete for the selected refined path. -/
theorem traceOnlyRepairPlan_componentComplete_refined :
    ComponentCompleteHandoffRepairPlan
      selectedRepairRefinementBasinCell.refinedPath.overlapCocycle
      traceOnlyRepairPlan := by
  intro component _hsupport htouched
  exact htouched

/-- The trace-only plan clears the coarse trace basin. -/
theorem traceOnlyRepairPlan_clears_coarseBasin :
    HandoffCechRepairObligation
      selectedRepairRefinementBasinCell.coarsePath
      traceOnlyRepairPlan := by
  exact
    (declaredClearance_iff_hitsEveryOverlapBasis_of_componentComplete
      (cover := selectedRepairRefinementBasinCell.coarsePath)
      (basis := repairRefinementCoarseBasis)
      (plan := traceOnlyRepairPlan)
      coarsePath_overlapBasis
      traceOnlyRepairPlan_componentComplete_coarse).mpr
      (by
        intro component hbasis
        exact hbasis)

/-- The trace-only plan does not touch the repair-frontier component. -/
theorem traceOnlyRepairPlan_misses_repairFrontier :
    Not (traceOnlyRepairPlan.touched BridgeComponent.repairFrontier) := by
  intro htouched
  cases htouched

/-- The trace-only plan fails the refined trace-plus-repair-frontier basin. -/
theorem traceOnlyRepairPlan_fails_refinedBasin :
    Not
      (HandoffCechRepairObligation
        selectedRepairRefinementBasinCell.refinedPath
        traceOnlyRepairPlan) := by
  intro hclear
  have hhit :
      OverlapBasisTransversal repairRefinementRefinedBasis
        traceOnlyRepairPlan.touched :=
    (declaredClearance_iff_hitsEveryOverlapBasis_of_componentComplete
      (cover := selectedRepairRefinementBasinCell.refinedPath)
      (basis := repairRefinementRefinedBasis)
      (plan := traceOnlyRepairPlan)
      refinedPath_overlapBasis
      traceOnlyRepairPlan_componentComplete_refined).mp hclear
  exact traceOnlyRepairPlan_misses_repairFrontier
    (hhit BridgeComponent.repairFrontier (Or.inr rfl))

/--
A repair-basin exchange obstruction: same visible/local projection and exact
selected bases, while one component-complete plan clears the coarse basin but
not the refined basin.
-/
def BasinExchangeObstruction
    (cell : RepairRefinementBasinCell)
    (coarseBasis refinedBasis : BridgeComponent -> Prop)
    (plan : HandoffRepairPlan) : Prop :=
  SameVisibleLocalRepairRefinementProjection cell /\
    OverlapObstructionBasis cell.coarsePath coarseBasis /\
    OverlapObstructionBasis cell.refinedPath refinedBasis /\
    HandoffCechRepairObligation cell.coarsePath plan /\
    Not (HandoffCechRepairObligation cell.refinedPath plan)

/-- The selected trace-only plan witnesses repair-basin exchange obstruction. -/
theorem repairRefinement_basinExchangeObstruction :
    BasinExchangeObstruction
      selectedRepairRefinementBasinCell
      repairRefinementCoarseBasis
      repairRefinementRefinedBasis
      traceOnlyRepairPlan := by
  exact
    ⟨repairRefinement_paths_same_visibleLocal,
      coarsePath_overlapBasis,
      refinedPath_overlapBasis,
      traceOnlyRepairPlan_clears_coarseBasin,
      traceOnlyRepairPlan_fails_refinedBasin⟩

/--
The visible repair/refinement projection is not faithful to protected
repair-basin exchange: the selected trace-only plan has the same visible/local
cell but separates coarse and refined selected basin membership.
-/
theorem visibleRepairRefinement_not_faithful_to_basinExchange :
    SameVisibleLocalRepairRefinementProjection
        selectedRepairRefinementBasinCell /\
      RepairBasinMembership
        selectedRepairRefinementBasinCell.coarsePath
        repairRefinementCoarseBasis
        traceOnlyRepairPlan /\
      Not
        (RepairBasinMembership
          selectedRepairRefinementBasinCell.refinedPath
          repairRefinementRefinedBasis
          traceOnlyRepairPlan) /\
      BasinExchangeObstruction
        selectedRepairRefinementBasinCell
        repairRefinementCoarseBasis
        repairRefinementRefinedBasis
        traceOnlyRepairPlan := by
  refine
    ⟨repairRefinement_paths_same_visibleLocal,
      ⟨coarsePath_overlapBasis, traceOnlyRepairPlan_clears_coarseBasin⟩,
      ?_,
      repairRefinement_basinExchangeObstruction⟩
  intro hrefined
  exact traceOnlyRepairPlan_fails_refinedBasin hrefined.2

/-! ## Theorem package -/

/--
Cycle-68 theorem package: a selected finite repair/refinement exchange cell has
same visible/local projection, exact coarse and refined overlap bases, common
clearance iff union-basis hitting for component-complete plans, and a trace-only
finite witness showing visible projection is not faithful to protected
repair-basin exchange.
-/
theorem repairBasinExchangeObstruction_package :
    SameVisibleLocalRepairRefinementProjection
        selectedRepairRefinementBasinCell /\
      OverlapObstructionBasis
        selectedRepairRefinementBasinCell.coarsePath
        repairRefinementCoarseBasis /\
      OverlapObstructionBasis
        selectedRepairRefinementBasinCell.refinedPath
        repairRefinementRefinedBasis /\
      (forall {plan : HandoffRepairPlan},
        ComponentCompleteHandoffRepairPlan
            selectedRepairRefinementBasinCell.coarsePath.overlapCocycle
            plan ->
          ComponentCompleteHandoffRepairPlan
            selectedRepairRefinementBasinCell.refinedPath.overlapCocycle
            plan ->
          (CommonRepairBasinClearance
              selectedRepairRefinementBasinCell plan <->
            OverlapBasisTransversal
              repairRefinementUnionBasis plan.touched)) /\
      HandoffCechRepairObligation
        selectedRepairRefinementBasinCell.coarsePath
        traceOnlyRepairPlan /\
      Not
        (HandoffCechRepairObligation
          selectedRepairRefinementBasinCell.refinedPath
          traceOnlyRepairPlan) /\
      BasinExchangeObstruction
        selectedRepairRefinementBasinCell
        repairRefinementCoarseBasis
        repairRefinementRefinedBasis
        traceOnlyRepairPlan /\
      (SameVisibleLocalRepairRefinementProjection
          selectedRepairRefinementBasinCell /\
        RepairBasinMembership
          selectedRepairRefinementBasinCell.coarsePath
          repairRefinementCoarseBasis
          traceOnlyRepairPlan /\
        Not
          (RepairBasinMembership
            selectedRepairRefinementBasinCell.refinedPath
            repairRefinementRefinedBasis
            traceOnlyRepairPlan) /\
        BasinExchangeObstruction
          selectedRepairRefinementBasinCell
          repairRefinementCoarseBasis
          repairRefinementRefinedBasis
          traceOnlyRepairPlan) := by
  exact
    ⟨repairRefinement_paths_same_visibleLocal,
      coarsePath_overlapBasis,
      refinedPath_overlapBasis,
      fun {plan} hcoarse hrefined =>
        commonClearance_iff_hits_unionBasis
          (plan := plan) hcoarse hrefined,
      traceOnlyRepairPlan_clears_coarseBasin,
      traceOnlyRepairPlan_fails_refinedBasin,
      repairRefinement_basinExchangeObstruction,
      visibleRepairRefinement_not_faithful_to_basinExchange⟩

end RepairBasinExchangeObstruction
end QualitySurface
end Formal.AG.Research
