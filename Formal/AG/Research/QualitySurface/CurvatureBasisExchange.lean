import Formal.AG.Research.QualitySurface.AntichainOverlapBasisTransversal

/-!
Cycle 70 evidence for `G-aat-quality-surface-01`.

This file reads the selected repair/refinement exchange cell as a
path-indexed Cech branch exchange object.  The protected datum is not merely
the visible union of bridge components; it is a branch family over
`ExchangeSide × BridgeComponent`.  The construction remains relative to the
selected finite repair/refinement cell, exact selected Cech overlap bases, and
declared repair predicates.  It does not assert global matroid basis exchange,
canonical atlas refinement, runtime repair synthesis, source extraction
completeness, ArchMap correctness, arbitrary route enumeration, global sheaf
completeness, or whole-codebase quality.
-/

namespace Formal.AG.Research
namespace QualitySurface
namespace CurvatureBasisExchange

open HeterogeneousRouteInteraction
open HeterogeneousRouteInteraction.BridgeComponent
open HandoffRepairTransversalTheorem
open HandoffCechExactness
open HandoffCechOverlapBasis
open RepairTransportCechCommutatorCurvature
open RepairBasinExchangeObstruction
open AntichainOverlapBasisTransversal

/-! ## Path-indexed exchange branches -/

/-- Which side of the selected repair/refinement exchange cell a branch belongs to. -/
inductive ExchangeSide where
  | coarse
  | refined
deriving DecidableEq

/-- A protected exchange component remembers both path side and bridge component. -/
abbrev ExchangeComponent := ExchangeSide × BridgeComponent

/-- A selected path-indexed exchange branch. -/
abbrev ExchangeBranchSupport := ExchangeComponent -> Prop

/-- A selected family of path-indexed exchange branches. -/
abbrev ExchangeBranchFamily := ExchangeBranchSupport -> Prop

/-- Lift an existing bridge-component branch onto one exchange side. -/
def liftBranchToExchangeSide
    (side : ExchangeSide)
    (branch : BranchSupport) : ExchangeBranchSupport :=
  fun component => component.1 = side /\ branch component.2

/-- The coarse trace exchange branch. -/
def coarseTraceExchangeBranch : ExchangeBranchSupport :=
  liftBranchToExchangeSide ExchangeSide.coarse traceBranch

/-- The refined trace exchange branch. -/
def refinedTraceExchangeBranch : ExchangeBranchSupport :=
  liftBranchToExchangeSide ExchangeSide.refined traceBranch

/-- The refined repair-frontier exchange branch. -/
def refinedRepairFrontierExchangeBranch : ExchangeBranchSupport :=
  liftBranchToExchangeSide ExchangeSide.refined repairFrontierBranch

/--
The selected path-indexed basis-exchange family: one coarse trace branch and
two refined branches.
-/
def selectedBasisExchangeFamily
    (branch : ExchangeBranchSupport) : Prop :=
  branch = coarseTraceExchangeBranch \/
    branch = refinedTraceExchangeBranch \/
      branch = refinedRepairFrontierExchangeBranch

/--
The coarser visible exchange family forgets the path side and remembers one
paired branch over trace and repair-frontier components.
-/
def collapsedVisibleExchangeBranch
    (component : ExchangeComponent) : Prop :=
  component.2 = BridgeComponent.trace \/
    component.2 = BridgeComponent.repairFrontier

/-- A singleton visible family containing the collapsed trace / repair-frontier branch. -/
def collapsedVisibleExchangeFamily
    (branch : ExchangeBranchSupport) : Prop :=
  branch = collapsedVisibleExchangeBranch

/-- The component-union projection of an exchange branch family forgets `ExchangeSide`. -/
def ExchangeVisibleUnion
    (family : ExchangeBranchFamily)
    (component : BridgeComponent) : Prop :=
  exists branch,
    family branch /\ exists side, branch (side, component)

/-- A declared repair support hits every selected path-indexed exchange branch. -/
def ExchangeBranchRepairTransversal
    (family : ExchangeBranchFamily)
    (support : HandoffRepairSupport) : Prop :=
  forall branch,
    family branch -> exists component, branch component /\ support component.2

/-- A selected exchange branch is missed by a declared component repair support. -/
def ExchangeBranchMissedBySupport
    (branch : ExchangeBranchSupport)
    (support : HandoffRepairSupport) : Prop :=
  forall component, branch component -> Not (support component.2)

/-- Declared residual exchange-branch support after a repair plan. -/
def DeclaredResidualExchangeBranchSupport
    (family : ExchangeBranchFamily)
    (plan : HandoffRepairPlan)
    (branch : ExchangeBranchSupport) : Prop :=
  family branch /\
    forall component, branch component -> Not (plan.clears component.2)

/-- Common clearance of the selected repair/refinement exchange cell. -/
def CommonExchangeClearance
    (plan : HandoffRepairPlan) : Prop :=
  CommonRepairBasinClearance selectedRepairRefinementBasinCell plan

/-! ## Exact side bases grounding the exchange family -/

/-- The coarse side has a singleton trace branch family. -/
def coarseTraceBranchFamily
    (branch : BranchSupport) : Prop :=
  branch = traceBranch

theorem coarseTraceBranchFamily_antichain :
    BranchFamilyAntichain coarseTraceBranchFamily := by
  intro left right hleft hright _hsubset component hrightComponent
  subst left
  subst right
  exact hrightComponent

theorem coarseTraceBranchFamily_nonempty
    (branch : BranchSupport)
    (hbranch : coarseTraceBranchFamily branch) :
    BranchNonempty branch := by
  subst branch
  exact ⟨BridgeComponent.trace, rfl⟩

theorem coarseTraceBranchFamily_sound :
    BranchFamilySound repairRefinementCoarseBasis
      coarseTraceBranchFamily := by
  intro branch hbranch component hcomponent
  subst branch
  simpa [repairRefinementCoarseBasis, traceBranch] using hcomponent

theorem coarseTraceBranchFamily_generates :
    BranchFamilyUnionGenerates repairRefinementCoarseBasis
      coarseTraceBranchFamily := by
  intro component hbasis
  exact
    ⟨traceBranch, rfl,
      by simpa [repairRefinementCoarseBasis, traceBranch] using hbasis⟩

/-- The selected coarse Cech overlap basis grounds the coarse trace branch. -/
theorem coarseTrace_antichainCechOverlapBasis :
    AntichainCechOverlapBasis
      selectedRepairRefinementBasinCell.coarsePath
      repairRefinementCoarseBasis
      coarseTraceBranchFamily := by
  exact
    ⟨coarsePath_overlapBasis,
      coarseTraceBranchFamily_antichain,
      coarseTraceBranchFamily_nonempty,
      coarseTraceBranchFamily_sound,
      coarseTraceBranchFamily_generates⟩

/-- The selected refined Cech overlap basis grounds the two singleton branches. -/
theorem refinedTwoSingleton_antichainCechOverlapBasis :
    AntichainCechOverlapBasis
      selectedRepairRefinementBasinCell.refinedPath
      repairRefinementRefinedBasis
      twoSingletonBranchFamily := by
  simpa [selectedRepairRefinementBasinCell, repairRefinementRefinedBasis]
    using twoSingleton_antichainCechOverlapBasis

/-- The selected basis-exchange branches are grounded side-wise in exact Cech bases. -/
theorem selectedBasisExchange_exact :
    AntichainCechOverlapBasis
        selectedRepairRefinementBasinCell.coarsePath
        repairRefinementCoarseBasis
        coarseTraceBranchFamily /\
      AntichainCechOverlapBasis
        selectedRepairRefinementBasinCell.refinedPath
        repairRefinementRefinedBasis
        twoSingletonBranchFamily := by
  exact
    ⟨coarseTrace_antichainCechOverlapBasis,
      refinedTwoSingleton_antichainCechOverlapBasis⟩

/--
Every selected exchange branch is the side lift of a branch grounded on either
the coarse trace basis or the refined two-singleton basis.
-/
theorem selectedBasisExchangeFamily_sideGrounded
    {branch : ExchangeBranchSupport}
    (hbranch : selectedBasisExchangeFamily branch) :
    (exists baseBranch,
      coarseTraceBranchFamily baseBranch /\
        branch = liftBranchToExchangeSide ExchangeSide.coarse baseBranch) \/
      (exists baseBranch,
        twoSingletonBranchFamily baseBranch /\
          branch = liftBranchToExchangeSide ExchangeSide.refined baseBranch) := by
  rcases hbranch with hbranch | hbranch
  · subst branch
    exact Or.inl ⟨traceBranch, rfl, rfl⟩
  · rcases hbranch with hbranch | hbranch
    · subst branch
      exact Or.inr ⟨traceBranch, Or.inl rfl, rfl⟩
    · subst branch
      exact Or.inr ⟨repairFrontierBranch, Or.inr rfl, rfl⟩

/-! ## Exchange clearance and visible-projection loss -/

/--
For component-complete repair plans, common clearance of the selected
repair/refinement exchange cell is equivalent to hitting every selected
path-indexed exchange branch.
-/
theorem commonClearance_iff_hits_selectedBasisExchange
    {plan : HandoffRepairPlan}
    (hcoarseComplete :
      ComponentCompleteHandoffRepairPlan
        selectedRepairRefinementBasinCell.coarsePath.overlapCocycle plan)
    (hrefinedComplete :
      ComponentCompleteHandoffRepairPlan
        selectedRepairRefinementBasinCell.refinedPath.overlapCocycle plan) :
    CommonExchangeClearance plan <->
      ExchangeBranchRepairTransversal
        selectedBasisExchangeFamily plan.touched := by
  constructor
  · intro hclear branch hbranch
    rcases hbranch with hbranch | hbranch
    · subst branch
      have hhit :
          OverlapBasisTransversal repairRefinementCoarseBasis
            plan.touched :=
        (declaredClearance_iff_hitsEveryOverlapBasis_of_componentComplete
          (cover := selectedRepairRefinementBasinCell.coarsePath)
          (basis := repairRefinementCoarseBasis)
          (plan := plan)
          coarsePath_overlapBasis
          hcoarseComplete).mp hclear.1
      exact
        ⟨(ExchangeSide.coarse, BridgeComponent.trace),
          ⟨rfl, rfl⟩,
          hhit BridgeComponent.trace rfl⟩
    · rcases hbranch with hbranch | hbranch
      · subst branch
        have hhit :
            OverlapBasisTransversal repairRefinementRefinedBasis
              plan.touched :=
          (declaredClearance_iff_hitsEveryOverlapBasis_of_componentComplete
            (cover := selectedRepairRefinementBasinCell.refinedPath)
            (basis := repairRefinementRefinedBasis)
            (plan := plan)
            refinedPath_overlapBasis
            hrefinedComplete).mp hclear.2
        exact
          ⟨(ExchangeSide.refined, BridgeComponent.trace),
            ⟨rfl, rfl⟩,
            hhit BridgeComponent.trace (Or.inl rfl)⟩
      · subst branch
        have hhit :
            OverlapBasisTransversal repairRefinementRefinedBasis
              plan.touched :=
          (declaredClearance_iff_hitsEveryOverlapBasis_of_componentComplete
            (cover := selectedRepairRefinementBasinCell.refinedPath)
            (basis := repairRefinementRefinedBasis)
            (plan := plan)
            refinedPath_overlapBasis
            hrefinedComplete).mp hclear.2
        exact
          ⟨(ExchangeSide.refined, BridgeComponent.repairFrontier),
            ⟨rfl, rfl⟩,
            hhit BridgeComponent.repairFrontier (Or.inr rfl)⟩
  · intro hhit
    exact
      (commonClearance_iff_hits_unionBasis
        (plan := plan) hcoarseComplete hrefinedComplete).mpr
        (by
          intro component hbasis
          rcases hbasis with hcoarse | hrefined
          · rcases
              hhit coarseTraceExchangeBranch (Or.inl rfl) with
              ⟨exchangeComponent, hbranch, htouched⟩
            rcases exchangeComponent with ⟨side, touchedComponent⟩
            rcases hbranch with ⟨_hside, hcomponent⟩
            subst component
            have htouchedComponent :
                touchedComponent = BridgeComponent.trace := by
              simpa [traceBranch, singletonRepairSupport] using hcomponent
            subst touchedComponent
            simpa using htouched
          · rcases hrefined with htrace | hrepair
            · rcases
                hhit refinedTraceExchangeBranch
                  (Or.inr (Or.inl rfl)) with
                ⟨exchangeComponent, hbranch, htouched⟩
              rcases exchangeComponent with ⟨side, touchedComponent⟩
              rcases hbranch with ⟨_hside, hcomponent⟩
              subst component
              have htouchedComponent :
                  touchedComponent = BridgeComponent.trace := by
                simpa [traceBranch, singletonRepairSupport] using hcomponent
              subst touchedComponent
              simpa using htouched
            · rcases
                hhit refinedRepairFrontierExchangeBranch
                  (Or.inr (Or.inr rfl)) with
                ⟨exchangeComponent, hbranch, htouched⟩
              rcases exchangeComponent with ⟨side, touchedComponent⟩
              rcases hbranch with ⟨_hside, hcomponent⟩
              subst component
              have htouchedComponent :
                  touchedComponent = BridgeComponent.repairFrontier := by
                simpa [repairFrontierBranch, singletonRepairSupport] using hcomponent
              subst touchedComponent
              simpa using htouched)

/--
The selected path-indexed family and the collapsed visible family have the
same visible component-union projection.
-/
theorem selected_collapsed_same_visibleUnion
    (component : BridgeComponent) :
    ExchangeVisibleUnion selectedBasisExchangeFamily component <->
      ExchangeVisibleUnion collapsedVisibleExchangeFamily component := by
  constructor
  · intro hunion
    rcases hunion with ⟨branch, hfamily, side, hcomponent⟩
    rcases hfamily with hfamily | hfamily
    · subst branch
      exact
        ⟨collapsedVisibleExchangeBranch, rfl, side,
          Or.inl hcomponent.2⟩
    · rcases hfamily with hfamily | hfamily
      · subst branch
        exact
          ⟨collapsedVisibleExchangeBranch, rfl, side,
            Or.inl hcomponent.2⟩
      · subst branch
        exact
          ⟨collapsedVisibleExchangeBranch, rfl, side,
            Or.inr hcomponent.2⟩
  · intro hunion
    rcases hunion with ⟨branch, hfamily, side, hcomponent⟩
    subst branch
    rcases hcomponent with htrace | hrepair
    · exact
        ⟨coarseTraceExchangeBranch, Or.inl rfl,
          ExchangeSide.coarse, ⟨rfl, htrace⟩⟩
    · exact
        ⟨refinedRepairFrontierExchangeBranch,
          Or.inr (Or.inr rfl),
          ExchangeSide.refined, ⟨rfl, hrepair⟩⟩

/-- The trace-only plan hits the collapsed visible exchange branch. -/
theorem traceOnly_hits_collapsedVisibleExchange :
    ExchangeBranchRepairTransversal
      collapsedVisibleExchangeFamily traceOnlyRepairPlan.touched := by
  intro branch hbranch
  subst branch
  exact
    ⟨(ExchangeSide.coarse, BridgeComponent.trace),
      Or.inl rfl,
      rfl⟩

/-- The trace-only plan misses the refined repair-frontier exchange branch. -/
theorem traceOnly_misses_refinedRepairFrontierExchangeBranch :
    ExchangeBranchMissedBySupport refinedRepairFrontierExchangeBranch
      traceOnlyRepairPlan.touched := by
  intro component hcomponent htouched
  rcases component with ⟨side, component⟩
  exact traceOnlyRepairPlan_misses_repairFrontier
    (by
      rcases hcomponent with ⟨_hside, hrepair⟩
      have hrepairComponent :
          component = BridgeComponent.repairFrontier := by
        simpa [repairFrontierBranch, singletonRepairSupport] using hrepair
      subst component
      simpa using htouched)

/-- The trace-only plan leaves the refined repair-frontier branch as residual support. -/
theorem traceOnly_refinedRepairFrontierExchange_residual :
    DeclaredResidualExchangeBranchSupport selectedBasisExchangeFamily
      traceOnlyRepairPlan refinedRepairFrontierExchangeBranch := by
  constructor
  · exact Or.inr (Or.inr rfl)
  · intro component hcomponent hclear
    exact traceOnly_misses_refinedRepairFrontierExchangeBranch
      component hcomponent
      (traceOnlyRepairPlan.clears_only_if_touched component.2 hclear)

/-- The trace-only plan does not hit every selected path-indexed exchange branch. -/
theorem traceOnly_not_hits_selectedBasisExchange :
    Not
      (ExchangeBranchRepairTransversal
        selectedBasisExchangeFamily traceOnlyRepairPlan.touched) := by
  intro hhit
  rcases
      hhit refinedRepairFrontierExchangeBranch
        (Or.inr (Or.inr rfl)) with
    ⟨component, hcomponent, htouched⟩
  exact traceOnly_misses_refinedRepairFrontierExchangeBranch
    component hcomponent htouched

/-- The trace-only plan fails common clearance of the selected exchange cell. -/
theorem traceOnly_fails_commonExchangeClearance :
    Not (CommonExchangeClearance traceOnlyRepairPlan) := by
  intro hclear
  exact traceOnlyRepairPlan_fails_refinedBasin hclear.2

/--
Visible component union is not faithful to path-indexed basis exchange:
the selected and collapsed families have the same visible union, but the
trace-only support is a transversal only for the collapsed family.
-/
theorem sameVisibleUnion_not_faithful_to_basisExchange :
    (forall component,
      ExchangeVisibleUnion selectedBasisExchangeFamily component <->
        ExchangeVisibleUnion collapsedVisibleExchangeFamily component) /\
      ExchangeBranchRepairTransversal
        collapsedVisibleExchangeFamily traceOnlyRepairPlan.touched /\
      Not
        (ExchangeBranchRepairTransversal
          selectedBasisExchangeFamily traceOnlyRepairPlan.touched) := by
  exact
    ⟨selected_collapsed_same_visibleUnion,
      traceOnly_hits_collapsedVisibleExchange,
      traceOnly_not_hits_selectedBasisExchange⟩

/-! ## Theorem package -/

/--
Cycle-70 theorem package: the selected repair/refinement exchange cell carries
side-indexed Cech branches; component-complete common clearance is exactly
selected exchange-branch hitting; and forgetting the side index loses the
branch-transversal class.
-/
theorem curvatureBasisExchange_package :
    AntichainCechOverlapBasis
        selectedRepairRefinementBasinCell.coarsePath
        repairRefinementCoarseBasis
        coarseTraceBranchFamily /\
      AntichainCechOverlapBasis
        selectedRepairRefinementBasinCell.refinedPath
        repairRefinementRefinedBasis
        twoSingletonBranchFamily /\
      (forall {branch : ExchangeBranchSupport},
        selectedBasisExchangeFamily branch ->
          (exists baseBranch,
            coarseTraceBranchFamily baseBranch /\
              branch =
                liftBranchToExchangeSide ExchangeSide.coarse baseBranch) \/
            (exists baseBranch,
              twoSingletonBranchFamily baseBranch /\
                branch =
                  liftBranchToExchangeSide ExchangeSide.refined baseBranch)) /\
      (forall {plan : HandoffRepairPlan},
        ComponentCompleteHandoffRepairPlan
            selectedRepairRefinementBasinCell.coarsePath.overlapCocycle
            plan ->
          ComponentCompleteHandoffRepairPlan
            selectedRepairRefinementBasinCell.refinedPath.overlapCocycle
            plan ->
          (CommonExchangeClearance plan <->
            ExchangeBranchRepairTransversal
              selectedBasisExchangeFamily plan.touched)) /\
      (forall component,
        ExchangeVisibleUnion selectedBasisExchangeFamily component <->
          ExchangeVisibleUnion collapsedVisibleExchangeFamily component) /\
      ExchangeBranchRepairTransversal
        collapsedVisibleExchangeFamily traceOnlyRepairPlan.touched /\
      DeclaredResidualExchangeBranchSupport selectedBasisExchangeFamily
        traceOnlyRepairPlan refinedRepairFrontierExchangeBranch /\
      Not
        (ExchangeBranchRepairTransversal
          selectedBasisExchangeFamily traceOnlyRepairPlan.touched) /\
      Not (CommonExchangeClearance traceOnlyRepairPlan) /\
      ((forall component,
        ExchangeVisibleUnion selectedBasisExchangeFamily component <->
          ExchangeVisibleUnion collapsedVisibleExchangeFamily component) /\
        ExchangeBranchRepairTransversal
          collapsedVisibleExchangeFamily traceOnlyRepairPlan.touched /\
        Not
          (ExchangeBranchRepairTransversal
            selectedBasisExchangeFamily traceOnlyRepairPlan.touched)) := by
  exact
    ⟨coarseTrace_antichainCechOverlapBasis,
      refinedTwoSingleton_antichainCechOverlapBasis,
      fun {branch} hbranch =>
        selectedBasisExchangeFamily_sideGrounded hbranch,
      fun {plan} hcoarse hrefined =>
        commonClearance_iff_hits_selectedBasisExchange
          (plan := plan) hcoarse hrefined,
      selected_collapsed_same_visibleUnion,
      traceOnly_hits_collapsedVisibleExchange,
      traceOnly_refinedRepairFrontierExchange_residual,
      traceOnly_not_hits_selectedBasisExchange,
      traceOnly_fails_commonExchangeClearance,
      sameVisibleUnion_not_faithful_to_basisExchange⟩

end CurvatureBasisExchange
end QualitySurface
end Formal.AG.Research
