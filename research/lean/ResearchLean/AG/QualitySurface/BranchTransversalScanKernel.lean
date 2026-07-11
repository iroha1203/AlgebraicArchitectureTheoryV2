import ResearchLean.AG.QualitySurface.NaiveRefinementSupportCounterexample

/-!
Cycle 72 evidence for `G-aat-quality-surface-01`.

This file turns the selected repair/refinement exchange branch obligation into
a selector-relative finite scan kernel.  The returned residual is canonical
only relative to the supplied selected branch-code order.  The construction is
relative to the selected finite exchange family, declared repair support, and
visible component-union projection.  It does not assert global minimal repair,
runtime repair synthesis, source extraction completeness, ArchMap correctness,
arbitrary route enumeration, global sheaf completeness, or whole-codebase
quality.
-/

namespace ResearchLean.AG
namespace QualitySurface
namespace BranchTransversalScanKernel

open HeterogeneousRouteInteraction
open HeterogeneousRouteInteraction.BridgeComponent
open HandoffRepairTransversalTheorem
open RepairBasinExchangeObstruction
open AntichainOverlapBasisTransversal
open CurvatureBasisExchange
open NaiveRefinementSupportCounterexample

instance traceOnlyRepairPlan_touched_decidable :
    DecidablePred traceOnlyRepairPlan.touched := by
  intro component
  cases component <;>
    simp [traceOnlyRepairPlan, singletonRepairSupport] <;>
    infer_instance

/-! ## Selected branch-code scan -/

/-- Selector codes for the selected path-indexed exchange branches. -/
inductive SelectedScanBranch where
  | coarseTrace
  | refinedTrace
  | refinedRepairFrontier
deriving DecidableEq

/-- Interpret a selected scan code as its path-indexed exchange branch. -/
def SelectedScanBranch.branch : SelectedScanBranch -> ExchangeBranchSupport
  | coarseTrace => coarseTraceExchangeBranch
  | refinedTrace => refinedTraceExchangeBranch
  | refinedRepairFrontier => refinedRepairFrontierExchangeBranch

/-- The selected finite order used by the scan kernel. -/
def selectedScanOrder : List SelectedScanBranch :=
  [SelectedScanBranch.coarseTrace,
    SelectedScanBranch.refinedTrace,
    SelectedScanBranch.refinedRepairFrontier]

/-- The selected branch codes cover exactly the selected exchange branch family. -/
def selectedScanBranchFamily
    (branch : ExchangeBranchSupport) : Prop :=
  exists code,
    code ∈ selectedScanOrder /\
      SelectedScanBranch.branch code = branch

/-- The selector-code family enumerates exactly the selected basis-exchange family. -/
theorem selectedScanBranchFamily_complete
    (branch : ExchangeBranchSupport) :
    selectedScanBranchFamily branch <->
      selectedBasisExchangeFamily branch := by
  constructor
  · intro hbranch
    rcases hbranch with ⟨code, _hmem, hcode⟩
    cases code <;> simp [SelectedScanBranch.branch] at hcode
    · subst branch
      exact Or.inl rfl
    · subst branch
      exact Or.inr (Or.inl rfl)
    · subst branch
      exact Or.inr (Or.inr rfl)
  · intro hbranch
    rcases hbranch with hbranch | hbranch
    · subst branch
      exact
        ⟨SelectedScanBranch.coarseTrace,
          by simp [selectedScanOrder],
          rfl⟩
    · rcases hbranch with hbranch | hbranch
      · subst branch
        exact
          ⟨SelectedScanBranch.refinedTrace,
            by simp [selectedScanOrder],
            rfl⟩
      · subst branch
        exact
          ⟨SelectedScanBranch.refinedRepairFrontier,
            by simp [selectedScanOrder],
            rfl⟩

/-- The supplied selected scan order lists every selected branch code. -/
theorem selectedScanOrder_covers
    (code : SelectedScanBranch) :
    code ∈ selectedScanOrder := by
  cases code <;> simp [selectedScanOrder]

/-- A selected scan branch is hit by a repair support. -/
def selectedScanBranchHit
    (support : HandoffRepairSupport) :
    SelectedScanBranch -> Prop
  | SelectedScanBranch.coarseTrace => support BridgeComponent.trace
  | SelectedScanBranch.refinedTrace => support BridgeComponent.trace
  | SelectedScanBranch.refinedRepairFrontier =>
      support BridgeComponent.repairFrontier

/-- Branch-code hit predicates are decidable when the component support is decidable. -/
instance selectedScanBranchHit_decidable
    (support : HandoffRepairSupport)
    [DecidablePred support]
    (code : SelectedScanBranch) :
    Decidable (selectedScanBranchHit support code) := by
  cases code <;>
    simp [selectedScanBranchHit] <;>
    infer_instance

/-- Hitting the selected branch code is the same as hitting its exchange branch. -/
theorem selectedScanBranchHit_iff_exchangeHit
    (support : HandoffRepairSupport)
    (code : SelectedScanBranch) :
    selectedScanBranchHit support code <->
      exists component,
        SelectedScanBranch.branch code component /\ support component.2 := by
  cases code
  · constructor
    · intro htrace
      exact
        ⟨(ExchangeSide.coarse, BridgeComponent.trace),
          ⟨rfl, rfl⟩,
          htrace⟩
    · intro hhit
      rcases hhit with ⟨component, hbranch, htouched⟩
      rcases component with ⟨side, component⟩
      rcases hbranch with ⟨_hside, hcomponent⟩
      have hcomponentTrace :
          component = BridgeComponent.trace := by
        simpa [SelectedScanBranch.branch, coarseTraceExchangeBranch,
          liftBranchToExchangeSide, traceBranch, singletonRepairSupport]
          using hcomponent
      subst component
      exact htouched
  · constructor
    · intro htrace
      exact
        ⟨(ExchangeSide.refined, BridgeComponent.trace),
          ⟨rfl, rfl⟩,
          htrace⟩
    · intro hhit
      rcases hhit with ⟨component, hbranch, htouched⟩
      rcases component with ⟨side, component⟩
      rcases hbranch with ⟨_hside, hcomponent⟩
      have hcomponentTrace :
          component = BridgeComponent.trace := by
        simpa [SelectedScanBranch.branch, refinedTraceExchangeBranch,
          liftBranchToExchangeSide, traceBranch, singletonRepairSupport]
          using hcomponent
      subst component
      exact htouched
  · constructor
    · intro hrepair
      exact
        ⟨(ExchangeSide.refined, BridgeComponent.repairFrontier),
          ⟨rfl, rfl⟩,
          hrepair⟩
    · intro hhit
      rcases hhit with ⟨component, hbranch, htouched⟩
      rcases component with ⟨side, component⟩
      rcases hbranch with ⟨_hside, hcomponent⟩
      have hcomponentRepair :
          component = BridgeComponent.repairFrontier := by
        simpa [SelectedScanBranch.branch,
          refinedRepairFrontierExchangeBranch,
          liftBranchToExchangeSide, repairFrontierBranch,
          singletonRepairSupport] using hcomponent
      subst component
      exact htouched

/-- All listed selected branch codes are hit by the support. -/
def ListedSelectedBranchesHit
    (support : HandoffRepairSupport)
    (codes : List SelectedScanBranch) : Prop :=
  forall code, code ∈ codes -> selectedScanBranchHit support code

/-- First missed selected branch code in the supplied order. -/
def firstMissedSelectedBranch?
    (support : HandoffRepairSupport)
    [DecidablePred support] :
    List SelectedScanBranch -> Option SelectedScanBranch
  | [] => none
  | code :: rest =>
      if selectedScanBranchHit support code then
        firstMissedSelectedBranch? support rest
      else
        some code

/-- A returned selected residual is a member of the supplied order. -/
theorem firstMissedSelectedBranch?_some_mem
    (support : HandoffRepairSupport)
    [DecidablePred support] :
    forall {codes : List SelectedScanBranch} {code : SelectedScanBranch},
      firstMissedSelectedBranch? support codes = some code ->
        code ∈ codes
  | [], _code, hsome => by
      cases hsome
  | head :: rest, code, hsome => by
      by_cases hhead : selectedScanBranchHit support head
      · have htail :
            firstMissedSelectedBranch? support rest = some code := by
          simpa [firstMissedSelectedBranch?, hhead] using hsome
        exact List.mem_cons_of_mem head
          (firstMissedSelectedBranch?_some_mem support htail)
      · have hcode : code = head := by
          simpa [firstMissedSelectedBranch?, hhead] using hsome.symm
        subst hcode
        simp

/-- A returned selected residual is really missed by the supplied support. -/
theorem firstMissedSelectedBranch?_some_missed
    (support : HandoffRepairSupport)
    [DecidablePred support] :
    forall {codes : List SelectedScanBranch} {code : SelectedScanBranch},
      firstMissedSelectedBranch? support codes = some code ->
        Not (selectedScanBranchHit support code)
  | [], _code, hsome => by
      cases hsome
  | head :: rest, code, hsome => by
      by_cases hhead : selectedScanBranchHit support head
      · have htail :
            firstMissedSelectedBranch? support rest = some code := by
          simpa [firstMissedSelectedBranch?, hhead] using hsome
        exact firstMissedSelectedBranch?_some_missed support htail
      · have hcode : code = head := by
          simpa [firstMissedSelectedBranch?, hhead] using hsome.symm
        subst hcode
        exact hhead

/-- The selected scan returns none exactly when all listed selected codes are hit. -/
theorem firstMissedSelectedBranch?_none_iff_listedHits
    (support : HandoffRepairSupport)
    [DecidablePred support] :
    forall codes,
      firstMissedSelectedBranch? support codes = none <->
        ListedSelectedBranchesHit support codes
  | [] => by
      constructor
      · intro _ code hmem
        cases hmem
      · intro _
        rfl
  | head :: rest => by
      constructor
      · intro hnone code hmem
        by_cases hhead : selectedScanBranchHit support head
        · have htail :
              firstMissedSelectedBranch? support rest = none := by
            simpa [firstMissedSelectedBranch?, hhead] using hnone
          cases hmem with
          | head =>
              exact hhead
          | tail _ hlisted =>
              exact
                ((firstMissedSelectedBranch?_none_iff_listedHits
                  support rest).mp htail) code hlisted
        · have hsome :
              firstMissedSelectedBranch? support (head :: rest) =
                some head := by
            simp [firstMissedSelectedBranch?, hhead]
          rw [hsome] at hnone
          cases hnone
      · intro hall
        have hhead : selectedScanBranchHit support head := hall head (by simp)
        have htail :
            ListedSelectedBranchesHit support rest := by
          intro code hmem
          exact hall code (by simp [hmem])
        have htailNone :
            firstMissedSelectedBranch? support rest = none :=
          (firstMissedSelectedBranch?_none_iff_listedHits
            support rest).mpr htail
        simp [firstMissedSelectedBranch?, hhead, htailNone]

/-! ## Exact residual criterion for selected exchange transversality -/

/--
The selected scan has no residual exactly when the selected exchange branch
family is hit by the declared support.
-/
theorem firstMissedSelectedBranch?_none_iff_transversal
    (support : HandoffRepairSupport)
    [DecidablePred support] :
    firstMissedSelectedBranch? support selectedScanOrder = none <->
      ExchangeBranchRepairTransversal
        selectedBasisExchangeFamily support := by
  constructor
  · intro hnone branch hbranch
    have hall :
        ListedSelectedBranchesHit support selectedScanOrder :=
      (firstMissedSelectedBranch?_none_iff_listedHits
        support selectedScanOrder).mp hnone
    rcases hbranch with hbranch | hbranch
    · subst branch
      exact
        (selectedScanBranchHit_iff_exchangeHit support
          SelectedScanBranch.coarseTrace).mp
          (hall SelectedScanBranch.coarseTrace
            (by simp [selectedScanOrder]))
    · rcases hbranch with hbranch | hbranch
      · subst branch
        exact
          (selectedScanBranchHit_iff_exchangeHit support
            SelectedScanBranch.refinedTrace).mp
            (hall SelectedScanBranch.refinedTrace
              (by simp [selectedScanOrder]))
      · subst branch
        exact
          (selectedScanBranchHit_iff_exchangeHit support
            SelectedScanBranch.refinedRepairFrontier).mp
            (hall SelectedScanBranch.refinedRepairFrontier
              (by simp [selectedScanOrder]))
  · intro htransversal
    apply
      (firstMissedSelectedBranch?_none_iff_listedHits
        support selectedScanOrder).mpr
    intro code _hmem
    cases code
    · exact
        (selectedScanBranchHit_iff_exchangeHit support
          SelectedScanBranch.coarseTrace).mpr
          (htransversal coarseTraceExchangeBranch (Or.inl rfl))
    · exact
        (selectedScanBranchHit_iff_exchangeHit support
          SelectedScanBranch.refinedTrace).mpr
          (htransversal refinedTraceExchangeBranch
            (Or.inr (Or.inl rfl)))
    · exact
        (selectedScanBranchHit_iff_exchangeHit support
          SelectedScanBranch.refinedRepairFrontier).mpr
          (htransversal refinedRepairFrontierExchangeBranch
            (Or.inr (Or.inr rfl)))

/-- The trace-only support first misses the refined repair-frontier branch code. -/
theorem traceOnly_firstMissedSelectedBranch :
    firstMissedSelectedBranch? traceOnlyRepairPlan.touched
      selectedScanOrder =
        some SelectedScanBranch.refinedRepairFrontier := by
  simp [firstMissedSelectedBranch?, selectedScanOrder,
    selectedScanBranchHit, traceOnlyRepairPlan, singletonRepairSupport]

/-- The returned trace-only residual is a selected branch and is missed. -/
theorem traceOnly_firstMissedSelectedBranch_residual :
    selectedBasisExchangeFamily
        (SelectedScanBranch.branch
          SelectedScanBranch.refinedRepairFrontier) /\
      ExchangeBranchMissedBySupport
        (SelectedScanBranch.branch
          SelectedScanBranch.refinedRepairFrontier)
        traceOnlyRepairPlan.touched := by
  constructor
  · exact Or.inr (Or.inr rfl)
  · exact traceOnly_misses_refinedRepairFrontierExchangeBranch

/--
Deleting the selector-relative first residual restores trace-only
transversality for the selected finite family.
-/
theorem dropFirstMissed_restores_traceOnlyTransversal :
    firstMissedSelectedBranch? traceOnlyRepairPlan.touched
        selectedScanOrder =
          some SelectedScanBranch.refinedRepairFrontier /\
      ExchangeBranchRepairTransversal
        (exchangeBranchFamilyDrops selectedBasisExchangeFamily
          (SelectedScanBranch.branch
            SelectedScanBranch.refinedRepairFrontier))
        traceOnlyRepairPlan.touched := by
  exact
    ⟨traceOnly_firstMissedSelectedBranch,
      by
        simpa [SelectedScanBranch.branch, reflectedSelectedBranchFamily,
          reflectedRepairFrontierSingleton]
          using dropRefinedRepairFrontier_restores_traceOnlyTransversal⟩

/-! ## Visible-equivalent kernel pair -/

/-- Selector code for the collapsed visible branch. -/
inductive CollapsedVisibleScanBranch where
  | collapsed
deriving DecidableEq

/-- Interpret the collapsed visible code as its exchange branch. -/
def CollapsedVisibleScanBranch.branch :
    CollapsedVisibleScanBranch -> ExchangeBranchSupport
  | CollapsedVisibleScanBranch.collapsed => collapsedVisibleExchangeBranch

/-- The singleton visible scan order for the collapsed reading. -/
def collapsedVisibleScanOrder : List CollapsedVisibleScanBranch :=
  [CollapsedVisibleScanBranch.collapsed]

/-- The collapsed visible branch is hit when trace or repair-frontier is hit. -/
def collapsedVisibleScanBranchHit
    (support : HandoffRepairSupport) :
    CollapsedVisibleScanBranch -> Prop
  | CollapsedVisibleScanBranch.collapsed =>
      support BridgeComponent.trace \/
        support BridgeComponent.repairFrontier

/-- Collapsed visible hit predicates are decidable when the support is decidable. -/
instance collapsedVisibleScanBranchHit_decidable
    (support : HandoffRepairSupport)
    [DecidablePred support]
    (code : CollapsedVisibleScanBranch) :
    Decidable (collapsedVisibleScanBranchHit support code) := by
  cases code
  change
    Decidable
      (support BridgeComponent.trace \/
        support BridgeComponent.repairFrontier)
  infer_instance

/-- First missed branch for the collapsed visible reading. -/
def firstMissedCollapsedVisibleBranch?
    (support : HandoffRepairSupport)
    [DecidablePred support] :
    List CollapsedVisibleScanBranch -> Option CollapsedVisibleScanBranch
  | [] => none
  | code :: rest =>
      if collapsedVisibleScanBranchHit support code then
        firstMissedCollapsedVisibleBranch? support rest
      else
        some code

/-- The trace-only support has no residual for the collapsed visible reading. -/
theorem collapsedVisible_firstMissedBranch_traceOnly :
    firstMissedCollapsedVisibleBranch? traceOnlyRepairPlan.touched
      collapsedVisibleScanOrder = none := by
  simp [firstMissedCollapsedVisibleBranch?,
    collapsedVisibleScanOrder, collapsedVisibleScanBranchHit,
    traceOnlyRepairPlan, singletonRepairSupport]

/--
Selected and collapsed readings have the same visible component union, but the
selector scan returns different residual behavior for trace-only repair.
-/
theorem visibleEquivalent_residualKernelPair :
    (forall component,
      ExchangeVisibleUnion selectedBasisExchangeFamily component <->
        ExchangeVisibleUnion collapsedVisibleExchangeFamily component) /\
      firstMissedSelectedBranch? traceOnlyRepairPlan.touched
        selectedScanOrder =
          some SelectedScanBranch.refinedRepairFrontier /\
      firstMissedCollapsedVisibleBranch? traceOnlyRepairPlan.touched
        collapsedVisibleScanOrder = none := by
  exact
    ⟨selected_collapsed_same_visibleUnion,
      traceOnly_firstMissedSelectedBranch,
      collapsedVisible_firstMissedBranch_traceOnly⟩

/--
The visible component-union projection is not faithful to the branch scan
kernel: the visible-equivalent selected and collapsed readings differ on the
trace-only residual scan.
-/
theorem visibleUnion_not_faithful_to_branchScanKernel :
    (forall component,
      ExchangeVisibleUnion selectedBasisExchangeFamily component <->
        ExchangeVisibleUnion collapsedVisibleExchangeFamily component) /\
      firstMissedSelectedBranch? traceOnlyRepairPlan.touched
        selectedScanOrder =
          some SelectedScanBranch.refinedRepairFrontier /\
      firstMissedCollapsedVisibleBranch? traceOnlyRepairPlan.touched
        collapsedVisibleScanOrder = none /\
      Not
        (ExchangeBranchRepairTransversal
          selectedBasisExchangeFamily traceOnlyRepairPlan.touched) /\
      ExchangeBranchRepairTransversal
        collapsedVisibleExchangeFamily traceOnlyRepairPlan.touched := by
  exact
    ⟨selected_collapsed_same_visibleUnion,
      traceOnly_firstMissedSelectedBranch,
      collapsedVisible_firstMissedBranch_traceOnly,
      traceOnly_not_hits_selectedBasisExchange,
      traceOnly_hits_collapsedVisibleExchange⟩

/-! ## Theorem package -/

/--
Cycle-72 theorem package: selected path-indexed repair obligations have a
selector-relative scan kernel, and visible component union cannot recover the
kernel residual.
-/
theorem branchTransversalScanKernel_package :
    (forall branch,
      selectedScanBranchFamily branch <->
        selectedBasisExchangeFamily branch) /\
      (forall (support : HandoffRepairSupport) [DecidablePred support],
        firstMissedSelectedBranch? support selectedScanOrder = none <->
          ExchangeBranchRepairTransversal
            selectedBasisExchangeFamily support) /\
      (firstMissedSelectedBranch? traceOnlyRepairPlan.touched
        selectedScanOrder =
          some SelectedScanBranch.refinedRepairFrontier) /\
      (selectedBasisExchangeFamily
          (SelectedScanBranch.branch
            SelectedScanBranch.refinedRepairFrontier) /\
        ExchangeBranchMissedBySupport
          (SelectedScanBranch.branch
            SelectedScanBranch.refinedRepairFrontier)
          traceOnlyRepairPlan.touched) /\
      ExchangeBranchRepairTransversal
        (exchangeBranchFamilyDrops selectedBasisExchangeFamily
          (SelectedScanBranch.branch
            SelectedScanBranch.refinedRepairFrontier))
        traceOnlyRepairPlan.touched /\
      ((forall component,
        ExchangeVisibleUnion selectedBasisExchangeFamily component <->
          ExchangeVisibleUnion collapsedVisibleExchangeFamily component) /\
        firstMissedSelectedBranch? traceOnlyRepairPlan.touched
          selectedScanOrder =
            some SelectedScanBranch.refinedRepairFrontier /\
        firstMissedCollapsedVisibleBranch? traceOnlyRepairPlan.touched
          collapsedVisibleScanOrder = none /\
        Not
          (ExchangeBranchRepairTransversal
            selectedBasisExchangeFamily traceOnlyRepairPlan.touched) /\
        ExchangeBranchRepairTransversal
          collapsedVisibleExchangeFamily traceOnlyRepairPlan.touched) := by
  exact
    ⟨selectedScanBranchFamily_complete,
      firstMissedSelectedBranch?_none_iff_transversal,
      traceOnly_firstMissedSelectedBranch,
      traceOnly_firstMissedSelectedBranch_residual,
      dropFirstMissed_restores_traceOnlyTransversal.2,
      visibleUnion_not_faithful_to_branchScanKernel⟩

end BranchTransversalScanKernel
end QualitySurface
end ResearchLean.AG
