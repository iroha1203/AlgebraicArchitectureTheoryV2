import ResearchLean.AG.QualitySurface.BranchReflectionAdequacyKernel

/-!
Cycle 74 evidence for `G-aat-quality-surface-01`.

This file strengthens the selected residual scan with selector-relative prefix
exactness and singleton-deletion minimality.  The result is relative to the
selected finite scan order, trace-only declared repair support, and collapsed
visible reading.  It does not assert a global canonical repair order, global
minimal repair, runtime repair synthesis, source extraction completeness,
ArchMap correctness, global sheaf completeness, or whole-codebase quality.
-/

namespace ResearchLean.AG
namespace QualitySurface
namespace SelectedResidualScanPrefixMinimality

open HeterogeneousRouteInteraction
open HeterogeneousRouteInteraction.BridgeComponent
open HandoffRepairTransversalTheorem
open RepairBasinExchangeObstruction
open CurvatureBasisExchange
open NaiveRefinementSupportCounterexample
open BranchTransversalScanKernel

/-! ## Selector-order prefix exactness -/

/-- The strict prefix relation induced by the selected scan order. -/
inductive selectedPrefixBefore :
    SelectedScanBranch -> SelectedScanBranch -> Prop where
  | coarse_before_refinedTrace :
      selectedPrefixBefore
        SelectedScanBranch.coarseTrace SelectedScanBranch.refinedTrace
  | coarse_before_refinedRepairFrontier :
      selectedPrefixBefore
        SelectedScanBranch.coarseTrace
        SelectedScanBranch.refinedRepairFrontier
  | refinedTrace_before_refinedRepairFrontier :
      selectedPrefixBefore
        SelectedScanBranch.refinedTrace
        SelectedScanBranch.refinedRepairFrontier

/--
If the selected scan returns `later`, every selected code before it in the
selected order is hit by the support.
-/
theorem firstMissedSelectedBranch?_some_prefixHit
    (support : HandoffRepairSupport)
    [DecidablePred support]
    {earlier later : SelectedScanBranch}
    (hscan :
      firstMissedSelectedBranch? support selectedScanOrder = some later)
    (hprefix : selectedPrefixBefore earlier later) :
    selectedScanBranchHit support earlier := by
  cases hprefix with
  | coarse_before_refinedTrace =>
      by_cases hcoarse :
        selectedScanBranchHit support SelectedScanBranch.coarseTrace
      · exact hcoarse
      · simp [selectedScanOrder, firstMissedSelectedBranch?, hcoarse] at hscan
  | coarse_before_refinedRepairFrontier =>
      by_cases hcoarse :
        selectedScanBranchHit support SelectedScanBranch.coarseTrace
      · exact hcoarse
      · simp [selectedScanOrder, firstMissedSelectedBranch?, hcoarse] at hscan
  | refinedTrace_before_refinedRepairFrontier =>
      by_cases hcoarse :
        selectedScanBranchHit support SelectedScanBranch.coarseTrace
      · by_cases hrefined :
          selectedScanBranchHit support SelectedScanBranch.refinedTrace
        · exact hrefined
        · simp [selectedScanOrder, firstMissedSelectedBranch?, hcoarse,
            hrefined] at hscan
      · simp [selectedScanOrder, firstMissedSelectedBranch?, hcoarse] at hscan

/--
For trace-only support, the selected first residual is the refined
repair-frontier code, every earlier selected code is hit, and the residual is
missed.
-/
theorem traceOnly_firstResidual_prefixExact :
    firstMissedSelectedBranch? traceOnlyRepairPlan.touched
        selectedScanOrder =
          some SelectedScanBranch.refinedRepairFrontier /\
      (forall code,
        selectedPrefixBefore code
            SelectedScanBranch.refinedRepairFrontier ->
          selectedScanBranchHit traceOnlyRepairPlan.touched code) /\
      Not
        (selectedScanBranchHit traceOnlyRepairPlan.touched
          SelectedScanBranch.refinedRepairFrontier) := by
  refine
    ⟨traceOnly_firstMissedSelectedBranch, ?_, ?_⟩
  · intro code hprefix
    exact
      firstMissedSelectedBranch?_some_prefixHit
        traceOnlyRepairPlan.touched
        traceOnly_firstMissedSelectedBranch hprefix
  · exact
      firstMissedSelectedBranch?_some_missed
        traceOnlyRepairPlan.touched
        traceOnly_firstMissedSelectedBranch

/-! ## Singleton-deletion minimality for the selected trace-only witness -/

/-- Drop the branch interpreted by one selected scan code. -/
def dropSelectedScanBranch
    (code : SelectedScanBranch) : ExchangeBranchFamily :=
  exchangeBranchFamilyDrops selectedBasisExchangeFamily
    (SelectedScanBranch.branch code)

theorem refinedRepairFrontier_ne_coarseTraceBranch :
    SelectedScanBranch.branch SelectedScanBranch.refinedRepairFrontier ≠
      SelectedScanBranch.branch SelectedScanBranch.coarseTrace := by
  intro hsame
  have hfrontier :
      SelectedScanBranch.branch SelectedScanBranch.refinedRepairFrontier
        (ExchangeSide.refined, BridgeComponent.repairFrontier) := by
    exact ⟨rfl, rfl⟩
  have hcoarse :
      SelectedScanBranch.branch SelectedScanBranch.coarseTrace
        (ExchangeSide.refined, BridgeComponent.repairFrontier) := by
    simpa [hsame] using hfrontier
  rcases hcoarse with ⟨hside, _hcomponent⟩
  cases hside

theorem refinedRepairFrontier_ne_refinedTraceBranch :
    SelectedScanBranch.branch SelectedScanBranch.refinedRepairFrontier ≠
      SelectedScanBranch.branch SelectedScanBranch.refinedTrace := by
  intro hsame
  have hfrontier :
      SelectedScanBranch.branch SelectedScanBranch.refinedRepairFrontier
        (ExchangeSide.refined, BridgeComponent.repairFrontier) := by
    exact ⟨rfl, rfl⟩
  have htrace :
      SelectedScanBranch.branch SelectedScanBranch.refinedTrace
        (ExchangeSide.refined, BridgeComponent.repairFrontier) := by
    simpa [hsame] using hfrontier
  rcases htrace with ⟨_hside, hcomponent⟩
  cases hcomponent

/-- Dropping the earlier coarse trace branch does not restore trace-only transversality. -/
theorem traceOnly_dropCoarseTrace_not_restore_selectedTransversal :
    Not
      (ExchangeBranchRepairTransversal
        (dropSelectedScanBranch SelectedScanBranch.coarseTrace)
        traceOnlyRepairPlan.touched) := by
  intro htransversal
  rcases
      htransversal
        (SelectedScanBranch.branch
          SelectedScanBranch.refinedRepairFrontier)
        ⟨Or.inr (Or.inr rfl),
          refinedRepairFrontier_ne_coarseTraceBranch⟩ with
    ⟨component, hcomponent, htouched⟩
  exact traceOnly_misses_refinedRepairFrontierExchangeBranch
    component hcomponent htouched

/-- Dropping the earlier refined trace branch does not restore trace-only transversality. -/
theorem traceOnly_dropRefinedTrace_not_restore_selectedTransversal :
    Not
      (ExchangeBranchRepairTransversal
        (dropSelectedScanBranch SelectedScanBranch.refinedTrace)
        traceOnlyRepairPlan.touched) := by
  intro htransversal
  rcases
      htransversal
        (SelectedScanBranch.branch
          SelectedScanBranch.refinedRepairFrontier)
        ⟨Or.inr (Or.inr rfl),
          refinedRepairFrontier_ne_refinedTraceBranch⟩ with
    ⟨component, hcomponent, htouched⟩
  exact traceOnly_misses_refinedRepairFrontierExchangeBranch
    component hcomponent htouched

/--
No selected singleton before the returned residual restores trace-only
transversality.
-/
theorem traceOnly_noEarlierDeletionRestoresSelectedTransversal
    (code : SelectedScanBranch)
    (hprefix :
      selectedPrefixBefore code
        SelectedScanBranch.refinedRepairFrontier) :
    Not
      (ExchangeBranchRepairTransversal
        (dropSelectedScanBranch code)
        traceOnlyRepairPlan.touched) := by
  cases hprefix with
  | coarse_before_refinedRepairFrontier =>
      exact traceOnly_dropCoarseTrace_not_restore_selectedTransversal
  | refinedTrace_before_refinedRepairFrontier =>
      exact traceOnly_dropRefinedTrace_not_restore_selectedTransversal

/-- Dropping the returned residual branch restores trace-only transversality. -/
theorem traceOnly_returnedDeletionRestoresSelectedTransversal :
    ExchangeBranchRepairTransversal
      (dropSelectedScanBranch SelectedScanBranch.refinedRepairFrontier)
      traceOnlyRepairPlan.touched := by
  exact dropFirstMissed_restores_traceOnlyTransversal.2

/-! ## Visible contrast and theorem package -/

/--
The selected prefix-minimal residual is invisible to the collapsed visible scan.
-/
theorem selectedResidualPrefix_visibleContrast :
    (forall component,
      ExchangeVisibleUnion selectedBasisExchangeFamily component <->
        ExchangeVisibleUnion collapsedVisibleExchangeFamily component) /\
      firstMissedSelectedBranch? traceOnlyRepairPlan.touched
        selectedScanOrder =
          some SelectedScanBranch.refinedRepairFrontier /\
      firstMissedCollapsedVisibleBranch? traceOnlyRepairPlan.touched
        collapsedVisibleScanOrder = none /\
      (forall code,
        selectedPrefixBefore code
            SelectedScanBranch.refinedRepairFrontier ->
          selectedScanBranchHit traceOnlyRepairPlan.touched code) /\
      Not
        (selectedScanBranchHit traceOnlyRepairPlan.touched
          SelectedScanBranch.refinedRepairFrontier) /\
      (forall code,
        selectedPrefixBefore code
            SelectedScanBranch.refinedRepairFrontier ->
          Not
            (ExchangeBranchRepairTransversal
              (dropSelectedScanBranch code)
              traceOnlyRepairPlan.touched)) /\
      ExchangeBranchRepairTransversal
        (dropSelectedScanBranch SelectedScanBranch.refinedRepairFrontier)
        traceOnlyRepairPlan.touched := by
  exact
    ⟨selected_collapsed_same_visibleUnion,
      traceOnly_firstMissedSelectedBranch,
      collapsedVisible_firstMissedBranch_traceOnly,
      traceOnly_firstResidual_prefixExact.2.1,
      traceOnly_firstResidual_prefixExact.2.2,
      traceOnly_noEarlierDeletionRestoresSelectedTransversal,
      traceOnly_returnedDeletionRestoresSelectedTransversal⟩

/--
Cycle-74 theorem package: the selected first residual is prefix-exact and
selector-minimal for singleton deletion restoration in the selected trace-only
witness, while the collapsed visible scan cannot recover it.
-/
theorem selectedResidualScanPrefixMinimality_package :
    (firstMissedSelectedBranch? traceOnlyRepairPlan.touched
        selectedScanOrder =
          some SelectedScanBranch.refinedRepairFrontier) /\
      (forall code,
        selectedPrefixBefore code
            SelectedScanBranch.refinedRepairFrontier ->
          selectedScanBranchHit traceOnlyRepairPlan.touched code) /\
      Not
        (selectedScanBranchHit traceOnlyRepairPlan.touched
          SelectedScanBranch.refinedRepairFrontier) /\
      (forall code,
        selectedPrefixBefore code
            SelectedScanBranch.refinedRepairFrontier ->
          Not
            (ExchangeBranchRepairTransversal
              (dropSelectedScanBranch code)
              traceOnlyRepairPlan.touched)) /\
      ExchangeBranchRepairTransversal
        (dropSelectedScanBranch SelectedScanBranch.refinedRepairFrontier)
        traceOnlyRepairPlan.touched /\
      ((forall component,
        ExchangeVisibleUnion selectedBasisExchangeFamily component <->
          ExchangeVisibleUnion collapsedVisibleExchangeFamily component) /\
        firstMissedSelectedBranch? traceOnlyRepairPlan.touched
          selectedScanOrder =
            some SelectedScanBranch.refinedRepairFrontier /\
        firstMissedCollapsedVisibleBranch? traceOnlyRepairPlan.touched
          collapsedVisibleScanOrder = none) := by
  exact
    ⟨traceOnly_firstResidual_prefixExact.1,
      traceOnly_firstResidual_prefixExact.2.1,
      traceOnly_firstResidual_prefixExact.2.2,
      traceOnly_noEarlierDeletionRestoresSelectedTransversal,
      traceOnly_returnedDeletionRestoresSelectedTransversal,
      visibleEquivalent_residualKernelPair⟩

end SelectedResidualScanPrefixMinimality
end QualitySurface
end ResearchLean.AG
