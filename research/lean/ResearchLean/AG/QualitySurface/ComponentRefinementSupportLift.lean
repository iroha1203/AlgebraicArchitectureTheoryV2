import ResearchLean.AG.QualitySurface.ArbitraryBranchFamilyAdequacy

/-!
Cycle 76 evidence for `G-aat-quality-surface-01`.

This file turns component-level refinement lifts into branch-family adequacy
certificates for the finite checker from Cycle 75.  The lift is explicit and
code-indexed: every target branch code carries a component transport and a
support-transport proof.  The result closes the selected residual only after
the declared repair support is expanded from trace-only to trace plus
repair-frontier.

The construction remains relative to finite target orders, selected exchange
branch families, explicit component lifts, and declared support predicates.  It
does not assert global atlas refinement, canonical source extraction, ArchMap
correctness, runtime repair synthesis, global sheaf completeness, or
whole-codebase quality.
-/

namespace ResearchLean.AG
namespace QualitySurface
namespace ComponentRefinementSupportLift

open HeterogeneousRouteInteraction
open HeterogeneousRouteInteraction.BridgeComponent
open HandoffRepairTransversalTheorem
open RepairBasinExchangeObstruction
open AntichainOverlapBasisTransversal
open CurvatureBasisExchange
open NaiveRefinementSupportCounterexample
open BranchTransversalScanKernel
open BranchReflectionAdequacyKernel
open ArbitraryBranchFamilyAdequacy

/-! ## Component lifts as adequacy certificates -/

/-- A component lift sends every source branch component into the target branch. -/
def BranchComponentLiftClosed
    (componentLift : ExchangeComponent -> ExchangeComponent)
    (sourceBranch targetBranch : ExchangeBranchSupport) : Prop :=
  forall component,
    sourceBranch component ->
      targetBranch (componentLift component)

/-- A component lift sends touched source support into touched target support. -/
def ComponentSupportLiftClosed
    (componentLift : ExchangeComponent -> ExchangeComponent)
    (sourceSupport targetSupport : HandoffRepairSupport) : Prop :=
  forall component,
    sourceSupport component.2 ->
      targetSupport (componentLift component).2

/- A branch-component lift plus support lift is exactly the witness shape
needed by the branch-reflection adequacy kernel. -/
theorem branchComponentLiftClosed_gives_supportLiftClosedForBranch
    {componentLift : ExchangeComponent -> ExchangeComponent}
    {sourceBranch targetBranch : ExchangeBranchSupport}
    {sourceSupport targetSupport : HandoffRepairSupport}
    (hbranch :
      BranchComponentLiftClosed componentLift sourceBranch targetBranch)
    (hsupport :
      ComponentSupportLiftClosed componentLift sourceSupport targetSupport) :
    SupportLiftClosedForBranch
      sourceBranch targetBranch sourceSupport targetSupport := by
  intro component hsourceBranch hsourceSupport
  exact
    ⟨componentLift component,
      hbranch component hsourceBranch,
      hsupport component hsourceSupport⟩

/--
A target code is covered by an explicit component-level refinement lift from a
source branch and source support to the coded target branch.
-/
def CodeComponentLiftCovered
    {TargetCode : Type}
    (componentLift : TargetCode -> ExchangeComponent -> ExchangeComponent)
    (sourceFamily : ExchangeBranchFamily)
    (sourceSupport targetSupport : HandoffRepairSupport)
    (branchOf : TargetCode -> ExchangeBranchSupport)
    (code : TargetCode) : Prop :=
  exists sourceBranch,
    sourceFamily sourceBranch /\
      BranchComponentLiftClosed
        (componentLift code) sourceBranch (branchOf code) /\
      ComponentSupportLiftClosed
        (componentLift code) sourceSupport targetSupport

/-- Component-lift coverage refines to the support-lift coverage predicate. -/
theorem codeComponentLiftCovered_gives_codeReflectionCovered
    {TargetCode : Type}
    {componentLift : TargetCode -> ExchangeComponent -> ExchangeComponent}
    {sourceFamily : ExchangeBranchFamily}
    {sourceSupport targetSupport : HandoffRepairSupport}
    {branchOf : TargetCode -> ExchangeBranchSupport}
    {code : TargetCode}
    (hcovered :
      CodeComponentLiftCovered
        componentLift sourceFamily sourceSupport targetSupport branchOf
        code) :
    CodeReflectionCovered
      sourceFamily sourceSupport targetSupport branchOf code := by
  rcases hcovered with
    ⟨sourceBranch, hsource, hbranch, hsupport⟩
  exact
    ⟨sourceBranch, hsource,
      branchComponentLiftClosed_gives_supportLiftClosedForBranch
        hbranch hsupport⟩

/--
Listed component-lift coverage plus target-order exactness gives full
branch-family adequacy for the underlying support-lift kernel.
-/
theorem listedComponentLiftCoverage_gives_branchFamilyAdequacy
    {TargetCode : Type}
    {targetFamily sourceFamily : ExchangeBranchFamily}
    {targetOrder : List TargetCode}
    {branchOf : TargetCode -> ExchangeBranchSupport}
    {componentLift : TargetCode -> ExchangeComponent -> ExchangeComponent}
    {sourceSupport targetSupport : HandoffRepairSupport}
    (henum : TargetOrderEnumerates targetFamily targetOrder branchOf)
    (hlisted :
      ListedTargetCodesCovered
        (CodeComponentLiftCovered
          componentLift sourceFamily sourceSupport targetSupport branchOf)
        targetOrder) :
    BranchFamilyReflectionAdequate
      sourceFamily targetFamily sourceSupport targetSupport := by
  apply listedCoverage_gives_branchFamilyAdequacy henum
  intro code hmem
  exact codeComponentLiftCovered_gives_codeReflectionCovered
    (hlisted code hmem)

/--
If the finite component-lift checker returns no residual, the target branch
family is adequate for support-lift transport.
-/
theorem firstUncoveredComponentLift?_none_gives_branchFamilyAdequacy
    {TargetCode : Type}
    {targetFamily sourceFamily : ExchangeBranchFamily}
    {targetOrder : List TargetCode}
    {branchOf : TargetCode -> ExchangeBranchSupport}
    {componentLift : TargetCode -> ExchangeComponent -> ExchangeComponent}
    {sourceSupport targetSupport : HandoffRepairSupport}
    [DecidablePred
      (CodeComponentLiftCovered
        componentLift sourceFamily sourceSupport targetSupport branchOf)]
    (henum : TargetOrderEnumerates targetFamily targetOrder branchOf)
    (hnone :
      firstUncoveredTargetBranch?
          (CodeComponentLiftCovered
            componentLift sourceFamily sourceSupport targetSupport branchOf)
          targetOrder = none) :
    BranchFamilyReflectionAdequate
      sourceFamily targetFamily sourceSupport targetSupport := by
  exact
    listedComponentLiftCoverage_gives_branchFamilyAdequacy henum
      ((firstUncoveredTargetBranch?_none_iff_listedAdequate
        (CodeComponentLiftCovered
          componentLift sourceFamily sourceSupport targetSupport branchOf)
        targetOrder).mp hnone)

/-! ## Selected refinement-support lift -/

/--
The selected component lift sends the collapsed visible source branch into the
target branch named by each selected code.
-/
def selectedCollapsedComponentLift :
    SelectedScanBranch -> ExchangeComponent -> ExchangeComponent
  | SelectedScanBranch.coarseTrace, _ =>
      (ExchangeSide.coarse, BridgeComponent.trace)
  | SelectedScanBranch.refinedTrace, _ =>
      (ExchangeSide.refined, BridgeComponent.trace)
  | SelectedScanBranch.refinedRepairFrontier, _ =>
      (ExchangeSide.refined, BridgeComponent.repairFrontier)

/-- The selected component lift covers every selected branch code. -/
theorem selectedCollapsedComponentLift_covers_code
    (code : SelectedScanBranch) :
    CodeComponentLiftCovered
      selectedCollapsedComponentLift collapsedVisibleExchangeFamily
      traceRepairFrontierRepairSupport traceRepairFrontierRepairSupport
      SelectedScanBranch.branch code := by
  refine
    ⟨collapsedVisibleExchangeBranch, rfl, ?_, ?_⟩
  · intro component _hsource
    cases code <;>
      simp [selectedCollapsedComponentLift, SelectedScanBranch.branch,
        coarseTraceExchangeBranch, refinedTraceExchangeBranch,
        refinedRepairFrontierExchangeBranch, liftBranchToExchangeSide,
        traceBranch, repairFrontierBranch, singletonRepairSupport]
  · intro component _hsupport
    cases code <;>
      simp [selectedCollapsedComponentLift,
        traceRepairFrontierRepairSupport]

instance selectedCollapsedComponentLift_covers_code_decidable
    (code : SelectedScanBranch) :
    Decidable
      (CodeComponentLiftCovered
        selectedCollapsedComponentLift collapsedVisibleExchangeFamily
        traceRepairFrontierRepairSupport traceRepairFrontierRepairSupport
        SelectedScanBranch.branch code) :=
  isTrue (selectedCollapsedComponentLift_covers_code code)

/--
Trace-only support admits no component-lift coverage for the selected refined
repair-frontier target branch.  Any branch-component lift into that target
forces the lifted touched component to be a repair-frontier component, which
trace-only support does not touch.
-/
theorem traceOnly_componentLift_not_covers_refinedRepairFrontier
    (componentLift : SelectedScanBranch -> ExchangeComponent -> ExchangeComponent) :
    Not
      (CodeComponentLiftCovered
        componentLift collapsedVisibleExchangeFamily
        traceOnlyRepairPlan.touched traceOnlyRepairPlan.touched
        SelectedScanBranch.branch
        SelectedScanBranch.refinedRepairFrontier) := by
  intro hcovered
  rcases hcovered with ⟨sourceBranch, hsource, hbranch, hsupport⟩
  subst sourceBranch
  have htarget :
      SelectedScanBranch.branch SelectedScanBranch.refinedRepairFrontier
        (componentLift
          SelectedScanBranch.refinedRepairFrontier
          (ExchangeSide.coarse, BridgeComponent.trace)) :=
    hbranch (ExchangeSide.coarse, BridgeComponent.trace) (Or.inl rfl)
  have hliftSupport :
      traceOnlyRepairPlan.touched
        (componentLift
          SelectedScanBranch.refinedRepairFrontier
          (ExchangeSide.coarse, BridgeComponent.trace)).2 :=
    hsupport (ExchangeSide.coarse, BridgeComponent.trace) rfl
  have hcomponent :
      (componentLift
        SelectedScanBranch.refinedRepairFrontier
        (ExchangeSide.coarse, BridgeComponent.trace)).2 =
        BridgeComponent.repairFrontier := by
    rcases htarget with ⟨_hside, htargetComponent⟩
    simpa [repairFrontierBranch, singletonRepairSupport] using htargetComponent
  exact traceOnlyRepairPlan_misses_repairFrontier
    (by simpa [hcomponent] using hliftSupport)

/--
The selected component-lift checker has no residual once the declared repair
support touches both trace and repair-frontier.
-/
theorem selectedComponentLift_firstUncovered_none :
    firstUncoveredTargetBranch?
        (CodeComponentLiftCovered
          selectedCollapsedComponentLift collapsedVisibleExchangeFamily
          traceRepairFrontierRepairSupport traceRepairFrontierRepairSupport
          SelectedScanBranch.branch)
        selectedScanOrder = none := by
  have hcoarse :
      CodeComponentLiftCovered
        selectedCollapsedComponentLift collapsedVisibleExchangeFamily
        traceRepairFrontierRepairSupport traceRepairFrontierRepairSupport
        SelectedScanBranch.branch SelectedScanBranch.coarseTrace :=
    selectedCollapsedComponentLift_covers_code SelectedScanBranch.coarseTrace
  have hrefinedTrace :
      CodeComponentLiftCovered
        selectedCollapsedComponentLift collapsedVisibleExchangeFamily
        traceRepairFrontierRepairSupport traceRepairFrontierRepairSupport
        SelectedScanBranch.branch SelectedScanBranch.refinedTrace :=
    selectedCollapsedComponentLift_covers_code SelectedScanBranch.refinedTrace
  have hrefinedRepair :
      CodeComponentLiftCovered
        selectedCollapsedComponentLift collapsedVisibleExchangeFamily
        traceRepairFrontierRepairSupport traceRepairFrontierRepairSupport
        SelectedScanBranch.branch
        SelectedScanBranch.refinedRepairFrontier :=
    selectedCollapsedComponentLift_covers_code
      SelectedScanBranch.refinedRepairFrontier
  simp [firstUncoveredTargetBranch?, selectedScanOrder,
    hcoarse, hrefinedTrace, hrefinedRepair]

/--
The selected component-lift certificate gives branch-family adequacy from the
collapsed visible branch family to the selected branch family.
-/
theorem selectedComponentLift_gives_branchFamilyAdequacy :
    BranchFamilyReflectionAdequate
      collapsedVisibleExchangeFamily selectedBasisExchangeFamily
      traceRepairFrontierRepairSupport traceRepairFrontierRepairSupport := by
  exact
    firstUncoveredComponentLift?_none_gives_branchFamilyAdequacy
      selectedTargetOrderEnumerates
      selectedComponentLift_firstUncovered_none

/--
Component-level refinement support lifts transport collapsed visible
transversality to the selected branch-reflection family.
-/
theorem componentLift_transports_selectedReflection :
    ExchangeBranchRepairTransversal
      selectedBasisExchangeFamily traceRepairFrontierRepairSupport := by
  exact
    branchFamilyAdequacy_transportsTransversal
      selectedComponentLift_gives_branchFamilyAdequacy
      traceRepairFrontierSupport_hits_collapsedVisible

/--
The component-lift pass exactly contrasts with the trace-only residual: the
same target order reports the protected repair-frontier residual under
trace-only support and no residual under the trace plus repair-frontier lift.
-/
theorem componentLift_closes_selected_residual :
    firstUncoveredTargetBranch?
        selectedTraceOnlyCoveredByCollapsed selectedScanOrder =
      some SelectedScanBranch.refinedRepairFrontier /\
      firstUncoveredTargetBranch?
          (CodeComponentLiftCovered
            selectedCollapsedComponentLift collapsedVisibleExchangeFamily
            traceRepairFrontierRepairSupport traceRepairFrontierRepairSupport
            SelectedScanBranch.branch)
          selectedScanOrder = none /\
      BranchFamilyReflectionAdequate
        collapsedVisibleExchangeFamily selectedBasisExchangeFamily
        traceRepairFrontierRepairSupport traceRepairFrontierRepairSupport /\
      ExchangeBranchRepairTransversal
        selectedBasisExchangeFamily traceRepairFrontierRepairSupport /\
      (forall componentLift,
        Not
          (CodeComponentLiftCovered
            componentLift collapsedVisibleExchangeFamily
            traceOnlyRepairPlan.touched traceOnlyRepairPlan.touched
            SelectedScanBranch.branch
            SelectedScanBranch.refinedRepairFrontier)) := by
  exact
    ⟨selected_firstUncoveredTargetBranch,
      selectedComponentLift_firstUncovered_none,
      selectedComponentLift_gives_branchFamilyAdequacy,
      componentLift_transports_selectedReflection,
      traceOnly_componentLift_not_covers_refinedRepairFrontier⟩

/-! ## Theorem package -/

/--
Cycle-76 theorem package: component-level refinement lifts are sufficient
evidence for the finite adequacy checker, and the selected lift closes exactly
the trace-only protected residual by expanding declared support to
trace plus repair-frontier.
-/
theorem componentRefinementSupportLift_package :
    (forall {componentLift : ExchangeComponent -> ExchangeComponent}
      {sourceBranch targetBranch : ExchangeBranchSupport}
      {sourceSupport targetSupport : HandoffRepairSupport},
        BranchComponentLiftClosed
          componentLift sourceBranch targetBranch ->
        ComponentSupportLiftClosed
          componentLift sourceSupport targetSupport ->
        SupportLiftClosedForBranch
          sourceBranch targetBranch sourceSupport targetSupport) /\
      (forall {TargetCode : Type}
        {componentLift :
          TargetCode -> ExchangeComponent -> ExchangeComponent}
        {sourceFamily : ExchangeBranchFamily}
        {sourceSupport targetSupport : HandoffRepairSupport}
        {branchOf : TargetCode -> ExchangeBranchSupport}
        {code : TargetCode},
          CodeComponentLiftCovered
            componentLift sourceFamily sourceSupport targetSupport
            branchOf code ->
          CodeReflectionCovered
            sourceFamily sourceSupport targetSupport branchOf code) /\
      (forall {TargetCode : Type}
        {targetFamily sourceFamily : ExchangeBranchFamily}
        {targetOrder : List TargetCode}
        {branchOf : TargetCode -> ExchangeBranchSupport}
        {componentLift :
          TargetCode -> ExchangeComponent -> ExchangeComponent}
        {sourceSupport targetSupport : HandoffRepairSupport},
          TargetOrderEnumerates targetFamily targetOrder branchOf ->
          ListedTargetCodesCovered
            (CodeComponentLiftCovered
              componentLift sourceFamily sourceSupport targetSupport
              branchOf)
            targetOrder ->
          BranchFamilyReflectionAdequate
            sourceFamily targetFamily sourceSupport targetSupport) /\
      firstUncoveredTargetBranch?
          (CodeComponentLiftCovered
            selectedCollapsedComponentLift collapsedVisibleExchangeFamily
            traceRepairFrontierRepairSupport traceRepairFrontierRepairSupport
            SelectedScanBranch.branch)
          selectedScanOrder = none /\
      BranchFamilyReflectionAdequate
        collapsedVisibleExchangeFamily selectedBasisExchangeFamily
        traceRepairFrontierRepairSupport traceRepairFrontierRepairSupport /\
      ExchangeBranchRepairTransversal
        selectedBasisExchangeFamily traceRepairFrontierRepairSupport /\
      firstUncoveredTargetBranch?
          selectedTraceOnlyCoveredByCollapsed selectedScanOrder =
        some SelectedScanBranch.refinedRepairFrontier /\
      (forall componentLift,
        Not
          (CodeComponentLiftCovered
            componentLift collapsedVisibleExchangeFamily
            traceOnlyRepairPlan.touched traceOnlyRepairPlan.touched
            SelectedScanBranch.branch
            SelectedScanBranch.refinedRepairFrontier)) := by
  exact
    ⟨fun hbranch hsupport =>
        branchComponentLiftClosed_gives_supportLiftClosedForBranch
          hbranch hsupport,
      fun hcovered =>
        codeComponentLiftCovered_gives_codeReflectionCovered hcovered,
      fun henum hlisted =>
        listedComponentLiftCoverage_gives_branchFamilyAdequacy
          henum hlisted,
      selectedComponentLift_firstUncovered_none,
      selectedComponentLift_gives_branchFamilyAdequacy,
      componentLift_transports_selectedReflection,
      selected_firstUncoveredTargetBranch,
      traceOnly_componentLift_not_covers_refinedRepairFrontier⟩

end ComponentRefinementSupportLift
end QualitySurface
end ResearchLean.AG
