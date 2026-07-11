import ResearchLean.AG.QualitySurface.BranchReflectionAdequacyKernel

/-!
Cycle 75 evidence for `G-aat-quality-surface-01`.

This file lifts the selected residual scan and branch-reflection adequacy kernel
to a finite branch-code checker.  The checker is deliberately relative to a
supplied finite target order that exactly enumerates the target family and to a
decidable coverage predicate.  It does not assert a canonical global branch
order, runtime repair synthesis, source extraction completeness, ArchMap
correctness, global sheaf completeness, or whole-codebase quality.
-/

namespace ResearchLean.AG
namespace QualitySurface
namespace ArbitraryBranchFamilyAdequacy

open HeterogeneousRouteInteraction
open HeterogeneousRouteInteraction.BridgeComponent
open HandoffRepairTransversalTheorem
open RepairBasinExchangeObstruction
open CurvatureBasisExchange
open NaiveRefinementSupportCounterexample
open BranchTransversalScanKernel
open BranchReflectionAdequacyKernel

/-! ## Finite target-order adequacy checker -/

/--
A supplied finite target order exactly enumerates a target branch family.
The checker is complete only relative to this enumeration hypothesis.
-/
def TargetOrderEnumerates
    {TargetCode : Type}
    (targetFamily : ExchangeBranchFamily)
    (targetOrder : List TargetCode)
    (branchOf : TargetCode -> ExchangeBranchSupport) : Prop :=
  (forall code, code ∈ targetOrder -> targetFamily (branchOf code)) /\
    (forall branch,
      targetFamily branch ->
        exists code, code ∈ targetOrder /\ branchOf code = branch)

/-- All listed target codes are covered by the supplied coverage predicate. -/
def ListedTargetCodesCovered
    {TargetCode : Type}
    (covered : TargetCode -> Prop)
    (targetOrder : List TargetCode) : Prop :=
  forall code, code ∈ targetOrder -> covered code

/--
A target code is covered by a source branch when a source branch belongs to the
source family and its hit witness can be lifted to the target branch.
-/
def CodeReflectionCovered
    {TargetCode : Type}
    (sourceFamily : ExchangeBranchFamily)
    (sourceSupport targetSupport : HandoffRepairSupport)
    (branchOf : TargetCode -> ExchangeBranchSupport)
    (code : TargetCode) : Prop :=
  exists sourceBranch,
    sourceFamily sourceBranch /\
      SupportLiftClosedForBranch
        sourceBranch (branchOf code) sourceSupport targetSupport

/-- Family-level reflection adequacy is the existing branch-reflection kernel. -/
abbrev BranchFamilyReflectionAdequate
    (sourceFamily targetFamily : ExchangeBranchFamily)
    (sourceSupport targetSupport : HandoffRepairSupport) : Prop :=
  BranchReflectionTransportAdequate
    sourceFamily targetFamily sourceSupport targetSupport

/-- First target code in the supplied order not covered by `covered`. -/
def firstUncoveredTargetBranch?
    {TargetCode : Type}
    (covered : TargetCode -> Prop)
    [DecidablePred covered] :
    List TargetCode -> Option TargetCode
  | [] => none
  | code :: rest =>
      if covered code then
        firstUncoveredTargetBranch? covered rest
      else
        some code

/-- A returned target code belongs to the supplied target order. -/
theorem firstUncoveredTargetBranch?_some_mem
    {TargetCode : Type}
    (covered : TargetCode -> Prop)
    [DecidablePred covered] :
    forall {targetOrder : List TargetCode} {code : TargetCode},
      firstUncoveredTargetBranch? covered targetOrder = some code ->
        code ∈ targetOrder
  | [], _code, hsome => by
      cases hsome
  | head :: rest, code, hsome => by
      by_cases hhead : covered head
      · have htail :
            firstUncoveredTargetBranch? covered rest = some code := by
          simpa [firstUncoveredTargetBranch?, hhead] using hsome
        exact List.mem_cons_of_mem head
          (firstUncoveredTargetBranch?_some_mem covered htail)
      · have hcode : code = head := by
          simpa [firstUncoveredTargetBranch?, hhead] using hsome.symm
        subst hcode
        simp

/-- A returned target code is genuinely uncovered. -/
theorem firstUncoveredTargetBranch?_some_uncovered
    {TargetCode : Type}
    (covered : TargetCode -> Prop)
    [DecidablePred covered] :
    forall {targetOrder : List TargetCode} {code : TargetCode},
      firstUncoveredTargetBranch? covered targetOrder = some code ->
        Not (covered code)
  | [], _code, hsome => by
      cases hsome
  | head :: rest, code, hsome => by
      by_cases hhead : covered head
      · have htail :
            firstUncoveredTargetBranch? covered rest = some code := by
          simpa [firstUncoveredTargetBranch?, hhead] using hsome
        exact firstUncoveredTargetBranch?_some_uncovered covered htail
      · have hcode : code = head := by
          simpa [firstUncoveredTargetBranch?, hhead] using hsome.symm
        subst hcode
        exact hhead

/--
A returned target code is listed, belongs to the target family under an exact
target-order enumeration, and is genuinely uncovered.
-/
theorem firstUncoveredTargetBranch?_some_witness
    {TargetCode : Type}
    {targetFamily : ExchangeBranchFamily}
    {targetOrder : List TargetCode}
    {branchOf : TargetCode -> ExchangeBranchSupport}
    {covered : TargetCode -> Prop}
    [DecidablePred covered]
    (henum : TargetOrderEnumerates targetFamily targetOrder branchOf)
    {code : TargetCode}
    (hsome :
      firstUncoveredTargetBranch? covered targetOrder = some code) :
    code ∈ targetOrder /\
      targetFamily (branchOf code) /\
        Not (covered code) := by
  have hmem :
      code ∈ targetOrder :=
    firstUncoveredTargetBranch?_some_mem covered hsome
  exact
    ⟨hmem,
      henum.1 code hmem,
      firstUncoveredTargetBranch?_some_uncovered covered hsome⟩

/-- The checker returns `none` exactly when every listed target code is covered. -/
theorem firstUncoveredTargetBranch?_none_iff_listedAdequate
    {TargetCode : Type}
    (covered : TargetCode -> Prop)
    [DecidablePred covered] :
    forall targetOrder,
      firstUncoveredTargetBranch? covered targetOrder = none <->
        ListedTargetCodesCovered covered targetOrder
  | [] => by
      constructor
      · intro _ code hmem
        cases hmem
      · intro _
        rfl
  | head :: rest => by
      constructor
      · intro hnone code hmem
        by_cases hhead : covered head
        · have htail :
            firstUncoveredTargetBranch? covered rest = none := by
            simpa [firstUncoveredTargetBranch?, hhead] using hnone
          cases hmem with
          | head =>
              exact hhead
          | tail _ hlisted =>
              exact
                ((firstUncoveredTargetBranch?_none_iff_listedAdequate
                  covered rest).mp htail) code hlisted
        · have hsome :
              firstUncoveredTargetBranch? covered (head :: rest) =
                some head := by
            simp [firstUncoveredTargetBranch?, hhead]
          rw [hsome] at hnone
          cases hnone
      · intro hall
        have hhead : covered head := hall head (by simp)
        have htail :
            ListedTargetCodesCovered covered rest := by
          intro code hmem
          exact hall code (by simp [hmem])
        have htailNone :
            firstUncoveredTargetBranch? covered rest = none :=
          (firstUncoveredTargetBranch?_none_iff_listedAdequate
            covered rest).mpr htail
        simp [firstUncoveredTargetBranch?, hhead, htailNone]

/--
Listed support-lift coverage plus target-order exactness gives full
family-level branch-reflection adequacy.
-/
theorem listedCoverage_gives_branchFamilyAdequacy
    {TargetCode : Type}
    {targetFamily sourceFamily : ExchangeBranchFamily}
    {targetOrder : List TargetCode}
    {branchOf : TargetCode -> ExchangeBranchSupport}
    {sourceSupport targetSupport : HandoffRepairSupport}
    (henum : TargetOrderEnumerates targetFamily targetOrder branchOf)
    (hlisted :
      ListedTargetCodesCovered
        (CodeReflectionCovered
          sourceFamily sourceSupport targetSupport branchOf)
        targetOrder) :
    BranchFamilyReflectionAdequate
      sourceFamily targetFamily sourceSupport targetSupport := by
  intro targetBranch htarget
  rcases henum.2 targetBranch htarget with ⟨code, hmem, hcode⟩
  rcases hlisted code hmem with ⟨sourceBranch, hsource, hlift⟩
  exact ⟨sourceBranch, hsource, by simpa [hcode] using hlift⟩

/--
With an exact target order, `none` is equivalent to full family-level adequacy.
-/
theorem firstUncoveredTargetBranch?_none_iff_adequate
    {TargetCode : Type}
    {targetFamily sourceFamily : ExchangeBranchFamily}
    {targetOrder : List TargetCode}
    {branchOf : TargetCode -> ExchangeBranchSupport}
    {sourceSupport targetSupport : HandoffRepairSupport}
    [DecidablePred
      (CodeReflectionCovered
        sourceFamily sourceSupport targetSupport branchOf)]
    (henum : TargetOrderEnumerates targetFamily targetOrder branchOf) :
    firstUncoveredTargetBranch?
        (CodeReflectionCovered
          sourceFamily sourceSupport targetSupport branchOf)
        targetOrder = none <->
      BranchFamilyReflectionAdequate
        sourceFamily targetFamily sourceSupport targetSupport := by
  constructor
  · intro hnone
    exact
      listedCoverage_gives_branchFamilyAdequacy henum
        ((firstUncoveredTargetBranch?_none_iff_listedAdequate
          (CodeReflectionCovered
            sourceFamily sourceSupport targetSupport branchOf)
          targetOrder).mp hnone)
  · intro hadequate
    apply
      (firstUncoveredTargetBranch?_none_iff_listedAdequate
        (CodeReflectionCovered
          sourceFamily sourceSupport targetSupport branchOf)
        targetOrder).mpr
    intro code hmem
    exact
      hadequate (branchOf code) (henum.1 code hmem)

/-- Adequacy transports source branch-transversal clearance to the target. -/
theorem branchFamilyAdequacy_transportsTransversal
    {sourceFamily targetFamily : ExchangeBranchFamily}
    {sourceSupport targetSupport : HandoffRepairSupport}
    (hadequate :
      BranchFamilyReflectionAdequate
        sourceFamily targetFamily sourceSupport targetSupport)
    (hsource :
      ExchangeBranchRepairTransversal sourceFamily sourceSupport) :
    ExchangeBranchRepairTransversal targetFamily targetSupport := by
  exact branchReflectionKernel_pass_preservesTransversal hadequate hsource

/-! ## Selected finite stress test -/

/-- Trace-only support covers the selected trace branches but not repair-frontier. -/
def selectedTraceOnlyCoveredByCollapsed :
    SelectedScanBranch -> Prop
  | SelectedScanBranch.coarseTrace => True
  | SelectedScanBranch.refinedTrace => True
  | SelectedScanBranch.refinedRepairFrontier => False

instance selectedTraceOnlyCoveredByCollapsed_decidable
    (code : SelectedScanBranch) :
    Decidable (selectedTraceOnlyCoveredByCollapsed code) := by
  cases code
  · exact isTrue trivial
  · exact isTrue trivial
  · exact isFalse (by intro hfalse; exact hfalse)

/-- Trace-only support covers the collapsed visible branch. -/
def collapsedTraceOnlyCoveredByCollapsed :
    CollapsedVisibleScanBranch -> Prop :=
  fun _ => True

instance collapsedTraceOnlyCoveredByCollapsed_decidable
    (code : CollapsedVisibleScanBranch) :
    Decidable (collapsedTraceOnlyCoveredByCollapsed code) := by
  cases code
  exact isTrue trivial

/-- The selected scan order exactly enumerates the selected exchange family. -/
theorem selectedTargetOrderEnumerates :
    TargetOrderEnumerates
      selectedBasisExchangeFamily selectedScanOrder
      SelectedScanBranch.branch := by
  constructor
  · intro code _hmem
    cases code
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  · intro branch hbranch
    exact
      (selectedScanBranchFamily_complete branch).mpr hbranch

/-- The collapsed visible scan order exactly enumerates the collapsed family. -/
theorem collapsedTargetOrderEnumerates :
    TargetOrderEnumerates
      collapsedVisibleExchangeFamily collapsedVisibleScanOrder
      CollapsedVisibleScanBranch.branch := by
  constructor
  · intro code _hmem
    cases code
    rfl
  · intro branch hbranch
    subst branch
    exact
      ⟨CollapsedVisibleScanBranch.collapsed,
        by simp [collapsedVisibleScanOrder],
        rfl⟩

/--
For the selected finite witness, the decidable coverage predicate agrees with
actual support-lift coverage from the collapsed visible source family.
-/
theorem selectedTraceOnlyCoveredByCollapsed_iff_reflection
    (code : SelectedScanBranch) :
    selectedTraceOnlyCoveredByCollapsed code <->
      CodeReflectionCovered
        collapsedVisibleExchangeFamily
        traceOnlyRepairPlan.touched traceOnlyRepairPlan.touched
        SelectedScanBranch.branch code := by
  cases code
  · constructor
    · intro _
      exact
        ⟨collapsedVisibleExchangeBranch, rfl,
          by
            intro _coarseComponent _hcoarseBranch _hcoarseSupport
            exact
              ⟨(ExchangeSide.coarse, BridgeComponent.trace),
                ⟨rfl, rfl⟩,
                rfl⟩⟩
    · intro _
      trivial
  · constructor
    · intro _
      exact
        ⟨collapsedVisibleExchangeBranch, rfl,
          by
            intro _coarseComponent _hcoarseBranch _hcoarseSupport
            exact
              ⟨(ExchangeSide.refined, BridgeComponent.trace),
                ⟨rfl, rfl⟩,
                rfl⟩⟩
    · intro _
      trivial
  · constructor
    · intro hfalse
      cases hfalse
    · intro hcovered
      rcases hcovered with ⟨sourceBranch, hsource, hlift⟩
      subst sourceBranch
      rcases
          hlift (ExchangeSide.coarse, BridgeComponent.trace)
            (Or.inl rfl) rfl with
        ⟨targetComponent, htargetBranch, htargetSupport⟩
      exact
        traceOnly_misses_refinedRepairFrontierExchangeBranch
          targetComponent htargetBranch htargetSupport

/-- The selected checker returns the refined repair-frontier residual. -/
theorem selected_firstUncoveredTargetBranch :
    firstUncoveredTargetBranch?
        selectedTraceOnlyCoveredByCollapsed selectedScanOrder =
      some SelectedScanBranch.refinedRepairFrontier := by
  simp [firstUncoveredTargetBranch?, selectedScanOrder,
    selectedTraceOnlyCoveredByCollapsed]

/-- The collapsed checker has no residual for the same trace-only support. -/
theorem collapsed_firstUncoveredTargetBranch_none :
    firstUncoveredTargetBranch?
        collapsedTraceOnlyCoveredByCollapsed collapsedVisibleScanOrder =
      none := by
  simp [firstUncoveredTargetBranch?, collapsedVisibleScanOrder,
    collapsedTraceOnlyCoveredByCollapsed]

/--
The returned selected residual is listed, is a target branch, and is not
covered by the reflected support-lift predicate.
-/
theorem selected_firstUncoveredTargetBranch_witness :
    (SelectedScanBranch.refinedRepairFrontier ∈ selectedScanOrder) /\
      selectedBasisExchangeFamily
        (SelectedScanBranch.branch
          SelectedScanBranch.refinedRepairFrontier) /\
      Not
        (selectedTraceOnlyCoveredByCollapsed
          SelectedScanBranch.refinedRepairFrontier) /\
      Not
        (CodeReflectionCovered
          collapsedVisibleExchangeFamily
          traceOnlyRepairPlan.touched traceOnlyRepairPlan.touched
          SelectedScanBranch.branch
          SelectedScanBranch.refinedRepairFrontier) := by
  exact
    ⟨by simp [selectedScanOrder],
      Or.inr (Or.inr rfl),
      by simp [selectedTraceOnlyCoveredByCollapsed],
      by
        intro hcovered
        exact
          (selectedTraceOnlyCoveredByCollapsed_iff_reflection
            SelectedScanBranch.refinedRepairFrontier).mpr hcovered⟩

/--
Visible component-union projection is not faithful to the arbitrary finite
adequacy checker: selected and collapsed readings have the same visible union,
but the selected checker returns a protected residual while the collapsed one
returns none.
-/
theorem visibleUnion_not_faithful_to_arbitraryAdequacyCheck :
    (forall component,
      ExchangeVisibleUnion selectedBasisExchangeFamily component <->
        ExchangeVisibleUnion collapsedVisibleExchangeFamily component) /\
      firstUncoveredTargetBranch?
          selectedTraceOnlyCoveredByCollapsed selectedScanOrder =
        some SelectedScanBranch.refinedRepairFrontier /\
      firstUncoveredTargetBranch?
          collapsedTraceOnlyCoveredByCollapsed collapsedVisibleScanOrder =
        none /\
      Not
        (BranchFamilyReflectionAdequate
          collapsedVisibleExchangeFamily selectedBasisExchangeFamily
          traceOnlyRepairPlan.touched traceOnlyRepairPlan.touched) /\
      BranchFamilyReflectionAdequate
        collapsedVisibleExchangeFamily collapsedVisibleExchangeFamily
        traceOnlyRepairPlan.touched traceOnlyRepairPlan.touched := by
  refine
    ⟨selected_collapsed_same_visibleUnion,
      selected_firstUncoveredTargetBranch,
      collapsed_firstUncoveredTargetBranch_none,
      ?_,
      ?_⟩
  · intro hadequate
    exact
      traceOnly_not_hits_selectedBasisExchange
        (branchFamilyAdequacy_transportsTransversal
          hadequate traceOnly_hits_collapsedVisibleExchange)
  · intro targetBranch htarget
    subst targetBranch
    exact
      ⟨collapsedVisibleExchangeBranch, rfl,
        by
          intro coarseComponent hcoarseBranch hcoarseSupport
          exact
            ⟨coarseComponent,
              hcoarseBranch,
              hcoarseSupport⟩⟩

/-! ## Theorem package -/

/--
Cycle-75 theorem package: finite target orders produce witness-complete
adequacy checks, adequacy transports branch-transversal repair, and visible
projection cannot recover the protected branch-family adequacy result.
-/
theorem arbitraryBranchFamilyAdequacyChecker_package :
    (forall {TargetCode : Type}
      {covered : TargetCode -> Prop}
      [DecidablePred covered] (targetOrder : List TargetCode),
        firstUncoveredTargetBranch? covered targetOrder = none <->
          ListedTargetCodesCovered covered targetOrder) /\
      (forall {TargetCode : Type}
        {targetFamily : ExchangeBranchFamily}
        {targetOrder : List TargetCode}
        {branchOf : TargetCode -> ExchangeBranchSupport}
        {covered : TargetCode -> Prop}
        [DecidablePred covered] {code : TargetCode},
          TargetOrderEnumerates targetFamily targetOrder branchOf ->
          firstUncoveredTargetBranch? covered targetOrder = some code ->
            code ∈ targetOrder /\
              targetFamily (branchOf code) /\
                Not (covered code)) /\
      (forall {TargetCode : Type}
        {targetFamily sourceFamily : ExchangeBranchFamily}
        {targetOrder : List TargetCode}
        {branchOf : TargetCode -> ExchangeBranchSupport}
        {sourceSupport targetSupport : HandoffRepairSupport}
        [DecidablePred
          (CodeReflectionCovered
            sourceFamily sourceSupport targetSupport branchOf)],
          TargetOrderEnumerates targetFamily targetOrder branchOf ->
            (firstUncoveredTargetBranch?
                (CodeReflectionCovered
                  sourceFamily sourceSupport targetSupport branchOf)
                targetOrder = none <->
              BranchFamilyReflectionAdequate
                sourceFamily targetFamily sourceSupport targetSupport)) /\
      (forall {sourceFamily targetFamily : ExchangeBranchFamily}
        {sourceSupport targetSupport : HandoffRepairSupport},
          BranchFamilyReflectionAdequate
            sourceFamily targetFamily sourceSupport targetSupport ->
          ExchangeBranchRepairTransversal sourceFamily sourceSupport ->
          ExchangeBranchRepairTransversal targetFamily targetSupport) /\
      firstUncoveredTargetBranch?
          selectedTraceOnlyCoveredByCollapsed selectedScanOrder =
        some SelectedScanBranch.refinedRepairFrontier /\
      firstUncoveredTargetBranch?
          collapsedTraceOnlyCoveredByCollapsed collapsedVisibleScanOrder =
        none /\
      ((forall component,
        ExchangeVisibleUnion selectedBasisExchangeFamily component <->
          ExchangeVisibleUnion collapsedVisibleExchangeFamily component) /\
        Not
          (BranchFamilyReflectionAdequate
            collapsedVisibleExchangeFamily selectedBasisExchangeFamily
            traceOnlyRepairPlan.touched traceOnlyRepairPlan.touched) /\
        BranchFamilyReflectionAdequate
          collapsedVisibleExchangeFamily collapsedVisibleExchangeFamily
          traceOnlyRepairPlan.touched traceOnlyRepairPlan.touched) := by
  refine
    ⟨?_, ?_, ?_, ?_,
      selected_firstUncoveredTargetBranch,
      collapsed_firstUncoveredTargetBranch_none,
      ?_⟩
  · intro TargetCode covered _ targetOrder
    exact firstUncoveredTargetBranch?_none_iff_listedAdequate
      covered targetOrder
  · intro TargetCode targetFamily targetOrder branchOf covered _ code
      henum hsome
    exact firstUncoveredTargetBranch?_some_witness henum hsome
  · intro TargetCode targetFamily sourceFamily targetOrder branchOf
      sourceSupport targetSupport _ henum
    exact firstUncoveredTargetBranch?_none_iff_adequate henum
  · intro sourceFamily targetFamily sourceSupport targetSupport
      hadequate hsource
    exact branchFamilyAdequacy_transportsTransversal hadequate hsource
  · exact
      ⟨visibleUnion_not_faithful_to_arbitraryAdequacyCheck.1,
        visibleUnion_not_faithful_to_arbitraryAdequacyCheck.2.2.2.1,
        visibleUnion_not_faithful_to_arbitraryAdequacyCheck.2.2.2.2⟩

end ArbitraryBranchFamilyAdequacy
end QualitySurface
end ResearchLean.AG
