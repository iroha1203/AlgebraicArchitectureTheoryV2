import Formal.AG.Research.QualitySurface.BranchTransversalScanKernel

/-!
Cycle 73 evidence for `G-aat-quality-surface-01`.

This file turns the selected branch-reflection failure and selected residual
scan into a finite adequacy kernel for refinement support transport.  The
positive condition is branch-local: a coarse hit witness must lift to a refined
hit witness.  It does not assume refined transversality, a zero residual scan,
or selected branch hitting as an input.

The construction remains relative to selected finite exchange branch families,
declared component repair supports, and the visible component-union projection.
It does not assert global atlas refinement, canonical refinement transport,
runtime repair synthesis, source extraction completeness, ArchMap correctness,
global sheaf completeness, or whole-codebase quality.
-/

namespace Formal.AG.Research
namespace QualitySurface
namespace BranchReflectionAdequacyKernel

open HeterogeneousRouteInteraction
open HeterogeneousRouteInteraction.BridgeComponent
open HandoffRepairTransversalTheorem
open RepairBasinExchangeObstruction
open CurvatureBasisExchange
open NaiveRefinementSupportCounterexample
open BranchTransversalScanKernel

/-! ## Branch-local support-lift adequacy -/

/--
A coarse branch hit can be transported to a refined branch hit by the declared
support lift.

This is deliberately weaker than, and distinct from, assuming the refined
branch family is already transversal: it only consumes a concrete coarse hit
witness and returns a concrete refined hit witness for the paired branch.
-/
def SupportLiftClosedForBranch
    (coarseBranch refinedBranch : ExchangeBranchSupport)
    (coarseSupport refinedSupport : HandoffRepairSupport) : Prop :=
  forall coarseComponent,
    coarseBranch coarseComponent ->
      coarseSupport coarseComponent.2 ->
        exists refinedComponent,
          refinedBranch refinedComponent /\
            refinedSupport refinedComponent.2

/--
A branch-reflection transport kernel is adequate when each refined branch has
a reflected coarse branch whose hit witnesses lift through the declared support
pair.
-/
def BranchReflectionTransportAdequate
    (coarseFamily refinedFamily : ExchangeBranchFamily)
    (coarseSupport refinedSupport : HandoffRepairSupport) : Prop :=
  forall refinedBranch,
    refinedFamily refinedBranch ->
      exists coarseBranch,
        coarseFamily coarseBranch /\
          SupportLiftClosedForBranch
            coarseBranch refinedBranch coarseSupport refinedSupport

/--
If the branch-reflection kernel is adequate, coarse branch-transversal
clearance transports to the refined selected family by witness transport.
-/
theorem branchReflectionKernel_pass_preservesTransversal
    {coarseFamily refinedFamily : ExchangeBranchFamily}
    {coarseSupport refinedSupport : HandoffRepairSupport}
    (hadequate :
      BranchReflectionTransportAdequate
        coarseFamily refinedFamily coarseSupport refinedSupport)
    (hcoarse :
      ExchangeBranchRepairTransversal coarseFamily coarseSupport) :
    ExchangeBranchRepairTransversal refinedFamily refinedSupport := by
  intro refinedBranch hrefined
  rcases hadequate refinedBranch hrefined with
    ⟨coarseBranch, hcoarseBranch, hlift⟩
  rcases hcoarse coarseBranch hcoarseBranch with
    ⟨coarseComponent, hcoarseComponent, hcoarseSupport⟩
  exact hlift coarseComponent hcoarseComponent hcoarseSupport

/-! ## Selected positive pass witness -/

/-- The selected repair support that touches both trace and repair-frontier. -/
def traceRepairFrontierRepairSupport : HandoffRepairSupport :=
  fun component =>
    component = BridgeComponent.trace \/
      component = BridgeComponent.repairFrontier

/-- The trace / repair-frontier support hits the collapsed visible branch. -/
theorem traceRepairFrontierSupport_hits_collapsedVisible :
    ExchangeBranchRepairTransversal
      collapsedVisibleExchangeFamily traceRepairFrontierRepairSupport := by
  intro branch hbranch
  subst branch
  exact
    ⟨(ExchangeSide.coarse, BridgeComponent.trace),
      Or.inl rfl,
      Or.inl rfl⟩

/--
The collapsed visible branch is adequate for the selected reflected branch
family when the declared support touches both trace and repair-frontier.
-/
theorem selectedAllExchangeAdequate :
    BranchReflectionTransportAdequate
      collapsedVisibleExchangeFamily selectedBasisExchangeFamily
      traceRepairFrontierRepairSupport traceRepairFrontierRepairSupport := by
  intro refinedBranch hrefined
  refine
    ⟨collapsedVisibleExchangeBranch, rfl, ?_⟩
  intro _coarseComponent _hcoarseBranch _hcoarseSupport
  rcases hrefined with hrefined | hrefined
  · subst refinedBranch
    exact
      ⟨(ExchangeSide.coarse, BridgeComponent.trace),
        ⟨rfl, rfl⟩,
        Or.inl rfl⟩
  · rcases hrefined with hrefined | hrefined
    · subst refinedBranch
      exact
        ⟨(ExchangeSide.refined, BridgeComponent.trace),
          ⟨rfl, rfl⟩,
          Or.inl rfl⟩
    · subst refinedBranch
      exact
        ⟨(ExchangeSide.refined, BridgeComponent.repairFrontier),
          ⟨rfl, rfl⟩,
          Or.inr rfl⟩

/--
The positive selected pass case: collapsed visible clearance transports to the
selected branch-reflection family only because the support-lift adequacy
condition is supplied.
-/
theorem allExchangeSupport_transports_selectedReflection :
    ExchangeBranchRepairTransversal
      selectedBasisExchangeFamily traceRepairFrontierRepairSupport := by
  exact
    branchReflectionKernel_pass_preservesTransversal
      selectedAllExchangeAdequate
      traceRepairFrontierSupport_hits_collapsedVisible

/-! ## Failure witness for missing branch reflection -/

/-- A source reading fails to cover a reflected branch required by the target reading. -/
def BranchReflectionCoverageFailure
    (source target : ExchangeBranchFamily)
    (branch : ExchangeBranchSupport) : Prop :=
  target branch /\ Not (source branch)

/-- The naive reading misses the reflected repair-frontier singleton branch. -/
theorem reflectedRepairFrontier_coverageFailure :
    BranchReflectionCoverageFailure
      naiveRefinementBranchFamily reflectedSelectedBranchFamily
      reflectedRepairFrontierSingleton := by
  exact
    ⟨reflectedSelected_reflects_repairFrontierSingleton,
      naiveReading_not_reflects_repairFrontierSingleton⟩

/--
Trace-only support cannot be an adequate transport kernel from the naive
reading to the reflected selected reading.
-/
theorem traceOnly_not_branchReflectionAdequate_naive_to_reflected :
    Not
      (BranchReflectionTransportAdequate
        naiveRefinementBranchFamily reflectedSelectedBranchFamily
        traceOnlyRepairPlan.touched traceOnlyRepairPlan.touched) := by
  intro hadequate
  exact
    traceOnly_not_hits_reflectedSelectedBranches
      (branchReflectionKernel_pass_preservesTransversal
        hadequate traceOnly_hits_naiveRefinementBranches)

/--
The failure branch is a reflected branch, is missed by trace-only support, and
blocks adequacy transport from the naive reading.
-/
theorem branchReflectionKernel_fail_returnsMissingBranch :
    BranchReflectionCoverageFailure
        naiveRefinementBranchFamily reflectedSelectedBranchFamily
        reflectedRepairFrontierSingleton /\
      ExchangeBranchMissedBySupport reflectedRepairFrontierSingleton
        traceOnlyRepairPlan.touched /\
      Not
        (BranchReflectionTransportAdequate
          naiveRefinementBranchFamily reflectedSelectedBranchFamily
          traceOnlyRepairPlan.touched traceOnlyRepairPlan.touched) := by
  exact
    ⟨reflectedRepairFrontier_coverageFailure,
      traceOnly_misses_refinedRepairFrontierExchangeBranch,
      traceOnly_not_branchReflectionAdequate_naive_to_reflected⟩

/--
Visible preservation does not prevent a missing reflected branch from breaking
transport adequacy.
-/
theorem missingReflection_witnessesTransportFailure :
    (forall component,
      ExchangeVisibleUnion naiveRefinementBranchFamily component <->
        ExchangeVisibleUnion reflectedSelectedBranchFamily component) /\
      BranchReflectionCoverageFailure
        naiveRefinementBranchFamily reflectedSelectedBranchFamily
        reflectedRepairFrontierSingleton /\
      ExchangeBranchRepairTransversal
        naiveRefinementBranchFamily traceOnlyRepairPlan.touched /\
      Not
        (ExchangeBranchRepairTransversal
          reflectedSelectedBranchFamily traceOnlyRepairPlan.touched) /\
      Not
        (BranchReflectionTransportAdequate
          naiveRefinementBranchFamily reflectedSelectedBranchFamily
          traceOnlyRepairPlan.touched traceOnlyRepairPlan.touched) := by
  exact
    ⟨naiveRefinement_preserves_visibleUnion,
      reflectedRepairFrontier_coverageFailure,
      traceOnly_hits_naiveRefinementBranches,
      traceOnly_not_hits_reflectedSelectedBranches,
      traceOnly_not_branchReflectionAdequate_naive_to_reflected⟩

/--
The visible component-union projection is not faithful to the branch-reflection
adequacy kernel.
-/
theorem visibleUnion_not_faithful_to_reflectionAdequacy :
    (forall component,
      ExchangeVisibleUnion naiveRefinementBranchFamily component <->
        ExchangeVisibleUnion reflectedSelectedBranchFamily component) /\
      ExchangeBranchRepairTransversal
        naiveRefinementBranchFamily traceOnlyRepairPlan.touched /\
      Not
        (ExchangeBranchRepairTransversal
          reflectedSelectedBranchFamily traceOnlyRepairPlan.touched) /\
      BranchReflectionCoverageFailure
        naiveRefinementBranchFamily reflectedSelectedBranchFamily
        reflectedRepairFrontierSingleton /\
      Not
        (BranchReflectionTransportAdequate
          naiveRefinementBranchFamily reflectedSelectedBranchFamily
          traceOnlyRepairPlan.touched traceOnlyRepairPlan.touched) := by
  exact
    ⟨naiveRefinement_preserves_visibleUnion,
      traceOnly_hits_naiveRefinementBranches,
      traceOnly_not_hits_reflectedSelectedBranches,
      reflectedRepairFrontier_coverageFailure,
      traceOnly_not_branchReflectionAdequate_naive_to_reflected⟩

/-! ## Theorem package -/

/--
Cycle-73 theorem package: branch-reflection transport has a non-tautological
support-lift pass criterion, while visible-equivalent naive readings still
return a missing reflected repair-frontier branch.
-/
theorem branchReflectionAdequacyKernel_package :
    (forall {coarseFamily refinedFamily : ExchangeBranchFamily}
      {coarseSupport refinedSupport : HandoffRepairSupport},
        BranchReflectionTransportAdequate
          coarseFamily refinedFamily coarseSupport refinedSupport ->
        ExchangeBranchRepairTransversal coarseFamily coarseSupport ->
          ExchangeBranchRepairTransversal refinedFamily refinedSupport) /\
      BranchReflectionTransportAdequate
        collapsedVisibleExchangeFamily selectedBasisExchangeFamily
        traceRepairFrontierRepairSupport traceRepairFrontierRepairSupport /\
      ExchangeBranchRepairTransversal
        collapsedVisibleExchangeFamily traceRepairFrontierRepairSupport /\
      ExchangeBranchRepairTransversal
        selectedBasisExchangeFamily traceRepairFrontierRepairSupport /\
      BranchReflectionCoverageFailure
        naiveRefinementBranchFamily reflectedSelectedBranchFamily
        reflectedRepairFrontierSingleton /\
      ExchangeBranchMissedBySupport reflectedRepairFrontierSingleton
        traceOnlyRepairPlan.touched /\
      Not
        (BranchReflectionTransportAdequate
          naiveRefinementBranchFamily reflectedSelectedBranchFamily
          traceOnlyRepairPlan.touched traceOnlyRepairPlan.touched) /\
      ((forall component,
        ExchangeVisibleUnion naiveRefinementBranchFamily component <->
          ExchangeVisibleUnion reflectedSelectedBranchFamily component) /\
        ExchangeBranchRepairTransversal
          naiveRefinementBranchFamily traceOnlyRepairPlan.touched /\
        Not
          (ExchangeBranchRepairTransversal
            reflectedSelectedBranchFamily traceOnlyRepairPlan.touched) /\
        BranchReflectionCoverageFailure
          naiveRefinementBranchFamily reflectedSelectedBranchFamily
          reflectedRepairFrontierSingleton /\
        Not
          (BranchReflectionTransportAdequate
            naiveRefinementBranchFamily reflectedSelectedBranchFamily
            traceOnlyRepairPlan.touched traceOnlyRepairPlan.touched)) := by
  exact
    ⟨fun {coarseFamily refinedFamily coarseSupport refinedSupport} =>
        branchReflectionKernel_pass_preservesTransversal
          (coarseFamily := coarseFamily)
          (refinedFamily := refinedFamily)
          (coarseSupport := coarseSupport)
          (refinedSupport := refinedSupport),
      selectedAllExchangeAdequate,
      traceRepairFrontierSupport_hits_collapsedVisible,
      allExchangeSupport_transports_selectedReflection,
      reflectedRepairFrontier_coverageFailure,
      traceOnly_misses_refinedRepairFrontierExchangeBranch,
      traceOnly_not_branchReflectionAdequate_naive_to_reflected,
      visibleUnion_not_faithful_to_reflectionAdequacy⟩

end BranchReflectionAdequacyKernel
end QualitySurface
end Formal.AG.Research
