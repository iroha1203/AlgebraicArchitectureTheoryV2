import Formal.AG.Research.QualitySurface.CurvatureBasisExchange

/-!
Cycle 71 evidence for `G-aat-quality-surface-01`.

This file gives a selected finite no-go result for a too-weak refinement
reading.  In the selected repair/refinement exchange cell, a naive reading can
pair the refined trace and repair-frontier components into one refined branch.
That reading preserves the visible component-union projection, but it does not
reflect the refined repair-frontier singleton branch needed by the selected
branch-transversal repair obligation.

The result is only a selected finite branch-reflection failure and
deletion/restoration witness.  It is not a global refinement transport theorem,
global minimality theorem, canonical atlas refinement result, runtime repair
synthesis claim, source extraction completeness claim, ArchMap correctness
claim, arbitrary route enumeration, global sheaf completeness, or whole-codebase
quality claim.
-/

namespace Formal.AG.Research
namespace QualitySurface
namespace NaiveRefinementSupportCounterexample

open HeterogeneousRouteInteraction
open HeterogeneousRouteInteraction.BridgeComponent
open HandoffRepairTransversalTheorem
open RepairBasinExchangeObstruction
open AntichainOverlapBasisTransversal
open CurvatureBasisExchange

/-! ## Naive and reflected branch readings -/

/-- The naive refined paired branch keeps the refined side but pairs trace and repair-frontier. -/
def naiveRefinedPairExchangeBranch : ExchangeBranchSupport :=
  liftBranchToExchangeSide ExchangeSide.refined traceRepairPairBranch

/-- A naive finite refinement reading: coarse trace plus one refined paired branch. -/
def naiveRefinementBranchFamily
    (branch : ExchangeBranchSupport) : Prop :=
  branch = coarseTraceExchangeBranch \/
    branch = naiveRefinedPairExchangeBranch

/-- The selected reflected reading is the Cycle 70 selected basis-exchange family. -/
def reflectedSelectedBranchFamily : ExchangeBranchFamily :=
  selectedBasisExchangeFamily

/-- The reflected refined repair-frontier singleton branch. -/
def reflectedRepairFrontierSingleton : ExchangeBranchSupport :=
  refinedRepairFrontierExchangeBranch

/--
A branch is reflected by a reading when the reading contains exactly that
path-indexed branch as an independent selected branch.
-/
def branchReflectedBy
    (reading : ExchangeBranchFamily)
    (branch : ExchangeBranchSupport) : Prop :=
  reading branch

/-- Dropping one path-indexed branch from an exchange branch family. -/
def exchangeBranchFamilyDrops
    (family : ExchangeBranchFamily)
    (dropped : ExchangeBranchSupport) : ExchangeBranchFamily :=
  fun branch => family branch /\ branch ≠ dropped

/-! ## Visible preservation and branch-reflection failure -/

/--
The naive paired reading and reflected selected reading have the same visible
component-union projection.
-/
theorem naiveRefinement_preserves_visibleUnion
    (component : BridgeComponent) :
    ExchangeVisibleUnion naiveRefinementBranchFamily component <->
      ExchangeVisibleUnion reflectedSelectedBranchFamily component := by
  constructor
  · intro hunion
    rcases hunion with ⟨branch, hfamily, side, hcomponent⟩
    rcases hfamily with hbranch | hbranch
    · subst branch
      exact
        ⟨coarseTraceExchangeBranch, Or.inl rfl,
          side, hcomponent⟩
    · subst branch
      rcases hcomponent.2 with htrace | hrepair
      · exact
          ⟨refinedTraceExchangeBranch, Or.inr (Or.inl rfl),
            ExchangeSide.refined, ⟨rfl, htrace⟩⟩
      · exact
          ⟨refinedRepairFrontierExchangeBranch,
            Or.inr (Or.inr rfl),
            ExchangeSide.refined, ⟨rfl, hrepair⟩⟩
  · intro hunion
    rcases hunion with ⟨branch, hfamily, side, hcomponent⟩
    rcases hfamily with hbranch | hbranch
    · subst branch
      exact
        ⟨coarseTraceExchangeBranch, Or.inl rfl,
          side, hcomponent⟩
    · rcases hbranch with hbranch | hbranch
      · subst branch
        exact
          ⟨naiveRefinedPairExchangeBranch, Or.inr rfl,
            ExchangeSide.refined, ⟨rfl, Or.inl hcomponent.2⟩⟩
      · subst branch
        exact
          ⟨naiveRefinedPairExchangeBranch, Or.inr rfl,
            ExchangeSide.refined, ⟨rfl, Or.inr hcomponent.2⟩⟩

/-- The reflected selected reading contains the refined repair-frontier singleton. -/
theorem reflectedSelected_reflects_repairFrontierSingleton :
    branchReflectedBy reflectedSelectedBranchFamily
      reflectedRepairFrontierSingleton := by
  exact Or.inr (Or.inr rfl)

/-- The naive paired reading does not reflect the repair-frontier singleton as an independent branch. -/
theorem naiveReading_not_reflects_repairFrontierSingleton :
    Not
      (branchReflectedBy naiveRefinementBranchFamily
        reflectedRepairFrontierSingleton) := by
  intro hreflect
  rcases hreflect with hbranch | hbranch
  · have hfrontier :
        reflectedRepairFrontierSingleton
          (ExchangeSide.refined, BridgeComponent.repairFrontier) := by
      exact ⟨rfl, rfl⟩
    have hbad :
        coarseTraceExchangeBranch
          (ExchangeSide.refined, BridgeComponent.repairFrontier) := by
      simpa [hbranch] using hfrontier
    exact
      (by
        rcases hbad with ⟨hside, _hcomponent⟩
        cases hside)
  · have hnaive :
        naiveRefinedPairExchangeBranch
          (ExchangeSide.refined, BridgeComponent.trace) := by
      exact ⟨rfl, Or.inl rfl⟩
    have hleft :
        reflectedRepairFrontierSingleton
          (ExchangeSide.refined, BridgeComponent.trace) := by
      simpa [hbranch] using hnaive
    exact
      (by
        rcases hleft with ⟨_hside, hcomponent⟩
        cases hcomponent)

/-! ## Trace-only transversal separation -/

/-- The trace-only plan hits the naive paired refinement reading. -/
theorem traceOnly_hits_naiveRefinementBranches :
    ExchangeBranchRepairTransversal
      naiveRefinementBranchFamily traceOnlyRepairPlan.touched := by
  intro branch hfamily
  rcases hfamily with hbranch | hbranch
  · subst branch
    exact
      ⟨(ExchangeSide.coarse, BridgeComponent.trace),
        ⟨rfl, rfl⟩,
        rfl⟩
  · subst branch
    exact
      ⟨(ExchangeSide.refined, BridgeComponent.trace),
        ⟨rfl, Or.inl rfl⟩,
        rfl⟩

/-- The trace-only plan does not hit the reflected selected reading. -/
theorem traceOnly_not_hits_reflectedSelectedBranches :
    Not
      (ExchangeBranchRepairTransversal
        reflectedSelectedBranchFamily traceOnlyRepairPlan.touched) := by
  exact traceOnly_not_hits_selectedBasisExchange

/-- The reflected repair-frontier singleton is the selected missed branch. -/
theorem reflectedRepairFrontier_minimal_obstruction :
    branchReflectedBy reflectedSelectedBranchFamily
        reflectedRepairFrontierSingleton /\
      ExchangeBranchMissedBySupport reflectedRepairFrontierSingleton
        traceOnlyRepairPlan.touched /\
      Not
        (branchReflectedBy naiveRefinementBranchFamily
          reflectedRepairFrontierSingleton) := by
  exact
    ⟨reflectedSelected_reflects_repairFrontierSingleton,
      traceOnly_misses_refinedRepairFrontierExchangeBranch,
      naiveReading_not_reflects_repairFrontierSingleton⟩

/--
Deleting the reflected repair-frontier singleton restores trace-only
transversality for the selected finite family.
-/
theorem dropRefinedRepairFrontier_restores_traceOnlyTransversal :
    ExchangeBranchRepairTransversal
      (exchangeBranchFamilyDrops reflectedSelectedBranchFamily
        reflectedRepairFrontierSingleton)
      traceOnlyRepairPlan.touched := by
  intro branch hfamily
  rcases hfamily.1 with hbranch | hbranch
  · subst branch
    exact
      ⟨(ExchangeSide.coarse, BridgeComponent.trace),
        ⟨rfl, rfl⟩,
        rfl⟩
  · rcases hbranch with hbranch | hbranch
    · subst branch
      exact
        ⟨(ExchangeSide.refined, BridgeComponent.trace),
          ⟨rfl, rfl⟩,
          rfl⟩
    · exact False.elim (hfamily.2 hbranch)

/--
The selected finite branch-reflection failure: visible union is preserved, but
the naive paired reading does not reflect the refined repair-frontier singleton
and therefore accepts trace-only transversality where the reflected selected
reading rejects it.
-/
theorem selectedBranchReflectionFailure :
    (forall component,
      ExchangeVisibleUnion naiveRefinementBranchFamily component <->
        ExchangeVisibleUnion reflectedSelectedBranchFamily component) /\
      Not
        (branchReflectedBy naiveRefinementBranchFamily
          reflectedRepairFrontierSingleton) /\
      branchReflectedBy reflectedSelectedBranchFamily
        reflectedRepairFrontierSingleton /\
      ExchangeBranchRepairTransversal
        naiveRefinementBranchFamily traceOnlyRepairPlan.touched /\
      Not
        (ExchangeBranchRepairTransversal
          reflectedSelectedBranchFamily traceOnlyRepairPlan.touched) /\
      ExchangeBranchRepairTransversal
        (exchangeBranchFamilyDrops reflectedSelectedBranchFamily
          reflectedRepairFrontierSingleton)
        traceOnlyRepairPlan.touched := by
  exact
    ⟨naiveRefinement_preserves_visibleUnion,
      naiveReading_not_reflects_repairFrontierSingleton,
      reflectedSelected_reflects_repairFrontierSingleton,
      traceOnly_hits_naiveRefinementBranches,
      traceOnly_not_hits_reflectedSelectedBranches,
      dropRefinedRepairFrontier_restores_traceOnlyTransversal⟩

/-! ## Theorem package -/

/--
Cycle-71 theorem package: a selected finite naive refinement reading can
preserve visible component union while failing to reflect the refined
repair-frontier singleton branch required by branch-transversal repair.
-/
theorem naiveRefinementCounterexample_package :
    (forall component,
      ExchangeVisibleUnion naiveRefinementBranchFamily component <->
        ExchangeVisibleUnion reflectedSelectedBranchFamily component) /\
      ExchangeBranchRepairTransversal
        naiveRefinementBranchFamily traceOnlyRepairPlan.touched /\
      Not
        (ExchangeBranchRepairTransversal
          reflectedSelectedBranchFamily traceOnlyRepairPlan.touched) /\
      branchReflectedBy reflectedSelectedBranchFamily
        reflectedRepairFrontierSingleton /\
      Not
        (branchReflectedBy naiveRefinementBranchFamily
          reflectedRepairFrontierSingleton) /\
      (branchReflectedBy reflectedSelectedBranchFamily
          reflectedRepairFrontierSingleton /\
        ExchangeBranchMissedBySupport reflectedRepairFrontierSingleton
          traceOnlyRepairPlan.touched /\
        Not
          (branchReflectedBy naiveRefinementBranchFamily
            reflectedRepairFrontierSingleton)) /\
      ExchangeBranchRepairTransversal
        (exchangeBranchFamilyDrops reflectedSelectedBranchFamily
          reflectedRepairFrontierSingleton)
        traceOnlyRepairPlan.touched /\
      ((forall component,
        ExchangeVisibleUnion naiveRefinementBranchFamily component <->
          ExchangeVisibleUnion reflectedSelectedBranchFamily component) /\
        Not
          (branchReflectedBy naiveRefinementBranchFamily
            reflectedRepairFrontierSingleton) /\
        branchReflectedBy reflectedSelectedBranchFamily
          reflectedRepairFrontierSingleton /\
        ExchangeBranchRepairTransversal
          naiveRefinementBranchFamily traceOnlyRepairPlan.touched /\
        Not
          (ExchangeBranchRepairTransversal
            reflectedSelectedBranchFamily traceOnlyRepairPlan.touched) /\
        ExchangeBranchRepairTransversal
          (exchangeBranchFamilyDrops reflectedSelectedBranchFamily
            reflectedRepairFrontierSingleton)
          traceOnlyRepairPlan.touched) := by
  exact
    ⟨naiveRefinement_preserves_visibleUnion,
      traceOnly_hits_naiveRefinementBranches,
      traceOnly_not_hits_reflectedSelectedBranches,
      reflectedSelected_reflects_repairFrontierSingleton,
      naiveReading_not_reflects_repairFrontierSingleton,
      reflectedRepairFrontier_minimal_obstruction,
      dropRefinedRepairFrontier_restores_traceOnlyTransversal,
      selectedBranchReflectionFailure⟩

end NaiveRefinementSupportCounterexample
end QualitySurface
end Formal.AG.Research
