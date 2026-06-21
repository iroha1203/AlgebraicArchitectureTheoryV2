import Formal.AG.Research.QualitySurface.RepairBasinExchangeObstruction

/-!
Cycle 69 evidence for `G-aat-quality-surface-01`.

This file adds a branch-incidence layer over an exact selected Cech overlap
component basis.  Branch clearance is intentionally separate from the existing
component-level `HandoffCechRepairObligation`: it is a declared branch predicate
whose residual form records missed selected branches.  The construction is
relative to selected finite Cech covers, selected overlap component bases, the
finite `BridgeComponent` vocabulary, and declared repair predicates.  It does
not assert runtime repair synthesis, canonical global minimality, source
extraction completeness, ArchMap correctness, arbitrary route enumeration,
global sheaf completeness, or whole-codebase quality.
-/

namespace Formal.AG.Research
namespace QualitySurface
namespace AntichainOverlapBasisTransversal

open HeterogeneousRouteInteraction
open HeterogeneousRouteInteraction.BridgeComponent
open HandoffRepairTransversalTheorem
open HandoffCechExactness
open HandoffCechOverlapBasis
open RepairTransportCechCommutatorCurvature
open RepairBasinExchangeObstruction

/-! ## Branch incidence over exact Cech overlap bases -/

/-- A protected branch is a predicate on finite bridge components. -/
abbrev BranchSupport := BridgeComponent -> Prop

/-- A branch family is a selected predicate on protected branches. -/
abbrev BranchFamily := BranchSupport -> Prop

/-- A branch has at least one protected component. -/
def BranchNonempty
    (branch : BranchSupport) : Prop :=
  exists component, branch component

/-- One branch is included in a selected component basis. -/
def BranchSubsupport
    (componentBasis : BridgeComponent -> Prop)
    (branch : BranchSupport) : Prop :=
  forall component, branch component -> componentBasis component

/--
A selected branch family is an antichain when a selected branch included in
another selected branch must have the same component membership.
-/
def BranchFamilyAntichain
    (family : BranchFamily) : Prop :=
  forall left right,
    family left ->
      family right ->
        (forall component, left component -> right component) ->
          forall component, right component -> left component

/-- The visible component-union projection of a branch family. -/
def BranchFamilyUnion
    (family : BranchFamily)
    (component : BridgeComponent) : Prop :=
  exists branch, family branch /\ branch component

/-- Every selected branch lives inside the selected component basis. -/
def BranchFamilySound
    (componentBasis : BridgeComponent -> Prop)
    (family : BranchFamily) : Prop :=
  forall branch, family branch -> BranchSubsupport componentBasis branch

/-- The selected branches generate the selected component basis by union. -/
def BranchFamilyUnionGenerates
    (componentBasis : BridgeComponent -> Prop)
    (family : BranchFamily) : Prop :=
  forall component,
    componentBasis component -> BranchFamilyUnion family component

/--
An antichain Cech overlap basis is a branch layer grounded by an exact selected
component overlap basis.
-/
def AntichainCechOverlapBasis
    (cover : HandoffCechCover)
    (componentBasis : BridgeComponent -> Prop)
    (family : BranchFamily) : Prop :=
  OverlapObstructionBasis cover componentBasis /\
    BranchFamilyAntichain family /\
    (forall branch, family branch -> BranchNonempty branch) /\
    BranchFamilySound componentBasis family /\
    BranchFamilyUnionGenerates componentBasis family

/-- Drop one selected branch from a branch family. -/
def branchFamilyDrops
    (family : BranchFamily)
    (dropped : BranchSupport) : BranchFamily :=
  fun branch => family branch /\ branch ≠ dropped

/-! ## Declared branch repair semantics -/

/-- A selected branch is missed by a declared repair support. -/
def BranchMissedBySupport
    (branch : BranchSupport)
    (support : HandoffRepairSupport) : Prop :=
  forall component, branch component -> Not (support component)

/-- Declared residual branch support after a repair plan. -/
def DeclaredResidualBranchSupport
    (family : BranchFamily)
    (plan : HandoffRepairPlan)
    (branch : BranchSupport) : Prop :=
  family branch /\
    forall component, branch component -> Not (plan.clears component)

/--
Branch-level clearance of every selected branch.

This is not the component-level `HandoffCechRepairObligation`; it asks for a
declared clear component inside each selected protected branch.
-/
def DeclaredBranchRepairClears
    (family : BranchFamily)
    (plan : HandoffRepairPlan) : Prop :=
  forall branch,
    family branch -> exists component, branch component /\ plan.clears component

/-- A repair support is a transversal for selected branches. -/
def BranchRepairTransversal
    (family : BranchFamily)
    (support : HandoffRepairSupport) : Prop :=
  forall branch,
    family branch -> exists component, branch component /\ support component

/--
A plan is branch-complete when every touched component inside a selected branch
is declared clear.
-/
def BranchCompleteRepairPlan
    (family : BranchFamily)
    (plan : HandoffRepairPlan) : Prop :=
  forall branch component,
    family branch ->
      branch component ->
        plan.touched component -> plan.clears component

/-- A selected missed branch remains as declared residual branch support. -/
theorem missedBranch_survives_as_residual
    {family : BranchFamily}
    {plan : HandoffRepairPlan}
    {branch : BranchSupport}
    (hfamily : family branch)
    (hmissed : BranchMissedBySupport branch plan.touched) :
    DeclaredResidualBranchSupport family plan branch := by
  constructor
  · exact hfamily
  · intro component hcomponent hclear
    exact hmissed component hcomponent
      (plan.clears_only_if_touched component hclear)

/--
In a selected antichain Cech branch basis and branch-complete repair regime,
branch clearance is exactly branch transversality.
-/
theorem declaredBranchClearance_iff_hits_antichainOverlapBasis
    {cover : HandoffCechCover}
    {componentBasis : BridgeComponent -> Prop}
    {family : BranchFamily}
    {plan : HandoffRepairPlan}
    (_hbasis : AntichainCechOverlapBasis cover componentBasis family)
    (hcomplete : BranchCompleteRepairPlan family plan) :
    DeclaredBranchRepairClears family plan <->
      BranchRepairTransversal family plan.touched := by
  constructor
  · intro hclear branch hfamily
    rcases hclear branch hfamily with ⟨component, hcomponent, hclears⟩
    exact
      ⟨component, hcomponent,
        plan.clears_only_if_touched component hclears⟩
  · intro hhit branch hfamily
    rcases hhit branch hfamily with ⟨component, hcomponent, htouched⟩
    exact
      ⟨component, hcomponent,
        hcomplete branch component hfamily hcomponent htouched⟩

/-! ## Selected trace / repair-frontier branch bases -/

/-- Singleton branch at the trace component. -/
def traceBranch : BranchSupport :=
  singletonRepairSupport BridgeComponent.trace

/-- Singleton branch at the repair-frontier component. -/
def repairFrontierBranch : BranchSupport :=
  singletonRepairSupport BridgeComponent.repairFrontier

/-- A paired branch containing trace and repair-frontier together. -/
def traceRepairPairBranch
    (component : BridgeComponent) : Prop :=
  component = BridgeComponent.trace \/
    component = BridgeComponent.repairFrontier

/-- The selected two-singleton branch family. -/
def twoSingletonBranchFamily
    (branch : BranchSupport) : Prop :=
  branch = traceBranch \/ branch = repairFrontierBranch

/-- The selected one-pair branch family. -/
def singlePairBranchFamily
    (branch : BranchSupport) : Prop :=
  branch = traceRepairPairBranch

theorem twoSingletonBranchFamily_antichain :
    BranchFamilyAntichain twoSingletonBranchFamily := by
  intro left right hleft hright hsubset component hrightComponent
  rcases hleft with hleft | hleft <;>
    rcases hright with hright | hright <;>
      subst left <;> subst right
  · exact hrightComponent
  · have hbad :
        repairFrontierBranch BridgeComponent.trace :=
      hsubset BridgeComponent.trace rfl
    cases hbad
  · have hbad :
        traceBranch BridgeComponent.repairFrontier :=
      hsubset BridgeComponent.repairFrontier rfl
    cases hbad
  · exact hrightComponent

theorem singlePairBranchFamily_antichain :
    BranchFamilyAntichain singlePairBranchFamily := by
  intro left right hleft hright _hsubset component hrightComponent
  subst left
  subst right
  exact hrightComponent

theorem twoSingletonBranchFamily_nonempty
    (branch : BranchSupport)
    (hbranch : twoSingletonBranchFamily branch) :
    BranchNonempty branch := by
  rcases hbranch with hbranch | hbranch
  · subst branch
    exact ⟨BridgeComponent.trace, rfl⟩
  · subst branch
    exact ⟨BridgeComponent.repairFrontier, rfl⟩

theorem singlePairBranchFamily_nonempty
    (branch : BranchSupport)
    (hbranch : singlePairBranchFamily branch) :
    BranchNonempty branch := by
  subst branch
  exact ⟨BridgeComponent.trace, Or.inl rfl⟩

theorem twoSingletonBranchFamily_sound :
    BranchFamilySound repairTransportCurvatureBasis
      twoSingletonBranchFamily := by
  intro branch hbranch component hcomponent
  rcases hbranch with hbranch | hbranch
  · subst branch
    exact Or.inl hcomponent
  · subst branch
    exact Or.inr hcomponent

theorem singlePairBranchFamily_sound :
    BranchFamilySound repairTransportCurvatureBasis
      singlePairBranchFamily := by
  intro branch hbranch component hcomponent
  subst branch
  exact hcomponent

theorem twoSingletonBranchFamily_generates :
    BranchFamilyUnionGenerates repairTransportCurvatureBasis
      twoSingletonBranchFamily := by
  intro component hbasis
  rcases hbasis with htrace | hrepair
  · subst component
    exact
      ⟨traceBranch, Or.inl rfl, rfl⟩
  · subst component
    exact
      ⟨repairFrontierBranch, Or.inr rfl, rfl⟩

theorem singlePairBranchFamily_generates :
    BranchFamilyUnionGenerates repairTransportCurvatureBasis
      singlePairBranchFamily := by
  intro component hbasis
  exact
    ⟨traceRepairPairBranch, rfl, hbasis⟩

/-- The selected curved Cech overlap basis supports two singleton branches. -/
theorem twoSingleton_antichainCechOverlapBasis :
    AntichainCechOverlapBasis
      selectedRepairTransportCechCommutatorCell.curvedPath
      repairTransportCurvatureBasis
      twoSingletonBranchFamily := by
  exact
    ⟨curvedPath_overlapBasis,
      twoSingletonBranchFamily_antichain,
      twoSingletonBranchFamily_nonempty,
      twoSingletonBranchFamily_sound,
      twoSingletonBranchFamily_generates⟩

/-- The same selected curved Cech overlap basis supports one paired branch. -/
theorem singlePair_antichainCechOverlapBasis :
    AntichainCechOverlapBasis
      selectedRepairTransportCechCommutatorCell.curvedPath
      repairTransportCurvatureBasis
      singlePairBranchFamily := by
  exact
    ⟨curvedPath_overlapBasis,
      singlePairBranchFamily_antichain,
      singlePairBranchFamily_nonempty,
      singlePairBranchFamily_sound,
      singlePairBranchFamily_generates⟩

/-! ## Branch deletion and visible-union nonfaithfulness -/

/-- Deleting the selected trace branch breaks union generation. -/
theorem dropTraceBranch_breaks_antichainGeneration :
    Not
      (BranchFamilyUnionGenerates repairTransportCurvatureBasis
        (branchFamilyDrops twoSingletonBranchFamily traceBranch)) := by
  intro hgenerates
  rcases hgenerates BridgeComponent.trace (Or.inl rfl) with
    ⟨branch, hdrop, hcomponent⟩
  rcases hdrop.1 with hbranch | hbranch
  · exact hdrop.2 hbranch
  · subst branch
    cases hcomponent

/-- The two branch families have the same visible component-union projection. -/
theorem twoSingleton_singlePair_same_visibleUnion
    (component : BridgeComponent) :
    BranchFamilyUnion twoSingletonBranchFamily component <->
      BranchFamilyUnion singlePairBranchFamily component := by
  constructor
  · intro hunion
    rcases hunion with ⟨branch, hfamily, hcomponent⟩
    rcases hfamily with hbranch | hbranch
    · subst branch
      exact
        ⟨traceRepairPairBranch, rfl, Or.inl hcomponent⟩
    · subst branch
      exact
        ⟨traceRepairPairBranch, rfl, Or.inr hcomponent⟩
  · intro hunion
    rcases hunion with ⟨branch, hfamily, hcomponent⟩
    subst branch
    rcases hcomponent with htrace | hrepair
    · subst component
      exact
        ⟨traceBranch, Or.inl rfl, rfl⟩
    · subst component
      exact
        ⟨repairFrontierBranch, Or.inr rfl, rfl⟩

/-- The trace-only plan hits the paired branch. -/
theorem traceOnly_hits_singlePairBranch :
    BranchRepairTransversal singlePairBranchFamily
      traceOnlyRepairPlan.touched := by
  intro branch hfamily
  subst branch
  exact ⟨BridgeComponent.trace, Or.inl rfl, rfl⟩

/-- The trace-only plan misses the repair-frontier singleton branch. -/
theorem traceOnly_misses_repairFrontierBranch :
    BranchMissedBySupport repairFrontierBranch
      traceOnlyRepairPlan.touched := by
  intro component hcomponent htouched
  subst component
  cases htouched

/-- The missed repair-frontier branch survives as residual branch support. -/
theorem traceOnly_repairFrontierBranch_residual :
    DeclaredResidualBranchSupport twoSingletonBranchFamily
      traceOnlyRepairPlan repairFrontierBranch :=
  missedBranch_survives_as_residual
    (family := twoSingletonBranchFamily)
    (plan := traceOnlyRepairPlan)
    (branch := repairFrontierBranch)
    (Or.inr rfl)
    traceOnly_misses_repairFrontierBranch

/-- The trace-only plan does not hit every singleton branch. -/
theorem traceOnly_not_hits_twoSingletonBranch :
    Not
      (BranchRepairTransversal twoSingletonBranchFamily
        traceOnlyRepairPlan.touched) := by
  intro hhit
  rcases hhit repairFrontierBranch (Or.inr rfl) with
    ⟨component, hcomponent, htouched⟩
  subst component
  cases htouched

/-- The trace-only plan is branch-complete for the paired-branch family. -/
theorem traceOnly_branchComplete_singlePair :
    BranchCompleteRepairPlan singlePairBranchFamily
      traceOnlyRepairPlan := by
  intro branch component hfamily _hcomponent htouched
  subst branch
  exact htouched

/--
The paired branch is clear for the trace-only plan, while the selected curved
Cech component-level repair obligation still fails.
-/
theorem traceOnly_branchClearance_singlePair_not_componentCechObligation :
    DeclaredBranchRepairClears singlePairBranchFamily traceOnlyRepairPlan /\
      Not
        (HandoffCechRepairObligation
          selectedRepairTransportCechCommutatorCell.curvedPath
          traceOnlyRepairPlan) := by
  constructor
  · exact
      (declaredBranchClearance_iff_hits_antichainOverlapBasis
        (cover := selectedRepairTransportCechCommutatorCell.curvedPath)
        (componentBasis := repairTransportCurvatureBasis)
        (family := singlePairBranchFamily)
        (plan := traceOnlyRepairPlan)
        singlePair_antichainCechOverlapBasis
        traceOnly_branchComplete_singlePair).mpr
        traceOnly_hits_singlePairBranch
  · simpa [selectedRepairRefinementBasinCell] using
      traceOnlyRepairPlan_fails_refinedBasin

/--
Visible component union is not faithful to protected branch-transversal class:
the one-pair and two-singleton branch families have the same visible union, but
the trace-only support is a transversal for only one of them.
-/
theorem sameVisibleUnion_not_faithful_to_branchTransversal :
    (forall component,
      BranchFamilyUnion twoSingletonBranchFamily component <->
        BranchFamilyUnion singlePairBranchFamily component) /\
      BranchRepairTransversal singlePairBranchFamily
        traceOnlyRepairPlan.touched /\
      Not
        (BranchRepairTransversal twoSingletonBranchFamily
          traceOnlyRepairPlan.touched) := by
  exact
    ⟨twoSingleton_singlePair_same_visibleUnion,
      traceOnly_hits_singlePairBranch,
      traceOnly_not_hits_twoSingletonBranch⟩

/-! ## Theorem package -/

/--
Cycle-69 theorem package: an exact selected Cech overlap component basis can
carry antichain branch incidence; missed selected branches survive as residual
branch support; branch-complete declared clearance is equivalent to branch
transversality; deleting a selected branch breaks generation; and the visible
component-union projection is not faithful to protected branch-transversal
class or to component-level Cech repair obligation.
-/
theorem antichainOverlapBasisTransversal_package :
    AntichainCechOverlapBasis
        selectedRepairTransportCechCommutatorCell.curvedPath
        repairTransportCurvatureBasis
        twoSingletonBranchFamily /\
      AntichainCechOverlapBasis
        selectedRepairTransportCechCommutatorCell.curvedPath
        repairTransportCurvatureBasis
        singlePairBranchFamily /\
      (forall {cover : HandoffCechCover}
          {componentBasis : BridgeComponent -> Prop}
          {family : BranchFamily}
          {plan : HandoffRepairPlan},
        AntichainCechOverlapBasis cover componentBasis family ->
          BranchCompleteRepairPlan family plan ->
            (DeclaredBranchRepairClears family plan <->
              BranchRepairTransversal family plan.touched)) /\
      (forall {family : BranchFamily}
          {plan : HandoffRepairPlan}
          {branch : BranchSupport},
        family branch ->
          BranchMissedBySupport branch plan.touched ->
            DeclaredResidualBranchSupport family plan branch) /\
      Not
        (BranchFamilyUnionGenerates repairTransportCurvatureBasis
          (branchFamilyDrops twoSingletonBranchFamily traceBranch)) /\
      (forall component,
        BranchFamilyUnion twoSingletonBranchFamily component <->
          BranchFamilyUnion singlePairBranchFamily component) /\
      DeclaredResidualBranchSupport twoSingletonBranchFamily
        traceOnlyRepairPlan repairFrontierBranch /\
      BranchRepairTransversal singlePairBranchFamily
        traceOnlyRepairPlan.touched /\
      Not
        (BranchRepairTransversal twoSingletonBranchFamily
          traceOnlyRepairPlan.touched) /\
      (DeclaredBranchRepairClears singlePairBranchFamily
          traceOnlyRepairPlan /\
        Not
          (HandoffCechRepairObligation
            selectedRepairTransportCechCommutatorCell.curvedPath
            traceOnlyRepairPlan)) /\
      ((forall component,
        BranchFamilyUnion twoSingletonBranchFamily component <->
          BranchFamilyUnion singlePairBranchFamily component) /\
        BranchRepairTransversal singlePairBranchFamily
          traceOnlyRepairPlan.touched /\
        Not
          (BranchRepairTransversal twoSingletonBranchFamily
            traceOnlyRepairPlan.touched)) := by
  exact
    ⟨twoSingleton_antichainCechOverlapBasis,
      singlePair_antichainCechOverlapBasis,
      fun {cover} {componentBasis} {family} {plan} hbasis hcomplete =>
        declaredBranchClearance_iff_hits_antichainOverlapBasis
          (cover := cover)
          (componentBasis := componentBasis)
          (family := family)
          (plan := plan)
          hbasis hcomplete,
      fun {family} {plan} {branch} hfamily hmissed =>
        missedBranch_survives_as_residual
          (family := family)
          (plan := plan)
          (branch := branch)
          hfamily hmissed,
      dropTraceBranch_breaks_antichainGeneration,
      twoSingleton_singlePair_same_visibleUnion,
      traceOnly_repairFrontierBranch_residual,
      traceOnly_hits_singlePairBranch,
      traceOnly_not_hits_twoSingletonBranch,
      traceOnly_branchClearance_singlePair_not_componentCechObligation,
      sameVisibleUnion_not_faithful_to_branchTransversal⟩

end AntichainOverlapBasisTransversal
end QualitySurface
end Formal.AG.Research
