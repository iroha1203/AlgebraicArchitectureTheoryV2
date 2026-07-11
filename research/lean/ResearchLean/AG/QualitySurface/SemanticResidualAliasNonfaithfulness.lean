import ResearchLean.AG.QualitySurface.VisibleLocalSemanticGluingObstruction

/-!
Cycle 81 evidence for `G-aat-quality-surface-01`.

This file turns the selected refined semantic-fiber counterexample into a
generic residual-alias criterion.  A semantic residual alias gap records a
residual atom that is closed by the source support, missed by the target
support, and nevertheless component-covered by the target through another atom
with the same protected component.  Such an alias gap makes component
projection nonfaithful to semantic repair closure.

The selected witness is the repair-frontier obligation atom and the
repair-frontier surface atom from Cycle 78.  The result remains finite and
projection-level.  It does not assert source extraction completeness, ArchMap
correctness, runtime repair synthesis, canonical global semantic ontology,
general sheaf gluing, global sheaf completeness, or whole-codebase quality.
-/

namespace ResearchLean.AG
namespace QualitySurface
namespace SemanticResidualAliasNonfaithfulness

open HeterogeneousRouteInteraction
open HeterogeneousRouteInteraction.BridgeComponent
open HandoffCechExactness
open HandoffCechOverlapBasis
open RepairTransportCechCommutatorCurvature
open SemanticRepairCocycleWitness
open SemanticSupportProjectionKernel
open ComponentClearanceSemanticObstruction
open VisibleLocalSemanticGluingObstruction

/-! ## Generic residual alias gap -/

/-- Two semantic supports have the same component projection. -/
def SameSemanticComponentProjection
    {Atom : Type u}
    (projection : Atom -> BridgeComponent)
    (sourceSupport targetSupport : Atom -> Prop) : Prop :=
  forall component,
    SemanticComponentSupport projection sourceSupport component <->
      SemanticComponentSupport projection targetSupport component

/--
A residual alias gap: a residual atom is closed by the source support and
missed by the target support, while the target support still covers the same
component through a different semantic atom.
-/
def ResidualAliasGap
    {Atom : Type u}
    (projection : Atom -> BridgeComponent)
    (cover : HandoffCechCover)
    (sourceSupport targetSupport : Atom -> Prop) : Prop :=
  exists residual aliasAtom,
    SemanticProjectedResidual projection cover residual /\
      sourceSupport residual /\
      Not (targetSupport residual) /\
      targetSupport aliasAtom /\
      projection aliasAtom = projection residual

/--
A residual alias gap already gives target component coverage for the missed
residual's protected component.
-/
theorem residualAliasGap_target_covers_residualComponent
    {Atom : Type u}
    {projection : Atom -> BridgeComponent}
    {cover : HandoffCechCover}
    {sourceSupport targetSupport : Atom -> Prop}
    (hgap :
      ResidualAliasGap projection cover sourceSupport targetSupport) :
    exists residual,
      SemanticProjectedResidual projection cover residual /\
        sourceSupport residual /\
        Not (targetSupport residual) /\
        SemanticComponentSupport projection targetSupport
          (projection residual) := by
  rcases hgap with
    ⟨residual, aliasAtom, hresidual, hsource, htargetMiss,
      htargetAlias, hprojection⟩
  exact
    ⟨residual, hresidual, hsource, htargetMiss,
      ⟨aliasAtom, htargetAlias, hprojection⟩⟩

/-- A residual alias gap obstructs singleton residual fibers. -/
theorem not_residualFiberSingleton_of_residualAliasGap
    {Atom : Type u}
    {projection : Atom -> BridgeComponent}
    {cover : HandoffCechCover}
    {sourceSupport targetSupport : Atom -> Prop}
    (hgap :
      ResidualAliasGap projection cover sourceSupport targetSupport) :
    Not (ResidualFiberSingleton projection cover) := by
  intro hsingleton
  rcases hgap with
    ⟨residual, aliasAtom, hresidual, _hsource, htargetMiss,
      htargetAlias, hprojection⟩
  have halias : aliasAtom = residual :=
    hsingleton residual aliasAtom hresidual hprojection
  subst aliasAtom
  exact htargetMiss htargetAlias

/--
Generic nonfaithfulness theorem: if two supports have the same component
projection and there is a residual alias gap from source to target, then
component projection is not faithful to semantic repair closure.
-/
theorem semanticRepairClosed_nonfaithful_of_residualAliasGap
    {Atom : Type u}
    {projection : Atom -> BridgeComponent}
    {cover : HandoffCechCover}
    {sourceSupport targetSupport : Atom -> Prop}
    (hsame :
      SameSemanticComponentProjection projection sourceSupport targetSupport)
    (hclosed :
      SemanticRepairClosed projection cover sourceSupport)
    (hgap :
      ResidualAliasGap projection cover sourceSupport targetSupport) :
    SameSemanticComponentProjection projection sourceSupport targetSupport /\
      SemanticRepairClosed projection cover sourceSupport /\
      Not (SemanticRepairClosed projection cover targetSupport) /\
      Not (ResidualFiberSingleton projection cover) := by
  refine ⟨hsame, hclosed, ?_, not_residualFiberSingleton_of_residualAliasGap hgap⟩
  intro htargetClosed
  rcases hgap with
    ⟨residual, _alias, hresidual, _hsource, htargetMiss,
      _htargetAlias, _hprojection⟩
  exact htargetMiss (htargetClosed residual hresidual)

/--
No component-projection reflection rule can hold for a projection/cover/support
pair that has a residual alias gap.
-/
theorem residualAliasGap_obstructs_universal_componentReflection
    {Atom : Type u}
    {projection : Atom -> BridgeComponent}
    {cover : HandoffCechCover}
    {sourceSupport targetSupport : Atom -> Prop}
    (hsame :
      SameSemanticComponentProjection projection sourceSupport targetSupport)
    (hclosed :
      SemanticRepairClosed projection cover sourceSupport)
    (hgap :
      ResidualAliasGap projection cover sourceSupport targetSupport) :
    Not
      (forall source target : Atom -> Prop,
        SameSemanticComponentProjection projection source target ->
          SemanticRepairClosed projection cover source ->
            SemanticRepairClosed projection cover target) := by
  intro hreflect
  have htargetClosed :
      SemanticRepairClosed projection cover targetSupport :=
    hreflect sourceSupport targetSupport hsame hclosed
  rcases hgap with
    ⟨residual, _alias, hresidual, _hsource, htargetMiss,
      _htargetAlias, _hprojection⟩
  exact htargetMiss (htargetClosed residual hresidual)

/-! ## Selected refined semantic-fiber witness -/

/-- Complete and surface supports have the same generic component projection. -/
theorem complete_and_surface_same_semanticComponentProjection :
    SameSemanticComponentProjection
      refinedSemanticComponent completeRepairSupport surfaceRepairSupport := by
  intro component
  simpa [SameSemanticComponentProjection, SemanticComponentSupport,
    componentSupportOfRefinedSemantic]
    using (surface_and_complete_same_componentProjection component).symm

/-- The selected refined repair-frontier fiber has a residual alias gap. -/
theorem selected_repairFrontierResidualAliasGap :
    ResidualAliasGap
      refinedSemanticComponent
      repairFrontierOverlapBasisCover
      completeRepairSupport
      surfaceRepairSupport := by
  exact
    ⟨RefinedSemanticRepairAtom.repairFrontierObligation,
      RefinedSemanticRepairAtom.repairFrontierSurface,
      ((repairFrontierOverlapBasis).1
        BridgeComponent.repairFrontier rfl),
      trivial,
      by intro htarget; exact htarget,
      trivial,
      rfl⟩

/-- The selected alias gap gives component coverage for the missed residual. -/
theorem selected_aliasGap_covers_missed_residualComponent :
    exists residual,
      SemanticProjectedResidual
          refinedSemanticComponent repairFrontierOverlapBasisCover residual /\
        completeRepairSupport residual /\
        Not (surfaceRepairSupport residual) /\
        SemanticComponentSupport refinedSemanticComponent surfaceRepairSupport
          (refinedSemanticComponent residual) :=
  residualAliasGap_target_covers_residualComponent
    selected_repairFrontierResidualAliasGap

/--
The selected refined semantic-fiber alias gap makes component projection
nonfaithful to semantic repair closure.
-/
theorem selected_semanticRepairClosed_nonfaithful_of_aliasGap :
    SameSemanticComponentProjection
        refinedSemanticComponent completeRepairSupport surfaceRepairSupport /\
      SemanticRepairClosed
        refinedSemanticComponent repairFrontierOverlapBasisCover
        completeRepairSupport /\
      Not
        (SemanticRepairClosed
          refinedSemanticComponent repairFrontierOverlapBasisCover
          surfaceRepairSupport) /\
      Not
        (ResidualFiberSingleton
          refinedSemanticComponent repairFrontierOverlapBasisCover) := by
  exact
    semanticRepairClosed_nonfaithful_of_residualAliasGap
      complete_and_surface_same_semanticComponentProjection
      completeRepairSupport_semanticRepairClosed
      selected_repairFrontierResidualAliasGap

/--
The selected cover/projection/support pair refutes a universal component
projection reflection rule for semantic repair closure.
-/
theorem selected_aliasGap_obstructs_componentReflection :
    Not
      (forall source target : RefinedSemanticRepairAtom -> Prop,
        SameSemanticComponentProjection refinedSemanticComponent source target ->
          SemanticRepairClosed
              refinedSemanticComponent repairFrontierOverlapBasisCover source ->
            SemanticRepairClosed
              refinedSemanticComponent repairFrontierOverlapBasisCover target) := by
  exact
    residualAliasGap_obstructs_universal_componentReflection
      complete_and_surface_same_semanticComponentProjection
      completeRepairSupport_semanticRepairClosed
      selected_repairFrontierResidualAliasGap

/-! ## Theorem package -/

/--
Cycle-81 theorem package: a residual alias gap is a generic obstruction to
component-projection faithfulness for semantic repair closure, and the selected
repair-frontier refined fiber realizes the obstruction.
-/
theorem semanticResidualAliasNonfaithfulness_package :
    (forall {Atom : Type u}
      {projection : Atom -> BridgeComponent}
      {cover : HandoffCechCover}
      {sourceSupport targetSupport : Atom -> Prop},
      SameSemanticComponentProjection projection sourceSupport targetSupport ->
        SemanticRepairClosed projection cover sourceSupport ->
          ResidualAliasGap projection cover sourceSupport targetSupport ->
            SameSemanticComponentProjection
              projection sourceSupport targetSupport /\
            SemanticRepairClosed projection cover sourceSupport /\
            Not (SemanticRepairClosed projection cover targetSupport) /\
            Not (ResidualFiberSingleton projection cover)) /\
      ResidualAliasGap
        refinedSemanticComponent
        repairFrontierOverlapBasisCover
        completeRepairSupport
        surfaceRepairSupport /\
      SameSemanticComponentProjection
        refinedSemanticComponent completeRepairSupport surfaceRepairSupport /\
      SemanticRepairClosed
        refinedSemanticComponent repairFrontierOverlapBasisCover
        completeRepairSupport /\
      Not
        (SemanticRepairClosed
          refinedSemanticComponent repairFrontierOverlapBasisCover
          surfaceRepairSupport) /\
      Not
        (ResidualFiberSingleton
          refinedSemanticComponent repairFrontierOverlapBasisCover) /\
      Not
        (forall source target : RefinedSemanticRepairAtom -> Prop,
          SameSemanticComponentProjection refinedSemanticComponent source target ->
            SemanticRepairClosed
                refinedSemanticComponent repairFrontierOverlapBasisCover source ->
              SemanticRepairClosed
                refinedSemanticComponent repairFrontierOverlapBasisCover target) := by
  exact
    ⟨fun {Atom} {projection} {cover} {sourceSupport} {targetSupport} =>
        semanticRepairClosed_nonfaithful_of_residualAliasGap,
      selected_repairFrontierResidualAliasGap,
      selected_semanticRepairClosed_nonfaithful_of_aliasGap.1,
      selected_semanticRepairClosed_nonfaithful_of_aliasGap.2.1,
      selected_semanticRepairClosed_nonfaithful_of_aliasGap.2.2.1,
      selected_semanticRepairClosed_nonfaithful_of_aliasGap.2.2.2,
      selected_aliasGap_obstructs_componentReflection⟩

end SemanticResidualAliasNonfaithfulness
end QualitySurface
end ResearchLean.AG
