import Formal.AG.Research.QualitySurface.SemanticResidualAliasNonfaithfulness

/-!
Cycle 82 evidence for `G-aat-quality-surface-01`.

This file turns the residual-alias obstruction into a viewer/reading criterion.
A component-only semantic reading records only the projected component support.
A semantic-fiber-aware reading records support at the semantic atom level.  The
semantic-fiber-aware reading reflects semantic repair closure, while the
component-only reading does not in the selected residual-alias witness.

The result is a finite reading criterion, not an implementation claim about
ArchView or any concrete UI.  It does not assert source extraction
completeness, ArchMap correctness, runtime repair synthesis, canonical global
semantic ontology, general sheaf gluing, global sheaf completeness, or
whole-codebase quality.
-/

namespace Formal.AG.Research
namespace QualitySurface
namespace SemanticFiberAwareViewerCriterion

open HeterogeneousRouteInteraction
open HeterogeneousRouteInteraction.BridgeComponent
open HandoffCechExactness
open SemanticSupportProjectionKernel
open SemanticResidualAliasNonfaithfulness

/-! ## Component-only versus semantic-fiber-aware readings -/

/-- A component-only semantic reading records only component-projected support. -/
def ComponentOnlySemanticReading
    {Atom : Type u}
    (projection : Atom -> BridgeComponent)
    (sourceSupport targetSupport : Atom -> Prop) : Prop :=
  SameSemanticComponentProjection projection sourceSupport targetSupport

/-- A semantic-fiber-aware reading records support at the semantic atom level. -/
def SemanticFiberAwareReading
    {Atom : Type u}
    (sourceSupport targetSupport : Atom -> Prop) : Prop :=
  forall atom, sourceSupport atom <-> targetSupport atom

/--
Semantic-fiber-aware readings reflect semantic repair closure because they
preserve the actual residual atom identity, not just its projected component.
-/
theorem semanticFiberAwareReading_reflects_semanticRepairClosed
    {Atom : Type u}
    {projection : Atom -> BridgeComponent}
    {cover : HandoffCechCover}
    {sourceSupport targetSupport : Atom -> Prop}
    (hreading : SemanticFiberAwareReading sourceSupport targetSupport)
    (hclosed : SemanticRepairClosed projection cover sourceSupport) :
    SemanticRepairClosed projection cover targetSupport := by
  intro atom hresidual
  exact (hreading atom).mp (hclosed atom hresidual)

/--
A residual alias gap is exactly the finite reason a component-only reading is
not semantic-fiber-aware: the missed residual atom and its alias have the same
projected component but different support status.
-/
theorem not_semanticFiberAwareReading_of_residualAliasGap
    {Atom : Type u}
    {projection : Atom -> BridgeComponent}
    {cover : HandoffCechCover}
    {sourceSupport targetSupport : Atom -> Prop}
    (hgap :
      ResidualAliasGap projection cover sourceSupport targetSupport) :
    Not (SemanticFiberAwareReading sourceSupport targetSupport) := by
  intro hreading
  rcases hgap with
    ⟨residual, _aliasAtom, _hresidual, hsource, htargetMiss,
      _htargetAlias, _hprojection⟩
  exact htargetMiss ((hreading residual).mp hsource)

/--
Component-only readings do not reflect semantic repair closure in the presence
of a residual alias gap.
-/
theorem componentOnlyReading_not_reflect_semanticRepairClosed_of_aliasGap
    {Atom : Type u}
    {projection : Atom -> BridgeComponent}
    {cover : HandoffCechCover}
    {sourceSupport targetSupport : Atom -> Prop}
    (hcomponent :
      ComponentOnlySemanticReading projection sourceSupport targetSupport)
    (hclosed :
      SemanticRepairClosed projection cover sourceSupport)
    (hgap :
      ResidualAliasGap projection cover sourceSupport targetSupport) :
    ComponentOnlySemanticReading projection sourceSupport targetSupport /\
      SemanticRepairClosed projection cover sourceSupport /\
      Not (SemanticRepairClosed projection cover targetSupport) /\
      Not (SemanticFiberAwareReading sourceSupport targetSupport) := by
  exact
    ⟨hcomponent,
      hclosed,
      (semanticRepairClosed_nonfaithful_of_residualAliasGap
        hcomponent hclosed hgap).2.2.1,
      not_semanticFiberAwareReading_of_residualAliasGap hgap⟩

/--
No rule from component-only reading equivalence to semantic repair closure
reflection can hold when the supports exhibit a residual alias gap.
-/
theorem residualAliasGap_obstructs_componentOnlyViewerReflection
    {Atom : Type u}
    {projection : Atom -> BridgeComponent}
    {cover : HandoffCechCover}
    {sourceSupport targetSupport : Atom -> Prop}
    (hcomponent :
      ComponentOnlySemanticReading projection sourceSupport targetSupport)
    (hclosed :
      SemanticRepairClosed projection cover sourceSupport)
    (hgap :
      ResidualAliasGap projection cover sourceSupport targetSupport) :
    Not
      (forall source target : Atom -> Prop,
        ComponentOnlySemanticReading projection source target ->
          SemanticRepairClosed projection cover source ->
            SemanticRepairClosed projection cover target) := by
  exact
    residualAliasGap_obstructs_universal_componentReflection
      hcomponent hclosed hgap

/-! ## Selected semantic-fiber-aware viewer separation -/

/-- Complete and surface supports agree for the component-only semantic reading. -/
theorem selected_componentOnlyReading_complete_surface :
    ComponentOnlySemanticReading
      refinedSemanticComponent completeRepairSupport surfaceRepairSupport :=
  complete_and_surface_same_semanticComponentProjection

/-- Complete and surface supports do not agree for the semantic-fiber-aware reading. -/
theorem selected_not_semanticFiberAwareReading_complete_surface :
    Not
      (SemanticFiberAwareReading
        completeRepairSupport surfaceRepairSupport) :=
  not_semanticFiberAwareReading_of_residualAliasGap
    selected_repairFrontierResidualAliasGap

/-- The selected component-only reading cannot reflect semantic repair closure. -/
theorem selected_componentOnlyReading_not_reflects_semanticClosure :
    ComponentOnlySemanticReading
        refinedSemanticComponent completeRepairSupport surfaceRepairSupport /\
      SemanticRepairClosed
        refinedSemanticComponent HandoffCechOverlapBasis.repairFrontierOverlapBasisCover
        completeRepairSupport /\
      Not
        (SemanticRepairClosed
          refinedSemanticComponent HandoffCechOverlapBasis.repairFrontierOverlapBasisCover
          surfaceRepairSupport) /\
      Not
        (SemanticFiberAwareReading
          completeRepairSupport surfaceRepairSupport) := by
  exact
    componentOnlyReading_not_reflect_semanticRepairClosed_of_aliasGap
      selected_componentOnlyReading_complete_surface
      completeRepairSupport_semanticRepairClosed
      selected_repairFrontierResidualAliasGap

/--
The selected cover/projection/support pair refutes component-only viewer
reflection for semantic repair closure.
-/
theorem selected_componentOnlyViewerReflection_fails :
    Not
      (forall source target : RefinedSemanticRepairAtom -> Prop,
        ComponentOnlySemanticReading refinedSemanticComponent source target ->
          SemanticRepairClosed
              refinedSemanticComponent HandoffCechOverlapBasis.repairFrontierOverlapBasisCover source ->
            SemanticRepairClosed
              refinedSemanticComponent HandoffCechOverlapBasis.repairFrontierOverlapBasisCover target) := by
  exact
    residualAliasGap_obstructs_componentOnlyViewerReflection
      selected_componentOnlyReading_complete_surface
      completeRepairSupport_semanticRepairClosed
      selected_repairFrontierResidualAliasGap

/-! ## Theorem package -/

/--
Cycle-82 theorem package: semantic-fiber-aware readings reflect semantic repair
closure, while component-only readings fail on the selected residual-alias
witness.
-/
theorem semanticFiberAwareViewerCriterion_package :
    (forall {Atom : Type u}
      {projection : Atom -> BridgeComponent}
      {cover : HandoffCechCover}
      {sourceSupport targetSupport : Atom -> Prop},
      SemanticFiberAwareReading sourceSupport targetSupport ->
        SemanticRepairClosed projection cover sourceSupport ->
          SemanticRepairClosed projection cover targetSupport) /\
      ComponentOnlySemanticReading
        refinedSemanticComponent completeRepairSupport surfaceRepairSupport /\
      Not
        (SemanticFiberAwareReading
          completeRepairSupport surfaceRepairSupport) /\
      SemanticRepairClosed
        refinedSemanticComponent HandoffCechOverlapBasis.repairFrontierOverlapBasisCover
        completeRepairSupport /\
      Not
        (SemanticRepairClosed
          refinedSemanticComponent HandoffCechOverlapBasis.repairFrontierOverlapBasisCover
          surfaceRepairSupport) /\
      Not
        (forall source target : RefinedSemanticRepairAtom -> Prop,
          ComponentOnlySemanticReading refinedSemanticComponent source target ->
            SemanticRepairClosed
                refinedSemanticComponent HandoffCechOverlapBasis.repairFrontierOverlapBasisCover source ->
              SemanticRepairClosed
                refinedSemanticComponent HandoffCechOverlapBasis.repairFrontierOverlapBasisCover target) := by
  exact
    ⟨fun {Atom} {projection} {cover} {sourceSupport} {targetSupport} =>
        semanticFiberAwareReading_reflects_semanticRepairClosed,
      selected_componentOnlyReading_complete_surface,
      selected_not_semanticFiberAwareReading_complete_surface,
      completeRepairSupport_semanticRepairClosed,
      selected_componentOnlyReading_not_reflects_semanticClosure.2.2.1,
      selected_componentOnlyViewerReflection_fails⟩

end SemanticFiberAwareViewerCriterion
end QualitySurface
end Formal.AG.Research
