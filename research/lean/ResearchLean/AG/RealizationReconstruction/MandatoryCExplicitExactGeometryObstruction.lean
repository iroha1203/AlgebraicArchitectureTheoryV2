import ResearchLean.AG.RealizationReconstruction.MandatoryCBoundedPrimitiveTreeObstruction
import ResearchLean.AG.RealizationReconstruction.CSAATExplicitExactGeometryCategory
import ResearchLean.AG.FullGeometryNormalization.ExactBarBetaFiniteWitness
import Formal.Util.AssertStandardAxioms

/-!
# Mandatory-C obstruction in the explicit exact geometry category

The Boolean tag in the fixed mandatory-C package is invisible to its object,
Law, equation, context, coverage, overlap, coefficient, and raw-data readings.
Consequently every source-indexed tag choice extends, without an input
certificate, to the independently defined explicit exact geometry category.

This proves membership in the current six-component exact geometry morphism
contract.  It does not identify that category with the still-unconstructed
final `R_Theta`, and it does not assume or prove final-syntax generation.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory AtomFoundation DoctrineFiberProduct GeometryTransport
open AAT.AG.FullGeometryNormalization

/-- The complete fixed geometry used by mandatory C.  Only its operation type
is extended by the invisible Boolean tag; all geometry and raw data are the
reviewed finite-axis-fold data. -/
noncomputable def taggedOperationGeometryPackage :
    GeometryPackage.{0, 0} FiniteModel.carrier where
  core := taggedOperationPackage
  geometry :=
    { requirements := finiteAxisFoldGeometryPackage.geometry.requirements
      overlap := finiteAxisFoldGeometryPackage.geometry.overlap }
  Coefficient := finiteAxisFoldGeometryPackage.Coefficient
  coefficientCommRing := finiteAxisFoldGeometryPackage.coefficientCommRing
  raw := finiteAxisFoldGeometryPackage.raw

/-- Every source-indexed Boolean choice satisfies all six independently
defined exact geometry morphism components.  The only nonidentity datum is the
operation map already constructed by `taggedSourceChoiceTotal`; the remaining
components are constructed from the unchanged primitive readings. -/
noncomputable def taggedSourceChoiceExplicitExactGeometryHom
    (choice : ArchitectureObject FiniteModel.carrier → Bool) :
    ExplicitExactGeometryHom taggedOperationGeometryPackage
      taggedOperationGeometryPackage where
  base := taggedSourceChoiceTotal choice
  coverage :=
    { requiredSupport := fun _ => _root_.id
      requiredEquationCoordinate := fun _ => _root_.id
      selectedViolationWitness := fun _ => _root_.id
      requiredAxis := fun _ => _root_.id
      supportVisibleOn := fun _ _ => _root_.id
      equationCoordinateVisibleOn := fun _ _ => _root_.id
      violationWitnessVisibleOn := fun _ _ => _root_.id
      axisReadableOn := fun _ _ => _root_.id
      boundaryVisibleOn := fun _ _ => _root_.id }
  overlap :=
    { overlapIso := fun _ _ _ => Iso.refl _ }
  coefficientHom := RingHom.id _
  raw := by
    exact RawAmbientRestrictionSystemExactMapAgainst.refl
      taggedOperationGeometryPackage.site
      taggedOperationGeometryPackage.Coefficient
      taggedOperationGeometryPackage.raw
  realization := by
    exact ExplicitRealizationTransportSupply.id taggedOperationPackage

/-- The base component is the previously constructed ambient package map;
no geometry-level membership certificate replaces it. -/
@[simp] theorem taggedSourceChoiceExplicitExactGeometryHom_base
    (choice : ArchitectureObject FiniteModel.carrier → Bool) :
    (taggedSourceChoiceExplicitExactGeometryHom choice).base =
      taggedSourceChoiceTotal choice :=
  rfl

/-- The constant-true member is exactly the fixed uniform flip from mandatory
C at the complete core level. -/
theorem taggedSourceChoiceExplicitExactGeometryHom_uniformFlip_base :
    (taggedSourceChoiceExplicitExactGeometryHom (fun _ => true)).base =
      taggedUniformFlipTotal :=
  rfl

/-- The fixed mandatory-C geometry as an object of the independent exact
geometry category, with no representability or decoder-image condition. -/
noncomputable def taggedOperationExplicitExactGeometryObject :
    ExplicitExactGeomCategory.{0, 0} FiniteModel.carrier :=
  ExplicitExactGeomCategory.ofGeometryPackage taggedOperationGeometryPackage

/-- Category-level form of the constructed arbitrary source-choice map. -/
noncomputable def taggedSourceChoiceExplicitExactGeometryMorphism
    (choice : ArchitectureObject FiniteModel.carrier → Bool) :
    taggedOperationExplicitExactGeometryObject ⟶
      taggedOperationExplicitExactGeometryObject :=
  taggedSourceChoiceExplicitExactGeometryHom choice

/-- Read every source choice back from the constructed exact geometry
endomorphism. -/
noncomputable def readTaggedSourceChoiceExplicitExactGeometry
    (hom : taggedOperationExplicitExactGeometryObject ⟶
      taggedOperationExplicitExactGeometryObject) :
    ArchitectureObject FiniteModel.carrier → Bool :=
  readTaggedSourceChoice hom.base

/-- Reading the exact-geometry morphism constructed from a source predicate
recovers that predicate at every architecture-object source. -/
@[simp] theorem
    readTaggedSourceChoiceExplicitExactGeometry_taggedSourceChoice
    (choice : ArchitectureObject FiniteModel.carrier → Bool) :
    readTaggedSourceChoiceExplicitExactGeometry
      (taggedSourceChoiceExplicitExactGeometryMorphism choice) = choice :=
  readTaggedSourceChoice_taggedSourceChoiceTotal choice

/-- The exact-geometry endomorphisms retain the complete source predicate,
not just the uniform flip. -/
theorem taggedSourceChoiceExplicitExactGeometryMorphism_injective :
    Function.Injective taggedSourceChoiceExplicitExactGeometryMorphism := by
  intro first second equality
  have readEquality :=
    congrArg readTaggedSourceChoiceExplicitExactGeometry equality
  simpa using readEquality

/-- No decoder from a bounded primitive tree can cover all mandatory-C
endomorphisms even after all exact geometry fields have been imposed. -/
theorem taggedSourceChoiceExplicitExactGeometryEndomorphisms_not_treeEnumerable
    {A : Type 1} (embed : A ↪ TaggedPrimitiveReference)
    (decode : Tree A →
      (taggedOperationExplicitExactGeometryObject ⟶
        taggedOperationExplicitExactGeometryObject)) :
    ¬ Function.Surjective decode := by
  intro decodeSurjective
  have choiceSurjective : Function.Surjective
      (readTaggedSourceChoiceExplicitExactGeometry ∘ decode ∘
        boundedPrimitiveFiniteTreeEnumeration embed) := by
    intro choice
    obtain ⟨tree, treeEquality⟩ :=
      decodeSurjective
        (taggedSourceChoiceExplicitExactGeometryMorphism choice)
    obtain ⟨references, referencesEquality⟩ :=
      boundedPrimitiveFiniteTreeEnumeration_surjective embed tree
    refine ⟨references, ?_⟩
    simp only [Function.comp_apply, referencesEquality, treeEquality]
    exact
      readTaggedSourceChoiceExplicitExactGeometry_taggedSourceChoice choice
  exact listTaggedPrimitiveReferences_not_surjective_choices _ choiceSurjective

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end AAT.AG.RealizationReconstruction
