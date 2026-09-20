import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryObjectDependentLawFinite
import Formal.Util.AssertStandardAxioms

/-!
# Closed finite formula families for the complete object declaration

Foundation, matching, active-row normalization, and every active object's six
dependent stages are collected into one instance family.  The construction
retains the original `IndependentGeometryPrimitive.IsLawful` proposition in
both directions while exposing every obligation as a closed finite formula.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryPrimitive.ObjectLawFinite

noncomputable section

universe u v

variable {U : AtomCarrier.{u}}

open ObjectFoundationFinite ObjectMatchingFinite

abbrev foundationFromInstances
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (hi : ObjectFoundationFinite.FoundationInstances t) :
    IndependentGeometryPrimitive.FoundationLaws t :=
  (ObjectFoundationFinite.foundationLaws_iff_instances t).2 hi

abbrev activeFromInstances
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (hi : ObjectMatchingFinite.Active.Instances t) :
    IndependentGeometryPrimitive.IsActiveTyped t :=
  (ObjectMatchingFinite.Active.activeTyped_iff_instances t).2 hi

structure Instances (t : IndependentGeometryPrimitive.Table.{u, v} U) : Prop where
  foundation : ObjectFoundationFinite.FoundationInstances t
  matching : ObjectMatchingFinite.Matching.Instances t
    (foundationFromInstances t foundation).extraction
  active : ObjectMatchingFinite.Active.Instances t
  dependent : ∀ A
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true),
    ObjectDependentFinite.Instances t (activeFromInstances t active) A hA
      (foundationFromInstances t foundation)

theorem lawful_iff_instances
    (t : IndependentGeometryPrimitive.Table.{u, v} U) :
    IndependentGeometryPrimitive.IsLawful t ↔ Instances t := by
  constructor
  · intro hl
    let hf : ObjectFoundationFinite.FoundationInstances t :=
      (ObjectFoundationFinite.foundationLaws_iff_instances t).1 hl.foundation
    let foundation := foundationFromInstances t hf
    let hm : ObjectMatchingFinite.Matching.Instances t foundation.extraction :=
      (ObjectMatchingFinite.Matching.lawful_iff_instances t foundation.extraction).1
        (by simpa only [Subsingleton.elim hl.foundation foundation] using hl.matching)
    let ha : ObjectMatchingFinite.Active.Instances t :=
      (ObjectMatchingFinite.Active.activeTyped_iff_instances t).1 hl.active
    let active := activeFromInstances t ha
    refine ⟨hf, hm, ha, ?_⟩
    intro A hA
    apply (ObjectDependentFinite.dependentLaws_iff_instances t active A hA foundation).1
    simpa only [Subsingleton.elim hl.foundation foundation,
      Subsingleton.elim hl.active active] using hl.dependent A hA
  · intro hi
    let foundation := foundationFromInstances t hi.foundation
    let active := activeFromInstances t hi.active
    exact {
      foundation := foundation
      matching := (ObjectMatchingFinite.Matching.lawful_iff_instances t
        foundation.extraction).2 hi.matching
      active := active
      dependent := fun A hA =>
        (ObjectDependentFinite.dependentLaws_iff_instances t active A hA foundation).2
          (hi.dependent A hA) }

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryPrimitive.ObjectLawFinite

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryPrimitive.ObjectLawFinite
