import ResearchLean.AG.DoctrineFiberProduct.DistinctArchitectureObjects

/-!
# G-116 internal normalization split no-go

This module proves that canonical object normalization cannot split through a
second object of the package total category.  Naturality would force the
normalization of the intermediate package to be the identity, contradicting
the existence of distinct objects over each configuration.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation

/-- The object map of a composite package morphism is the composite of its
object maps.  This is supporting API for G-116(e2). -/
theorem packageTotalHom_objectMap_comp_apply
    {U : AtomCarrier.{u}} {P Q R : AATCorePackage U}
    (first : P ⟶ Q) (second : Q ⟶ R) (object : ArchitectureObject U) :
    (first ≫ second).upper.objectMap object =
      second.upper.objectMap (first.upper.objectMap object) :=
  rfl

/-- The identity package morphism has the identity object map.  This is
supporting API for G-116(e2). -/
theorem packageTotalHom_objectMap_id_apply
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    (object : ArchitectureObject U) :
    (𝟙 P : P ⟶ P).upper.objectMap object = object :=
  rfl

/-- The canonical total endomorphism has canonical object normalization as its
object map.  This is supporting API for G-116(e2). -/
theorem canonicalObjectNormalizationTotal_objectMap_apply
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    (admissible : CanonicalObjectNormalizationAdmissible P)
    (object : ArchitectureObject U) :
    (canonicalObjectNormalizationTotal P admissible).upper.objectMap object =
      canonicalObjectNormalization P object :=
  rfl

/-- G-116(e2): canonical package normalization has no splitting through an
object of the package total category. -/
theorem canonicalObjectNormalizationTotal_not_internal_split
    {U : AtomCarrier.{u}} (P Q : AATCorePackage U)
    (admissible : CanonicalObjectNormalizationAdmissible P)
    (r : P ⟶ Q) (i : Q ⟶ P) :
    ¬ (i ≫ r = 𝟙 Q ∧
      r ≫ i = canonicalObjectNormalizationTotal P admissible) := by
  rintro ⟨retraction, normalization⟩
  have retraction_apply (object : ArchitectureObject U) :
      r.upper.objectMap (i.upper.objectMap object) = object := by
    have applied := congrArg
      (fun hom : PackageTotalHom Q Q => hom.upper.objectMap object)
      retraction
    simpa only [packageTotalHom_objectMap_comp_apply,
      packageTotalHom_objectMap_id_apply] using applied
  have normalization_apply (object : ArchitectureObject U) :
      i.upper.objectMap (r.upper.objectMap object) =
        canonicalObjectNormalization P object := by
    have applied := congrArg
      (fun hom : PackageTotalHom P P => hom.upper.objectMap object)
      normalization
    simpa only [packageTotalHom_objectMap_comp_apply,
      canonicalObjectNormalizationTotal_objectMap_apply] using applied
  have i_injective : Function.Injective i.upper.objectMap := by
    intro first second equality
    calc
      first = r.upper.objectMap (i.upper.objectMap first) :=
        (retraction_apply first).symm
      _ = r.upper.objectMap (i.upper.objectMap second) := congrArg _ equality
      _ = second := retraction_apply second
  have normalization_fixed (object : ArchitectureObject U) :
      canonicalObjectNormalization Q object = object := by
    apply i_injective
    calc
      i.upper.objectMap (canonicalObjectNormalization Q object) =
          canonicalObjectNormalization P (i.upper.objectMap object) :=
        canonicalObjectNormalization_natural_apply i object
      _ = i.upper.objectMap (r.upper.objectMap (i.upper.objectMap object)) :=
        (normalization_apply (i.upper.objectMap object)).symm
      _ = i.upper.objectMap object := congrArg i.upper.objectMap
        (retraction_apply object)
  let configuration : AtomConfiguration U :=
    { family := { mem := fun _ => False }
      relation := fun _ _ => False
      identification := fun _ _ => False }
  obtain ⟨first, second, distinct, first_configuration,
      second_configuration⟩ :=
    exists_distinct_architectureObjects_over_configuration
      configuration
  apply distinct
  calc
    first = canonicalObjectNormalization Q first :=
      (normalization_fixed first).symm
    _ = canonicalObjectNormalization Q second := by
      unfold canonicalObjectNormalization
      rw [first_configuration, second_configuration]
    _ = second := normalization_fixed second

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct

end AAT.AG.DoctrineFiberProduct
