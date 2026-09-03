import ResearchLean.AG.DoctrineFiberProduct.IdempotentExchangeCellProjector

/-!
# G-116 canonical object-normalization naturality

This module discharges G-116(c2).  The selected object of a transported
configuration is fixed by the complete exact-hom laws, so canonical object
normalization commutes with the object map of every package total morphism.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open AtomFoundation

/-- Public evaluation API for canonical object normalization. -/
@[simp]
theorem canonicalObjectNormalization_apply
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    (object : ArchitectureObject U) :
    canonicalObjectNormalization P object =
      P.reading.objectReading.object object.configuration :=
  rfl

/-- Objects with the same configuration have the same canonical
normalization. -/
theorem canonicalObjectNormalization_eq_of_configuration_eq
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    {first second : ArchitectureObject U}
    (configuration_eq : first.configuration = second.configuration) :
    canonicalObjectNormalization P first =
      canonicalObjectNormalization P second := by
  rw [canonicalObjectNormalization_apply,
    canonicalObjectNormalization_apply, configuration_eq]

/-- G-116(c2) pointwise API: canonical object normalization commutes with the
object map of every package total morphism.  The proof uses the morphism's
declared `object_formation_eq` and `configuration_eq` laws; it assumes no
admissibility or invertibility. -/
theorem canonicalObjectNormalization_natural_apply
    {U : AtomCarrier.{u}} {P Q : AATCorePackage U}
    (hom : PackageTotalHom P Q) (object : ArchitectureObject U) :
    hom.upper.objectMap (canonicalObjectNormalization P object) =
      canonicalObjectNormalization Q (hom.upper.objectMap object) := by
  rw [canonicalObjectNormalization_apply,
    canonicalObjectNormalization_apply,
    hom.upper.object_formation_eq, hom.upper.configuration_eq]

/-- G-116(c2): at the `ArchitectureObject`-valued object-map level,
`U(hom) ∘ n_P = n_Q ∘ U(hom)` for every package total morphism.  This is
the fixed naturality statement, not a package-morphism equality. -/
theorem canonicalObjectNormalization_natural
    {U : AtomCarrier.{u}} {P Q : AATCorePackage U}
    (hom : PackageTotalHom P Q) :
    hom.upper.objectMap ∘ canonicalObjectNormalization P =
      canonicalObjectNormalization Q ∘ hom.upper.objectMap := by
  funext object
  exact canonicalObjectNormalization_natural_apply hom object

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct

end AAT.AG.DoctrineFiberProduct
