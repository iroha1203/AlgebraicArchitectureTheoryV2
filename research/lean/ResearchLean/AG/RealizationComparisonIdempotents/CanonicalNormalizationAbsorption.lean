import ResearchLean.AG.DoctrineFiberProduct.IdempotentExchangeNormalization
import ResearchLean.AG.DoctrineFiberProduct.CanonicalObjectNormalizationNaturality

/-!
# Canonical normalization absorption on admissible core packages

This file begins G-119(D).  It restricts the core-package category to objects
carrying the existing canonical-normalization admissibility laws and proves the
one-sided sandwich equation for every total morphism between them.

## Implementation notes

The subcategory is the ordinary `ObjectProperty.FullSubcategory`, so its
morphisms are all package total morphisms and carry no added absorption or
operation-coherence field.  The proof extends package morphisms componentwise.
In particular, the dependent operation component is compared by heterogeneous
function extensionality and `cast_heq`, rather than being hidden in a new
certificate.  The opposite two-sided naturality equation is deliberately not
used: G-117 shows that it can fail for admissible packages.
-/

open CategoryTheory

namespace AAT.AG.RealizationComparisonIdempotents

open AtomFoundation DoctrineFiberProduct

universe u

/-- The existing canonical-normalization admissibility predicate, exposed as
an `ObjectProperty` for the standard full-subcategory construction. -/
abbrev canonicalNormalizationAdmissibleProperty (U : AtomCarrier.{u}) :
    ObjectProperty (AATCorePackage U) :=
  fun P => CanonicalObjectNormalizationAdmissible P

/-- G-119(D)'s full subcategory of core packages carrying the existing
canonical object-normalization admissibility laws. -/
abbrev CanonicalNormalizationAdmissiblePackage (U : AtomCarrier.{u}) :=
  (canonicalNormalizationAdmissibleProperty U).FullSubcategory

/-- The existing canonical total normalization, regarded as an endomorphism in
the full admissible-package subcategory.  Admissibility is exactly the object
condition supplied by G-119(D). -/
noncomputable def canonicalPackageNormalization
    {U : AtomCarrier.{u}} (P : CanonicalNormalizationAdmissiblePackage U) :
    P ⟶ P :=
  ObjectProperty.homMk
    (canonicalObjectNormalizationTotal P.obj P.property)

/-- API lemma for the underlying package morphism of the admissible-package
normalization. -/
@[simp]
theorem canonicalPackageNormalization_hom
    {U : AtomCarrier.{u}} (P : CanonicalNormalizationAdmissiblePackage U) :
    (canonicalPackageNormalization P).hom =
      canonicalObjectNormalizationTotal P.obj P.property :=
  rfl

/-- After source normalization and an arbitrary total morphism, the resulting
object is fixed by the target normalization.  This is the object-map API used
inside the complete package-morphism equality. -/
theorem canonicalObjectNormalization_fixed_after_map
    {U : AtomCarrier.{u}}
    {P Q : CanonicalNormalizationAdmissiblePackage U}
    (f : P ⟶ Q) (object : ArchitectureObject U) :
    canonicalObjectNormalization Q.obj
        (f.hom.upper.objectMap
          (canonicalObjectNormalization P.obj object)) =
      f.hom.upper.objectMap
        (canonicalObjectNormalization P.obj object) := by
  rw [← canonicalObjectNormalization_natural_apply f.hom,
    canonicalObjectNormalization_idempotent]

/-- G-119(D)'s absorption theorem.  In Lean composition order it says
`e_P ≫ f ≫ e_Q = e_P ≫ f`, which is `e_Q f e_P = f e_P` in the
fixed target's conventional notation.  It uses only the two endpoint objects'
existing admissibility and the laws already carried by the arbitrary total
morphism `f`; the dependent operation-map component is included in the
extensional equality. -/
theorem canonicalPackageNormalization_absorption
    {U : AtomCarrier.{u}}
    {P Q : CanonicalNormalizationAdmissiblePackage U} (f : P ⟶ Q) :
    canonicalPackageNormalization P ≫ f ≫
        canonicalPackageNormalization Q =
      canonicalPackageNormalization P ≫ f := by
  apply ObjectProperty.hom_ext
  apply PackageTotalHom.ext
  · rfl
  · apply SignedExactCoreReadingHom.ext
    · rfl
    · funext object
      exact canonicalObjectNormalization_fixed_after_map f object
    · apply equationSystemExactTransport_hext
      · rfl
      · funext object
        exact canonicalObjectNormalization_fixed_after_map f object
      · rfl
      · rfl
      · rfl
    · apply Function.hfunext rfl
      intro first first' hfirst
      cases hfirst
      apply Function.hfunext rfl
      intro second second' hsecond
      cases hsecond
      apply Function.hfunext rfl
      intro operation operation' hoperation
      cases hoperation
      change HEq
        (cast (Q.property.operation_type_eq
          (f.hom.upper.objectMap
            (canonicalObjectNormalization P.obj first))
          (f.hom.upper.objectMap
            (canonicalObjectNormalization P.obj second)))
          (f.hom.upper.operationMap
            (cast (P.property.operation_type_eq first second) operation)))
        (f.hom.upper.operationMap
          (cast (P.property.operation_type_eq first second) operation))
      exact cast_heq
        (Q.property.operation_type_eq
          (f.hom.upper.objectMap
            (canonicalObjectNormalization P.obj first))
          (f.hom.upper.objectMap
            (canonicalObjectNormalization P.obj second)))
        (f.hom.upper.operationMap
          (cast (P.property.operation_type_eq first second) operation))
    · rfl
    · rfl
    · rfl

/-- The admissible package normalization is idempotent.  This packages the
existing total-morphism computation for the later Karoubi construction. -/
theorem canonicalPackageNormalization_idem
    {U : AtomCarrier.{u}} (P : CanonicalNormalizationAdmissiblePackage U) :
    canonicalPackageNormalization P ≫ canonicalPackageNormalization P =
      canonicalPackageNormalization P := by
  apply ObjectProperty.hom_ext
  exact canonicalObjectNormalizationTotal_comp P.obj P.property

/-- G-119(D)'s base computation: package projection sends the canonical
normalization to the identity of the existing package point. -/
theorem packageProjection_canonicalPackageNormalization
    {U : AtomCarrier.{u}} (P : CanonicalNormalizationAdmissiblePackage U) :
    (packageProjection U).map (canonicalPackageNormalization P).hom =
      𝟙 (packagePoint P.obj) :=
  rfl

#assert_standard_axioms_only AAT.AG.RealizationComparisonIdempotents

end AAT.AG.RealizationComparisonIdempotents
