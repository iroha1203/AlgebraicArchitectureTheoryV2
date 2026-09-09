import ResearchLean.AG.RealizationComparisonIdempotents.NormalizationCategory
import ResearchLean.AG.RealizationComparisonIdempotents.FunctorNaturality

/-!
# Projection of the canonical normalization category

This file constructs G-119(D)'s comparison from normalized package arrows to
`M(E_core) = Arrow (Karoubi E_core)`.  It applies the standard Karoubi action
to the full-subcategory inclusion and exposes the normalized comparison as the
raw comparison precomposed by its source idempotent.

It also constructs the bottom projection `π_N : N_C ⥤ B`.  The equality
`π_N N = π V` is proved on both objects and morphisms, using the independently
proved computation `π(e_P)=1` rather than adding a preservation premise.

## Implementation notes

The induced Karoubi and arrow functors are mathlib's `functorExtension₂` and
`Functor.mapArrow`.  Reusing them keeps this comparison on the same
`Arrow (Karoubi _)` surface as clause A and avoids a second, definitionally
unrelated presentation of `M(E_core)`.
-/

open CategoryTheory CategoryTheory.Idempotents

namespace AAT.AG.RealizationComparisonIdempotents

open AtomFoundation

universe u

/-- G-119(D)'s inclusion `V : C ⥤ E_core`; it forgets only the proof that an
object satisfies the fixed admissibility predicate and retains every raw total
morphism. -/
def canonicalNormalizationCoreInclusion (U : AtomCarrier.{u}) :
    CanonicalNormalizationAdmissiblePackage U ⥤ AATCorePackage U :=
  (canonicalNormalizationAdmissibleProperty U).ι

/-- The comparison `Kar(V)K : N_C ⥤ Kar(E_core)`, formed by the standard
Karoubi action on the admissible-package inclusion. -/
noncomputable def normalizedPackageCoreKaroubiFunctor (U : AtomCarrier.{u}) :
    NormalizedPackageObject U ⥤ Karoubi (AATCorePackage U) :=
  normalizedPackageKaroubiFunctor U ⋙
    (functorExtension₂
      (CanonicalNormalizationAdmissiblePackage U)
      (AATCorePackage U)).obj (canonicalNormalizationCoreInclusion U)

/-- The induced comparison `Arr(N_C) ⥤ M(E_core)` obtained from `Kar(V)K`.
Its codomain is the fixed realization-comparison category
`Arrow (Karoubi E_core)`. -/
noncomputable def normalizedPackageArrowCoreComparison (U : AtomCarrier.{u}) :
    Arrow (NormalizedPackageObject U) ⥤
      Arrow (Karoubi (AATCorePackage U)) :=
  (normalizedPackageKaroubiFunctor U).mapArrow ⋙
    arrowKaroubiMap (canonicalNormalizationCoreInclusion U)

/-- The two-stage definition of the normalized-package arrow comparison is
definitionally the arrow functor induced by `Kar(V)K`. -/
theorem normalizedPackageArrowCoreComparison_eq (U : AtomCarrier.{u}) :
    normalizedPackageArrowCoreComparison U =
      (normalizedPackageCoreKaroubiFunctor U).mapArrow :=
  rfl

/-- Normalization rule: the comparison underlying the image of an `N_C` arrow
reduces to that arrow's raw total morphism after forgetting admissibility. -/
@[simp]
theorem normalizedPackageArrowCoreComparison_obj_hom_f
    {U : AtomCarrier.{u}} (c : Arrow (NormalizedPackageObject U)) :
    ((normalizedPackageArrowCoreComparison U).obj c).hom.f = c.hom.f.hom :=
  rfl

/-- The normalized comparison from raw admissible-package arrows to
`M(E_core)`: normalize by `N`, then apply the comparison induced by `Kar(V)K`.
-/
noncomputable def canonicalNormalizedCoreComparison (U : AtomCarrier.{u}) :
    Arrow (CanonicalNormalizationAdmissiblePackage U) ⥤
      Arrow (Karoubi (AATCorePackage U)) :=
  (packageNormalizationFunctor U).mapArrow ⋙
    normalizedPackageArrowCoreComparison U

/-- Normalization rule: the underlying comparison after canonical
normalization is `e_P ≫ c`, the Lean-order form of the fixed target's
`c e_P`. -/
@[simp]
theorem canonicalNormalizedCoreComparison_obj_hom_f
    {U : AtomCarrier.{u}}
    (c : Arrow (CanonicalNormalizationAdmissiblePackage U)) :
    ((canonicalNormalizedCoreComparison U).obj c).hom.f =
      (canonicalPackageNormalization c.left).hom ≫ c.hom.hom :=
  rfl

/-- G-119(D)'s bottom projection `π_N : N_C ⥤ B`.  It sends a labelled
package to its existing package point and a sandwich morphism to the base map
of its underlying raw total morphism. -/
noncomputable def normalizedPackageProjection (U : AtomCarrier.{u}) :
    NormalizedPackageObject U ⥤ ExtractionInstance U where
  obj P := packagePoint P.obj.obj
  map f := f.f.hom.base
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Normalization rule: `π_N` sends a normalized-package label to the package
point of its underlying core package. -/
@[simp]
theorem normalizedPackageProjection_obj
    {U : AtomCarrier.{u}} (P : NormalizedPackageObject U) :
    (normalizedPackageProjection U).obj P = packagePoint P.obj.obj :=
  rfl

/-- Normalization rule: `π_N` maps a sandwich morphism to the base component
of its underlying raw total morphism. -/
@[simp]
theorem normalizedPackageProjection_map
    {U : AtomCarrier.{u}} {P Q : NormalizedPackageObject U} (f : P ⟶ Q) :
    (normalizedPackageProjection U).map f = f.f.hom.base :=
  rfl

/-- On objects, bottom projection after normalization agrees with first
forgetting admissibility and then applying the existing package projection. -/
@[simp]
theorem normalizedPackageProjection_normalization_obj
    {U : AtomCarrier.{u}} (P : CanonicalNormalizationAdmissiblePackage U) :
    ((packageNormalizationFunctor U ⋙ normalizedPackageProjection U).obj P) =
      ((canonicalNormalizationCoreInclusion U ⋙ packageProjection U).obj P) :=
  rfl

/-- On morphisms, `π_N N` reduces to `π V`: the source idempotent disappears
because `π(e_P)=1`, leaving precisely the original base map. -/
@[simp]
theorem normalizedPackageProjection_normalization_map
    {U : AtomCarrier.{u}}
    {P Q : CanonicalNormalizationAdmissiblePackage U} (f : P ⟶ Q) :
    ((packageNormalizationFunctor U ⋙ normalizedPackageProjection U).map f) =
      ((canonicalNormalizationCoreInclusion U ⋙ packageProjection U).map f) := by
  change (packageProjection U).map (canonicalPackageNormalization P).hom ≫
      (packageProjection U).map f.hom = (packageProjection U).map f.hom
  rw [packageProjection_canonicalPackageNormalization]
  exact Category.id_comp _

/-- G-119(D)'s functor equality `π_N N = π V`, established by the preceding
object and morphism computations. -/
theorem normalizedPackageProjection_normalization_eq {U : AtomCarrier.{u}} :
    packageNormalizationFunctor U ⋙ normalizedPackageProjection U =
      canonicalNormalizationCoreInclusion U ⋙ packageProjection U := by
  exact CategoryTheory.Functor.ext
    (F := packageNormalizationFunctor U ⋙ normalizedPackageProjection U)
    (G := canonicalNormalizationCoreInclusion U ⋙ packageProjection U)
    (fun _ => rfl)
    (fun P Q f => by
      simpa using normalizedPackageProjection_normalization_map f)

#assert_standard_axioms_only AAT.AG.RealizationComparisonIdempotents

end AAT.AG.RealizationComparisonIdempotents
