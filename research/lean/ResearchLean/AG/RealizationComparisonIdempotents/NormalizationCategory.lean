import ResearchLean.AG.RealizationComparisonIdempotents.CanonicalNormalizationAbsorption
import Mathlib.CategoryTheory.Idempotents.Karoubi

/-!
# The category of canonically normalized package images

This file constructs G-119(D)'s category `N_C`.  Its objects retain an
admissible core package as a label, while a morphism is precisely a raw package
morphism fixed by the canonical idempotents at both endpoints.  The resulting
category embeds fully faithfully into the Karoubi completion, and canonical
normalization defines a full functor into it.

## Implementation notes

The object wrapper is required because `N_C` and the admissible full
subcategory have different morphisms and hence different category structures.
For its Hom type we reuse the Hom of the corresponding mathlib Karoubi objects:
its `comm` field is exactly the required sandwich equality.  This avoids a
duplicate AAT-specific sandwich record.  We do not define `N_C` as the range of
the normalization functor, because that would replace the fixed requirement of
all sandwich morphisms by a selected-image presentation.
-/

open CategoryTheory CategoryTheory.Idempotents

namespace AAT.AG.RealizationComparisonIdempotents

open AtomFoundation

universe u

/-- An object of G-119(D)'s normalized category retains its admissible core
package as an explicit label. -/
structure NormalizedPackageObject (U : AtomCarrier.{u}) where
  /-- The underlying admissible package label; no image or fixed-point condition
  is imposed on objects of the normalized category. -/
  obj : CanonicalNormalizationAdmissiblePackage U

/-- Two normalized-package objects are equal when their underlying package
labels are equal.  This is the basic no-unfold extensionality API for `N_C`. -/
@[ext]
theorem normalizedPackageObject_ext {U : AtomCarrier.{u}}
    {P Q : NormalizedPackageObject U} (h : P.obj = Q.obj) : P = Q := by
  cases P
  cases Q
  cases h
  rfl

/-- The Karoubi object `(P,e_P)` associated with a labelled normalized-package
object.  Its idempotence is supplied by the reviewed D1 theorem. -/
noncomputable def normalizedPackageKaroubiObject
    {U : AtomCarrier.{u}} (P : CanonicalNormalizationAdmissiblePackage U) :
    Karoubi (CanonicalNormalizationAdmissiblePackage U) where
  X := P
  p := canonicalPackageNormalization P
  idem := canonicalPackageNormalization_idem P

/-- G-119(D)'s category `N_C`.  Its morphisms are exactly the Karoubi morphisms
between `(P,e_P)` and `(Q,e_Q)`, so their `comm` field is the required equation
`e_P ≫ a ≫ e_Q = a`; identities and composition have underlying maps `e_P`
and raw composition, respectively. -/
noncomputable instance normalizedPackageCategory (U : AtomCarrier.{u}) :
    Category (NormalizedPackageObject U) where
  Hom P Q :=
    normalizedPackageKaroubiObject P.obj ⟶
      normalizedPackageKaroubiObject Q.obj
  id P := 𝟙 (normalizedPackageKaroubiObject P.obj)
  comp f g := f ≫ g
  id_comp := by simp
  comp_id := by simp
  assoc := by simp

/-- Normalization rule: the underlying raw map of an `N_C` identity reduces to
the canonical idempotent of its labelled package. -/
@[simp]
theorem normalizedPackageCategory_id_f
    {U : AtomCarrier.{u}} (P : NormalizedPackageObject U) :
    (𝟙 P : P ⟶ P).f = canonicalPackageNormalization P.obj :=
  rfl

/-- Normalization rule: the underlying raw map of an `N_C` composite reduces
to the raw composite of the two underlying sandwich maps. -/
@[simp]
theorem normalizedPackageCategory_comp_f
    {U : AtomCarrier.{u}} {P Q R : NormalizedPackageObject U}
    (f : P ⟶ Q) (g : Q ⟶ R) :
    (f ≫ g).f = f.f ≫ g.f :=
  rfl

/-- Every `N_C` morphism satisfies the fixed two-endpoint sandwich equation in
the admissible package category. -/
theorem normalizedPackageHom_sandwich
    {U : AtomCarrier.{u}} {P Q : NormalizedPackageObject U}
    (f : P ⟶ Q) :
    canonicalPackageNormalization P.obj ≫ f.f ≫
        canonicalPackageNormalization Q.obj = f.f :=
  f.comm

/-- G-119(D)'s comparison `K : N_C ⥤ Kar(C)`, retaining the labelled package,
its canonical idempotent, and every sandwich morphism without alteration. -/
noncomputable def normalizedPackageKaroubiFunctor (U : AtomCarrier.{u}) :
    NormalizedPackageObject U ⥤
      Karoubi (CanonicalNormalizationAdmissiblePackage U) where
  obj P := normalizedPackageKaroubiObject P.obj
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Normalization rule: `K` sends an object label to its canonical Karoubi
object. -/
@[simp]
theorem normalizedPackageKaroubiFunctor_obj
    {U : AtomCarrier.{u}} (P : NormalizedPackageObject U) :
    (normalizedPackageKaroubiFunctor U).obj P =
      normalizedPackageKaroubiObject P.obj :=
  rfl

/-- Normalization rule: the raw map underlying `K(f)` is the raw sandwich map
underlying `f`. -/
@[simp]
theorem normalizedPackageKaroubiFunctor_map_f
    {U : AtomCarrier.{u}} {P Q : NormalizedPackageObject U}
    (f : P ⟶ Q) :
    ((normalizedPackageKaroubiFunctor U).map f).f = f.f :=
  rfl

/-- The comparison `K` is faithful because it retains each sandwich morphism
itself. -/
instance normalizedPackageKaroubiFunctor_faithful (U : AtomCarrier.{u}) :
    (normalizedPackageKaroubiFunctor U).Faithful where
  map_injective h := h

/-- The comparison `K` is full because every Karoubi morphism between its
objects is already an `N_C` sandwich morphism. -/
instance normalizedPackageKaroubiFunctor_full (U : AtomCarrier.{u}) :
    (normalizedPackageKaroubiFunctor U).Full where
  map_surjective f := ⟨f, rfl⟩

/-- G-119(D)'s canonical normalization functor `N : C ⥤ N_C`.  It is the
identity on package labels and sends `f` to `e_P ≫ f`; D1 absorption proves
that this raw map satisfies the target sandwich equation. -/
noncomputable def packageNormalizationFunctor (U : AtomCarrier.{u}) :
    CanonicalNormalizationAdmissiblePackage U ⥤
      NormalizedPackageObject U where
  obj P := ⟨P⟩
  map := fun {P _} f =>
    { f := canonicalPackageNormalization P ≫ f
      comm := by
        change canonicalPackageNormalization P ≫
            (canonicalPackageNormalization P ≫ f) ≫
              canonicalPackageNormalization _ =
          canonicalPackageNormalization P ≫ f
        rw [← Category.assoc]
        rw [← Category.assoc
          (canonicalPackageNormalization P)
          (canonicalPackageNormalization P) f,
          canonicalPackageNormalization_idem]
        exact canonicalPackageNormalization_absorption f }
  map_id P := by
    apply Karoubi.Hom.ext
    exact Category.comp_id _
  map_comp f g := by
    apply Karoubi.Hom.ext
    change canonicalPackageNormalization _ ≫ (f ≫ g) =
      (canonicalPackageNormalization _ ≫ f) ≫
        (canonicalPackageNormalization _ ≫ g)
    simpa only [Category.assoc] using congrArg
      (fun h => h ≫ g)
      (canonicalPackageNormalization_absorption f).symm

/-- Normalization rule: `N` preserves the admissible package label exactly. -/
@[simp]
theorem packageNormalizationFunctor_obj_obj
    {U : AtomCarrier.{u}} (P : CanonicalNormalizationAdmissiblePackage U) :
    ((packageNormalizationFunctor U).obj P).obj = P :=
  rfl

/-- Normalization rule: the raw map underlying `N(f)` is `e_P ≫ f`, matching
the fixed target's conventional `f e_P`. -/
@[simp]
theorem packageNormalizationFunctor_map_f
    {U : AtomCarrier.{u}}
    {P Q : CanonicalNormalizationAdmissiblePackage U} (f : P ⟶ Q) :
    ((packageNormalizationFunctor U).map f).f =
      canonicalPackageNormalization P ≫ f :=
  rfl

/-- G-119(D): `N` is full for arbitrary endpoint packages and arbitrary
sandwich morphisms.  The preimage is the sandwich morphism's own raw map; its
left normalization law identifies the resulting `N`-image with the original
morphism. -/
instance packageNormalizationFunctor_full (U : AtomCarrier.{u}) :
    (packageNormalizationFunctor U).Full where
  map_surjective f := by
    refine ⟨f.f, ?_⟩
    apply Karoubi.Hom.ext
    exact Karoubi.p_comp f

#assert_standard_axioms_only AAT.AG.RealizationComparisonIdempotents

end AAT.AG.RealizationComparisonIdempotents
