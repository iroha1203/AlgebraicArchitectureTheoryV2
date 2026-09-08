import ResearchLean.AG.RealizationComparisonIdempotents.KaroubiArrowEquivalence
import Mathlib.CategoryTheory.Idempotents.FunctorExtension

/-!
# Functorial naturality of the Karoubi--arrow equivalence

This file constructs G-119(A2).  For every functor `F : E ⥤ E'`, the
equivalence functors of A1 commute with the induced Karoubi and arrow functors
up to a natural isomorphism.  Its endpoint components are the Karoubi
identities with raw maps `F(e)` and `F(d)`.  The component family satisfies
identity and composition coherence.

## Implementation notes

The Karoubi action is mathlib's `functorExtension₂`; it is not reimplemented
here.  The two routes retain different comparison expressions,
`F.map (e ≫ c ≫ d)` and `F.map e ≫ F.map c ≫ F.map d`, so a functor equality
would hide the required endpoint data.  We instead choose an explicit natural
isomorphism whose endpoints are Karoubi identities.  This also rules out the
rejected alternatives of treating the routes as definitionally equal or using
raw identities at their endpoints.
-/

open CategoryTheory CategoryTheory.Idempotents

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace AAT.AG.RealizationComparisonIdempotents

variable {E : Type u₁} [Category.{v₁} E]
variable {E' : Type u₂} [Category.{v₂} E']
variable {E'' : Type u₃} [Category.{v₃} E'']

/-- The induced functor on `Karoubi (Arrow E)`. -/
def karoubiArrowMap (F : E ⥤ E') : Karoubi (Arrow E) ⥤ Karoubi (Arrow E') :=
  (functorExtension₂ (Arrow E) (Arrow E')).obj F.mapArrow

/-- The induced functor on `Arrow (Karoubi E)`. -/
def arrowKaroubiMap (F : E ⥤ E') : Arrow (Karoubi E) ⥤ Arrow (Karoubi E') :=
  ((functorExtension₂ E E').obj F).mapArrow

/-- Normalization rule exposing the raw comparison after applying `Kar(Arr(F))`. -/
@[simp]
theorem karoubiArrowMap_obj_X_hom (F : E ⥤ E') (P : Karoubi (Arrow E)) :
    ((karoubiArrowMap F).obj P).X.hom = F.map P.X.hom :=
  rfl

/-- Normalization rule exposing the source idempotent after `Kar(Arr(F))`. -/
@[simp]
theorem karoubiArrowMap_obj_p_left (F : E ⥤ E') (P : Karoubi (Arrow E)) :
    ((karoubiArrowMap F).obj P).p.left = F.map P.p.left :=
  rfl

/-- Normalization rule exposing the target idempotent after `Kar(Arr(F))`. -/
@[simp]
theorem karoubiArrowMap_obj_p_right (F : E ⥤ E') (P : Karoubi (Arrow E)) :
    ((karoubiArrowMap F).obj P).p.right = F.map P.p.right :=
  rfl

/-- Normalization rule exposing the source endpoint map after `Arr(Kar(F))`. -/
@[simp]
theorem arrowKaroubiMap_map_left_f
    (F : E ⥤ E') {P Q : Arrow (Karoubi E)} (f : P ⟶ Q) :
    ((arrowKaroubiMap F).map f).left.f = F.map f.left.f :=
  rfl

/-- Normalization rule exposing the target endpoint map after `Arr(Kar(F))`. -/
@[simp]
theorem arrowKaroubiMap_map_right_f
    (F : E ⥤ E') {P Q : Arrow (Karoubi E)} (f : P ⟶ Q) :
    ((arrowKaroubiMap F).map f).right.f = F.map f.right.f :=
  rfl

/-- First route around the A2 square: compare first, then apply `F`. -/
def karoubiArrowNaturalityLeft (F : E ⥤ E') :
    Karoubi (Arrow E) ⥤ Arrow (Karoubi E') :=
  karoubiArrowToArrowKaroubi (E := E) ⋙ arrowKaroubiMap F

/-- Second route around the A2 square: apply `F` first, then compare. -/
def karoubiArrowNaturalityRight (F : E ⥤ E') :
    Karoubi (Arrow E) ⥤ Arrow (Karoubi E') :=
  karoubiArrowMap F ⋙ karoubiArrowToArrowKaroubi (E := E')

/-- Normalization rule exposing the source idempotent on the compare-then-map route. -/
@[simp]
theorem karoubiArrowNaturalityLeft_obj_left_p
    (F : E ⥤ E') (P : Karoubi (Arrow E)) :
    ((karoubiArrowNaturalityLeft F).obj P).left.p = F.map P.p.left :=
  rfl

/-- Normalization rule exposing the target idempotent on the compare-then-map route. -/
@[simp]
theorem karoubiArrowNaturalityLeft_obj_right_p
    (F : E ⥤ E') (P : Karoubi (Arrow E)) :
    ((karoubiArrowNaturalityLeft F).obj P).right.p = F.map P.p.right :=
  rfl

/-- The compare-then-map route keeps the normalized comparison inside `F.map`. -/
@[simp]
theorem karoubiArrowNaturalityLeft_obj_hom_f
    (F : E ⥤ E') (P : Karoubi (Arrow E)) :
    ((karoubiArrowNaturalityLeft F).obj P).hom.f =
      F.map (P.p.left ≫ P.X.hom ≫ P.p.right) :=
  rfl

/-- The map-then-compare route normalizes the three mapped factors separately. -/
@[simp]
theorem karoubiArrowNaturalityRight_obj_hom_f
    (F : E ⥤ E') (P : Karoubi (Arrow E)) :
    ((karoubiArrowNaturalityRight F).obj P).hom.f =
      F.map P.p.left ≫ F.map P.X.hom ≫ F.map P.p.right :=
  rfl

/-- Normalization rule for the source map on the compare-then-map route. -/
@[simp]
theorem karoubiArrowNaturalityLeft_map_left_f
    (F : E ⥤ E') {P Q : Karoubi (Arrow E)} (f : P ⟶ Q) :
    ((karoubiArrowNaturalityLeft F).map f).left.f = F.map f.f.left :=
  rfl

/-- Normalization rule for the target map on the compare-then-map route. -/
@[simp]
theorem karoubiArrowNaturalityLeft_map_right_f
    (F : E ⥤ E') {P Q : Karoubi (Arrow E)} (f : P ⟶ Q) :
    ((karoubiArrowNaturalityLeft F).map f).right.f = F.map f.f.right :=
  rfl

/-- Normalization rule for the source map on the map-then-compare route. -/
@[simp]
theorem karoubiArrowNaturalityRight_map_left_f
    (F : E ⥤ E') {P Q : Karoubi (Arrow E)} (f : P ⟶ Q) :
    ((karoubiArrowNaturalityRight F).map f).left.f = F.map f.f.left :=
  rfl

/-- Normalization rule for the target map on the map-then-compare route. -/
@[simp]
theorem karoubiArrowNaturalityRight_map_right_f
    (F : E ⥤ E') {P Q : Karoubi (Arrow E)} (f : P ⟶ Q) :
    ((karoubiArrowNaturalityRight F).map f).right.f = F.map f.f.right :=
  rfl

/-- The A2 component at an idempotent square.  Both endpoint isomorphisms are
Karoubi identities, with underlying maps `F(e)` and `F(d)`. -/
def karoubiArrowNaturalityIsoApp (F : E ⥤ E') (P : Karoubi (Arrow E)) :
    (karoubiArrowNaturalityLeft F).obj P ≅
      (karoubiArrowNaturalityRight F).obj P :=
  Arrow.isoMk (Iso.refl _) (Iso.refl _) (by
    apply Karoubi.Hom.ext
    simp only [Karoubi.comp_f, Iso.refl_hom, Karoubi.id_f]
    rw [karoubiArrowNaturalityLeft_obj_left_p,
      karoubiArrowNaturalityLeft_obj_right_p,
      karoubiArrowNaturalityLeft_obj_hom_f,
      karoubiArrowNaturalityRight_obj_hom_f]
    have he : F.map P.p.left ≫ F.map P.p.left = F.map P.p.left := by
      rw [← F.map_comp, congrArg F.map
        (by simpa only [Arrow.comp_left] using
          congrArg CommaMorphism.left P.idem)]
    have hd : F.map P.p.right ≫ F.map P.p.right = F.map P.p.right := by
      rw [← F.map_comp, congrArg F.map
        (by simpa only [Arrow.comp_right] using
          congrArg CommaMorphism.right P.idem)]
    rw [F.map_comp, F.map_comp]
    calc
      F.map P.p.left ≫
            (F.map P.p.left ≫ F.map P.X.hom ≫ F.map P.p.right) =
          F.map P.p.left ≫ F.map P.X.hom ≫ F.map P.p.right := by
            rw [← Category.assoc, he]
      _ = (F.map P.p.left ≫ F.map P.X.hom ≫ F.map P.p.right) ≫
            F.map P.p.right := by
            simp only [Category.assoc, hd])

/-- The component hom at the source endpoint reduces to the mapped idempotent. -/
@[simp]
theorem karoubiArrowNaturalityIsoApp_hom_left_f
    (F : E ⥤ E') (P : Karoubi (Arrow E)) :
    ((karoubiArrowNaturalityIsoApp F P).hom.left).f = F.map P.p.left :=
  rfl

/-- The component hom at the target endpoint reduces to the mapped idempotent. -/
@[simp]
theorem karoubiArrowNaturalityIsoApp_hom_right_f
    (F : E ⥤ E') (P : Karoubi (Arrow E)) :
    ((karoubiArrowNaturalityIsoApp F P).hom.right).f = F.map P.p.right :=
  rfl

/-- The component inverse at the source endpoint reduces to the mapped idempotent. -/
@[simp]
theorem karoubiArrowNaturalityIsoApp_inv_left_f
    (F : E ⥤ E') (P : Karoubi (Arrow E)) :
    ((karoubiArrowNaturalityIsoApp F P).inv.left).f = F.map P.p.left :=
  rfl

/-- The component inverse at the target endpoint reduces to the mapped idempotent. -/
@[simp]
theorem karoubiArrowNaturalityIsoApp_inv_right_f
    (F : E ⥤ E') (P : Karoubi (Arrow E)) :
    ((karoubiArrowNaturalityIsoApp F P).inv.right).f = F.map P.p.right :=
  rfl

/-- G-119(A2): the Karoubi--arrow equivalence is natural in the category. -/
def karoubiArrowNaturalityIso (F : E ⥤ E') :
    karoubiArrowNaturalityLeft F ≅ karoubiArrowNaturalityRight F :=
  NatIso.ofComponents (karoubiArrowNaturalityIsoApp F) (by
    intro P Q f
    apply Arrow.hom_ext
    · apply Karoubi.Hom.ext
      change
        ((karoubiArrowNaturalityLeft F).map f).left.f ≫
            ((karoubiArrowNaturalityIsoApp F Q).hom.left).f =
          ((karoubiArrowNaturalityIsoApp F P).hom.left).f ≫
            ((karoubiArrowNaturalityRight F).map f).left.f
      rw [karoubiArrowNaturalityLeft_map_left_f,
        karoubiArrowNaturalityRight_map_left_f,
        karoubiArrowNaturalityIsoApp_hom_left_f,
        karoubiArrowNaturalityIsoApp_hom_left_f]
      exact (Karoubi.p_comm
        (((functorExtension₂ E E').obj F).map (karoubiArrowLeftMap f))).symm
    · apply Karoubi.Hom.ext
      change
        ((karoubiArrowNaturalityLeft F).map f).right.f ≫
            ((karoubiArrowNaturalityIsoApp F Q).hom.right).f =
          ((karoubiArrowNaturalityIsoApp F P).hom.right).f ≫
            ((karoubiArrowNaturalityRight F).map f).right.f
      rw [karoubiArrowNaturalityLeft_map_right_f,
        karoubiArrowNaturalityRight_map_right_f,
        karoubiArrowNaturalityIsoApp_hom_right_f,
        karoubiArrowNaturalityIsoApp_hom_right_f]
      exact (Karoubi.p_comm
        (((functorExtension₂ E E').obj F).map (karoubiArrowRightMap f))).symm)

/-- The packaged natural isomorphism hom exposes the source endpoint without unfolding. -/
@[simp]
theorem karoubiArrowNaturalityIso_hom_app_left_f
    (F : E ⥤ E') (P : Karoubi (Arrow E)) :
    ((karoubiArrowNaturalityIso F).hom.app P).left.f = F.map P.p.left :=
  rfl

/-- The packaged natural isomorphism hom exposes the target endpoint without unfolding. -/
@[simp]
theorem karoubiArrowNaturalityIso_hom_app_right_f
    (F : E ⥤ E') (P : Karoubi (Arrow E)) :
    ((karoubiArrowNaturalityIso F).hom.app P).right.f = F.map P.p.right :=
  rfl

/-- The packaged natural isomorphism inverse exposes the source endpoint without unfolding. -/
@[simp]
theorem karoubiArrowNaturalityIso_inv_app_left_f
    (F : E ⥤ E') (P : Karoubi (Arrow E)) :
    ((karoubiArrowNaturalityIso F).inv.app P).left.f = F.map P.p.left :=
  rfl

/-- The packaged natural isomorphism inverse exposes the target endpoint without unfolding. -/
@[simp]
theorem karoubiArrowNaturalityIso_inv_app_right_f
    (F : E ⥤ E') (P : Karoubi (Arrow E)) :
    ((karoubiArrowNaturalityIso F).inv.app P).right.f = F.map P.p.right :=
  rfl

/-- Identity coherence: the A2 component for the identity functor is the
identity isomorphism in the arrow category. -/
theorem karoubiArrowNaturalityIsoApp_id (P : Karoubi (Arrow E)) :
    karoubiArrowNaturalityIsoApp (𝟭 E : E ⥤ E) P = Iso.refl _ := by
  apply Iso.ext
  apply Arrow.hom_ext
  · apply Karoubi.Hom.ext
    change
      ((karoubiArrowNaturalityIsoApp (𝟭 E : E ⥤ E) P).hom.left).f =
        ((Iso.refl ((karoubiArrowNaturalityLeft (𝟭 E)).obj P)).hom.left).f
    rw [karoubiArrowNaturalityIsoApp_hom_left_f]
    rfl
  · apply Karoubi.Hom.ext
    change
      ((karoubiArrowNaturalityIsoApp (𝟭 E : E ⥤ E) P).hom.right).f =
        ((Iso.refl ((karoubiArrowNaturalityLeft (𝟭 E)).obj P)).hom.right).f
    rw [karoubiArrowNaturalityIsoApp_hom_right_f]
    rfl

/-- Composition coherence: the component for `F ⋙ G` is the composite of the
component for `F`, mapped by `G`, with the component for `G`. -/
theorem karoubiArrowNaturalityIsoApp_comp
    (F : E ⥤ E') (G : E' ⥤ E'') (P : Karoubi (Arrow E)) :
    karoubiArrowNaturalityIsoApp (F ⋙ G) P =
      (arrowKaroubiMap G).mapIso (karoubiArrowNaturalityIsoApp F P) ≪≫
        karoubiArrowNaturalityIsoApp G ((karoubiArrowMap F).obj P) := by
  apply Iso.ext
  apply Arrow.hom_ext
  · apply Karoubi.Hom.ext
    change
      ((karoubiArrowNaturalityIsoApp (F ⋙ G) P).hom.left).f =
        ((arrowKaroubiMap G).map
              (karoubiArrowNaturalityIsoApp F P).hom).left.f ≫
          ((karoubiArrowNaturalityIsoApp G
              ((karoubiArrowMap F).obj P)).hom.left).f
    rw [karoubiArrowNaturalityIsoApp_hom_left_f,
      arrowKaroubiMap_map_left_f,
      karoubiArrowNaturalityIsoApp_hom_left_f,
      karoubiArrowNaturalityIsoApp_hom_left_f,
      karoubiArrowMap_obj_p_left]
    exact (((functorExtension₂ E E'').obj (F ⋙ G)).obj
      (karoubiArrowSource P)).idem.symm
  · apply Karoubi.Hom.ext
    change
      ((karoubiArrowNaturalityIsoApp (F ⋙ G) P).hom.right).f =
        ((arrowKaroubiMap G).map
              (karoubiArrowNaturalityIsoApp F P).hom).right.f ≫
          ((karoubiArrowNaturalityIsoApp G
              ((karoubiArrowMap F).obj P)).hom.right).f
    rw [karoubiArrowNaturalityIsoApp_hom_right_f,
      arrowKaroubiMap_map_right_f,
      karoubiArrowNaturalityIsoApp_hom_right_f,
      karoubiArrowNaturalityIsoApp_hom_right_f,
      karoubiArrowMap_obj_p_right]
    exact (((functorExtension₂ E E'').obj (F ⋙ G)).obj
      (karoubiArrowTarget P)).idem.symm

#assert_standard_axioms_only AAT.AG.RealizationComparisonIdempotents

end AAT.AG.RealizationComparisonIdempotents
