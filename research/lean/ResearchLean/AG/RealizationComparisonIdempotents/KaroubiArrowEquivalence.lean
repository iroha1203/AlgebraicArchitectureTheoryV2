import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.CategoryTheory.Idempotents.Karoubi
import Formal.Util.AssertStandardAxioms

/-!
# Karoubi completion and arrow categories

This file constructs clause A of G-119: the equivalence between idempotent
squares of arrows and arrows between Karoubi objects.  The comparison arrow is
the independently normalized composite `e ≫ c ≫ d`; it is not obtained by
assuming that the raw comparison already lies in the selected image.

Implementation notes: the construction uses mathlib's `Arrow` and `Karoubi`
categories directly.  A custom comparison record was rejected because it
would hide the universal categorical content that clause A asks to expose.
-/

namespace AAT.AG.RealizationComparisonIdempotents

open CategoryTheory
open CategoryTheory.Idempotents

universe v u

variable {E : Type u} [Category.{v} E]

private theorem karoubiArrow_left_idem (P : Karoubi (Arrow E)) :
    P.p.left ≫ P.p.left = P.p.left := by
  simpa only [Arrow.comp_left] using congrArg CommaMorphism.left P.idem

private theorem karoubiArrow_right_idem (P : Karoubi (Arrow E)) :
    P.p.right ≫ P.p.right = P.p.right := by
  simpa only [Arrow.comp_right] using congrArg CommaMorphism.right P.idem

/-- The source Karoubi object of an idempotent square. -/
def karoubiArrowSource (P : Karoubi (Arrow E)) : Karoubi E where
  X := P.X.left
  p := P.p.left
  idem := by
    simpa only [Arrow.comp_left] using congrArg CommaMorphism.left P.idem

/-- The target Karoubi object of an idempotent square. -/
def karoubiArrowTarget (P : Karoubi (Arrow E)) : Karoubi E where
  X := P.X.right
  p := P.p.right
  idem := by
    simpa only [Arrow.comp_right] using congrArg CommaMorphism.right P.idem

/-- Clause A object map: `(c,e,d)` is sent to the image comparison `e ≫ c ≫ d`. -/
def karoubiArrowToArrowKaroubiObj (P : Karoubi (Arrow E)) : Arrow (Karoubi E) :=
  { left := karoubiArrowSource P
    right := karoubiArrowTarget P
    hom :=
      { f := P.p.left ≫ P.X.hom ≫ P.p.right
        comm := by
          change P.p.left ≫ (P.p.left ≫ P.X.hom ≫ P.p.right) ≫ P.p.right = _
          simp [Category.assoc, karoubiArrow_right_idem] } }

/-- Evaluation of the normalized comparison underlying clause A's object map. -/
@[simp]
theorem karoubiArrowToArrowKaroubiObj_hom_f (P : Karoubi (Arrow E)) :
    (karoubiArrowToArrowKaroubiObj P).hom.f =
      P.p.left ≫ P.X.hom ≫ P.p.right :=
  rfl

/-- The retained source endpoint of a morphism of idempotent squares. -/
def karoubiArrowLeftMap {P Q : Karoubi (Arrow E)} (f : P ⟶ Q) :
    karoubiArrowSource P ⟶ karoubiArrowSource Q where
  f := f.f.left
  comm := by
    simpa only [Arrow.comp_left, karoubiArrowSource] using
      congrArg CommaMorphism.left f.comm

/-- The retained target endpoint of a morphism of idempotent squares. -/
def karoubiArrowRightMap {P Q : Karoubi (Arrow E)} (f : P ⟶ Q) :
    karoubiArrowTarget P ⟶ karoubiArrowTarget Q where
  f := f.f.right
  comm := by
    simpa only [Arrow.comp_right, karoubiArrowTarget] using
      congrArg CommaMorphism.right f.comm

/-- Clause A forward functor.  A morphism retains its two endpoint maps. -/
def karoubiArrowToArrowKaroubi : Karoubi (Arrow E) ⥤ Arrow (Karoubi E) where
  obj := karoubiArrowToArrowKaroubiObj
  map {P Q} f :=
    Arrow.homMk
      (karoubiArrowLeftMap f)
      (karoubiArrowRightMap f)
      (by
        apply Karoubi.Hom.ext
        change f.f.left ≫ (Q.p.left ≫ Q.X.hom ≫ Q.p.right) =
          (P.p.left ≫ P.X.hom ≫ P.p.right) ≫ f.f.right
        have hleft := Karoubi.comp_p (karoubiArrowLeftMap f)
        change f.f.left ≫ Q.p.left = f.f.left at hleft
        have hright := Karoubi.p_comp (karoubiArrowRightMap f)
        change P.p.right ≫ f.f.right = f.f.right at hright
        have hcomp := Karoubi.comp_p (karoubiArrowRightMap f)
        change f.f.right ≫ Q.p.right = f.f.right at hcomp
        calc
          f.f.left ≫ (Q.p.left ≫ Q.X.hom ≫ Q.p.right) =
              (f.f.left ≫ Q.p.left) ≫ Q.X.hom ≫ Q.p.right := by simp
          _ = f.f.left ≫ Q.X.hom ≫ Q.p.right := by rw [hleft]
          _ = (P.X.hom ≫ f.f.right) ≫ Q.p.right := by
            rw [← Category.assoc, Arrow.w f.f]
          _ = P.X.hom ≫ f.f.right := by simp [Category.assoc, hcomp]
          _ = P.p.left ≫ P.X.hom ≫ f.f.right := by
            rw [← Category.assoc, Arrow.w P.p, Category.assoc, hright]
          _ = (P.p.left ≫ P.X.hom ≫ P.p.right) ≫ f.f.right := by
            simp [Category.assoc, hright])
  map_id P := by
    apply Arrow.hom_ext
    · apply Karoubi.Hom.ext
      rfl
    · apply Karoubi.Hom.ext
      rfl
  map_comp f g := by
    apply Arrow.hom_ext
    · apply Karoubi.Hom.ext
      rfl
    · apply Karoubi.Hom.ext
      rfl

/-- A comparison in `Karoubi E` determines its raw arrow and endpoint idempotent square. -/
def arrowKaroubiToKaroubiArrowObj (P : Arrow (Karoubi E)) : Karoubi (Arrow E) where
  X := { left := P.left.X, right := P.right.X, hom := P.hom.f }
  p := Arrow.homMk P.left.p P.right.p (Karoubi.p_comm P.hom)
  idem := by
    apply Arrow.hom_ext
    · exact P.left.idem
    · exact P.right.idem

/-- Clause A inverse functor. -/
def arrowKaroubiToKaroubiArrow : Arrow (Karoubi E) ⥤ Karoubi (Arrow E) where
  obj := arrowKaroubiToKaroubiArrowObj
  map {P Q} f :=
    { f := Arrow.homMk f.left.f f.right.f (by
          have h := congrArg Karoubi.Hom.f (Arrow.w f)
          simpa only [Karoubi.comp_f, Arrow.mk_hom] using h)
      comm := by
        apply Arrow.hom_ext
        · exact f.left.comm
        · exact f.right.comm }
  map_id P := by
    apply Karoubi.Hom.ext
    apply Arrow.hom_ext <;> rfl
  map_comp f g := by
    apply Karoubi.Hom.ext
    apply Arrow.hom_ext <;> rfl

/-- Unit square.  Both directions have endpoint maps `(e,d)`, which are the
identities of the corresponding Karoubi objects rather than raw identities. -/
def karoubiArrowUnitIsoApp (P : Karoubi (Arrow E)) :
    P ≅ arrowKaroubiToKaroubiArrow.obj (karoubiArrowToArrowKaroubi.obj P) where
  hom :=
    { f := Arrow.homMk P.p.left P.p.right (by
          simp only [arrowKaroubiToKaroubiArrow, arrowKaroubiToKaroubiArrowObj,
            karoubiArrowToArrowKaroubi]
          simp [karoubiArrow_right_idem])
      comm := by
        apply Arrow.hom_ext
        · change P.p.left ≫ P.p.left ≫ P.p.left = P.p.left
          simp [karoubiArrow_left_idem]
        · change P.p.right ≫ P.p.right ≫ P.p.right = P.p.right
          simp [karoubiArrow_right_idem] }
  inv :=
    { f := Arrow.homMk P.p.left P.p.right (by
          simp only [arrowKaroubiToKaroubiArrow, arrowKaroubiToKaroubiArrowObj,
            karoubiArrowToArrowKaroubi]
          simp [karoubiArrow_right_idem])
      comm := by
        apply Arrow.hom_ext
        · change P.p.left ≫ P.p.left ≫ P.p.left = P.p.left
          simp [karoubiArrow_left_idem]
        · change P.p.right ≫ P.p.right ≫ P.p.right = P.p.right
          simp [karoubiArrow_right_idem] }
  hom_inv_id := by
    apply Karoubi.Hom.ext
    apply Arrow.hom_ext
    · exact congrArg CommaMorphism.left P.idem
    · exact congrArg CommaMorphism.right P.idem
  inv_hom_id := by
    apply Karoubi.Hom.ext
    apply Arrow.hom_ext
    · change P.p.left ≫ P.p.left = P.p.left
      exact karoubiArrow_left_idem P
    · change P.p.right ≫ P.p.right = P.p.right
      exact karoubiArrow_right_idem P

/-- The unit natural isomorphism of the comparison equivalence. -/
def karoubiArrowUnitIso :
    𝟭 (Karoubi (Arrow E)) ≅ karoubiArrowToArrowKaroubi ⋙ arrowKaroubiToKaroubiArrow :=
  NatIso.ofComponents karoubiArrowUnitIsoApp (by
    intro P Q f
    apply Karoubi.Hom.ext
    apply Arrow.hom_ext
    · change f.f.left ≫ Q.p.left = P.p.left ≫ f.f.left
      exact (Karoubi.p_comm (karoubiArrowLeftMap f)).symm
    · change f.f.right ≫ Q.p.right = P.p.right ≫ f.f.right
      exact (Karoubi.p_comm (karoubiArrowRightMap f)).symm)

/-- Counit square.  Its endpoint maps are the endpoint idempotents, i.e. the
identity morphisms of the corresponding Karoubi objects. -/
def karoubiArrowCounitIsoApp (P : Arrow (Karoubi E)) :
    karoubiArrowToArrowKaroubi.obj (arrowKaroubiToKaroubiArrow.obj P) ≅ P :=
  Arrow.isoMk (Iso.refl P.left) (Iso.refl P.right) (by
    apply Karoubi.Hom.ext
    change P.left.p ≫ P.hom.f =
      (P.left.p ≫ P.hom.f ≫ P.right.p) ≫ P.right.p
    simp)

/-- The counit natural isomorphism of the comparison equivalence. -/
def karoubiArrowCounitIso :
    arrowKaroubiToKaroubiArrow ⋙ karoubiArrowToArrowKaroubi ≅
      𝟭 (Arrow (Karoubi E)) :=
  NatIso.ofComponents karoubiArrowCounitIsoApp (by
    intro P Q f
    apply Arrow.hom_ext
    · apply Karoubi.Hom.ext
      dsimp [karoubiArrowCounitIsoApp, karoubiArrowToArrowKaroubi,
        arrowKaroubiToKaroubiArrow, karoubiArrowLeftMap]
      change f.left.f ≫ Q.left.p = P.left.p ≫ f.left.f
      exact (Karoubi.p_comm f.left).symm
    · apply Karoubi.Hom.ext
      dsimp [karoubiArrowCounitIsoApp, karoubiArrowToArrowKaroubi,
        arrowKaroubiToKaroubiArrow, karoubiArrowRightMap]
      change f.right.f ≫ Q.right.p = P.right.p ≫ f.right.f
      exact (Karoubi.p_comm f.right).symm)

/-- G-119(A): taking arrows commutes with Karoubi completion. -/
def karoubiArrowEquivalence : Karoubi (Arrow E) ≌ Arrow (Karoubi E) where
  functor := karoubiArrowToArrowKaroubi
  inverse := arrowKaroubiToKaroubiArrow
  unitIso := karoubiArrowUnitIso
  counitIso := karoubiArrowCounitIso
  functor_unitIso_comp P := by
    apply Arrow.hom_ext
    · apply Karoubi.Hom.ext
      exact karoubiArrow_left_idem P
    · apply Karoubi.Hom.ext
      exact karoubiArrow_right_idem P

#assert_standard_axioms_only AAT.AG.RealizationComparisonIdempotents

end AAT.AG.RealizationComparisonIdempotents
