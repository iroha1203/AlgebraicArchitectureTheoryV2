import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.CategoryTheory.Idempotents.Karoubi
import Formal.Util.AssertStandardAxioms

/-!
# Karoubi completion and arrow categories

This file constructs the equivalence portion of clause A of G-119: the equivalence between idempotent
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

/-- Evaluation API: the forward functor retains the source endpoint map. -/
@[simp]
theorem karoubiArrowToArrowKaroubi_map_left_f
    {P Q : Karoubi (Arrow E)} (f : P ⟶ Q) :
    (karoubiArrowToArrowKaroubi.map f).left.f = f.f.left :=
  rfl

/-- Evaluation API: the forward functor retains the target endpoint map. -/
@[simp]
theorem karoubiArrowToArrowKaroubi_map_right_f
    {P Q : Karoubi (Arrow E)} (f : P ⟶ Q) :
    (karoubiArrowToArrowKaroubi.map f).right.f = f.f.right :=
  rfl

/-- A comparison in `Karoubi E` determines its raw arrow and endpoint idempotent square. -/
def arrowKaroubiToKaroubiArrowObj (P : Arrow (Karoubi E)) : Karoubi (Arrow E) where
  X := { left := P.left.X, right := P.right.X, hom := P.hom.f }
  p := Arrow.homMk P.left.p P.right.p (Karoubi.p_comm P.hom)
  idem := by
    apply Arrow.hom_ext
    · exact P.left.idem
    · exact P.right.idem

/-- Evaluation API for the raw comparison recovered by the inverse object map. -/
@[simp]
theorem arrowKaroubiToKaroubiArrowObj_X_hom (P : Arrow (Karoubi E)) :
    (arrowKaroubiToKaroubiArrowObj P).X.hom = P.hom.f :=
  rfl

/-- Evaluation API for the source idempotent recovered by the inverse object map. -/
@[simp]
theorem arrowKaroubiToKaroubiArrowObj_p_left (P : Arrow (Karoubi E)) :
    (arrowKaroubiToKaroubiArrowObj P).p.left = P.left.p :=
  rfl

/-- Evaluation API for the target idempotent recovered by the inverse object map. -/
@[simp]
theorem arrowKaroubiToKaroubiArrowObj_p_right (P : Arrow (Karoubi E)) :
    (arrowKaroubiToKaroubiArrowObj P).p.right = P.right.p :=
  rfl

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

/-- Evaluation API: the inverse functor recovers the raw source endpoint map. -/
@[simp]
theorem arrowKaroubiToKaroubiArrow_map_f_left
    {P Q : Arrow (Karoubi E)} (f : P ⟶ Q) :
    (arrowKaroubiToKaroubiArrow.map f).f.left = f.left.f :=
  rfl

/-- Evaluation API: the inverse functor recovers the raw target endpoint map. -/
@[simp]
theorem arrowKaroubiToKaroubiArrow_map_f_right
    {P Q : Arrow (Karoubi E)} (f : P ⟶ Q) :
    (arrowKaroubiToKaroubiArrow.map f).f.right = f.right.f :=
  rfl

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

/-- Evaluation API for the source endpoint of the unit hom. -/
@[simp]
theorem karoubiArrowUnitIsoApp_hom_f_left (P : Karoubi (Arrow E)) :
    (karoubiArrowUnitIsoApp P).hom.f.left = P.p.left :=
  rfl

/-- Evaluation API for the target endpoint of the unit hom. -/
@[simp]
theorem karoubiArrowUnitIsoApp_hom_f_right (P : Karoubi (Arrow E)) :
    (karoubiArrowUnitIsoApp P).hom.f.right = P.p.right :=
  rfl

/-- Evaluation API for the source endpoint of the unit inverse. -/
@[simp]
theorem karoubiArrowUnitIsoApp_inv_f_left (P : Karoubi (Arrow E)) :
    (karoubiArrowUnitIsoApp P).inv.f.left = P.p.left :=
  rfl

/-- Evaluation API for the target endpoint of the unit inverse. -/
@[simp]
theorem karoubiArrowUnitIsoApp_inv_f_right (P : Karoubi (Arrow E)) :
    (karoubiArrowUnitIsoApp P).inv.f.right = P.p.right :=
  rfl

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

/-- Evaluation API for the source endpoint of the counit hom. -/
@[simp]
theorem karoubiArrowCounitIsoApp_hom_left_f (P : Arrow (Karoubi E)) :
    (karoubiArrowCounitIsoApp P).hom.left.f = P.left.p :=
  rfl

/-- Evaluation API for the target endpoint of the counit hom. -/
@[simp]
theorem karoubiArrowCounitIsoApp_hom_right_f (P : Arrow (Karoubi E)) :
    (karoubiArrowCounitIsoApp P).hom.right.f = P.right.p :=
  rfl

/-- Evaluation API for the source endpoint of the counit inverse. -/
@[simp]
theorem karoubiArrowCounitIsoApp_inv_left_f (P : Arrow (Karoubi E)) :
    (karoubiArrowCounitIsoApp P).inv.left.f = P.left.p :=
  rfl

/-- Evaluation API for the target endpoint of the counit inverse. -/
@[simp]
theorem karoubiArrowCounitIsoApp_inv_right_f (P : Arrow (Karoubi E)) :
    (karoubiArrowCounitIsoApp P).inv.right.f = P.right.p :=
  rfl

/-- The counit natural isomorphism of the comparison equivalence. -/
def karoubiArrowCounitIso :
    arrowKaroubiToKaroubiArrow ⋙ karoubiArrowToArrowKaroubi ≅
      𝟭 (Arrow (Karoubi E)) :=
  NatIso.ofComponents karoubiArrowCounitIsoApp (by
    intro P Q f
    apply Arrow.hom_ext
    · apply Karoubi.Hom.ext
      change
        (karoubiArrowToArrowKaroubi.map
              (arrowKaroubiToKaroubiArrow.map f)).left.f ≫
            (karoubiArrowCounitIsoApp Q).hom.left.f =
          (karoubiArrowCounitIsoApp P).hom.left.f ≫ f.left.f
      rw [karoubiArrowToArrowKaroubi_map_left_f,
        arrowKaroubiToKaroubiArrow_map_f_left,
        karoubiArrowCounitIsoApp_hom_left_f,
        karoubiArrowCounitIsoApp_hom_left_f]
      exact (Karoubi.p_comm f.left).symm
    · apply Karoubi.Hom.ext
      change
        (karoubiArrowToArrowKaroubi.map
              (arrowKaroubiToKaroubiArrow.map f)).right.f ≫
            (karoubiArrowCounitIsoApp Q).hom.right.f =
          (karoubiArrowCounitIsoApp P).hom.right.f ≫ f.right.f
      rw [karoubiArrowToArrowKaroubi_map_right_f,
        arrowKaroubiToKaroubiArrow_map_f_right,
        karoubiArrowCounitIsoApp_hom_right_f,
        karoubiArrowCounitIsoApp_hom_right_f]
      exact (Karoubi.p_comm f.right).symm)

/-- G-119(A1): taking arrows commutes with Karoubi completion. -/
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
