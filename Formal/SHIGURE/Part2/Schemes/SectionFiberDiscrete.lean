import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.FiberedCategory.Fiber

/-! # Fixing an object in the category of elements of its sections -/

namespace SHIGURE.SchemeDescent

open CategoryTheory CategoryTheory.Functor CategoryTheory.IsHomLift

noncomputable section

universe u v w

variable {C : Type u} [Category.{v} C] (P : C ⥤ Type w) (X : C)

/-- Regard a section at the fixed object as an object of the category of elements. -/
private def fixedObjectSections : Discrete (P.obj X) ⥤ P.Elements :=
  Discrete.functor fun s => P.elementsMk X s

private theorem fixedObjectSections_comp :
    fixedObjectSections P X ⋙ CategoryOfElements.π P = (Functor.const (Discrete (P.obj X))).obj X := by
  let A := fixedObjectSections P X ⋙ CategoryOfElements.π P
  let B := (Functor.const (Discrete (P.obj X))).obj X
  let e : A ≅ B := NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro s t f
    obtain rfl := Discrete.ext (Discrete.eq_of_hom f)
    have h : f = 𝟙 s := Subsingleton.elim _ _
    subst f
    simp)
  exact Functor.ext_of_iso e (fun _ => rfl)

/-- Lift each section into the categorical fiber of the projection. -/
private def discreteToElementsFiber :
    Discrete (P.obj X) ⥤ (CategoryOfElements.π P).Fiber X :=
  Fiber.inducedFunctor (fixedObjectSections_comp P X)

/-- A fixed object has a discrete fiber of sections. Its morphisms lie over
the identity of that object in the original category. -/
def elementsFiberEquivDiscrete : (CategoryOfElements.π P).Fiber X ≌ Discrete (P.obj X) := by
  let T := discreteToElementsFiber P X
  haveI : T.Full := by
    constructor
    intro s t f
    let I : (CategoryOfElements.π P).Fiber X ⥤ P.Elements := Fiber.fiberInclusion
    let m := I.map f
    have hm : (CategoryOfElements.π P).map m = 𝟙 X := by
      simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using
        (IsHomLift.fac' (CategoryOfElements.π P) (𝟙 X) m)
    have h : s.as = t.as := by
      have e : P.map ((CategoryOfElements.π P).map m) s.as = t.as := m.property
      rw [hm] at e
      exact (FunctorToTypes.map_id_apply P s.as).symm.trans e
    obtain rfl := Discrete.ext h
    refine ⟨𝟙 s, ?_⟩
    apply Fiber.hom_ext
    apply (CategoryOfElements.π P).map_injective
    change (CategoryOfElements.π P).map (I.map (T.map (𝟙 s))) = (CategoryOfElements.π P).map m
    rw [T.map_id, I.map_id, (CategoryOfElements.π P).map_id]
    exact hm.symm
  haveI : T.Faithful := { map_injective := fun _ => Subsingleton.elim _ _ }
  haveI : T.EssSurj := by
    constructor
    rintro ⟨⟨Y, s⟩, h⟩
    change Y = X at h
    subst Y
    exact ⟨⟨s⟩, ⟨Iso.refl _⟩⟩
  haveI : T.IsEquivalence := { }
  exact T.asEquivalence.symm

end

end SHIGURE.SchemeDescent
