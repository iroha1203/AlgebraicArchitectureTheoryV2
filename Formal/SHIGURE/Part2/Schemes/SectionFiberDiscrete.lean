import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.FiberedCategory.Fiber

/-! # Fixing an object in the category of elements of its sections

## Implementation notes

The fixed-object category uses mathlib's `Functor.Fiber` of the actual
projection. Its comparison starts from the discrete category of
sections and regards a section as an object with the given projection.
A morphism in the fiber projects to the identity, which forces the
section values to agree.
-/

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

/-- A section in the categorical fiber is transported to the exact fixed object. -/
def elementsFiberSection (s : (CategoryOfElements.π P).Fiber X) : P.obj X :=
  P.map (eqToHom s.2) s.1.2

/-- A section of the exact fixed object is read without changing its value. -/
theorem elementsFiberSection_mk (s : P.obj X) :
    elementsFiberSection P X (Fiber.mk (a := P.elementsMk X s) (p := CategoryOfElements.π P) rfl) = s := by
  change P.map (eqToHom (rfl : X = X)) s = s
  rw [eqToHom_refl, FunctorToTypes.map_id_apply]

private theorem elementsFiberSection_hom {s t : (CategoryOfElements.π P).Fiber X} (m : s ⟶ t) :
    elementsFiberSection P X s = elementsFiberSection P X t := by
  rcases s with ⟨⟨Y, s⟩, hs⟩
  rcases t with ⟨⟨Z, t⟩, ht⟩
  change Y = X at hs
  change Z = X at ht
  subst Y
  subst Z
  let p := CategoryOfElements.π P
  let a := (Fiber.fiberInclusion (p := p) (S := X)).map m
  have above : p.map a = 𝟙 X := by
    simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using
      (IsHomLift.fac' p (𝟙 X) a)
  have e : P.map (p.map a) s = t := a.property
  rw [above] at e
  have same := (FunctorToTypes.map_id_apply P s).symm.trans e
  exact (elementsFiberSection_mk P X s).trans (same.trans (elementsFiberSection_mk P X t).symm)

/-- The equivalence reads the section carried by each actual object of the categorical fiber. -/
theorem elementsFiberEquivDiscrete_obj_as (s : (CategoryOfElements.π P).Fiber X) :
    ((elementsFiberEquivDiscrete P X).functor.obj s).as = elementsFiberSection P X s := by
  let E := elementsFiberEquivDiscrete P X
  let t := E.functor.obj s
  have h := elementsFiberSection_hom P X (E.unitIso.app s).hom
  change elementsFiberSection P X s =
    elementsFiberSection P X (Fiber.mk (a := P.elementsMk X t.as) (p := CategoryOfElements.π P) rfl) at h
  rw [elementsFiberSection_mk] at h
  exact h.symm

/-- Transport the fixed structure by an isomorphism, mapping the section by the
action of the original sections functor. -/
def elementsFiberTransport {Y : C} (e : X ≅ Y) :
    (CategoryOfElements.π P).Fiber X ⥤ (CategoryOfElements.π P).Fiber Y :=
  (elementsFiberEquivDiscrete P X).functor ⋙
    Discrete.functor (fun s => (⟨P.map e.hom s⟩ : Discrete (P.obj Y))) ⋙
    (elementsFiberEquivDiscrete P Y).inverse

/-- The transported object carries the image of its original section. -/
theorem elementsFiberTransport_section {Y : C} (e : X ≅ Y)
    (s : (CategoryOfElements.π P).Fiber X) :
    elementsFiberSection P Y ((elementsFiberTransport P X e).obj s) =
      P.map e.hom (elementsFiberSection P X s) := by
  rw [← elementsFiberEquivDiscrete_obj_as P X s]
  let value := P.map e.hom ((elementsFiberEquivDiscrete P X).functor.obj s).as
  change elementsFiberSection P Y
      (Fiber.mk (a := P.elementsMk Y value) (p := CategoryOfElements.π P) rfl) = value
  exact elementsFiberSection_mk P Y value

end

end SHIGURE.SchemeDescent
