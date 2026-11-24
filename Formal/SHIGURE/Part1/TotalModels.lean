import Formal.SHIGURE.Part1.ModelSemantics
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
import Mathlib.CategoryTheory.Core
import Mathlib.CategoryTheory.FiberedCategory.Grothendieck

/-! # The total category of theories and models

## Implementation notes

Construction 2.5 uses mathlib's contravariant Grothendieck construction on
the model semantics functor. The strict equalities of pullback functors
give the object transports in equations (2.6)–(2.7). Constructing a
category of pairs directly would reconstruct the same composition and
coherence proofs. Here those laws are inherited from the mathlib
construction, with the state components identified explicitly.
-/

universe u

namespace SHIGURE

open CategoryTheory

/-- Construction 2.5: a theory with a model, with the mathlib total-category instance. -/
noncomputable abbrev TotalModel :=
  Pseudofunctor.CoGrothendieck (Theory.modelSemantics.{u}).toPseudoFunctor'

namespace TotalModel

/-- The object in the total category specified by the theory and its model. -/
noncomputable def ofModel (T : Theory.{u}) (A : Model T) : TotalModel.{u} :=
  ⟨T, A⟩

variable {A B C : TotalModel.{u}}

/-- Equation (2.6): a theory arrow together with a model arrow to the corresponding pullback. -/
noncomputable def homMk (theory : A.base ⟶ B.base) (state : A.fiber ⟶ (Theory.modelPullback theory).obj B.fiber) :
    A ⟶ B :=
  ⟨theory, state⟩

/-- The base arrow of a total morphism is its theory component. -/
noncomputable def theory (f : A ⟶ B) : A.base ⟶ B.base := f.base

/-- The state arrow of a total morphism lies in the semantic category of the domain theory. -/
noncomputable def state (f : A ⟶ B) : A.fiber ⟶ (Theory.modelPullback (theory f)).obj B.fiber := f.fiber

/-- The pair in equation (2.6) has the specified theory component. -/
@[simp] theorem theory_homMk (f : A.base ⟶ B.base)
    (h : A.fiber ⟶ (Theory.modelPullback f).obj B.fiber) : theory (homMk f h) = f :=
  rfl

/-- The pair in equation (2.6) has the specified state component. -/
@[simp] theorem state_homMk (f : A.base ⟶ B.base)
    (h : A.fiber ⟶ (Theory.modelPullback f).obj B.fiber) : state (homMk f h) = h :=
  rfl

/-- The theory component of the identity is the identity of the theory. -/
@[simp] theorem theory_id (A : TotalModel.{u}) : theory (𝟙 A) = 𝟙 A.base := rfl

/-- The state identity is the model identity transported to the pullback of the theory identity. -/
theorem state_id (A : TotalModel.{u}) :
    state (𝟙 A) = eqToHom
      ((congrArg (fun F : Model A.base ⥤ Model A.base => F.obj A.fiber)
        (Theory.modelPullback_id A.base)).symm) := by
  change (𝟙 A : A ⟶ A).fiber = _
  rw [Pseudofunctor.CoGrothendieck.categoryStruct_id_fiber]
  simp only [Functor.toPseudoFunctor'_mapId, eqToIso.inv, Cat.eqToHom_app]

/-- The theory component of equation (2.7) is composition in the theory category. -/
@[simp] theorem theory_comp (f : A ⟶ B) (g : B ⟶ C) : theory (f ≫ g) = theory f ≫ theory g :=
  rfl

/-- Equation (2.7): compose the first state arrow with the second one pulled back along the first
theory arrow. The final transport is along the strict pullback comparison. -/
theorem state_comp (f : A ⟶ B) (g : B ⟶ C) :
    state (f ≫ g) = state f ≫ (Theory.modelPullback (theory f)).map (state g) ≫
      eqToHom ((congrArg (fun F : Model C.base ⥤ Model A.base => F.obj C.fiber)
        (Theory.modelPullback_comp (theory f) (theory g))).symm) := by
  change (f ≫ g).fiber = _
  rw [Pseudofunctor.CoGrothendieck.categoryStruct_comp_fiber]
  simp only [Functor.toPseudoFunctor'_mapComp, eqToIso.inv, Cat.eqToHom_app]
  rfl

/-- The projection of Construction 2.5 forgets the model and its state arrow. -/
noncomputable def projection : TotalModel.{u} ⥤ Theory.{u} :=
  Pseudofunctor.CoGrothendieck.forget (Theory.modelSemantics.{u}).toPseudoFunctor'

/-- The projection on an object is its theory. -/
@[simp] theorem projection_obj (A : TotalModel.{u}) : projection.obj A = A.base :=
  rfl

/-- The projection on a morphism is its theory arrow. -/
@[simp] theorem projection_map (f : A ⟶ B) : projection.map f = theory f :=
  rfl

/-- The canonical family of fibers supplied by the Grothendieck construction. -/
noncomputable instance hasFibers : HasFibers (projection.{u}) :=
  inferInstanceAs (HasFibers
    (Pseudofunctor.CoGrothendieck.forget (Theory.modelSemantics.{u}).toPseudoFunctor'))

/-- The chosen fiber over a theory is its semantic category on the same type of models. -/
theorem chosenFiber_eq (T : Theory.{u}) : HasFibers.Fib projection T = Model T :=
  rfl

/-- The chosen fiber has the same category structure as the semantic category. -/
theorem chosenFiber_category (T : Theory.{u}) :
    HEq (HasFibers.category (p := projection.{u}) T) (inferInstance : Category.{u} (Model T)) :=
  HEq.rfl

/-- Equation (2.7) restricts to the ordinary semantic category in the standard mathlib fiber. -/
noncomputable def fiberEquivalence (T : Theory.{u}) :
    Model T ≌ Functor.Fiber projection T :=
  (HasFibers.inducedFunctor projection T).asEquivalence

end TotalModel

namespace Model

/-- The groupoid in Construction 2.5 keeps the model objects and their invertible arrows. -/
abbrev core (T : Theory.{u}) := CategoryTheory.Core (Model T)

/-- Inclusion of the invertible semantic arrows in the whole semantic category. -/
def coreInclusion (T : Theory.{u}) : core T ⥤ Model T :=
  CategoryTheory.Core.inclusion _

end Model

end SHIGURE
