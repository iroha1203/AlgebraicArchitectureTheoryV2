import Mathlib.CategoryTheory.Action
import Formal.Util.AssertStandardAxioms

/-!
# Equivariant coordinates retain every action label

API for G-130 A and C: an equivariant bijection of objects induces a native
action-groupoid equivalence whose maps keep the original group element.
The repair layer supplies this bijection and proves equivariance from d0.
-/

namespace AAT.AG.RelativeRepairComposition

open CategoryTheory

universe uG uX uY

variable {G : Type uG} [Group G] {X : Type uX} {Y : Type uY}
variable [MulAction G X] [MulAction G Y]

/-- Equal-object transport in a native action category has identity label. -/
theorem action_eqToHom_label {x y : ActionCategory G X} (h : x = y) :
    (eqToHom h).1 = 1 := by cases h; rfl

/-- An equivariant map of objects keeps each original scalar as its morphism. -/
def labeledActionFunctor (e : X ≃ Y) (he : ∀ (g : G) (x : X), e (g • x) = g • e x) :
    ActionCategory G X ⥤ ActionCategory G Y where
  obj x := (e x.back : ActionCategory G Y)
  map {x _} f := ⟨f.1, (he f.1 x.back).symm.trans (congrArg e f.2)⟩
  map_id _ := Subtype.ext rfl
  map_comp _ _ := Subtype.ext rfl

/-- Equivariance of the inverse follows from injectivity of the original coordinates. -/
theorem inverse_equivariant (e : X ≃ Y) (he : ∀ (g : G) (x : X), e (g • x) = g • e x)
    (g : G) (y : Y) : e.symm (g • y) = g • e.symm y := by
  apply e.injective
  rw [e.apply_symm_apply, he, e.apply_symm_apply]

/-- Inverse labeled functor, generated from the same object equivalence. -/
def labeledActionInverse (e : X ≃ Y) (he : ∀ (g : G) (x : X), e (g • x) = g • e x) :
    ActionCategory G Y ⥤ ActionCategory G X :=
  labeledActionFunctor e.symm (inverse_equivariant e he)

/-- The labeled functor preserves every scalar. -/
theorem labeledActionFunctor_label (e : X ≃ Y) (he : ∀ (g : G) (x : X), e (g • x) = g • e x)
    {x y : ActionCategory G X} (f : x ⟶ y) :
    ((labeledActionFunctor e he).map f).1 = f.1 := rfl

/-- The inverse labeled functor preserves every scalar. -/
theorem labeledActionInverse_label (e : X ≃ Y) (he : ∀ (g : G) (x : X), e (g • x) = g • e x)
    {x y : ActionCategory G Y} (f : x ⟶ y) :
    ((labeledActionInverse e he).map f).1 = f.1 := rfl

/-- The inverse composite restores the original object. -/
theorem labeledAction_left_obj (e : X ≃ Y) (he : ∀ (g : G) (x : X), e (g • x) = g • e x)
    (x : ActionCategory G X) :
    (labeledActionInverse e he).obj ((labeledActionFunctor e he).obj x) = x := by
  exact (congrArg (fun x : X => (x : ActionCategory G X))
    (e.symm_apply_apply x.back)).trans (ActionCategory.back_coe x)

/-- The forward composite restores the original coordinate object. -/
theorem labeledAction_right_obj (e : X ≃ Y) (he : ∀ (g : G) (x : X), e (g • x) = g • e x)
    (y : ActionCategory G Y) :
    (labeledActionFunctor e he).obj ((labeledActionInverse e he).obj y) = y := by
  exact (congrArg (fun y : Y => (y : ActionCategory G Y))
    (e.apply_symm_apply y.back)).trans (ActionCategory.back_coe y)

/-- The unit is identity-labeled transport of the restored object. -/
def labeledActionUnit (e : X ≃ Y) (he : ∀ (g : G) (x : X), e (g • x) = g • e x) :
    𝟭 (ActionCategory G X) ≅ labeledActionFunctor e he ⋙ labeledActionInverse e he :=
  NatIso.ofComponents (fun x => eqToIso (labeledAction_left_obj e he x).symm) (by
    intro x y f
    apply Subtype.ext
    change (eqToHom (labeledAction_left_obj e he y).symm).1 * f.1 =
      f.1 * (eqToHom (labeledAction_left_obj e he x).symm).1
    rw [action_eqToHom_label, action_eqToHom_label, one_mul, mul_one])

/-- The counit is identity-labeled transport of the restored coordinate object. -/
def labeledActionCounit (e : X ≃ Y) (he : ∀ (g : G) (x : X), e (g • x) = g • e x) :
    labeledActionInverse e he ⋙ labeledActionFunctor e he ≅ 𝟭 (ActionCategory G Y) :=
  NatIso.ofComponents (fun y => eqToIso (labeledAction_right_obj e he y)) (by
    intro x y f
    apply Subtype.ext
    change (eqToHom (labeledAction_right_obj e he y)).1 * f.1 =
      f.1 * (eqToHom (labeledAction_right_obj e he x)).1
    rw [action_eqToHom_label, action_eqToHom_label, one_mul, mul_one])

/-- Equivariant coordinates give a native groupoid equivalence with the same labels. -/
def labeledActionEquivalence (e : X ≃ Y) (he : ∀ (g : G) (x : X), e (g • x) = g • e x) :
    ActionCategory G X ≌ ActionCategory G Y where
  functor := labeledActionFunctor e he
  inverse := labeledActionInverse e he
  unitIso := labeledActionUnit e he
  counitIso := labeledActionCounit e he
  functor_unitIso_comp x := by
    apply Subtype.ext
    change (eqToHom (labeledAction_right_obj e he ((labeledActionFunctor e he).obj x))).1 *
      (eqToHom (labeledAction_left_obj e he x).symm).1 = (1 : G)
    rw [action_eqToHom_label, action_eqToHom_label, one_mul]

end AAT.AG.RelativeRepairComposition

#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
