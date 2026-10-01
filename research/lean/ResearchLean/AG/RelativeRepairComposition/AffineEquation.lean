import ResearchLean.AG.RelativeRepairComposition.LabeledAction
import Mathlib.CategoryTheory.Comma.Basic
import Mathlib.Tactic.Abel

/-!
# Affine equations and their complete label action.

G-130 B. These generic constructions are instantiated using the
original relative cochains and the actual defect. The solution type is indexed
by the differential pair so its native action uses the specified vertex
coboundary; the zero-composition premise is proved by the relative complex.
## Implementation notes

This is the full affine action category used in G-130 B. Its objects are all
solutions, indexed by the specified differential pair; its arrows retain every
zero-cochain label. An orbit quotient would discard stabilizers and overlap
isomorphisms, so it cannot serve as the native descent category.
-/

namespace AAT.AG.RelativeRepairComposition
open CategoryTheory

namespace Equation
universe u0 u1 u2
variable {A0 : Type u0} {A1 : Type u1} {A2 : Type u2}
variable [AddCommGroup A0] [AddCommGroup A1] [AddCommGroup A2]
variable (d0 : A0 →+ A1) (d1 : A1 →+ A2)
variable (hzero : ∀ b, d1 (d0 b) = 0) (rhs : A2)

/-- Every solution of the same affine differential equation. -/
def Solution (d0 : A0 →+ A1) (d1 : A1 →+ A2)
    (_hzero : ∀ b, d1 (d0 b) = 0) (rhs : A2) := {h : A1 // d1 h = rhs}

/-- The zero right-hand side always has its original zero-cochain solution. -/
theorem solution_zero_nonempty : Nonempty (Solution d0 d1 hzero 0) :=
  ⟨⟨0, map_zero d1⟩⟩

/-- A nonzero right-hand side with zero face differential has no affine solution. -/
theorem not_solution_zero_differential (rhs : A2) (hrhs : rhs ≠ 0) :
    ¬ Nonempty (Solution d0 (0 : A1 →+ A2) (fun _ => rfl) rhs) := by
  rintro ⟨h⟩
  exact hrhs h.2.symm

/-- The original zero-cochain label acts by its coboundary. -/
def gauge (b : A0) (h : Solution d0 d1 hzero rhs) : Solution d0 d1 hzero rhs :=
  ⟨h.1 + d0 b, by rw [map_add, h.2, hzero, add_zero]⟩

/-- Every label is retained in the affine action, including stabilizers. -/
instance addAction : AddAction A0 (Solution d0 d1 hzero rhs) where
  vadd := gauge d0 d1 hzero rhs
  zero_vadd h := Subtype.ext (by change h.1 + d0 0 = h.1; rw [map_zero, add_zero])
  add_vadd b c h := Subtype.ext (by
    change h.1 + d0 (b + c) = (h.1 + d0 c) + d0 b
    rw [map_add]; abel)

/-- The native action groupoid of the same affine solutions. -/
abbrev Groupoid := by
  letI := addAction d0 d1 hzero rhs
  exact ActionCategory (Multiplicative A0) (Solution d0 d1 hzero rhs)

/-- An affine gauge arrow is exactly the named coboundary equation. -/
theorem hom_condition {x y : Groupoid d0 d1 hzero rhs} (b : x ⟶ y) :
    y.back.1 = x.back.1 + d0 b.1.toAdd :=
  (congrArg Subtype.val b.2).symm

/-- Every named gauge-equation label gives an arrow of the native groupoid. -/
def homOfLabel {x y : Groupoid d0 d1 hzero rhs} (b : A0)
    (hb : y.back.1 = x.back.1 + d0 b) : x ⟶ y :=
  ⟨Multiplicative.ofAdd b, Subtype.ext hb.symm⟩

/-- The arrow construction keeps the entire original label. -/
theorem homOfLabel_label {x y : Groupoid d0 d1 hzero rhs} (b : A0)
    (hb : y.back.1 = x.back.1 + d0 b) :
    (homOfLabel d0 d1 hzero rhs b hb).1.toAdd = b := rfl

end Equation

universe uG uH uX uY
variable {G : Type uG} {H : Type uH} [Group G] [Group H]
variable {X : Type uX} {Y : Type uY} [MulAction G X] [MulAction H Y]

/-- An equivariant object map and label homomorphism give a native action functor. -/
def actionLabelFunctor (φ : G →* H) (e : X → Y)
    (he : ∀ g x, e (g • x) = φ g • e x) :
    ActionCategory G X ⥤ ActionCategory H Y where
  obj x := (e x.back : ActionCategory H Y)
  map {x _} f := ⟨φ f.1, (he f.1 x.back).symm.trans (congrArg e f.2)⟩
  map_id _ := Subtype.ext (map_one φ)
  map_comp f g := Subtype.ext (map_mul φ g.1 f.1)

/-- A change of coordinate labels maps every group element through the specified isomorphism. -/
def changedLabelFunctor (φ : G ≃* H) (e : X ≃ Y)
    (he : ∀ g x, e (g • x) = φ g • e x) :
    ActionCategory G X ⥤ ActionCategory H Y where
  obj x := (e x.back : ActionCategory H Y)
  map {x _} f := ⟨φ f.1, (he f.1 x.back).symm.trans (congrArg e f.2)⟩
  map_id _ := Subtype.ext (map_one φ)
  map_comp f g := Subtype.ext (map_mul φ g.1 f.1)

/-- Inverse equivariance follows from the specified object and label isomorphisms. -/
theorem changed_label_inverse_equivariant (φ : G ≃* H) (e : X ≃ Y)
    (he : ∀ g x, e (g • x) = φ g • e x) (h : H) (y : Y) :
    e.symm (h • y) = φ.symm h • e.symm y := by
  apply e.injective
  rw [e.apply_symm_apply, he, φ.apply_symm_apply, e.apply_symm_apply]

/-- The inverse restores every label through the inverse group isomorphism. -/
def changedLabelInverse (φ : G ≃* H) (e : X ≃ Y)
    (he : ∀ g x, e (g • x) = φ g • e x) :
    ActionCategory H Y ⥤ ActionCategory G X :=
  changedLabelFunctor φ.symm e.symm (changed_label_inverse_equivariant φ e he)

/-- Every mapped arrow has the specified full coordinate label. -/
theorem changed_label_functor_label (φ : G ≃* H) (e : X ≃ Y)
    (he : ∀ g x, e (g • x) = φ g • e x)
    {x y : ActionCategory G X} (f : x ⟶ y) :
    ((changedLabelFunctor φ e he).map f).1 = φ f.1 := rfl

/-- The inverse composite restores each independent object. -/
theorem changed_label_left_obj (φ : G ≃* H) (e : X ≃ Y)
    (he : ∀ g x, e (g • x) = φ g • e x) (x : ActionCategory G X) :
    (changedLabelInverse φ e he).obj ((changedLabelFunctor φ e he).obj x) = x := by
  exact (congrArg (fun x : X => (x : ActionCategory G X))
    (e.symm_apply_apply x.back)).trans (ActionCategory.back_coe x)

/-- The forward composite restores each independent coordinate object. -/
theorem changed_label_right_obj (φ : G ≃* H) (e : X ≃ Y)
    (he : ∀ g x, e (g • x) = φ g • e x) (y : ActionCategory H Y) :
    (changedLabelFunctor φ e he).obj ((changedLabelInverse φ e he).obj y) = y := by
  exact (congrArg (fun y : Y => (y : ActionCategory H Y))
    (e.apply_symm_apply y.back)).trans (ActionCategory.back_coe y)

/-- The unit is identity-labeled transport, with every old label restored. -/
def changedLabelUnit (φ : G ≃* H) (e : X ≃ Y)
    (he : ∀ g x, e (g • x) = φ g • e x) :
    𝟭 (ActionCategory G X) ≅ changedLabelFunctor φ e he ⋙ changedLabelInverse φ e he :=
  NatIso.ofComponents (fun x => eqToIso (changed_label_left_obj φ e he x).symm) (by
    intro x y f
    apply Subtype.ext
    change (eqToHom (changed_label_left_obj φ e he y).symm).1 * f.1 =
      φ.symm (φ f.1) * (eqToHom (changed_label_left_obj φ e he x).symm).1
    rw [action_eqToHom_label, action_eqToHom_label, φ.symm_apply_apply, one_mul, mul_one])

/-- The counit is identity-labeled transport, with every new label restored. -/
def changedLabelCounit (φ : G ≃* H) (e : X ≃ Y)
    (he : ∀ g x, e (g • x) = φ g • e x) :
    changedLabelInverse φ e he ⋙ changedLabelFunctor φ e he ≅ 𝟭 (ActionCategory H Y) :=
  NatIso.ofComponents (fun y => eqToIso (changed_label_right_obj φ e he y)) (by
    intro x y f
    apply Subtype.ext
    change (eqToHom (changed_label_right_obj φ e he y)).1 * φ (φ.symm f.1) =
      f.1 * (eqToHom (changed_label_right_obj φ e he x)).1
    rw [action_eqToHom_label, action_eqToHom_label, φ.apply_symm_apply, one_mul, mul_one])

/-- Equivariant object and label coordinates yield a native groupoid equivalence. -/
def changedLabelEquivalence (φ : G ≃* H) (e : X ≃ Y)
    (he : ∀ g x, e (g • x) = φ g • e x) :
    ActionCategory G X ≌ ActionCategory H Y where
  functor := changedLabelFunctor φ e he
  inverse := changedLabelInverse φ e he
  unitIso := changedLabelUnit φ e he
  counitIso := changedLabelCounit φ e he
  functor_unitIso_comp x := by
    apply Subtype.ext
    change (eqToHom (changed_label_right_obj φ e he ((changedLabelFunctor φ e he).obj x))).1 *
      φ ((eqToHom (changed_label_left_obj φ e he x).symm).1) = (1 : H)
    rw [action_eqToHom_label, action_eqToHom_label, map_one, one_mul]

/-- The coordinate-change unit has identity label on every original object. -/
theorem changed_label_unit_label (φ : G ≃* H) (e : X ≃ Y)
    (he : ∀ g x, e (g • x) = φ g • e x) (x : ActionCategory G X) :
    ((changedLabelEquivalence φ e he).unitIso.hom.app x).1 = 1 :=
  action_eqToHom_label (changed_label_left_obj φ e he x).symm

/-- The inverse unit has the same identity label. -/
theorem changed_label_unit_inv_label (φ : G ≃* H) (e : X ≃ Y)
    (he : ∀ g x, e (g • x) = φ g • e x) (x : ActionCategory G X) :
    ((changedLabelEquivalence φ e he).unitIso.inv.app x).1 = 1 :=
  action_eqToHom_label (changed_label_left_obj φ e he x)

/-- The coordinate-change counit has identity label on every coordinate object. -/
theorem changed_label_counit_label (φ : G ≃* H) (e : X ≃ Y)
    (he : ∀ g x, e (g • x) = φ g • e x) (y : ActionCategory H Y) :
    ((changedLabelEquivalence φ e he).counitIso.hom.app y).1 = 1 :=
  action_eqToHom_label (changed_label_right_obj φ e he y)

/-- The inverse counit has the same identity label. -/
theorem changed_label_counit_inv_label (φ : G ≃* H) (e : X ≃ Y)
    (he : ∀ g x, e (g • x) = φ g • e x) (y : ActionCategory H Y) :
    ((changedLabelEquivalence φ e he).counitIso.inv.app y).1 = 1 :=
  action_eqToHom_label (changed_label_right_obj φ e he y).symm

end AAT.AG.RelativeRepairComposition

#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
