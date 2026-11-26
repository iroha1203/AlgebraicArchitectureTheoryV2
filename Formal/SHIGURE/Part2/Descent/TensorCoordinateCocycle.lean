import Formal.SHIGURE.Part2.Descent.ScalarCocycle

/-! # Recovering the tensor cocycle from its coordinate comparisons -/

namespace SHIGURE.CoefficientDescent

open CategoryTheory TensorProduct

noncomputable section

universe u

variable {A B M : Type u} [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]

/-- On a generator of the first-position extension, the first-to-last
comparison inserts the unchanged unit in the middle coefficient position. -/
theorem move02_unit (θ : OverlapIso A B M) (x : M) :
    move02 θ ((x ⊗ₜ[A] (1 : B)) ⊗ₜ[A] (1 : B)) =
      ((TensorProduct.mk A B M (1 : B)).lTensor B) (θ (x ⊗ₜ[A] (1 : B))) := by
  change (TensorProduct.comm A M B).toLinearMap.lTensor B
    ((TensorProduct.assoc A B M B) (θ (x ⊗ₜ[A] (1 : B)) ⊗ₜ[A] (1 : B))) = _
  generalize θ (x ⊗ₜ[A] (1 : B)) = y
  induction y using TensorProduct.induction_on with
  | zero => simp only [zero_tmul, map_zero]
  | add y z hy hz => simp only [add_tmul, map_add, hy, hz]
  | tmul y z => rfl

variable {T : Type u} [CommRing T]

/-- Evaluating a scalar-extension cocycle on its generators proves the
ordered tensor cocycle once the three pullbacks have the specified formulas. -/
theorem coefficientCocycle_of_coordinate_composition
    (θ : OverlapIso A B M) {X Y Z : ModuleCat.{u} T}
    (p : X ⟶ Y) (q : Y ⟶ Z) (r : X ⟶ Z)
    (u : M → X) (v : Y → (B ⊗[A] M) ⊗[A] B) (w : Z → B ⊗[A] (B ⊗[A] M))
    (cocycle : p ≫ q = r)
    (first : ∀ x : M, v (p (u x)) = move01 θ ((x ⊗ₜ[A] (1 : B)) ⊗ₜ[A] (1 : B)))
    (second : ∀ y : Y, w (q y) = move12 θ (v y))
    (direct : ∀ x : M, w (r (u x)) = move02 θ ((x ⊗ₜ[A] (1 : B)) ⊗ₜ[A] (1 : B))) :
    (move12 θ).comp (move01 θ) = move02 θ := by
  apply coefficientCocycle_of_unit_tensors θ
  intro x
  rw [← first x, ← second (p (u x)), ← direct x]
  exact congrArg (fun k : X ⟶ Z => w (k (u x))) cocycle

end

end SHIGURE.CoefficientDescent
