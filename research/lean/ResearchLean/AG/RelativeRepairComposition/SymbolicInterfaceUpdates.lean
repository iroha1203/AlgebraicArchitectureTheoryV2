import ResearchLean.AG.RelativeRepairComposition.SymbolicInterfaceAction

/-!
# Parameter updates reuse the same section and full-label increments

## Implementation notes

Changing the primitive value changes only the affine right-hand side and its
section term. The same full public map, private kernel, generated section and
original-label increments remain in use. These formulas compare expressions
and valid coordinates; they do not manufacture a repair in an empty fibre.
-/
namespace AAT.AG.RelativeRepairComposition.SymbolicInterface
open LinearInterface
universe uk ux uz uv up ub
variable {k : Type uk} [Field k]
variable {X : Type ux} {Z : Type uz} {V : Type uv} {P : Type up} {G : Type ub}
variable [AddCommGroup X] [Module k X] [AddCommGroup Z] [Module k Z]
variable [AddCommGroup V] [Module k V] [AddCommGroup P] [Module k P]
variable [AddCommGroup G] [Module k G]
variable (D : X →ₗ[k] V) (F : Z →ₗ[k] V) (σ : V →ₗ[k] X)
variable (B : P →ₗ[k] V) (r : V)

/-- Updating the value updates the right-hand side by precisely the generated primitive linear term. -/
theorem rhs_difference (v w : P) : rhs B r w - rhs B r v = B (w - v) := by
  simp only [rhs, map_sub]
  abel

/-- Reusing the same section changes only its generated affine term at every original public value. -/
theorem section_update (v w : P) (z : Z) :
    σ (rhs B r w - F z) - σ (rhs B r v - F z) = σ (B (w - v)) := by
  rw [← map_sub]
  congr 1
  rw [map_sub]
  unfold rhs
  abel

/-- The same entire private-kernel vector contributes unchanged to reconstruction under each value update. -/
theorem reconstruction_update (v w : P) (z : Z) (h : LinearMap.ker D) :
    (σ (rhs B r w - F z) + h.1) - (σ (rhs B r v - F z) + h.1) = σ (B (w - v)) := by
  have hs := section_update F σ B r v w z
  calc
    _ = σ (rhs B r w - F z) - σ (rhs B r v - F z) := by abel
    _ = _ := hs

variable (hσ : ∀ x, D (σ (D x)) = D x)
variable (a : G →ₗ[k] X) (c : G →ₗ[k] Z) (hzero : ∀ g, D (a g) + F (c g) = 0)

/-- Every full original label has the identical public increment at every value and right-hand side. -/
theorem gauge_public_increment (v : P) (g : G)
    (y : FiberObjects D F σ B r hσ a c hzero v) :
    (fiberGauge D F σ hσ B r a c hzero v g y).1.1 - y.1.1 = c g :=
  add_sub_cancel_left _ _

/-- Every full original label has the identical whole private-kernel increment at every value and right-hand side. -/
theorem gauge_kernel_increment (v : P) (g : G)
    (y : FiberObjects D F σ B r hσ a c hzero v) :
    (fiberGauge D F σ hσ B r a c hzero v g y).2 - y.2 = gamma D σ hσ a g :=
  add_sub_cancel_left _ _

end AAT.AG.RelativeRepairComposition.SymbolicInterface
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
