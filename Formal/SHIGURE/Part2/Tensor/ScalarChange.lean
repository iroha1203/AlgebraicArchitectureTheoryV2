import Formal.SHIGURE.Part1.CoefficientReading
import Formal.SHIGURE.Part2.AffineBaseChange
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Scalar extension of tensor realizations

Construction 4.8 changes the coefficient ring by tensoring an arbitrary
module with the new coefficients. The unit and tower comparisons compute
on pure tensors. Partial operations extend to the image of a specified
universally injective domain inclusion.

## Implementation notes

The coefficients are on the left of the module tensor, as in mathlib's
`LinearMap.baseChange`. The symmetry of the underlying tensor product
identifies this presentation with the right coefficient factor.
-/

open TensorProduct
open scoped TensorProduct

universe u

noncomputable section

namespace SHIGURE.TensorRealization

variable {k : Type u} [CommRing k]
variable {M N : Type u} [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]

/-- Changing from the base ring to itself has the usual unit comparison. -/
def scalarUnit : k ⊗[k] M ≃ₗ[k] M :=
  TensorProduct.lid k M

/-- The unit of scalar extension acts by multiplication on a pure tensor. -/
@[simp]
theorem scalarUnit_tmul (a : k) (m : M) : scalarUnit (a ⊗ₜ[k] m) = a • m :=
  rfl

/-- The unit comparison respects any linear map between the original modules. -/
theorem scalarUnit_natural (f : M →ₗ[k] N) :
    scalarUnit.toLinearMap.comp (f.baseChange k) = f.comp scalarUnit.toLinearMap := by
  apply AlgebraTensorModule.ext
  intro a m
  simp

/-- The native scalar sort extends to the new coefficient ring itself. -/
def extendScalarSort (R : Type u) [CommRing R] [Algebra k R] :
    R ⊗[k] k ≃ₗ[R] R :=
  AlgebraTensorModule.rid k R R

/-- The scalar sort comparison applies the coefficient map on pure tensors. -/
@[simp]
theorem extendScalarSort_tmul {R : Type u} [CommRing R] [Algebra k R] (r : R) (a : k) :
    extendScalarSort R (r ⊗ₜ[k] a) = a • r :=
  rfl

/-- Two coefficient ring maps and their composite make the required scalar tower. -/
theorem ringHom_scalarTower {A B C : CoefficientRing.{u}} (f : A.Hom B) (g : B.Hom C) :
    letI := A.ring
    letI := B.ring
    letI := C.ring
    letI := f.toAlgebra
    letI := g.toAlgebra
    letI := (g.comp f).toAlgebra
    IsScalarTower A.Carrier B.Carrier C.Carrier := by
  letI := A.ring
  letI := B.ring
  letI := C.ring
  letI := f.toAlgebra
  letI := g.toAlgebra
  letI := (g.comp f).toAlgebra
  exact IsScalarTower.of_algebraMap_eq' rfl

section Tower

variable {R S : Type u} [CommRing R] [CommRing S]
variable [Algebra k R] [Algebra k S] [Algebra R S] [IsScalarTower k R S]

/-- Consecutive scalar extensions identify with scalar extension along the composite. -/
def scalarTower : S ⊗[R] (R ⊗[k] M) ≃ₗ[S] S ⊗[k] M :=
  AlgebraTensorModule.cancelBaseChange k R S S M

/-- Simplify the tower comparison on pure tensors by applying the intervening coefficient map. -/
@[simp]
theorem scalarTower_tmul (s : S) (r : R) (m : M) :
    scalarTower (k := k) (s ⊗ₜ[R] (r ⊗ₜ[k] m)) = (r • s) ⊗ₜ[k] m :=
  rfl

/-- The tower comparison commutes with extending an arbitrary linear map. -/
theorem scalarTower_natural (f : M →ₗ[k] N) :
    (scalarTower (k := k) (R := R) (S := S)).toLinearMap.comp ((f.baseChange R).baseChange S) =
      (f.baseChange S).comp (scalarTower (k := k) (R := R) (S := S)).toLinearMap := by
  apply AlgebraTensorModule.ext
  intro s t
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul r m => simp
  | add x y hx hy => rw [tmul_add, map_add, map_add, hx, hy]

variable {T : Type u} [CommRing T] [Algebra k T] [Algebra R T] [Algebra S T]
variable [IsScalarTower k R T] [IsScalarTower k S T] [IsScalarTower R S T]

/-- The two ways to collapse three consecutive scalar extensions agree. -/
theorem scalarTower_three :
    (scalarTower (k := k) (R := S) (S := T) (M := M)).toLinearMap.comp
      (((scalarTower (k := k) (R := R) (S := S) (M := M)).toLinearMap).baseChange T) =
    (scalarTower (k := k) (R := R) (S := T) (M := M)).toLinearMap.comp
      (scalarTower (k := R) (R := S) (S := T) (M := R ⊗[k] M)).toLinearMap := by
  apply AlgebraTensorModule.ext
  intro t v
  induction v using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [tmul_add, map_add, map_add, ha, hb]
  | tmul s w =>
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => rw [tmul_add, tmul_add, map_add, map_add, ha, hb]
    | tmul r m => simp [smul_assoc]

end Tower

/-- A linear inclusion is universally injective if it stays injective after every
scalar extension to a commutative algebra. -/
def UniversallyInjective (f : M →ₗ[k] N) : Prop :=
  ∀ (R : Type u) [CommRing R] [Algebra k R], Function.Injective (f.baseChange R)

/-- A split inclusion stays injective because scalar extension preserves its retraction. -/
theorem universallyInjective_of_retraction (f : M →ₗ[k] N) (g : N →ₗ[k] M)
    (h : g.comp f = LinearMap.id) : UniversallyInjective f := by
  intro R _ _
  apply Function.LeftInverse.injective (g := g.baseChange R)
  intro x
  have he := congrArg (fun m : M →ₗ[k] M => m.baseChange R) h
  change (g.comp f).baseChange R = (LinearMap.id : M →ₗ[k] M).baseChange R at he
  rw [LinearMap.baseChange_comp, LinearMap.baseChange_id] at he
  exact LinearMap.congr_fun he x

end SHIGURE.TensorRealization
