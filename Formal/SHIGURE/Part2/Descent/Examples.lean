import Formal.SHIGURE.Part2.Descent.ModuleEquivalence
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Algebra.Prod

/-! # A split coefficient algebra

The two idempotents of the product algebra occupy distinct coefficient
positions. Scalar extension of a linear map acts on the final module
factor and the fixed-vector comparison recovers that action.
-/

namespace SHIGURE.CoefficientDescent.Examples

open TensorProduct CategoryTheory

noncomputable section

private abbrev Base := ℚ
private abbrev Cover := ℚ × ℚ

/-- The split coefficient algebra is faithfully flat over the rational field. -/
theorem split_faithfullyFlat : Module.FaithfullyFlat Base Cover := inferInstance

/-- On a genuine product cover, the transition retains the two different idempotents. -/
theorem split_overlap (x : ℚ) :
    standardOverlap (A := Base) (B := Cover) (M := Base)
      ((((1, 0) : Cover) ⊗ₜ[Base] x) ⊗ₜ[Base] ((0, 1) : Cover)) =
      ((1, 0) : Cover) ⊗ₜ[Base] (((0, 1) : Cover) ⊗ₜ[Base] x) :=
  standardOverlap_tmul _ _ _

/-- The named comparison recovers the initial scalar even on the product cover. -/
theorem split_unit_recovers (x : ℚ) :
    (standardUnitEquiv (A := Base) (B := Cover) (M := Base)).symm
      (standardUnit (A := Base) (B := Cover) (M := Base) x) = x :=
  (standardUnitEquiv (A := Base) (B := Cover) (M := Base)).symm_apply_apply x

private abbrev line := ModuleCat.of Base Base

private def twice : line ⟶ line := ModuleCat.ofHom (2 • (LinearMap.id : Base →ₗ[Base] Base))

/-- The equivalence transports doubling on the module factor while retaining the first idempotent. -/
theorem split_map_doubles :
    ((DescentModule.equivalence (A := Base) (B := Cover)).functor.map twice).hom
      (((1, 0) : Cover) ⊗ₜ[Base] (3 : ℚ)) = ((1, 0) : Cover) ⊗ₜ[Base] (6 : ℚ) := by
  change twice.hom.baseChange Cover (((1, 0) : Cover) ⊗ₜ[Base] (3 : ℚ)) = _
  rw [LinearMap.baseChange_tmul]
  apply congrArg (fun x : ℚ => ((1, 0) : Cover) ⊗ₜ[Base] x)
  norm_num [twice]

end

end SHIGURE.CoefficientDescent.Examples
