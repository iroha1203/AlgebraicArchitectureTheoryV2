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

private def coverLine : DescentModule Base Cover :=
  (DescentModule.extend (A := Base) (B := Cover)).obj line

private def coverTwice : coverLine ⟶ coverLine :=
  (DescentModule.extend (A := Base) (B := Cover)).map twice

private def fixedThree : coverLine.datum.toCoaction.descended :=
  standardUnit (A := Base) (B := Cover) (M := Base) 3

/-- On an actual fixed vector the comparison multiplies by the chosen idempotent. -/
theorem split_comparison_fixed_vector :
    coverLine.datum.toCoaction.comparisonEquiv (((1, 0) : Cover) ⊗ₜ[Base] fixedThree) =
      ((1, 0) : Cover) ⊗ₜ[Base] (3 : ℚ) := by
  rw [Datum.comparisonEquiv_tmul]
  change ((1, 0) : Cover) • ((1 : Cover) ⊗ₜ[Base] (3 : ℚ)) = _
  rw [smul_tmul', smul_eq_mul, mul_one]

/-- Both paths around the comparison square give the same nonzero doubled vector. -/
theorem split_comparison_doubling_square :
    let input : Cover ⊗[Base] coverLine.datum.toCoaction.descended := ((1, 0) : Cover) ⊗ₜ[Base] fixedThree
    let output := ((1, 0) : Cover) ⊗ₜ[Base] (6 : ℚ)
    coverTwice.hom (coverLine.datum.toCoaction.comparison input) = output ∧
      coverLine.datum.toCoaction.comparison
        ((coverLine.datum.descendMap coverLine.datum coverTwice.hom coverTwice.compatible).baseChange Cover input) =
        output := by
  dsimp only
  have afterCompare :
      coverTwice.hom (coverLine.datum.toCoaction.comparison (((1, 0) : Cover) ⊗ₜ[Base] fixedThree)) =
        ((1, 0) : Cover) ⊗ₜ[Base] (6 : ℚ) := by
    change coverTwice.hom (coverLine.datum.toCoaction.comparisonEquiv
      (((1, 0) : Cover) ⊗ₜ[Base] fixedThree)) = _
    rw [split_comparison_fixed_vector]
    exact split_map_doubles
  refine ⟨afterCompare, ?_⟩
  have natural := coverLine.datum.comparison_natural coverLine.datum coverTwice.hom coverTwice.compatible
  exact (LinearMap.congr_fun natural (((1, 0) : Cover) ⊗ₜ[Base] fixedThree)).symm.trans afterCompare

private def firstProjection : Cover →ₗ[Base] Base := LinearMap.fst Base Base Base

private def secondProjection : Cover →ₗ[Base] Base := LinearMap.snd Base Base Base

private def readOffDiagonal : Cover ⊗[Base] (Cover ⊗[Base] Base) →ₗ[Base] Base :=
  (TensorProduct.lid Base Base).toLinearMap.comp (TensorProduct.map firstProjection
    ((TensorProduct.lid Base Base).toLinearMap.comp (secondProjection.rTensor Base)))

private def multiplyByFirst : coverLine.carrier →ₗ[Cover] coverLine.carrier :=
  ((1, 0) : Cover) • LinearMap.id

/-- Multiplication by one idempotent is linear over the cover and fails descent. -/
theorem split_idempotent_incompatible :
    ¬ coverLine.datum.Compatible coverLine.datum multiplyByFirst := by
  intro compatible
  have held := (coverLine.datum.compatible_iff_coaction coverLine.datum multiplyByFirst).1 compatible
    ((1 : Cover) ⊗ₜ[Base] (1 : Base))
  have scalarValue :
      multiplyByFirst ((1 : Cover) ⊗ₜ[Base] (1 : Base)) =
        ((1, 0) : Cover) ⊗ₜ[Base] (1 : Base) := by
    change ((1, 0) : Cover) • ((1 : Cover) ⊗ₜ[Base] (1 : Base)) = _
    rw [smul_tmul', smul_eq_mul, mul_one]
  have initial : coverLine.datum.coactionMap ((1 : Cover) ⊗ₜ[Base] (1 : Base)) =
      (1 : Cover) ⊗ₜ[Base] ((1 : Cover) ⊗ₜ[Base] (1 : Base)) := rfl
  have image : coverLine.datum.coactionMap (((1, 0) : Cover) ⊗ₜ[Base] (1 : Base)) =
      ((1, 0) : Cover) ⊗ₜ[Base] ((1 : Cover) ⊗ₜ[Base] (1 : Base)) := rfl
  rw [initial, LinearMap.baseChange_tmul, LinearMap.restrictScalars_apply, scalarValue, image] at held
  have contradiction := congrArg readOffDiagonal held
  norm_num [readOffDiagonal, firstProjection, secondProjection] at contradiction

/-- The zero linear map fails the counit on a nonzero vector. -/
theorem zero_coaction_fails :
    ¬ ∃ ρ : Coaction Base Base Base, ρ.map = 0 := by
  rintro ⟨ρ, same⟩
  have contradiction := ρ.counit 1
  rw [same, LinearMap.zero_apply, map_zero] at contradiction
  exact zero_ne_one contradiction

attribute [local instance] doubleModule

private def negativeOverlap : OverlapIso Base Base Base :=
  LinearEquiv.neg (Base ⊗[Base] Base)

private theorem negativeOverlap_apply (x : Base ⊗[Base] Base) : negativeOverlap x = -x :=
  LinearEquiv.neg_apply x

/-- A double-linear overlap with a reversed sign fails the triple condition. -/
theorem sign_reversed_overlap_fails :
    ¬ (move12 negativeOverlap).comp (move01 negativeOverlap) = move02 negativeOverlap := by
  intro compatible
  let D : Datum Base Base Base := ⟨negativeOverlap, compatible⟩
  have contradiction := D.coaction_counit (1 : Base)
  change multiply (A := Base) (negativeOverlap ((1 : Base) ⊗ₜ[Base] (1 : Base))) = 1 at contradiction
  rw [negativeOverlap_apply, map_neg, multiply_tmul, one_smul] at contradiction
  norm_num at contradiction

end

end SHIGURE.CoefficientDescent.Examples
