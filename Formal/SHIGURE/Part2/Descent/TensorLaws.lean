import Formal.SHIGURE.Part2.Descent.ExpressionNaturality
import Formal.SHIGURE.Part2.Descent.Structures
import Formal.SHIGURE.Part2.Tensor.ExpressionBaseChange

/-! # Descent of equations between written tensor expressions -/

namespace SHIGURE.CoefficientDescent.TensorDatum

open TensorProduct TensorRealization

noncomputable section

universe u

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable [Module.FaithfullyFlat A B] {sig : Signature.{u}}

variable (D : TensorDatum A B sig)

/-- The shape comparison uses coefficient extension followed by the B.4 fixed vectors at each sort. -/
def shapeComparison (X : TensorShape sig.SortType) :
    (B ⊗[A] X.module D.descended) ≃ₗ[B] X.module D.native :=
  shapeBaseChange D.descended X ≪≫ₗ
    X.equivSorts (fun s => (D.sort s).datum.toCoaction.comparisonEquiv)

/-- Every native tensor expression is evaluated by the coefficient extension of its descended evaluation. -/
theorem eval_comparison {X Y : TensorShape sig.SortType} (term : TensorExpression A sig X Y) :
    (D.shapeComparison Y).toLinearMap.comp ((term.eval D.descended).baseChange B) =
      ((term.mapScalars (algebraMap A B)).eval D.native).comp (D.shapeComparison X).toLinearMap := by
  let e (X : TensorShape sig.SortType) :=
    X.equivSorts (U := extendStructure A B D.descended) (V := D.native)
      (fun s => (D.sort s).datum.toCoaction.comparisonEquiv)
  let extended := term.mapScalars (algebraMap A B)
  have comparison (X : TensorShape sig.SortType) : X.mapSorts D.comparison.onSort = (e X).toLinearMap :=
    (TensorShape.equivSorts_toLinearMap (U := extendStructure A B D.descended) (V := D.native)
      (fun s => (D.sort s).datum.toCoaction.comparisonEquiv) X).symm
  have square := extended.eval_natural D.comparison
  rw [comparison Y, comparison X, eval_mapScalars_eq_extendShapeMap] at square
  apply LinearMap.ext
  intro z
  have evaluated := LinearMap.congr_fun square (shapeBaseChange (R := B) D.descended X z)
  simpa only [extendShapeMap, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] using evaluated

/-- The equality of the two actual Law evaluations is preserved and reflected by faithful descent. -/
theorem tensorLaw_holds_iff (law : TensorLaw A sig) :
    (law.mapScalars (algebraMap A B)).holds D.native ↔ law.holds D.descended := by
  change (law.left.mapScalars (algebraMap A B)).eval D.native =
    (law.right.mapScalars (algebraMap A B)).eval D.native ↔ law.left.eval D.descended = law.right.eval D.descended
  constructor
  · intro h
    apply LinearMap.ext
    intro x
    have left := LinearMap.congr_fun (D.eval_comparison law.left) ((1 : B) ⊗ₜ[A] x)
    have right := LinearMap.congr_fun (D.eval_comparison law.right) ((1 : B) ⊗ₜ[A] x)
    rw [h] at left
    have equal := (D.shapeComparison law.target).injective (left.trans right.symm)
    rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul] at equal
    apply (standardUnitEquiv (A := A) (B := B) (M := law.target.module D.descended)).injective
    exact Subtype.ext equal
  · intro h
    apply (LinearMap.cancel_right (g := (D.shapeComparison law.source).toLinearMap)
      (D.shapeComparison law.source).surjective).1
    rw [← D.eval_comparison law.left, ← D.eval_comparison law.right, h]

end

end SHIGURE.CoefficientDescent.TensorDatum
