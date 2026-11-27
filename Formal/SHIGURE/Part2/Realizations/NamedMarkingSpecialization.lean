import Formal.SHIGURE.Part2.Realizations.MarkingTransport
import Formal.SHIGURE.Part2.Realizations.MarkedChartSpecialization

/-! # Specialization preserves the original named marking columns -/

namespace SHIGURE.RealizationFamilies

open CategoryTheory Module MvPolynomial TensorProduct SHIGURE.TensorRealization
open scoped TensorProduct

noncomputable section

universe u

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  (sig : Signature.{u}) (rank m : sig.SortType → ℕ)
  (choice : MarkedBasisChoice sig rank m)

private abbrev ambient := MvPolynomial (MarkedChartVariable sig rank m choice) R

private theorem standard_basis_change_unit {k A : Type u} [CommRing k] [CommRing A] [Algebra k A]
    {n : ℕ} (x : Fin n → k) (i : Fin n) :
    ((Pi.basisFun k (Fin n)).baseChange A).equivFun ((1 : A) ⊗ₜ[k] x) i = algebraMap k A (x i) := by
  rw [Basis.equivFun_apply, Basis.baseChange_repr_tmul, Algebra.smul_def, mul_one, ← Basis.equivFun_apply,
    Pi.basisFun_equivFun]
  rfl

/-- On unit tensors, the original specialization comparison applies the
coefficient map to each coordinate of the source vector. -/
theorem universalMarkedTensor_specializationIso_unit
    (c : PrimitiveCoefficients sig rank S) (v : MarkingCoordinate sig rank m choice → S)
    (s : sig.SortType) (x : Fin (rank s) → ambient (R := R) sig rank m choice) (i : Fin (rank s)) :
    let q := markedChartEvaluator (R := R) sig rank m choice c v
    let A := ambient (R := R) sig rank m choice
    letI : Algebra A S := q.toRingHom.toAlgebra
    ((universalMarkedTensor_specializationIso (R := R) sig rank m choice c v).hom.onSort s)
        ((1 : S) ⊗ₜ[A] x) i = q (x i) := by
  let q := markedChartEvaluator (R := R) sig rank m choice c v
  let A := ambient (R := R) sig rank m choice
  letI : Algebra A S := q.toRingHom.toAlgebra
  let U := universalMarkedTensor (R := R) sig rank m choice
  let b := extendedBasis (S := S) U (fun _ => Pi.basisFun _ _)
  have carrier := tensorIsoOfBasisAndCoefficients_onSort sig rank (extendStructure A S U) b c
    (universalMarkedTensor_coefficients (R := R) sig rank m choice c v) s
  have evaluate := standard_basis_change_unit (A := S) x i
  exact (congrArg (fun h => h ((1 : S) ⊗ₜ[A] x) i) carrier).trans evaluate

/-- The full marked specialization gives the actual evaluated operations and
every original marking column, without adding variables for the named generators. -/
def universalNamedMarkedTensor_specializationIso
    (c : PrimitiveCoefficients sig rank S) (v : MarkingCoordinate sig rank m choice → S) :
    let q := markedChartEvaluator (R := R) sig rank m choice c v
    let A := ambient (R := R) sig rank m choice
    letI : Algebra A S := q.toRingHom.toAlgebra
    extendStructure A S (universalNamedMarkedTensor (R := R) sig m rank choice) ≅
      withMarkingOperations sig m (c.toTensor sig rank)
        (fun s j i => markingMatrix sig rank m choice v s i j) := by
  let q := markedChartEvaluator (R := R) sig rank m choice c v
  let A := ambient (R := R) sig rank m choice
  letI : Algebra A S := q.toRingHom.toAlgebra
  let U := universalMarkedTensor (R := R) sig rank m choice
  let rows (s : sig.SortType) (j : Fin (m s)) (i : Fin (rank s)) := universalMarkingMatrix (R := R) sig rank m choice s i j
  let e := universalMarkedTensor_specializationIso (R := R) sig rank m choice c v
  let changed (s : sig.SortType) (j : Fin (m s)) : (extendStructure A S U).carrier s :=
    (1 : S) ⊗ₜ[A] rows s j
  have exactMarks (s : sig.SortType) (j : Fin (m s)) :
      e.hom.onSort s (changed s j) = fun i => markingMatrix sig rank m choice v s i j := by
    funext i
    have eval := universalMarkedTensor_specializationIso_unit (R := R) sig rank m choice c v s (rows s j) i
    have matrix := congrArg (fun M => M i j) (universalMarkingMatrix_eval (R := R) sig rank m choice c v s)
    exact eval.trans matrix
  exact markedScalarIso sig m U rows ≪≫ markPreservingExtensionIso sig m changed e exactMarks

end

end SHIGURE.RealizationFamilies
