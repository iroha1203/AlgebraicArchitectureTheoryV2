import Formal.SHIGURE.Part2.Realizations.MixedMarkedSchemeChart
import Formal.SHIGURE.Part2.Tensor.FrobeniusExample

/-! # A named-generator equation in both chart syntaxes -/

namespace SHIGURE.RealizationFamilies.Examples

open SHIGURE.TensorRealization
open scoped TensorProduct

noncomputable section

private abbrev sig := SHIGURE.TensorRealization.scalarRingSignature
private abbrev rank (_ : Unit) := 1
private abbrev m (_ : Unit) := 2
private abbrev choice : MarkedBasisChoice sig rank m := fun _ => Fin.castAddOrderEmb 1

private abbrev named := markingSignature sig m
private abbrev generator : named.Total := Sum.inr ⟨(), 1⟩

private def vanishingMark : Bool → MixedMarkedLaw ℤ sig m
  | true => .tensor
      { source := .arguments []
        target := .sort ()
        left := TensorExpression.total (R := ℤ) (sig := named) generator
        right := .zero _ _ }
  | false => .polynomial (Γ := []) (s := ())
      ⟨PolynomialTerm.total (k := ℤ) (sig := named) (Γ := []) generator
          (fun i => nomatch i.2),
        PolynomialTerm.zero (k := ℤ) (sig := named) (Γ := []) ()⟩

private def point (z : ℤ) : MarkedCoordinatePair sig rank m choice ℤ :=
  (⟨fun _ _ _ => 0, fun _ _ _ => 0⟩, fun _ => z)

private theorem second_not_selected : (1 : Fin 2) ∉ Set.range (choice ()) := by
  rintro ⟨j, h⟩
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  exact (by decide : ¬ (choice () (0 : Fin 1) = 1)) h

private theorem point_second (z : ℤ) (i : Fin 1) :
    markingMatrix sig rank m choice (point z).2 () i 1 = z :=
  markingMatrix_nonselected sig rank m choice (point z).2 () i 1 second_not_selected

private abbrev A (z : ℤ) := namedMarkedCoordinateTensor sig rank m choice (point z)

private theorem second_total (z : ℤ)
    (x : ∀ i : TensorPosition ([] : List Unit), (A z).carrier i.1) :
    (A z).total generator x = fun _ => z := by
  funext i
  exact point_second z i

private theorem zeroTensor :
    (vanishingMark true).holds sig m (A 0) := by
  change PiTensorProduct.lift ((A 0).total generator) = 0
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  change PiTensorProduct.lift ((A 0).total generator) (PiTensorProduct.tprod ℤ x) = 0
  exact (PiTensorProduct.lift.tprod (φ := (A 0).total generator) x).trans (second_total 0 x)

private theorem zeroPolynomial :
    (vanishingMark false).holds sig m (A 0) := by
  intro S _ algebra x
  letI : Module ℤ S := algebra.toModule
  change (extendStructure ℤ S (A 0)).total generator (fun i => nomatch i.2) = 0
  let y : ∀ i : TensorPosition ([] : List Unit), (A 0).carrier i.1 := fun i => nomatch i.2
  let Y := (A 0).carrier
  let input (i : TensorPosition ([] : List Unit)) : extendCarriers ℤ Y S i.1 :=
    (1 : S) ⊗ₜ[ℤ] y i
  have scalar := extendOperation_unit ℤ Y S ((A 0).total generator) y
  change extendOperation ℤ Y S ((A 0).total generator) input = _ at scalar
  change extendOperation ℤ Y S ((A 0).total generator) _ = 0
  calc
    _ = extendOperation ℤ Y S ((A 0).total generator) input := by
      congr 1
      funext i
      exact nomatch i.2
    _ = (1 : S) ⊗ₜ[ℤ] ((A 0).total generator y) := scalar
    _ = 0 := by
      rw [show (A 0).total generator y = 0 from second_total 0 y, TensorProduct.tmul_zero]

/-- Both equations that set a designated generator to zero give a point
of the same affine chart, with the first generator retained as a basis. -/
def mixedMarkedZeroColumnPoint :
    mixedMarkedChartAlgebra sig rank m choice vanishingMark →ₐ[ℤ] ℤ :=
  (mixedMarkedChartCoordinateEquiv sig rank m choice vanishingMark).symm
    ⟨point 0, fun b => Bool.casesOn b zeroPolynomial zeroTensor⟩

/-- Giving that same generator the value one violates its tensor equation. -/
theorem mixedMarkedNonzeroColumn_rejected :
    ¬ (vanishingMark true).holds sig m (A 1) := by
  intro law
  change PiTensorProduct.lift ((A 1).total generator) = 0 at law
  let x : ∀ i : TensorPosition ([] : List Unit), (A 1).carrier i.1 := fun i => nomatch i.2
  have evaluated := DFunLike.congr_fun law (PiTensorProduct.tprod ℤ x)
  have vanishes : (A 1).total generator x = 0 :=
    (PiTensorProduct.lift.tprod (φ := (A 1).total generator) x).symm.trans evaluated
  exact one_ne_zero (congrFun ((second_total 1 x).symm.trans vanishes) (0 : Fin 1))

end

end SHIGURE.RealizationFamilies.Examples
