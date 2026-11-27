import Formal.SHIGURE.Part2.Realizations.MarkedChart
import Formal.SHIGURE.Part2.Realizations.PolynomialCoefficientChange

/-! # Specializing the actual marked realization -/

namespace SHIGURE.RealizationFamilies

open AlgebraicGeometry CategoryTheory MvPolynomial SHIGURE.TensorRealization

noncomputable section

universe u

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  (sig : Signature.{u}) (rank generators : sig.SortType → ℕ)
  (choice : MarkedBasisChoice sig rank generators)

private abbrev ambient := MvPolynomial (MarkedChartVariable sig rank generators choice) R

/-- The coordinates of the scalar extension are the images of the
original coefficients, for all input tuples and all output coordinates. -/
theorem primitiveCoordinates_baseChange
    (A : TensorStructure R sig) (b : ∀ s, Module.Basis (Fin (rank s)) R (A.carrier s)) (z : PrimitiveCoordinate sig rank) :
    PrimitiveCoefficients.valuesEquiv sig rank
      (PrimitiveCoefficients.ofTensor sig rank (extendStructure R S A) (extendedBasis A b)) z =
      algebraMap R S (PrimitiveCoefficients.valuesEquiv sig rank (PrimitiveCoefficients.ofTensor sig rank A b) z) := by
  cases z with
  | total e a j => exact operationCoefficient_baseChange (S := S) A b (A.total e) a j
  | quantity q a j => exact operationCoefficient_baseChange (S := S) A b (A.quantity q) a j

/-- In the extended basis, specializing the universal coefficients gives the chosen array. -/
theorem universalMarkedTensor_coefficients (c : PrimitiveCoefficients sig rank S)
    (v : MarkingCoordinate sig rank generators choice → S) :
    let q := markedChartEvaluator (R := R) sig rank generators choice c v
    let A := ambient (R := R) sig rank generators choice
    letI : Algebra A S := q.toRingHom.toAlgebra
    let U := universalMarkedTensor (R := R) sig rank generators choice
    PrimitiveCoefficients.ofTensor sig rank (extendStructure A S U) (extendedBasis U (fun _ => Pi.basisFun _ _)) = c := by
  let q := markedChartEvaluator (R := R) sig rank generators choice c v
  let A := ambient (R := R) sig rank generators choice
  letI : Algebra A S := q.toRingHom.toAlgebra
  let U := universalMarkedTensor (R := R) sig rank generators choice
  apply (PrimitiveCoefficients.valuesEquiv sig rank).injective
  funext z
  have changed := primitiveCoordinates_baseChange (S := S) sig rank U (fun _ => Pi.basisFun _ _) z
  have read : PrimitiveCoefficients.ofTensor sig rank U (fun _ => Pi.basisFun _ _) =
      universalPrimitiveCoefficients (R := R) sig rank generators choice :=
    PrimitiveCoefficients.ofTensor_toTensor sig rank _
  exact changed.trans ((congrArg (fun w =>
    q (PrimitiveCoefficients.valuesEquiv sig rank w z)) read).trans
    (universalPrimitiveCoefficients_eval sig rank generators choice c v z))

/-- The actual specialized primitive realization is isomorphic to the
realization constructed in the chosen coordinates. -/
def universalMarkedTensor_specializationIso (c : PrimitiveCoefficients sig rank S)
    (v : MarkingCoordinate sig rank generators choice → S) :
    let q := markedChartEvaluator (R := R) sig rank generators choice c v
    let A := ambient (R := R) sig rank generators choice
    letI : Algebra A S := q.toRingHom.toAlgebra
    extendStructure A S (universalMarkedTensor (R := R) sig rank generators choice) ≅ c.toTensor sig rank := by
  let q := markedChartEvaluator (R := R) sig rank generators choice c v
  let A := ambient (R := R) sig rank generators choice
  letI : Algebra A S := q.toRingHom.toAlgebra
  let U := universalMarkedTensor (R := R) sig rank generators choice
  exact tensorIsoOfBasisAndCoefficients sig rank (extendStructure A S U)
    (extendedBasis U (fun _ => Pi.basisFun _ _)) c
    (universalMarkedTensor_coefficients (R := R) sig rank generators choice c v)

variable {J : Type u} (laws : MarkedPolynomialLaws (R := R) sig J)

/-- The residual equations on coordinates impose exactly the written Laws
on the original free realization associated to those coordinates. -/
theorem markedChartEvaluator_lawful_iff (c : PrimitiveCoefficients sig rank S)
    (v : MarkingCoordinate sig rank generators choice → S) :
    markedResidualIdeal sig rank generators choice laws ≤
      RingHom.ker (markedChartEvaluator sig rank generators choice c v).toRingHom ↔
      ∀ j, (laws.law j).Holds (algebraMap R S) (c.toTensor sig rank) := by
  exact (markedResidualIdeal_le_ker_iff sig rank generators choice laws
    (markedChartEvaluator sig rank generators choice c v)).trans
      (forall_congr' fun j => (laws.law j).holds_iff_of_iso (algebraMap R S)
        (universalMarkedTensor_specializationIso (R := R) sig rank generators choice c v))

/-- The primitive and marking coordinates of a point of the ambient affine space. -/
abbrev MarkedCoordinatePair (S : Type u) :=
  PrimitiveCoefficients sig rank S × (MarkingCoordinate sig rank generators choice → S)

/-- A point of the ambient ring is specified independently on both sets of variables. -/
def markedAmbientCoordinateEquiv :
    (ambient (R := R) sig rank generators choice →ₐ[R] S) ≃
      MarkedCoordinatePair sig rank generators choice S :=
  polynomialPointEquiv.trans ((Equiv.sumArrowEquivProdArrow _ _ _).trans
    (Equiv.prodCongr (PrimitiveCoefficients.valuesEquiv sig rank).symm (Equiv.refl _)))

/-- The inverse of reading the two kinds of coordinate evaluates the original variables. -/
theorem markedAmbientCoordinateEquiv_symm_apply (c : MarkedCoordinatePair sig rank generators choice S) :
    (markedAmbientCoordinateEquiv (R := R) sig rank generators choice).symm c =
      markedChartEvaluator sig rank generators choice c.1 c.2 := rfl

/-- The coordinate pairs in the actual free chart are those whose primitive structure satisfies all Laws. -/
abbrev LawfulMarkedCoordinates (S : Type u) [CommRing S] [Algebra R S] :=
  {c : MarkedCoordinatePair sig rank generators choice S //
    ∀ j, (laws.law j).Holds (algebraMap R S) (c.1.toTensor sig rank)}

/-- Algebra points of the quotient correspond to lawful coordinates for the original free structures. -/
def markedChartCoordinateEquiv :
    (markedChartAlgebra sig rank generators choice laws →ₐ[R] S) ≃
      LawfulMarkedCoordinates sig rank generators choice laws S := by
  let e := markedAmbientCoordinateEquiv (R := R) (S := S) sig rank generators choice
  refine (markedChartAlgHomEquiv sig rank generators choice laws S).trans (e.subtypeEquiv ?_)
  intro q
  have fromCoordinates : q = markedChartEvaluator sig rank generators choice (e q).1 (e q).2 :=
    (e.symm_apply_apply q).symm.trans
      (markedAmbientCoordinateEquiv_symm_apply sig rank generators choice (e q))
  have sameKernel := congrArg (fun p => RingHom.ker p.toRingHom) fromCoordinates
  exact (Iff.of_eq (congrArg (markedResidualIdeal sig rank generators choice laws ≤ ·) sameKernel)).trans
    (markedChartEvaluator_lawful_iff sig rank generators choice laws (e q).1 (e q).2)

/-- Maps from any relative scheme to this chart give its lawful coordinates in global sections. -/
def markedChartCoordinatePointEquiv (T : Over (Spec (CommRingCat.of R))) :
    letI := globalSectionsAlgebra T
    (T ⟶ markedChartScheme sig rank generators choice laws) ≃
      LawfulMarkedCoordinates sig rank generators choice laws Γ(T.left, ⊤) := by
  letI := globalSectionsAlgebra T
  exact (specOverPointEquiv T (markedChartAlgebra sig rank generators choice laws)).trans
    (markedChartCoordinateEquiv sig rank generators choice laws)

end

end SHIGURE.RealizationFamilies
