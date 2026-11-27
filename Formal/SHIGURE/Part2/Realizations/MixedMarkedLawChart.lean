import Formal.SHIGURE.Part2.Realizations.MarkingNullaryTerms
import Formal.SHIGURE.Part2.Realizations.TensorShapeCoordinates
import Formal.SHIGURE.Part2.Realizations.TensorLawScalarComposition
import Formal.SHIGURE.Part2.Realizations.PolynomialCoordinates
import Formal.SHIGURE.Part2.Quantities.Representation

/-! # The common affine chart for tensor and polynomial Laws with marked generators -/

namespace SHIGURE.RealizationFamilies

open AlgebraicGeometry CategoryTheory MvPolynomial SHIGURE.TensorRealization

noncomputable section

universe u

/-- Required Laws may have either linear tensor syntax or typed polynomial
syntax, in both cases over the originally designated generators. -/
inductive MixedMarkedLaw (R : Type u) (sig : Signature.{u}) (m : sig.SortType → ℕ)
  | tensor (law : TensorLaw R (markingSignature sig m))
  | polynomial {Γ : List sig.SortType} {s : sig.SortType}
      (law : PolynomialLaw R (markingSignature sig m) Γ s)

variable {R : Type u} [CommRing R] (sig : Signature.{u}) (rank m : sig.SortType → ℕ)
  (choice : MarkedBasisChoice sig rank m)

private abbrev ambient := MvPolynomial (MarkedChartVariable sig rank m choice) R

variable {S : Type u} [CommRing S] [Algebra R S]

/-- Evaluate a written Law with its native syntax in the actual realized structure. -/
def MixedMarkedLaw.holds (A : TensorStructure S (markingSignature sig m)) :
    MixedMarkedLaw R sig m → Prop
  | .tensor law => (law.mapScalars (algebraMap R S)).holds A
  | .polynomial law => law.Holds (algebraMap R S) A

/-- Equation (6.2) takes the original tensor entries or all monomial
coefficients, according to the original written Law. -/
def mixedMarkedLawIdeal :
    MixedMarkedLaw R sig m → Ideal (ambient (R := R) sig rank m choice)
  | .tensor law =>
    tensorLawResidualIdeal (fun _ => Pi.basisFun _ _) (law.mapScalars (algebraMap R _))
      (A := universalNamedMarkedTensor sig m rank choice)
  | .polynomial law =>
    polynomialResidualIdeal
      (law.residual (algebraMap R _) (universalNamedMarkedTensor sig m rank choice) (fun _ => Pi.basisFun _ _))

/-- A specialization kills the residual ideal of the original Law exactly
when the actual specialized marked realization satisfies that Law. -/
theorem mixedMarkedLawIdeal_le_ker_iff
    (q : ambient (R := R) sig rank m choice →ₐ[R] S) (l : MixedMarkedLaw R sig m) :
    let A := ambient (R := R) sig rank m choice
    letI : Algebra A S := q.toRingHom.toAlgebra
    mixedMarkedLawIdeal sig rank m choice l ≤ RingHom.ker q.toRingHom ↔
      l.holds sig m (extendStructure A S (universalNamedMarkedTensor sig m rank choice)) := by
  let A := ambient (R := R) sig rank m choice
  letI : Algebra A S := q.toRingHom.toAlgebra
  let U := universalNamedMarkedTensor (R := R) sig m rank choice
  have factors : (algebraMap A S).comp (algebraMap R A) = algebraMap R S := RingHom.ext q.commutes
  cases l with
  | tensor law =>
    have works := tensorLawResidualIdeal_le_ker_iff (S := S) (A := U)
      (fun s => Pi.basisFun A (Fin (rank s))) (law.mapScalars (algebraMap R A))
    rw [TensorLaw.mapScalars_comp, factors] at works
    exact works
  | polynomial law =>
    have works := law.residualIdeal_baseChange (S := S) (algebraMap R A) U
      (fun s => Pi.basisFun A (Fin (rank s)))
    rw [factors] at works
    change polynomialResidualIdeal (law.residual (algebraMap R A) U (fun _ => Pi.basisFun _ _)) ≤
      RingHom.ker q.toRingHom ↔ law.Holds (algebraMap R S) (extendStructure A S U)
    rw [RingHom.ker_eq_comap_bot, ← Ideal.map_le_iff_le_comap]
    change (polynomialResidualIdeal (law.residual (algebraMap R A) U (fun _ => Pi.basisFun _ _))).map
      (algebraMap A S) ≤ ⊥ ↔ law.Holds (algebraMap R S) (extendStructure A S U)
    rw [← works, le_bot_iff]
    exact (law.holds_iff_residualIdeal_eq_bot (algebraMap R S) (extendStructure A S U)
      (extendedBasis U (fun _ => Pi.basisFun _ _))).symm

variable {J : Type u} (laws : J → MixedMarkedLaw R sig m)

/-- Impose every required Law, for an arbitrary small family. -/
def mixedMarkedResidualIdeal : Ideal (ambient (R := R) sig rank m choice) :=
  ⨆ j, mixedMarkedLawIdeal sig rank m choice (laws j)

/-- The complete chart algebra of the written tensor and polynomial Laws. -/
abbrev mixedMarkedChartAlgebra :=
  ambient (R := R) sig rank m choice ⧸ mixedMarkedResidualIdeal sig rank m choice laws

/-- The actual mixed Law affine chart over the original base. -/
def mixedMarkedChartScheme : Over (Spec (CommRingCat.of R)) :=
  specOver (mixedMarkedChartAlgebra sig rank m choice laws)

/-- The universal marked tensor realization over the quotient satisfies
each of the written Laws under its original interpretation. -/
theorem mixedMarkedChart_universal_holds (j : J) :
    let A := ambient (R := R) sig rank m choice
    let B := mixedMarkedChartAlgebra sig rank m choice laws
    let q := Ideal.Quotient.mkₐ R (mixedMarkedResidualIdeal sig rank m choice laws)
    letI : Algebra A B := q.toRingHom.toAlgebra
    (laws j).holds sig m (extendStructure A B (universalNamedMarkedTensor sig m rank choice)) := by
  let q := Ideal.Quotient.mkₐ R (mixedMarkedResidualIdeal sig rank m choice laws)
  apply (mixedMarkedLawIdeal_le_ker_iff sig rank m choice q (laws j)).mp
  have quotientKernel : RingHom.ker q.toRingHom = mixedMarkedResidualIdeal sig rank m choice laws :=
    Ideal.Quotient.mkₐ_ker R _
  rw [quotientKernel]
  exact le_iSup (fun k => mixedMarkedLawIdeal sig rank m choice (laws k)) j

/-- Maps of the chart algebra are exactly the specializations satisfying every
required Law on the original tensor with its actual marking sections. -/
def mixedMarkedChartAlgHomEquiv :
    (mixedMarkedChartAlgebra sig rank m choice laws →ₐ[R] S) ≃
      {q : ambient (R := R) sig rank m choice →ₐ[R] S //
        let A := ambient (R := R) sig rank m choice
        letI : Algebra A S := q.toRingHom.toAlgebra
        ∀ j, (laws j).holds sig m (extendStructure A S (universalNamedMarkedTensor sig m rank choice))} := by
  let I := mixedMarkedResidualIdeal sig rank m choice laws
  let p := Ideal.Quotient.mkₐ R I
  let admissible (q : ambient (R := R) sig rank m choice →ₐ[R] S) :=
    I ≤ RingHom.ker q.toRingHom
  let lift : (mixedMarkedChartAlgebra sig rank m choice laws →ₐ[R] S) ≃
      {q : ambient (R := R) sig rank m choice →ₐ[R] S // admissible q} :=
    { toFun := fun f => ⟨f.comp p, by
        intro x hx
        change f (p x) = 0
        rw [show p x = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]⟩
      invFun := fun q => Ideal.Quotient.liftₐ I q.1 (fun x hx => q.2 hx)
      left_inv := fun f => by
        apply Ideal.Quotient.algHom_ext
        exact Ideal.Quotient.liftₐ_comp _ _ _
      right_inv := fun q => by
        apply Subtype.ext
        exact Ideal.Quotient.liftₐ_comp _ _ _ }
  refine lift.trans (Equiv.subtypeEquivRight (fun q => ?_))
  change mixedMarkedResidualIdeal sig rank m choice laws ≤ RingHom.ker q.toRingHom ↔ _
  rw [mixedMarkedResidualIdeal, iSup_le_iff]
  exact forall_congr' fun j => mixedMarkedLawIdeal_le_ker_iff sig rank m choice q (laws j)

/-- The chart's specializations apply to arbitrary relative test schemes. -/
def mixedMarkedChartSchemePointEquiv (T : Over (Spec (CommRingCat.of R))) :
    letI := globalSectionsAlgebra T
    (T ⟶ mixedMarkedChartScheme sig rank m choice laws) ≃
      {q : ambient (R := R) sig rank m choice →ₐ[R] Γ(T.left, ⊤) //
        let A := ambient (R := R) sig rank m choice
        letI : Algebra A Γ(T.left, ⊤) := q.toRingHom.toAlgebra
        ∀ j, (laws j).holds sig m
          (extendStructure A Γ(T.left, ⊤) (universalNamedMarkedTensor sig m rank choice))} := by
  letI := globalSectionsAlgebra T
  exact (specOverPointEquiv T (mixedMarkedChartAlgebra sig rank m choice laws)).trans
    (mixedMarkedChartAlgHomEquiv sig rank m choice laws)

end

end SHIGURE.RealizationFamilies
