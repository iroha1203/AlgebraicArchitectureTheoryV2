import Formal.SHIGURE.Part2.Realizations.MarkedChartSpecialization

/-! # Pulling back the coordinates of a marked chart point -/

namespace SHIGURE.RealizationFamilies

open AlgebraicGeometry CategoryTheory MvPolynomial SHIGURE.TensorRealization

noncomputable section

universe u

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  (sig : Signature.{u}) (rank generators : sig.SortType → ℕ)
  (choice : MarkedBasisChoice sig rank generators)
  {J : Type u} (laws : MarkedPolynomialLaws (R := R) sig J)

/-- In the affine quotient, each original primitive variable is its
corresponding coefficient of the realized operation. -/
theorem markedChartCoordinateEquiv_primitive
    (q : markedChartAlgebra sig rank generators choice laws →ₐ[R] S) (z : PrimitiveCoordinate sig rank) :
    PrimitiveCoefficients.valuesEquiv sig rank
      ((markedChartCoordinateEquiv sig rank generators choice laws q).val.1) z =
    q (Ideal.Quotient.mkₐ R (markedResidualIdeal sig rank generators choice laws) (X (Sum.inl z))) := by
  let p := Ideal.Quotient.mkₐ R (markedResidualIdeal sig rank generators choice laws)
  let c := PrimitiveCoefficients.valuesEquiv (R := S) sig rank
  change c (c.symm (fun i => q (p (X (Sum.inl i))))) z = _
  rw [Equiv.apply_symm_apply]

/-- In the affine quotient, each original marking variable is the
corresponding entry of the nonselected column. -/
theorem markedChartCoordinateEquiv_marking
    (q : markedChartAlgebra sig rank generators choice laws →ₐ[R] S)
    (z : MarkingCoordinate sig rank generators choice) :
    (markedChartCoordinateEquiv sig rank generators choice laws q).val.2 z =
    q (Ideal.Quotient.mkₐ R (markedResidualIdeal sig rank generators choice laws) (X (Sum.inr z))) := rfl

variable {T T' : Over (Spec (CommRingCat.of R))}

/-- Along any relative test morphism, a primitive coefficient is pulled
back by the actual map on global sections. -/
theorem markedChartCoordinatePointEquiv_precomp_primitive (g : T' ⟶ T)
    (p : T ⟶ markedChartScheme sig rank generators choice laws) (z : PrimitiveCoordinate sig rank) :
    PrimitiveCoefficients.valuesEquiv sig rank
      ((markedChartCoordinatePointEquiv sig rank generators choice laws T' (g ≫ p)).val.1) z =
    (Scheme.Γ.map g.left.op).hom (PrimitiveCoefficients.valuesEquiv sig rank
      ((markedChartCoordinatePointEquiv sig rank generators choice laws T p).val.1) z) := by
  letI := globalSectionsAlgebra T
  letI := globalSectionsAlgebra T'
  let B := markedChartAlgebra sig rank generators choice laws
  let e := (Ideal.Quotient.mkₐ R (markedResidualIdeal sig rank generators choice laws)) (X (Sum.inl z))
  have direct := markedChartCoordinateEquiv_primitive sig rank generators choice laws
    (specOverPointEquiv T B p) z
  have composed := markedChartCoordinateEquiv_primitive sig rank generators choice laws
    (specOverPointEquiv T' B (g ≫ p)) z
  exact composed.trans ((AlgHom.congr_fun (specOverPointEquiv_precomp g p) e).trans
    (congrArg (Scheme.Γ.map g.left.op).hom direct.symm))

/-- The nonselected markings pull back by the same actual global sections map. -/
theorem markedChartCoordinatePointEquiv_precomp_marking (g : T' ⟶ T)
    (p : T ⟶ markedChartScheme sig rank generators choice laws) (z : MarkingCoordinate sig rank generators choice) :
    (markedChartCoordinatePointEquiv sig rank generators choice laws T' (g ≫ p)).val.2 z =
    (Scheme.Γ.map g.left.op).hom ((markedChartCoordinatePointEquiv sig rank generators choice laws T p).val.2 z) := by
  letI := globalSectionsAlgebra T
  letI := globalSectionsAlgebra T'
  exact AlgHom.congr_fun (specOverPointEquiv_precomp g p) _

end

end SHIGURE.RealizationFamilies
