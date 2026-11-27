import Formal.SHIGURE.Part2.Realizations.MixedMarkedSchemeChart
import Formal.SHIGURE.Part2.Realizations.SchemeMarkedNormalization

/-! # Isomorphism classes, universal realization, and coefficient naturality for the mixed chart -/

namespace SHIGURE.RealizationFamilies

open AlgebraicGeometry CategoryTheory MvPolynomial SHIGURE.TensorRealization

noncomputable section

universe u

variable {R : Type u} [CommRing R] (sig : Signature.{u}) (rank m : sig.SortType → ℕ)
  (choice : MarkedBasisChoice sig rank m) {J : Type u} (laws : J → MixedMarkedLaw R sig m)

private abbrev B := mixedMarkedChartAlgebra sig rank m choice laws
private abbrev chart := mixedMarkedChartScheme sig rank m choice laws
private abbrev quotient := Ideal.Quotient.mkₐ R (mixedMarkedResidualIdeal sig rank m choice laws)

variable (T : Over (Spec (CommRingCat.of R)))

private abbrev originalClasses :=
  Quot (fun A B : BasedSchemeMarkedRealization T.left sig rank m choice =>
    Nonempty (BasedSchemeMarkedRealization.MarkedIso T.left sig rank m choice A B))

private abbrev classesToNormalized :=
  BasedSchemeMarkedRealization.markedIsoClassEquiv T.left sig rank m choice

/-- Isomorphism classes of originally marked realizations with the chosen
basis and all the required written Laws. -/
abbrev LawfulMixedMarkedClasses :=
  letI := globalSectionsAlgebra T
  {a : originalClasses sig rank m choice T //
    ∀ j, (laws j).holds sig m
      (namedSchemeMarkedStructure T.left sig rank m choice (classesToNormalized sig rank m choice T a))}

/-- The chart has exactly the original marked isomorphism classes with
that basis, with their actual operations and Law interpretations. -/
def mixedMarkedChartClassEquiv :
    (T ⟶ chart sig rank m choice laws) ≃ LawfulMixedMarkedClasses sig rank m choice laws T := by
  letI := globalSectionsAlgebra T
  exact (mixedMarkedChartRealizationEquiv sig rank m choice laws T).trans
    ((classesToNormalized sig rank m choice T).subtypeEquiv (fun _ => Iff.rfl)).symm

/-- The identity point gives the universal marked realization on the chart itself. -/
def mixedMarkedChartUniversal :
    LawfulMixedMarkedSchemeTensor sig rank m choice laws (chart sig rank m choice laws) :=
  mixedMarkedChartRealizationEquiv sig rank m choice laws
    (chart sig rank m choice laws) (𝟙 (chart sig rank m choice laws))

/-- Read coordinates from the actual marked sheaf data of a chart point. -/
def mixedMarkedChartPointCoordinates (p : T ⟶ chart sig rank m choice laws) :
    MarkedCoordinatePair sig rank m choice Γ(T.left, ⊤) :=
  normalizedSchemeMarkedTensorCoordinates T.left sig rank m choice
    ((mixedMarkedChartRealizationEquiv sig rank m choice laws T p).val)

private theorem mixedMarkedChartPointCoordinates_algebra (p : T ⟶ chart sig rank m choice laws) :
    letI := globalSectionsAlgebra T
    mixedMarkedChartPointCoordinates sig rank m choice laws T p =
      (mixedMarkedChartCoordinateEquiv sig rank m choice laws
        (specOverPointEquiv T (B sig rank m choice laws) p)).val := by
  letI := globalSectionsAlgebra T
  let e := normalizedSchemeMarkedTensorCoordinates T.left sig rank m choice
  let e' : LawfulMixedMarkedSchemeTensor sig rank m choice laws T ≃
      LawfulMixedMarkedCoordinates sig rank m choice laws Γ(T.left, ⊤) :=
    e.subtypeEquiv fun P => forall_congr' fun j =>
      MixedMarkedLaw.holds_iff_of_iso sig m
        (namedSchemeMarkedStructure_coordinateIso T.left sig rank m choice P) (laws j)
  let p' := mixedMarkedChartCoordinateEquiv sig rank m choice laws
    (specOverPointEquiv T (B sig rank m choice laws) p)
  exact congrArg Subtype.val (e'.apply_symm_apply p')

/-- The primitive coordinate of a chart point is the value of the
corresponding universal variable in the quotient. -/
theorem mixedMarkedChartPoint_primitive (p : T ⟶ chart sig rank m choice laws) (z : PrimitiveCoordinate sig rank) :
    PrimitiveCoefficients.valuesEquiv sig rank (mixedMarkedChartPointCoordinates sig rank m choice laws T p).1 z =
    letI := globalSectionsAlgebra T
    specOverPointEquiv T (B sig rank m choice laws) p
      ((quotient sig rank m choice laws) (X (Sum.inl z))) := by
  letI := globalSectionsAlgebra T
  rw [mixedMarkedChartPointCoordinates_algebra]
  let v := specOverPointEquiv T (B sig rank m choice laws) p
  let e := PrimitiveCoefficients.valuesEquiv (R := Γ(T.left, ⊤)) sig rank
  change e (e.symm (fun z => v (quotient sig rank m choice laws (X (Sum.inl z))))) z = _
  rw [Equiv.apply_symm_apply]

/-- A nonselected marking coordinate is the value of its original universal variable. -/
theorem mixedMarkedChartPoint_marking (p : T ⟶ chart sig rank m choice laws)
    (z : MarkingCoordinate sig rank m choice) :
    (mixedMarkedChartPointCoordinates sig rank m choice laws T p).2 z =
    letI := globalSectionsAlgebra T
    specOverPointEquiv T (B sig rank m choice laws) p
      ((quotient sig rank m choice laws) (X (Sum.inr z))) := by
  letI := globalSectionsAlgebra T
  rw [mixedMarkedChartPointCoordinates_algebra]
  rfl

variable {T} {T' : Over (Spec (CommRingCat.of R))}

/-- Primitive coefficients are natural along the actual global-sections maps of all test morphisms. -/
theorem mixedMarkedChartPoint_primitive_precomp (g : T' ⟶ T)
    (p : T ⟶ chart sig rank m choice laws) (z : PrimitiveCoordinate sig rank) :
    PrimitiveCoefficients.valuesEquiv sig rank (mixedMarkedChartPointCoordinates sig rank m choice laws T' (g ≫ p)).1 z =
      g.left.appTop.hom
        (PrimitiveCoefficients.valuesEquiv sig rank (mixedMarkedChartPointCoordinates sig rank m choice laws T p).1 z) := by
  letI := globalSectionsAlgebra T
  letI := globalSectionsAlgebra T'
  let e := quotient sig rank m choice laws (X (Sum.inl z))
  have direct := mixedMarkedChartPoint_primitive sig rank m choice laws T p z
  have composed := mixedMarkedChartPoint_primitive sig rank m choice laws T' (g ≫ p) z
  exact composed.trans ((AlgHom.congr_fun (specOverPointEquiv_precomp g p) e).trans
    (congrArg g.left.appTop.hom direct.symm))

/-- The nonselected marking coordinates commute with the same actual global-sections maps. -/
theorem mixedMarkedChartPoint_marking_precomp (g : T' ⟶ T)
    (p : T ⟶ chart sig rank m choice laws) (z : MarkingCoordinate sig rank m choice) :
    (mixedMarkedChartPointCoordinates sig rank m choice laws T' (g ≫ p)).2 z =
      g.left.appTop.hom ((mixedMarkedChartPointCoordinates sig rank m choice laws T p).2 z) := by
  letI := globalSectionsAlgebra T
  letI := globalSectionsAlgebra T'
  let e := quotient sig rank m choice laws (X (Sum.inr z))
  have direct := mixedMarkedChartPoint_marking sig rank m choice laws T p z
  have composed := mixedMarkedChartPoint_marking sig rank m choice laws T' (g ≫ p) z
  exact composed.trans ((AlgHom.congr_fun (specOverPointEquiv_precomp g p) e).trans
    (congrArg g.left.appTop.hom direct.symm))

end

end SHIGURE.RealizationFamilies
