import Formal.SHIGURE.Part2.Realizations.MixedMarkedLawChart
import Formal.SHIGURE.Part2.Realizations.NamedMarkingSpecialization
import Formal.SHIGURE.Part2.Realizations.NamedSchemeMarkedStructure
import Formal.SHIGURE.Part2.Realizations.TensorExpressionIso

/-! # The full Law chart and actual named realizations over each test scheme -/

namespace SHIGURE.RealizationFamilies

open AlgebraicGeometry CategoryTheory MvPolynomial SHIGURE.TensorRealization

noncomputable section

universe u

variable {R : Type u} [CommRing R] (sig : Signature.{u}) (rank m : sig.SortType → ℕ)
  (choice : MarkedBasisChoice sig rank m)
  {J : Type u} (laws : J → MixedMarkedLaw R sig m)

variable {S : Type u} [CommRing S] [Algebra R S]

/-- Every required interpretation of the equation is invariant under the
actual isomorphisms preserving all operations and named markings. -/
theorem MixedMarkedLaw.holds_iff_of_iso {A B : TensorStructure S (markingSignature sig m)}
    (e : A ≅ B) (l : MixedMarkedLaw R sig m) :
    l.holds sig m A ↔ l.holds sig m B := by
  cases l with
  | tensor l => exact tensorLaw_holds_iff_of_iso e (l.mapScalars (algebraMap R S))
  | polynomial l => exact l.holds_iff_of_iso (algebraMap R S) e

/-- The normalized realization of a coordinate pair uses the original
primitive coefficients and the entries of its actual marking matrices. -/
def namedMarkedCoordinateTensor (p : MarkedCoordinatePair sig rank m choice S) :
    TensorStructure S (markingSignature sig m) :=
  withMarkingOperations sig m (p.1.toTensor sig rank)
    (fun s j i => markingMatrix sig rank m choice p.2 s i j)

/-- The lawful coordinates are the complete chart's actual primitive and marking data. -/
abbrev LawfulMixedMarkedCoordinates (S : Type u) [CommRing S] [Algebra R S] :=
  {p : MarkedCoordinatePair sig rank m choice S //
    ∀ j, (laws j).holds sig m (namedMarkedCoordinateTensor sig rank m choice p)}

/-- Algebra maps into any test ring correspond to the original marked
coordinates satisfying all required Laws. -/
def mixedMarkedChartCoordinateEquiv :
    (mixedMarkedChartAlgebra sig rank m choice laws →ₐ[R] S) ≃
      LawfulMixedMarkedCoordinates sig rank m choice laws S := by
  let E := (markedAmbientCoordinateEquiv (R := R) (S := S) sig rank m choice).symm
  refine (mixedMarkedChartAlgHomEquiv sig rank m choice laws).trans
    ((E.subtypeEquiv (fun p => ?_)).symm)
  let A := MvPolynomial (MarkedChartVariable sig rank m choice) R
  let q := markedChartEvaluator (R := R) sig rank m choice p.1 p.2
  letI : Algebra A S := q.toRingHom.toAlgebra
  change (∀ j, (laws j).holds sig m (namedMarkedCoordinateTensor sig rank m choice p)) ↔
    ∀ j, (laws j).holds sig m (extendStructure A S (universalNamedMarkedTensor sig m rank choice))
  let actual := universalNamedMarkedTensor_specializationIso (R := R) sig rank m choice p.1 p.2
  exact forall_congr' fun j => (MixedMarkedLaw.holds_iff_of_iso sig m actual (laws j)).symm

variable (T : Over (Spec (CommRingCat.of R)))

/-- Test objects in this chart are the actual named marked sheaf morphisms
satisfying all written tensor and polynomial Laws on the global basis. -/
abbrev LawfulMixedMarkedSchemeTensor :=
  letI := globalSectionsAlgebra T
  {P : NormalizedSchemeMarkedTensor T.left sig rank m choice //
    ∀ j, (laws j).holds sig m (namedSchemeMarkedStructure T.left sig rank m choice P)}

/-- Equation (6.2) represents actual marked realizations in the selected
global sheaf basis on every relative test scheme, with the Laws interpreted
on the resulting global section structure. -/
def mixedMarkedChartRealizationEquiv :
    (T ⟶ mixedMarkedChartScheme sig rank m choice laws) ≃
      LawfulMixedMarkedSchemeTensor sig rank m choice laws T := by
  letI := globalSectionsAlgebra T
  let reading := normalizedSchemeMarkedTensorCoordinates T.left sig rank m choice
  let lawful : LawfulMixedMarkedSchemeTensor sig rank m choice laws T ≃
      LawfulMixedMarkedCoordinates sig rank m choice laws Γ(T.left, ⊤) :=
    reading.subtypeEquiv fun P => forall_congr' fun j =>
      MixedMarkedLaw.holds_iff_of_iso sig m
        (namedSchemeMarkedStructure_coordinateIso T.left sig rank m choice P) (laws j)
  exact (specOverPointEquiv T (mixedMarkedChartAlgebra sig rank m choice laws)).trans
    ((mixedMarkedChartCoordinateEquiv sig rank m choice laws).trans lawful.symm)

end

end SHIGURE.RealizationFamilies
