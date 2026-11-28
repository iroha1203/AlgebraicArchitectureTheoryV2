import Formal.SHIGURE.Part2.Marked.ChartRingRepresentation

/-! # Nonvacuous instances of normalized marked charts

The same rank-one free carrier over `ℤ`, singleton sort, nullary total
primitive, and written Law `primitive = 0` are used throughout. Assigning
the independent primitive coefficient zero or one gives the Law instance
pair. Replacing the actual marking by zero gives the normalization
counterexample, while preserving the carrier and primitive operation.

## Implementation notes

These examples use the actual multilinear operation supplied by
`dataOfAssignment`; the basis-value theorem detects the primitive value.
The chart ideal comparison connects the same instances to the universal
residual equations of Construction 6.4.
-/

namespace SHIGURE.RealizationFamilies.Marked.ChartExamples

open Module

noncomputable section

/-- A singleton sort with one genuine nullary total primitive. -/
def sectionSignature : Signature where
  SortType := Unit
  Total := Unit
  Rel := Empty
  Partial := Empty
  Quantity := Empty
  totalArity _ := ⟨[], ()⟩
  relInputs := Empty.elim
  partialArity := Empty.elim
  quantityArity := Empty.elim

/-- The single generator is selected as the rank-one carrier basis. -/
def singleChart : ChartIndex (sig := sectionSignature) (fun _ => 1) (fun _ => 1) :=
  fun _ => OrderEmbedding.ofStrictMono id (fun _ _ h => h)

/-- The same nonempty equation is tested for both coefficient assignments. -/
def vanishingSectionLaw : TensorLaw ℤ sectionSignature where
  source := .arguments []
  target := .sort ()
  left := .total ()
  right := .zero _ _

/-- A nonempty tensor-Law presentation with no polynomial Laws. -/
def vanishingSectionLaws : AffineLawPresentation ℤ sectionSignature where
  tensorIndex := Unit
  tensorLaw _ := vanishingSectionLaw
  polynomialIndex := Empty
  inputs := Empty.elim
  output := Empty.elim
  polynomialLaw i := nomatch i

/-- Assign the sole primitive coefficient on the normalized rank-one chart. -/
def assignedData (c : ℤ) :
    FreeMarkedData (sig := sectionSignature) ℤ (fun _ => 1) (fun _ => 1) :=
  dataOfAssignment ℤ singleChart (fun _ => c)

/-- The general specialization theorem supplies positive normalization
instances for every primitive coefficient, independently of the Law. -/
theorem assignedData_normalized (c : ℤ) : (assignedData c).IsNormalized singleChart :=
  dataOfAssignment_normalized ℤ singleChart (fun _ => c)

private theorem assignedData_primitive (c : ℤ)
    (x : ∀ i : TensorPosition ([] : List sectionSignature.SortType),
      (assignedData c).realization.carrier i.1) (b : Fin 1) :
    (assignedData c).realization.total () x b = c := by
  have empty : x = fun i => freeBasis (fun _ : sectionSignature.SortType => 1) ℤ i.1
      ((fun i : TensorPosition ([] : List sectionSignature.SortType) => nomatch i.2) i) := by
    funext i
    exact nomatch i.2
  rw [empty]
  exact operationOfCoefficients_basis (fun _ => 1) ℤ (sectionSignature.totalArity ())
    (fun _ _ => c) b (fun i => nomatch i.2)

/-- The actual tensor interpretation of the fixed Law detects precisely
the assigned primitive coefficient; no Law is stored in the datum. -/
theorem assignedData_satisfies_iff (c : ℤ) :
    (assignedData c).Satisfies vanishingSectionLaws (algebraMap ℤ ℤ) ↔ c = 0 := by
  constructor
  · intro h
    have law := h.1 ()
    change PiTensorProduct.lift ((assignedData c).realization.total ()) = 0 at law
    have value := LinearMap.congr_fun law
      (PiTensorProduct.tprod ℤ (fun i => nomatch i.2))
    rw [PiTensorProduct.lift.tprod] at value
    have coefficient := congrFun value (0 : Fin 1)
    rw [assignedData_primitive] at coefficient
    exact coefficient
  · intro zero
    constructor
    · intro l
      change PiTensorProduct.lift ((assignedData c).realization.total ()) = 0
      apply PiTensorProduct.ext
      apply MultilinearMap.ext
      intro x
      funext b
      change (PiTensorProduct.lift ((assignedData c).realization.total ()))
        (PiTensorProduct.tprod ℤ x) b = 0
      rw [PiTensorProduct.lift.tprod]
      exact (assignedData_primitive c x b).trans zero
    · intro l
      exact nomatch l

/-- Zero satisfies the same written Law in the normalized free chart. -/
theorem zeroAssignment_satisfies :
    (assignedData 0).Satisfies vanishingSectionLaws (algebraMap ℤ ℤ) :=
  (assignedData_satisfies_iff 0).mpr rfl

/-- One violates the written Law on the same carrier and normalized marking. -/
theorem oneAssignment_not_satisfies :
    ¬ (assignedData 1).Satisfies vanishingSectionLaws (algebraMap ℤ ℤ) :=
  fun h => Int.one_ne_zero ((assignedData_satisfies_iff 1).mp h)

/-- The general chart comparison tests the identical primitive assignment
by vanishing of its full universal residual ideal. -/
theorem assigned_ideal_vanishes_iff (c : ℤ) :
    chartLawIdeal (fun _ => 1) singleChart vanishingSectionLaws ≤
      RingHom.ker (MvPolynomial.aeval (fun _ : ChartVariable singleChart => c)).toRingHom ↔
        c = 0 :=
  (dataOfAssignment_satisfies_iff ℤ singleChart vanishingSectionLaws (fun _ => c)).symm.trans
    (assignedData_satisfies_iff c)

/-- The same free carrier and zero primitive, with an independently chosen
actual zero marking. Normalization is tested only afterwards. -/
def zeroMarkedData :
    FreeMarkedData (sig := sectionSignature) ℤ (fun _ => 1) (fun _ => 1) where
  realization := (assignedData 0).realization
  carrier_eq := (assignedData 0).carrier_eq
  marking _ := 0

/-- A zero actual marking cannot map the selected generator to a basis
vector in the nonzero rank-one integer carrier. -/
theorem zeroMarkedData_not_normalized : ¬ zeroMarkedData.IsNormalized singleChart := by
  intro normalized
  have value := congrArg
    (fun x => (zeroMarkedData.carrierBasis ()).repr x (0 : Fin 1))
    (normalized () (0 : Fin 1))
  have impossible : (0 : ℤ) = 1 := by
    simpa only [zeroMarkedData, LinearMap.zero_apply, map_zero, Basis.repr_self,
      Finsupp.single_eq_same] using value
  exact Int.zero_ne_one impossible

end

end SHIGURE.RealizationFamilies.Marked.ChartExamples
