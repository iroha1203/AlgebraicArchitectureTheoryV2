import ResearchLean.AG.RelativeRepairComposition.W1OriginalObstruction

/-!
# Original W1 candidate columns in the full actual cokernel

## Implementation notes

Each column inserts the whole original terminal kernel at its original b or c
name into the same actual relative d1. Its quotient reading is derived from
the full always cokernel, retaining both candidates even though their quotient
columns agree. No candidate representative or separation certificate is input.
-/
namespace AAT.AG.RelativeRepairComposition.W1CandidateColumns
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine W1AffineInput W1Regions W1ActualRepairs
open W1FiniteCoefficients W1RelativeCoefficients W1OriginalObstruction
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000

variable (x y : ZMod 3)
local notation "M" => TowerPresentation.localCoefficients
  (OriginalTowerPresentation.toTower (originalTower true x y))

/-- The complete original candidate b retains its entire terminal coefficient space. -/
def candidateB : candidates := ⟨name edgeB, Or.inl rfl⟩

/-- The complete original candidate c retains its distinct original name and entire terminal coefficient space. -/
def candidateC : candidates := ⟨name edgeC, Or.inr rfl⟩

/-- The original b,c names remain distinct even though their derived quotient columns coincide. -/
theorem candidateB_ne_candidateC : candidateB ≠ candidateC := by
  intro he
  have hv := congrArg (fun e : candidates => e.1.2.2) he
  change (2 : Fin 6) = 3 at hv
  exact (by decide : (2 : Fin 6) ≠ 3) hv

/-- Candidate restoration keeps the full original value at every same original candidate name. -/
theorem candidate_coordinate (values : OriginalColumns.CandidateValues (M) candidates) (e : candidates) :
    edgeCoordinate true x y
        (OriginalColumns.candidateCochain (k := ZMod 3) (M) fixedRegion candidates candidates_outside values) e.1 =
      kernelCoordinate true x y e.1.2.1 (values e) := by
  rw [edgeCoordinate, OriginalColumns.candidate_value]

/-- Candidate restoration is zero at every noncandidate original name, including the original shared always edge. -/
theorem noncandidate_coordinate (values : OriginalColumns.CandidateValues (M) candidates)
    (e : EdgeName (K := geometry)) (he : e ∉ candidates) :
    edgeCoordinate true x y
        (OriginalColumns.candidateCochain (k := ZMod 3) (M) fixedRegion candidates candidates_outside values) e = 0 := by
  rw [edgeCoordinate, OriginalColumns.noncandidate_value (k := ZMod 3) (M)
    fixedRegion candidates candidates_outside values e he, map_zero]

/-- The first original relative face reads precisely the whole candidate b value. -/
theorem candidate_d1_first (values : OriginalColumns.CandidateValues (M) candidates) :
    faceCoordinates true x y
        (FiniteCoefficients.differential1 (M) (original_linear true x y) ClosedRegion.all fixedRegion
          (OriginalColumns.candidateCochain (k := ZMod 3) (M) fixedRegion candidates candidates_outside values)) false =
      kernelCoordinate true x y () (values candidateB) := by
  rw [relative_d1_first, noncandidate_coordinate x y values (name edgeE)
    (by simp [geometry, candidates, name, edgeE, edgeB, edgeC]), zero_add]
  exact candidate_coordinate x y values candidateB

/-- The complete negative second authored face reads minus the whole b value plus the whole c value. -/
theorem candidate_d1_second (values : OriginalColumns.CandidateValues (M) candidates) :
    faceCoordinates true x y
        (FiniteCoefficients.differential1 (M) (original_linear true x y) ClosedRegion.all fixedRegion
          (OriginalColumns.candidateCochain (k := ZMod 3) (M) fixedRegion candidates candidates_outside values)) true =
      -kernelCoordinate true x y () (values candidateB) + kernelCoordinate true x y () (values candidateC) := by
  rw [relative_d1_second_negative, noncandidate_coordinate x y values (name edgeE)
    (by simp [geometry, candidates, name, edgeE, edgeB, edgeC]), zero_sub]
  have hb := candidate_coordinate x y values candidateB
  have hc := candidate_coordinate x y values candidateC
  change edgeCoordinate true x y
    (OriginalColumns.candidateCochain (k := ZMod 3) (M) fixedRegion candidates candidates_outside values)
    (name edgeB) = kernelCoordinate true x y () (values candidateB) at hb
  change edgeCoordinate true x y
    (OriginalColumns.candidateCochain (k := ZMod 3) (M) fixedRegion candidates candidates_outside values)
    (name edgeC) = kernelCoordinate true x y () (values candidateC) at hc
  rw [hb, hc]

/-- Each original full candidate column's actual quotient reading is derived from the original two face values. -/
theorem column_reading (e : candidates) (a : (M).A e.1.2.1) :
    obstructionCoordinate x y
        (OriginalRanges.column (k := ZMod 3) (M) fixedRegion candidates candidates_outside
          (original_linear true x y) e a) =
      -kernelCoordinate true x y ()
        ((LinearMap.single (ZMod 3) (fun e : candidates => (M).A e.1.2.1) e a) candidateB) +
      kernelCoordinate true x y ()
        ((LinearMap.single (ZMod 3) (fun e : candidates => (M).A e.1.2.1) e a) candidateC) -
      kernelCoordinate true x y ()
        ((LinearMap.single (ZMod 3) (fun e : candidates => (M).A e.1.2.1) e a) candidateB) := by
  let values := LinearMap.single (ZMod 3) (fun e : candidates => (M).A e.1.2.1) e a
  have hf := candidate_d1_first x y values
  have hs := candidate_d1_second x y values
  rw [FiniteCoefficients.differential1_eq] at hf hs
  rw [OriginalRanges.column_apply, obstructionCoordinate_q, obstructionReading_value,
    OriginalColumns.column_apply, FiniteCoefficients.differential1_eq, hf, hs]

/-- Original b's complete quotient column is the full coefficient identity, using characteristic three after its transported minus sign. -/
theorem b_column_coordinate (a : (M).A ()) :
    obstructionCoordinate x y
        (OriginalRanges.column (k := ZMod 3) (M) fixedRegion candidates candidates_outside
          (original_linear true x y) candidateB a) = kernelCoordinate true x y () a := by
  rw [column_reading]
  simp only [LinearMap.single_apply, Pi.single_eq_same,
    Pi.single_eq_of_ne candidateB_ne_candidateC.symm, map_zero, add_zero]
  have ht : (3 : ZMod 3) * kernelCoordinate true x y () a = 0 := by
    rw [show (3 : ZMod 3) = 0 by decide, zero_mul]
  linear_combination -ht

/-- Original c's complete quotient column is the same full coefficient identity at its own original name. -/
theorem c_column_coordinate (a : (M).A ()) :
    obstructionCoordinate x y
        (OriginalRanges.column (k := ZMod 3) (M) fixedRegion candidates candidates_outside
          (original_linear true x y) candidateC a) = kernelCoordinate true x y () a := by
  rw [column_reading]
  simp only [LinearMap.single_apply, Pi.single_eq_same,
    Pi.single_eq_of_ne candidateB_ne_candidateC, map_zero, neg_zero, zero_add, sub_zero]

/-- The actual original b column covers the whole original always cokernel. -/
theorem b_column_surjective : Function.Surjective
    (OriginalRanges.column (k := ZMod 3) (M) fixedRegion candidates candidates_outside
      (original_linear true x y) candidateB) := by
  intro o
  refine ⟨(kernelCoordinate true x y ()).symm (obstructionCoordinate x y o), ?_⟩
  apply (obstructionCoordinate x y).injective
  rw [b_column_coordinate, LinearEquiv.apply_symm_apply]

/-- The distinct original c column also covers the whole original always cokernel. -/
theorem c_column_surjective : Function.Surjective
    (OriginalRanges.column (k := ZMod 3) (M) fixedRegion candidates candidates_outside
      (original_linear true x y) candidateC) := by
  intro o
  refine ⟨(kernelCoordinate true x y ()).symm (obstructionCoordinate x y o), ?_⟩
  apply (obstructionCoordinate x y).injective
  rw [c_column_coordinate, LinearEquiv.apply_symm_apply]

end AAT.AG.RelativeRepairComposition.W1CandidateColumns
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W1CandidateColumns
