import ResearchLean.AG.RelativeRepairComposition.W1SubdivisionRanges

/-!
# All original W1 minimal repair permissions survive subdivision

Both predicates use the complete independently specified native repair sets.
Candidate names are compared by their original-name bijection, for all selected
sets. The original actual-affine inverse and the actual signed obstruction give
the zero-empty and nonzero-two-singleton conclusions on the same full witness.
-/
namespace AAT.AG.RelativeRepairComposition.W1SubdivisionMinimalRanges
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine W1AffineInput W1Regions W1ActualRepairs W1FiniteCoefficients W1RelativeCoefficients
open W1OriginalObstruction W1CandidateColumns W1DualMinimalRanges W1SubdivisionInput W1SubdivisionRanges
attribute [local instance] Classical.propDecidable
attribute [local instance] Subdivision.LinearCoefficients.coefficientModules
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 4096

variable (x y : ZMod 3)
local notation "T" => originalTower true x y
local notation "F" => factors x y
local notation "Pn" => Subdivision.oldRegion geometry chosen fixedRegion chosen_not_P
local notation "Cn" => Subdivision.oldEdgeSet geometry chosen candidates
local notation "newFix" V => fixedEdgesForRange (ClosedRegion.edges (Pn)) (Cn) (OriginalRanges.allowed (Cn) V)

/-- Every complete selected original range has the same exact feasibility condition after subdivision. -/
theorem feasibility (S : Set candidates) :
    Nonempty (SupportedRepair (splitTower x y) (newFix (candidateNames '' S))) ↔ y-x = 0 ∨ S.Nonempty :=
  (Subdivision.MinimalRanges.repair_nonempty_iff (T) fixedRegion candidates chosen (F)
    chosen_not_P chosen_not_candidate S).trans
    ((native_range_iff x y S).trans (range_contains_iff x y S))

/-- Inclusion-minimal actual repair ranges agree on all complete original candidate permissions. -/
theorem minimal_iff_old_actual (S : Set candidates) :
    Minimal (fun V => Nonempty (SupportedRepair (splitTower x y) (newFix V))) (candidateNames '' S) ↔
    Minimal (fun V => Nonempty (RealRepairs true x y (OriginalRanges.allowed candidates V))) S :=
  (Subdivision.MinimalRanges.minimal_actual_repair_iff (T) fixedRegion candidates chosen (F)
    chosen_not_P chosen_not_candidate (original_linear true x y) candidates_outside (fixed_faces true x y) S).trans
    ((OriginalRangeClassification.minimal_repair_iff_range (k := ZMod 3) (T) fixedRegion candidates
      candidates_outside (original_linear true x y) (fixed_faces true x y) S).trans
      (minimal_actual_iff_range x y S).symm)

/-- At zero actual difference the empty original selection is still the unique minimal native repair range. -/
theorem minimal_zero (hd : y-x = 0) (S : Set candidates) :
    Minimal (fun V => Nonempty (SupportedRepair (splitTower x y) (newFix V))) (candidateNames '' S) ↔ S = ∅ :=
  (minimal_iff_old_actual x y S).trans (minimal_zero_iff x y hd S)

/-- At nonzero actual difference precisely the two distinct retained original singleton names are minimal. -/
theorem minimal_nonzero (hd : y-x ≠ 0) (S : Set candidates) :
    Minimal (fun V => Nonempty (SupportedRepair (splitTower x y) (newFix V))) (candidateNames '' S) ↔
      S = {candidateB} ∨ S = {candidateC} :=
  (minimal_iff_old_actual x y S).trans (minimal_nonzero_iff x y hd S)

end AAT.AG.RelativeRepairComposition.W1SubdivisionMinimalRanges
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W1SubdivisionMinimalRanges
