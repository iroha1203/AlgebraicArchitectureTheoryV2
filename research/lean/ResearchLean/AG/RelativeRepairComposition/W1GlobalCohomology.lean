import ResearchLean.AG.RelativeRepairComposition.W1DualMinimalRanges
import ResearchLean.AG.RelativeRepairComposition.OriginalRangeCohomology
import ResearchLean.AG.RelativeRepairComposition.OriginalNativeRangeCohomology

/-!
# W1 full original face differential and the all-candidate second quotient

The always cokernel is the nonzero whole F3 quotient already constructed.
Allowing all original candidates makes the full original face differential
surjective. The same original all-column quotient and original H2 therefore
vanish, keeping their unchanged full face representatives.
-/
namespace AAT.AG.RelativeRepairComposition.W1GlobalCohomology
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine W1AffineInput W1AuthoredOperations W1Regions W1ActualRepairs W1FiniteCoefficients
open W1RelativeCoefficients W1OriginalObstruction W1CandidateColumns W1DualMinimalRanges
attribute [local instance] Classical.propDecidable
attribute [local instance] OriginalRangeQuotient.allEdgesDecidable
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000

variable (x y : ZMod 3)
local notation "M" => TowerPresentation.localCoefficients (OriginalTowerPresentation.toTower (originalTower true x y))
local notation "B" => OriginalRanges.column (k := ZMod 3) (M) fixedRegion candidates candidates_outside (original_linear true x y)

/-- Every full original relative face cochain is attained by the complete original d1, without a supplied image certificate. -/
theorem differential_surjective : Function.Surjective
    (FiniteCoefficients.differential1 (M) (original_linear true x y) ClosedRegion.all fixedRegion) := by
  intro c
  let u := faceCoordinates true x y c false
  let v := faceCoordinates true x y c true - u
  refine ⟨relativeCochain true x y u 0 0 v, ?_⟩
  apply (faceCoordinates true x y).injective
  funext f
  cases f
  · have hv := relative_d1_first true x y (relativeCochain true x y u 0 0 v)
    rw [FiniteCoefficients.differential1_eq] at hv
    rw [FiniteCoefficients.differential1_eq, hv, relativeCochain_value, relativeCochain_value]
    simp [correctionValue, geometry, name, edgeE, edgeA, edgeB, edgeC, u]
  · have hv := relative_d1_second_negative x y (relativeCochain true x y u 0 0 v)
    rw [FiniteCoefficients.differential1_eq] at hv
    rw [FiniteCoefficients.differential1_eq, hv, relativeCochain_value, relativeCochain_value, relativeCochain_value]
    simp [correctionValue, geometry, name, edgeE, edgeA, edgeB, edgeC, u, v]

/-- The full differential image is the whole original CP2, although the always image is only diagonal. -/
theorem differential_range_top :
    LinearMap.range (FiniteCoefficients.differential1 (M) (original_linear true x y)
      ClosedRegion.all fixedRegion) = ⊤ :=
  LinearMap.range_eq_top.mpr (differential_surjective x y)

/-- Every original quotient face representative becomes zero after all original candidate columns are admitted. -/
theorem all_candidate_face_class_zero (c : RelativeCover.C2 (M) ClosedRegion.all fixedRegion) :
    (NamedDual.ranges (B) Set.univ).mkQ
      (LinearInterface.q (OriginalColumns.D (k := ZMod 3) (M) fixedRegion candidates (original_linear true x y)) c) = 0 := by
  exact (Submodule.Quotient.mk_eq_zero _).mpr (by
    rw [nonempty_range_top x y Set.univ (show (Set.univ : Set candidates).Nonempty from ⟨candidateB, Set.mem_univ _⟩)]
    exact Submodule.mem_top)

/-- The same complete all-column second quotient is identified with original CP2 modulo full original d1. -/
noncomputable def secondQuotientEquivalence :=
  OriginalRangeQuotient.equivalence (k := ZMod 3) (M) fixedRegion candidates candidates_outside (original_linear true x y)

/-- The complete quotient equivalence keeps the same original full face representative. -/
theorem secondQuotient_value (c : RelativeCover.C2 (M) ClosedRegion.all fixedRegion) :
    secondQuotientEquivalence x y
      ((NamedDual.ranges (B) Set.univ).mkQ
        (LinearInterface.q (OriginalColumns.D (k := ZMod 3) (M) fixedRegion candidates (original_linear true x y)) c)) =
      (LinearMap.range (FiniteCoefficients.differential1 (M) (original_linear true x y)
        ClosedRegion.all fixedRegion)).mkQ c :=
  OriginalRangeQuotient.equivalence_value (k := ZMod 3) (M) fixedRegion candidates candidates_outside (original_linear true x y) c

/-- Every class in the actual full relative H2 is zero by a restored complete original edge cochain. -/
theorem h2_zero (h : CoverCohomology.H2 (M) fixedRegion ClosedRegion.all) : h = 0 := by
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk'_surjective
    (CoverCohomology.boundary2 (M) fixedRegion ClosedRegion.all).range h
  apply (CoverCohomology.h2_eq_zero_iff (M) fixedRegion ClosedRegion.all z).mpr
  obtain ⟨a, ha⟩ := differential_surjective x y z.1
  refine ⟨a, Subtype.ext ?_⟩
  rw [FiniteCoefficients.differential1_eq] at ha
  exact ha

/-- Every class of the full original-K relative H2 is zero under the accepted complete original-index comparison. -/
theorem original_h2_zero (h : RelativeComplex.H2 (M) fixedRegion ∅ ∅) : h = 0 := by
  have hv := h2_zero x y ((OriginalCohomology.familySecondIso (M) fixedRegion).inv h)
  have hh := congrArg (OriginalCohomology.familySecondIso (M) fixedRegion).hom hv
  simpa only [Iso.inv_hom_id_apply, map_zero] using hh

end AAT.AG.RelativeRepairComposition.W1GlobalCohomology
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W1GlobalCohomology
