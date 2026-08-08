import ResearchLean.AG.ResolutionInvariance.CanonicalInadequateHiddenClass
import ResearchLean.AG.ResolutionInvariance.ResolutionInvarianceConditions
import Formal.Util.AssertStandardAxioms

/-!
# An adequate failure of the fixed resolution-invariance condition

This module realizes G-104 claim (iv)(c) on the current canonical K0/K1
surface.  It reuses the exact `Factors` subtype from Cycle 27 as the law family,
so both readings are adequate.  The two distinct fine parallel edges map to the
same coarse edge, directly violating current C5 and therefore the full fixed
condition C.  On the same data, the actual generated comparison map is not
surjective and hence not bijective.

No historical custom complex, selected law list, arbitrary comparison map, or
nonisomorphism certificate is used.  The face-free fixture is only the required
claim (iv)(c) counterexample and is not counted as the claim (v) firing witness.
-/

noncomputable section

namespace AAT.AG.ResolutionInvariance

open CanonicalResolution

namespace AdequateConditionCFailure

open CanonicalInadequateHiddenClass

/-- The exact retained family still contains a genuinely nonconstant law. -/
theorem retainedLaw_nonconstant :
    ∃ left right : Source,
      retainedLaws.eval retainedLaw left ≠
        retainedLaws.eval retainedLaw right := by
  simpa [retainedLaws, retainedLaw] using factorLaw_nonconstant

/-- The two distinct fine edges have the same declared coarse edge image. -/
theorem parallel_edge_lifts :
    (0 : fineNerve.EdgeComponent) ≠ 1 ∧
      nerveMorphism.edgeMap 0 = some PUnit.unit ∧
      nerveMorphism.edgeMap 1 = some PUnit.unit := by
  exact ⟨by decide, rfl, rfl⟩

/-- The duplicate declared lifts violate the current whole-nerve condition C5. -/
theorem conditionC5_not : ¬ nerveMorphism.ConditionC5 := by
  intro hC5
  rcases parallel_edge_lifts with ⟨hdistinct, hzero, hone⟩
  exact hdistinct (hC5 PUnit.unit 0 1 hzero hone)

/-- Failure of C5 rules out the complete current C0--C6 package. -/
theorem conditionC_not :
    ¬ nerveMorphism.ConditionC retainedLaws coarseRetainedAdequate
      retainedLawsFineAdequate := by
  intro hC
  exact conditionC5_not hC.c5

/-- The current generated comparison map is not surjective on actual `H^1`. -/
theorem generatedComparisonH1Map_not_surjective :
    ¬ Function.Surjective
      (nerveMorphism.generatedComparisonH1Map retainedLaws
        coarseRetainedAdequate retainedLawsFineAdequate) := by
  simpa [retainedComparisonH1Map] using retainedComparisonH1Map_not_surjective

/-- The current generated comparison map is consequently not bijective. -/
theorem generatedComparisonH1Map_not_bijective :
    ¬ Function.Bijective
      (nerveMorphism.generatedComparisonH1Map retainedLaws
        coarseRetainedAdequate retainedLawsFineAdequate) := by
  intro hbijective
  exact generatedComparisonH1Map_not_surjective hbijective.2

/--
G-104 claim (iv)(c): an adequate pair violates C5 and the fixed condition C,
and its actual canonical comparison map is not an `H^1` isomorphism.
-/
theorem fixed_claim_iv_c :
    retainedLaws.Adequate coarseReading ∧
      retainedLaws.Adequate fineReading ∧
      coarseReading.CoarserThan fineReading ∧
      (¬ Function.Injective
        (comparisonFactor coarseReading fineReading coarse_coarser_fine)) ∧
      (∃ left right : Source,
        retainedLaws.eval retainedLaw left ≠
          retainedLaws.eval retainedLaw right) ∧
      coarseDiagnosticComplex.H1Zero ∧
      retainedFineClass ≠ 0 ∧
      (¬ nerveMorphism.ConditionC5) ∧
      (¬ nerveMorphism.ConditionC retainedLaws coarseRetainedAdequate
        retainedLawsFineAdequate) ∧
      (¬ Function.Bijective
        (nerveMorphism.generatedComparisonH1Map retainedLaws
          coarseRetainedAdequate retainedLawsFineAdequate)) :=
  ⟨coarseRetainedAdequate, retainedLawsFineAdequate, coarse_coarser_fine,
    comparisonFactor_not_injective, retainedLaw_nonconstant,
    coarseFactorsDiagnosticH1Zero, retainedFineClass_ne_zero,
    conditionC5_not, conditionC_not, generatedComparisonH1Map_not_bijective⟩

end AdequateConditionCFailure

end AAT.AG.ResolutionInvariance

#assert_standard_axioms_only AAT.AG.ResolutionInvariance.AdequateConditionCFailure
