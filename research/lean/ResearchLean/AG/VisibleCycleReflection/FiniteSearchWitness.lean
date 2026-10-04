import ResearchLean.AG.VisibleCycleReflection.ActualSearchCounterinput
import ResearchLean.AG.VisibleCycleReflection.FiniteValidationWitness
import Formal.Util.AssertStandardAxioms

/-!
# Runtime and actual-input witnesses for the finite reflection procedure

## Implementation notes

The one-point table exercises successful validation and reflection. The valid
nonreflecting triangle exercises generated failure data, including its actual
zero-diagnostic and nonzero existing obstruction. Invalid tables are rejected
before reflection scanning. These are cycle witnesses; the prescribed W1–W3
remain separate fixed obligations.
-/

namespace AAT.AG.VisibleCycleReflection.FiniteSearchWitness
open FiniteValidationWitness FiniteInputTable

/-- The positive checked table has no failing label/edge pair. -/
theorem onePoint_search_success : onePointTable.reflectsTest = true := by decide

/-- The raw B3 predicate holds on the positive checked table. -/
theorem onePoint_raw_nonbridge : onePointTable.RawNonbridgeVisible :=
  onePointTable.searchFailure_none_iff.mp (by decide)

/-- The actual B2 inclusions are surjective for the positive checked table. -/
theorem onePoint_actual_homology : onePointTable.ActualHomologySurjective onePointTable_valid :=
  (onePointTable.reflectsTest_iff_actual_homology _).mp onePoint_search_success

/-- The combined procedure returns success on the positive checked table. -/
theorem onePoint_checked_success : onePointTable.checkAndSearch = .success :=
  (onePointTable.checkAndSearch_success_iff onePointTable_valid).mpr onePoint_search_success

/-- The valid nonreflecting triangle produces a finite failure. -/
theorem triangle_failure_generated : nonreflectingTriangle.searchFailure.isSome = true := by decide

/-- The failure object is extracted by evaluation from the actual finite scan, without choice. -/
def triangleFailure : nonreflectingTriangle.SearchFailure :=
  nonreflectingTriangle.searchFailure.get triangle_failure_generated

/-- The retained failure is exactly the output of the finite scan. -/
theorem triangleFailure_search : nonreflectingTriangle.searchFailure = some triangleFailure := by
  exact (Option.some_get _).symm

/-- The actual serialized failure has label1, edge01 and the generated once-through cycle 1,0,2,1. -/
theorem triangleFailure_codes :
    triangleFailure.label.val = ⟨(0 : Fin 1),(1 : Fin 2)⟩ ∧ triangleFailure.edge.val = ((0 : Fin 3),(1 : Fin 3)) ∧
      triangleFailure.cycle.support = [(1 : Fin 3),0,2,1] := by decide

/-- The raw nonbridge visibility condition fails on the same valid triangle. -/
theorem triangle_not_raw_nonbridge : ¬nonreflectingTriangle.RawNonbridgeVisible := by
  intro h
  have hz := nonreflectingTriangle.searchFailure_none_iff.mpr h
  rw [triangleFailure_search] at hz
  contradiction

/-- The actual B2 inclusions fail on the same valid triangle. -/
theorem triangle_not_actual_homology :
    ¬nonreflectingTriangle.ActualHomologySurjective nonreflectingTriangle_valid := by
  intro h
  have hs := (nonreflectingTriangle.reflectsTest_iff_actual_homology _).mpr h
  have hn : nonreflectingTriangle.reflectsTest = false := by decide
  rw [hn] at hs
  contradiction

/-- The combined procedure returns the very scan-generated failure on the valid triangle. -/
theorem triangle_checked_failure :
    nonreflectingTriangle.checkAndSearch = .failure triangleFailure :=
  (nonreflectingTriangle.checkAndSearch_failure_iff nonreflectingTriangle_valid _).mpr triangleFailure_search

/-- Actual Cech input decoding of the generated failure has zero diagnostic and nonzero existing class. -/
theorem triangle_actual_failure :
    (SearchFailure.actualInput nonreflectingTriangle triangleFailure nonreflectingTriangle_valid).diagnosticMismatch
      (nonreflectingTriangle.actualAdequate nonreflectingTriangle_valid) = 0 ∧
    (SearchFailure.actualInput nonreflectingTriangle triangleFailure nonreflectingTriangle_valid).existingDescentAdditiveClass ≠ 0 :=
  ⟨(nonreflectingTriangle.checkAndSearch_actual_failure _ _ triangle_checked_failure).2.1,
    (nonreflectingTriangle.checkAndSearch_actual_failure _ _ triangle_checked_failure).2.2.2⟩

/-- A missing topology column is rejected by the combined finite procedure. -/
theorem missingOpens_checked_invalid : missingOpens.checkAndSearch = .invalid :=
  missingOpens.checkAndSearch_invalid_iff.mpr ((missingOpens.validate_false_iff).mp (by decide))

/-- Missing primitive Rq is rejected before any reflection result is returned. -/
theorem missingRelation_checked_invalid : missingPrimitiveRelation.checkAndSearch = .invalid :=
  missingPrimitiveRelation.checkAndSearch_invalid_iff.mpr
    ((missingPrimitiveRelation.validate_false_iff).mp (by decide))

end AAT.AG.VisibleCycleReflection.FiniteSearchWitness
#assert_standard_axioms_only AAT.AG.VisibleCycleReflection.FiniteSearchWitness
