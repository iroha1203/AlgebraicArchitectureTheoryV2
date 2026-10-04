import ResearchLean.AG.VisibleCycleReflection.WitnessRepair
import ResearchLean.AG.VisibleCycleReflection.WitnessCycles
import Formal.Util.AssertStandardAxioms

/-!
# W3: an actual forest repair with no visible label-one edge

## Implementation notes

Both actual intersections are bridges. The table's reflection test succeeds
for all transitions and states, despite label one having only an isolated
visible vertex. The original n=(0,0,u1) chart sections correct the actual
single-edge 12 transition and glue through the same AAT state sheaf.
Replacing the specified transition by zero was rejected because the forest
example must retain a nonzero original mismatch despite no visible label-one edge.
-/

noncomputable section
namespace AAT.AG.VisibleCycleReflection.WitnessThree
open WitnessInputs FiniteInputTable CanonicalResolution ResolutionInvariance ObstructionDiagnosticBridge
/-- Original generated label one of the two-source identity-reading input. -/
def labelOne : LawValueLabel three.laws := LawValueLabel.ofSource three.laws (0 : Fin 1) (1 : Fin 2)
/-- Original primitive quotient basis for label one. -/
def u1 : (three.actualPresentation three_valid).PresentationGroup :=
  labelBasis _ (three.actualReflectionCondition three_valid) labelOne
/-- The prescribed original integer correction values n=(0,0,u1). -/
def chartValues : three.Chart → (three.actualPresentation three_valid).PresentationGroup := ![0,0,u1]
/-- Original actual chart sections of the prescribed integer correction. -/
def correction := three.chartCochain three_valid chartValues
/-- Actual xi=d0n and zero local state, retaining the original primitive coefficient sheaf. -/
def input : three.ActualLocalData three_valid := three.chartDifferenceInput three_valid chartValues
/-- The prescribed selected edge is the original 12 intersection cell. -/
def edge12 : three.RawEdge := ⟨(1,2),by decide⟩

/-- The forest table's complete ordered edge table has only 01 and 12. -/
theorem raw_edge_pairs (e : three.RawEdge) : e.val = (0,1) ∨ e.val = (1,2) := by
  have h : ∀ e : three.RawEdge, e.val = (0,1) ∨ e.val = (1,2) := by decide
  exact h e
/-- The explicit chart differences restore exactly the specified actual 12 single-edge input. -/
theorem input_single_edge :
    letI : TopologicalSpace three.Point := three.actualTopology three_valid
    input = (three.actualGeometry three_valid).singleEdgeData (three.actualTarget three_valid)
      (three.actualTarget_nonempty three_valid) (three.actualPresentation three_valid)
      (three.actualReflectionCondition three_valid) labelOne (three.actualEdge three_valid edge12) := by
  letI : TopologicalSpace three.Point := three.actualTopology three_valid
  apply three.chartDifferenceInput_eq_singleEdgeData three_valid chartValues
  intro e
  change chartValues e.val.2 - chartValues e.val.1 = _
  have hp : e.val = ((0 : Fin 3),1) ∨ e.val = ((1 : Fin 3),2) := by
    rw [← three.actualGraphRawEdgeEquiv_val three_valid e]
    exact raw_edge_pairs _
  have heq : e = three.actualEdge three_valid edge12 ↔ e.val = ((1 : Fin 3),2) := by
    change e = three.actualEdge three_valid edge12 ↔ e.val = edge12.val
    rw [← three.actualEdge_val three_valid edge12]
    exact Subtype.ext_iff
  rcases hp with hp | hp
  · simp [heq,hp,chartValues]
  · simp [heq,hp,chartValues,u1]

/-- The specified actual transition is zero on 01 and u1 on 12. -/
theorem transition_values :
    letI : TopologicalSpace three.Point := three.actualTopology three_valid
    ∀ e : Graph.Edge (three.actualGeometry three_valid).graph,
      (three.actualPresentation three_valid).faceEmptyCechCochain1Equiv _ input.transition
        ((three.actualGeometry three_valid).graphEdgeEquiv.symm e) =
          if e.val = ((1 : Fin 3),2) then u1 else 0 := by
  letI : TopologicalSpace three.Point := three.actualTopology three_valid
  intro e
  rw [input_single_edge,GeometricCover.singleEdgeData_transition_value]
  have heq : e = three.actualEdge three_valid edge12 ↔ e.val = ((1 : Fin 3),2) := by
    change e = three.actualEdge three_valid edge12 ↔ e.val = edge12.val
    rw [← three.actualEdge_val three_valid edge12]
    exact Subtype.ext_iff
  simp only [heq,u1]

/-- The actual state is identically zero. -/
theorem state_zero : input.localState = 0 := rfl
/-- Both original edges are bridges according to the finite deleted-path test. -/
theorem bridges : ∀ e : three.RawEdge, three.bridgeTest e = true := by decide
/-- The all-label finite reflection test succeeds on the actual forest table. -/
theorem finite_success : three.reflectsTest = true := by decide
/-- C returns success on the same valid table. -/
theorem checked_success : three.checkAndSearch = .success :=
  (three.checkAndSearch_success_iff three_valid).mpr finite_success
/-- All actual-input B1, B2, B3 statements hold, including the label with no visible edge. -/
theorem all_input_reflection : three.ActualReflects three_valid ∧
    three.ActualHomologySurjective three_valid ∧ three.ActualNonbridgeVisible three_valid :=
  (three.checkAndSearch_actual_success three_valid).mp checked_success
/-- The exact prescribed n is an integer correction of the same actual mismatch. -/
theorem correction_equation :
    letI : TopologicalSpace three.Point := three.actualTopology three_valid
    ((three.actualPresentation three_valid).faceEmptyCechComplex _).d 0 correction = input.actualMismatch :=
  three.chartDifferenceInput_correction three_valid chartValues
/-- The original chart section normalization recovers exactly n=(0,0,u1). -/
theorem correction_values :
    letI : TopologicalSpace three.Point := three.actualTopology three_valid
    (three.actualPresentation three_valid).faceEmptyCechCochain0Equiv _ correction = chartValues :=
  three.chartCochain_values three_valid chartValues
/-- The nonzero basis transition yields a nonzero actual mismatch on edge 12. -/
theorem mismatch_nonzero : input.actualMismatch ≠ 0 := by
  letI : TopologicalSpace three.Point := three.actualTopology three_valid
  intro hz
  have hzero : input.transition = 0 := by
    change (three.chartDifferenceInput three_valid chartValues).actualMismatch = 0 at hz
    rw [three.chartDifferenceInput_mismatch] at hz
    exact hz
  have ht := transition_values (three.actualEdge three_valid edge12)
  rw [hzero,map_zero,three.actualEdge_val] at ht
  have hu : u1 = 0 := by simpa [edge12] using ht.symm
  exact labelBasis_ne_zero _ (three.actualReflectionCondition three_valid) labelOne hu
/-- Label one's original 12 edge is invisible in the actual target-supported nerve. -/
theorem edge_invisible :
    letI : TopologicalSpace three.Point := three.actualTopology three_valid
    three.actualEdge three_valid edge12 ∉ (three.actualGeometry three_valid).visibleEdgeSet
      (three.actualTarget three_valid) (three.actualTarget_nonempty three_valid)
      (three.actualAdequate three_valid) labelOne := by
  letI : TopologicalSpace three.Point := three.actualTopology three_valid
  rw [← three.edgeVisible_iff_actual,three.actualEdge_raw]
  change ¬three.EdgeVisible ⟨(0 : Fin 1),(1 : Fin 2)⟩ ((1 : Fin 3),2)
  decide
/-- The independent diagnostic cochain vanishes even though the actual mismatch is nonzero. -/
theorem diagnostic_cochain_zero : input.diagnosticMismatch (three.actualAdequate three_valid) = 0 := by
  letI : TopologicalSpace three.Point := three.actualTopology three_valid
  rw [input_single_edge]
  exact (three.actualGeometry three_valid).singleEdgeData_diagnostic_mismatch_zero _ _ _ _ _ _ _ edge_invisible
/-- The original existing descent obstruction class of the repaired input is zero. -/
theorem existing_zero : input.existingDescentAdditiveClass = 0 :=
  three.chartDifferenceInput_existing_zero three_valid chartValues
/-- The independent diagnostic class also vanishes on this same real nonzero transition input. -/
theorem diagnostic_zero : input.diagnosticClass (three.actualAdequate three_valid) = 0 :=
  input.diagnosticClass_zero_of_mismatch_zero _ diagnostic_cochain_zero

/-- The prescribed original p-n sections have an actual unique AAT gluing. -/
theorem gluing : three.ActualCorrectedGluing three_valid input correction :=
  three.chartDifferenceInput_gluing three_valid chartValues

/-- A applies to this same original actual input for every generated label. -/
theorem comparison (l : LawValueLabel three.laws) :
    letI : TopologicalSpace three.Point := three.actualTopology three_valid
    (DirectSum.linearEquivFunOnFintype ℚ (LawValueLabel three.laws)
      (fun a => VisibleGraphH1 (three.actualNerve three_valid) (three.actualAdequate three_valid) a)
      (diagnosticVisibleH1Equiv (three.actualNerve three_valid) (three.actualAdequate three_valid)
        (input.diagnosticClass (three.actualAdequate three_valid)))) l =
      rationalRestrictionH1 (three.actualNerve three_valid) (three.actualAdequate three_valid) l
        (integerToRationalH1 (three.actualNerve three_valid).nerve (LawValueLabel three.laws)
          (actualIntegralH1Equiv (three.actualPresentation three_valid)
            ((three.actualGeometry three_valid).actualCechCover (three.actualPresentation three_valid)
              (three.actualTarget three_valid) (three.actualTarget_nonempty three_valid)) (three.actualReflectionCondition three_valid)
            input.existingDescentAdditiveClass)) :=
  three.actual_input_factorization three_valid input l

end AAT.AG.VisibleCycleReflection.WitnessThree
#assert_standard_axioms_only AAT.AG.VisibleCycleReflection.WitnessThree
