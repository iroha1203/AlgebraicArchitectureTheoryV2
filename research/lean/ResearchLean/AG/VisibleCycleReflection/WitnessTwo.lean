import ResearchLean.AG.VisibleCycleReflection.WitnessCycles
import Formal.Util.AssertStandardAxioms

/-!
# W2: the specified invisible 34 transition on two actual triangles

## Implementation notes

The finite scan chooses label one and edge 34 before the other invisible edges.
Its full serialized integer input is decoded into the original primitive actual
Cech sections. The manually prescribed 0,3,4,0 cycle has the positive basis
period; the computed cycle has the opposite orientation and nonzero period.
-/

noncomputable section
namespace AAT.AG.VisibleCycleReflection.WitnessTwo
open WitnessInputs FiniteInputTable CanonicalResolution ResolutionInvariance ObstructionDiagnosticBridge

/-- The same table's bounded scan generates a failure. -/
theorem failure_generated : two.searchFailure.isSome = true := by decide
/-- Extract the computational failure without choosing an abstract certificate. -/
def failure : two.SearchFailure := two.searchFailure.get failure_generated
/-- The bounded scan returns exactly this retained output. -/
theorem failure_search : two.searchFailure = some failure := (Option.some_get _).symm
/-- The first failure is the specified label one and edge 34, with deleted path 3,0,4. -/
theorem failure_codes : failure.label.val = ⟨(0 : Fin 1),(1 : Fin 2)⟩ ∧
    failure.edge.val = ((3 : Fin 5),(4 : Fin 5)) ∧
    failure.path.val.support = [(3 : Fin 5),0,4] ∧
    failure.cycle.support = [(4 : Fin 5),3,0,4] := by decide
/-- C returns the same computed failure after validating the original table. -/
theorem checked_failure : two.checkAndSearch = .failure failure :=
  (two.checkAndSearch_failure_iff two_valid failure).mpr failure_search
/-- The returned real locally constant input is decoded from the same original primitive table. -/
def input : two.ActualLocalData two_valid := SearchFailure.actualInput two failure two_valid
/-- The actual basis in the returned original primitive coefficient quotient. -/
def u1 : (two.actualPresentation two_valid).PresentationGroup :=
  labelBasis _ (two.actualReflectionCondition two_valid) (two.actualLabel failure.label)

/-- The local states in this same decoded input are all zero. -/
theorem state_zero : input.localState = 0 := SearchFailure.actual_state_zero two failure two_valid
/-- Every actual transition section is u1 on 34 and zero on all other actual edges. -/
theorem transition_values :
    letI : TopologicalSpace two.Point := two.actualTopology two_valid
    ∀ e : Graph.Edge (two.actualGeometry two_valid).graph,
      (two.actualPresentation two_valid).faceEmptyCechCochain1Equiv _ input.transition
        ((two.actualGeometry two_valid).graphEdgeEquiv.symm e) =
          if e.1 = ((3 : Fin 5),(4 : Fin 5)) then u1 else 0 := by
  letI : TopologicalSpace two.Point := two.actualTopology two_valid
  intro e
  change (two.actualPresentation two_valid).faceEmptyCechCochain1Equiv _
    (SearchFailure.actualInput two failure two_valid).transition _ = _
  rw [SearchFailure.actualInput_singleEdgeData,GeometricCover.singleEdgeData_transition_value]
  have he : e = two.actualEdge two_valid failure.edge ↔ e.1 = ((3 : Fin 5),(4 : Fin 5)) := by
    rw [← failure_codes.2.1]
    rw [← two.actualEdge_val two_valid failure.edge]
    exact Subtype.ext_iff
  simp only [he,u1]

/-- The same independently generated diagnostic cochain and diagnostic class are zero. -/
theorem diagnostic_zero : input.diagnosticMismatch (two.actualAdequate two_valid) = 0 ∧
    input.diagnosticClass (two.actualAdequate two_valid) = 0 :=
  SearchFailure.actual_diagnostic_zero two failure two_valid
/-- The original existing descent class is nonzero on the same decoded local input. -/
theorem existing_nonzero : input.existingDescentAdditiveClass ≠ 0 :=
  SearchFailure.actual_existing_nonzero two failure two_valid
/-- B1, B2 and B3 each fail for this same valid two-triangle input. -/
theorem reflection_fails : ¬two.ActualReflects two_valid ∧
    ¬two.ActualHomologySurjective two_valid ∧ ¬two.ActualNonbridgeVisible two_valid := by
  have hf : two.reflectsTest = false := by decide
  refine ⟨?_,?_,?_⟩
  · intro h; have ht := (two.reflectsTest_iff_actual_reflection two_valid).mpr h
    rw [hf] at ht; contradiction
  · intro h; have ht := (two.reflectsTest_iff_actual_homology two_valid).mpr h
    rw [hf] at ht; contradiction
  · intro h; have ht := (two.reflectsTest_iff_actual_nonbridge two_valid).mpr h
    rw [hf] at ht; contradiction

/-- The original 34 actual intersection column. -/
def edge34 : two.RawEdge := ⟨(3,4),by decide⟩
/-- The failure retains exactly the specified 34 column. -/
theorem failure_edge34 : failure.edge = edge34 := Subtype.ext failure_codes.2.1
/-- The prescribed positive closed walk gamma=(0,3,4,0) on the complete original nerve. -/
def rawGamma : two.rawGraph.Walk (0 : Fin 5) 0 :=
  .cons (by decide : two.rawGraph.Adj 0 3)
    (.cons (by decide : two.rawGraph.Adj 3 4)
      (.cons (by decide : two.rawGraph.Adj 4 0) .nil))
/-- Its selected 34 signed chain coefficient is positive one. -/
theorem gamma_coefficient : Graph.walkChain two.rawGraph rawGamma (two.rawGraphEdge edge34) = 1 := by
  simp only [rawGamma,Graph.walkChain_cons,Graph.walkChain_nil,Pi.add_apply,Pi.zero_apply]
  rw [Graph.hopChain_of_lt _ _ (by decide),Graph.hopChain_of_lt _ _ (by decide),
    Graph.hopChain_of_not_lt _ _ (by decide)]
  have h30 : (3 : Fin 5) ≠ 0 := by decide
  norm_num [Graph.edgeUnit_apply,edge34,FiniteInputTable.rawGraphEdge,h30]
/-- The manually prescribed walk is transported to the same actual geometric graph. -/
def gamma :
    letI : TopologicalSpace two.Point := two.actualTopology two_valid
    (two.actualGeometry two_valid).graph.Walk (0 : Fin 5) 0 :=
  Graph.transportWalk (two.actualGeometry_graph two_valid).symm rawGamma
/-- The original actual period on the prescribed gamma is u1. -/
theorem prescribed_period :
    letI : TopologicalSpace two.Point := two.actualTopology two_valid
    (two.actualGeometry two_valid).actualTransitionPeriod (two.actualTarget two_valid)
      (two.actualTarget_nonempty two_valid) (two.actualPresentation two_valid) input gamma = u1 := by
  letI : TopologicalSpace two.Point := two.actualTopology two_valid
  apply GeometricCover.singleEdgeData_period_one
  change Graph.walkChain _ gamma (two.actualEdge two_valid failure.edge) = 1
  rw [failure_edge34,two.actualEdge_transport]
  change Graph.walkChain _ (Graph.transportWalk _ rawGamma) _ = 1
  rw [Graph.transportWalk_coefficient,gamma_coefficient]
/-- The prescribed positive basis period is nonzero in the original primitive coefficient group. -/
theorem prescribed_period_nonzero :
    letI : TopologicalSpace two.Point := two.actualTopology two_valid
    (two.actualGeometry two_valid).actualTransitionPeriod (two.actualTarget two_valid)
      (two.actualTarget_nonempty two_valid) (two.actualPresentation two_valid) input gamma ≠ 0 := by
  rw [prescribed_period]
  exact labelBasis_ne_zero _ (two.actualReflectionCondition two_valid) _
/-- The scan-generated opposite orientation has period minus the same original basis. -/
theorem computed_period :
    letI : TopologicalSpace two.Point := two.actualTopology two_valid
    (two.actualGeometry two_valid).actualTransitionPeriod (two.actualTarget two_valid)
      (two.actualTarget_nonempty two_valid) (two.actualPresentation two_valid) input
      (SearchFailure.actualCycle two failure two_valid) = -u1 :=
  SearchFailure.actual_period two failure two_valid

/-- A applies to this same original actual input for every generated label. -/
theorem comparison (l : LawValueLabel two.laws) :
    letI : TopologicalSpace two.Point := two.actualTopology two_valid
    (DirectSum.linearEquivFunOnFintype ℚ (LawValueLabel two.laws)
      (fun a => VisibleGraphH1 (two.actualNerve two_valid) (two.actualAdequate two_valid) a)
      (diagnosticVisibleH1Equiv (two.actualNerve two_valid) (two.actualAdequate two_valid)
        (input.diagnosticClass (two.actualAdequate two_valid)))) l =
      rationalRestrictionH1 (two.actualNerve two_valid) (two.actualAdequate two_valid) l
        (integerToRationalH1 (two.actualNerve two_valid).nerve (LawValueLabel two.laws)
          (actualIntegralH1Equiv (two.actualPresentation two_valid)
            ((two.actualGeometry two_valid).actualCechCover (two.actualPresentation two_valid)
              (two.actualTarget two_valid) (two.actualTarget_nonempty two_valid)) (two.actualReflectionCondition two_valid)
            input.existingDescentAdditiveClass)) :=
  two.actual_input_factorization two_valid input l

end AAT.AG.VisibleCycleReflection.WitnessTwo
#assert_standard_axioms_only AAT.AG.VisibleCycleReflection.WitnessTwo
