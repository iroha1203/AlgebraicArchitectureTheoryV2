import ResearchLean.AG.VisibleCycleReflection.WitnessRepair
import ResearchLean.AG.VisibleCycleReflection.WitnessCycles
import ResearchLean.AG.ObstructionDiagnosticBridge.SpecifiedClassReflection
import Formal.Util.AssertStandardAxioms

/-!
# W1: visible triangle, invisible bridge, and original integer repair

## Implementation notes

The actual transition is the differential of the specified original chart
values. The all-input reflection statement is obtained from the finite scan,
while its nonzero H1 witness is an actual closed walk on the same geometry.
The fractional potential includes chart three; its floor is the explicit
original correction, whose p-n sections glue on the original AAT site.
A common-label representative proof was rejected because the prescribed last
chart has no label-one representative; the full graph potential retains its
nonzero value on that chart.
-/

noncomputable section
open Classical
namespace AAT.AG.VisibleCycleReflection.WitnessOne
open WitnessInputs FiniteInputTable CanonicalResolution ResolutionInvariance ObstructionDiagnosticBridge

/-- Source-generated label one of the original four-source Law input. -/
def labelOne : LawValueLabel one.laws := LawValueLabel.ofSource one.laws (0 : Fin 1) (1 : Fin 4)
/-- The same original primitive coefficient basis for label one. -/
def u1 : (one.actualPresentation one_valid).PresentationGroup :=
  labelBasis _ (one.actualReflectionCondition one_valid) labelOne
/-- The prescribed integer original chart table h=(0,u1,0,u1). -/
def chartValues : one.Chart → (one.actualPresentation one_valid).PresentationGroup := ![0,u1,0,u1]
/-- Actual integer chart sections restored from the original h table. -/
def correction := one.chartCochain one_valid chartValues
/-- The prescribed actual transition xi=d0h and original zero state p=0. -/
def input : one.ActualLocalData one_valid := one.chartDifferenceInput one_valid chartValues

/-- The actual local state is identically zero. -/
theorem state_zero : input.localState = 0 := rfl
/-- The original integer chart section n=h is an exact correction of the actual mismatch. -/
theorem correction_equation :
    letI : TopologicalSpace one.Point := one.actualTopology one_valid
    ((one.actualPresentation one_valid).faceEmptyCechComplex _).d 0 correction = input.actualMismatch :=
  one.chartDifferenceInput_correction one_valid chartValues

/-- The bridge test and reflection scan succeed on W1's same finite table. -/
theorem finite_success : one.reflectsTest = true := by decide
/-- C returns success on W1 after the same table passes T0 validation. -/
theorem checked_success : one.checkAndSearch = .success :=
  (one.checkAndSearch_success_iff one_valid).mpr finite_success
/-- B1, B2 and B3 all hold for every actual integer transition and every actual chart state. -/
theorem all_input_reflection : one.ActualReflects one_valid ∧
    one.ActualHomologySurjective one_valid ∧ one.ActualNonbridgeVisible one_valid :=
  (one.checkAndSearch_actual_success one_valid).mp checked_success

/-- Original chart coordinates of the correction are exactly the prescribed h table. -/
theorem correction_values :
    letI : TopologicalSpace one.Point := one.actualTopology one_valid
    (one.actualPresentation one_valid).faceEmptyCechCochain0Equiv _
    correction = chartValues := one.chartCochain_values one_valid chartValues

/-- On all actual edges, the transition has the prescribed (u1,0,-u1,u1) original values. -/
theorem transition_values :
    letI : TopologicalSpace one.Point := one.actualTopology one_valid
    ∀ e : Graph.Edge (one.actualGeometry one_valid).graph,
      (one.actualPresentation one_valid).faceEmptyCechCochain1Equiv _ input.transition
          ((one.actualGeometry one_valid).graphEdgeEquiv.symm e) =
        chartValues e.1.2 - chartValues e.1.1 :=
  one.chartDifferenceInput_transition one_valid chartValues

/-- The selected actual 01 edge is decoded from its original finite intersection cell. -/
def edge01 : one.RawEdge := ⟨(0,1),by decide⟩
/-- The mismatch is nonzero, already on the original basis-valued 01 section. -/
theorem mismatch_nonzero : input.actualMismatch ≠ 0 := by
  letI : TopologicalSpace one.Point := one.actualTopology one_valid
  intro hz
  have hm := one.chartDifferenceInput_mismatch one_valid chartValues
  have ht := transition_values (one.actualEdge one_valid edge01)
  have hzero : input.transition = 0 := by
    change (one.chartDifferenceInput one_valid chartValues).actualMismatch = 0 at hz
    rw [hm] at hz
    exact hz
  rw [hzero,map_zero] at ht
  change 0 = chartValues (one.actualEdge one_valid edge01).1.2 -
    chartValues (one.actualEdge one_valid edge01).1.1 at ht
  rw [one.actualEdge_val] at ht
  change 0 = u1 - 0 at ht
  exact labelBasis_ne_zero _ (one.actualReflectionCondition one_valid) labelOne
    (by simpa [u1] using ht.symm)

/-- The repaired witness has zero existing original descent class. -/
theorem existing_zero : input.existingDescentAdditiveClass = 0 :=
  one.chartDifferenceInput_existing_zero one_valid chartValues
/-- The independently generated diagnostic class vanishes on the same repaired input. -/
theorem diagnostic_zero : input.diagnosticClass (one.actualAdequate one_valid) = 0 :=
  (all_input_reflection.1 input).mpr existing_zero

/-- A rational full-graph potential: label zero is zero; label one is (1/2,3/2,1/2,3/2). -/
def rationalPotential (i : one.Chart) (l : LawValueLabel one.laws) : ℚ :=
  if l = labelOne then (![1/2,3/2,1/2,3/2] : Fin 4 → ℚ) i else 0

/-- Original chart table's integral coordinates are supported on charts one and three and label one. -/
theorem chartValues_coordinates (i : one.Chart) (l : LawValueLabel one.laws) :
    integralLabelEquiv (one.actualPresentation one_valid) (one.actualReflectionCondition one_valid)
      (chartValues i) l = if i = 1 ∨ i = 3 then if l = labelOne then 1 else 0 else 0 := by
  fin_cases i
  · change integralLabelEquiv _ _ 0 l = _
    simp only [map_zero,Pi.zero_apply]; simp
  · change integralLabelEquiv _ _ (labelBasis _ _ labelOne) l = _
    rw [integralLabelEquiv_labelBasis]; simp
  · change integralLabelEquiv _ _ 0 l = _
    simp only [map_zero,Pi.zero_apply]; simp
  · change integralLabelEquiv _ _ (labelBasis _ _ labelOne) l = _
    rw [integralLabelEquiv_labelBasis]; simp

/-- The floor is exactly the original chart table in integral label coordinates, including chart three. -/
theorem floor_coordinates :
    IntegralReflection.floorCorrection rationalPotential =
      fun i => integralLabelEquiv (one.actualPresentation one_valid)
        (one.actualReflectionCondition one_valid) (chartValues i) := by
  classical
  funext i l
  rw [chartValues_coordinates]
  fin_cases i <;> by_cases hl : l = labelOne <;>
    simp [IntegralReflection.floorCorrection_apply,rationalPotential,hl] <;> norm_num

/-- The same original full-graph rational potential has every required integral transition difference. -/
theorem rational_differences :
    letI : TopologicalSpace one.Point := one.actualTopology one_valid
    ∀ (e : Graph.Edge (one.actualGeometry one_valid).graph) (l : LawValueLabel one.laws),
      rationalPotential e.1.2 l - rationalPotential e.1.1 l =
        (integralLabelEquiv (one.actualPresentation one_valid)
          (one.actualReflectionCondition one_valid)
          ((one.actualPresentation one_valid).faceEmptyCechCochain1Equiv _ input.transition
            ((one.actualGeometry one_valid).graphEdgeEquiv.symm e)) l : ℚ) := by
  letI : TopologicalSpace one.Point := one.actualTopology one_valid
  classical
  intro e l
  rw [transition_values,map_sub]
  simp only [Pi.sub_apply,chartValues_coordinates]
  generalize hi : e.1.1 = i
  generalize hj : e.1.2 = j
  fin_cases i <;> fin_cases j <;> by_cases hl : l = labelOne <;>
    simp [rationalPotential,hl] <;> norm_num

/-- Actual integer chart sections obtained by flooring the prescribed full rational potential. -/
def floorSections :
    letI : TopologicalSpace one.Point := one.actualTopology one_valid
    ((one.actualPresentation one_valid).faceEmptyCechComplex
      ((one.actualGeometry one_valid).actualCechCover (one.actualPresentation one_valid)
        (one.actualTarget one_valid) (one.actualTarget_nonempty one_valid))).Cn 0 := by
  letI : TopologicalSpace one.Point := one.actualTopology one_valid
  exact (actualIntegralCochain0Equiv (one.actualPresentation one_valid) _
    (one.actualReflectionCondition one_valid)).symm
      (IntegralReflection.floorCorrection rationalPotential)

/-- Restoring the floor to actual primitive sections returns exactly the prescribed correction h. -/
theorem floor_restores_correction : floorSections = correction := by
  letI : TopologicalSpace one.Point := one.actualTopology one_valid
  apply (actualIntegralCochain0Equiv (one.actualPresentation one_valid) _
    (one.actualReflectionCondition one_valid)).injective
  change (actualIntegralCochain0Equiv _ _ _)
    ((actualIntegralCochain0Equiv _ _ _).symm _) = _
  rw [AddEquiv.apply_symm_apply,floor_coordinates]
  funext i l
  rw [actualIntegralCochain0Equiv_apply,correction_values]

/-- Common-label chart support fails because chart three contains only the original source c. -/
theorem no_common_label :
    letI : TopologicalSpace one.Point := one.actualTopology one_valid
    ¬GeneratorPresentation.CommonLabelChartSupport (one.actualNerve one_valid)
      one.laws (one.actualAdequate one_valid) := by
  letI : TopologicalSpace one.Point := one.actualTopology one_valid
  intro hs
  obtain ⟨t,ht,hv⟩ := hs labelOne
  have ht3 := ht (3 : Fin 4)
  change t ∈ ((one.actualGeometry one_valid).supportedNerve
    (one.actualTarget one_valid) (one.actualTarget_nonempty one_valid)).chartSupport (3 : Fin 4) at ht3
  rw [GeometricCover.supportedNerve_chartSupport,one.actualTarget_mem] at ht3
  change t ∈ one.target (3 : Fin 4) at ht3
  rw [one_target_three] at ht3
  have ht0 : t = (0 : Fin 4) := Finset.mem_singleton.mp ht3
  subst t
  have he := one.actualLawDescend_read one_valid labelOne (0 : Fin 4)
  change lawDescend one.laws (one.actualReading one_valid) (one.actualAdequate one_valid)
    labelOne.law (0 : Fin 4) = (0 : Fin 2) at he
  have hn : (0 : Fin 2) ≠ 1 := by decide
  exact hn (he.symm.trans hv)

/-- The original triangle gives a concrete closed walk on the complete raw nerve. -/
def rawTriangle : one.rawGraph.Walk (0 : Fin 4) 0 :=
  .cons (by decide : one.rawGraph.Adj 0 1)
    (.cons (by decide : one.rawGraph.Adj 1 2)
      (.cons (by decide : one.rawGraph.Adj 2 0) .nil))

/-- Its 01 signed chain coefficient is one. -/
theorem triangle_coefficient : Graph.walkChain one.rawGraph rawTriangle (one.rawGraphEdge edge01) = 1 := by
  simp only [rawTriangle,Graph.walkChain_cons,Graph.walkChain_nil,Pi.add_apply,Pi.zero_apply]
  rw [Graph.hopChain_of_lt _ _ (by decide),Graph.hopChain_of_lt _ _ (by decide),
    Graph.hopChain_of_not_lt _ _ (by decide)]
  simp only [Graph.edgeUnit_apply,Subtype.ext_iff,FiniteInputTable.rawGraphEdge_val]
  norm_num [edge01]
  decide

/-- W1 has nonzero actual H1 despite lacking common-label representatives. -/
theorem actual_h1_nonzero :
    letI : TopologicalSpace one.Point := one.actualTopology one_valid
    ∃ c : Graph.H1 (one.actualGeometry one_valid).graph, c ≠ 0 := by
  letI : TopologicalSpace one.Point := one.actualTopology one_valid
  let p := Graph.transportWalk (one.actualGeometry_graph one_valid).symm rawTriangle
  refine ⟨Graph.closedWalkH1 _ p,?_⟩
  intro hz
  have hc := congrArg (fun c : Graph.H1 (one.actualGeometry one_valid).graph =>
    c.val (one.actualEdge one_valid edge01)) hz
  dsimp only at hc
  rw [Graph.closedWalkH1_value] at hc
  change Graph.walkChain _ p (one.actualEdge one_valid edge01) = 0 at hc
  rw [one.actualEdge_transport] at hc
  rw [Graph.transportWalk_coefficient] at hc
  rw [triangle_coefficient] at hc
  norm_num at hc

/-- The prescribed original p-n sections have an actual unique AAT gluing. -/
theorem gluing : one.ActualCorrectedGluing one_valid input correction :=
  one.chartDifferenceInput_gluing one_valid chartValues

/-- A applies to this same original actual input for every generated label. -/
theorem comparison (l : LawValueLabel one.laws) :
    letI : TopologicalSpace one.Point := one.actualTopology one_valid
    (DirectSum.linearEquivFunOnFintype ℚ (LawValueLabel one.laws)
      (fun a => VisibleGraphH1 (one.actualNerve one_valid) (one.actualAdequate one_valid) a)
      (diagnosticVisibleH1Equiv (one.actualNerve one_valid) (one.actualAdequate one_valid)
        (input.diagnosticClass (one.actualAdequate one_valid)))) l =
      rationalRestrictionH1 (one.actualNerve one_valid) (one.actualAdequate one_valid) l
        (integerToRationalH1 (one.actualNerve one_valid).nerve (LawValueLabel one.laws)
          (actualIntegralH1Equiv (one.actualPresentation one_valid)
            ((one.actualGeometry one_valid).actualCechCover (one.actualPresentation one_valid)
              (one.actualTarget one_valid) (one.actualTarget_nonempty one_valid)) (one.actualReflectionCondition one_valid)
            input.existingDescentAdditiveClass)) :=
  one.actual_input_factorization one_valid input l

end AAT.AG.VisibleCycleReflection.WitnessOne
#assert_standard_axioms_only AAT.AG.VisibleCycleReflection.WitnessOne
