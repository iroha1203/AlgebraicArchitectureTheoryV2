import ResearchLean.AG.ObstructionDiagnosticBridge.CombinedAtomReadingNaturality
import ResearchLean.AG.ObstructionDiagnosticBridge.CombinedAtomSpecifiedReflection
import ResearchLean.AG.ResolutionInvariance.LawValueBlockComparisonBijectivity
import Formal.Util.AssertStandardAxioms

/-!
# Condition C and obstruction transport for the selected reading refinement

The selected fine diagnostic support contains one representative
`(value, false)` for each Law value.  Hence every generated Law-value block is
canonically enumerated by the cells of the underlying finite nerve.  This file
uses that enumeration to verify C0--C6 for the actual three-chart/four-chart
refinement and then proves the G-125(C2) vanishing equivalence.
-/

noncomputable section

namespace AAT.AG.ObstructionDiagnosticBridge
namespace SelectedReadingConditionC

open BigOperators Cohomology ResolutionInvariance TwoPhase
open SelectedFiniteGeometry PointAtomActualNerve PointAtomLawInput
open SelectedReadingRefinement CombinedAtomSpecifiedObstruction
open CombinedAtomReadingNaturality CombinedAtomSpecifiedReflection
open GeneratorPresentation

set_option maxHeartbeats 1000000

/-! ## Named coordinates for an arbitrary generated label -/

def fineChartCoordinate (label : LawValueLabel laws) (chart : FineChart) :
    fineSupportedNerve.ChartBlockCoordinate laws fine_adequate label :=
  ⟨CommonLabelChartSupport.chartCoordinate fine_adequate
      fine_commonLabelChartSupport chart label, by simp⟩

def coarseChartCoordinate (label : LawValueLabel laws) (chart : CoarseChart) :
    coarseSupportedNerve.ChartBlockCoordinate laws coarse_adequate label :=
  ⟨CommonLabelChartSupport.chartCoordinate coarse_adequate
      coarse_commonLabelChartSupport chart label, by simp⟩

def fineEdgeCoordinate (label : LawValueLabel laws) (edge : Edge) :
    fineSupportedNerve.EdgeBlockCoordinate laws fine_adequate label :=
  ⟨CommonLabelChartSupport.edgeCoordinate fine_adequate
      fine_commonLabelChartSupport edge label, by simp⟩

def coarseEdgeCoordinate (label : LawValueLabel laws) (edge : CoarseEdge) :
    coarseSupportedNerve.EdgeBlockCoordinate laws coarse_adequate label :=
  ⟨CommonLabelChartSupport.edgeCoordinate coarse_adequate
      coarse_commonLabelChartSupport edge label, by simp⟩

@[simp] theorem fineChartCoordinate_cell (label) (chart) :
    (fineChartCoordinate label chart).1.cell = chart := rfl

@[simp] theorem coarseChartCoordinate_cell (label) (chart) :
    (coarseChartCoordinate label chart).1.cell = chart := rfl

@[simp] theorem fineEdgeCoordinate_cell (label) (edge) :
    (fineEdgeCoordinate label edge).1.cell = edge := rfl

@[simp] theorem coarseEdgeCoordinate_cell (label) (edge) :
    (coarseEdgeCoordinate label edge).1.cell = edge := rfl

theorem fineChartCoordinate_eq (label) (coordinate) :
    fineChartCoordinate label coordinate.1.cell = coordinate := by
  apply fineSupportedNerve.lawValueCoordinateSubnerveChartCell_injective
  rfl

theorem coarseChartCoordinate_eq (label) (coordinate) :
    coarseChartCoordinate label coordinate.1.cell = coordinate := by
  apply coarseSupportedNerve.lawValueCoordinateSubnerveChartCell_injective
  rfl

theorem fineEdgeCoordinate_eq (label) (coordinate) :
    fineEdgeCoordinate label coordinate.1.cell = coordinate := by
  apply fineSupportedNerve.lawValueCoordinateSubnerveEdgeCell_injective
  rfl

theorem coarseEdgeCoordinate_eq (label) (coordinate) :
    coarseEdgeCoordinate label coordinate.1.cell = coordinate := by
  apply coarseSupportedNerve.lawValueCoordinateSubnerveEdgeCell_injective
  rfl

theorem fineChartCoordinate_cases (label)
    {P : fineSupportedNerve.ChartBlockCoordinate laws fine_adequate label → Prop}
    (h : ∀ chart, P (fineChartCoordinate label chart)) (coordinate) :
    P coordinate := by
  rw [← fineChartCoordinate_eq label coordinate]
  exact h coordinate.1.cell

theorem coarseChartCoordinate_cases (label)
    {P : coarseSupportedNerve.ChartBlockCoordinate laws coarse_adequate label → Prop}
    (h : ∀ chart, P (coarseChartCoordinate label chart)) (coordinate) :
    P coordinate := by
  rw [← coarseChartCoordinate_eq label coordinate]
  exact h coordinate.1.cell

theorem fineEdgeCoordinate_cases (label)
    {P : fineSupportedNerve.EdgeBlockCoordinate laws fine_adequate label → Prop}
    (h : ∀ edge, P (fineEdgeCoordinate label edge)) (coordinate) :
    P coordinate := by
  rw [← fineEdgeCoordinate_eq label coordinate]
  exact h coordinate.1.cell

theorem coarseEdgeCoordinate_cases (label)
    {P : coarseSupportedNerve.EdgeBlockCoordinate laws coarse_adequate label → Prop}
    (h : ∀ edge, P (coarseEdgeCoordinate label edge)) (coordinate) :
    P coordinate := by
  rw [← coarseEdgeCoordinate_eq label coordinate]
  exact h coordinate.1.cell

@[simp] theorem fineChartCoordinate_inj (label) {left right : FineChart} :
    fineChartCoordinate label left = fineChartCoordinate label right ↔ left = right := by
  constructor
  · exact fun h => congrArg (fun coordinate => coordinate.1.cell) h
  · exact fun h => congrArg (fineChartCoordinate label) h

@[simp] theorem coarseChartCoordinate_inj (label) {left right : CoarseChart} :
    coarseChartCoordinate label left = coarseChartCoordinate label right ↔ left = right := by
  constructor
  · exact fun h => congrArg (fun coordinate => coordinate.1.cell) h
  · exact fun h => congrArg (coarseChartCoordinate label) h

@[simp] theorem fineEdgeCoordinate_inj (label) {left right : Edge} :
    fineEdgeCoordinate label left = fineEdgeCoordinate label right ↔ left = right := by
  constructor
  · exact fun h => congrArg (fun coordinate => coordinate.1.cell) h
  · exact fun h => congrArg (fineEdgeCoordinate label) h

def fineEdgeCoordinateEquiv (label : LawValueLabel laws) :
    Edge ≃ fineSupportedNerve.EdgeBlockCoordinate laws fine_adequate label where
  toFun := fineEdgeCoordinate label
  invFun := fun coordinate => coordinate.1.cell
  left_inv := fineEdgeCoordinate_cell label
  right_inv := fineEdgeCoordinate_eq label

noncomputable local instance fineEdgeBlockFintype (label : LawValueLabel laws) :
    Fintype (fineSupportedNerve.EdgeBlockCoordinate laws fine_adequate label) := by
  change Fintype
    (fineSupportedNerve.lawValueCoordinateSubnerve laws fine_adequate label).EdgeComponent
  exact TargetSupportedNerve.lawValueCoordinateSubnerveEdgeFintype
    fineSupportedNerve laws fine_adequate label

noncomputable local instance fineFaceBlockFintype (label : LawValueLabel laws) :
    Fintype (fineSupportedNerve.FaceBlockCoordinate laws fine_adequate label) := by
  change Fintype
    (fineSupportedNerve.lawValueCoordinateSubnerve laws fine_adequate label).FaceComponent
  exact TargetSupportedNerve.lawValueCoordinateSubnerveFaceFintype
    fineSupportedNerve laws fine_adequate label

/-! ## Coordinate incidence and partial maps -/

@[simp] theorem chartBlockCoordinateMap (label) (chart : FineChart) :
    nerveMorphism.chartBlockCoordinateMap laws coarse_adequate fine_adequate
        label (fineChartCoordinate label chart) =
      coarseChartCoordinate label (chartMap chart) := by
  apply coarseSupportedNerve.lawValueCoordinateSubnerveChartCell_injective
  rfl

@[simp] theorem fine_edgeLeftBlockCoordinate (label) (edge : Edge) :
    fineSupportedNerve.edgeLeftBlockCoordinate laws fine_adequate label
        (fineEdgeCoordinate label edge) =
      fineChartCoordinate label (fineEdgeLeft edge) := by
  apply fineSupportedNerve.lawValueCoordinateSubnerveChartCell_injective
  rfl

@[simp] theorem fine_edgeRightBlockCoordinate (label) (edge : Edge) :
    fineSupportedNerve.edgeRightBlockCoordinate laws fine_adequate label
        (fineEdgeCoordinate label edge) =
      fineChartCoordinate label (fineEdgeRight edge) := by
  apply fineSupportedNerve.lawValueCoordinateSubnerveChartCell_injective
  rfl

theorem edgeBlockCoordinateMapOption (label) (edge : CoarseEdge) :
    nerveMorphism.edgeBlockCoordinateMapOption laws coarse_adequate fine_adequate
        label (fineEdgeCoordinate label (match edge with
          | .ab => .ab | .bc => .bc | .ac => .ac)) =
      some (coarseEdgeCoordinate label edge) := by
  cases edge <;>
    rw [nerveMorphism.edgeBlockCoordinateMapOption_eq_some laws coarse_adequate
      fine_adequate label]
  all_goals rfl

/-! ## C0--C6 -/

theorem conditionC0 : nerveMorphism.ConditionC0 := by
  intro coarseChart coarseTarget
  constructor
  · intro _
    cases coarseChart
    · exact ⟨.a0, (coarseTarget, false), rfl, by simp [fineSupportedNerve], by
        simp [comparisonFactor_eq_fst]⟩
    · exact ⟨.b, (coarseTarget, false), rfl, by simp [fineSupportedNerve], by
        simp [comparisonFactor_eq_fst]⟩
    · exact ⟨.c, (coarseTarget, false), rfl, by simp [fineSupportedNerve], by
        simp [comparisonFactor_eq_fst]⟩
  · rintro ⟨fineChart, fineTarget, hchart, htarget, hfactor⟩
    rw [← hchart, ← hfactor]
    exact nerveMorphism.chartSupport_compatible fineChart fineTarget htarget

theorem fiberEdge_k (label) :
    nerveMorphism.CoordinateFiberEdge laws coarse_adequate fine_adequate label
      (coarseChartCoordinate label .c0) (fineEdgeCoordinate label .k) := by
  simp [TargetSupportedNerveMorphism.CoordinateFiberEdge, chartMap,
    fineEdgeLeft, fineEdgeRight]

theorem fiberAdjacent_a0_a1 (label) :
    nerveMorphism.CoordinateFiberAdjacent laws coarse_adequate fine_adequate label
      (coarseChartCoordinate label .c0) (fineChartCoordinate label .a0)
        (fineChartCoordinate label .a1) := by
  refine ⟨fineEdgeCoordinate label .k, fiberEdge_k label, ?_⟩
  exact Or.inl ⟨by simp [fineEdgeLeft], by simp [fineEdgeRight]⟩

theorem fiberAdjacent_a1_a0 (label) :
    nerveMorphism.CoordinateFiberAdjacent laws coarse_adequate fine_adequate label
      (coarseChartCoordinate label .c0) (fineChartCoordinate label .a1)
        (fineChartCoordinate label .a0) :=
  (fiberAdjacent_a0_a1 label).symm nerveMorphism laws coarse_adequate fine_adequate

theorem conditionC1 :
    nerveMorphism.ConditionC1 laws coarse_adequate fine_adequate := by
  intro label coarseCoordinate
  refine coarseChartCoordinate_cases label
    (P := fun current =>
      (∃ fineChart,
        nerveMorphism.chartBlockCoordinateMap laws coarse_adequate fine_adequate
          label fineChart = current) ∧
      ∀ left right,
        nerveMorphism.chartBlockCoordinateMap laws coarse_adequate fine_adequate
            label left = current →
        nerveMorphism.chartBlockCoordinateMap laws coarse_adequate fine_adequate
            label right = current →
        Relation.ReflTransGen
          (nerveMorphism.CoordinateFiberAdjacent laws coarse_adequate
            fine_adequate label current) left right)
    (coordinate := coarseCoordinate) ?_
  intro coarseChart
  constructor
  · cases coarseChart
    · exact ⟨fineChartCoordinate label .a0, by simp [chartMap]⟩
    · exact ⟨fineChartCoordinate label .b, by simp [chartMap]⟩
    · exact ⟨fineChartCoordinate label .c, by simp [chartMap]⟩
  · intro left right
    refine fineChartCoordinate_cases label
      (P := fun currentLeft =>
        nerveMorphism.chartBlockCoordinateMap laws coarse_adequate fine_adequate
            label currentLeft = coarseChartCoordinate label coarseChart →
        nerveMorphism.chartBlockCoordinateMap laws coarse_adequate fine_adequate
            label right = coarseChartCoordinate label coarseChart →
        Relation.ReflTransGen
          (nerveMorphism.CoordinateFiberAdjacent laws coarse_adequate
            fine_adequate label (coarseChartCoordinate label coarseChart))
          currentLeft right)
      (coordinate := left) ?_
    intro leftChart hleft hright
    refine fineChartCoordinate_cases label
      (P := fun currentRight =>
        nerveMorphism.chartBlockCoordinateMap laws coarse_adequate fine_adequate
            label (fineChartCoordinate label leftChart) =
              coarseChartCoordinate label coarseChart →
        nerveMorphism.chartBlockCoordinateMap laws coarse_adequate fine_adequate
            label currentRight = coarseChartCoordinate label coarseChart →
        Relation.ReflTransGen
          (nerveMorphism.CoordinateFiberAdjacent laws coarse_adequate
            fine_adequate label (coarseChartCoordinate label coarseChart))
          (fineChartCoordinate label leftChart) currentRight)
      (coordinate := right) ?_ hleft hright
    intro rightChart hleft hright
    cases coarseChart <;> cases leftChart <;> cases rightChart <;>
      simp [chartMap] at hleft hright
    all_goals first
      | exact Relation.ReflTransGen.refl
      | exact Relation.ReflTransGen.single (fiberAdjacent_a0_a1 label)
      | exact Relation.ReflTransGen.single (fiberAdjacent_a1_a0 label)

theorem conditionC2 :
    nerveMorphism.ConditionC2 laws coarse_adequate fine_adequate := by
  intro label coarseCoordinate
  refine coarseEdgeCoordinate_cases label
    (P := fun current => ∃ fineEdge,
      nerveMorphism.edgeBlockCoordinateMapOption laws coarse_adequate
        fine_adequate label fineEdge = some current)
    (coordinate := coarseCoordinate) ?_
  intro edge
  exact ⟨fineEdgeCoordinate label (match edge with
    | .ab => .ab | .bc => .bc | .ac => .ac),
      edgeBlockCoordinateMapOption label edge⟩

theorem conditionC4 :
    nerveMorphism.ConditionC4 laws coarse_adequate fine_adequate := by
  intro _label coarseFace
  exact isEmptyElim coarseFace.1.cell

theorem conditionC5 : nerveMorphism.ConditionC5 := by
  intro coarseEdge fineLeft fineRight hleft hright
  change edgeMap fineLeft = some coarseEdge at hleft
  change edgeMap fineRight = some coarseEdge at hright
  cases coarseEdge <;> cases fineLeft <;> cases fineRight <;>
    simp [edgeMap] at hleft hright ⊢

theorem conditionC6 : nerveMorphism.ConditionC6 := by
  intro fineEdge coarseEdge hmap hloop
  change edgeMap fineEdge = some coarseEdge at hmap
  change coarseEdgeLeft coarseEdge = coarseEdgeRight coarseEdge at hloop
  cases fineEdge <;> cases coarseEdge <;>
    simp [edgeMap, coarseEdgeLeft, coarseEdgeRight] at hmap hloop ⊢

/-! ## The face-free local fiber condition C3 -/

theorem coordinateFiberIncoming_formula (label)
    (chain : fineSupportedNerve.EdgeBlockCoordinate laws fine_adequate label → ℚ)
    (chart : FineChart) :
    TargetSupportedNerveMorphism.coordinateFiberIncoming laws fine_adequate
        fineSupportedNerve label chain (fineChartCoordinate label chart) =
      ∑ edge : Edge,
        if fineEdgeRight edge = chart then chain (fineEdgeCoordinate label edge) else 0 := by
  unfold TargetSupportedNerveMorphism.coordinateFiberIncoming
  rw [← (fineEdgeCoordinateEquiv label).sum_comp]
  simp [fineEdgeCoordinateEquiv]

theorem coordinateFiberOutgoing_formula (label)
    (chain : fineSupportedNerve.EdgeBlockCoordinate laws fine_adequate label → ℚ)
    (chart : FineChart) :
    TargetSupportedNerveMorphism.coordinateFiberOutgoing laws fine_adequate
        fineSupportedNerve label chain (fineChartCoordinate label chart) =
      ∑ edge : Edge,
        if fineEdgeLeft edge = chart then chain (fineEdgeCoordinate label edge) else 0 := by
  unfold TargetSupportedNerveMorphism.coordinateFiberOutgoing
  rw [← (fineEdgeCoordinateEquiv label).sum_comp]
  simp [fineEdgeCoordinateEquiv]

/-- Expand a finite sum over the four selected fine edges. -/
theorem sum_edge (f : Edge → ℚ) :
    ∑ edge, f edge = f .k + f .ab + f .bc + f .ac := by
  classical
  rw [show (Finset.univ : Finset Edge) = {.k, .ab, .bc, .ac} by decide]
  simp [add_assoc]

theorem conditionC3 :
    nerveMorphism.ConditionC3 laws coarse_adequate fine_adequate := by
  intro label coarseCoordinate
  refine coarseChartCoordinate_cases label
    (P := fun current =>
      ∀ chain,
        nerveMorphism.CoordinateFiberCycle laws coarse_adequate fine_adequate
            label current chain →
          ∃ faces,
            (∀ fineFace,
              ¬ nerveMorphism.CoordinateInternalFace laws coarse_adequate
                  fine_adequate label current fineFace →
                faces fineFace = 0) ∧
            ∀ fineEdge,
              chain fineEdge =
                TargetSupportedNerveMorphism.coordinateFaceBoundary laws
                  fine_adequate fineSupportedNerve label faces fineEdge)
    (coordinate := coarseCoordinate) ?_
  intro coarseChart chain hcycle
  have hedge_zero (edge : Edge)
      (houtside : ¬ nerveMorphism.CoordinateFiberEdge laws coarse_adequate
        fine_adequate label (coarseChartCoordinate label coarseChart)
          (fineEdgeCoordinate label edge)) :
      chain (fineEdgeCoordinate label edge) = 0 :=
    hcycle.1 _ houtside
  have hab : chain (fineEdgeCoordinate label .ab) = 0 := hedge_zero .ab (by
    cases coarseChart <;> simp [TargetSupportedNerveMorphism.CoordinateFiberEdge,
      chartMap, fineEdgeLeft, fineEdgeRight])
  have hbc : chain (fineEdgeCoordinate label .bc) = 0 := hedge_zero .bc (by
    cases coarseChart <;> simp [TargetSupportedNerveMorphism.CoordinateFiberEdge,
      chartMap, fineEdgeLeft, fineEdgeRight])
  have hac : chain (fineEdgeCoordinate label .ac) = 0 := hedge_zero .ac (by
    cases coarseChart <;> simp [TargetSupportedNerveMorphism.CoordinateFiberEdge,
      chartMap, fineEdgeLeft, fineEdgeRight])
  have hk : chain (fineEdgeCoordinate label .k) = 0 := by
    cases coarseChart
    · have hconserve := hcycle.2 (fineChartCoordinate label .a0) (by
        simp [chartMap])
      rw [coordinateFiberIncoming_formula, coordinateFiberOutgoing_formula] at hconserve
      rw [sum_edge, sum_edge] at hconserve
      symm
      simpa [fineEdgeLeft, fineEdgeRight, hab, hbc, hac] using hconserve
    · exact hedge_zero .k (by
        simp [TargetSupportedNerveMorphism.CoordinateFiberEdge, chartMap,
          fineEdgeLeft, fineEdgeRight])
    · exact hedge_zero .k (by
        simp [TargetSupportedNerveMorphism.CoordinateFiberEdge, chartMap,
          fineEdgeLeft, fineEdgeRight])
  refine ⟨0, ?_, ?_⟩
  · intro fineFace
    exact isEmptyElim fineFace.1.cell
  · intro fineCoordinate
    refine fineEdgeCoordinate_cases label
      (P := fun current => chain current =
        TargetSupportedNerveMorphism.coordinateFaceBoundary laws fine_adequate
          fineSupportedNerve label 0 current)
      (coordinate := fineCoordinate) ?_
    intro edge
    cases edge <;>
      simp [TargetSupportedNerveMorphism.coordinateFaceBoundary, hk, hab, hbc, hac]

theorem conditionC :
    nerveMorphism.ConditionC laws coarse_adequate fine_adequate where
  c0 := conditionC0
  c1 := conditionC1
  c2 := conditionC2
  c3 := conditionC3
  c4 := conditionC4
  c5 := conditionC5
  c6 := conditionC6

/-! ## G-125(C2) -/

theorem diagnosticH1Map_bijective : Function.Bijective diagnosticH1Map :=
  nerveMorphism.generatedComparisonH1Map_bijective laws coarse_adequate
    fine_adequate conditionC

theorem diagnostic_class_eq_zero_iff_mapped_diagnostic_class_eq_zero
    (x : CoarseLocalData) :
    coarseDiagnosticClass x = 0 ↔ fineDiagnosticClass (mapLocalData x) = 0 := by
  change x.diagnosticClass coarse_adequate = 0 ↔
    (mapLocalData x).diagnosticClass fine_adequate = 0
  rw [← diagnosticH1Map_diagnosticClass]
  constructor
  · intro hzero
    rw [hzero, map_zero]
  · intro hzero
    exact diagnosticH1Map_bijective.1 (by simpa using hzero)

/-- G-125(C2): refinement preserves and reflects the specified obstruction zero class. -/
theorem actual_class_eq_zero_iff_mapped_actual_class_eq_zero
    (x : CoarseLocalData) :
    coarseActualClass x = 0 ↔ fineActualClass (mapLocalData x) = 0 := by
  rw [← coarse_diagnostic_class_eq_zero_iff_actual_class_eq_zero]
  rw [← fine_diagnostic_class_eq_zero_iff_actual_class_eq_zero]
  exact diagnostic_class_eq_zero_iff_mapped_diagnostic_class_eq_zero x

#assert_standard_axioms_only
  AAT.AG.ObstructionDiagnosticBridge.SelectedReadingConditionC

end SelectedReadingConditionC
end AAT.AG.ObstructionDiagnosticBridge
