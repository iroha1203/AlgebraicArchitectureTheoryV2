import ResearchLean.AG.UniformInvariance.ConditionCAllAChecker
import ResearchLean.AG.ResolutionInvariance.ResolutionInvarianceFiringWitness
import Formal.Util.AssertStandardAxioms

/-!
# Nondegenerate firing of the all-subset Condition C checker

This module reuses the exact reviewed G-104 firing geometry.  Its coarse
reading is noninjective, its declared law is nonconstant, and the existing
coarse and fine H¹ classes are both nonzero.  We prove `ConditionCAllA` on the
original `nerveMorphism`, then present the same raw reading, incidence, support,
and partial-map tables as executable finite data and run the generic checker.

The presentation stores no condition bit, path, filling chain, matrix, rank,
H¹ class, or expected Boolean result.  The only new data are explicit source
and target enumerations and `Finset` versions of the already reviewed chart
supports.
-/

namespace AAT.AG.ResolutionInvariance

open CanonicalResolution BigOperators

namespace ResolutionInvarianceFiringWitness

/-! ## Executable support tables -/

/-- Finite-table form of the reviewed coarse chart support. -/
def firingCoarseChartSupportFinset
    (chart : coarseNerve.Chart) : Finset coarseReading.Target :=
  if chart = 0 then Finset.univ else {0}

/-- Finite-table form of the reviewed fine chart support. -/
def firingFineChartSupportFinset
    (chart : fineNerve.Chart) : Finset fineReading.Target :=
  if chart = 0 then {0, 2} else if chart = 1 then {0, 1} else {0}

/-- The executable coarse support table is exactly the reviewed Set support. -/
@[simp]
theorem mem_firingCoarseChartSupportFinset_iff
    (chart : coarseNerve.Chart) (target : coarseReading.Target) :
    target ∈ firingCoarseChartSupportFinset chart ↔
      target ∈ coarseChartSupport chart := by
  fin_cases chart <;> fin_cases target <;>
    simp [firingCoarseChartSupportFinset, coarseChartSupport]

/-- The executable fine support table is exactly the reviewed Set support. -/
@[simp]
theorem mem_firingFineChartSupportFinset_iff
    (chart : fineNerve.Chart) (target : fineReading.Target) :
    target ∈ firingFineChartSupportFinset chart ↔
      target ∈ fineChartSupport chart := by
  fin_cases chart <;> fin_cases target <;>
    simp [firingFineChartSupportFinset, fineChartSupport]

/-! ## The raw presentation of the reviewed firing fixture -/

/-- Executable finite presentation of the exact G-104 firing geometry.

Position: existing nonvacuous firing fixture reused by the Cycle 23
production-kernel validation.  Its new explicit entry lists are complete raw
coverage data, not reducer, observation, or expected-result fields. -/
def pFire : FiniteComparisonPresentation where
  Source := Source
  sourceFintype := inferInstance
  sourceDecidableEq := inferInstance
  sourceDefault := 0
  sourceEntries := [0, 1, 2]
  source_mem_sourceEntries := by
    intro source
    fin_cases source <;> simp
  CoarseTarget := coarseReading.Target
  coarseTargetFintype := inferInstance
  coarseTargetDecidableEq := inferInstance
  coarseTargetEntries := [0, 1]
  coarseTarget_mem_coarseTargetEntries := by
    intro target
    fin_cases target <;> simp
  FineTarget := fineReading.Target
  fineTargetFintype := inferInstance
  fineTargetDecidableEq := inferInstance
  coarseRead := coarseRead
  fineRead := fineReading.read
  coarseRead_surjective := coarseReading.surjective
  fineRead_surjective := fineReading.surjective
  rawCoarserThan := coarse_coarser_fine
  CoarseChart := coarseNerve.Chart
  coarseChartFintype := inferInstance
  coarseChartDecidableEq := inferInstance
  coarseChartEntries := [0, 1]
  coarseChart_mem_coarseChartEntries := by intro chart; fin_cases chart <;> simp
  CoarseEdge := coarseNerve.EdgeComponent
  coarseEdgeFintype := inferInstance
  coarseEdgeDecidableEq := inferInstance
  coarseEdgeEntries := [0, 1, 2]
  coarseEdge_mem_coarseEdgeEntries := by intro edge; fin_cases edge <;> simp
  CoarseFace := coarseNerve.FaceComponent
  coarseFaceFintype := inferInstance
  coarseFaceDecidableEq := inferInstance
  coarseFaceEntries := [PUnit.unit]
  coarseFace_mem_coarseFaceEntries := by intro face; cases face; simp
  coarseEdgeLeft := coarseNerve.edgeLeft
  coarseEdgeRight := coarseNerve.edgeRight
  coarseFaceEdge0 := coarseNerve.faceEdge0
  coarseFaceEdge1 := coarseNerve.faceEdge1
  coarseFaceEdge2 := coarseNerve.faceEdge2
  coarseFaceEdge0_left := coarseSupported.faceEdge0_left
  coarseFaceEdge0_right := coarseSupported.faceEdge0_right
  coarseFaceEdge1_right := coarseSupported.faceEdge1_right
  coarseChartSupport := firingCoarseChartSupportFinset
  coarseChartSupport_nonempty := by
    intro chart
    fin_cases chart <;>
      exact ⟨0, by simp [firingCoarseChartSupportFinset]⟩
  FineChart := fineNerve.Chart
  fineChartFintype := inferInstance
  fineChartDecidableEq := inferInstance
  fineChartEntries := [0, 1, 2]
  fineChart_mem_fineChartEntries := by intro chart; fin_cases chart <;> simp
  FineEdge := fineNerve.EdgeComponent
  fineEdgeFintype := inferInstance
  fineEdgeDecidableEq := inferInstance
  fineEdgeEntries := [0, 1, 2, 3, 4]
  fineEdge_mem_fineEdgeEntries := by intro edge; fin_cases edge <;> simp
  FineFace := fineNerve.FaceComponent
  fineFaceFintype := inferInstance
  fineFaceDecidableEq := inferInstance
  fineFaceEntries := [0, 1]
  fineFace_mem_fineFaceEntries := by intro face; fin_cases face <;> simp
  fineEdgeLeft := fineNerve.edgeLeft
  fineEdgeRight := fineNerve.edgeRight
  fineFaceEdge0 := fineNerve.faceEdge0
  fineFaceEdge1 := fineNerve.faceEdge1
  fineFaceEdge2 := fineNerve.faceEdge2
  fineFaceEdge0_left := fineSupported.faceEdge0_left
  fineFaceEdge0_right := fineSupported.faceEdge0_right
  fineFaceEdge1_right := fineSupported.faceEdge1_right
  fineChartSupport := firingFineChartSupportFinset
  fineChartSupport_nonempty := by
    intro chart
    fin_cases chart <;>
      exact ⟨0, by simp [firingFineChartSupportFinset]⟩
  chartMap := chartMap
  edgeMap := edgeMap
  faceMap := faceMap
  edge_some_left := nerveMorphism.edge_some_left
  edge_some_right := nerveMorphism.edge_some_right
  edge_none_fiber := nerveMorphism.edge_none_fiber
  face_some_edge0 := nerveMorphism.face_some_edge0
  face_some_edge1 := nerveMorphism.face_some_edge1
  face_some_edge2 := nerveMorphism.face_some_edge2
  face_none_edge0 := nerveMorphism.face_none_edge0
  face_none_edge1 := nerveMorphism.face_none_edge1
  face_none_edge2 := nerveMorphism.face_none_edge2
  chartSupport_compatible_source := by
    intro fineChart source htarget
    rw [mem_firingFineChartSupportFinset_iff] at htarget
    rw [mem_firingCoarseChartSupportFinset_iff]
    simpa only [comparisonFactor_eq_coarseRead] using
      nerveMorphism.chartSupport_compatible fineChart source htarget

/-! ## Fieldwise correspondence with G-104 -/

/-- Normalize the executable coarse reading to the reviewed firing reading. -/
@[simp] theorem pFire_coarseRead_apply (source : Source) :
    pFire.coarseRead source = coarseRead source := rfl

/-- Normalize the executable fine reading to the reviewed firing reading. -/
@[simp] theorem pFire_fineRead_apply (source : Source) :
    pFire.fineRead source = fineReading.read source := rfl

/-- Normalize an executable coarse left endpoint to the reviewed endpoint. -/
@[simp] theorem pFire_coarseEdgeLeft_apply (edge : coarseNerve.EdgeComponent) :
    pFire.coarseEdgeLeft edge = coarseNerve.edgeLeft edge := rfl

/-- Normalize an executable coarse right endpoint to the reviewed endpoint. -/
@[simp] theorem pFire_coarseEdgeRight_apply (edge : coarseNerve.EdgeComponent) :
    pFire.coarseEdgeRight edge = coarseNerve.edgeRight edge := rfl

/-- Normalize executable coarse face incidence zero to the reviewed incidence. -/
@[simp] theorem pFire_coarseFaceEdge0_apply (face : coarseNerve.FaceComponent) :
    pFire.coarseFaceEdge0 face = coarseNerve.faceEdge0 face := rfl

/-- Normalize executable coarse face incidence one to the reviewed incidence. -/
@[simp] theorem pFire_coarseFaceEdge1_apply (face : coarseNerve.FaceComponent) :
    pFire.coarseFaceEdge1 face = coarseNerve.faceEdge1 face := rfl

/-- Normalize executable coarse face incidence two to the reviewed incidence. -/
@[simp] theorem pFire_coarseFaceEdge2_apply (face : coarseNerve.FaceComponent) :
    pFire.coarseFaceEdge2 face = coarseNerve.faceEdge2 face := rfl

/-- Normalize an executable fine left endpoint to the reviewed endpoint. -/
@[simp] theorem pFire_fineEdgeLeft_apply (edge : fineNerve.EdgeComponent) :
    pFire.fineEdgeLeft edge = fineNerve.edgeLeft edge := rfl

/-- Normalize an executable fine right endpoint to the reviewed endpoint. -/
@[simp] theorem pFire_fineEdgeRight_apply (edge : fineNerve.EdgeComponent) :
    pFire.fineEdgeRight edge = fineNerve.edgeRight edge := rfl

/-- Normalize executable fine face incidence zero to the reviewed incidence. -/
@[simp] theorem pFire_fineFaceEdge0_apply (face : fineNerve.FaceComponent) :
    pFire.fineFaceEdge0 face = fineNerve.faceEdge0 face := rfl

/-- Normalize executable fine face incidence one to the reviewed incidence. -/
@[simp] theorem pFire_fineFaceEdge1_apply (face : fineNerve.FaceComponent) :
    pFire.fineFaceEdge1 face = fineNerve.faceEdge1 face := rfl

/-- Normalize executable fine face incidence two to the reviewed incidence. -/
@[simp] theorem pFire_fineFaceEdge2_apply (face : fineNerve.FaceComponent) :
    pFire.fineFaceEdge2 face = fineNerve.faceEdge2 face := rfl

/-- Normalize the executable chart map to the reviewed firing chart map. -/
@[simp] theorem pFire_chartMap_apply (chart : fineNerve.Chart) :
    pFire.chartMap chart = chartMap chart := rfl

/-- Normalize the executable partial edge map to the reviewed partial map. -/
@[simp] theorem pFire_edgeMap_apply (edge : fineNerve.EdgeComponent) :
    pFire.edgeMap edge = edgeMap edge := rfl

/-- Normalize the executable partial face map to the reviewed partial map. -/
@[simp] theorem pFire_faceMap_apply (face : fineNerve.FaceComponent) :
    pFire.faceMap face = faceMap face := rfl

/-- The executable representative search recovers the reviewed quotient map. -/
theorem pFire_computedFactor_eq_coarseRead :
    pFire.computedFactor = coarseRead := by
  rw [pFire.computedFactor_eq_comparisonFactor]
  exact comparisonFactor_eq_coarseRead

private theorem subset_cases (A : Finset pFire.CoarseTarget) :
    A = ∅ ∨ A = {(0 : coarseReading.Target)} ∨
      A = {(1 : coarseReading.Target)} ∨ A = Finset.univ := by
  fin_cases A <;> decide

/-- Cycle 12 firing support helper: raw fine-edge support and the canonical
factor place every fine edge in a subset containing coarse target zero. -/
private theorem fineEdge_mem_of_zero_mem
    (A : Finset coarseReading.Target) (hzero : (0 : coarseReading.Target) ∈ A)
    (edge : fineNerve.EdgeComponent) : edge ∈ pFire.fineEdgesIn A := by
  apply (pFire.mem_fineEdgesIn_iff_raw A edge).2
  refine ⟨(0 : fineReading.Target), ?_, ?_⟩
  · rw [pFire.mem_fineEdgeSupportFinset_iff_raw]
    fin_cases edge <;>
      simp [pFire, firingFineChartSupportFinset, fineNerve]
  · rw [pFire_computedFactor_eq_coarseRead]
    simpa [coarseRead] using hzero

/-- Cycle 12 firing support helper: raw face support and the canonical factor
place every fine face in a subset containing coarse target zero. -/
private theorem fineFace_mem_of_zero_mem
    (A : Finset coarseReading.Target) (hzero : (0 : coarseReading.Target) ∈ A)
    (face : fineNerve.FaceComponent) : face ∈ pFire.fineFacesIn A := by
  apply (pFire.mem_fineFacesIn_iff_raw A face).2
  refine ⟨(0 : fineReading.Target), ?_, ?_⟩
  · rw [pFire.mem_fineFaceSupportFinset_iff_raw]
    simp only [pFire.mem_fineEdgeSupportFinset_iff_raw]
    fin_cases face <;>
      simp [pFire, firingFineChartSupportFinset, fineNerve]
  · rw [pFire_computedFactor_eq_coarseRead]
    simpa [coarseRead] using hzero

/-- Cycle 12 firing support helper: raw chart support and the canonical factor
place every fine chart in a subset containing coarse target zero. -/
private theorem fineChart_mem_of_zero_mem
    (A : Finset coarseReading.Target) (hzero : (0 : coarseReading.Target) ∈ A)
    (chart : fineNerve.Chart) : chart ∈ pFire.fineChartsIn A := by
  apply (pFire.mem_fineChartsIn_iff_raw A chart).2
  refine ⟨(0 : fineReading.Target), ?_, ?_⟩
  · fin_cases chart <;> simp [pFire, firingFineChartSupportFinset]
  · rw [pFire_computedFactor_eq_coarseRead]
    simpa [coarseRead] using hzero

/-- Cycle 12 firing support helper: raw coarse-chart support selects every
coarse chart in a subset containing target zero. -/
private theorem coarseChart_mem_of_zero_mem
    (A : Finset coarseReading.Target) (hzero : (0 : coarseReading.Target) ∈ A)
    (chart : coarseNerve.Chart) : chart ∈ pFire.coarseChartsIn A := by
  apply (pFire.mem_coarseChartsIn_iff_raw A chart).2
  refine ⟨(0 : coarseReading.Target), ?_, hzero⟩
  fin_cases chart <;> simp [pFire, firingCoarseChartSupportFinset]

private def fullFineChartEquiv (A : Finset coarseReading.Target)
    (hzero : (0 : coarseReading.Target) ∈ A) :
    fineNerve.Chart ≃ pFire.FineChartIn A where
  toFun chart := ⟨chart, fineChart_mem_of_zero_mem A hzero chart⟩
  invFun chart := chart.1
  left_inv _ := rfl
  right_inv _ := Subtype.ext rfl

private def fullCoarseChartEquiv (A : Finset coarseReading.Target)
    (hzero : (0 : coarseReading.Target) ∈ A) :
    coarseNerve.Chart ≃ pFire.CoarseChartIn A where
  toFun chart := ⟨chart, coarseChart_mem_of_zero_mem A hzero chart⟩
  invFun chart := chart.1
  left_inv _ := rfl
  right_inv _ := Subtype.ext rfl

@[simp] private theorem fullFineChartEquiv_val
    (A : Finset coarseReading.Target) (hzero : (0 : coarseReading.Target) ∈ A)
    (chart : fineNerve.Chart) : (fullFineChartEquiv A hzero chart).1 = chart := rfl

@[simp] private theorem fullCoarseChartEquiv_val
    (A : Finset coarseReading.Target) (hzero : (0 : coarseReading.Target) ∈ A)
    (chart : coarseNerve.Chart) :
    (fullCoarseChartEquiv A hzero chart).1 = chart := rfl

private def fullFineEdgeEquiv (A : Finset coarseReading.Target)
    (hzero : (0 : coarseReading.Target) ∈ A) :
    fineNerve.EdgeComponent ≃ pFire.FineEdgeIn A where
  toFun edge := ⟨edge, fineEdge_mem_of_zero_mem A hzero edge⟩
  invFun edge := edge.1
  left_inv _ := rfl
  right_inv _ := Subtype.ext rfl

private def fullFineFaceEquiv (A : Finset coarseReading.Target)
    (hzero : (0 : coarseReading.Target) ∈ A) :
    fineNerve.FaceComponent ≃ pFire.FineFaceIn A where
  toFun face := ⟨face, fineFace_mem_of_zero_mem A hzero face⟩
  invFun face := face.1
  left_inv _ := rfl
  right_inv _ := Subtype.ext rfl

@[simp] private theorem fullFineEdgeEquiv_val
    (A : Finset coarseReading.Target) (hzero : (0 : coarseReading.Target) ∈ A)
    (edge : fineNerve.EdgeComponent) : (fullFineEdgeEquiv A hzero edge).1 = edge := rfl

@[simp] private theorem fullFineFaceEquiv_val
    (A : Finset coarseReading.Target) (hzero : (0 : coarseReading.Target) ∈ A)
    (face : fineNerve.FaceComponent) : (fullFineFaceEquiv A hzero face).1 = face := rfl

private theorem full_rawFiberEdge_iff
    (A : Finset coarseReading.Target) (hzero : (0 : coarseReading.Target) ∈ A)
    (coarseChart : coarseNerve.Chart) (edge : fineNerve.EdgeComponent) :
    pFire.rawFiberEdge A (fullCoarseChartEquiv A hzero coarseChart)
        (fullFineEdgeEquiv A hzero edge) ↔
      chartMap (fineNerve.edgeLeft edge) = coarseChart ∧
        chartMap (fineNerve.edgeRight edge) = coarseChart := by
  simp [FiniteComparisonPresentation.rawFiberEdge,
    FiniteComparisonPresentation.chartMapIn,
    FiniteComparisonPresentation.fineEdgeLeftIn,
    FiniteComparisonPresentation.fineEdgeRightIn, fullCoarseChartEquiv,
    fullFineEdgeEquiv, pFire]

private theorem full_rawFiberIncoming_formula
    (A : Finset coarseReading.Target) (hzero : (0 : coarseReading.Target) ∈ A)
    (chain : pFire.FineEdgeIn A → ℚ) (chart : fineNerve.Chart) :
    pFire.rawFiberIncoming A chain (fullFineChartEquiv A hzero chart) =
      ∑ edge : fineNerve.EdgeComponent,
        if fineNerve.edgeRight edge = chart then
          chain (fullFineEdgeEquiv A hzero edge) else 0 := by
  rw [pFire.rawFiberIncoming_apply]
  rw [← (fullFineEdgeEquiv A hzero).sum_comp]
  apply Finset.sum_congr rfl
  intro edge _hedge
  simp [fullFineChartEquiv, fullFineEdgeEquiv,
    FiniteComparisonPresentation.fineEdgeRightIn, pFire]

private theorem full_rawFiberOutgoing_formula
    (A : Finset coarseReading.Target) (hzero : (0 : coarseReading.Target) ∈ A)
    (chain : pFire.FineEdgeIn A → ℚ) (chart : fineNerve.Chart) :
    pFire.rawFiberOutgoing A chain (fullFineChartEquiv A hzero chart) =
      ∑ edge : fineNerve.EdgeComponent,
        if fineNerve.edgeLeft edge = chart then
          chain (fullFineEdgeEquiv A hzero edge) else 0 := by
  rw [pFire.rawFiberOutgoing_apply]
  rw [← (fullFineEdgeEquiv A hzero).sum_comp]
  apply Finset.sum_congr rfl
  intro edge _hedge
  simp [fullFineChartEquiv, fullFineEdgeEquiv,
    FiniteComparisonPresentation.fineEdgeLeftIn, pFire]

private theorem full_internalFaceBoundary_formula
    (A : Finset coarseReading.Target) (hzero : (0 : coarseReading.Target) ∈ A)
    (coarseChart : coarseNerve.Chart) (faces : pFire.FineFaceIn A → ℚ)
    (edge : fineNerve.EdgeComponent) :
    pFire.internalFaceBoundaryLinearMap A
        (fullCoarseChartEquiv A hzero coarseChart) faces
        (fullFineEdgeEquiv A hzero edge) =
      (∑ face : fineNerve.FaceComponent,
        if fineNerve.faceEdge0 face = edge then
          pFire.maskedInternalFaceChain A
            (fullCoarseChartEquiv A hzero coarseChart) faces
            (fullFineFaceEquiv A hzero face) else 0) -
      (∑ face : fineNerve.FaceComponent,
        if fineNerve.faceEdge1 face = edge then
          pFire.maskedInternalFaceChain A
            (fullCoarseChartEquiv A hzero coarseChart) faces
            (fullFineFaceEquiv A hzero face) else 0) +
      ∑ face : fineNerve.FaceComponent,
        if fineNerve.faceEdge2 face = edge then
          pFire.maskedInternalFaceChain A
            (fullCoarseChartEquiv A hzero coarseChart) faces
            (fullFineFaceEquiv A hzero face) else 0 := by
  rw [pFire.internalFaceBoundaryLinearMap_apply]
  rw [← (fullFineFaceEquiv A hzero).sum_comp]
  rw [← (fullFineFaceEquiv A hzero).sum_comp]
  rw [← (fullFineFaceEquiv A hzero).sum_comp]
  simp [fullFineFaceEquiv, fullFineEdgeEquiv,
    FiniteComparisonPresentation.fineFaceEdge0In,
    FiniteComparisonPresentation.fineFaceEdge1In,
    FiniteComparisonPresentation.fineFaceEdge2In, pFire]

private theorem full_rawInternalFace_zero
    (A : Finset coarseReading.Target) (hzero : (0 : coarseReading.Target) ∈ A)
    (face : fineNerve.FaceComponent) :
    pFire.rawInternalFace A (fullCoarseChartEquiv A hzero 0)
      (fullFineFaceEquiv A hzero face) := by
  fin_cases face <;>
    simp [FiniteComparisonPresentation.rawInternalFace,
      FiniteComparisonPresentation.rawFiberEdge,
      FiniteComparisonPresentation.chartMapIn,
      FiniteComparisonPresentation.fineEdgeLeftIn,
      FiniteComparisonPresentation.fineEdgeRightIn,
      FiniteComparisonPresentation.fineFaceEdge0In,
      FiniteComparisonPresentation.fineFaceEdge1In,
      FiniteComparisonPresentation.fineFaceEdge2In, fullCoarseChartEquiv,
      fullFineFaceEquiv, pFire, fineNerve, chartMap]

private theorem full_not_rawFiberEdge_one
    (A : Finset coarseReading.Target) (hzero : (0 : coarseReading.Target) ∈ A)
    (edge : fineNerve.EdgeComponent) :
    ¬ pFire.rawFiberEdge A (fullCoarseChartEquiv A hzero 1)
      (fullFineEdgeEquiv A hzero edge) := by
  apply (not_congr (full_rawFiberEdge_iff A hzero 1 edge)).2
  fin_cases edge <;> simp [fineNerve, chartMap]

private theorem rawConditionC3At_of_zero_mem
    (A : Finset coarseReading.Target) (hzero : (0 : coarseReading.Target) ∈ A) :
    pFire.RawConditionC3At A := by
  intro coarseChart chain hcycle
  obtain ⟨coarseCell, rfl⟩ := (fullCoarseChartEquiv A hzero).surjective coarseChart
  fin_cases coarseCell
  · change pFire.fiberCycleConstraintLinearMap A
        (fullCoarseChartEquiv A hzero 0) chain = 0 at hcycle
    change ∃ faces, pFire.internalFaceBoundaryLinearMap A
      (fullCoarseChartEquiv A hzero 0) faces = chain
    let edge0 := fullFineEdgeEquiv A hzero (0 : fineNerve.EdgeComponent)
    let edge1 := fullFineEdgeEquiv A hzero (1 : fineNerve.EdgeComponent)
    let edge2 := fullFineEdgeEquiv A hzero (2 : fineNerve.EdgeComponent)
    let edge3 := fullFineEdgeEquiv A hzero (3 : fineNerve.EdgeComponent)
    let edge4 := fullFineEdgeEquiv A hzero (4 : fineNerve.EdgeComponent)
    let chart1 := fullFineChartEquiv A hzero (1 : fineNerve.Chart)
    have h0 : chain edge0 = 0 := by
      have hrow := congrFun hcycle (Sum.inl edge0)
      simp only [Pi.zero_apply] at hrow
      rw [pFire.fiberCycleConstraintLinearMap_apply_inl] at hrow
      have houtside :
          ¬ pFire.rawFiberEdge A (fullCoarseChartEquiv A hzero 0) edge0 := by
        simpa [edge0, fineNerve, chartMap] using
          not_congr (full_rawFiberEdge_iff A hzero 0 0)
      rw [if_neg houtside] at hrow
      exact hrow
    have h1 : chain edge1 = 0 := by
      have hrow := congrFun hcycle (Sum.inl edge1)
      simp only [Pi.zero_apply] at hrow
      rw [pFire.fiberCycleConstraintLinearMap_apply_inl] at hrow
      have houtside :
          ¬ pFire.rawFiberEdge A (fullCoarseChartEquiv A hzero 0) edge1 := by
        simpa [edge1, fineNerve, chartMap] using
          not_congr (full_rawFiberEdge_iff A hzero 0 1)
      rw [if_neg houtside] at hrow
      exact hrow
    have h3 : chain edge3 = 0 := by
      have hrow := congrFun hcycle (Sum.inr chart1)
      simp only [Pi.zero_apply] at hrow
      rw [pFire.fiberCycleConstraintLinearMap_apply_inr] at hrow
      have hmap :
          pFire.chartMapIn A chart1 = fullCoarseChartEquiv A hzero 0 := by
        apply Subtype.ext
        simp [chart1, fullFineChartEquiv, fullCoarseChartEquiv,
          FiniteComparisonPresentation.chartMapIn, pFire, chartMap]
      rw [if_pos hmap] at hrow
      change pFire.rawFiberIncoming A chain
          (fullFineChartEquiv A hzero 1) -
        pFire.rawFiberOutgoing A chain (fullFineChartEquiv A hzero 1) = 0
        at hrow
      rw [full_rawFiberIncoming_formula A hzero chain 1,
        full_rawFiberOutgoing_formula A hzero chain 1] at hrow
      simpa [edge0, edge1, edge2, edge3, edge4, chart1, fineNerve,
        Fin.sum_univ_succ, h0, h1] using hrow
    let faces : pFire.FineFaceIn A → ℚ := fun face =>
      if face.1 = (0 : fineNerve.FaceComponent) then chain edge2
      else chain edge4
    have hface0 := full_rawInternalFace_zero A hzero
      (0 : fineNerve.FaceComponent)
    have hface1 := full_rawInternalFace_zero A hzero
      (1 : fineNerve.FaceComponent)
    have hfaceNe : (1 : fineNerve.FaceComponent) ≠ 0 := by decide
    refine ⟨faces, ?_⟩
    funext edge
    obtain ⟨edgeCell, rfl⟩ := (fullFineEdgeEquiv A hzero).surjective edge
    fin_cases edgeCell <;>
      rw [full_internalFaceBoundary_formula] <;>
      simp [FiniteComparisonPresentation.maskedInternalFaceChain,
        hface0, hface1, fineNerve, Fin.sum_univ_succ] <;>
      simp [faces, fullFineFaceEquiv, edge0, edge1, edge2, edge3, edge4,
        hfaceNe, h0, h1, h3]
  · change pFire.fiberCycleConstraintLinearMap A
        (fullCoarseChartEquiv A hzero 1) chain = 0 at hcycle
    change ∃ faces, pFire.internalFaceBoundaryLinearMap A
      (fullCoarseChartEquiv A hzero 1) faces = chain
    have hchain : chain = 0 := by
      funext edge
      obtain ⟨edgeCell, rfl⟩ := (fullFineEdgeEquiv A hzero).surjective edge
      have hrow := congrFun hcycle
        (Sum.inl (fullFineEdgeEquiv A hzero edgeCell))
      simp only [Pi.zero_apply] at hrow
      rw [pFire.fiberCycleConstraintLinearMap_apply_inl] at hrow
      have houtside :
          ¬ pFire.rawFiberEdge A (fullCoarseChartEquiv A hzero 1)
            (fullFineEdgeEquiv A hzero edgeCell) :=
        full_not_rawFiberEdge_one A hzero edgeCell
      rw [if_neg houtside] at hrow
      exact hrow
    refine ⟨0, ?_⟩
    simp [hchain]

private abbrev oneSubset : Finset coarseReading.Target := {1}

private def oneCoarseChart : pFire.CoarseChartIn oneSubset :=
  ⟨(0 : coarseNerve.Chart), by decide⟩

private def oneFineEdge : pFire.FineEdgeIn oneSubset :=
  ⟨(2 : fineNerve.EdgeComponent), by decide⟩

private def oneFineFace : pFire.FineFaceIn oneSubset :=
  ⟨(0 : fineNerve.FaceComponent), by decide⟩

/-- Cycle 12 singleton-subset helper: raw selected-chart membership identifies
every coarse chart over target one with the named representative. -/
private theorem oneCoarseChart_eq (chart : pFire.CoarseChartIn oneSubset) :
    chart = oneCoarseChart := by
  rcases chart with ⟨chart, hchart⟩
  have hselected := (pFire.mem_coarseChartsIn_iff_raw oneSubset chart).1 hchart
  apply Subtype.ext
  fin_cases chart
  · rfl
  · simp [pFire, firingCoarseChartSupportFinset, oneSubset] at hselected

private theorem oneFineEdge_eq (edge : pFire.FineEdgeIn oneSubset) :
    edge = oneFineEdge := by
  rcases edge with ⟨edge, hedge⟩
  apply Subtype.ext
  fin_cases edge
  all_goals first | rfl | (exfalso; revert hedge; decide)

private theorem oneFineFace_eq (face : pFire.FineFaceIn oneSubset) :
    face = oneFineFace := by
  rcases face with ⟨face, hface⟩
  apply Subtype.ext
  fin_cases face
  · rfl
  · exfalso
    revert hface
    decide

private def oneFineFaceEquiv : Unit ≃ pFire.FineFaceIn oneSubset where
  toFun _ := oneFineFace
  invFun _ := ()
  left_inv _ := Subsingleton.elim _ _
  right_inv face := (oneFineFace_eq face).symm

@[simp] private theorem oneFineFaceEdge0In :
    pFire.fineFaceEdge0In oneSubset oneFineFace = oneFineEdge := by
  apply Subtype.ext
  rfl

@[simp] private theorem oneFineFaceEdge1In :
    pFire.fineFaceEdge1In oneSubset oneFineFace = oneFineEdge := by
  apply Subtype.ext
  rfl

@[simp] private theorem oneFineFaceEdge2In :
    pFire.fineFaceEdge2In oneSubset oneFineFace = oneFineEdge := by
  apply Subtype.ext
  rfl

private theorem one_rawInternalFace :
    pFire.rawInternalFace oneSubset oneCoarseChart oneFineFace := by
  decide

private theorem rawConditionC3At_oneSubset :
    pFire.RawConditionC3At oneSubset := by
  intro coarseChart chain _hcycle
  rw [oneCoarseChart_eq coarseChart]
  let faces : pFire.FineFaceIn oneSubset → ℚ := fun _ => chain oneFineEdge
  refine ⟨faces, ?_⟩
  funext edge
  rw [oneFineEdge_eq edge]
  rw [pFire.internalFaceBoundaryLinearMap_apply]
  rw [← oneFineFaceEquiv.sum_comp]
  rw [← oneFineFaceEquiv.sum_comp]
  rw [← oneFineFaceEquiv.sum_comp]
  simp [oneFineFaceEquiv, FiniteComparisonPresentation.maskedInternalFaceChain,
    one_rawInternalFace, faces]

private theorem rawSubsetClauses
    (A : Finset pFire.CoarseTarget) (hA : A.Nonempty) :
    pFire.RawConditionC1At A ∧
      pFire.RawConditionC2At A ∧
      pFire.RawConditionC3At A ∧
      pFire.RawConditionC4At A := by
  rcases subset_cases A with hEmpty | hZero | hOne | hUniv
  · subst A
    exact (Finset.not_nonempty_empty hA).elim
  · subst A
    exact ⟨by decide, by decide,
      rawConditionC3At_of_zero_mem {0} (by simp), by decide⟩
  · subst A
    exact ⟨by decide, by decide, rawConditionC3At_oneSubset, by decide⟩
  · subst A
    exact ⟨by decide, by decide,
      rawConditionC3At_of_zero_mem Finset.univ (by simp), by decide⟩

private theorem semanticFiniteSubsetClauses
    (A : Finset pFire.CoarseTarget) (hA : A.Nonempty) :
    pFire.toGeometry.ConditionC1AtTargetSubset (A : Set pFire.CoarseTarget) ∧
      pFire.toGeometry.ConditionC2AtTargetSubset (A : Set pFire.CoarseTarget) ∧
      pFire.toGeometry.ConditionC3AtTargetSubset (A : Set pFire.CoarseTarget) ∧
      pFire.toGeometry.ConditionC4AtTargetSubset
        (A : Set pFire.CoarseTarget) := by
  obtain ⟨h1, h2, h3, h4⟩ := rawSubsetClauses A hA
  exact ⟨(pFire.rawConditionC1At_iff_conditionC1AtTargetSubset A).1 h1,
    (pFire.rawConditionC2At_iff_conditionC2AtTargetSubset A).1 h2,
    (pFire.rawConditionC3At_iff_conditionC3AtTargetSubset A).1 h3,
    (pFire.rawConditionC4At_iff_conditionC4AtTargetSubset A).1 h4⟩

/-- The raw presentation satisfies the semantic all-subset Atlas condition. -/
theorem pFire_conditionCAllA : pFire.toGeometry.ConditionCAllA := by
  apply pFire.toGeometry.conditionCAllA_intro
  · apply pFire.rawConditionC0_iff_conditionC0.mp
    decide
  · exact pFire.allNonemptyFiniteSubsetClauses_iff.mp semanticFiniteSubsetClauses
  · apply pFire.rawConditionC5_iff_conditionC5.mp
    decide
  · apply pFire.rawConditionC6_iff_conditionC6.mp
    decide

/-- The generic executable checker fires on the raw G-104 presentation. -/
theorem pFire_conditionCAllACheck : pFire.conditionCAllACheck = true :=
  pFire.conditionCAllACheck_eq_true_iff.mpr pFire_conditionCAllA

private def actualFullCoarseChartEquiv
    (A : Set coarseReading.Target) (hzero : (0 : coarseReading.Target) ∈ A) :
    coarseNerve.Chart ≃ coarseSupported.ChartInTargetSubset A where
  toFun chart := ⟨chart, (0 : coarseReading.Target), by
    fin_cases chart <;> simp [coarseChartSupport], hzero⟩
  invFun chart := chart.1
  left_inv _ := rfl
  right_inv _ := Subtype.ext rfl

private def actualFullFineChartEquiv
    (A : Set coarseReading.Target) (hzero : (0 : coarseReading.Target) ∈ A) :
    fineNerve.Chart ≃ fineSupported.ChartInTargetSubset
      (comparisonFactor coarseReading fineReading coarse_coarser_fine ⁻¹' A) where
  toFun chart := ⟨chart, (0 : fineReading.Target), by
    fin_cases chart <;> simp [fineChartSupport], by
      simpa [comparisonFactor_eq_coarseRead, coarseRead] using hzero⟩
  invFun chart := chart.1
  left_inv _ := rfl
  right_inv _ := Subtype.ext rfl

private def actualFullFineEdgeEquiv
    (A : Set coarseReading.Target) (hzero : (0 : coarseReading.Target) ∈ A) :
    fineNerve.EdgeComponent ≃ fineSupported.EdgeInTargetSubset
      (comparisonFactor coarseReading fineReading coarse_coarser_fine ⁻¹' A) where
  toFun edge := ⟨edge, (0 : fineReading.Target), by
    fin_cases edge <;>
      simp [TargetSupportedNerve.edgeSupport, fineNerve, fineChartSupport], by
        simpa [comparisonFactor_eq_coarseRead, coarseRead] using hzero⟩
  invFun edge := edge.1
  left_inv _ := rfl
  right_inv _ := Subtype.ext rfl

private def actualFullFineFaceEquiv
    (A : Set coarseReading.Target) (hzero : (0 : coarseReading.Target) ∈ A) :
    fineNerve.FaceComponent ≃ fineSupported.FaceInTargetSubset
      (comparisonFactor coarseReading fineReading coarse_coarser_fine ⁻¹' A) where
  toFun face := ⟨face, (0 : fineReading.Target), by
    fin_cases face <;>
      simp [TargetSupportedNerve.faceSupport, TargetSupportedNerve.edgeSupport,
        fineNerve, fineChartSupport], by
          simpa [comparisonFactor_eq_coarseRead, coarseRead] using hzero⟩
  invFun face := face.1
  left_inv _ := rfl
  right_inv _ := Subtype.ext rfl

@[simp] private theorem actualFullCoarseChartEquiv_val
    (A : Set coarseReading.Target) (hzero : (0 : coarseReading.Target) ∈ A)
    (chart : coarseNerve.Chart) :
    (actualFullCoarseChartEquiv A hzero chart).1 = chart := rfl

@[simp] private theorem actualFullFineChartEquiv_val
    (A : Set coarseReading.Target) (hzero : (0 : coarseReading.Target) ∈ A)
    (chart : fineNerve.Chart) :
    (actualFullFineChartEquiv A hzero chart).1 = chart := rfl

@[simp] private theorem actualFullFineEdgeEquiv_val
    (A : Set coarseReading.Target) (hzero : (0 : coarseReading.Target) ∈ A)
    (edge : fineNerve.EdgeComponent) :
    (actualFullFineEdgeEquiv A hzero edge).1 = edge := rfl

@[simp] private theorem actualFullFineFaceEquiv_val
    (A : Set coarseReading.Target) (hzero : (0 : coarseReading.Target) ∈ A)
    (face : fineNerve.FaceComponent) :
    (actualFullFineFaceEquiv A hzero face).1 = face := rfl

private theorem actualFull_chartMap_eq_iff
    (A : Set coarseReading.Target) (hzero : (0 : coarseReading.Target) ∈ A)
    (fineChart : fineNerve.Chart) (coarseChart : coarseNerve.Chart) :
    nerveMorphism.aSubnerveChartMap A
        (actualFullFineChartEquiv A hzero fineChart) =
      actualFullCoarseChartEquiv A hzero coarseChart ↔
        chartMap fineChart = coarseChart := by
  rw [nerveMorphism.aSubnerveChartMap_eq_iff]
  rfl

private theorem actualFull_fiberEdge_iff
    (A : Set coarseReading.Target) (hzero : (0 : coarseReading.Target) ∈ A)
    (coarseChart : coarseNerve.Chart) (edge : fineNerve.EdgeComponent) :
    nerveMorphism.TargetSubsetFiberEdge A
        (actualFullCoarseChartEquiv A hzero coarseChart)
        (actualFullFineEdgeEquiv A hzero edge) ↔
      chartMap (fineNerve.edgeLeft edge) = coarseChart ∧
        chartMap (fineNerve.edgeRight edge) = coarseChart := by
  rw [nerveMorphism.targetSubsetFiberEdge_iff_endpoint_cells]
  rfl

private theorem actualFull_edgeLeft
    (A : Set coarseReading.Target) (hzero : (0 : coarseReading.Target) ∈ A)
    (edge : fineNerve.EdgeComponent) :
    fineSupported.targetSubsetEdgeLeft
        (comparisonFactor coarseReading fineReading coarse_coarser_fine ⁻¹' A)
        (actualFullFineEdgeEquiv A hzero edge) =
      actualFullFineChartEquiv A hzero (fineNerve.edgeLeft edge) := by
  apply Subtype.ext
  rfl

private theorem actualFull_edgeRight
    (A : Set coarseReading.Target) (hzero : (0 : coarseReading.Target) ∈ A)
    (edge : fineNerve.EdgeComponent) :
    fineSupported.targetSubsetEdgeRight
        (comparisonFactor coarseReading fineReading coarse_coarser_fine ⁻¹' A)
        (actualFullFineEdgeEquiv A hzero edge) =
      actualFullFineChartEquiv A hzero (fineNerve.edgeRight edge) := by
  apply Subtype.ext
  rfl

private theorem actualFull_fiberAdjacent_zero_one
    (A : Set coarseReading.Target) (hzero : (0 : coarseReading.Target) ∈ A) :
    nerveMorphism.TargetSubsetFiberAdjacent A
      (actualFullCoarseChartEquiv A hzero 0)
      (actualFullFineChartEquiv A hzero 0)
      (actualFullFineChartEquiv A hzero 1) := by
  let edge3 := actualFullFineEdgeEquiv A hzero (3 : fineNerve.EdgeComponent)
  have hfiber : nerveMorphism.TargetSubsetFiberEdge A
      (actualFullCoarseChartEquiv A hzero 0) edge3 := by
    simpa [edge3, fineNerve, chartMap] using
      (actualFull_fiberEdge_iff A hzero 0 3).2 ⟨rfl, rfl⟩
  have hadjacent := nerveMorphism.targetSubsetFiberAdjacent_of_edge A
    (actualFullCoarseChartEquiv A hzero 0) edge3 hfiber
  simpa [edge3, actualFull_edgeLeft, actualFull_edgeRight, fineNerve] using hadjacent

private theorem actualFull_conditionC1
    (A : Set coarseReading.Target) (hzero : (0 : coarseReading.Target) ∈ A) :
    nerveMorphism.ConditionC1AtTargetSubset A := by
  intro coarseChart
  obtain ⟨coarseCell, rfl⟩ :=
    (actualFullCoarseChartEquiv A hzero).surjective coarseChart
  fin_cases coarseCell
  · change
      (∃ fineChart, nerveMorphism.aSubnerveChartMap A fineChart =
        actualFullCoarseChartEquiv A hzero 0) ∧ _
    constructor
    · exact ⟨actualFullFineChartEquiv A hzero 0,
        (actualFull_chartMap_eq_iff A hzero 0 0).2 (by simp [chartMap])⟩
    · intro left right hleft hright
      obtain ⟨leftCell, rfl⟩ :=
        (actualFullFineChartEquiv A hzero).surjective left
      obtain ⟨rightCell, rfl⟩ :=
        (actualFullFineChartEquiv A hzero).surjective right
      rw [actualFull_chartMap_eq_iff] at hleft hright
      fin_cases leftCell <;> fin_cases rightCell <;>
        simp [chartMap] at hleft hright
      all_goals first
        | exact Relation.ReflTransGen.refl
        | exact Relation.ReflTransGen.single
            (actualFull_fiberAdjacent_zero_one A hzero)
        | exact Relation.ReflTransGen.single
            (actualFull_fiberAdjacent_zero_one A hzero).symm
  · change
      (∃ fineChart, nerveMorphism.aSubnerveChartMap A fineChart =
        actualFullCoarseChartEquiv A hzero 1) ∧ _
    constructor
    · exact ⟨actualFullFineChartEquiv A hzero 2,
        (actualFull_chartMap_eq_iff A hzero 2 1).2 (by simp [chartMap])⟩
    · intro left right hleft hright
      obtain ⟨leftCell, rfl⟩ :=
        (actualFullFineChartEquiv A hzero).surjective left
      obtain ⟨rightCell, rfl⟩ :=
        (actualFullFineChartEquiv A hzero).surjective right
      rw [actualFull_chartMap_eq_iff] at hleft hright
      fin_cases leftCell <;> fin_cases rightCell <;>
        simp [chartMap] at hleft hright
      exact Relation.ReflTransGen.refl

private theorem actualFull_conditionC2
    (A : Set coarseReading.Target) (hzero : (0 : coarseReading.Target) ∈ A) :
    nerveMorphism.ConditionC2AtTargetSubset A := by
  intro coarseEdge
  let fineEdge := actualFullFineEdgeEquiv A hzero
    coarseEdge.1.castSucc.castSucc
  refine ⟨fineEdge, ?_⟩
  apply (nerveMorphism.aSubnerveEdgeMapOption_eq_some_iff A
    fineEdge coarseEdge).2
  rcases coarseEdge with ⟨coarseEdge, _hsupport⟩
  fin_cases coarseEdge <;>
    simp [fineEdge, actualFullFineEdgeEquiv, edgeMap]

private theorem actualFull_conditionC4
    (A : Set coarseReading.Target) (hzero : (0 : coarseReading.Target) ∈ A) :
    nerveMorphism.ConditionC4AtTargetSubset A := by
  intro coarseFace
  let fineFace := actualFullFineFaceEquiv A hzero
    (0 : fineNerve.FaceComponent)
  refine ⟨fineFace, ?_⟩
  apply (nerveMorphism.aSubnerveFaceMapOption_eq_some_iff A
    fineFace coarseFace).2
  cases coarseFace.1
  simp [fineFace, actualFullFineFaceEquiv, faceMap]

private theorem actualFull_incoming_formula
    (A : Set coarseReading.Target) (hzero : (0 : coarseReading.Target) ∈ A)
    (chain : fineSupported.EdgeInTargetSubset
      (comparisonFactor coarseReading fineReading coarse_coarser_fine ⁻¹' A) → ℚ)
    (chart : fineNerve.Chart) :
    TargetSupportedNerveMorphism.targetSubsetFiberIncoming fineSupported
        (comparisonFactor coarseReading fineReading coarse_coarser_fine ⁻¹' A)
        chain (actualFullFineChartEquiv A hzero chart) =
      ∑ edge : fineNerve.EdgeComponent,
        if fineNerve.edgeRight edge = chart then
          chain (actualFullFineEdgeEquiv A hzero edge) else 0 := by
  classical
  letI : Fintype (fineSupported.EdgeInTargetSubset
      (comparisonFactor coarseReading fineReading coarse_coarser_fine ⁻¹' A)) :=
    @Subtype.fintype
      fineSupported.nerve.EdgeComponent
      (fun edge => ∃ target ∈ fineSupported.edgeSupport edge,
        target ∈ comparisonFactor coarseReading fineReading
          coarse_coarser_fine ⁻¹' A)
      (fun _ => Classical.propDecidable _)
      fineSupported.edgeFintype
  rw [TargetSupportedNerveMorphism.targetSubsetFiberIncoming_apply]
  symm
  apply Fintype.sum_equiv (actualFullFineEdgeEquiv A hzero)
  intro edge
  rw [actualFull_edgeRight]
  simp

private theorem actualFull_outgoing_formula
    (A : Set coarseReading.Target) (hzero : (0 : coarseReading.Target) ∈ A)
    (chain : fineSupported.EdgeInTargetSubset
      (comparisonFactor coarseReading fineReading coarse_coarser_fine ⁻¹' A) → ℚ)
    (chart : fineNerve.Chart) :
    TargetSupportedNerveMorphism.targetSubsetFiberOutgoing fineSupported
        (comparisonFactor coarseReading fineReading coarse_coarser_fine ⁻¹' A)
        chain (actualFullFineChartEquiv A hzero chart) =
      ∑ edge : fineNerve.EdgeComponent,
        if fineNerve.edgeLeft edge = chart then
          chain (actualFullFineEdgeEquiv A hzero edge) else 0 := by
  classical
  letI : Fintype (fineSupported.EdgeInTargetSubset
      (comparisonFactor coarseReading fineReading coarse_coarser_fine ⁻¹' A)) :=
    @Subtype.fintype
      fineSupported.nerve.EdgeComponent
      (fun edge => ∃ target ∈ fineSupported.edgeSupport edge,
        target ∈ comparisonFactor coarseReading fineReading
          coarse_coarser_fine ⁻¹' A)
      (fun _ => Classical.propDecidable _)
      fineSupported.edgeFintype
  rw [TargetSupportedNerveMorphism.targetSubsetFiberOutgoing_apply]
  symm
  apply Fintype.sum_equiv (actualFullFineEdgeEquiv A hzero)
  intro edge
  rw [actualFull_edgeLeft]
  simp

private theorem actualFull_faceEdge0
    (A : Set coarseReading.Target) (hzero : (0 : coarseReading.Target) ∈ A)
    (face : fineNerve.FaceComponent) :
    fineSupported.targetSubsetFaceEdge0
        (comparisonFactor coarseReading fineReading coarse_coarser_fine ⁻¹' A)
        (actualFullFineFaceEquiv A hzero face) =
      actualFullFineEdgeEquiv A hzero (fineNerve.faceEdge0 face) := by
  apply Subtype.ext
  rfl

private theorem actualFull_faceEdge1
    (A : Set coarseReading.Target) (hzero : (0 : coarseReading.Target) ∈ A)
    (face : fineNerve.FaceComponent) :
    fineSupported.targetSubsetFaceEdge1
        (comparisonFactor coarseReading fineReading coarse_coarser_fine ⁻¹' A)
        (actualFullFineFaceEquiv A hzero face) =
      actualFullFineEdgeEquiv A hzero (fineNerve.faceEdge1 face) := by
  apply Subtype.ext
  rfl

private theorem actualFull_faceEdge2
    (A : Set coarseReading.Target) (hzero : (0 : coarseReading.Target) ∈ A)
    (face : fineNerve.FaceComponent) :
    fineSupported.targetSubsetFaceEdge2
        (comparisonFactor coarseReading fineReading coarse_coarser_fine ⁻¹' A)
        (actualFullFineFaceEquiv A hzero face) =
      actualFullFineEdgeEquiv A hzero (fineNerve.faceEdge2 face) := by
  apply Subtype.ext
  rfl

private theorem actualFull_faceBoundary_formula
    (A : Set coarseReading.Target) (hzero : (0 : coarseReading.Target) ∈ A)
    (faces : fineSupported.FaceInTargetSubset
      (comparisonFactor coarseReading fineReading coarse_coarser_fine ⁻¹' A) → ℚ)
    (edge : fineNerve.EdgeComponent) :
    TargetSupportedNerveMorphism.targetSubsetFaceBoundary fineSupported
        (comparisonFactor coarseReading fineReading coarse_coarser_fine ⁻¹' A)
        faces (actualFullFineEdgeEquiv A hzero edge) =
      (∑ face : fineNerve.FaceComponent,
        if fineNerve.faceEdge0 face = edge then
          faces (actualFullFineFaceEquiv A hzero face) else 0) -
      (∑ face : fineNerve.FaceComponent,
        if fineNerve.faceEdge1 face = edge then
          faces (actualFullFineFaceEquiv A hzero face) else 0) +
      ∑ face : fineNerve.FaceComponent,
        if fineNerve.faceEdge2 face = edge then
          faces (actualFullFineFaceEquiv A hzero face) else 0 := by
  classical
  letI actualFaceFintype : Fintype (fineSupported.FaceInTargetSubset
      (comparisonFactor coarseReading fineReading coarse_coarser_fine ⁻¹' A)) :=
    @Subtype.fintype
      fineSupported.nerve.FaceComponent
      (fun face => ∃ target ∈ fineSupported.faceSupport face,
        target ∈ comparisonFactor coarseReading fineReading
          coarse_coarser_fine ⁻¹' A)
      (fun _ => Classical.propDecidable _)
      fineSupported.faceFintype
  letI actualEdgeDecidable : DecidableEq (fineSupported.EdgeInTargetSubset
      (comparisonFactor coarseReading fineReading coarse_coarser_fine ⁻¹' A)) :=
    @Subtype.instDecidableEq
      fineSupported.nerve.EdgeComponent
      (fun edge => ∃ target ∈ fineSupported.edgeSupport edge,
        target ∈ comparisonFactor coarseReading fineReading
          coarse_coarser_fine ⁻¹' A)
      (fun _ _ => Classical.propDecidable _)
  rw [TargetSupportedNerveMorphism.targetSubsetFaceBoundary_apply]
  have hsum0 :
      (∑ face,
        if fineSupported.targetSubsetFaceEdge0
            (comparisonFactor coarseReading fineReading coarse_coarser_fine ⁻¹' A)
            face = actualFullFineEdgeEquiv A hzero edge then faces face else 0) =
      ∑ face : fineNerve.FaceComponent,
        if fineNerve.faceEdge0 face = edge then
          faces (actualFullFineFaceEquiv A hzero face) else 0 := by
    symm
    apply Fintype.sum_equiv (actualFullFineFaceEquiv A hzero)
    intro face
    rw [actualFull_faceEdge0]
    simp
  have hsum1 :
      (∑ face,
        if fineSupported.targetSubsetFaceEdge1
            (comparisonFactor coarseReading fineReading coarse_coarser_fine ⁻¹' A)
            face = actualFullFineEdgeEquiv A hzero edge then faces face else 0) =
      ∑ face : fineNerve.FaceComponent,
        if fineNerve.faceEdge1 face = edge then
          faces (actualFullFineFaceEquiv A hzero face) else 0 := by
    symm
    apply Fintype.sum_equiv (actualFullFineFaceEquiv A hzero)
    intro face
    rw [actualFull_faceEdge1]
    simp
  have hsum2 :
      (∑ face,
        if fineSupported.targetSubsetFaceEdge2
            (comparisonFactor coarseReading fineReading coarse_coarser_fine ⁻¹' A)
            face = actualFullFineEdgeEquiv A hzero edge then faces face else 0) =
      ∑ face : fineNerve.FaceComponent,
        if fineNerve.faceEdge2 face = edge then
          faces (actualFullFineFaceEquiv A hzero face) else 0 := by
    symm
    apply Fintype.sum_equiv (actualFullFineFaceEquiv A hzero)
    intro face
    rw [actualFull_faceEdge2]
    simp
  have hcombined := congrArg₂ (fun x y : ℚ => x + y)
    (congrArg₂ (fun x y : ℚ => x - y) hsum0 hsum1) hsum2
  have hdec : actualEdgeDecidable =
      (@Subtype.instDecidableEq
        fineSupported.nerve.EdgeComponent
        (fun edge => ∃ target ∈ fineSupported.edgeSupport edge,
          target ∈ comparisonFactor coarseReading fineReading
            coarse_coarser_fine ⁻¹' A)
        (fun _ _ => Classical.propDecidable _)) :=
    Subsingleton.elim _ _
  rw [hdec] at hcombined
  simpa only [actualFaceFintype] using hcombined

private theorem actualFull_internalFace_zero
    (A : Set coarseReading.Target) (hzero : (0 : coarseReading.Target) ∈ A)
    (face : fineNerve.FaceComponent) :
    nerveMorphism.TargetSubsetInternalFace A
      (actualFullCoarseChartEquiv A hzero 0)
      (actualFullFineFaceEquiv A hzero face) := by
  apply nerveMorphism.targetSubsetInternalFace_mk
  · rw [actualFull_faceEdge0, actualFull_fiberEdge_iff]
    fin_cases face <;> simp [fineNerve, chartMap]
  · rw [actualFull_faceEdge1, actualFull_fiberEdge_iff]
    fin_cases face <;> simp [fineNerve, chartMap]
  · rw [actualFull_faceEdge2, actualFull_fiberEdge_iff]
    fin_cases face <;> simp [fineNerve, chartMap]

private theorem actualFull_conditionC3
    (A : Set coarseReading.Target) (hzero : (0 : coarseReading.Target) ∈ A) :
    nerveMorphism.ConditionC3AtTargetSubset A := by
  intro coarseChart
  obtain ⟨coarseCell, rfl⟩ :=
    (actualFullCoarseChartEquiv A hzero).surjective coarseChart
  intro chain hcycle
  fin_cases coarseCell
  · have h0 : chain (actualFullFineEdgeEquiv A hzero 0) = 0 :=
      hcycle.1 (actualFullFineEdgeEquiv A hzero 0) (by
        rw [actualFull_fiberEdge_iff]
        simp [fineNerve, chartMap])
    have h1 : chain (actualFullFineEdgeEquiv A hzero 1) = 0 :=
      hcycle.1 (actualFullFineEdgeEquiv A hzero 1) (by
        rw [actualFull_fiberEdge_iff]
        simp [fineNerve, chartMap])
    have hconserve := hcycle.2 (actualFullFineChartEquiv A hzero 1)
      ((actualFull_chartMap_eq_iff A hzero 1 0).2 (by simp [chartMap]))
    rw [actualFull_incoming_formula, actualFull_outgoing_formula] at hconserve
    have h3 : chain (actualFullFineEdgeEquiv A hzero 3) = 0 := by
      simpa [fineNerve, Fin.sum_univ_succ, h0, h1] using hconserve
    let faces : fineSupported.FaceInTargetSubset
        (comparisonFactor coarseReading fineReading coarse_coarser_fine ⁻¹' A) → ℚ :=
      fun face =>
        if face.1 = 0 then chain (actualFullFineEdgeEquiv A hzero 2)
        else chain (actualFullFineEdgeEquiv A hzero 4)
    refine ⟨faces, ?_, ?_⟩
    · intro face hnot
      obtain ⟨faceCell, rfl⟩ :=
        (actualFullFineFaceEquiv A hzero).surjective face
      fin_cases faceCell
      · exact (hnot (actualFull_internalFace_zero A hzero 0)).elim
      · exact (hnot (actualFull_internalFace_zero A hzero 1)).elim
    · intro edge
      obtain ⟨edgeCell, rfl⟩ :=
        (actualFullFineEdgeEquiv A hzero).surjective edge
      fin_cases edgeCell <;> rw [actualFull_faceBoundary_formula] <;>
        simp [faces, actualFullFineFaceEquiv, fineNerve,
          Fin.sum_univ_succ, h0, h1, h3]
  · have hzeroEdge (edge : fineNerve.EdgeComponent) :
        chain (actualFullFineEdgeEquiv A hzero edge) = 0 :=
      hcycle.1 (actualFullFineEdgeEquiv A hzero edge) (by
        rw [actualFull_fiberEdge_iff]
        fin_cases edge <;> simp [fineNerve, chartMap])
    refine ⟨0, ?_, ?_⟩
    · intro _face _hnot
      rfl
    · intro edge
      obtain ⟨edgeCell, rfl⟩ :=
        (actualFullFineEdgeEquiv A hzero).surjective edge
      rw [hzeroEdge, actualFull_faceBoundary_formula]
      simp

private abbrev actualOneSet : Set coarseReading.Target := {1}

private def actualOneCoarseChart :
    coarseSupported.ChartInTargetSubset actualOneSet :=
  ⟨0, 1, by simp [coarseChartSupport], by simp⟩

private def actualOneCoarseEdge :
    coarseSupported.EdgeInTargetSubset actualOneSet :=
  ⟨2, 1, by
    simp [TargetSupportedNerve.edgeSupport, coarseNerve,
      coarseChartSupport], by simp⟩

private def actualOneCoarseFace :
    coarseSupported.FaceInTargetSubset actualOneSet :=
  ⟨PUnit.unit, 1, by
    simp [TargetSupportedNerve.faceSupport, TargetSupportedNerve.edgeSupport,
      coarseNerve, coarseChartSupport], by simp⟩

private def actualOneFineChart :
    fineSupported.ChartInTargetSubset
      (comparisonFactor coarseReading fineReading coarse_coarser_fine ⁻¹'
        actualOneSet) :=
  ⟨0, 2, by simp [fineChartSupport], by
    simp [comparisonFactor_eq_coarseRead, coarseRead]⟩

private def actualOneFineEdge :
    fineSupported.EdgeInTargetSubset
      (comparisonFactor coarseReading fineReading coarse_coarser_fine ⁻¹'
        actualOneSet) :=
  ⟨2, 2, by
    simp [TargetSupportedNerve.edgeSupport, fineNerve, fineChartSupport], by
      simp [comparisonFactor_eq_coarseRead, coarseRead]⟩

private def actualOneFineFace :
    fineSupported.FaceInTargetSubset
      (comparisonFactor coarseReading fineReading coarse_coarser_fine ⁻¹'
        actualOneSet) :=
  ⟨0, 2, by
    simp [TargetSupportedNerve.faceSupport, TargetSupportedNerve.edgeSupport,
      fineNerve, fineChartSupport], by
      simp [comparisonFactor_eq_coarseRead, coarseRead]⟩

private theorem actualOneCoarseChart_eq
    (chart : coarseSupported.ChartInTargetSubset actualOneSet) :
    chart = actualOneCoarseChart := by
  rcases chart with ⟨chart, target, hsupport, htarget⟩
  apply Subtype.ext
  fin_cases chart
  · rfl
  · fin_cases target <;> simp [coarseChartSupport] at hsupport htarget

private theorem actualOneCoarseEdge_eq
    (edge : coarseSupported.EdgeInTargetSubset actualOneSet) :
    edge = actualOneCoarseEdge := by
  rcases edge with ⟨edge, target, hsupport, htarget⟩
  apply Subtype.ext
  fin_cases edge <;> fin_cases target <;>
    simp [TargetSupportedNerve.edgeSupport, coarseNerve,
      coarseChartSupport] at hsupport htarget
  all_goals rfl

private theorem actualOneCoarseFace_eq
    (face : coarseSupported.FaceInTargetSubset actualOneSet) :
    face = actualOneCoarseFace := by
  cases face.1
  apply Subtype.ext
  rfl

private theorem actualOneFineChart_eq
    (chart : fineSupported.ChartInTargetSubset
      (comparisonFactor coarseReading fineReading coarse_coarser_fine ⁻¹'
        actualOneSet)) :
    chart = actualOneFineChart := by
  rcases chart with ⟨chart, target, hsupport, htarget⟩
  apply Subtype.ext
  fin_cases chart <;> fin_cases target <;>
    simp [fineChartSupport, comparisonFactor_eq_coarseRead, coarseRead]
      at hsupport htarget
  all_goals rfl

private theorem actualOneFineEdge_eq
    (edge : fineSupported.EdgeInTargetSubset
      (comparisonFactor coarseReading fineReading coarse_coarser_fine ⁻¹'
        actualOneSet)) :
    edge = actualOneFineEdge := by
  rcases edge with ⟨edge, target, hsupport, htarget⟩
  apply Subtype.ext
  fin_cases edge <;> fin_cases target <;>
    simp [TargetSupportedNerve.edgeSupport, fineNerve, fineChartSupport,
      comparisonFactor_eq_coarseRead, coarseRead] at hsupport htarget
  all_goals rfl

private theorem actualOneFineFace_eq
    (face : fineSupported.FaceInTargetSubset
      (comparisonFactor coarseReading fineReading coarse_coarser_fine ⁻¹'
        actualOneSet)) :
    face = actualOneFineFace := by
  rcases face with ⟨face, target, hsupport, htarget⟩
  apply Subtype.ext
  fin_cases face <;> fin_cases target <;>
    simp [TargetSupportedNerve.faceSupport, TargetSupportedNerve.edgeSupport,
      fineNerve, fineChartSupport, comparisonFactor_eq_coarseRead, coarseRead]
      at hsupport htarget
  all_goals rfl

private theorem actualOne_conditionC1 :
    nerveMorphism.ConditionC1AtTargetSubset actualOneSet := by
  intro coarseChart
  rw [actualOneCoarseChart_eq coarseChart]
  constructor
  · refine ⟨actualOneFineChart, ?_⟩
    exact (nerveMorphism.aSubnerveChartMap_eq_iff actualOneSet
      actualOneFineChart actualOneCoarseChart).2 rfl
  · intro left right _hleft _hright
    rw [actualOneFineChart_eq left, actualOneFineChart_eq right]

private theorem actualOne_conditionC2 :
    nerveMorphism.ConditionC2AtTargetSubset actualOneSet := by
  intro coarseEdge
  rw [actualOneCoarseEdge_eq coarseEdge]
  refine ⟨actualOneFineEdge, ?_⟩
  apply (nerveMorphism.aSubnerveEdgeMapOption_eq_some_iff actualOneSet
    actualOneFineEdge actualOneCoarseEdge).2
  rfl

private theorem actualOne_conditionC4 :
    nerveMorphism.ConditionC4AtTargetSubset actualOneSet := by
  intro coarseFace
  rw [actualOneCoarseFace_eq coarseFace]
  refine ⟨actualOneFineFace, ?_⟩
  apply (nerveMorphism.aSubnerveFaceMapOption_eq_some_iff actualOneSet
    actualOneFineFace actualOneCoarseFace).2
  rfl

private def actualOneFineFaceEquiv : PUnit.{1} ≃
    fineSupported.FaceInTargetSubset
      (comparisonFactor coarseReading fineReading coarse_coarser_fine ⁻¹'
        actualOneSet) where
  toFun _ := actualOneFineFace
  invFun _ := PUnit.unit
  left_inv _ := Subsingleton.elim _ _
  right_inv face := (actualOneFineFace_eq face).symm

@[simp] private theorem actualOne_faceEdge0 :
    fineSupported.targetSubsetFaceEdge0
        (comparisonFactor coarseReading fineReading coarse_coarser_fine ⁻¹'
          actualOneSet) actualOneFineFace = actualOneFineEdge := by
  apply Subtype.ext
  rfl

@[simp] private theorem actualOne_faceEdge1 :
    fineSupported.targetSubsetFaceEdge1
        (comparisonFactor coarseReading fineReading coarse_coarser_fine ⁻¹'
          actualOneSet) actualOneFineFace = actualOneFineEdge := by
  apply Subtype.ext
  rfl

@[simp] private theorem actualOne_faceEdge2 :
    fineSupported.targetSubsetFaceEdge2
        (comparisonFactor coarseReading fineReading coarse_coarser_fine ⁻¹'
          actualOneSet) actualOneFineFace = actualOneFineEdge := by
  apply Subtype.ext
  rfl

private theorem actualOne_fiberEdge :
    nerveMorphism.TargetSubsetFiberEdge actualOneSet actualOneCoarseChart
      actualOneFineEdge := by
  apply (nerveMorphism.targetSubsetFiberEdge_iff_endpoint_cells actualOneSet
    actualOneCoarseChart actualOneFineEdge).2
  exact ⟨rfl, rfl⟩

private theorem actualOne_internalFace :
    nerveMorphism.TargetSubsetInternalFace actualOneSet actualOneCoarseChart
      actualOneFineFace := by
  apply nerveMorphism.targetSubsetInternalFace_mk
  · rw [actualOne_faceEdge0]
    exact actualOne_fiberEdge
  · rw [actualOne_faceEdge1]
    exact actualOne_fiberEdge
  · rw [actualOne_faceEdge2]
    exact actualOne_fiberEdge

private theorem actualOne_faceBoundary_formula
    (faces : fineSupported.FaceInTargetSubset
      (comparisonFactor coarseReading fineReading coarse_coarser_fine ⁻¹'
        actualOneSet) → ℚ) :
    TargetSupportedNerveMorphism.targetSubsetFaceBoundary fineSupported
        (comparisonFactor coarseReading fineReading coarse_coarser_fine ⁻¹'
          actualOneSet) faces actualOneFineEdge =
      faces actualOneFineFace := by
  classical
  letI : Fintype (fineSupported.FaceInTargetSubset
      (comparisonFactor coarseReading fineReading coarse_coarser_fine ⁻¹'
        actualOneSet)) :=
    @Subtype.fintype
      fineSupported.nerve.FaceComponent
      (fun face => ∃ target ∈ fineSupported.faceSupport face,
        target ∈ comparisonFactor coarseReading fineReading
          coarse_coarser_fine ⁻¹' actualOneSet)
      (fun _ => Classical.propDecidable _)
      fineSupported.faceFintype
  rw [TargetSupportedNerveMorphism.targetSubsetFaceBoundary_apply]
  rw [← actualOneFineFaceEquiv.sum_comp]
  rw [← actualOneFineFaceEquiv.sum_comp]
  rw [← actualOneFineFaceEquiv.sum_comp]
  simp [actualOneFineFaceEquiv]
  all_goals
    rw [actualOne_faceEdge0, actualOne_faceEdge1, actualOne_faceEdge2]
    simp

private theorem actualOne_conditionC3 :
    nerveMorphism.ConditionC3AtTargetSubset actualOneSet := by
  intro coarseChart
  rw [actualOneCoarseChart_eq coarseChart]
  intro chain _hcycle
  let faces : fineSupported.FaceInTargetSubset
      (comparisonFactor coarseReading fineReading coarse_coarser_fine ⁻¹'
        actualOneSet) → ℚ :=
    fun _ => chain actualOneFineEdge
  refine ⟨faces, ?_, ?_⟩
  · intro face hnot
    rw [actualOneFineFace_eq face] at hnot ⊢
    exact (hnot actualOne_internalFace).elim
  · intro edge
    rw [actualOneFineEdge_eq edge]
    rw [actualOne_faceBoundary_formula]

private theorem actualSubsetClauses
    (A : Set coarseReading.Target) (hA : A.Nonempty) :
    nerveMorphism.ConditionC1AtTargetSubset A ∧
      nerveMorphism.ConditionC2AtTargetSubset A ∧
      nerveMorphism.ConditionC3AtTargetSubset A ∧
      nerveMorphism.ConditionC4AtTargetSubset A := by
  by_cases hzero : (0 : coarseReading.Target) ∈ A
  · exact ⟨actualFull_conditionC1 A hzero,
      actualFull_conditionC2 A hzero,
      actualFull_conditionC3 A hzero,
      actualFull_conditionC4 A hzero⟩
  · have hone : (1 : coarseReading.Target) ∈ A := by
      obtain ⟨target, htarget⟩ := hA
      fin_cases target
      · exact (hzero htarget).elim
      · exact htarget
    have hAeq : A = actualOneSet := by
      ext target
      fin_cases target <;> simp [hzero, hone]
    subst A
    exact ⟨actualOne_conditionC1, actualOne_conditionC2,
      actualOne_conditionC3, actualOne_conditionC4⟩

/-- The original reviewed G-104 geometry satisfies Condition C on every
nonempty target subset. -/
theorem firing_conditionCAllA : nerveMorphism.ConditionCAllA := by
  apply nerveMorphism.conditionCAllA_intro
  · exact firing_conditionC0
  · exact actualSubsetClauses
  · exact firing_conditionC5
  · exact firing_conditionC6

/-- One closed nondegenerate witness joins the original geometry, its raw
presentation and checker, the proper comparison, the nonconstant law, and
nonzero cohomology classes on both sides. -/
theorem fixed_conditionCAllA_firing :
    pFire.coarseReading = coarseReading ∧
      pFire.fineReading = fineReading ∧
      pFire.computedFactor =
        comparisonFactor coarseReading fineReading coarse_coarser_fine ∧
      (¬ Function.Injective
        (comparisonFactor coarseReading fineReading coarse_coarser_fine)) ∧
      (∃ law left right,
        laws.eval law left ≠ laws.eval law right) ∧
      nerveMorphism.ConditionCAllA ∧
      pFire.conditionCAllACheck = true ∧
      coarseFiringClass ≠ 0 ∧
      fineFiringClass ≠ 0 ∧
      nerveMorphism.generatedComparisonH1Map laws coarse_adequate fine_adequate
        coarseFiringClass = fineFiringClass := by
  refine ⟨rfl, rfl, ?_, comparisonFactor_not_injective, law_nonconstant,
    firing_conditionCAllA, pFire_conditionCAllACheck,
    coarseFiringClass_ne_zero, fineFiringClass_ne_zero, ?_⟩
  · rw [pFire_computedFactor_eq_coarseRead, comparisonFactor_eq_coarseRead]
  · rfl


end ResolutionInvarianceFiringWitness

end AAT.AG.ResolutionInvariance

#assert_standard_axioms_only
  AAT.AG.ResolutionInvariance.ResolutionInvarianceFiringWitness
