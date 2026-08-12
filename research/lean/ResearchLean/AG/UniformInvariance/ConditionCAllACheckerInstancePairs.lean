import ResearchLean.AG.UniformInvariance.ConditionCAllAChecker
import ResearchLean.AG.ResolutionInvariance.ResolutionInvarianceConditionInstances
import Formal.Util.AssertStandardAxioms

/-!
# Executed instance pairs for the all-subset Condition C checker

This module fires the Cycle 11 checker on three finite raw presentations.  The
positive presentation has a two-chart fiber connected by a degenerate edge, a
nonzero self-loop cycle, and an internal repeated face that fills it.  The two
negative presentations isolate disconnected-fiber C1 and face-free-cycle C3.

All results are obtained by running the same generic raw-table checker.  The
fixtures store no path, filling chain, matrix, rank, condition bit, or expected
Boolean result.  These are checker quality instances, not the nonconstant-law
G-107 firing presentation required later in claim (iii).
-/

namespace AAT.AG.ResolutionInvariance

open CanonicalResolution

namespace ConditionCAllACheckerInstancePairs

open ResolutionInvarianceConditionInstances

/-! ## Nontrivial positive raw presentation -/

/-- Raw finite presentation of the reviewed two-chart-fiber incidence
fixture.  The coarse target is singleton-valued, while the fine reading
distinguishes the two sources.  This module tests the geometric checker rather
than the later nonconstant-law firing. -/
def positivePresentation : FiniteComparisonPresentation where
  Source := Fin 2
  sourceFintype := inferInstance
  sourceDecidableEq := inferInstance
  sourceDefault := 0
  sourceEntries := [0, 1]
  source_mem_sourceEntries := by
    intro source
    fin_cases source <;> simp
  CoarseTarget := PUnit
  coarseTargetFintype := inferInstance
  coarseTargetDecidableEq := inferInstance
  coarseTargetEntries := [PUnit.unit]
  coarseTarget_mem_coarseTargetEntries := by
    intro target
    cases target
    simp
  FineTarget := Fin 2
  fineTargetFintype := inferInstance
  fineTargetDecidableEq := inferInstance
  coarseRead := fun _ => PUnit.unit
  fineRead := id
  coarseRead_surjective := by
    intro target
    cases target
    exact ⟨0, rfl⟩
  fineRead_surjective := by
    exact Function.surjective_id
  rawCoarserThan := by
    intro _left _right _hequal
    rfl
  CoarseChart := Fin 2
  coarseChartFintype := inferInstance
  coarseChartDecidableEq := inferInstance
  CoarseEdge := Fin 3
  coarseEdgeFintype := inferInstance
  coarseEdgeDecidableEq := inferInstance
  CoarseFace := Fin 2
  coarseFaceFintype := inferInstance
  coarseFaceDecidableEq := inferInstance
  coarseEdgeLeft := coarseNerve.edgeLeft
  coarseEdgeRight := coarseNerve.edgeRight
  coarseFaceEdge0 := coarseNerve.faceEdge0
  coarseFaceEdge1 := coarseNerve.faceEdge1
  coarseFaceEdge2 := coarseNerve.faceEdge2
  coarseFaceEdge0_left := by
    intro face
    fin_cases face <;> simp
  coarseFaceEdge0_right := by
    intro face
    fin_cases face <;> simp
  coarseFaceEdge1_right := by
    intro face
    fin_cases face <;> simp
  coarseChartSupport := fun _ => Finset.univ
  coarseChartSupport_nonempty := by
    intro chart
    exact ⟨PUnit.unit, Finset.mem_univ _⟩
  FineChart := Fin 3
  fineChartFintype := inferInstance
  fineChartDecidableEq := inferInstance
  FineEdge := Fin 4
  fineEdgeFintype := inferInstance
  fineEdgeDecidableEq := inferInstance
  FineFace := Fin 2
  fineFaceFintype := inferInstance
  fineFaceDecidableEq := inferInstance
  fineEdgeLeft := fineNerve.edgeLeft
  fineEdgeRight := fineNerve.edgeRight
  fineFaceEdge0 := fineNerve.faceEdge0
  fineFaceEdge1 := fineNerve.faceEdge1
  fineFaceEdge2 := fineNerve.faceEdge2
  fineFaceEdge0_left := by
    intro face
    fin_cases face <;> simp
  fineFaceEdge0_right := by
    intro face
    fin_cases face <;> simp
  fineFaceEdge1_right := by
    intro face
    fin_cases face <;> simp
  fineChartSupport := fun _ => Finset.univ
  fineChartSupport_nonempty := by
    intro chart
    exact ⟨0, Finset.mem_univ _⟩
  chartMap := chartMap
  edgeMap := positiveEdgeMap
  faceMap := positiveFaceMap
  edge_some_left := by
    intro fineEdge coarseEdge hmap
    fin_cases fineEdge <;> fin_cases coarseEdge <;>
      simp [positiveEdgeMap, chartMap, fineNerve, coarseNerve] at hmap ⊢
  edge_some_right := by
    intro fineEdge coarseEdge hmap
    fin_cases fineEdge <;> fin_cases coarseEdge <;>
      simp [positiveEdgeMap, chartMap, fineNerve, coarseNerve] at hmap ⊢
  edge_none_fiber := by
    intro fineEdge hmap
    fin_cases fineEdge <;>
      simp [positiveEdgeMap, chartMap, fineNerve] at hmap ⊢
  face_some_edge0 := by
    intro fineFace coarseFace hmap
    fin_cases fineFace <;> fin_cases coarseFace <;>
      simp [positiveFaceMap, positiveEdgeMap, fineNerve, coarseNerve]
        at hmap ⊢
  face_some_edge1 := by
    intro fineFace coarseFace hmap
    fin_cases fineFace <;> fin_cases coarseFace <;>
      simp [positiveFaceMap, positiveEdgeMap, fineNerve, coarseNerve]
        at hmap ⊢
  face_some_edge2 := by
    intro fineFace coarseFace hmap
    fin_cases fineFace <;> fin_cases coarseFace <;>
      simp [positiveFaceMap, positiveEdgeMap, fineNerve, coarseNerve]
        at hmap ⊢
  face_none_edge0 := by
    intro fineFace hmap
    fin_cases fineFace <;> simp [positiveFaceMap] at hmap
  face_none_edge1 := by
    intro fineFace hmap
    fin_cases fineFace <;> simp [positiveFaceMap] at hmap
  face_none_edge2 := by
    intro fineFace hmap
    fin_cases fineFace <;> simp [positiveFaceMap] at hmap
  chartSupport_compatible_source := by
    intro fineChart source hsource
    exact Finset.mem_univ _

/-! ## Isolated C1 and C3 negative raw presentations -/

/-- Two fine charts in one coarse fiber with no fine edges. -/
def disconnectedFiberPresentation : FiniteComparisonPresentation where
  Source := PUnit
  sourceFintype := inferInstance
  sourceDecidableEq := inferInstance
  sourceDefault := PUnit.unit
  sourceEntries := [PUnit.unit]
  source_mem_sourceEntries := by intro source; cases source; simp
  CoarseTarget := PUnit
  coarseTargetFintype := inferInstance
  coarseTargetDecidableEq := inferInstance
  coarseTargetEntries := [PUnit.unit]
  coarseTarget_mem_coarseTargetEntries := by intro target; cases target; simp
  FineTarget := PUnit
  fineTargetFintype := inferInstance
  fineTargetDecidableEq := inferInstance
  coarseRead := fun _ => PUnit.unit
  fineRead := fun _ => PUnit.unit
  coarseRead_surjective := by intro target; cases target; exact ⟨0, rfl⟩
  fineRead_surjective := by intro target; cases target; exact ⟨PUnit.unit, rfl⟩
  rawCoarserThan := by intro _left _right _hequal; rfl
  CoarseChart := PUnit
  coarseChartFintype := inferInstance
  coarseChartDecidableEq := inferInstance
  CoarseEdge := PEmpty
  coarseEdgeFintype := inferInstance
  coarseEdgeDecidableEq := inferInstance
  CoarseFace := PEmpty
  coarseFaceFintype := inferInstance
  coarseFaceDecidableEq := inferInstance
  coarseEdgeLeft := fun edge => nomatch edge
  coarseEdgeRight := fun edge => nomatch edge
  coarseFaceEdge0 := fun face => nomatch face
  coarseFaceEdge1 := fun face => nomatch face
  coarseFaceEdge2 := fun face => nomatch face
  coarseFaceEdge0_left := by intro face; exact nomatch face
  coarseFaceEdge0_right := by intro face; exact nomatch face
  coarseFaceEdge1_right := by intro face; exact nomatch face
  coarseChartSupport := fun _ => Finset.univ
  coarseChartSupport_nonempty := by
    intro chart
    exact ⟨PUnit.unit, Finset.mem_univ _⟩
  FineChart := Bool
  fineChartFintype := inferInstance
  fineChartDecidableEq := inferInstance
  FineEdge := PEmpty
  fineEdgeFintype := inferInstance
  fineEdgeDecidableEq := inferInstance
  FineFace := PEmpty
  fineFaceFintype := inferInstance
  fineFaceDecidableEq := inferInstance
  fineEdgeLeft := fun edge => nomatch edge
  fineEdgeRight := fun edge => nomatch edge
  fineFaceEdge0 := fun face => nomatch face
  fineFaceEdge1 := fun face => nomatch face
  fineFaceEdge2 := fun face => nomatch face
  fineFaceEdge0_left := by intro face; exact nomatch face
  fineFaceEdge0_right := by intro face; exact nomatch face
  fineFaceEdge1_right := by intro face; exact nomatch face
  fineChartSupport := fun _ => Finset.univ
  fineChartSupport_nonempty := by
    intro chart
    exact ⟨PUnit.unit, Finset.mem_univ _⟩
  chartMap := fun _ => PUnit.unit
  edgeMap := fun edge => nomatch edge
  faceMap := fun face => nomatch face
  edge_some_left := by intro fineEdge; exact nomatch fineEdge
  edge_some_right := by intro fineEdge; exact nomatch fineEdge
  edge_none_fiber := by intro fineEdge; exact nomatch fineEdge
  face_some_edge0 := by intro fineFace; exact nomatch fineFace
  face_some_edge1 := by intro fineFace; exact nomatch fineFace
  face_some_edge2 := by intro fineFace; exact nomatch fineFace
  face_none_edge0 := by intro fineFace; exact nomatch fineFace
  face_none_edge1 := by intro fineFace; exact nomatch fineFace
  face_none_edge2 := by intro fineFace; exact nomatch fineFace
  chartSupport_compatible_source := by
    intro fineChart source hsource
    exact Finset.mem_univ _

/-- One fine self-loop in a single chart fiber and no fine faces. -/
def faceFreeCyclePresentation : FiniteComparisonPresentation where
  Source := Fin 2
  sourceFintype := inferInstance
  sourceDecidableEq := inferInstance
  sourceDefault := 0
  sourceEntries := [0, 1]
  source_mem_sourceEntries := by intro source; fin_cases source <;> simp
  CoarseTarget := PUnit
  coarseTargetFintype := inferInstance
  coarseTargetDecidableEq := inferInstance
  coarseTargetEntries := [PUnit.unit]
  coarseTarget_mem_coarseTargetEntries := by intro target; cases target; simp
  FineTarget := Fin 2
  fineTargetFintype := inferInstance
  fineTargetDecidableEq := inferInstance
  coarseRead := fun _ => PUnit.unit
  fineRead := id
  coarseRead_surjective := by intro target; cases target; exact ⟨0, rfl⟩
  fineRead_surjective := Function.surjective_id
  rawCoarserThan := by intro _left _right _hequal; rfl
  CoarseChart := PUnit
  coarseChartFintype := inferInstance
  coarseChartDecidableEq := inferInstance
  CoarseEdge := Empty
  coarseEdgeFintype := inferInstance
  coarseEdgeDecidableEq := inferInstance
  CoarseFace := Empty
  coarseFaceFintype := inferInstance
  coarseFaceDecidableEq := inferInstance
  coarseEdgeLeft := fun edge => nomatch edge
  coarseEdgeRight := fun edge => nomatch edge
  coarseFaceEdge0 := fun face => nomatch face
  coarseFaceEdge1 := fun face => nomatch face
  coarseFaceEdge2 := fun face => nomatch face
  coarseFaceEdge0_left := by intro face; exact nomatch face
  coarseFaceEdge0_right := by intro face; exact nomatch face
  coarseFaceEdge1_right := by intro face; exact nomatch face
  coarseChartSupport := fun _ => Finset.univ
  coarseChartSupport_nonempty := by
    intro chart
    exact ⟨PUnit.unit, Finset.mem_univ _⟩
  FineChart := PUnit
  fineChartFintype := inferInstance
  fineChartDecidableEq := inferInstance
  FineEdge := PUnit
  fineEdgeFintype := inferInstance
  fineEdgeDecidableEq := inferInstance
  FineFace := Empty
  fineFaceFintype := inferInstance
  fineFaceDecidableEq := inferInstance
  fineEdgeLeft := fun _ => PUnit.unit
  fineEdgeRight := fun _ => PUnit.unit
  fineFaceEdge0 := fun face => nomatch face
  fineFaceEdge1 := fun face => nomatch face
  fineFaceEdge2 := fun face => nomatch face
  fineFaceEdge0_left := by intro face; exact nomatch face
  fineFaceEdge0_right := by intro face; exact nomatch face
  fineFaceEdge1_right := by intro face; exact nomatch face
  fineChartSupport := fun _ => Finset.univ
  fineChartSupport_nonempty := by
    intro chart
    exact ⟨0, Finset.mem_univ _⟩
  chartMap := fun _ => PUnit.unit
  edgeMap := fun _ => none
  faceMap := fun face => nomatch face
  edge_some_left := by intro fineEdge coarseEdge; exact nomatch coarseEdge
  edge_some_right := by intro fineEdge coarseEdge; exact nomatch coarseEdge
  edge_none_fiber := by intro fineEdge hmap; rfl
  face_some_edge0 := by intro fineFace; exact nomatch fineFace
  face_some_edge1 := by intro fineFace; exact nomatch fineFace
  face_some_edge2 := by intro fineFace; exact nomatch fineFace
  face_none_edge0 := by intro fineFace; exact nomatch fineFace
  face_none_edge1 := by intro fineFace; exact nomatch fineFace
  face_none_edge2 := by intro fineFace; exact nomatch fineFace
  chartSupport_compatible_source := by
    intro fineChart source hsource
    exact Finset.mem_univ _

/-! ## Named selected cells and raw finite formulas -/

/-- A selected coarse chart of the positive full target subset. -/
def positiveCoarseChart (chart : Fin 2) :
    positivePresentation.CoarseChartIn Finset.univ :=
  ⟨chart, by
    apply (positivePresentation.mem_coarseChartsIn_iff_raw Finset.univ chart).2
    exact ⟨PUnit.unit, by simp [positivePresentation], Finset.mem_univ _⟩
  ⟩

/-- A selected fine chart of the positive full target subset. -/
def positiveFineChart (chart : Fin 3) :
    positivePresentation.FineChartIn Finset.univ :=
  ⟨chart, by
    apply (positivePresentation.mem_fineChartsIn_iff_raw Finset.univ chart).2
    exact ⟨(0 : Fin 2), by simp [positivePresentation], Finset.mem_univ _⟩
  ⟩

/-- A selected fine edge of the positive full target subset. -/
def positiveFineEdge (edge : Fin 4) :
    positivePresentation.FineEdgeIn Finset.univ :=
  ⟨edge, by
    apply (positivePresentation.mem_fineEdgesIn_iff_raw Finset.univ edge).2
    refine ⟨(0 : Fin 2), ?_, Finset.mem_univ _⟩
    rw [positivePresentation.mem_fineEdgeSupportFinset_iff_raw]
    fin_cases edge <;> simp [positivePresentation]
  ⟩

/-- A selected fine face of the positive full target subset. -/
def positiveFineFace (face : Fin 2) :
    positivePresentation.FineFaceIn Finset.univ :=
  ⟨face, by
    apply (positivePresentation.mem_fineFacesIn_iff_raw Finset.univ face).2
    refine ⟨(0 : Fin 2), ?_, Finset.mem_univ _⟩
    rw [positivePresentation.mem_fineFaceSupportFinset_iff_raw]
    simp only [positivePresentation.mem_fineEdgeSupportFinset_iff_raw]
    fin_cases face <;> simp [positivePresentation]
  ⟩

/-- Every selected positive coarse chart is its named raw chart. -/
theorem positiveCoarseChart_eq (chart) :
    positiveCoarseChart chart.1 = chart := by
  apply Subtype.ext
  rfl

/-- Every selected positive fine chart is its named raw chart. -/
theorem positiveFineChart_eq (chart) :
    positiveFineChart chart.1 = chart := by
  apply Subtype.ext
  rfl

/-- Every selected positive fine edge is its named raw edge. -/
theorem positiveFineEdge_eq (edge) :
    positiveFineEdge edge.1 = edge := by
  apply Subtype.ext
  rfl

/-- Every selected positive fine face is its named raw face. -/
theorem positiveFineFace_eq (face) :
    positiveFineFace face.1 = face := by
  apply Subtype.ext
  rfl

/-- Dependent eliminator for selected positive coarse charts. -/
theorem positiveCoarseChart_cases
    {Q : positivePresentation.CoarseChartIn Finset.univ → Prop}
    (h : ∀ chart, Q (positiveCoarseChart chart)) (current) : Q current := by
  rw [← positiveCoarseChart_eq current]
  exact h current.1

/-- Dependent eliminator for selected positive fine edges. -/
theorem positiveFineEdge_cases
    {Q : positivePresentation.FineEdgeIn Finset.univ → Prop}
    (h : ∀ edge, Q (positiveFineEdge edge)) (current) : Q current := by
  rw [← positiveFineEdge_eq current]
  exact h current.1

/-- The selected positive fine edges are enumerated by the raw `Fin 4`
table. -/
def positiveFineEdgeEquiv : Fin 4 ≃
    positivePresentation.FineEdgeIn Finset.univ where
  toFun := positiveFineEdge
  invFun := Subtype.val
  left_inv _edge := rfl
  right_inv := positiveFineEdge_eq

/-- The selected positive fine faces are enumerated by the raw `Fin 2`
table. -/
def positiveFineFaceEquiv : Fin 2 ≃
    positivePresentation.FineFaceIn Finset.univ where
  toFun := positiveFineFace
  invFun := Subtype.val
  left_inv _face := rfl
  right_inv := positiveFineFace_eq

/-- The inverse selected-face enumeration returns the original raw face. -/
@[simp]
theorem positiveFineFaceEquiv_symm_positiveFineFace (face : Fin 2) :
    positiveFineFaceEquiv.symm (positiveFineFace face) = face :=
  positiveFineFaceEquiv.symm_apply_apply face

/-- Raw incoming coefficients in the positive fixture are the explicit
four-edge endpoint sum. -/
theorem positiveRawFiberIncoming_formula
    (chain : positivePresentation.FineEdgeIn Finset.univ → ℚ)
    (chart : Fin 3) :
    positivePresentation.rawFiberIncoming Finset.univ chain
        (positiveFineChart chart) =
      ∑ edge : Fin 4,
        if fineNerve.edgeRight edge = chart then
          chain (positiveFineEdge edge) else 0 := by
  rw [positivePresentation.rawFiberIncoming_apply,
    ← positiveFineEdgeEquiv.sum_comp]
  simp [positiveFineEdgeEquiv, positiveFineEdge, positiveFineChart,
    FiniteComparisonPresentation.fineEdgeRightIn, positivePresentation]

/-- Raw outgoing coefficients in the positive fixture are the explicit
four-edge endpoint sum. -/
theorem positiveRawFiberOutgoing_formula
    (chain : positivePresentation.FineEdgeIn Finset.univ → ℚ)
    (chart : Fin 3) :
    positivePresentation.rawFiberOutgoing Finset.univ chain
        (positiveFineChart chart) =
      ∑ edge : Fin 4,
        if fineNerve.edgeLeft edge = chart then
          chain (positiveFineEdge edge) else 0 := by
  rw [positivePresentation.rawFiberOutgoing_apply,
    ← positiveFineEdgeEquiv.sum_comp]
  simp [positiveFineEdgeEquiv, positiveFineEdge, positiveFineChart,
    FiniteComparisonPresentation.fineEdgeLeftIn, positivePresentation]

/-- The positive raw internal-face boundary is the explicit two-face
oriented sum. -/
theorem positiveInternalFaceBoundary_formula
    (coarseChart : Fin 2)
    (faces : positivePresentation.FineFaceIn Finset.univ → ℚ)
    (edge : Fin 4) :
    positivePresentation.internalFaceBoundaryLinearMap Finset.univ
        (positiveCoarseChart coarseChart) faces (positiveFineEdge edge) =
      (∑ face : Fin 2,
        if fineNerve.faceEdge0 face = edge then
          positivePresentation.maskedInternalFaceChain Finset.univ
            (positiveCoarseChart coarseChart) faces (positiveFineFace face)
        else 0) -
      (∑ face : Fin 2,
        if fineNerve.faceEdge1 face = edge then
          positivePresentation.maskedInternalFaceChain Finset.univ
            (positiveCoarseChart coarseChart) faces (positiveFineFace face)
        else 0) +
      ∑ face : Fin 2,
        if fineNerve.faceEdge2 face = edge then
          positivePresentation.maskedInternalFaceChain Finset.univ
            (positiveCoarseChart coarseChart) faces (positiveFineFace face)
        else 0 := by
  rw [positivePresentation.internalFaceBoundaryLinearMap_apply]
  rw [← positiveFineFaceEquiv.sum_comp]
  rw [← positiveFineFaceEquiv.sum_comp]
  rw [← positiveFineFaceEquiv.sum_comp]
  simp [positiveFineFaceEquiv, positiveFineFace, positiveFineEdge,
    FiniteComparisonPresentation.fineFaceEdge0In,
    FiniteComparisonPresentation.fineFaceEdge1In,
    FiniteComparisonPresentation.fineFaceEdge2In,
    positivePresentation]

/-- Raw C3 holds in the nontrivial positive presentation: conservation kills
the connecting edge and the repeated internal face fills the remaining
self-loop coefficient. -/
theorem positive_rawConditionC3At :
    positivePresentation.RawConditionC3At Finset.univ := by
  intro coarseCurrent
  refine positiveCoarseChart_cases
    (Q := fun coarseChart =>
      ∀ chain,
        positivePresentation.fiberCycleConstraintLinearMap Finset.univ
            coarseChart chain = 0 →
          ∃ faces,
            positivePresentation.internalFaceBoundaryLinearMap Finset.univ
              coarseChart faces = chain)
    ?_ coarseCurrent
  intro coarseChart
  fin_cases coarseChart
  · intro chain hzero
    change positivePresentation.fiberCycleConstraintLinearMap Finset.univ
      (positiveCoarseChart 0) chain = 0 at hzero
    change ∃ faces,
      positivePresentation.internalFaceBoundaryLinearMap Finset.univ
        (positiveCoarseChart 0) faces = chain
    have hnot0 : ¬ positivePresentation.rawFiberEdge Finset.univ
        (positiveCoarseChart 0) (positiveFineEdge 0) := by decide
    have hnot2 : ¬ positivePresentation.rawFiberEdge Finset.univ
        (positiveCoarseChart 0) (positiveFineEdge 2) := by decide
    have h0row := congrFun hzero (Sum.inl (positiveFineEdge 0))
    rw [positivePresentation.fiberCycleConstraintLinearMap_apply_inl,
      if_neg hnot0] at h0row
    have h0 : chain (positiveFineEdge 0) = 0 := by simpa using h0row
    have h2row := congrFun hzero (Sum.inl (positiveFineEdge 2))
    rw [positivePresentation.fiberCycleConstraintLinearMap_apply_inl,
      if_neg hnot2] at h2row
    have h2 : chain (positiveFineEdge 2) = 0 := by simpa using h2row
    have hmap1 : positivePresentation.chartMapIn Finset.univ
        (positiveFineChart 1) = positiveCoarseChart 0 := by decide
    have h3row := congrFun hzero (Sum.inr (positiveFineChart 1))
    rw [positivePresentation.fiberCycleConstraintLinearMap_apply_inr,
      if_pos hmap1, positiveRawFiberIncoming_formula,
      positiveRawFiberOutgoing_formula] at h3row
    have h3 : chain (positiveFineEdge 3) = 0 := by
      simpa [fineNerve, Fin.sum_univ_succ, h0, h2] using h3row
    let faces : positivePresentation.FineFaceIn Finset.univ → ℚ :=
      fun face => if positiveFineFaceEquiv.symm face = (1 : Fin 2) then
        chain (positiveFineEdge 1) else 0
    have hface0 : ¬ positivePresentation.rawInternalFace Finset.univ
        (positiveCoarseChart 0) (positiveFineFace 0) := by decide
    have hface1 : positivePresentation.rawInternalFace Finset.univ
        (positiveCoarseChart 0) (positiveFineFace 1) := by decide
    refine ⟨faces, ?_⟩
    funext edge
    refine positiveFineEdge_cases
      (Q := fun current =>
        positivePresentation.internalFaceBoundaryLinearMap Finset.univ
            (positiveCoarseChart 0) faces current = chain current)
      ?_ edge
    intro edgeCell
    fin_cases edgeCell <;>
      rw [positiveInternalFaceBoundary_formula] <;>
      simp [faces, hface0, hface1, fineNerve,
        Fin.sum_univ_succ, h0, h2, h3]
  · intro chain hzero
    change positivePresentation.fiberCycleConstraintLinearMap Finset.univ
      (positiveCoarseChart 1) chain = 0 at hzero
    change ∃ faces,
      positivePresentation.internalFaceBoundaryLinearMap Finset.univ
        (positiveCoarseChart 1) faces = chain
    have hedgeZero (edge : Fin 4) : chain (positiveFineEdge edge) = 0 := by
      have hnot : ¬ positivePresentation.rawFiberEdge Finset.univ
          (positiveCoarseChart 1) (positiveFineEdge edge) := by
        fin_cases edge <;> decide
      have hrow := congrFun hzero (Sum.inl (positiveFineEdge edge))
      rw [positivePresentation.fiberCycleConstraintLinearMap_apply_inl,
        if_neg hnot] at hrow
      simpa using hrow
    have hchain : chain = 0 := by
      funext edge
      refine positiveFineEdge_cases
        (Q := fun current => chain current = (0 :
          positivePresentation.FineEdgeIn Finset.univ → ℚ) current)
        ?_ edge
      intro edgeCell
      simpa using hedgeZero edgeCell
    refine ⟨0, ?_⟩
    rw [hchain]
    exact LinearMap.map_zero _

/-- Named selected coarse chart of the face-free fixture. -/
def faceFreeCoarseChart :
    faceFreeCyclePresentation.CoarseChartIn Finset.univ :=
  ⟨PUnit.unit, by
    apply (faceFreeCyclePresentation.mem_coarseChartsIn_iff_raw
      Finset.univ PUnit.unit).2
    exact ⟨PUnit.unit, by simp [faceFreeCyclePresentation], Finset.mem_univ _⟩
  ⟩

/-- Named selected fine self-loop of the face-free fixture. -/
def faceFreeFineEdge :
    faceFreeCyclePresentation.FineEdgeIn Finset.univ :=
  ⟨PUnit.unit, by
    apply (faceFreeCyclePresentation.mem_fineEdgesIn_iff_raw
      Finset.univ PUnit.unit).2
    refine ⟨(0 : Fin 2), ?_, Finset.mem_univ _⟩
    rw [faceFreeCyclePresentation.mem_fineEdgeSupportFinset_iff_raw]
    simp [faceFreeCyclePresentation]
  ⟩

/-- The constant-one chain on the sole selected face-free self-loop. -/
def faceFreeLoopChain :
    faceFreeCyclePresentation.FineEdgeIn Finset.univ → ℚ :=
  fun _ => 1

/-- The sole nonzero raw self-loop is in the kernel of the face-free cycle
constraint. -/
theorem faceFreeLoopChain_constraint :
    faceFreeCyclePresentation.fiberCycleConstraintLinearMap Finset.univ
      faceFreeCoarseChart faceFreeLoopChain = 0 := by
  funext row
  simp only [Pi.zero_apply]
  cases row with
  | inl edge =>
      rw [faceFreeCyclePresentation.fiberCycleConstraintLinearMap_apply_inl]
      have hfiber : faceFreeCyclePresentation.rawFiberEdge Finset.univ
          faceFreeCoarseChart edge := by
        constructor <;> apply Subtype.ext <;> rfl
      simp [hfiber]
  | inr chart =>
      rw [faceFreeCyclePresentation.fiberCycleConstraintLinearMap_apply_inr]
      have hmap : faceFreeCyclePresentation.chartMapIn Finset.univ chart =
          faceFreeCoarseChart := by
        apply Subtype.ext
        rfl
      rw [if_pos hmap, sub_eq_zero]
      rw [faceFreeCyclePresentation.rawFiberIncoming_apply,
        faceFreeCyclePresentation.rawFiberOutgoing_apply]
      apply Finset.sum_congr rfl
      intro edge _hedge
      have hendpoints :
          faceFreeCyclePresentation.fineEdgeRightIn Finset.univ edge =
            faceFreeCyclePresentation.fineEdgeLeftIn Finset.univ edge := by
        apply Subtype.ext
        rfl
      rw [hendpoints]

/-- Raw C3 fails in the face-free presentation because its nonzero loop
cannot be the boundary of an empty face table. -/
theorem faceFree_not_rawConditionC3At :
    ¬ faceFreeCyclePresentation.RawConditionC3At Finset.univ := by
  intro hraw
  obtain ⟨faces, hboundary⟩ :=
    hraw faceFreeCoarseChart faceFreeLoopChain
      faceFreeLoopChain_constraint
  have heq := congrFun hboundary faceFreeFineEdge
  rw [faceFreeCyclePresentation.internalFaceBoundaryLinearMap_apply] at heq
  have hzeroSum
      (summand : faceFreeCyclePresentation.FineFaceIn Finset.univ → ℚ) :
      ∑ face, summand face = 0 := by
    apply Finset.sum_eq_zero
    intro face _hface
    exact Empty.elim face.1
  simp only [hzeroSum, zero_sub, faceFreeLoopChain] at heq
  norm_num at heq

/-! ## Direct generic-checker firing -/

/-- The nontrivial connected fiber passes the executable C1 check. -/
theorem positive_conditionC1AtTargetSubsetCheck :
    positivePresentation.conditionC1AtTargetSubsetCheck Finset.univ = true := by
  decide

/-- The disconnected two-chart fiber fails the executable C1 check. -/
theorem disconnected_conditionC1AtTargetSubsetCheck :
    disconnectedFiberPresentation.conditionC1AtTargetSubsetCheck
      Finset.univ = false := by
  decide

/-- The internal repeated face makes the positive fiber chain complex exact. -/
theorem positive_conditionC3AtTargetSubsetCheck :
    positivePresentation.conditionC3AtTargetSubsetCheck Finset.univ = true := by
  exact (positivePresentation.conditionC3AtTargetSubsetCheck_eq_true_iff_raw
    Finset.univ).2 positive_rawConditionC3At

/-- The nonzero self-loop with no faces fails the executable C3 rank check. -/
theorem faceFree_conditionC3AtTargetSubsetCheck :
    faceFreeCyclePresentation.conditionC3AtTargetSubsetCheck
      Finset.univ = false := by
  cases hcheck :
      faceFreeCyclePresentation.conditionC3AtTargetSubsetCheck Finset.univ
  · rfl
  · exfalso
    exact faceFree_not_rawConditionC3At
      ((faceFreeCyclePresentation.conditionC3AtTargetSubsetCheck_eq_true_iff_raw
        Finset.univ).1 hcheck)

/-- The same generic all-clause checker accepts the nontrivial positive raw
presentation. -/
theorem positive_conditionCAllACheck :
    positivePresentation.conditionCAllACheck = true := by
  have h0 : positivePresentation.conditionC0Check = true := by decide
  have h5 : positivePresentation.conditionC5Check = true := by decide
  have h6 : positivePresentation.conditionC6Check = true := by decide
  have hsubsets :
      positivePresentation.conditionC1ToC4AllNonemptySubsetsCheck = true := by
    apply positivePresentation.conditionC1ToC4AllNonemptySubsetsCheck_eq_true_iff.mpr
    intro A hA
    have hAeq : A = Finset.univ := by
      ext target
      constructor
      · intro _htarget
        exact Finset.mem_univ target
      · intro _htarget
        obtain ⟨member, hmember⟩ := hA
        have heq : member = target := by
          cases member
          cases target
          rfl
        simpa [heq] using hmember
    subst A
    constructor
    · exact (positivePresentation.conditionC1AtTargetSubsetCheck_eq_true_iff
        Finset.univ).mp positive_conditionC1AtTargetSubsetCheck
    constructor
    · exact (positivePresentation.conditionC2AtTargetSubsetCheck_eq_true_iff
        Finset.univ).mp (by decide)
    constructor
    · exact (positivePresentation.conditionC3AtTargetSubsetCheck_eq_true_iff
        Finset.univ).mp positive_conditionC3AtTargetSubsetCheck
    · exact (positivePresentation.conditionC4AtTargetSubsetCheck_eq_true_iff
        Finset.univ).mp (by decide)
  simp [FiniteComparisonPresentation.conditionCAllACheck, h0, hsubsets, h5,
    h6]

/-- The same generic all-clause checker rejects the face-free-cycle raw
presentation. -/
theorem faceFree_conditionCAllACheck :
    faceFreeCyclePresentation.conditionCAllACheck = false := by
  cases hcheck : faceFreeCyclePresentation.conditionCAllACheck
  · rfl
  · exfalso
    have hcondition :=
      faceFreeCyclePresentation.conditionCAllACheck_eq_true_iff.mp hcheck
    have hC3 := hcondition.conditionC3At
      faceFreeCyclePresentation.toGeometry
      ((Finset.univ : Finset faceFreeCyclePresentation.CoarseTarget) :
        Set faceFreeCyclePresentation.CoarseTarget)
      (by
        refine ⟨PUnit.unit, ?_⟩
        simp)
    have htrue :=
      (faceFreeCyclePresentation.conditionC3AtTargetSubsetCheck_eq_true_iff
        Finset.univ).2 hC3
    simp [faceFree_conditionC3AtTargetSubsetCheck] at htrue

end ConditionCAllACheckerInstancePairs

end AAT.AG.ResolutionInvariance

#assert_standard_axioms_only
  AAT.AG.ResolutionInvariance.ConditionCAllACheckerInstancePairs
