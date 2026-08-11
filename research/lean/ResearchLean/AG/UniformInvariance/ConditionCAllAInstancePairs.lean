import ResearchLean.AG.ResolutionInvariance.ResolutionInvarianceConditionInstances
import ResearchLean.AG.UniformInvariance.ConditionCAllA
import Formal.Util.AssertStandardAxioms

/-!
# Finite instance pairs for Condition C on all target subnerves

This module realizes every proposition introduced by `ConditionCAllA` on
finite actual A-subnerves.  It reuses the reviewed G-104 incidence fixture:
the positive morphism has a proper reading factor, a two-chart fiber, a
degenerate fiber edge, mapped coarse cells, and an internal face filling a
nonzero local cycle.  The negative instances reuse the corresponding
missing-image and face-free morphisms.

The fixtures carry only readings, supported nerves, incidence, and partial
maps.  No condition result, path, filling chain, rank, defect, or uniformity
truth value is stored in an input structure.  These are quality instances for
the geometric predicate; they are not the final nonconstant-law firing
fixture required by claim (iii) of G-107.
-/

noncomputable section

namespace AAT.AG.ResolutionInvariance

open CanonicalResolution BigOperators

namespace ConditionCAllAInstancePairs

open ResolutionInvarianceConditionInstances

/-! ## Named cells in the actual full target subnerve -/

/-- The full coarse target subset used by the finite quality fixture. -/
abbrev coarseAll : Set coarseReading.Target := Set.univ

/-- The canonical fine preimage of the full coarse target subset. -/
abbrev fineAll : Set fineReading.Target :=
  comparisonFactor coarseReading fineReading coarse_coarser_fine ⁻¹' coarseAll

/-- Named coarse chart in the actual full target subnerve. -/
def coarseChart (chart : coarseNerve.Chart) :
    coarseSupported.ChartInTargetSubset coarseAll :=
  ⟨chart, PUnit.unit, Set.mem_univ _, Set.mem_univ _⟩

/-- Named fine chart in the canonical preimage subnerve. -/
def fineChart (chart : fineNerve.Chart) :
    fineSupported.ChartInTargetSubset fineAll :=
  ⟨chart, 0, Set.mem_univ _, Set.mem_univ _⟩

/-- Named coarse edge in the actual full target subnerve. -/
def coarseEdge (edge : coarseNerve.EdgeComponent) :
    coarseSupported.EdgeInTargetSubset coarseAll :=
  ⟨edge, PUnit.unit, by
    simp [TargetSupportedNerve.edgeSupport]
  ⟩

/-- Named fine edge in the canonical preimage subnerve. -/
def fineEdge (edge : fineNerve.EdgeComponent) :
    fineSupported.EdgeInTargetSubset fineAll :=
  ⟨edge, 0, by
    simp [TargetSupportedNerve.edgeSupport]
  ⟩

/-- Named coarse face in the actual full target subnerve. -/
def coarseFace (face : coarseNerve.FaceComponent) :
    coarseSupported.FaceInTargetSubset coarseAll :=
  ⟨face, PUnit.unit, by
    simp [TargetSupportedNerve.faceSupport, TargetSupportedNerve.edgeSupport]
  ⟩

/-- Named fine face in the canonical preimage subnerve. -/
def fineFace (face : fineNerve.FaceComponent) :
    fineSupported.FaceInTargetSubset fineAll :=
  ⟨face, 0, by
    simp [TargetSupportedNerve.faceSupport, TargetSupportedNerve.edgeSupport]
  ⟩

/-- Simp normalizes a named coarse A-subnerve chart to its raw chart. -/
@[simp] theorem coarseChart_cell (chart) : (coarseChart chart).1 = chart := rfl

/-- Simp normalizes a named fine A-subnerve chart to its raw chart. -/
@[simp] theorem fineChart_cell (chart) : (fineChart chart).1 = chart := rfl

/-- Simp normalizes a named coarse A-subnerve edge to its raw edge. -/
@[simp] theorem coarseEdge_cell (edge) : (coarseEdge edge).1 = edge := rfl

/-- Simp normalizes a named fine A-subnerve edge to its raw edge. -/
@[simp] theorem fineEdge_cell (edge) : (fineEdge edge).1 = edge := rfl

/-- Simp normalizes a named coarse A-subnerve face to its raw face. -/
@[simp] theorem coarseFace_cell (face) : (coarseFace face).1 = face := rfl

/-- Simp normalizes a named fine A-subnerve face to its raw face. -/
@[simp] theorem fineFace_cell (face) : (fineFace face).1 = face := rfl

/-- Every coarse A-subnerve chart is reconstructed from its raw chart. -/
theorem coarseChart_eq (chart) : coarseChart chart.1 = chart := by
  apply Subtype.ext
  rfl

/-- Every fine A-subnerve chart is reconstructed from its raw chart. -/
theorem fineChart_eq (chart) : fineChart chart.1 = chart := by
  apply Subtype.ext
  rfl

/-- Every coarse A-subnerve edge is reconstructed from its raw edge. -/
theorem coarseEdge_eq (edge) : coarseEdge edge.1 = edge := by
  apply Subtype.ext
  rfl

/-- Every fine A-subnerve edge is reconstructed from its raw edge. -/
theorem fineEdge_eq (edge) : fineEdge edge.1 = edge := by
  apply Subtype.ext
  rfl

/-- Every coarse A-subnerve face is reconstructed from its raw face. -/
theorem coarseFace_eq (face) : coarseFace face.1 = face := by
  apply Subtype.ext
  rfl

/-- Every fine A-subnerve face is reconstructed from its raw face. -/
theorem fineFace_eq (face) : fineFace face.1 = face := by
  apply Subtype.ext
  rfl

/-- Dependent eliminator for coarse A-subnerve charts. -/
theorem coarseChart_cases
    {P : coarseSupported.ChartInTargetSubset coarseAll → Prop}
    (h : ∀ chart, P (coarseChart chart)) (current) : P current := by
  rw [← coarseChart_eq current]
  exact h current.1

/-- Dependent eliminator for fine A-subnerve charts. -/
theorem fineChart_cases
    {P : fineSupported.ChartInTargetSubset fineAll → Prop}
    (h : ∀ chart, P (fineChart chart)) (current) : P current := by
  rw [← fineChart_eq current]
  exact h current.1

/-- Dependent eliminator for coarse A-subnerve edges. -/
theorem coarseEdge_cases
    {P : coarseSupported.EdgeInTargetSubset coarseAll → Prop}
    (h : ∀ edge, P (coarseEdge edge)) (current) : P current := by
  rw [← coarseEdge_eq current]
  exact h current.1

/-- Dependent eliminator for fine A-subnerve edges. -/
theorem fineEdge_cases
    {P : fineSupported.EdgeInTargetSubset fineAll → Prop}
    (h : ∀ edge, P (fineEdge edge)) (current) : P current := by
  rw [← fineEdge_eq current]
  exact h current.1

/-- Dependent eliminator for coarse A-subnerve faces. -/
theorem coarseFace_cases
    {P : coarseSupported.FaceInTargetSubset coarseAll → Prop}
    (h : ∀ face, P (coarseFace face)) (current) : P current := by
  rw [← coarseFace_eq current]
  exact h current.1

/-- Dependent eliminator for fine A-subnerve faces. -/
theorem fineFace_cases
    {P : fineSupported.FaceInTargetSubset fineAll → Prop}
    (h : ∀ face, P (fineFace face)) (current) : P current := by
  rw [← fineFace_eq current]
  exact h current.1

/-- Equivalence enumerating fine A-subnerve edges by the raw finite edges. -/
def fineEdgeEquiv : fineNerve.EdgeComponent ≃
    fineSupported.EdgeInTargetSubset fineAll where
  toFun := fineEdge
  invFun := Subtype.val
  left_inv := fineEdge_cell
  right_inv := fineEdge_eq

/-- Equivalence enumerating fine A-subnerve faces by the raw finite faces. -/
def fineFaceEquiv : fineNerve.FaceComponent ≃
    fineSupported.FaceInTargetSubset fineAll where
  toFun := fineFace
  invFun := Subtype.val
  left_inv := fineFace_cell
  right_inv := fineFace_eq

/-! ## Positive and negative helper-relation instances -/

/-- Positive §1.4 instance: fine edge three lies in the two-chart actual fiber. -/
theorem positive_targetSubsetFiberEdge :
    positiveMorphism.TargetSubsetFiberEdge coarseAll (coarseChart 0)
      (fineEdge 3) := by
  rw [positiveMorphism.targetSubsetFiberEdge_iff_endpoint_cells]
  simp [fineNerve, chartMap, coarseChart, fineEdge]

/-- Negative §1.4 instance: fine edge zero leaves coarse chart zero's fiber. -/
theorem not_targetSubsetFiberEdge :
    ¬ positiveMorphism.TargetSubsetFiberEdge coarseAll (coarseChart 0)
      (fineEdge 0) := by
  rw [positiveMorphism.targetSubsetFiberEdge_iff_endpoint_cells]
  simp [fineNerve, chartMap, coarseChart, fineEdge]

/-- Positive §1.4 instance: the two distinct fine fiber charts are adjacent. -/
theorem positive_targetSubsetFiberAdjacent :
    positiveMorphism.TargetSubsetFiberAdjacent coarseAll (coarseChart 0)
      (fineChart 0) (fineChart 1) := by
  refine ⟨fineEdge 3, positive_targetSubsetFiberEdge, Or.inl ⟨?_, ?_⟩⟩
  · apply Subtype.ext
    rfl
  · apply Subtype.ext
    rfl

/-- Negative §1.4 instance: the fixture has no loop adjacency at fine chart one. -/
theorem not_targetSubsetFiberAdjacent :
    ¬ positiveMorphism.TargetSubsetFiberAdjacent coarseAll (coarseChart 0)
      (fineChart 1) (fineChart 1) := by
  rintro ⟨edge, _hfiber, hendpoints⟩
  refine fineEdge_cases
    (P := fun current =>
      ((fineSupported.targetSubsetEdgeLeft fineAll current = fineChart 1 ∧
          fineSupported.targetSubsetEdgeRight fineAll current = fineChart 1) ∨
        (fineSupported.targetSubsetEdgeLeft fineAll current = fineChart 1 ∧
          fineSupported.targetSubsetEdgeRight fineAll current = fineChart 1)) →
        False)
    ?_ edge hendpoints
  intro cell hendpoints
  fin_cases cell <;>
    simp [fineNerve, fineChart, fineEdge,
      TargetSupportedNerve.targetSubsetEdgeLeft,
      TargetSupportedNerve.targetSubsetEdgeRight] at hendpoints

/-- Positive §1.4 instance: repeated face one is internal to the actual fiber. -/
theorem positive_targetSubsetInternalFace :
    positiveMorphism.TargetSubsetInternalFace coarseAll (coarseChart 0)
      (fineFace 1) := by
  constructor
  · simpa [fineFace, fineEdge] using positive_targetSubsetFiberEdge
  constructor
  · simpa [fineFace, fineEdge] using positive_targetSubsetFiberEdge
  · simpa [fineFace, fineEdge] using positive_targetSubsetFiberEdge

/-- Negative §1.4 instance: triangle face zero is not internal to that fiber. -/
theorem not_targetSubsetInternalFace :
    ¬ positiveMorphism.TargetSubsetInternalFace coarseAll (coarseChart 0)
      (fineFace 0) := by
  intro hface
  exact not_targetSubsetFiberEdge (by
    simpa [fineFace, fineEdge, fineNerve] using hface.1)

/-! ## Positive C1, C2, and C4 on the actual full target subnerve -/

/-- Positive §1.4 instance for connected chart fibers on the actual subnerve. -/
theorem positive_conditionC1AtTargetSubset :
    positiveMorphism.ConditionC1AtTargetSubset coarseAll := by
  intro coarseCurrent
  refine coarseChart_cases
    (P := fun current =>
      (∃ fineCurrent,
        positiveMorphism.aSubnerveChartMap coarseAll fineCurrent = current) ∧
      ∀ left right,
        positiveMorphism.aSubnerveChartMap coarseAll left = current →
        positiveMorphism.aSubnerveChartMap coarseAll right = current →
        Relation.ReflTransGen
          (positiveMorphism.TargetSubsetFiberAdjacent coarseAll current)
          left right)
    ?_ coarseCurrent
  intro coarseCell
  constructor
  · fin_cases coarseCell
    · exact ⟨fineChart 0, by apply Subtype.ext; rfl⟩
    · exact ⟨fineChart 2, by apply Subtype.ext; rfl⟩
  · intro left right
    refine fineChart_cases
      (P := fun currentLeft =>
        positiveMorphism.aSubnerveChartMap coarseAll currentLeft =
            coarseChart coarseCell →
        positiveMorphism.aSubnerveChartMap coarseAll right =
            coarseChart coarseCell →
        Relation.ReflTransGen
          (positiveMorphism.TargetSubsetFiberAdjacent coarseAll
            (coarseChart coarseCell)) currentLeft right)
      ?_ left
    intro leftCell hleft hright
    refine fineChart_cases
      (P := fun currentRight =>
        positiveMorphism.aSubnerveChartMap coarseAll (fineChart leftCell) =
            coarseChart coarseCell →
        positiveMorphism.aSubnerveChartMap coarseAll currentRight =
            coarseChart coarseCell →
        Relation.ReflTransGen
          (positiveMorphism.TargetSubsetFiberAdjacent coarseAll
            (coarseChart coarseCell)) (fineChart leftCell) currentRight)
      ?_ right hleft hright
    intro rightCell hleft hright
    fin_cases coarseCell <;> fin_cases leftCell <;> fin_cases rightCell <;>
      simp [TargetSupportedNerveMorphism.aSubnerveChartMap_eq_iff,
        chartMap] at hleft hright
    all_goals first
      | exact Relation.ReflTransGen.refl
      | exact Relation.ReflTransGen.single positive_targetSubsetFiberAdjacent
      | exact Relation.ReflTransGen.single
          positive_targetSubsetFiberAdjacent.symm

/-- Positive §1.4 instance for exact edge lifts on the actual subnerve. -/
theorem positive_conditionC2AtTargetSubset :
    positiveMorphism.ConditionC2AtTargetSubset coarseAll := by
  intro current
  refine coarseEdge_cases
    (P := fun coarseCurrent => ∃ fineCurrent,
      positiveMorphism.aSubnerveEdgeMapOption coarseAll fineCurrent =
        some coarseCurrent)
    ?_ current
  intro edge
  refine ⟨fineEdge edge.castSucc, ?_⟩
  apply (positiveMorphism.aSubnerveEdgeMapOption_eq_some_iff _ _ _).2
  fin_cases edge <;> rfl

/-- Positive §1.4 instance for exact face lifts on the actual subnerve. -/
theorem positive_conditionC4AtTargetSubset :
    positiveMorphism.ConditionC4AtTargetSubset coarseAll := by
  intro current
  refine coarseFace_cases
    (P := fun coarseCurrent => ∃ fineCurrent,
      positiveMorphism.aSubnerveFaceMapOption coarseAll fineCurrent =
        some coarseCurrent)
    ?_ current
  intro face
  refine ⟨fineFace face, ?_⟩
  apply (positiveMorphism.aSubnerveFaceMapOption_eq_some_iff _ _ _).2
  rfl

/-! ## A nonzero actual fiber cycle and its internal-face filling -/

/-- Finite-cell formula for incoming coefficients in the actual full subnerve. -/
theorem targetSubsetFiberIncoming_formula
    (chain : fineSupported.EdgeInTargetSubset fineAll → ℚ)
    (chart : fineNerve.Chart) :
    TargetSupportedNerveMorphism.targetSubsetFiberIncoming fineSupported fineAll
        chain (fineChart chart) =
      ∑ edge : fineNerve.EdgeComponent,
        if fineNerve.edgeRight edge = chart then chain (fineEdge edge) else 0 := by
  classical
  rw [TargetSupportedNerveMorphism.targetSubsetFiberIncoming_apply]
  symm
  refine @Fintype.sum_equiv _ _ ℚ inferInstance
    (@Subtype.fintype fineSupported.nerve.EdgeComponent
      (fun edge => ∃ target,
        target ∈ fineSupported.edgeSupport edge ∧ target ∈ fineAll)
      (fun _ => Classical.propDecidable _)
      fineSupported.edgeFintype)
    inferInstance fineEdgeEquiv _ _ ?_
  intro edge
  simp [fineEdgeEquiv, fineNerve, fineChart, fineEdge,
    TargetSupportedNerve.targetSubsetEdgeRight]

/-- Finite-cell formula for outgoing coefficients in the actual full subnerve. -/
theorem targetSubsetFiberOutgoing_formula
    (chain : fineSupported.EdgeInTargetSubset fineAll → ℚ)
    (chart : fineNerve.Chart) :
    TargetSupportedNerveMorphism.targetSubsetFiberOutgoing fineSupported fineAll
        chain (fineChart chart) =
      ∑ edge : fineNerve.EdgeComponent,
        if fineNerve.edgeLeft edge = chart then chain (fineEdge edge) else 0 := by
  classical
  rw [TargetSupportedNerveMorphism.targetSubsetFiberOutgoing_apply]
  symm
  refine @Fintype.sum_equiv _ _ ℚ inferInstance
    (@Subtype.fintype fineSupported.nerve.EdgeComponent
      (fun edge => ∃ target,
        target ∈ fineSupported.edgeSupport edge ∧ target ∈ fineAll)
      (fun _ => Classical.propDecidable _)
      fineSupported.edgeFintype)
    inferInstance fineEdgeEquiv _ _ ?_
  intro edge
  simp [fineEdgeEquiv, fineNerve, fineChart, fineEdge,
    TargetSupportedNerve.targetSubsetEdgeLeft]

/-- Finite-cell formula for the oriented face boundary in the actual subnerve. -/
theorem targetSubsetFaceBoundary_formula
    (faces : fineSupported.FaceInTargetSubset fineAll → ℚ)
    (edge : fineNerve.EdgeComponent) :
    TargetSupportedNerveMorphism.targetSubsetFaceBoundary fineSupported fineAll
        faces (fineEdge edge) =
      (∑ face : fineNerve.FaceComponent,
        if fineNerve.faceEdge0 face = edge then faces (fineFace face) else 0) -
      (∑ face : fineNerve.FaceComponent,
        if fineNerve.faceEdge1 face = edge then faces (fineFace face) else 0) +
      ∑ face : fineNerve.FaceComponent,
        if fineNerve.faceEdge2 face = edge then faces (fineFace face) else 0 := by
  classical
  rw [TargetSupportedNerveMorphism.targetSubsetFaceBoundary_apply]
  apply congrArg₂ (· + ·)
  · apply congrArg₂ (· - ·)
    · symm
      refine @Fintype.sum_equiv _ _ ℚ inferInstance
        (@Subtype.fintype fineSupported.nerve.FaceComponent
          (fun face => ∃ target,
            target ∈ fineSupported.faceSupport face ∧ target ∈ fineAll)
          (fun _ => Classical.propDecidable _)
          fineSupported.faceFintype)
        inferInstance fineFaceEquiv _ _ ?_
      intro face
      simp [fineFaceEquiv, fineNerve, fineFace, fineEdge,
        TargetSupportedNerve.targetSubsetFaceEdge0]
    · symm
      refine @Fintype.sum_equiv _ _ ℚ inferInstance
        (@Subtype.fintype fineSupported.nerve.FaceComponent
          (fun face => ∃ target,
            target ∈ fineSupported.faceSupport face ∧ target ∈ fineAll)
          (fun _ => Classical.propDecidable _)
          fineSupported.faceFintype)
        inferInstance fineFaceEquiv _ _ ?_
      intro face
      simp [fineFaceEquiv, fineNerve, fineFace, fineEdge,
        TargetSupportedNerve.targetSubsetFaceEdge1]
  · symm
    refine @Fintype.sum_equiv _ _ ℚ inferInstance
      (@Subtype.fintype fineSupported.nerve.FaceComponent
        (fun face => ∃ target,
          target ∈ fineSupported.faceSupport face ∧ target ∈ fineAll)
        (fun _ => Classical.propDecidable _)
        fineSupported.faceFintype)
      inferInstance fineFaceEquiv _ _ ?_
    intro face
    simp [fineFaceEquiv, fineNerve, fineFace, fineEdge,
      TargetSupportedNerve.targetSubsetFaceEdge2]

/-- Nonzero self-loop chain in the actual full target subnerve. -/
def loopChain : fineSupported.EdgeInTargetSubset fineAll → ℚ :=
  fun edge => if edge.1 = 1 then 1 else 0

/-- Chain supported on an edge outside the chosen fiber. -/
def badSupportChain : fineSupported.EdgeInTargetSubset fineAll → ℚ :=
  fun edge => if edge.1 = 0 then 1 else 0

/-- Positive §1.4 instance: the named nonzero chain is an actual fiber cycle. -/
theorem positive_targetSubsetFiberCycle :
    positiveMorphism.TargetSubsetFiberCycle coarseAll (coarseChart 0)
      loopChain := by
  apply positiveMorphism.targetSubsetFiberCycle_mk
  · intro edge
    refine fineEdge_cases
      (P := fun current =>
        ¬ positiveMorphism.TargetSubsetFiberEdge coarseAll (coarseChart 0)
            current → loopChain current = 0)
      ?_ edge
    intro cell hnot
    fin_cases cell <;>
      simp [loopChain,
        TargetSupportedNerveMorphism.targetSubsetFiberEdge_iff_endpoint_cells,
        fineNerve, chartMap, coarseChart, fineEdge] at hnot ⊢
  · intro chart
    refine fineChart_cases
      (P := fun current =>
        positiveMorphism.aSubnerveChartMap coarseAll current = coarseChart 0 →
          TargetSupportedNerveMorphism.targetSubsetFiberIncoming fineSupported
              fineAll loopChain current =
            TargetSupportedNerveMorphism.targetSubsetFiberOutgoing fineSupported
              fineAll loopChain current)
      ?_ chart
    intro cell hmap
    fin_cases cell <;>
      simp [TargetSupportedNerveMorphism.aSubnerveChartMap_eq_iff,
        chartMap] at hmap
    all_goals
      rw [targetSubsetFiberIncoming_formula,
        targetSubsetFiberOutgoing_formula]
      simp [loopChain, fineNerve, Fin.sum_univ_succ]

/-- Negative §1.4 instance: the outside-edge chain is not a fiber cycle. -/
theorem not_targetSubsetFiberCycle :
    ¬ positiveMorphism.TargetSubsetFiberCycle coarseAll (coarseChart 0)
      badSupportChain := by
  intro hcycle
  have hzero := hcycle.support positiveMorphism (fineEdge 0)
    not_targetSubsetFiberEdge
  simp [badSupportChain] at hzero

/-- Positive §1.4 instance: every actual local fiber cycle has an internal-face
filling in the reviewed finite fixture. -/
theorem positive_conditionC3AtTargetSubset :
    positiveMorphism.ConditionC3AtTargetSubset coarseAll := by
  intro coarseCurrent
  refine coarseChart_cases
    (P := fun current =>
      ∀ chain,
        positiveMorphism.TargetSubsetFiberCycle coarseAll current chain →
          ∃ faces,
            (∀ fineCurrent,
              ¬ positiveMorphism.TargetSubsetInternalFace coarseAll current
                  fineCurrent → faces fineCurrent = 0) ∧
            ∀ fineCurrent,
              chain fineCurrent =
                TargetSupportedNerveMorphism.targetSubsetFaceBoundary
                  fineSupported fineAll faces fineCurrent)
    ?_ coarseCurrent
  intro coarseCell chain hcycle
  fin_cases coarseCell
  · have h0 : chain (fineEdge 0) = 0 :=
      hcycle.support positiveMorphism (fineEdge 0) not_targetSubsetFiberEdge
    have h2 : chain (fineEdge 2) = 0 :=
      hcycle.support positiveMorphism (fineEdge 2) (by
        rw [positiveMorphism.targetSubsetFiberEdge_iff_endpoint_cells]
        simp [fineNerve, chartMap, coarseChart, fineEdge])
    have hconserve := hcycle.conservation positiveMorphism (fineChart 1)
      (by apply Subtype.ext; rfl)
    rw [targetSubsetFiberIncoming_formula,
      targetSubsetFiberOutgoing_formula] at hconserve
    have h3 : chain (fineEdge 3) = 0 := by
      simpa [fineNerve, Fin.sum_univ_succ, h0, h2] using hconserve
    let faces : fineSupported.FaceInTargetSubset fineAll → ℚ :=
      fun face => if face.1 = 1 then chain (fineEdge 1) else 0
    refine ⟨faces, ?_, ?_⟩
    · intro face
      refine fineFace_cases
        (P := fun current =>
          ¬ positiveMorphism.TargetSubsetInternalFace coarseAll
              (coarseChart 0) current → faces current = 0)
        ?_ face
      intro cell hnot
      fin_cases cell
      · simp [faces]
      · exact (hnot positive_targetSubsetInternalFace).elim
    · intro edge
      refine fineEdge_cases
        (P := fun current =>
          chain current =
            TargetSupportedNerveMorphism.targetSubsetFaceBoundary fineSupported
              fineAll faces current)
        ?_ edge
      intro cell
      fin_cases cell <;> rw [targetSubsetFaceBoundary_formula] <;>
        simp [faces, fineNerve, Fin.sum_univ_succ, h0, h2, h3]
  · have hzero (edge : fineNerve.EdgeComponent) : chain (fineEdge edge) = 0 :=
      hcycle.support positiveMorphism (fineEdge edge) (by
        rw [positiveMorphism.targetSubsetFiberEdge_iff_endpoint_cells]
        fin_cases edge <;>
          simp [fineNerve, chartMap, coarseChart, fineEdge])
    refine ⟨0, ?_, ?_⟩
    · intro face _hnot
      rfl
    · intro edge
      refine fineEdge_cases
        (P := fun current =>
          chain current =
            TargetSupportedNerveMorphism.targetSubsetFaceBoundary fineSupported
              fineAll
              (0 : fineSupported.FaceInTargetSubset fineAll → ℚ) current)
        ?_ edge
      intro cell
      rw [hzero cell, targetSubsetFaceBoundary_formula]
      simp

/-! ## Missing-image and acyclicity counterinstances -/

/-- Negative §1.4 instance: the missing morphism has an empty actual chart fiber. -/
theorem missing_not_conditionC1AtTargetSubset :
    ¬ missingMorphism.ConditionC1AtTargetSubset coarseAll := by
  intro hC1
  obtain ⟨fineCurrent, hmap⟩ :=
    (hC1.fiber_nonempty missingMorphism (coarseChart 1))
  have hcell := congrArg Subtype.val hmap
  change missingChartMap fineCurrent.1 = 1 at hcell
  simp [missingChartMap] at hcell

/-- Negative §1.4 instance: the missing morphism has no exact actual edge lift. -/
theorem missing_not_conditionC2AtTargetSubset :
    ¬ missingMorphism.ConditionC2AtTargetSubset coarseAll := by
  intro hC2
  obtain ⟨fineCurrent, hmap⟩ := hC2.lift missingMorphism (coarseEdge 0)
  have hwhole :=
    (missingMorphism.aSubnerveEdgeMapOption_eq_some_iff coarseAll
      fineCurrent (coarseEdge 0)).1 hmap
  simp [missingEdgeMap] at hwhole

/-- Negative §1.4 instance: the missing morphism has no exact actual face lift. -/
theorem missing_not_conditionC4AtTargetSubset :
    ¬ missingMorphism.ConditionC4AtTargetSubset coarseAll := by
  intro hC4
  obtain ⟨fineCurrent, hmap⟩ := hC4.lift missingMorphism (coarseFace 0)
  have hwhole :=
    (missingMorphism.aSubnerveFaceMapOption_eq_some_iff coarseAll
      fineCurrent (coarseFace 0)).1 hmap
  simp [missingFaceMap] at hwhole

namespace AcyclicityFailureActual

open ResolutionInvarianceConditionInstances.AcyclicityFailure

/-- Named coarse chart in the face-free actual subnerve. -/
def coarseChart :
    AcyclicityFailure.coarseSupported.ChartInTargetSubset coarseAll :=
  ⟨PUnit.unit, PUnit.unit, Set.mem_univ _, Set.mem_univ _⟩

/-- Named fine chart in the face-free actual subnerve. -/
def fineChart : AcyclicityFailure.fineSupported.ChartInTargetSubset fineAll :=
  ⟨PUnit.unit, 0, Set.mem_univ _, Set.mem_univ _⟩

/-- Named fine self-loop in the face-free actual subnerve. -/
def fineEdge : AcyclicityFailure.fineSupported.EdgeInTargetSubset fineAll :=
  ⟨PUnit.unit, 0, by
    simp [TargetSupportedNerve.edgeSupport]
  ⟩

/-- Nonzero chain on the sole actual self-loop. -/
def loopChain : AcyclicityFailure.fineSupported.EdgeInTargetSubset fineAll → ℚ :=
  fun _ => 1

/-- The sole nonzero self-loop is a fiber cycle in the face-free subnerve. -/
theorem loopChain_cycle :
    AcyclicityFailure.morphism.TargetSubsetFiberCycle coarseAll coarseChart
      loopChain := by
  apply AcyclicityFailure.morphism.targetSubsetFiberCycle_mk
  · intro edge hnot
    exfalso
    apply hnot
    rw [AcyclicityFailure.morphism.targetSubsetFiberEdge_iff_endpoint_cells]
    constructor <;> exact Subsingleton.elim _ _
  · intro chart _hmap
    rw [TargetSupportedNerveMorphism.targetSubsetFiberIncoming_apply,
      TargetSupportedNerveMorphism.targetSubsetFiberOutgoing_apply]
    apply Finset.sum_congr rfl
    intro edge _hedge
    rw [if_pos (Subsingleton.elim _ _), if_pos (Subsingleton.elim _ _)]

end AcyclicityFailureActual

/-- Negative §1.4 instance: a nonzero actual fiber cycle has no face filling. -/
theorem acyclicityFailure_not_conditionC3AtTargetSubset :
    ¬ TargetSupportedNerveMorphism.ConditionC3AtTargetSubset
      ResolutionInvarianceConditionInstances.AcyclicityFailure.morphism
      coarseAll := by
  intro hC3
  obtain ⟨faces, _hoff, hboundary⟩ :=
    hC3.fill _ AcyclicityFailureActual.coarseChart
      AcyclicityFailureActual.loopChain
      AcyclicityFailureActual.loopChain_cycle
  have heq := hboundary AcyclicityFailureActual.fineEdge
  simp [AcyclicityFailureActual.loopChain,
    TargetSupportedNerveMorphism.targetSubsetFaceBoundary] at heq

/-! ## The aggregate positive and negative pair -/

/-- Positive §1.4 instance: the reviewed nontrivial morphism satisfies all
subset clauses for every nonempty coarse target subset. -/
theorem positive_conditionCAllA : positiveMorphism.ConditionCAllA := by
  apply positiveMorphism.conditionCAllA_intro positive_conditionC0
  · intro A hA
    have hAeq : A = coarseAll := by
      ext target
      constructor
      · intro _htarget
        exact Set.mem_univ _
      · intro _htarget
        obtain ⟨witness, hwitness⟩ := hA
        simpa only [Subsingleton.elim target witness] using hwitness
    subst A
    exact ⟨positive_conditionC1AtTargetSubset,
      positive_conditionC2AtTargetSubset,
      positive_conditionC3AtTargetSubset,
      positive_conditionC4AtTargetSubset⟩
  · exact positive_conditionC5
  · exact positive_conditionC6

/-- Negative §1.4 instance: the missing-image morphism fails the aggregate
predicate already at whole-nerve C0. -/
theorem missing_not_conditionCAllA : ¬ missingMorphism.ConditionCAllA := by
  intro hC
  exact missing_not_conditionC0 (hC.conditionC0 missingMorphism)

end ConditionCAllAInstancePairs

end AAT.AG.ResolutionInvariance

#assert_standard_axioms_only AAT.AG.ResolutionInvariance
