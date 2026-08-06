import ResearchLean.AG.ResolutionInvariance.EdgeFiberObstruction
import Formal.Util.AssertStandardAxioms

/-!
# A loop-lift obstruction to C0--C5 resolution invariance

This module tests the C0--C5 incidence conditions of
`G-104-aat-resolution-invariance`.  It reuses the reviewed proper adequate
reading pair and its generated nonconstant law values.  The coarse nerve has a
self-loop, a filled triangle, and a second unfilled cycle.  Its unique fine
self-loop lift joins two distinct charts in the same chart fiber, while a
declared degenerate edge extends that fiber to a nontrivial tree.

Consequently C1 and C3 hold on the fiber tree, C2 and C5 give exactly one lift
of every coarse edge, and C4 is witnessed by the actual filling face.  The
coarse self-loop still gives a nonzero `H^1` class, but its canonical pullback
is a fine coboundary.  A separate parallel-edge class remains nonzero on the
fine side, so the failure is not caused by vanishing of all fine cohomology.
-/

noncomputable section

namespace AAT.AG.ResolutionInvariance

open CanonicalResolution Cohomology TwoPhase

namespace LoopLiftObstruction

/-! ## Reviewed reading and law data -/

/-- The finite source inherited from the reviewed obstruction witnesses. -/
abbrev Source := FaceLiftObstruction.Source

/-- The reviewed nonconstant finite law family. -/
abbrev laws : FiniteLawFamily Source := FaceLiftObstruction.laws

/-- The reviewed proper coarse reading. -/
abbrev coarseReading : Reading Source := FaceLiftObstruction.coarseReading

/-- The reviewed fine identity reading. -/
abbrev fineReading : Reading Source := FaceLiftObstruction.fineReading

/-! ## A C0--C5 incidence comparison -/

/--
The coarse nerve has one filled triangle, one self-loop at chart zero, and a
second edge parallel to the first triangle edge.
-/
abbrev coarseNerve : CoverNerve where
  Chart := Fin 3
  EdgeComponent := Fin 5
  FaceComponent := PUnit
  edgeLeft edge :=
    if edge = 0 then 0 else if edge = 1 then 0 else
      if edge = 2 then 1 else 0
  edgeRight edge :=
    if edge = 0 then 1 else if edge = 1 then 2 else
      if edge = 2 then 2 else if edge = 3 then 0 else 1
  faceEdge0 _ := 0
  faceEdge1 _ := 1
  faceEdge2 _ := 2
  edgeOverlapComponent := fun _ => True
  faceTripleOverlapComponent := fun _ => True
  edgeOverlapComponent_holds := fun _ => trivial
  faceTripleOverlapComponent_holds := fun _ => trivial

/--
The fine nerve splits coarse chart zero into a three-chart tree.  Edge three is
the unique lift of the coarse self-loop and joins charts zero and one; edge four
is declared degenerate and joins charts one and two.  Edge five lifts the
unfilled parallel coarse edge.
-/
abbrev fineNerve : CoverNerve where
  Chart := Fin 5
  EdgeComponent := Fin 6
  FaceComponent := PUnit
  edgeLeft edge :=
    if edge = 0 then 0 else if edge = 1 then 0 else
      if edge = 2 then 3 else if edge = 3 then 0 else
        if edge = 4 then 1 else 0
  edgeRight edge :=
    if edge = 0 then 3 else if edge = 1 then 4 else
      if edge = 2 then 4 else if edge = 3 then 1 else
        if edge = 4 then 2 else 3
  faceEdge0 _ := 0
  faceEdge1 _ := 1
  faceEdge2 _ := 2
  edgeOverlapComponent := fun _ => True
  faceTripleOverlapComponent := fun _ => True
  edgeOverlapComponent_holds := fun _ => trivial
  faceTripleOverlapComponent_holds := fun _ => trivial

/-- Full coarse supports keep every law value genuinely available. -/
abbrev coarseSupported :
    FaceLiftObstruction.TargetSupportedNerve coarseReading where
  nerve := coarseNerve
  chartSupport := fun _ => Set.univ
  edgeSupport := fun _ => Set.univ
  faceSupport := fun _ => Set.univ
  chartSupport_nonempty := fun _ => Set.univ_nonempty
  edgeSupport_left := fun _ => Set.subset_univ _
  edgeSupport_right := fun _ => Set.subset_univ _
  faceSupport_edge0 := fun _ => Set.subset_univ _
  faceSupport_edge1 := fun _ => Set.subset_univ _
  faceSupport_edge2 := fun _ => Set.subset_univ _

/-- Full fine supports keep every generated law coordinate available. -/
abbrev fineSupported :
    FaceLiftObstruction.TargetSupportedNerve fineReading where
  nerve := fineNerve
  chartSupport := fun _ => Set.univ
  edgeSupport := fun _ => Set.univ
  faceSupport := fun _ => Set.univ
  chartSupport_nonempty := fun _ => Set.univ_nonempty
  edgeSupport_left := fun _ => Set.subset_univ _
  edgeSupport_right := fun _ => Set.subset_univ _
  faceSupport_edge0 := fun _ => Set.subset_univ _
  faceSupport_edge1 := fun _ => Set.subset_univ _
  faceSupport_edge2 := fun _ => Set.subset_univ _

/-- The first three fine charts form the fiber over coarse chart zero. -/
def chartMap (chart : fineNerve.Chart) : coarseNerve.Chart :=
  if chart = 0 then 0 else if chart = 1 then 0 else
    if chart = 2 then 0 else if chart = 3 then 1 else 2

/-- Every coarse edge has exactly one lift; fine edge four is degenerate. -/
def edgeMap (edge : fineNerve.EdgeComponent) :
    Option coarseNerve.EdgeComponent :=
  if edge = 0 then some 0 else if edge = 1 then some 1 else
    if edge = 2 then some 2 else if edge = 3 then some 3 else
      if edge = 4 then none else some 4

/-- The unique fine face lifts the unique coarse filling face. -/
def faceMap (_face : fineNerve.FaceComponent) :
    Option coarseNerve.FaceComponent :=
  some PUnit.unit

/-- The incidence morphism generated by the loop-lift comparison. -/
abbrev nerveMorphism :
    FaceLiftObstruction.NerveMorphism fineNerve coarseNerve where
  chartMap := chartMap
  edgeMap := edgeMap
  faceMap := faceMap
  edge_some_left := by
    intro fineEdge coarseEdge hmap
    fin_cases fineEdge <;> fin_cases coarseEdge <;>
      simp [edgeMap, chartMap, fineNerve, coarseNerve] at hmap ⊢
  edge_some_right := by
    intro fineEdge coarseEdge hmap
    fin_cases fineEdge <;> fin_cases coarseEdge <;>
      simp [edgeMap, chartMap, fineNerve, coarseNerve] at hmap ⊢
  edge_none_fiber := by
    intro fineEdge hmap
    fin_cases fineEdge <;>
      simp [edgeMap, chartMap, fineNerve] at hmap ⊢
  face_some_edge0 := by
    intro fineFace coarseFace hmap
    cases fineFace
    cases coarseFace
    simp [edgeMap, fineNerve, coarseNerve]
  face_some_edge1 := by
    intro fineFace coarseFace hmap
    cases fineFace
    cases coarseFace
    simp [edgeMap, fineNerve, coarseNerve]
  face_some_edge2 := by
    intro fineFace coarseFace hmap
    cases fineFace
    cases coarseFace
    simp [edgeMap, fineNerve, coarseNerve]
  face_none_edge0 := by
    intro fineFace hmap
    cases fineFace
    simp [faceMap] at hmap
  face_none_edge1 := by
    intro fineFace hmap
    cases fineFace
    simp [faceMap] at hmap
  face_none_edge2 := by
    intro fineFace hmap
    cases fineFace
    simp [faceMap] at hmap

/-!
The condition predicates are private proof helpers for this closed finite
witness.  The exported package theorem below states their incidence content
without creating one-sided public `Prop` APIs.
-/

/-- Fine chart support maps into the corresponding coarse chart support. -/
private def SupportCompatible : Prop :=
  ∀ chart target, target ∈ fineSupported.chartSupport chart →
    comparisonFactor coarseReading fineReading
        FaceLiftObstruction.coarse_coarser_fine target ∈
      coarseSupported.chartSupport (nerveMorphism.chartMap chart)

/-- C0: coarse chart support is the image union of its fine chart fiber. -/
private def ConditionC0 : Prop :=
  ∀ coarseChart target,
    target ∈ coarseSupported.chartSupport coarseChart ↔
      ∃ fineChart fineTarget,
        nerveMorphism.chartMap fineChart = coarseChart ∧
        fineTarget ∈ fineSupported.chartSupport fineChart ∧
        comparisonFactor coarseReading fineReading
            FaceLiftObstruction.coarse_coarser_fine fineTarget = target

/-- Undirected adjacency inside one chart fiber. -/
private def FiberAdjacent (left right : fineNerve.Chart) : Prop :=
  ∃ edge,
    ((fineNerve.edgeLeft edge = left ∧ fineNerve.edgeRight edge = right) ∨
      (fineNerve.edgeLeft edge = right ∧ fineNerve.edgeRight edge = left)) ∧
    nerveMorphism.chartMap left = nerveMorphism.chartMap right

/-- C1: every chart fiber is nonempty and connected. -/
private def ConditionC1 : Prop :=
  ∀ coarseChart,
    (∃ fineChart, nerveMorphism.chartMap fineChart = coarseChart) ∧
      ∀ left right,
        nerveMorphism.chartMap left = coarseChart →
        nerveMorphism.chartMap right = coarseChart →
        Relation.ReflTransGen FiberAdjacent left right

/-- C2: every coarse edge has a fine lift. -/
private def ConditionC2 : Prop :=
  ∀ coarseEdge, ∃ fineEdge,
    nerveMorphism.edgeMap fineEdge = some coarseEdge

/-- A fine edge whose endpoints lie over one coarse chart. -/
private def FiberEdge (coarseChart : coarseNerve.Chart)
    (edge : fineNerve.EdgeComponent) : Prop :=
  nerveMorphism.chartMap (fineNerve.edgeLeft edge) = coarseChart ∧
    nerveMorphism.chartMap (fineNerve.edgeRight edge) = coarseChart

/-- Incoming coefficient sum at one fine chart. -/
private def incoming (chain : fineNerve.EdgeComponent → ℚ)
    (chart : fineNerve.Chart) : ℚ :=
  ∑ edge, if fineNerve.edgeRight edge = chart then chain edge else 0

/-- Outgoing coefficient sum at one fine chart. -/
private def outgoing (chain : fineNerve.EdgeComponent → ℚ)
    (chart : fineNerve.Chart) : ℚ :=
  ∑ edge, if fineNerve.edgeLeft edge = chart then chain edge else 0

/-- A one-cycle supported on the graph over one coarse chart. -/
private def IsFiberCycle (coarseChart : coarseNerve.Chart)
    (chain : fineNerve.EdgeComponent → ℚ) : Prop :=
  (∀ edge, ¬ FiberEdge coarseChart edge → chain edge = 0) ∧
    ∀ chart, nerveMorphism.chartMap chart = coarseChart →
      incoming chain chart = outgoing chain chart

/-- A fine face whose three edges lie over one coarse chart. -/
private def InternalFace (coarseChart : coarseNerve.Chart)
    (face : fineNerve.FaceComponent) : Prop :=
  FiberEdge coarseChart (fineNerve.faceEdge0 face) ∧
    FiberEdge coarseChart (fineNerve.faceEdge1 face) ∧
    FiberEdge coarseChart (fineNerve.faceEdge2 face)

/-- The explicit oriented face-incidence sum. -/
private def faceBoundary (faces : fineNerve.FaceComponent → ℚ)
    (edge : fineNerve.EdgeComponent) : ℚ :=
  (∑ face, if fineNerve.faceEdge0 face = edge then faces face else 0) -
    (∑ face, if fineNerve.faceEdge1 face = edge then faces face else 0) +
      ∑ face, if fineNerve.faceEdge2 face = edge then faces face else 0

/-- C3: every fiber-graph cycle is generated by fiber faces. -/
private def ConditionC3 : Prop :=
  ∀ coarseChart chain, IsFiberCycle coarseChart chain →
    ∃ faces : fineNerve.FaceComponent → ℚ,
      (∀ face, ¬ InternalFace coarseChart face → faces face = 0) ∧
        ∀ edge, chain edge = faceBoundary faces edge

/-- C4: every coarse face has a fine lift. -/
private def ConditionC4 : Prop :=
  ∀ coarseFace, ∃ fineFace,
    nerveMorphism.faceMap fineFace = some coarseFace

/-- C5: a coarse edge has at most one fine edge lift. -/
private def ConditionC5 : Prop :=
  ∀ coarseEdge fineLeft fineRight,
    nerveMorphism.edgeMap fineLeft = some coarseEdge →
    nerveMorphism.edgeMap fineRight = some coarseEdge →
    fineLeft = fineRight

/-- Full supports are compatible with the canonical comparison factor. -/
theorem support_compatible : SupportCompatible := by
  intro chart target htarget
  exact Set.mem_univ _

/-- Every coarse support is the image union of its fine chart fiber. -/
theorem conditionC0 : ConditionC0 := by
  intro coarseChart target
  constructor
  · intro _htarget
    obtain ⟨fineTarget, htarget⟩ :=
      comparisonFactor_surjective coarseReading fineReading
        FaceLiftObstruction.coarse_coarser_fine target
    let fineChart : fineNerve.Chart :=
      if coarseChart = 0 then 0 else if coarseChart = 1 then 3 else 4
    refine ⟨fineChart, fineTarget, ?_, Set.mem_univ _, htarget⟩
    fin_cases coarseChart <;> simp [fineChart, chartMap]
  · intro _hwitness
    exact Set.mem_univ _

/-- Fine charts zero and one are adjacent through the mapped self-loop lift. -/
private theorem fiberAdjacent_zero_one : FiberAdjacent 0 1 := by
  refine ⟨3, ?_, ?_⟩
  · exact Or.inl ⟨rfl, rfl⟩
  · rfl

/-- The first fiber adjacency is symmetric. -/
private theorem fiberAdjacent_one_zero : FiberAdjacent 1 0 := by
  refine ⟨3, ?_, ?_⟩
  · exact Or.inr ⟨rfl, rfl⟩
  · rfl

/-- Fine charts one and two are adjacent through the declared degenerate edge. -/
private theorem fiberAdjacent_one_two : FiberAdjacent 1 2 := by
  refine ⟨4, ?_, ?_⟩
  · exact Or.inl ⟨rfl, rfl⟩
  · rfl

/-- The second fiber adjacency is symmetric. -/
private theorem fiberAdjacent_two_one : FiberAdjacent 2 1 := by
  refine ⟨4, ?_, ?_⟩
  · exact Or.inr ⟨rfl, rfl⟩
  · rfl

/-- C1 holds; the only nonsingleton fiber is the path zero--one--two. -/
theorem conditionC1 : ConditionC1 := by
  intro coarseChart
  constructor
  · fin_cases coarseChart
    · exact ⟨0, rfl⟩
    · exact ⟨3, rfl⟩
    · exact ⟨4, rfl⟩
  · intro left right hleft hright
    fin_cases coarseChart
    · have hl : left = 0 ∨ left = 1 ∨ left = 2 := by
        fin_cases left <;> simp_all [chartMap]
      have hr : right = 0 ∨ right = 1 ∨ right = 2 := by
        fin_cases right <;> simp_all [chartMap]
      rcases hl with rfl | rfl | rfl <;> rcases hr with rfl | rfl | rfl
      · exact Relation.ReflTransGen.refl
      · exact Relation.ReflTransGen.single fiberAdjacent_zero_one
      · exact (Relation.ReflTransGen.single fiberAdjacent_zero_one).trans
          (Relation.ReflTransGen.single fiberAdjacent_one_two)
      · exact Relation.ReflTransGen.single fiberAdjacent_one_zero
      · exact Relation.ReflTransGen.refl
      · exact Relation.ReflTransGen.single fiberAdjacent_one_two
      · exact (Relation.ReflTransGen.single fiberAdjacent_two_one).trans
          (Relation.ReflTransGen.single fiberAdjacent_one_zero)
      · exact Relation.ReflTransGen.single fiberAdjacent_two_one
      · exact Relation.ReflTransGen.refl
    · have hl : left = 3 := by
        fin_cases left <;> simp_all [chartMap]
      have hr : right = 3 := by
        fin_cases right <;> simp_all [chartMap]
      subst left
      subst right
      exact Relation.ReflTransGen.refl
    · have hl : left = 4 := by
        fin_cases left <;> simp_all [chartMap]
      have hr : right = 4 := by
        fin_cases right <;> simp_all [chartMap]
      subst left
      subst right
      exact Relation.ReflTransGen.refl

/-- C2 holds by the five declared nondegenerate fine lifts. -/
theorem conditionC2 : ConditionC2 := by
  intro coarseEdge
  fin_cases coarseEdge
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩
  · exact ⟨5, rfl⟩

/-- Every fiber-supported cycle on the path fiber is zero. -/
private theorem fiberCycle_eq_zero (coarseChart : coarseNerve.Chart)
    (chain : fineNerve.EdgeComponent → ℚ)
    (hcycle : IsFiberCycle coarseChart chain) :
    chain = 0 := by
  fin_cases coarseChart
  · have h0 : chain 0 = 0 := hcycle.1 0 (by
      simp [FiberEdge, chartMap, fineNerve])
    have h1 : chain 1 = 0 := hcycle.1 1 (by
      simp [FiberEdge, chartMap, fineNerve])
    have h2 : chain 2 = 0 := hcycle.1 2 (by
      simp [FiberEdge, chartMap, fineNerve])
    have h5 : chain 5 = 0 := hcycle.1 5 (by
      simp [FiberEdge, chartMap, fineNerve])
    have hdiv0 := hcycle.2 0 (by rfl)
    have hdiv1 := hcycle.2 1 (by rfl)
    simp [incoming, outgoing, fineNerve, Fin.sum_univ_succ] at hdiv0 hdiv1
    have h3 : chain 3 = 0 := by linarith
    have h4 : chain 4 = 0 := by linarith
    funext edge
    fin_cases edge <;> simp [h0, h1, h2, h3, h4, h5]
  · funext edge
    apply hcycle.1 edge
    fin_cases edge <;> simp [FiberEdge, chartMap, fineNerve]
  · funext edge
    apply hcycle.1 edge
    fin_cases edge <;> simp [FiberEdge, chartMap, fineNerve]

/-- C3 holds because each chart fiber graph is a tree. -/
theorem conditionC3 : ConditionC3 := by
  intro coarseChart chain hcycle
  refine ⟨0, ?_, ?_⟩
  · intro face _hface
    rfl
  · intro edge
    rw [fiberCycle_eq_zero coarseChart chain hcycle]
    simp [faceBoundary]

/-- C4 is witnessed by the actual fine filling face. -/
theorem conditionC4 : ConditionC4 := by
  intro coarseFace
  exact ⟨PUnit.unit, by cases coarseFace; rfl⟩

/-- C5 holds: every coarse edge has exactly the lift listed in C2. -/
theorem conditionC5 : ConditionC5 := by
  intro coarseEdge fineLeft fineRight hleft hright
  fin_cases coarseEdge <;> fin_cases fineLeft <;> fin_cases fineRight <;>
    simp [edgeMap] at hleft hright ⊢

/-- The coarse edge used by the obstruction is genuinely a self-loop. -/
theorem coarse_loop_endpoints_equal :
    coarseNerve.edgeLeft 3 = coarseNerve.edgeRight 3 :=
  rfl

/-- Its unique fine lift joins two distinct charts in the same chart fiber. -/
theorem fine_loop_lift_endpoints_distinct :
    fineNerve.edgeLeft 3 ≠ fineNerve.edgeRight 3 := by
  decide

/-- The fine comparison also contains a declared degenerate fiber edge. -/
theorem degenerate_fiber_edge_exists :
    ∃ fineEdge,
      nerveMorphism.edgeMap fineEdge = none ∧
        nerveMorphism.chartMap (fineNerve.edgeLeft fineEdge) =
          nerveMorphism.chartMap (fineNerve.edgeRight fineEdge) := by
  exact ⟨4, rfl, rfl⟩

/-! ## Law-generated incidence complexes and canonical comparison -/

/-- Coarse coordinates are the actual reviewed law values. -/
abbrev CoarseCoordinate := FaceLiftObstruction.CoarseCoordinate

/-- Fine coordinates are the same actual reviewed law values. -/
abbrev FineCoordinate := FaceLiftObstruction.FineCoordinate

/-- The coarse nerve expanded by the generated law values. -/
abbrev coarseLawNerve : CoverNerve where
  Chart := coarseNerve.Chart × CoarseCoordinate
  EdgeComponent := coarseNerve.EdgeComponent × CoarseCoordinate
  FaceComponent := coarseNerve.FaceComponent × CoarseCoordinate
  edgeLeft edge := (coarseNerve.edgeLeft edge.1, edge.2)
  edgeRight edge := (coarseNerve.edgeRight edge.1, edge.2)
  faceEdge0 face := (coarseNerve.faceEdge0 face.1, face.2)
  faceEdge1 face := (coarseNerve.faceEdge1 face.1, face.2)
  faceEdge2 face := (coarseNerve.faceEdge2 face.1, face.2)
  edgeOverlapComponent := fun _ => True
  faceTripleOverlapComponent := fun _ => True
  edgeOverlapComponent_holds := fun _ => trivial
  faceTripleOverlapComponent_holds := fun _ => trivial

/-- The fine nerve expanded by the generated law values. -/
abbrev fineLawNerve : CoverNerve where
  Chart := fineNerve.Chart × FineCoordinate
  EdgeComponent := fineNerve.EdgeComponent × FineCoordinate
  FaceComponent := fineNerve.FaceComponent × FineCoordinate
  edgeLeft edge := (fineNerve.edgeLeft edge.1, edge.2)
  edgeRight edge := (fineNerve.edgeRight edge.1, edge.2)
  faceEdge0 face := (fineNerve.faceEdge0 face.1, face.2)
  faceEdge1 face := (fineNerve.faceEdge1 face.1, face.2)
  faceEdge2 face := (fineNerve.faceEdge2 face.1, face.2)
  edgeOverlapComponent := fun _ => True
  faceTripleOverlapComponent := fun _ => True
  edgeOverlapComponent_holds := fun _ => trivial
  faceTripleOverlapComponent_holds := fun _ => trivial

/-- The actual coarse incidence complex over generated law values. -/
abbrev coarseCoefficientComplex :
    FiniteNerveCochainComplex coarseLawNerve ℚ where
  C0 := coarseLawNerve.Chart → ℚ
  C1 := coarseLawNerve.EdgeComponent → ℚ
  C2 := coarseLawNerve.FaceComponent → ℚ
  d0 := FaceLiftObstruction.edgeIncidence coarseLawNerve ℚ
  d1 := FaceLiftObstruction.faceIncidence coarseLawNerve ℚ
  d1_comp_d0 := by
    intro cochain
    funext face
    rcases face with ⟨face, coordinate⟩
    cases face
    simp [FaceLiftObstruction.edgeIncidence, FaceLiftObstruction.faceIncidence,
      coarseLawNerve, coarseNerve]
  zeroCochainCoordinates := LinearEquiv.refl ℚ _
  oneCochainCoordinates := LinearEquiv.refl ℚ _
  twoCochainCoordinates := LinearEquiv.refl ℚ _
  d0_eq_edgeIncidence := by intros; rfl
  d1_eq_faceIncidence := by intros; rfl

/-- The actual fine incidence complex over generated law values. -/
abbrev fineCoefficientComplex :
    FiniteNerveCochainComplex fineLawNerve ℚ where
  C0 := fineLawNerve.Chart → ℚ
  C1 := fineLawNerve.EdgeComponent → ℚ
  C2 := fineLawNerve.FaceComponent → ℚ
  d0 := FaceLiftObstruction.edgeIncidence fineLawNerve ℚ
  d1 := FaceLiftObstruction.faceIncidence fineLawNerve ℚ
  d1_comp_d0 := by
    intro cochain
    funext face
    rcases face with ⟨face, coordinate⟩
    cases face
    simp [FaceLiftObstruction.edgeIncidence, FaceLiftObstruction.faceIncidence,
      fineLawNerve, fineNerve]
  zeroCochainCoordinates := LinearEquiv.refl ℚ _
  oneCochainCoordinates := LinearEquiv.refl ℚ _
  twoCochainCoordinates := LinearEquiv.refl ℚ _
  d0_eq_edgeIncidence := by intros; rfl
  d1_eq_faceIncidence := by intros; rfl

/-- The coarse generated coefficient complex in the shared G-102 API. -/
abbrev coarseComplex : ThreeCochainComplex ℚ :=
  FaceLiftObstruction.asThreeComplex coarseCoefficientComplex

/-- The fine generated coefficient complex in the shared G-102 API. -/
abbrev fineComplex : ThreeCochainComplex ℚ :=
  FaceLiftObstruction.asThreeComplex fineCoefficientComplex

/-- Pullback of chart cochains along the chart and generated-value maps. -/
def pullback0 : coarseComplex.C0 →ₗ[ℚ] fineComplex.C0 where
  toFun cochain chart :=
    cochain (nerveMorphism.chartMap chart.1,
      FaceLiftObstruction.coordinateMap chart.2)
  map_add' left right := by funext chart; simp
  map_smul' scalar cochain := by funext chart; simp

/-- Pullback of edge cochains, zero on the declared degenerate edge. -/
def pullback1 : coarseComplex.C1 →ₗ[ℚ] fineComplex.C1 where
  toFun cochain edge :=
    match nerveMorphism.edgeMap edge.1 with
    | none => 0
    | some coarseEdge =>
        cochain (coarseEdge, FaceLiftObstruction.coordinateMap edge.2)
  map_add' left right := by
    funext edge
    rcases edge with ⟨edge, coordinate⟩
    fin_cases edge <;> simp [edgeMap]
  map_smul' scalar cochain := by
    funext edge
    rcases edge with ⟨edge, coordinate⟩
    fin_cases edge <;> simp [edgeMap]

/-- Pullback of face cochains along the nonvacuous C4 lift. -/
def pullback2 : coarseComplex.C2 →ₗ[ℚ] fineComplex.C2 where
  toFun cochain face :=
    match nerveMorphism.faceMap face.1 with
    | none => 0
    | some coarseFace =>
        cochain (coarseFace, FaceLiftObstruction.coordinateMap face.2)
  map_add' left right := by
    funext face
    rcases face with ⟨face, coordinate⟩
    cases face
    simp [faceMap]
  map_smul' scalar cochain := by
    funext face
    rcases face with ⟨face, coordinate⟩
    cases face
    simp [faceMap]

/-- The cochain map generated by the nerve morphism and canonical law values. -/
def comparisonCochainMap :
    ThreeCochainComplex.Hom coarseComplex fineComplex where
  f0 := pullback0
  f1 := pullback1
  f2 := pullback2
  comm0 := by
    intro cochain
    funext edge
    rcases edge with ⟨edge, coordinate⟩
    fin_cases edge <;>
      simp [pullback0, pullback1, FaceLiftObstruction.edgeIncidence,
        coarseComplex, fineComplex, FaceLiftObstruction.asThreeComplex,
        coarseCoefficientComplex, fineCoefficientComplex,
        coarseLawNerve, fineLawNerve, coarseNerve, fineNerve,
        edgeMap, chartMap]
  comm1 := by
    intro cochain
    funext face
    rcases face with ⟨face, coordinate⟩
    cases face
    simp [pullback1, pullback2, FaceLiftObstruction.faceIncidence,
      coarseComplex, fineComplex, FaceLiftObstruction.asThreeComplex,
      coarseCoefficientComplex, fineCoefficientComplex,
      coarseLawNerve, fineLawNerve, coarseNerve, fineNerve,
      edgeMap, faceMap]

/-- The canonical map on standard first cohomology. -/
def comparisonH1Map : coarseComplex.H1 →ₗ[ℚ] fineComplex.H1 :=
  comparisonCochainMap.h1Map

/-- The nonvacuous C4 face is the actual fine degree-one differential. -/
theorem fine_d1_formula (cochain : fineComplex.C1)
    (coordinate : FineCoordinate) :
    fineComplex.d1 cochain (PUnit.unit, coordinate) =
      cochain (0, coordinate) - cochain (1, coordinate) +
        cochain (2, coordinate) :=
  rfl

/-! ## A nonzero coarse loop class killed by the canonical map -/

/-- One actual generated law coordinate used by the witness classes. -/
def selectedCoordinate : CoarseCoordinate := 0

/-- Evaluation on the coarse self-loop coordinate. -/
def coarseLoopPeriod (cochain : coarseComplex.C1) : ℚ :=
  cochain (3, selectedCoordinate)

/-- Every coarse coboundary vanishes on the coarse self-loop. -/
theorem coarseLoopPeriod_boundary_zero (cochain : coarseComplex.C0) :
    coarseLoopPeriod (coarseComplex.d0 cochain) = 0 := by
  simp [coarseLoopPeriod, coarseComplex, FaceLiftObstruction.asThreeComplex,
    coarseCoefficientComplex, FaceLiftObstruction.edgeIncidence,
    coarseLawNerve, coarseNerve]

/-- The standard basis cochain on the coarse self-loop. -/
def coarseLoopCochain : coarseComplex.C1 :=
  coordinateVector (3, selectedCoordinate)

/-- The coarse self-loop cochain is a cocycle. -/
theorem coarseLoopCochain_cocycle :
    coarseComplex.d1 coarseLoopCochain = 0 := by
  funext face
  rcases face with ⟨face, coordinate⟩
  cases face
  change _ = (0 : ℚ)
  simp [coarseComplex, FaceLiftObstruction.asThreeComplex,
    coarseCoefficientComplex, FaceLiftObstruction.faceIncidence,
    coarseLoopCochain, coordinateVector, coarseLawNerve, coarseNerve]

/-- The explicit coarse cocycle supported on the self-loop. -/
def coarseLoopCycle : LinearMap.ker coarseComplex.d1 :=
  ⟨coarseLoopCochain, coarseLoopCochain_cocycle⟩

/-- The standard first-cohomology class of the coarse self-loop. -/
def coarseLoopClass : coarseComplex.H1 :=
  (LinearMap.range coarseComplex.boundaryToCycles).mkQ coarseLoopCycle

/-- The coarse self-loop cochain has unit loop period. -/
theorem coarseLoopPeriod_firing :
    coarseLoopPeriod coarseLoopCycle.1 = 1 := by
  simp [coarseLoopPeriod, coarseLoopCycle, coarseLoopCochain,
    coordinateVector, selectedCoordinate]

/-- The coarse self-loop gives a nonzero first-cohomology class. -/
theorem coarseLoopClass_ne_zero : coarseLoopClass ≠ 0 := by
  intro hzero
  have hmem := (Submodule.Quotient.mk_eq_zero
    (LinearMap.range coarseComplex.boundaryToCycles)).1 hzero
  rcases hmem with ⟨cochain, hcochain⟩
  have hperiod := congrArg (fun cycle : LinearMap.ker coarseComplex.d1 =>
    coarseLoopPeriod cycle.1) hcochain
  change coarseLoopPeriod (coarseComplex.d0 cochain) =
    coarseLoopPeriod coarseLoopCycle.1 at hperiod
  rw [coarseLoopPeriod_boundary_zero, coarseLoopPeriod_firing] at hperiod
  exact zero_ne_one hperiod

/-- A fine zero-cochain whose coboundary is the pulled-back coarse loop. -/
def fineLoopPrimitive : fineComplex.C0 := fun chart =>
  if chart.2 = selectedCoordinate ∧ (chart.1 = 1 ∨ chart.1 = 2) then 1 else 0

/-- Pullback of the coarse loop cocycle is the displayed fine coboundary. -/
theorem pullback1_coarseLoopCochain :
    pullback1 coarseLoopCochain = fineComplex.d0 fineLoopPrimitive := by
  funext edge
  rcases edge with ⟨edge, coordinate⟩
  fin_cases edge <;> fin_cases coordinate <;>
    simp [pullback1, coarseLoopCochain, coordinateVector, selectedCoordinate,
      fineLoopPrimitive, fineComplex, FaceLiftObstruction.asThreeComplex,
      fineCoefficientComplex, FaceLiftObstruction.edgeIncidence,
      fineLawNerve, fineNerve, edgeMap]

/-- The canonical map kills the coarse loop class. -/
theorem comparisonH1Map_coarseLoopClass_zero :
    comparisonH1Map coarseLoopClass = 0 := by
  change comparisonCochainMap.h1Map
      ((LinearMap.range coarseComplex.boundaryToCycles).mkQ coarseLoopCycle) = 0
  rw [ThreeCochainComplex.Hom.h1Map_mk]
  apply (Submodule.Quotient.mk_eq_zero
    (LinearMap.range fineComplex.boundaryToCycles)).2
  refine ⟨fineLoopPrimitive, ?_⟩
  apply Subtype.ext
  exact pullback1_coarseLoopCochain.symm

/-- The canonical comparison map is not injective on first cohomology. -/
theorem comparisonH1Map_not_injective :
    ¬ Function.Injective comparisonH1Map := by
  intro hinjective
  apply coarseLoopClass_ne_zero
  apply hinjective
  simpa using comparisonH1Map_coarseLoopClass_zero

/-! ## A separate fine class witnessing nonvanishing -/

/-- Difference across the unfilled parallel fine edges. -/
def fineParallelPeriod (cochain : fineComplex.C1) : ℚ :=
  cochain (5, selectedCoordinate) - cochain (0, selectedCoordinate)

/-- Every fine coboundary has zero parallel-edge period. -/
theorem fineParallelPeriod_boundary_zero (cochain : fineComplex.C0) :
    fineParallelPeriod (fineComplex.d0 cochain) = 0 := by
  simp [fineParallelPeriod, fineComplex, FaceLiftObstruction.asThreeComplex,
    fineCoefficientComplex, FaceLiftObstruction.edgeIncidence,
    fineLawNerve, fineNerve]

/-- The standard basis cochain on the unfilled parallel edge. -/
def fineSurvivingCochain : fineComplex.C1 :=
  coordinateVector (5, selectedCoordinate)

/-- The unfilled parallel-edge cochain is a cocycle. -/
theorem fineSurvivingCochain_cocycle :
    fineComplex.d1 fineSurvivingCochain = 0 := by
  funext face
  rcases face with ⟨face, coordinate⟩
  cases face
  change _ = (0 : ℚ)
  simp [fineComplex, FaceLiftObstruction.asThreeComplex,
    fineCoefficientComplex, FaceLiftObstruction.faceIncidence,
    fineSurvivingCochain, coordinateVector, fineLawNerve, fineNerve]

/-- The explicit nonzero fine cocycle. -/
def fineSurvivingCycle : LinearMap.ker fineComplex.d1 :=
  ⟨fineSurvivingCochain, fineSurvivingCochain_cocycle⟩

/-- Its standard first-cohomology class. -/
def fineSurvivingClass : fineComplex.H1 :=
  (LinearMap.range fineComplex.boundaryToCycles).mkQ fineSurvivingCycle

/-- The surviving fine cochain has unit parallel-edge period. -/
theorem fineParallelPeriod_firing :
    fineParallelPeriod fineSurvivingCycle.1 = 1 := by
  simp [fineParallelPeriod, fineSurvivingCycle, fineSurvivingCochain,
    coordinateVector, selectedCoordinate]

/-- The fine side has a nonzero first-cohomology class independent of the killed loop. -/
theorem fineSurvivingClass_ne_zero : fineSurvivingClass ≠ 0 := by
  intro hzero
  have hmem := (Submodule.Quotient.mk_eq_zero
    (LinearMap.range fineComplex.boundaryToCycles)).1 hzero
  rcases hmem with ⟨cochain, hcochain⟩
  have hperiod := congrArg (fun cycle : LinearMap.ker fineComplex.d1 =>
    fineParallelPeriod cycle.1) hcochain
  change fineParallelPeriod (fineComplex.d0 cochain) =
    fineParallelPeriod fineSurvivingCycle.1 at hperiod
  rw [fineParallelPeriod_boundary_zero, fineParallelPeriod_firing] at hperiod
  exact zero_ne_one hperiod

/-!
## Fixed-condition blocker
-/

/--
The same proper adequate law-generated comparison satisfies C0--C5, has a
nonvacuous face and a declared degenerate fiber edge, and has nonzero `H^1` on
both sides.  Nevertheless its canonical coarse-to-fine map kills the nonzero
coarse self-loop class and is therefore not injective.
-/
theorem fixedConditionC0C5_not_sufficient :
    let supportCompatible : Prop :=
      ∀ chart target, target ∈ fineSupported.chartSupport chart →
        comparisonFactor coarseReading fineReading
            FaceLiftObstruction.coarse_coarser_fine target ∈
          coarseSupported.chartSupport (nerveMorphism.chartMap chart)
    let conditionC0 : Prop :=
      ∀ coarseChart target,
        target ∈ coarseSupported.chartSupport coarseChart ↔
          ∃ fineChart fineTarget,
            nerveMorphism.chartMap fineChart = coarseChart ∧
            fineTarget ∈ fineSupported.chartSupport fineChart ∧
            comparisonFactor coarseReading fineReading
                FaceLiftObstruction.coarse_coarser_fine fineTarget = target
    let fiberAdjacent : fineNerve.Chart → fineNerve.Chart → Prop :=
      fun left right =>
        ∃ edge,
          ((fineNerve.edgeLeft edge = left ∧
              fineNerve.edgeRight edge = right) ∨
            (fineNerve.edgeLeft edge = right ∧
              fineNerve.edgeRight edge = left)) ∧
          nerveMorphism.chartMap left = nerveMorphism.chartMap right
    let conditionC1 : Prop :=
      ∀ coarseChart,
        (∃ fineChart, nerveMorphism.chartMap fineChart = coarseChart) ∧
          ∀ left right,
            nerveMorphism.chartMap left = coarseChart →
            nerveMorphism.chartMap right = coarseChart →
            Relation.ReflTransGen fiberAdjacent left right
    let conditionC2 : Prop :=
      ∀ coarseEdge, ∃ fineEdge,
        nerveMorphism.edgeMap fineEdge = some coarseEdge
    let fiberEdge : coarseNerve.Chart → fineNerve.EdgeComponent → Prop :=
      fun coarseChart edge =>
        nerveMorphism.chartMap (fineNerve.edgeLeft edge) = coarseChart ∧
          nerveMorphism.chartMap (fineNerve.edgeRight edge) = coarseChart
    let incoming : (fineNerve.EdgeComponent → ℚ) → fineNerve.Chart → ℚ :=
      fun chain chart =>
        ∑ edge, if fineNerve.edgeRight edge = chart then chain edge else 0
    let outgoing : (fineNerve.EdgeComponent → ℚ) → fineNerve.Chart → ℚ :=
      fun chain chart =>
        ∑ edge, if fineNerve.edgeLeft edge = chart then chain edge else 0
    let isFiberCycle : coarseNerve.Chart →
        (fineNerve.EdgeComponent → ℚ) → Prop := fun coarseChart chain =>
      (∀ edge, ¬ fiberEdge coarseChart edge → chain edge = 0) ∧
        ∀ chart, nerveMorphism.chartMap chart = coarseChart →
          incoming chain chart = outgoing chain chart
    let internalFace : coarseNerve.Chart → fineNerve.FaceComponent → Prop :=
      fun coarseChart face =>
        fiberEdge coarseChart (fineNerve.faceEdge0 face) ∧
          fiberEdge coarseChart (fineNerve.faceEdge1 face) ∧
          fiberEdge coarseChart (fineNerve.faceEdge2 face)
    let faceBoundary : (fineNerve.FaceComponent → ℚ) →
        fineNerve.EdgeComponent → ℚ := fun faces edge =>
      (∑ face, if fineNerve.faceEdge0 face = edge then faces face else 0) -
        (∑ face, if fineNerve.faceEdge1 face = edge then faces face else 0) +
          ∑ face, if fineNerve.faceEdge2 face = edge then faces face else 0
    let conditionC3 : Prop :=
      ∀ coarseChart chain, isFiberCycle coarseChart chain →
        ∃ faces : fineNerve.FaceComponent → ℚ,
          (∀ face, ¬ internalFace coarseChart face → faces face = 0) ∧
            ∀ edge, chain edge = faceBoundary faces edge
    let conditionC4 : Prop :=
      ∀ coarseFace, ∃ fineFace,
        nerveMorphism.faceMap fineFace = some coarseFace
    let conditionC5 : Prop :=
      ∀ coarseEdge fineLeft fineRight,
        nerveMorphism.edgeMap fineLeft = some coarseEdge →
        nerveMorphism.edgeMap fineRight = some coarseEdge →
        fineLeft = fineRight
    laws.Adequate coarseReading ∧
      laws.Adequate fineReading ∧
      coarseReading.CoarserThan fineReading ∧
      supportCompatible ∧
      conditionC0 ∧
      conditionC1 ∧
      conditionC2 ∧
      conditionC3 ∧
      conditionC4 ∧
      conditionC5 ∧
      (¬ Function.Injective
        (comparisonFactor coarseReading fineReading
          FaceLiftObstruction.coarse_coarser_fine)) ∧
      (∃ law x y, laws.eval law x ≠ laws.eval law y) ∧
      (∀ value : CoarseCoordinate,
        ∃ target : coarseReading.Target,
          target ∈ (Set.univ : Set coarseReading.Target) ∧
          lawDescend laws coarseReading FaceLiftObstruction.coarse_adequate
            PUnit.unit target = value) ∧
      (∀ value : FineCoordinate,
        ∃ target : fineReading.Target,
          target ∈ (Set.univ : Set fineReading.Target) ∧
          lawDescend laws fineReading FaceLiftObstruction.fine_adequate
            PUnit.unit target = value) ∧
      (∀ target : fineReading.Target,
        lawDescend laws coarseReading FaceLiftObstruction.coarse_adequate
            PUnit.unit
            (comparisonFactor coarseReading fineReading
              FaceLiftObstruction.coarse_coarser_fine target) =
          FaceLiftObstruction.coordinateMap
            (lawDescend laws fineReading FaceLiftObstruction.fine_adequate
              PUnit.unit target)) ∧
      coarseNerve.edgeLeft 3 = coarseNerve.edgeRight 3 ∧
      nerveMorphism.edgeMap 3 = some 3 ∧
      fineNerve.edgeLeft 3 ≠ fineNerve.edgeRight 3 ∧
      (∃ fineEdge,
        nerveMorphism.edgeMap fineEdge = none ∧
          nerveMorphism.chartMap (fineNerve.edgeLeft fineEdge) =
            nerveMorphism.chartMap (fineNerve.edgeRight fineEdge)) ∧
      coarseLoopClass ≠ 0 ∧
      fineSurvivingClass ≠ 0 ∧
      (¬ Function.Injective comparisonH1Map) := by
  dsimp only
  exact ⟨FaceLiftObstruction.coarse_adequate,
    FaceLiftObstruction.fine_adequate,
    FaceLiftObstruction.coarse_coarser_fine, support_compatible, conditionC0,
    conditionC1, conditionC2, conditionC3, conditionC4, conditionC5,
    FaceLiftObstruction.comparisonFactor_not_injective,
    FaceLiftObstruction.law_nonconstant,
    FaceLiftObstruction.coarseCoordinate_generated,
    FaceLiftObstruction.fineCoordinate_generated,
    FaceLiftObstruction.coordinateMap_descend_compatible,
    coarse_loop_endpoints_equal, rfl, fine_loop_lift_endpoints_distinct,
    degenerate_fiber_edge_exists, coarseLoopClass_ne_zero,
    fineSurvivingClass_ne_zero, comparisonH1Map_not_injective⟩

end LoopLiftObstruction

end AAT.AG.ResolutionInvariance

#assert_standard_axioms_only AAT.AG.ResolutionInvariance.LoopLiftObstruction
