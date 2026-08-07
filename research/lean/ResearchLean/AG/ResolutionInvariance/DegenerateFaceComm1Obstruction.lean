import ResearchLean.AG.ResolutionInvariance.FaceLiftObstruction
import ResearchLean.AG.ResolutionInvariance.LawGeneratedComplex
import ResearchLean.AG.TwoPhase.CohomologyComparison
import Formal.Util.AssertStandardAxioms

/-!
# A degenerate-face obstruction to the canonical comparison map

This module tests claim (i) of the revised
`G-104-aat-resolution-invariance` statement against the literal degeneracy
rule fixed by the GOAL.  A fiber-internal edge is defined by its endpoint chart
images.  Such an edge may still map to a coarse self-loop.  The GOAL also
permits a fine face whose three boundary edges are fiber-internal to have no
coarse face image, with degree-two pullback zero on that degenerate face.

The finite witness below uses a proper adequate reading pair and a nonconstant
law.  Its coefficient spaces and differentials are the K0/K1
`lawGeneratedComplex` objects, not a freely declared proxy.  One fine
self-loop maps to one coarse self-loop, while a fine face with boundary
`(e,e,e)` is declared degenerate.  The standard basis cochain on the generated
coarse edge coordinate pulls back with boundary value `1 - 1 + 1 = 1`, whereas
the generated degree-two pullback is zero.  Therefore the prescribed maps
cannot be the components of a `ThreeCochainComplex.Hom`.
-/

noncomputable section

namespace AAT.AG.ResolutionInvariance

open CanonicalResolution Cohomology TwoPhase

namespace DegenerateFaceComm1Obstruction

/-! ## A proper adequate pair with a nonconstant law -/

/-- Reuse only the reviewed reading/law input of the earlier finite witness. -/
abbrev Source := FaceLiftObstruction.Source

abbrev fineReading : Reading Source := FaceLiftObstruction.fineReading

abbrev coarseReading : Reading Source := FaceLiftObstruction.coarseReading

abbrev laws : FiniteLawFamily Source := FaceLiftObstruction.laws

theorem coarse_adequate : laws.Adequate coarseReading :=
  FaceLiftObstruction.coarse_adequate

theorem fine_adequate : laws.Adequate fineReading :=
  FaceLiftObstruction.fine_adequate

theorem coarse_coarser_fine : coarseReading.CoarserThan fineReading :=
  FaceLiftObstruction.coarse_coarser_fine

theorem comparisonFactor_not_injective :
    ¬ Function.Injective
      (comparisonFactor coarseReading fineReading coarse_coarser_fine) :=
  FaceLiftObstruction.comparisonFactor_not_injective

theorem law_nonconstant :
    ∃ law x y, laws.eval law x ≠ laws.eval law y :=
  FaceLiftObstruction.law_nonconstant

/-! ## Literal endpoint-degenerate comparison geometry -/

/--
The literal partial nerve morphism described by the fixed GOAL.  A missing edge
must have endpoints in one chart fiber.  A missing face only requires each
boundary edge to be fiber-internal by that endpoint condition; it does not
require those edges themselves to have `edgeMap = none`.
-/
structure EndpointDegenerateNerveMorphism (fine coarse : CoverNerve) where
  chartMap : fine.Chart → coarse.Chart
  edgeMap : fine.EdgeComponent → Option coarse.EdgeComponent
  faceMap : fine.FaceComponent → Option coarse.FaceComponent
  edge_some_left : ∀ fineEdge coarseEdge,
    edgeMap fineEdge = some coarseEdge →
      chartMap (fine.edgeLeft fineEdge) = coarse.edgeLeft coarseEdge
  edge_some_right : ∀ fineEdge coarseEdge,
    edgeMap fineEdge = some coarseEdge →
      chartMap (fine.edgeRight fineEdge) = coarse.edgeRight coarseEdge
  edge_none_fiber : ∀ fineEdge,
    edgeMap fineEdge = none →
      chartMap (fine.edgeLeft fineEdge) = chartMap (fine.edgeRight fineEdge)
  face_some_edge0 : ∀ fineFace coarseFace,
    faceMap fineFace = some coarseFace →
      edgeMap (fine.faceEdge0 fineFace) = some (coarse.faceEdge0 coarseFace)
  face_some_edge1 : ∀ fineFace coarseFace,
    faceMap fineFace = some coarseFace →
      edgeMap (fine.faceEdge1 fineFace) = some (coarse.faceEdge1 coarseFace)
  face_some_edge2 : ∀ fineFace coarseFace,
    faceMap fineFace = some coarseFace →
      edgeMap (fine.faceEdge2 fineFace) = some (coarse.faceEdge2 coarseFace)
  face_none_edge0_fiber : ∀ fineFace,
    faceMap fineFace = none →
      chartMap (fine.edgeLeft (fine.faceEdge0 fineFace)) =
        chartMap (fine.edgeRight (fine.faceEdge0 fineFace))
  face_none_edge1_fiber : ∀ fineFace,
    faceMap fineFace = none →
      chartMap (fine.edgeLeft (fine.faceEdge1 fineFace)) =
        chartMap (fine.edgeRight (fine.faceEdge1 fineFace))
  face_none_edge2_fiber : ∀ fineFace,
    faceMap fineFace = none →
      chartMap (fine.edgeLeft (fine.faceEdge2 fineFace)) =
        chartMap (fine.edgeRight (fine.faceEdge2 fineFace))

/-- One coarse chart, one coarse self-loop, and no coarse face. -/
abbrev coarseNerve : CoverNerve where
  Chart := PUnit
  EdgeComponent := PUnit
  FaceComponent := Empty
  edgeLeft _ := PUnit.unit
  edgeRight _ := PUnit.unit
  faceEdge0 := Empty.elim
  faceEdge1 := Empty.elim
  faceEdge2 := Empty.elim
  edgeOverlapComponent := fun _ => True
  faceTripleOverlapComponent := fun _ => True
  edgeOverlapComponent_holds := fun _ => trivial
  faceTripleOverlapComponent_holds := Empty.elim

/--
One fine chart, one fine self-loop, and one fine face whose oriented boundary
uses that edge in all three positions.
-/
abbrev fineNerve : CoverNerve where
  Chart := PUnit
  EdgeComponent := PUnit
  FaceComponent := PUnit
  edgeLeft _ := PUnit.unit
  edgeRight _ := PUnit.unit
  faceEdge0 _ := PUnit.unit
  faceEdge1 _ := PUnit.unit
  faceEdge2 _ := PUnit.unit
  edgeOverlapComponent := fun _ => True
  faceTripleOverlapComponent := fun _ => True
  edgeOverlapComponent_holds := fun _ => trivial
  faceTripleOverlapComponent_holds := fun _ => trivial

/-- The coarse K0/K1 input nerve has full nonempty chart support. -/
abbrev coarseSupported : TargetSupportedNerve coarseReading where
  nerve := coarseNerve
  chartFintype := inferInstance
  edgeFintype := inferInstance
  faceFintype := inferInstance
  chartSupport := fun _ => Set.univ
  chartSupport_nonempty := fun _ => ⟨0, Set.mem_univ _⟩
  faceEdge0_left := fun face => Empty.elim face
  faceEdge0_right := fun face => Empty.elim face
  faceEdge1_right := fun face => Empty.elim face

/-- The fine K0/K1 input nerve also has full nonempty chart support. -/
abbrev fineSupported : TargetSupportedNerve fineReading where
  nerve := fineNerve
  chartFintype := inferInstance
  edgeFintype := inferInstance
  faceFintype := inferInstance
  chartSupport := fun _ => Set.univ
  chartSupport_nonempty := fun _ => ⟨0, Set.mem_univ _⟩
  faceEdge0_left := fun _ => rfl
  faceEdge0_right := fun _ => rfl
  faceEdge1_right := fun _ => rfl

/-- The unique fine chart maps to the unique coarse chart. -/
def chartMap (_chart : fineNerve.Chart) : coarseNerve.Chart :=
  PUnit.unit

/-- The fine self-loop is nondegenerate and maps to the coarse self-loop. -/
def edgeMap (_edge : fineNerve.EdgeComponent) :
    Option coarseNerve.EdgeComponent :=
  some PUnit.unit

/-- The fine face has no coarse face image. -/
def faceMap (_face : fineNerve.FaceComponent) :
    Option coarseNerve.FaceComponent :=
  none

/-- The finite comparison data satisfies the literal endpoint-degeneracy rule. -/
abbrev nerveMorphism :
    EndpointDegenerateNerveMorphism fineNerve coarseNerve where
  chartMap := chartMap
  edgeMap := edgeMap
  faceMap := faceMap
  edge_some_left := by intros; rfl
  edge_some_right := by intros; rfl
  edge_none_fiber := by intros; rfl
  face_some_edge0 := by
    intro _fineFace coarseFace
    exact Empty.elim coarseFace
  face_some_edge1 := by
    intro _fineFace coarseFace
    exact Empty.elim coarseFace
  face_some_edge2 := by
    intro _fineFace coarseFace
    exact Empty.elim coarseFace
  face_none_edge0_fiber := by intros; rfl
  face_none_edge1_fiber := by intros; rfl
  face_none_edge2_fiber := by intros; rfl

/-- The unique fine edge is fiber-internal by the fixed endpoint definition. -/
theorem fine_edge_fiber_internal :
    nerveMorphism.chartMap (fineNerve.edgeLeft PUnit.unit) =
      nerveMorphism.chartMap (fineNerve.edgeRight PUnit.unit) :=
  rfl

/-- The same fiber-internal edge nevertheless maps to a coarse self-loop. -/
theorem fine_edge_maps_to_coarse_self_loop :
    nerveMorphism.edgeMap PUnit.unit = some PUnit.unit :=
  rfl

/-- The fine face is declared degenerate under the literal GOAL rule. -/
theorem fine_face_declared_degenerate :
    nerveMorphism.faceMap PUnit.unit = none :=
  rfl

/-- All three boundary edges are fiber-internal, nonvacuously. -/
theorem fine_face_boundary_fiber_internal :
    nerveMorphism.chartMap
        (fineNerve.edgeLeft (fineNerve.faceEdge0 PUnit.unit)) =
        nerveMorphism.chartMap
          (fineNerve.edgeRight (fineNerve.faceEdge0 PUnit.unit)) ∧
      nerveMorphism.chartMap
        (fineNerve.edgeLeft (fineNerve.faceEdge1 PUnit.unit)) =
        nerveMorphism.chartMap
          (fineNerve.edgeRight (fineNerve.faceEdge1 PUnit.unit)) ∧
      nerveMorphism.chartMap
        (fineNerve.edgeLeft (fineNerve.faceEdge2 PUnit.unit)) =
        nerveMorphism.chartMap
          (fineNerve.edgeRight (fineNerve.faceEdge2 PUnit.unit)) :=
  ⟨rfl, rfl, rfl⟩

/-- Full chart supports are compatible with the canonical comparison factor. -/
theorem chartSupport_compatible (chart : fineNerve.Chart)
    (target : fineReading.Target)
    (_htarget : target ∈ fineSupported.chartSupport chart) :
    comparisonFactor coarseReading fineReading coarse_coarser_fine target ∈
      coarseSupported.chartSupport (nerveMorphism.chartMap chart) := by
  simp

/-! ## Canonical coordinate maps and generated pullbacks -/

/-- Canonical chart-coordinate transport generated by `π` and law descent. -/
def chartCoordinateMap
    (coordinate : fineSupported.ChartCoordinate laws fine_adequate) :
    coarseSupported.ChartCoordinate laws coarse_adequate := by
  refine ⟨PUnit.unit, coordinate.law, coordinate.value, ?_⟩
  obtain ⟨target, htarget, hvalue⟩ := coordinate.generated
  refine ⟨comparisonFactor coarseReading fineReading coarse_coarser_fine target,
    chartSupport_compatible coordinate.cell target htarget, ?_⟩
  exact (lawDescend_comparisonFactor laws coarseReading fineReading
    coarse_adequate fine_adequate coarse_coarser_fine coordinate.law target).trans
      hvalue

/-- Canonical edge-coordinate transport along the mapped self-loop. -/
def edgeCoordinateMap
    (coordinate : fineSupported.EdgeCoordinate laws fine_adequate) :
    coarseSupported.EdgeCoordinate laws coarse_adequate := by
  refine ⟨PUnit.unit, coordinate.law, coordinate.value, ?_⟩
  obtain ⟨target, htarget, hvalue⟩ := coordinate.generated
  refine ⟨comparisonFactor coarseReading fineReading coarse_coarser_fine target,
    ?_, ?_⟩
  · simp [TargetSupportedNerve.edgeSupport]
  · exact (lawDescend_comparisonFactor laws coarseReading fineReading
      coarse_adequate fine_adequate coarse_coarser_fine coordinate.law target).trans
        hvalue

/-- Generated degree-zero pullback along the unique chart map. -/
def generatedPullback0 :
    (coarseSupported.ChartCoordinate laws coarse_adequate → ℚ) →ₗ[ℚ]
      (fineSupported.ChartCoordinate laws fine_adequate → ℚ) where
  toFun cochain coordinate := cochain (chartCoordinateMap coordinate)
  map_add' left right := by ext; simp
  map_smul' scalar cochain := by ext; simp

/-- Generated degree-one pullback along the mapped self-loop. -/
def generatedPullback1 :
    (coarseSupported.EdgeCoordinate laws coarse_adequate → ℚ) →ₗ[ℚ]
      (fineSupported.EdgeCoordinate laws fine_adequate → ℚ) where
  toFun cochain coordinate := cochain (edgeCoordinateMap coordinate)
  map_add' left right := by ext; simp
  map_smul' scalar cochain := by ext; simp

/-- Generated degree-two pullback is zero on the declared degenerate face. -/
def generatedPullback2 :
    (coarseSupported.FaceCoordinate laws coarse_adequate → ℚ) →ₗ[ℚ]
      (fineSupported.FaceCoordinate laws fine_adequate → ℚ) :=
  0

/-- The actual K0/K1 coarse complex. -/
abbrev coarseComplex : ThreeCochainComplex ℚ :=
  coarseSupported.lawGeneratedComplex laws coarse_adequate

/-- The actual K0/K1 fine complex. -/
abbrev fineComplex : ThreeCochainComplex ℚ :=
  fineSupported.lawGeneratedComplex laws fine_adequate

/-- A genuine fine face coordinate generated from the actual law descent. -/
def selectedFineFaceCoordinate :
    fineSupported.FaceCoordinate laws fine_adequate :=
  CellCoordinate.ofSupportedTarget laws fineReading fine_adequate
    fineNerve.FaceComponent fineSupported.faceSupport PUnit.unit PUnit.unit 0
    (by
      simp [TargetSupportedNerve.faceSupport,
        TargetSupportedNerve.edgeSupport])

/-- The mapped coarse edge coordinate occurring on boundary edge zero. -/
def selectedCoarseEdgeCoordinate :
    coarseSupported.EdgeCoordinate laws coarse_adequate :=
  edgeCoordinateMap
    (fineSupported.faceEdge0Coordinate laws fine_adequate
      selectedFineFaceCoordinate)

theorem edgeCoordinateMap_faceEdge0_eq_selected :
    edgeCoordinateMap
        (fineSupported.faceEdge0Coordinate laws fine_adequate
          selectedFineFaceCoordinate) =
      selectedCoarseEdgeCoordinate :=
  rfl

theorem edgeCoordinateMap_faceEdge1_eq_selected :
    edgeCoordinateMap
        (fineSupported.faceEdge1Coordinate laws fine_adequate
          selectedFineFaceCoordinate) =
      selectedCoarseEdgeCoordinate := by
  apply CellCoordinate.ext <;> rfl

theorem edgeCoordinateMap_faceEdge2_eq_selected :
    edgeCoordinateMap
        (fineSupported.faceEdge2Coordinate laws fine_adequate
          selectedFineFaceCoordinate) =
      selectedCoarseEdgeCoordinate := by
  apply CellCoordinate.ext <;> rfl

/-- Standard basis cochain on an actual law-generated coarse edge coordinate. -/
def selectedCoarseCochain : coarseComplex.C1 :=
  coordinateVector selectedCoarseEdgeCoordinate

/--
The prescribed degree-one and degree-two pullbacks fail the cochain-map law on
the literal degenerate face.
-/
theorem generated_pullback_comm1_fails :
    generatedPullback2 (coarseComplex.d1 selectedCoarseCochain) ≠
      fineComplex.d1 (generatedPullback1 selectedCoarseCochain) := by
  intro hcomm
  have hface := congrFun hcomm selectedFineFaceCoordinate
  have hleft :
      generatedPullback2 (coarseComplex.d1 selectedCoarseCochain)
          selectedFineFaceCoordinate = 0 := by
    simp [generatedPullback2]
  have hright :
      fineComplex.d1 (generatedPullback1 selectedCoarseCochain)
          selectedFineFaceCoordinate = 1 := by
    change fineSupported.lawGeneratedD1 laws fine_adequate
        (generatedPullback1 selectedCoarseCochain)
          selectedFineFaceCoordinate = 1
    rw [fineSupported.lawGeneratedD1_apply]
    change selectedCoarseCochain
          (edgeCoordinateMap (fineSupported.faceEdge0Coordinate laws
            fine_adequate selectedFineFaceCoordinate)) -
        selectedCoarseCochain
          (edgeCoordinateMap (fineSupported.faceEdge1Coordinate laws
            fine_adequate selectedFineFaceCoordinate)) +
        selectedCoarseCochain
          (edgeCoordinateMap (fineSupported.faceEdge2Coordinate laws
            fine_adequate selectedFineFaceCoordinate)) = 1
    rw [edgeCoordinateMap_faceEdge0_eq_selected,
      edgeCoordinateMap_faceEdge1_eq_selected,
      edgeCoordinateMap_faceEdge2_eq_selected]
    simp [selectedCoarseCochain, coordinateVector]
  have hzeroOne : (0 : ℚ) = 1 := hleft.symm.trans (hface.trans hright)
  norm_num at hzeroOne

/--
No cochain map can have all three pullback components prescribed by the fixed
GOAL on this comparison data.
-/
theorem no_generated_comparison_hom :
    ¬ ∃ F : ThreeCochainComplex.Hom coarseComplex fineComplex,
      F.f0 = generatedPullback0 ∧
        F.f1 = generatedPullback1 ∧
          F.f2 = generatedPullback2 := by
  rintro ⟨F, _hf0, hf1, hf2⟩
  apply generated_pullback_comm1_fails
  have hcomm := F.comm1 selectedCoarseCochain
  rw [hf1, hf2] at hcomm
  exact hcomm

/--
The fixed claim (i) is refuted by one proper adequate, nonconstant-law,
K0/K1-generated finite comparison witness.
-/
theorem fixed_claim_i_refuted :
    laws.Adequate coarseReading ∧
      laws.Adequate fineReading ∧
      coarseReading.CoarserThan fineReading ∧
      (¬ Function.Injective
        (comparisonFactor coarseReading fineReading coarse_coarser_fine)) ∧
      (∃ law x y, laws.eval law x ≠ laws.eval law y) ∧
      (∀ chart target,
        target ∈ fineSupported.chartSupport chart →
          comparisonFactor coarseReading fineReading coarse_coarser_fine target ∈
            coarseSupported.chartSupport (nerveMorphism.chartMap chart)) ∧
      nerveMorphism.edgeMap PUnit.unit = some PUnit.unit ∧
      nerveMorphism.faceMap PUnit.unit = none ∧
      ¬ ∃ F : ThreeCochainComplex.Hom coarseComplex fineComplex,
        F.f0 = generatedPullback0 ∧
          F.f1 = generatedPullback1 ∧
            F.f2 = generatedPullback2 := by
  exact ⟨coarse_adequate, fine_adequate, coarse_coarser_fine,
    comparisonFactor_not_injective, law_nonconstant, chartSupport_compatible,
    fine_edge_maps_to_coarse_self_loop, fine_face_declared_degenerate,
    no_generated_comparison_hom⟩

end DegenerateFaceComm1Obstruction

end AAT.AG.ResolutionInvariance

#assert_standard_axioms_only AAT.AG.ResolutionInvariance.DegenerateFaceComm1Obstruction
