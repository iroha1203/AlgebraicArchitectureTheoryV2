import ResearchLean.AG.ResolutionInvariance.ResolutionInvarianceConditions
import Formal.Util.AssertStandardAxioms

/-!
# Nondegenerate firing data for resolution invariance

This module fixes the single finite fixture used by the final firing witness of
`G-104-aat-resolution-invariance`.  A noninjective reading comparison and a
nonconstant law produce two genuine law-value blocks.  The incidence data have
a two-chart fiber, a mapped repeated face, a mapped self-loop, a declared fiber
edge, and a hereditary declared face whose repeated boundary edge is also
declared.

The value-one coordinate subnerve is a proper part of the whole nerve, while
the declared face still carries a value-zero K0/K1 coordinate.  On that actual
coordinate the three degree-one pullback terms and the degree-two pullback are
all zero, giving an explicit nonvacuous degenerate-face component of `comm1`.
Condition C and the two nonzero cohomology classes are proved in later modules
over exactly these definitions; no firing certificate is stored here.
-/

noncomputable section

namespace AAT.AG.ResolutionInvariance

open CanonicalResolution Cohomology TwoPhase

namespace ResolutionInvarianceFiringWitness

/-! ## A proper adequate reading pair and two law-value labels -/

/-- Three sources, with sources zero and one identified by the coarse reading. -/
abbrev Source := Fin 3

/-- The explicit noninjective quotient map used by both the reading and the law. -/
def coarseRead (source : Source) : Fin 2 :=
  if source = 2 then 1 else 0

/-- The coarse reading remembers whether the source is the distinguished point two. -/
abbrev coarseReading : Reading Source where
  Target := Fin 2
  read := coarseRead
  surjective := by
    intro target
    fin_cases target
    · exact ⟨0, by simp [coarseRead]⟩
    · exact ⟨2, by simp [coarseRead]⟩

/-- The fine reading keeps all three sources distinct. -/
abbrev fineReading : Reading Source where
  Target := Fin 3
  read := id
  surjective := Function.surjective_id

/-- The coarse reading is coarser than the identity fine reading. -/
theorem coarse_coarser_fine : coarseReading.CoarserThan fineReading := by
  intro left right heq
  change left = right at heq
  subst right
  rfl

/-- The one declared law is the nonconstant coarse-read value. -/
def laws : FiniteLawFamily Source where
  Law := PUnit
  lawFintype := inferInstance
  Value := fun _ => Fin 2
  valueDecidableEq := fun _ => inferInstance
  eval := fun _ => coarseRead

/-- The law descends through the coarse reading by the identity function. -/
theorem coarse_adequate : laws.Adequate coarseReading := by
  intro law
  cases law
  exact ⟨id, fun _ => rfl⟩

/-- The law descends through the identity fine reading by `coarseRead`. -/
theorem fine_adequate : laws.Adequate fineReading := by
  intro law
  cases law
  exact ⟨coarseRead, fun _ => rfl⟩

/-- The canonical comparison factor is the explicit quotient map `coarseRead`. -/
theorem comparisonFactor_eq_coarseRead :
    comparisonFactor coarseReading fineReading coarse_coarser_fine =
      coarseRead := by
  symm
  apply comparisonFactor_unique coarseReading fineReading coarse_coarser_fine
  intro source
  rfl

/-- The canonical target factor genuinely identifies two distinct fine targets. -/
theorem comparisonFactor_not_injective :
    ¬ Function.Injective
      (comparisonFactor coarseReading fineReading coarse_coarser_fine) := by
  intro hinjective
  have hsame :
      comparisonFactor coarseReading fineReading coarse_coarser_fine 0 =
        comparisonFactor coarseReading fineReading coarse_coarser_fine 1 := by
    rw [comparisonFactor_eq_coarseRead]
    rfl
  exact (by decide : (0 : Fin 3) ≠ 1) (hinjective hsame)

/-- The declared law takes different values at sources zero and two. -/
theorem law_nonconstant :
    ∃ law left right,
      laws.eval law left ≠ laws.eval law right := by
  exact ⟨PUnit.unit, 0, 2, by decide⟩

/-- The canonical coarse law descent evaluates as the identity on `Fin 2`. -/
@[simp]
theorem coarse_lawDescend_apply (law : laws.Law)
    (target : coarseReading.Target) :
    lawDescend laws coarseReading coarse_adequate law target = target := by
  have hidentity :
      (id : coarseReading.Target → Fin 2) =
        lawDescend laws coarseReading coarse_adequate law := by
    apply lawDescend_unique laws coarseReading coarse_adequate law id
    intro source
    cases law
    rfl
  exact congrFun hidentity.symm target

/-- The canonical fine law descent evaluates by `coarseRead`. -/
@[simp]
theorem fine_lawDescend_apply (law : laws.Law)
    (target : fineReading.Target) :
    lawDescend laws fineReading fine_adequate law target = coarseRead target := by
  have hread :
      coarseRead = lawDescend laws fineReading fine_adequate law := by
    apply lawDescend_unique laws fineReading fine_adequate law coarseRead
    intro source
    cases law
    rfl
  exact congrFun hread.symm target

/-- The source-generated label with law value zero. -/
def zeroLabel : LawValueLabel laws :=
  LawValueLabel.ofSource laws PUnit.unit 0

/-- The source-generated label with law value one. -/
def oneLabel : LawValueLabel laws :=
  LawValueLabel.ofSource laws PUnit.unit 2

/-- The two source-generated labels are distinct. -/
theorem zeroLabel_ne_oneLabel : zeroLabel ≠ oneLabel := by
  intro heq
  have hvalue := congrArg (fun label : LawValueLabel laws => label.value) heq
  simp [zeroLabel, oneLabel, laws, coarseRead] at hvalue

/-- Every generated law-value label is one of the two named labels. -/
theorem lawValueLabel_eq_zero_or_one (label : LawValueLabel laws) :
    label = zeroLabel ∨ label = oneLabel := by
  cases label with
  | mk law value generated =>
      cases law
      obtain ⟨source, hvalue⟩ := generated
      fin_cases source
      · change coarseRead 0 = value at hvalue
        simp [coarseRead] at hvalue
        subst value
        left
        apply LawValueLabel.ext <;> rfl
      · change coarseRead 1 = value at hvalue
        simp [coarseRead] at hvalue
        subst value
        left
        apply LawValueLabel.ext <;> rfl
      · change coarseRead 2 = value at hvalue
        simp [coarseRead] at hvalue
        subst value
        right
        apply LawValueLabel.ext <;> rfl

/-! ## Finite incidence geometry and K1 chart supports -/

/--
The coarse nerve has a directed two-edge cycle and a self-loop.  Its unique
face repeats the self-loop, so it fires face lifting without killing the global
two-edge cycle used later for nonzero `H¹`.
-/
abbrev coarseNerve : CoverNerve where
  Chart := Fin 2
  EdgeComponent := Fin 3
  FaceComponent := PUnit
  edgeLeft edge := if edge = 1 then 1 else 0
  edgeRight edge := if edge = 0 then 1 else 0
  faceEdge0 _ := 2
  faceEdge1 _ := 2
  faceEdge2 _ := 2
  edgeOverlapComponent := fun _ => True
  faceTripleOverlapComponent := fun _ => True
  edgeOverlapComponent_holds := fun _ => trivial
  faceTripleOverlapComponent_holds := fun _ => trivial

/--
The fine nerve lifts all three coarse edges, adds a declared connector from
chart zero to chart one, and adds a declared self-loop on chart one.  Face zero
lifts the coarse repeated self-loop face; face one is a hereditary declared
face repeating the declared self-loop.
-/
abbrev fineNerve : CoverNerve where
  Chart := Fin 3
  EdgeComponent := Fin 5
  FaceComponent := Fin 2
  edgeLeft edge := if edge = 1 then 2 else if edge = 4 then 1 else 0
  edgeRight edge := if edge = 0 then 2 else if edge = 3 ∨ edge = 4 then 1 else 0
  faceEdge0 face := if face = 0 then 2 else 4
  faceEdge1 face := if face = 0 then 2 else 4
  faceEdge2 face := if face = 0 then 2 else 4
  edgeOverlapComponent := fun _ => True
  faceTripleOverlapComponent := fun _ => True
  edgeOverlapComponent_holds := fun _ => trivial
  faceTripleOverlapComponent_holds := fun _ => trivial

/-- Coarse chart support: chart zero sees both values and chart one sees only zero. -/
def coarseChartSupport (chart : coarseNerve.Chart) : Set coarseReading.Target :=
  if chart = 0 then Set.univ else {0}

/--
Fine chart support: chart zero sees targets zero and two, chart one sees zero
and one, and chart two sees only zero.
-/
def fineChartSupport (chart : fineNerve.Chart) : Set fineReading.Target :=
  if chart = 0 then {0, 2} else if chart = 1 then {0, 1} else {0}

/-- The coarse K1-supported nerve carrying the value distribution. -/
abbrev coarseSupported : TargetSupportedNerve coarseReading where
  nerve := coarseNerve
  chartFintype := inferInstance
  edgeFintype := inferInstance
  faceFintype := inferInstance
  chartSupport := coarseChartSupport
  chartSupport_nonempty := by
    intro chart
    fin_cases chart <;> exact ⟨0, by simp [coarseChartSupport]⟩
  faceEdge0_left := by
    intro face
    cases face
    rfl
  faceEdge0_right := by
    intro face
    cases face
    rfl
  faceEdge1_right := by
    intro face
    cases face
    rfl

/-- The fine K1-supported nerve carrying the nonconstant law-value distribution. -/
abbrev fineSupported : TargetSupportedNerve fineReading where
  nerve := fineNerve
  chartFintype := inferInstance
  edgeFintype := inferInstance
  faceFintype := inferInstance
  chartSupport := fineChartSupport
  chartSupport_nonempty := by
    intro chart
    fin_cases chart <;> exact ⟨0, by simp [fineChartSupport]⟩
  faceEdge0_left := by
    intro face
    fin_cases face <;> rfl
  faceEdge0_right := by
    intro face
    fin_cases face <;> rfl
  faceEdge1_right := by
    intro face
    fin_cases face <;> rfl

/-- Fine charts zero and one form the fiber over coarse chart zero. -/
def chartMap (chart : fineNerve.Chart) : coarseNerve.Chart :=
  if chart = 2 then 1 else 0

/-- The connector and chart-one self-loop are declared degenerate edges. -/
def edgeMap (edge : fineNerve.EdgeComponent) :
    Option coarseNerve.EdgeComponent :=
  if edge = 0 then some 0 else if edge = 1 then some 1 else
    if edge = 2 then some 2 else none

/-- Face zero is mapped and face one is declared degenerate. -/
def faceMap (face : fineNerve.FaceComponent) :
    Option coarseNerve.FaceComponent :=
  if face = 0 then some PUnit.unit else none

/--
The hereditary supported-nerve morphism for the firing fixture.  In particular,
the declared face has the declared self-loop in all three boundary positions.
-/
abbrev nerveMorphism :
    TargetSupportedNerveMorphism coarseReading fineReading coarse_coarser_fine
      coarseSupported fineSupported where
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
    fin_cases fineFace
    · cases coarseFace
      simp [faceMap, edgeMap, fineNerve, coarseNerve] at hmap ⊢
    · simp [faceMap] at hmap
  face_some_edge1 := by
    intro fineFace coarseFace hmap
    fin_cases fineFace
    · cases coarseFace
      simp [faceMap, edgeMap, fineNerve, coarseNerve] at hmap ⊢
    · simp [faceMap] at hmap
  face_some_edge2 := by
    intro fineFace coarseFace hmap
    fin_cases fineFace
    · cases coarseFace
      simp [faceMap, edgeMap, fineNerve, coarseNerve] at hmap ⊢
    · simp [faceMap] at hmap
  face_none_edge0 := by
    intro fineFace hmap
    fin_cases fineFace <;> simp [faceMap, edgeMap, fineNerve] at hmap ⊢
  face_none_edge1 := by
    intro fineFace hmap
    fin_cases fineFace <;> simp [faceMap, edgeMap, fineNerve] at hmap ⊢
  face_none_edge2 := by
    intro fineFace hmap
    fin_cases fineFace <;> simp [faceMap, edgeMap, fineNerve] at hmap ⊢
  chartSupport_compatible := by
    intro fineChart fineTarget htarget
    fin_cases fineChart <;> fin_cases fineTarget <;>
      simp [fineChartSupport, coarseChartSupport, chartMap,
        comparisonFactor_eq_coarseRead, coarseRead] at htarget ⊢

/-! ## Closed nonvacuity facts of the comparison geometry -/

/-- Coarse chart zero has the two distinct fine charts zero and one in its fiber. -/
theorem nontrivial_chart_fiber :
    ∃ left right : fineNerve.Chart,
      left ≠ right ∧ chartMap left = 0 ∧ chartMap right = 0 := by
  exact ⟨0, 1, by decide, by simp [chartMap], by simp [chartMap]⟩

/-- Fine face zero is an actual lift of the unique coarse repeated-loop face. -/
theorem mapped_face_fires :
    ∃ fineFace coarseFace,
      faceMap fineFace = some coarseFace := by
  exact ⟨0, PUnit.unit, by simp [faceMap]⟩

/-- Fine edge three is a declared fiber edge with distinct endpoints. -/
theorem declared_edge_fires :
    edgeMap 3 = none ∧
      fineNerve.edgeLeft 3 ≠ fineNerve.edgeRight 3 ∧
      chartMap (fineNerve.edgeLeft 3) =
        chartMap (fineNerve.edgeRight 3) := by
  simp [edgeMap, fineNerve, chartMap]

/-- Fine face one is declared and all three repeated boundary edges are declared. -/
theorem hereditary_face_fires :
    faceMap 1 = none ∧
      edgeMap (fineNerve.faceEdge0 1) = none ∧
      edgeMap (fineNerve.faceEdge1 1) = none ∧
      edgeMap (fineNerve.faceEdge2 1) = none := by
  simp [faceMap, edgeMap, fineNerve]

/-- The mapped fine self-loop reflects the unique coarse self-loop literally. -/
theorem self_loop_reflection_fires :
    edgeMap 2 = some 2 ∧
      coarseNerve.edgeLeft 2 = coarseNerve.edgeRight 2 ∧
      fineNerve.edgeLeft 2 = fineNerve.edgeRight 2 := by
  simp [edgeMap, coarseNerve, fineNerve]

/-! ## Actual law-generated coordinates and a proper coordinate subnerve -/

/-- The declared fine face carries an actual K0/K1 coordinate generated at target zero. -/
def fineDegenerateFaceCoordinate :
    fineSupported.FaceCoordinate laws fine_adequate :=
  CellCoordinate.ofSupportedTarget laws fineReading fine_adequate
    fineNerve.FaceComponent fineSupported.faceSupport 1 PUnit.unit 0 (by
      simp [TargetSupportedNerve.faceSupport,
        TargetSupportedNerve.edgeSupport, fineNerve, fineChartSupport])

/-- The named declared-face coordinate lies over fine face one. -/
@[simp]
theorem fineDegenerateFaceCoordinate_cell :
    fineDegenerateFaceCoordinate.cell = 1 :=
  rfl

/-- The named declared-face coordinate belongs to the value-zero block. -/
theorem fineDegenerateFaceCoordinate_label :
    fineDegenerateFaceCoordinate.lawValueLabel laws fineReading fine_adequate
        fineNerve.FaceComponent fineSupported.faceSupport = zeroLabel := by
  apply LawValueLabel.ext
  · rfl
  · simpa only [fineDegenerateFaceCoordinate,
      CellCoordinate.ofSupportedTarget, CellCoordinate.lawValueLabel,
      zeroLabel, LawValueLabel.ofSource, laws, coarseRead] using
        heq_of_eq (fine_lawDescend_apply PUnit.unit (0 : fineReading.Target))

/-- The declared face as an actual coordinate of the value-zero face block. -/
def fineDegenerateFaceBlockCoordinate :
    fineSupported.FaceBlockCoordinate laws fine_adequate zeroLabel :=
  ⟨fineDegenerateFaceCoordinate, fineDegenerateFaceCoordinate_label⟩

/-- The value-one label occurs at fine chart zero through supported target two. -/
theorem oneLabel_chart_zero_occurs :
    ∃ coordinate :
        (fineSupported.lawValueCoordinateSubnerve laws fine_adequate
          oneLabel).Chart,
      fineSupported.lawValueCoordinateSubnerveChartCell laws fine_adequate
        oneLabel coordinate = 0 := by
  rw [fineSupported.chart_occurs_in_lawValueCoordinateSubnerve_iff]
  refine ⟨2, ?_, ?_⟩
  · simp [fineChartSupport]
  · simpa only [oneLabel, LawValueLabel.ofSource, laws, coarseRead] using
      fine_lawDescend_apply PUnit.unit (2 : fineReading.Target)

/-- Fine chart one does not occur in the value-one coordinate subnerve. -/
theorem oneLabel_chart_one_not_occurs :
    ¬ ∃ coordinate :
        (fineSupported.lawValueCoordinateSubnerve laws fine_adequate
          oneLabel).Chart,
      fineSupported.lawValueCoordinateSubnerveChartCell laws fine_adequate
        oneLabel coordinate = 1 := by
  rw [fineSupported.chart_occurs_in_lawValueCoordinateSubnerve_iff]
  rintro ⟨target, htarget, hvalue⟩
  fin_cases target
  · rw [fine_lawDescend_apply] at hvalue
    simp [oneLabel, LawValueLabel.ofSource, laws, coarseRead] at hvalue
  · rw [fine_lawDescend_apply] at hvalue
    simp [oneLabel, LawValueLabel.ofSource, laws, coarseRead] at hvalue
  · simp [fineChartSupport] at htarget

/-- The value-one coordinate subnerve is genuinely smaller than the whole fine nerve. -/
theorem oneLabel_subnerve_proper :
    ¬ Function.Surjective
      (fineSupported.lawValueCoordinateSubnerveChartCell laws fine_adequate
        oneLabel) := by
  intro hsurjective
  obtain ⟨coordinate, hcoordinate⟩ := hsurjective 1
  exact oneLabel_chart_one_not_occurs ⟨coordinate, hcoordinate⟩

/-! ## Explicit hereditary degenerate-face component of the actual cochain map -/

/-- The actual law-generated coarse complex attached to the firing data. -/
abbrev coarseComplex : ThreeCochainComplex ℚ :=
  coarseSupported.lawGeneratedComplex laws coarse_adequate

/-- The actual law-generated fine complex attached to the firing data. -/
abbrev fineComplex : ThreeCochainComplex ℚ :=
  fineSupported.lawGeneratedComplex laws fine_adequate

/--
All three actual degree-one pullback evaluations on the declared face boundary
are zero for every coarse one-cochain.
-/
theorem degenerateFace_boundary_pullbacks_zero
    (cochain : coarseComplex.C1) :
    nerveMorphism.generatedPullback1 laws coarse_adequate fine_adequate cochain
          (fineSupported.faceEdge0Coordinate laws fine_adequate
            fineDegenerateFaceCoordinate) = 0 ∧
      nerveMorphism.generatedPullback1 laws coarse_adequate fine_adequate cochain
          (fineSupported.faceEdge1Coordinate laws fine_adequate
            fineDegenerateFaceCoordinate) = 0 ∧
      nerveMorphism.generatedPullback1 laws coarse_adequate fine_adequate cochain
          (fineSupported.faceEdge2Coordinate laws fine_adequate
            fineDegenerateFaceCoordinate) = 0 := by
  have hface : faceMap fineDegenerateFaceCoordinate.cell = none := by
    simp [faceMap]
  have hedge0 := nerveMorphism.face_none_edge0
    fineDegenerateFaceCoordinate.cell hface
  have hedge1 := nerveMorphism.face_none_edge1
    fineDegenerateFaceCoordinate.cell hface
  have hedge2 := nerveMorphism.face_none_edge2
    fineDegenerateFaceCoordinate.cell hface
  constructor
  · rw [nerveMorphism.generatedPullback1_apply,
      nerveMorphism.edgeCoordinateMapOption_eq_none laws coarse_adequate
        fine_adequate
        (fineSupported.faceEdge0Coordinate laws fine_adequate
          fineDegenerateFaceCoordinate) hedge0]
    rfl
  · constructor
    · rw [nerveMorphism.generatedPullback1_apply,
        nerveMorphism.edgeCoordinateMapOption_eq_none laws coarse_adequate
          fine_adequate
          (fineSupported.faceEdge1Coordinate laws fine_adequate
            fineDegenerateFaceCoordinate) hedge1]
      rfl
    · rw [nerveMorphism.generatedPullback1_apply,
        nerveMorphism.edgeCoordinateMapOption_eq_none laws coarse_adequate
          fine_adequate
          (fineSupported.faceEdge2Coordinate laws fine_adequate
            fineDegenerateFaceCoordinate) hedge2]
      rfl

/-- The actual degree-two pullback is zero on the declared face coordinate. -/
theorem degenerateFace_degreeTwo_pullback_zero
    (cochain : coarseComplex.C1) :
    nerveMorphism.generatedPullback2 laws coarse_adequate fine_adequate
        (coarseComplex.d1 cochain) fineDegenerateFaceCoordinate = 0 := by
  have hface : faceMap fineDegenerateFaceCoordinate.cell = none := by
    simp [faceMap]
  rw [nerveMorphism.generatedPullback2_apply,
    nerveMorphism.faceCoordinateMapOption_eq_none laws coarse_adequate
      fine_adequate fineDegenerateFaceCoordinate hface]
  rfl

/--
The actual fine differential evaluates the three zero boundary pullbacks as
`0 - 0 + 0 = 0` on the declared face coordinate.
-/
theorem degenerateFace_degreeOne_alternating_sum_zero
    (cochain : coarseComplex.C1) :
    fineComplex.d1
        (nerveMorphism.generatedPullback1 laws coarse_adequate fine_adequate
          cochain) fineDegenerateFaceCoordinate = 0 := by
  change fineSupported.lawGeneratedD1 laws fine_adequate
      (nerveMorphism.generatedPullback1 laws coarse_adequate fine_adequate
        cochain) fineDegenerateFaceCoordinate = 0
  rw [fineSupported.lawGeneratedD1_apply]
  obtain ⟨hzero0, hzero1, hzero2⟩ :=
    degenerateFace_boundary_pullbacks_zero cochain
  rw [hzero0, hzero1, hzero2]
  ring

/--
The declared face gives an explicit nonvacuous component of actual `comm1`:
both the degree-two pullback and the degree-one alternating sum are zero, and
the reviewed generated cochain-map equality identifies them.
-/
theorem degenerateFace_comm1_zero
    (cochain : coarseComplex.C1) :
    nerveMorphism.generatedPullback2 laws coarse_adequate fine_adequate
          (coarseComplex.d1 cochain) fineDegenerateFaceCoordinate = 0 ∧
      fineComplex.d1
          (nerveMorphism.generatedPullback1 laws coarse_adequate fine_adequate
            cochain) fineDegenerateFaceCoordinate = 0 ∧
      nerveMorphism.generatedPullback2 laws coarse_adequate fine_adequate
          (coarseComplex.d1 cochain) fineDegenerateFaceCoordinate =
        fineComplex.d1
          (nerveMorphism.generatedPullback1 laws coarse_adequate fine_adequate
            cochain) fineDegenerateFaceCoordinate := by
  refine ⟨degenerateFace_degreeTwo_pullback_zero cochain,
    degenerateFace_degreeOne_alternating_sum_zero cochain, ?_⟩
  exact congrFun
    (nerveMorphism.generatedPullback_comm1 laws coarse_adequate fine_adequate
      cochain) fineDegenerateFaceCoordinate

/-!
## Cycle 29 firing-data checkpoint
-/

/--
The single closed fixture simultaneously realizes every data/provenance and
hereditary-`comm1` nonvacuity requirement assigned to Cycle 29.  Condition C
and nonzero cohomology are deliberately not premises or conclusions here; they
are the next two proof-DAG nodes over these exact constants.
-/
theorem fixed_firing_input_nonvacuity :
    laws.Adequate coarseReading ∧
      laws.Adequate fineReading ∧
      coarseReading.CoarserThan fineReading ∧
      (¬ Function.Injective
        (comparisonFactor coarseReading fineReading coarse_coarser_fine)) ∧
      (∃ law left right,
        laws.eval law left ≠ laws.eval law right) ∧
      zeroLabel ≠ oneLabel ∧
      (∃ left right : fineNerve.Chart,
        left ≠ right ∧ chartMap left = 0 ∧ chartMap right = 0) ∧
      (∃ fineFace coarseFace,
        faceMap fineFace = some coarseFace) ∧
      (edgeMap 3 = none ∧
        fineNerve.edgeLeft 3 ≠ fineNerve.edgeRight 3 ∧
        chartMap (fineNerve.edgeLeft 3) =
          chartMap (fineNerve.edgeRight 3)) ∧
      (faceMap 1 = none ∧
        edgeMap (fineNerve.faceEdge0 1) = none ∧
        edgeMap (fineNerve.faceEdge1 1) = none ∧
        edgeMap (fineNerve.faceEdge2 1) = none) ∧
      (edgeMap 2 = some 2 ∧
        coarseNerve.edgeLeft 2 = coarseNerve.edgeRight 2 ∧
        fineNerve.edgeLeft 2 = fineNerve.edgeRight 2) ∧
      fineDegenerateFaceBlockCoordinate.1.cell = 1 ∧
      (∃ coordinate :
          (fineSupported.lawValueCoordinateSubnerve laws fine_adequate
            oneLabel).Chart,
        fineSupported.lawValueCoordinateSubnerveChartCell laws fine_adequate
          oneLabel coordinate = 0) ∧
      (¬ Function.Surjective
        (fineSupported.lawValueCoordinateSubnerveChartCell laws fine_adequate
          oneLabel)) ∧
      ∀ cochain : coarseComplex.C1,
        nerveMorphism.generatedPullback2 laws coarse_adequate fine_adequate
              (coarseComplex.d1 cochain) fineDegenerateFaceCoordinate = 0 ∧
          fineComplex.d1
              (nerveMorphism.generatedPullback1 laws coarse_adequate
                fine_adequate cochain) fineDegenerateFaceCoordinate = 0 ∧
          nerveMorphism.generatedPullback2 laws coarse_adequate fine_adequate
              (coarseComplex.d1 cochain) fineDegenerateFaceCoordinate =
            fineComplex.d1
              (nerveMorphism.generatedPullback1 laws coarse_adequate
                fine_adequate cochain) fineDegenerateFaceCoordinate := by
  exact ⟨coarse_adequate, fine_adequate, coarse_coarser_fine,
    comparisonFactor_not_injective, law_nonconstant, zeroLabel_ne_oneLabel,
    nontrivial_chart_fiber, mapped_face_fires, declared_edge_fires,
    hereditary_face_fires, self_loop_reflection_fires, rfl,
    oneLabel_chart_zero_occurs, oneLabel_subnerve_proper,
    degenerateFace_comm1_zero⟩

end ResolutionInvarianceFiringWitness

end AAT.AG.ResolutionInvariance

#assert_standard_axioms_only AAT.AG.ResolutionInvariance.ResolutionInvarianceFiringWitness
