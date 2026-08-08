import ResearchLean.AG.ResolutionInvariance.CanonicalInadequateDiagnostic
import ResearchLean.AG.ResolutionInvariance.GeneratedComparisonMap
import Formal.Util.AssertStandardAxioms

/-!
# A canonical false-positive diagnostic for an inadequate reading

This finite fixture realizes G-104 claim (iv)(a) on the current K0/K1 law-generated
complexes.  A noninjective coarse reading retains exactly one nonconstant law by
the G-103 `Factors` predicate and excludes a second law that separates one coarse
fiber.  Its canonical Factors diagnostic has a nonzero self-loop class.

The fine reading uses the same original law family and a two-chart tree.  Every
class in its full canonical Factors diagnostic is a coboundary, and the actual
generated comparison map for the coarse-retained family kills the displayed
coarse class.  Thus the false class is not an artifact of comparing unrelated
Lean types, a selected law list, or a hand-written coefficient complex.  This
fixture is only the claim (iv)(a) counterexample; it is not a claim (v) firing
witness.
-/

noncomputable section

namespace AAT.AG.ResolutionInvariance

open CanonicalResolution Cohomology TwoPhase

namespace CanonicalInadequateFalsePositive

/-- Three source points, two of which are identified by the coarse reading. -/
abbrev Source := Fin 3

/-- The noninjective coarse observation that identifies sources zero and one. -/
def coarseRead (source : Source) : Fin 2 :=
  if source = 2 then 1 else 0

/-- The surjective two-valued coarse reading used by the false-positive fixture. -/
abbrev coarseReading : Reading Source where
  Target := Fin 2
  read := coarseRead
  surjective := by
    intro target
    fin_cases target
    · exact ⟨0, by simp [coarseRead]⟩
    · exact ⟨2, by simp [coarseRead]⟩

/-- The identity fine reading on the same finite source. -/
abbrev fineReading : Reading Source where
  Target := Source
  read := id
  surjective := Function.surjective_id

/-- The retained coarse observation law and the law that separates its collapsed fiber. -/
def lawEval (law : Fin 2) (source : Source) : Fin 2 :=
  if law = 0 then coarseRead source else if source = 1 then 1 else 0

/-- The two-law family shared by the coarse and fine diagnostics. -/
def laws : FiniteLawFamily Source where
  Law := Fin 2
  lawFintype := inferInstance
  Value := fun _ => Fin 2
  valueDecidableEq := fun _ => inferInstance
  eval := lawEval

/-- The nonconstant law that factors through the coarse reading. -/
def factorLaw : Fin 2 := 0

/-- The law that distinguishes the coarse fiber and therefore does not factor. -/
def separatingLaw : Fin 2 := 1

/-- The retained nonconstant law factors through the coarse reading. -/
theorem coarse_factorLaw_factors :
    coarseReading.Factors (laws.eval factorLaw) := by
  change coarseReading.Factors (lawEval factorLaw)
  refine ⟨id, ?_⟩
  intro source
  simp [lawEval, factorLaw, coarseReading]

/-- The separating law cannot factor through the coarse reading. -/
theorem coarse_separatingLaw_not_factors :
    ¬ coarseReading.Factors (laws.eval separatingLaw) := by
  change ¬ coarseReading.Factors (lawEval separatingLaw)
  rintro ⟨descend, hdescend⟩
  have hzero := hdescend (0 : Source)
  have hone := hdescend (1 : Source)
  have hzero' : descend 0 = 0 := by
    simpa [lawEval, separatingLaw, coarseReading, coarseRead] using hzero
  have hone' : descend 0 = 1 := by
    simpa [lawEval, separatingLaw, coarseReading, coarseRead] using hone
  exact zero_ne_one (hzero'.symm.trans hone')

/-- A law factors through the coarse reading exactly when it is the retained law. -/
theorem coarse_factors_iff (law : laws.Law) :
    coarseReading.Factors (laws.eval law) ↔ law = factorLaw := by
  change coarseReading.Factors (lawEval law) ↔ law = factorLaw
  fin_cases law
  · constructor
    · intro _hfactors
      rfl
    · intro _heq
      simpa [laws, factorLaw] using coarse_factorLaw_factors
  · constructor
    · intro hfactors
      exact (coarse_separatingLaw_not_factors
        (by simpa [laws, separatingLaw] using hfactors)).elim
    · intro heq
      have hne : (1 : Fin 2) ≠ factorLaw := by decide
      exact (hne heq).elim

/-- The law retained by the coarse diagnostic is genuinely nonconstant. -/
theorem factorLaw_nonconstant :
    ∃ left right : Source,
      laws.eval factorLaw left ≠ laws.eval factorLaw right := by
  refine ⟨0, 2, ?_⟩
  change lawEval factorLaw 0 ≠ lawEval factorLaw 2
  decide

/-- The original two-law family is not adequate for the coarse reading. -/
theorem coarse_not_adequate : ¬ laws.Adequate coarseReading := by
  intro hadequate
  exact coarse_separatingLaw_not_factors (hadequate separatingLaw)

/-- Every law in the original family factors through the identity fine reading. -/
theorem fine_adequate : laws.Adequate fineReading := by
  intro law
  refine ⟨laws.eval law, ?_⟩
  intro source
  rfl

/-- The coarse reading is coarser than the identity fine reading. -/
theorem coarse_coarser_fine : coarseReading.CoarserThan fineReading := by
  intro left right heq
  change left = right at heq
  cases heq
  rfl

/-- The canonical target factor for the reading comparison is not injective. -/
theorem comparisonFactor_not_injective :
    ¬ Function.Injective
      (comparisonFactor coarseReading fineReading coarse_coarser_fine) := by
  intro hinjective
  have hsame :
      comparisonFactor coarseReading fineReading coarse_coarser_fine
          (fineReading.read (0 : Source)) =
        comparisonFactor coarseReading fineReading coarse_coarser_fine
          (fineReading.read (1 : Source)) := by
    rw [comparisonFactor_commutes, comparisonFactor_commutes]
    rfl
  have heq := hinjective hsame
  change (0 : Source) = 1 at heq
  exact zero_ne_one heq

/-- The one-chart coarse nerve with one selected self-loop and no faces. -/
abbrev coarseNerve : CoverNerve where
  Chart := PUnit
  EdgeComponent := PUnit
  FaceComponent := PEmpty
  edgeLeft := fun _ => PUnit.unit
  edgeRight := fun _ => PUnit.unit
  faceEdge0 := PEmpty.elim
  faceEdge1 := PEmpty.elim
  faceEdge2 := PEmpty.elim
  edgeOverlapComponent := fun _ => True
  faceTripleOverlapComponent := fun _ => True
  edgeOverlapComponent_holds := fun _ => True.intro
  faceTripleOverlapComponent_holds := PEmpty.elim

/-- The two-chart fine tree with one selected edge and no faces. -/
abbrev fineNerve : CoverNerve where
  Chart := Fin 2
  EdgeComponent := PUnit
  FaceComponent := PEmpty
  edgeLeft := fun _ => 0
  edgeRight := fun _ => 1
  faceEdge0 := PEmpty.elim
  faceEdge1 := PEmpty.elim
  faceEdge2 := PEmpty.elim
  edgeOverlapComponent := fun _ => True
  faceTripleOverlapComponent := fun _ => True
  edgeOverlapComponent_holds := fun _ => True.intro
  faceTripleOverlapComponent_holds := PEmpty.elim

/-- The coarse self-loop nerve with total chart support. -/
abbrev coarseSupported : TargetSupportedNerve coarseReading where
  nerve := coarseNerve
  chartFintype := inferInstance
  edgeFintype := inferInstance
  faceFintype := inferInstance
  chartSupport := fun _ => Set.univ
  chartSupport_nonempty := fun _ => ⟨0, Set.mem_univ _⟩
  faceEdge0_left := fun face => PEmpty.elim face
  faceEdge0_right := fun face => PEmpty.elim face
  faceEdge1_right := fun face => PEmpty.elim face

/-- The fine tree nerve with total chart support. -/
abbrev fineSupported : TargetSupportedNerve fineReading where
  nerve := fineNerve
  chartFintype := inferInstance
  edgeFintype := inferInstance
  faceFintype := inferInstance
  chartSupport := fun _ => Set.univ
  chartSupport_nonempty := fun _ => ⟨0, Set.mem_univ _⟩
  faceEdge0_left := fun face => PEmpty.elim face
  faceEdge0_right := fun face => PEmpty.elim face
  faceEdge1_right := fun face => PEmpty.elim face

/-- Both fine charts lie over the unique coarse chart. -/
def chartMap (_chart : fineSupported.nerve.Chart) :
    coarseSupported.nerve.Chart := PUnit.unit

/-- The fine tree edge maps to the coarse self-loop. -/
def edgeMap (_edge : fineSupported.nerve.EdgeComponent) :
    Option coarseSupported.nerve.EdgeComponent := some PUnit.unit

/-- The unique map out of the empty fine face type. -/
def faceMap (face : fineSupported.nerve.FaceComponent) :
    Option coarseSupported.nerve.FaceComponent := PEmpty.elim face

/-- The current hereditary supported-nerve morphism for the finite fixture. -/
abbrev nerveMorphism : TargetSupportedNerveMorphism coarseReading fineReading
    coarse_coarser_fine coarseSupported fineSupported where
  chartMap := chartMap
  edgeMap := edgeMap
  faceMap := faceMap
  edge_some_left := by
    intro _fineEdge _coarseEdge _hmap
    rfl
  edge_some_right := by
    intro _fineEdge _coarseEdge _hmap
    rfl
  edge_none_fiber := by
    intro _fineEdge hnone
    simp [edgeMap] at hnone
  face_some_edge0 := by
    intro fineFace
    exact PEmpty.elim fineFace
  face_some_edge1 := by
    intro fineFace
    exact PEmpty.elim fineFace
  face_some_edge2 := by
    intro fineFace
    exact PEmpty.elim fineFace
  face_none_edge0 := by
    intro fineFace
    exact PEmpty.elim fineFace
  face_none_edge1 := by
    intro fineFace
    exact PEmpty.elim fineFace
  face_none_edge2 := by
    intro fineFace
    exact PEmpty.elim fineFace
  chartSupport_compatible := by
    intro fineChart fineTarget htarget
    exact Set.mem_univ _

/-- The canonical Factors-selected subfamily for the inadequate coarse reading. -/
abbrev retainedLaws : FiniteLawFamily Source :=
  laws.descendableSubfamily coarseReading

/-- Adequacy of the retained family for the coarse reading, derived by Cycle 25. -/
theorem coarseRetainedAdequate : retainedLaws.Adequate coarseReading :=
  laws.descendableSubfamily_adequate coarseReading

/-- Every coarse-retained law also factors through the finer identity reading. -/
theorem retainedLaws_fine_adequate : retainedLaws.Adequate fineReading := by
  intro law
  exact fine_adequate law.1

/-- The actual canonical Factors diagnostic complex on the coarse nerve. -/
abbrev coarseDiagnosticComplex : ThreeCochainComplex ℚ :=
  coarseSupported.factorsDiagnosticComplex laws

/-- The actual canonical Factors diagnostic complex on the fine nerve. -/
abbrev fineDiagnosticComplex : ThreeCochainComplex ℚ :=
  fineSupported.factorsDiagnosticComplex laws

/-- The fine actual complex for the exact family retained on the coarse side. -/
abbrev fineRetainedComplex : ThreeCochainComplex ℚ :=
  fineSupported.lawGeneratedComplex retainedLaws retainedLaws_fine_adequate

/-- A fine chart coordinate determines the same law-value coordinate on the tree edge. -/
def fineEdgeCoordinateOfChart (family : FiniteLawFamily Source)
    (hadequate : family.Adequate fineReading)
    (coordinate : fineSupported.ChartCoordinate family hadequate) :
    fineSupported.EdgeCoordinate family hadequate := by
  refine ⟨PUnit.unit, coordinate.law, coordinate.value, ?_⟩
  obtain ⟨target, _htarget, hvalue⟩ := coordinate.generated
  refine ⟨target, ?_, hvalue⟩
  rw [fineSupported.mem_edgeSupport_iff]
  exact ⟨Set.mem_univ _, Set.mem_univ _⟩

/-- Reconstructing an edge coordinate from its right chart coordinate returns it. -/
theorem fineEdgeCoordinateOfChart_edgeRight
    (family : FiniteLawFamily Source)
    (hadequate : family.Adequate fineReading)
    (coordinate : fineSupported.EdgeCoordinate family hadequate) :
    fineEdgeCoordinateOfChart family hadequate
      (fineSupported.edgeRightCoordinate family hadequate coordinate) =
        coordinate := by
  apply CellCoordinate.ext
  · rfl
  · rfl
  · rfl

/-- The coordinatewise tree potential integrating any fine degree-one cochain. -/
def finePrimitive (family : FiniteLawFamily Source)
    (hadequate : family.Adequate fineReading)
    (cochain : fineSupported.EdgeCoordinate family hadequate → ℚ) :
    fineSupported.ChartCoordinate family hadequate → ℚ :=
  fun coordinate =>
    if coordinate.cell = 0 then 0 else
      cochain (fineEdgeCoordinateOfChart family hadequate coordinate)

/-- The actual generated `d0` of the tree potential is the original cochain. -/
theorem fine_lawGeneratedD0_primitive
    (family : FiniteLawFamily Source)
    (hadequate : family.Adequate fineReading)
    (cochain : fineSupported.EdgeCoordinate family hadequate → ℚ) :
    fineSupported.lawGeneratedD0 family hadequate
      (finePrimitive family hadequate cochain) = cochain := by
  funext coordinate
  rw [fineSupported.lawGeneratedD0_apply]
  simp [finePrimitive, fineNerve,
    fineEdgeCoordinateOfChart_edgeRight]

/-- Every actual law-generated complex on the fine tree has zero first cohomology. -/
theorem fineH1Zero (family : FiniteLawFamily Source)
    (hadequate : family.Adequate fineReading) :
    (fineSupported.lawGeneratedComplex family hadequate).H1Zero := by
  intro cohomologyClass
  obtain ⟨cycle, rfl⟩ :=
    (LinearMap.range
      (fineSupported.lawGeneratedComplex family hadequate).boundaryToCycles).mkQ_surjective
        cohomologyClass
  apply (Submodule.Quotient.mk_eq_zero _).2
  refine ⟨finePrimitive family hadequate cycle.1, ?_⟩
  apply Subtype.ext
  exact fine_lawGeneratedD0_primitive family hadequate cycle.1

/-- The full canonical Factors diagnostic of the fine reading has zero `H¹`. -/
theorem fineFactorsDiagnosticH1Zero : fineDiagnosticComplex.H1Zero :=
  fineH1Zero (laws.descendableSubfamily fineReading)
    (laws.descendableSubfamily_adequate fineReading)

/-- The named element of the canonical coarse-descendable law subtype. -/
def retainedLaw : retainedLaws.Law :=
  ⟨factorLaw, coarse_factorLaw_factors⟩

/-- A concrete K0/K1 edge coordinate on the coarse self-loop. -/
def coarseLoopCoordinate :
    coarseSupported.EdgeCoordinate retainedLaws coarseRetainedAdequate :=
  CellCoordinate.ofSupportedTarget retainedLaws coarseReading
    coarseRetainedAdequate coarseNerve.EdgeComponent
      coarseSupported.edgeSupport PUnit.unit retainedLaw 0 (by
        simp [TargetSupportedNerve.edgeSupport])

/-- Evaluation on the selected coarse self-loop coordinate. -/
def coarseLoopPeriod (cochain : coarseDiagnosticComplex.C1) : ℚ :=
  cochain coarseLoopCoordinate

/-- Every actual coarse coboundary has zero selected self-loop period. -/
theorem coarseLoopPeriod_boundary_zero
    (cochain : coarseDiagnosticComplex.C0) :
    coarseLoopPeriod (coarseDiagnosticComplex.d0 cochain) = 0 := by
  change (coarseSupported.lawGeneratedD0 retainedLaws
    coarseRetainedAdequate cochain) coarseLoopCoordinate = 0
  rw [coarseSupported.lawGeneratedD0_apply]
  have hendpoints :
      coarseSupported.edgeRightCoordinate retainedLaws coarseRetainedAdequate
          coarseLoopCoordinate =
        coarseSupported.edgeLeftCoordinate retainedLaws coarseRetainedAdequate
          coarseLoopCoordinate := by
    apply CellCoordinate.ext
    · rfl
    · rfl
    · rfl
  rw [hendpoints]
  exact sub_self _

/-- The unit cochain on every retained-law coarse loop coordinate. -/
def coarseLoopCochain : coarseDiagnosticComplex.C1 := fun _ => 1

/-- The coarse loop cochain is an actual cocycle because there are no faces. -/
theorem coarseLoopCochain_cocycle :
    coarseDiagnosticComplex.d1 coarseLoopCochain = 0 := by
  funext coordinate
  exact PEmpty.elim coordinate.cell

/-- The explicit coarse self-loop cocycle in the actual kernel. -/
def coarseLoopCycle : LinearMap.ker coarseDiagnosticComplex.d1 :=
  ⟨coarseLoopCochain, coarseLoopCochain_cocycle⟩

/-- The actual G-102 quotient class of the coarse self-loop cocycle. -/
def coarseLoopClass : coarseDiagnosticComplex.H1 :=
  (LinearMap.range coarseDiagnosticComplex.boundaryToCycles).mkQ
    coarseLoopCycle

/-- The displayed coarse loop cocycle has unit selected period. -/
theorem coarseLoopPeriod_firing :
    coarseLoopPeriod coarseLoopCycle.1 = 1 :=
  rfl

/-- The canonical coarse Factors diagnostic contains a nonzero class. -/
theorem coarseLoopClass_ne_zero : coarseLoopClass ≠ 0 := by
  intro hzero
  have hmem := (Submodule.Quotient.mk_eq_zero
    (LinearMap.range coarseDiagnosticComplex.boundaryToCycles)).1 hzero
  rcases hmem with ⟨cochain, hcochain⟩
  have hperiod := congrArg
    (fun cycle : LinearMap.ker coarseDiagnosticComplex.d1 =>
      coarseLoopPeriod cycle.1) hcochain
  change coarseLoopPeriod (coarseDiagnosticComplex.d0 cochain) =
    coarseLoopPeriod coarseLoopCycle.1 at hperiod
  rw [coarseLoopPeriod_boundary_zero, coarseLoopPeriod_firing] at hperiod
  exact zero_ne_one hperiod

/-- The actual generated comparison map for the exact coarse-retained family. -/
def retainedComparisonH1Map :
    coarseDiagnosticComplex.H1 →ₗ[ℚ] fineRetainedComplex.H1 :=
  nerveMorphism.generatedComparisonH1Map retainedLaws
    coarseRetainedAdequate retainedLaws_fine_adequate

/-- The actual comparison map kills the nonzero coarse self-loop class. -/
theorem retainedComparisonH1Map_coarseLoopClass_zero :
    retainedComparisonH1Map coarseLoopClass = 0 :=
  fineH1Zero retainedLaws retainedLaws_fine_adequate _

/-- G-104 claim (iv)(a): an inadequate coarse reading creates a false nonzero class. -/
theorem fixed_claim_iv_a :
    ¬ laws.Adequate coarseReading ∧
      laws.Adequate fineReading ∧
      coarseReading.CoarserThan fineReading ∧
      (¬ Function.Injective
        (comparisonFactor coarseReading fineReading coarse_coarser_fine)) ∧
      (∀ law : laws.Law,
        coarseReading.Factors (laws.eval law) ↔ law = factorLaw) ∧
      (∃ left right : Source,
        laws.eval factorLaw left ≠ laws.eval factorLaw right) ∧
      coarseLoopClass ≠ 0 ∧
      retainedComparisonH1Map coarseLoopClass = 0 ∧
      fineDiagnosticComplex.H1Zero :=
  ⟨coarse_not_adequate, fine_adequate, coarse_coarser_fine,
    comparisonFactor_not_injective, coarse_factors_iff,
    factorLaw_nonconstant, coarseLoopClass_ne_zero,
    retainedComparisonH1Map_coarseLoopClass_zero, fineFactorsDiagnosticH1Zero⟩

end CanonicalInadequateFalsePositive

end AAT.AG.ResolutionInvariance

#assert_standard_axioms_only AAT.AG.ResolutionInvariance.CanonicalInadequateFalsePositive
