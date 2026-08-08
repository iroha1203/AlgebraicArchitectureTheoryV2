import ResearchLean.AG.ResolutionInvariance.CanonicalInadequateFalsePositive
import Formal.Util.AssertStandardAxioms

/-!
# A canonical hidden class for an inadequate reading

This finite fixture realizes G-104 claim (iv)(b) on the current canonical
`Factors` diagnostics.  It reuses the noninjective reading pair and exact
two-law provenance from Cycle 26, but changes the incidence geometry: the
coarse nerve is a one-edge tree and the fine nerve has two parallel lifts of
that edge.

The canonical coarse diagnostic has zero first cohomology.  For the exact law
family retained by the inadequate coarse reading, the actual generated
comparison map is not surjective onto the fine complex because a parallel-edge
class is nonzero.  The same class pattern is also constructed in the full fine
canonical diagnostic of the original two-law family, so the witness is not a
consequence of comparing differently indexed Lean types.  This fixture is only
the claim (iv)(b) counterexample; it is not a claim (v) firing witness.
-/

noncomputable section

namespace AAT.AG.ResolutionInvariance

open CanonicalResolution Cohomology TwoPhase

namespace CanonicalInadequateHiddenClass

/-! ## Reused reading and law provenance -/

/-- The three-point source inherited from the canonical false-positive fixture. -/
abbrev Source := CanonicalInadequateFalsePositive.Source

/-- The same noninjective coarse reading used by Cycle 26. -/
abbrev coarseReading : Reading Source :=
  CanonicalInadequateFalsePositive.coarseReading

/-- The same identity fine reading used by Cycle 26. -/
abbrev fineReading : Reading Source :=
  CanonicalInadequateFalsePositive.fineReading

/-- The same two-law family with one retained and one separating law. -/
abbrev laws : FiniteLawFamily Source :=
  CanonicalInadequateFalsePositive.laws

/-- The named nonconstant law retained by the coarse reading. -/
abbrev factorLaw : laws.Law :=
  CanonicalInadequateFalsePositive.factorLaw

/-- The original family is inadequate for the coarse reading. -/
theorem coarse_not_adequate : ¬ laws.Adequate coarseReading :=
  CanonicalInadequateFalsePositive.coarse_not_adequate

/-- The original family is adequate for the identity fine reading. -/
theorem fine_adequate : laws.Adequate fineReading :=
  CanonicalInadequateFalsePositive.fine_adequate

/-- The coarse reading is coarser than the identity fine reading. -/
theorem coarse_coarser_fine : coarseReading.CoarserThan fineReading :=
  CanonicalInadequateFalsePositive.coarse_coarser_fine

/-- The canonical target factor remains genuinely noninjective. -/
theorem comparisonFactor_not_injective :
    ¬ Function.Injective
      (comparisonFactor coarseReading fineReading coarse_coarser_fine) :=
  CanonicalInadequateFalsePositive.comparisonFactor_not_injective

/-- The coarse reading retains exactly the named nonconstant law. -/
theorem coarse_factors_iff (law : laws.Law) :
    coarseReading.Factors (laws.eval law) ↔ law = factorLaw :=
  CanonicalInadequateFalsePositive.coarse_factors_iff law

/-- The retained law is genuinely nonconstant on the common source. -/
theorem factorLaw_nonconstant :
    ∃ left right : Source,
      laws.eval factorLaw left ≠ laws.eval factorLaw right :=
  CanonicalInadequateFalsePositive.factorLaw_nonconstant

/-! ## Current supported nerves and their morphism -/

/-- The coarse two-chart tree with one edge and no faces. -/
abbrev coarseNerve : CoverNerve where
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

/-- The fine two-chart multigraph with two parallel edges and no faces. -/
abbrev fineNerve : CoverNerve where
  Chart := Fin 2
  EdgeComponent := Fin 2
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

/-- The coarse tree with total target support on both charts. -/
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

/-- The fine parallel-edge nerve with total target support on both charts. -/
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

/-- Fine and coarse charts use the same two chart indices. -/
def chartMap (chart : fineSupported.nerve.Chart) :
    coarseSupported.nerve.Chart := chart

/-- Both fine parallel edges map to the unique coarse tree edge. -/
def edgeMap (_edge : fineSupported.nerve.EdgeComponent) :
    Option coarseSupported.nerve.EdgeComponent := some PUnit.unit

/-- The unique map out of the empty fine face type. -/
def faceMap (face : fineSupported.nerve.FaceComponent) :
    Option coarseSupported.nerve.FaceComponent := PEmpty.elim face

/-- The current hereditary morphism that identifies the two parallel fine edges. -/
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
    intro _fineChart _fineTarget _htarget
    exact Set.mem_univ _

/-! ## Canonical law families and actual complexes -/

/-- The exact law family selected by coarse `Factors`. -/
abbrev retainedLaws : FiniteLawFamily Source :=
  laws.descendableSubfamily coarseReading

/-- Coarse adequacy of the exact retained family, derived from subtype properties. -/
theorem coarseRetainedAdequate : retainedLaws.Adequate coarseReading :=
  laws.descendableSubfamily_adequate coarseReading

/-- Fine adequacy of every law retained on the coarse side. -/
theorem retainedLawsFineAdequate : retainedLaws.Adequate fineReading := by
  intro law
  exact fine_adequate law.1

/-- The exact law family selected by fine `Factors` from the original family. -/
abbrev fullFineLaws : FiniteLawFamily Source :=
  laws.descendableSubfamily fineReading

/-- Fine adequacy of the full canonical fine law family. -/
theorem fullFineAdequate : fullFineLaws.Adequate fineReading :=
  laws.descendableSubfamily_adequate fineReading

/-- The actual canonical coarse Factors diagnostic complex. -/
abbrev coarseDiagnosticComplex : ThreeCochainComplex ℚ :=
  coarseSupported.factorsDiagnosticComplex laws

/-- The actual fine complex for the exact family retained on the coarse side. -/
abbrev fineRetainedComplex : ThreeCochainComplex ℚ :=
  fineSupported.lawGeneratedComplex retainedLaws retainedLawsFineAdequate

/-- The actual full canonical fine Factors diagnostic complex. -/
abbrev fineDiagnosticComplex : ThreeCochainComplex ℚ :=
  fineSupported.factorsDiagnosticComplex laws

/-! ## Vanishing of the coarse tree diagnostic -/

/-- A coarse chart coordinate determines the matching coordinate on the tree edge. -/
def coarseEdgeCoordinateOfChart
    (coordinate : coarseSupported.ChartCoordinate retainedLaws
      coarseRetainedAdequate) :
    coarseSupported.EdgeCoordinate retainedLaws coarseRetainedAdequate := by
  refine ⟨PUnit.unit, coordinate.law, coordinate.value, ?_⟩
  obtain ⟨target, _htarget, hvalue⟩ := coordinate.generated
  refine ⟨target, ?_, hvalue⟩
  rw [coarseSupported.mem_edgeSupport_iff]
  exact ⟨Set.mem_univ _, Set.mem_univ _⟩

/-- Reconstructing the coarse edge coordinate from its right chart returns it. -/
theorem coarseEdgeCoordinateOfChart_edgeRight
    (coordinate : coarseSupported.EdgeCoordinate retainedLaws
      coarseRetainedAdequate) :
    coarseEdgeCoordinateOfChart
      (coarseSupported.edgeRightCoordinate retainedLaws
        coarseRetainedAdequate coordinate) = coordinate := by
  apply CellCoordinate.ext
  · rfl
  · rfl
  · rfl

/-- The explicit tree potential integrating any coarse degree-one cochain. -/
def coarsePrimitive (cochain : coarseDiagnosticComplex.C1) :
    coarseDiagnosticComplex.C0 :=
  fun coordinate =>
    if coordinate.cell = 0 then 0 else
      cochain (coarseEdgeCoordinateOfChart coordinate)

/-- The actual coarse generated `d0` of the tree potential is the input cochain. -/
theorem coarse_lawGeneratedD0_primitive
    (cochain : coarseDiagnosticComplex.C1) :
    coarseDiagnosticComplex.d0 (coarsePrimitive cochain) = cochain := by
  funext coordinate
  change
    (coarseSupported.lawGeneratedD0 retainedLaws coarseRetainedAdequate
      (coarsePrimitive cochain)) coordinate = cochain coordinate
  rw [coarseSupported.lawGeneratedD0_apply]
  simp [coarsePrimitive, coarseNerve,
    coarseEdgeCoordinateOfChart_edgeRight]

/-- The canonical coarse Factors diagnostic has zero first cohomology. -/
theorem coarseFactorsDiagnosticH1Zero :
    coarseDiagnosticComplex.H1Zero := by
  intro cohomologyClass
  obtain ⟨cycle, rfl⟩ :=
    (LinearMap.range coarseDiagnosticComplex.boundaryToCycles).mkQ_surjective
      cohomologyClass
  apply (Submodule.Quotient.mk_eq_zero _).2
  refine ⟨coarsePrimitive cycle.1, ?_⟩
  apply Subtype.ext
  exact coarse_lawGeneratedD0_primitive cycle.1

/-! ## Parallel-edge classes in actual fine complexes -/

/-- The coordinate on a chosen fine edge generated by target zero and one law. -/
def fineEdgeCoordinate (family : FiniteLawFamily Source)
    (hadequate : family.Adequate fineReading) (law : family.Law)
    (edge : fineSupported.nerve.EdgeComponent) :
    fineSupported.EdgeCoordinate family hadequate :=
  CellCoordinate.ofSupportedTarget family fineReading hadequate
    fineNerve.EdgeComponent (fineSupported.edgeSupport) edge law 0 (by
      simp [TargetSupportedNerve.edgeSupport])

/-- The two selected fine edge coordinates are distinct by their edge cells. -/
theorem fineEdgeCoordinate_zero_ne_one (family : FiniteLawFamily Source)
    (hadequate : family.Adequate fineReading) (law : family.Law) :
    fineEdgeCoordinate family hadequate law 0 ≠
      fineEdgeCoordinate family hadequate law 1 := by
  intro heq
  have hcell := congrArg
    (fun coordinate : fineSupported.EdgeCoordinate family hadequate =>
      coordinate.cell) heq
  change (0 : Fin 2) = 1 at hcell
  exact zero_ne_one hcell

/-- Difference of a fine cochain on the two parallel edge coordinates. -/
def fineParallelPeriod (family : FiniteLawFamily Source)
    (hadequate : family.Adequate fineReading) (law : family.Law)
    (cochain : (fineSupported.lawGeneratedComplex family hadequate).C1) : ℚ :=
  cochain (fineEdgeCoordinate family hadequate law 1) -
    cochain (fineEdgeCoordinate family hadequate law 0)

/-- Every actual fine coboundary has zero parallel-edge period. -/
theorem fineParallelPeriod_boundary_zero (family : FiniteLawFamily Source)
    (hadequate : family.Adequate fineReading) (law : family.Law)
    (cochain : (fineSupported.lawGeneratedComplex family hadequate).C0) :
    fineParallelPeriod family hadequate law
      ((fineSupported.lawGeneratedComplex family hadequate).d0 cochain) = 0 := by
  change
    (fineSupported.lawGeneratedD0 family hadequate cochain)
        (fineEdgeCoordinate family hadequate law 1) -
      (fineSupported.lawGeneratedD0 family hadequate cochain)
        (fineEdgeCoordinate family hadequate law 0) = 0
  rw [fineSupported.lawGeneratedD0_apply,
    fineSupported.lawGeneratedD0_apply]
  have hright :
      fineSupported.edgeRightCoordinate family hadequate
          (fineEdgeCoordinate family hadequate law 1) =
        fineSupported.edgeRightCoordinate family hadequate
          (fineEdgeCoordinate family hadequate law 0) := by
    apply CellCoordinate.ext
    · rfl
    · rfl
    · rfl
  have hleft :
      fineSupported.edgeLeftCoordinate family hadequate
          (fineEdgeCoordinate family hadequate law 1) =
        fineSupported.edgeLeftCoordinate family hadequate
          (fineEdgeCoordinate family hadequate law 0) := by
    apply CellCoordinate.ext
    · rfl
    · rfl
    · rfl
  rw [hright, hleft]
  exact sub_self _

/-- The unit cochain on the second selected parallel edge coordinate. -/
def fineParallelCochain (family : FiniteLawFamily Source)
    (hadequate : family.Adequate fineReading) (law : family.Law) :
    (fineSupported.lawGeneratedComplex family hadequate).C1 := by
  classical
  exact fun coordinate =>
    if coordinate = fineEdgeCoordinate family hadequate law 1 then 1 else 0

/-- The parallel-edge cochain is an actual cocycle because there are no faces. -/
theorem fineParallelCochain_cocycle (family : FiniteLawFamily Source)
    (hadequate : family.Adequate fineReading) (law : family.Law) :
    (fineSupported.lawGeneratedComplex family hadequate).d1
      (fineParallelCochain family hadequate law) = 0 := by
  funext coordinate
  exact PEmpty.elim coordinate.cell

/-- The selected parallel-edge cocycle in the actual fine kernel. -/
def fineParallelCycle (family : FiniteLawFamily Source)
    (hadequate : family.Adequate fineReading) (law : family.Law) :
    LinearMap.ker (fineSupported.lawGeneratedComplex family hadequate).d1 :=
  ⟨fineParallelCochain family hadequate law,
    fineParallelCochain_cocycle family hadequate law⟩

/-- The actual G-102 quotient class of the selected parallel-edge cocycle. -/
def fineParallelClass (family : FiniteLawFamily Source)
    (hadequate : family.Adequate fineReading) (law : family.Law) :
    (fineSupported.lawGeneratedComplex family hadequate).H1 :=
  (LinearMap.range
      (fineSupported.lawGeneratedComplex family hadequate).boundaryToCycles).mkQ
    (fineParallelCycle family hadequate law)

/-- The selected fine cocycle has unit parallel-edge period. -/
theorem fineParallelPeriod_firing (family : FiniteLawFamily Source)
    (hadequate : family.Adequate fineReading) (law : family.Law) :
    fineParallelPeriod family hadequate law
      (fineParallelCycle family hadequate law).1 = 1 := by
  classical
  change
    (if fineEdgeCoordinate family hadequate law 1 =
        fineEdgeCoordinate family hadequate law 1 then 1 else 0) -
      (if fineEdgeCoordinate family hadequate law 0 =
        fineEdgeCoordinate family hadequate law 1 then 1 else 0) = 1
  rw [if_pos rfl,
    if_neg (fineEdgeCoordinate_zero_ne_one family hadequate law)]
  norm_num

/-- Every selected parallel-edge quotient class is nonzero. -/
theorem fineParallelClass_ne_zero (family : FiniteLawFamily Source)
    (hadequate : family.Adequate fineReading) (law : family.Law) :
    fineParallelClass family hadequate law ≠ 0 := by
  intro hzero
  have hmem := (Submodule.Quotient.mk_eq_zero
    (LinearMap.range
      (fineSupported.lawGeneratedComplex family hadequate).boundaryToCycles)).1
        hzero
  rcases hmem with ⟨cochain, hcochain⟩
  have hperiod := congrArg
    (fun cycle : LinearMap.ker
        (fineSupported.lawGeneratedComplex family hadequate).d1 =>
      fineParallelPeriod family hadequate law cycle.1) hcochain
  change
    fineParallelPeriod family hadequate law
        ((fineSupported.lawGeneratedComplex family hadequate).d0 cochain) =
      fineParallelPeriod family hadequate law
        (fineParallelCycle family hadequate law).1 at hperiod
  rw [fineParallelPeriod_boundary_zero,
    fineParallelPeriod_firing] at hperiod
  exact zero_ne_one hperiod

/-! ## Canonical retained and full fine witnesses -/

/-- The retained nonconstant law as an element of the exact coarse subtype. -/
def retainedLaw : retainedLaws.Law :=
  CanonicalInadequateFalsePositive.retainedLaw

/-- The nonzero parallel-edge class for the exact coarse-retained family. -/
def retainedFineClass : fineRetainedComplex.H1 :=
  fineParallelClass retainedLaws retainedLawsFineAdequate retainedLaw

/-- The retained-family fine class is nonzero. -/
theorem retainedFineClass_ne_zero : retainedFineClass ≠ 0 :=
  fineParallelClass_ne_zero retainedLaws retainedLawsFineAdequate retainedLaw

/-- The retained law as an element of the full fine canonical Factors subtype. -/
def fullFineFactorLaw : fullFineLaws.Law :=
  ⟨factorLaw, fine_adequate factorLaw⟩

/-- The parallel-edge class in the full fine canonical diagnostic. -/
def fullFineClass : fineDiagnosticComplex.H1 :=
  fineParallelClass fullFineLaws fullFineAdequate fullFineFactorLaw

/-- The full fine canonical diagnostic contains a nonzero class. -/
theorem fullFineClass_ne_zero : fullFineClass ≠ 0 :=
  fineParallelClass_ne_zero fullFineLaws fullFineAdequate fullFineFactorLaw

/-- The actual generated comparison map for the exact coarse-retained family. -/
def retainedComparisonH1Map :
    coarseDiagnosticComplex.H1 →ₗ[ℚ] fineRetainedComplex.H1 :=
  nerveMorphism.generatedComparisonH1Map retainedLaws
    coarseRetainedAdequate retainedLawsFineAdequate

/-- The actual generated comparison map misses the retained parallel-edge class. -/
theorem retainedComparisonH1Map_not_surjective :
    ¬ Function.Surjective retainedComparisonH1Map := by
  intro hsurjective
  obtain ⟨sourceClass, hsource⟩ := hsurjective retainedFineClass
  rw [coarseFactorsDiagnosticH1Zero sourceClass, map_zero] at hsource
  exact retainedFineClass_ne_zero hsource.symm

/-- G-104 claim (iv)(b): an inadequate coarse reading hides a true fine class. -/
theorem fixed_claim_iv_b :
    ¬ laws.Adequate coarseReading ∧
      laws.Adequate fineReading ∧
      coarseReading.CoarserThan fineReading ∧
      (¬ Function.Injective
        (comparisonFactor coarseReading fineReading coarse_coarser_fine)) ∧
      (∀ law : laws.Law,
        coarseReading.Factors (laws.eval law) ↔ law = factorLaw) ∧
      (∃ left right : Source,
        laws.eval factorLaw left ≠ laws.eval factorLaw right) ∧
      coarseDiagnosticComplex.H1Zero ∧
      retainedFineClass ≠ 0 ∧
      (¬ Function.Surjective retainedComparisonH1Map) ∧
      fullFineClass ≠ 0 :=
  ⟨coarse_not_adequate, fine_adequate, coarse_coarser_fine,
    comparisonFactor_not_injective, coarse_factors_iff,
    factorLaw_nonconstant, coarseFactorsDiagnosticH1Zero,
    retainedFineClass_ne_zero, retainedComparisonH1Map_not_surjective,
    fullFineClass_ne_zero⟩

end CanonicalInadequateHiddenClass

end AAT.AG.ResolutionInvariance

#assert_standard_axioms_only AAT.AG.ResolutionInvariance.CanonicalInadequateHiddenClass
