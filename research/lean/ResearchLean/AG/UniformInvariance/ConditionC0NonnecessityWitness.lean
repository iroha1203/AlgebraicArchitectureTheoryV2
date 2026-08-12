import ResearchLean.AG.UniformInvariance.ConditionCAllAChecker
import ResearchLean.AG.UniformInvariance.UniformPresentationDecider
import Formal.Util.AssertStandardAxioms

/-!
# A uniform comparison outside the C0 locus

This module formalizes the exact `C0_not_necessary` fixture from the bounded
R1 necessity map for `G-107-aat-uniform-invariance-characterization`.  The raw
presentation is copied field by field from the deterministic R1 payload: its
parent payload has SHA-256
`ff2d9fa12eb64bf343d3148f081e1164d4216d8548e53d90550eb53886dd359a`,
and the canonical name-free serializer recomputes SHA-256
`9222cd14e8e9ff2685b346f9e27ec239ccb86c91a53870811b3a3b4f8da07348`.

The coarse and fine nerves each have two charts, one self-loop at chart zero,
and no faces.  The reading factor is the proper map `[0,0,1]`.  Coarse chart
one supports targets `{0,1}`, while its unique fine chart fiber supports only
fine target `{2}`.  Thus C0 fails at coarse chart one and target zero.  The
same target-zero block retains the self-loop on both sides, and all actual
A-subnerve H¹ comparisons remain bijective.

The finite presentation stores only raw readings, incidence, support, partial
cell maps, and their well-formedness proofs.  It stores no factor, matrix,
rank, cohomology class, defect, condition result, checker result, or
uniformity certificate.  The R1 experiment is provenance for the table, not
a premise of any Lean theorem below.
-/

namespace AAT.AG.ResolutionInvariance

open CanonicalResolution Cohomology TwoPhase

namespace R1ConditionC0Witness

/-! ## Exact raw R1 presentation -/

/-- The proper coarse reading table `[0,0,1]`.  This fixture-local definition
is canonical raw R1 input to `presentation`, not a supplied factor or result. -/
def coarseRead (source : Fin 3) : Fin 2 :=
  if source = 2 then 1 else 0

/-- Coarse chart supports `[{0},{0,1}]`.  This fixture-local function is raw
support input and contains no C0 truth certificate. -/
def coarseChartSupport (chart : Fin 2) : Finset (Fin 2) :=
  if chart = 0 then {0} else {0, 1}

/-- Fine chart supports `[{0,1},{2}]`.  This fixture-local function is the
raw support table whose canonical image is compared in the C0 proof. -/
def fineChartSupport (chart : Fin 2) : Finset (Fin 3) :=
  if chart = 0 then {0, 1} else {2}

/-- Exact finite R1 C0 presentation.  Its fields are only finite readings,
one self-loop incidence table, empty face tables, supports, identity cell
maps, and well-formedness proofs; it stores no factor, H¹, rank, or result. -/
def presentation : FiniteComparisonPresentation where
  Source := Fin 3
  sourceFintype := inferInstance
  sourceDecidableEq := inferInstance
  sourceDefault := 0
  sourceEntries := [0, 1, 2]
  source_mem_sourceEntries := by intro source; fin_cases source <;> simp
  CoarseTarget := Fin 2
  coarseTargetFintype := inferInstance
  coarseTargetDecidableEq := inferInstance
  coarseTargetEntries := [0, 1]
  coarseTarget_mem_coarseTargetEntries := by intro target; fin_cases target <;> simp
  FineTarget := Fin 3
  fineTargetFintype := inferInstance
  fineTargetDecidableEq := inferInstance
  coarseRead := coarseRead
  fineRead := id
  coarseRead_surjective := by
    intro target
    fin_cases target
    · exact ⟨0, by simp [coarseRead]⟩
    · exact ⟨2, by simp [coarseRead]⟩
  fineRead_surjective := Function.surjective_id
  rawCoarserThan := by
    intro left right hequal
    simpa only [id_eq] using congrArg coarseRead hequal
  CoarseChart := Fin 2
  coarseChartFintype := inferInstance
  coarseChartDecidableEq := inferInstance
  CoarseEdge := Fin 1
  coarseEdgeFintype := inferInstance
  coarseEdgeDecidableEq := inferInstance
  CoarseFace := Fin 0
  coarseFaceFintype := inferInstance
  coarseFaceDecidableEq := inferInstance
  coarseEdgeLeft := fun _ => 0
  coarseEdgeRight := fun _ => 0
  coarseFaceEdge0 := fun face => nomatch face
  coarseFaceEdge1 := fun face => nomatch face
  coarseFaceEdge2 := fun face => nomatch face
  coarseFaceEdge0_left := by intro face; exact nomatch face
  coarseFaceEdge0_right := by intro face; exact nomatch face
  coarseFaceEdge1_right := by intro face; exact nomatch face
  coarseChartSupport := coarseChartSupport
  coarseChartSupport_nonempty := by
    intro chart
    fin_cases chart <;> simp [coarseChartSupport]
  FineChart := Fin 2
  fineChartFintype := inferInstance
  fineChartDecidableEq := inferInstance
  FineEdge := Fin 1
  fineEdgeFintype := inferInstance
  fineEdgeDecidableEq := inferInstance
  FineFace := Fin 0
  fineFaceFintype := inferInstance
  fineFaceDecidableEq := inferInstance
  fineEdgeLeft := fun _ => 0
  fineEdgeRight := fun _ => 0
  fineFaceEdge0 := fun face => nomatch face
  fineFaceEdge1 := fun face => nomatch face
  fineFaceEdge2 := fun face => nomatch face
  fineFaceEdge0_left := by intro face; exact nomatch face
  fineFaceEdge0_right := by intro face; exact nomatch face
  fineFaceEdge1_right := by intro face; exact nomatch face
  fineChartSupport := fineChartSupport
  fineChartSupport_nonempty := by
    intro chart
    fin_cases chart <;> simp [fineChartSupport]
  chartMap := id
  edgeMap := some
  faceMap := fun face => nomatch face
  edge_some_left := by
    intro fineEdge coarseEdge hmap
    fin_cases fineEdge
    fin_cases coarseEdge
    rfl
  edge_some_right := by
    intro fineEdge coarseEdge hmap
    fin_cases fineEdge
    fin_cases coarseEdge
    rfl
  edge_none_fiber := by intro fineEdge hmap; simp at hmap
  face_some_edge0 := by intro fineFace; exact nomatch fineFace
  face_some_edge1 := by intro fineFace; exact nomatch fineFace
  face_some_edge2 := by intro fineFace; exact nomatch fineFace
  face_none_edge0 := by intro fineFace; exact nomatch fineFace
  face_none_edge1 := by intro fineFace; exact nomatch fineFace
  face_none_edge2 := by intro fineFace; exact nomatch fineFace
  chartSupport_compatible_source := by
    intro fineChart source hsource
    fin_cases fineChart <;> fin_cases source <;>
      simp [fineChartSupport, coarseChartSupport, coarseRead] at hsource ⊢

/-! ## Canonical factor and degree-one comparison -/

/-- The factor computed from the source enumeration is `[0,0,1]`.  This owner
connection derives the factor from raw readings rather than a fixture field. -/
theorem computedFactor_eq_coarseRead : presentation.computedFactor = coarseRead := by
  funext target
  fin_cases target <;> decide

/-- The semantic canonical factor is the same raw table, by the generic
computed-factor uniqueness theorem. -/
theorem comparisonFactor_eq_coarseRead :
    comparisonFactor presentation.coarseReading presentation.fineReading
      presentation.coarserThan = coarseRead := by
  rw [← presentation.computedFactor_eq_comparisonFactor]
  exact computedFactor_eq_coarseRead

/-- For every coarse target subset, the selected fine and coarse edge tables
have the same unique raw edge.  This is derived from the two support tables and
the computed factor, before any H¹ conclusion. -/
theorem fineEdgesIn_eq_coarseEdgesIn (A : Finset (Fin 2)) :
    presentation.fineEdgesIn A = presentation.coarseEdgesIn A := by
  ext edge
  rw [presentation.mem_fineEdgesIn_iff_raw,
    presentation.mem_coarseEdgesIn_iff_raw, computedFactor_eq_coarseRead]
  simp only [presentation.mem_fineEdgeSupportFinset_iff_raw,
    presentation.mem_coarseEdgeSupportFinset_iff_raw]
  fin_cases edge
  simp [presentation, fineChartSupport, coarseChartSupport, coarseRead]

/-- Forgetting selection proofs identifies selected fine and coarse edges.
This fixture-local equivalence packages the preceding raw-set equality only. -/
def selectedEdgeEquiv (A : Finset (Fin 2)) :
    presentation.FineEdgeIn A ≃ presentation.CoarseEdgeIn A where
  toFun edge := ⟨edge.1, by
    rw [← fineEdgesIn_eq_coarseEdgesIn A]
    exact edge.2⟩
  invFun edge := ⟨edge.1, by
    rw [fineEdgesIn_eq_coarseEdgesIn A]
    exact edge.2⟩
  left_inv edge := Subtype.ext rfl
  right_inv edge := Subtype.ext rfl

/-- Reindex coarse edge cochains along `selectedEdgeEquiv`.  This is the
degree-one linear equivalence used to analyze the actual comparison map. -/
def rawEdgeCochainEquiv (A : Finset (Fin 2)) :
    (presentation.CoarseEdgeIn A → ℚ) ≃ₗ[ℚ]
      (presentation.FineEdgeIn A → ℚ) :=
  cochainEquivOfIndexEquiv (selectedEdgeEquiv A)

/-- The selected partial edge map is the raw identity edge correspondence.
This evaluation theorem is proved through the public partial-map API. -/
theorem edgeMapOptionIn_eq_some_selected (A : Finset (Fin 2))
    (edge : presentation.FineEdgeIn A) :
    presentation.edgeMapOptionIn A edge = some (selectedEdgeEquiv A edge) := by
  exact (presentation.edgeMapOptionIn_eq_some_iff A edge
    (selectedEdgeEquiv A edge)).2 rfl

/-- The raw degree-one pullback is exactly edge reindexing.  This theorem ties
the presentation's partial map to the linear equivalence without an inverse
certificate field. -/
theorem edgePullback1_eq_rawEdgeCochainEquiv (A : Finset (Fin 2))
    (cochain : presentation.CoarseEdgeIn A → ℚ) :
    presentation.edgePullback1LinearMap A cochain =
      rawEdgeCochainEquiv A cochain := by
  funext edge
  rw [presentation.edgePullback1LinearMap_apply]
  rw [edgeMapOptionIn_eq_some_selected]
  rfl

/-! ## Actual H¹ comparison on every target subset -/

/-- The actual coarse constant-rational A-subnerve complex.  This abbreviation
only names the existing semantic construction. -/
abbrev coarseComplex (A : Finset (Fin 2)) : ThreeCochainComplex ℚ :=
  presentation.coarseSupportedNerve.targetSubsetComplex (↑A : Set (Fin 2))

/-- The actual fine complex on the canonical preimage of `A`.  This
abbreviation adds no comparison or cohomology data. -/
abbrev fineComplex (A : Finset (Fin 2)) : ThreeCochainComplex ℚ :=
  presentation.fineSupportedNerve.targetSubsetComplex
    (presentation.canonicalFinePreimage A)

/-- Degree-one equivalence between the actual selected complexes, obtained by
composing the raw/semantic coordinate equivalences with raw edge reindexing. -/
noncomputable def semanticEdgeCochainEquiv (A : Finset (Fin 2)) :
    (coarseComplex A).C1 ≃ₗ[ℚ] (fineComplex A).C1 :=
  (presentation.coarseEdgeCochainEquiv A).trans
    ((rawEdgeCochainEquiv A).trans
      (presentation.fineEdgeCochainEquiv A).symm)

/-- The canonical actual comparison's degree-one map equals the constructed
edge-cochain equivalence.  Its proof uses the raw partial-edge map API. -/
theorem aSubnerveComparisonHom_f1_eq_semanticEquiv
    (A : Finset (Fin 2)) (cochain : (coarseComplex A).C1) :
    (presentation.toGeometry.aSubnerveComparisonHom
        (↑A : Set (Fin 2))).f1 cochain =
      semanticEdgeCochainEquiv A cochain := by
  apply (presentation.fineEdgeCochainEquiv A).injective
  rw [← presentation.edgePullback1_commutes A cochain]
  simp only [semanticEdgeCochainEquiv, LinearEquiv.trans_apply]
  exact edgePullback1_eq_rawEdgeCochainEquiv A
    (presentation.coarseEdgeCochainEquiv A cochain)

/-- Every fine degree-zero boundary vanishes because the only possible edge is
a self-loop.  This is an incidence consequence, not stored rank evidence. -/
theorem fine_d0_zero (A : Finset (Fin 2))
    (cochain : (fineComplex A).C0) :
    (fineComplex A).d0 cochain = 0 := by
  funext edge
  rw [TargetSupportedNerve.targetSubsetComplex_d0_apply]
  have hloop :
      presentation.fineSupportedNerve.targetSubsetEdgeRight
          (presentation.canonicalFinePreimage A) edge =
        presentation.fineSupportedNerve.targetSubsetEdgeLeft
          (presentation.canonicalFinePreimage A) edge := by
    apply Subtype.ext
    rfl
  rw [hloop, sub_self]
  rfl

/-- Every coarse degree-one differential vanishes because the raw coarse face
type is empty. -/
theorem coarse_d1_zero (A : Finset (Fin 2))
    (cochain : (coarseComplex A).C1) :
    (coarseComplex A).d1 cochain = 0 := by
  funext face
  exact Fin.elim0 face.1

/-- The actual canonical H¹ comparison is bijective for every finite target
subset.  Injectivity uses zero fine boundaries and the degree-one equivalence;
surjectivity pulls an arbitrary fine cycle back along that equivalence. -/
theorem aSubnerveComparisonHom_h1Map_bijective (A : Finset (Fin 2)) :
    Function.Bijective
      (presentation.toGeometry.aSubnerveComparisonHom
        (↑A : Set (Fin 2))).h1Map := by
  constructor
  · intro left right hequal
    obtain ⟨leftCycle, rfl⟩ :=
      (LinearMap.range (coarseComplex A).boundaryToCycles).mkQ_surjective left
    obtain ⟨rightCycle, rfl⟩ :=
      (LinearMap.range (coarseComplex A).boundaryToCycles).mkQ_surjective right
    rw [ThreeCochainComplex.Hom.h1Map_mk,
      ThreeCochainComplex.Hom.h1Map_mk] at hequal
    have hquotientZero :
        (LinearMap.range (fineComplex A).boundaryToCycles).mkQ
            ((presentation.toGeometry.aSubnerveComparisonHom
              (↑A : Set (Fin 2))).cyclesMap leftCycle -
              (presentation.toGeometry.aSubnerveComparisonHom
                (↑A : Set (Fin 2))).cyclesMap rightCycle) = 0 := by
      rw [map_sub, hequal, sub_self]
    have hequalMem :=
      (Submodule.Quotient.mk_eq_zero
        (LinearMap.range (fineComplex A).boundaryToCycles)).1 hquotientZero
    rcases hequalMem with ⟨fineCochain, hfineCochain⟩
    have hvalues := congrArg Subtype.val hfineCochain
    simp only [ThreeCochainComplex.boundaryToCycles_apply,
      ThreeCochainComplex.Hom.cyclesMap_sub_apply] at hvalues
    rw [fine_d0_zero] at hvalues
    have hdiff : leftCycle.1 - rightCycle.1 = 0 := by
      apply (semanticEdgeCochainEquiv A).injective
      rw [map_sub, map_zero]
      rw [← aSubnerveComparisonHom_f1_eq_semanticEquiv,
        ← aSubnerveComparisonHom_f1_eq_semanticEquiv]
      exact hvalues.symm
    have hcycles : leftCycle = rightCycle := by
      apply Subtype.ext
      exact sub_eq_zero.mp hdiff
    rw [hcycles]
  · intro targetClass
    obtain ⟨targetCycle, rfl⟩ :=
      (LinearMap.range (fineComplex A).boundaryToCycles).mkQ_surjective targetClass
    let sourceCochain : (coarseComplex A).C1 :=
      (semanticEdgeCochainEquiv A).symm targetCycle.1
    have hcycle : (coarseComplex A).d1 sourceCochain = 0 :=
      coarse_d1_zero A sourceCochain
    let sourceCycle : LinearMap.ker (coarseComplex A).d1 :=
      ⟨sourceCochain, hcycle⟩
    refine ⟨(LinearMap.range (coarseComplex A).boundaryToCycles).mkQ
      sourceCycle, ?_⟩
    rw [ThreeCochainComplex.Hom.h1Map_mk]
    apply congrArg (LinearMap.range (fineComplex A).boundaryToCycles).mkQ
    apply Subtype.ext
    rw [ThreeCochainComplex.Hom.cyclesMap_apply]
    rw [aSubnerveComparisonHom_f1_eq_semanticEquiv]
    exact (semanticEdgeCochainEquiv A).apply_symm_apply targetCycle.1

/-- Every executable A-subnerve defect is literally `(0,0)`, by the generic
raw-to-actual defect theorem and the preceding actual H¹ bijectivity proof. -/
theorem all_computedASubnerveDefects_zero (A : Finset (Fin 2)) :
    presentation.computedASubnerveDefect A = (0, 0) := by
  rw [presentation.computedASubnerveDefect_eq_aSubnerveDefect]
  exact
    (presentation.toGeometry.aSubnerveDefect_eq_zero_iff_bijective
      (↑A : Set (Fin 2))).2
      (aSubnerveComparisonHom_h1Map_bijective A)

/-- The generic finite all-subset uniformity checker accepts this raw table.
This follows from all actual-map defects, not an expected Boolean field. -/
theorem uniformPresentationCheck_true :
    presentation.uniformPresentationCheck = true := by
  apply
    (presentation.uniformPresentationCheck_eq_true_iff_allNonemptyDefects).2
  intro A _hA
  exact all_computedASubnerveDefects_zero A

/-- The exact R1 presentation is semantically uniformly invariant, retaining
the full internal quantification over law families and adequacy proofs. -/
theorem uniformPresentation : UniformPresentation presentation :=
  presentation.uniformPresentationCheck_eq_true_iff.mp
    uniformPresentationCheck_true

/-! ## Direct C0 and all-subset-condition failure -/

/-- Coarse chart one, where the raw support table has an extra target.  This
fixture-local datum is chosen directly from the registered R1 table. -/
def failedCoarseChart : Fin 2 := 1

/-- Coarse target zero, the extra support value causing C0 failure. -/
def failedCoarseTarget : Fin 2 := 0

/-- The nonempty block containing the failed C0 support target and retaining
the common self-loop used for H¹ nonvacuity. -/
def targetZero : Finset (Fin 2) := {0}

/-- The target-zero semantic subset is nonempty, directly from its singleton
definition. -/
theorem targetZero_nonempty :
    (↑targetZero : Set (Fin 2)).Nonempty :=
  ⟨0, by simp [targetZero]⟩

/-- The explicit failed support target lies in the named nonvacuity block. -/
theorem failedCoarseTarget_mem_targetZero :
    failedCoarseTarget ∈ targetZero := by
  simp [failedCoarseTarget, targetZero]

/-- Coarse chart one really supports target zero in the raw presentation. -/
theorem failedCoarseSupport :
    failedCoarseTarget ∈
      presentation.coarseChartSupport failedCoarseChart := by
  simp [failedCoarseTarget, failedCoarseChart, presentation,
    coarseChartSupport]

/-- No fine target supported on the unique fine chart over chart one maps to
coarse target zero.  This is the direct raw support obstruction to C0. -/
theorem failedSupportDatum :
    ¬ ∃ fineChart fineTarget,
      presentation.chartMap fineChart = failedCoarseChart ∧
      fineTarget ∈ presentation.fineChartSupport fineChart ∧
      presentation.computedFactor fineTarget = failedCoarseTarget := by
  rintro ⟨fineChart, fineTarget, hchart, hsupport, hfactor⟩
  rw [computedFactor_eq_coarseRead] at hfactor
  fin_cases fineChart <;> fin_cases fineTarget <;>
    simp [presentation, fineChartSupport, coarseRead, failedCoarseChart,
      failedCoarseTarget] at hchart hsupport hfactor

/-- The executable raw C0 proposition fails at the named chart-target pair. -/
theorem not_rawConditionC0 : ¬ presentation.RawConditionC0 := by
  intro hC0
  exact failedSupportDatum
    ((hC0 failedCoarseChart failedCoarseTarget).mp failedCoarseSupport)

/-- The generic raw-table C0 checker evaluates to false.  The proof reflects
`not_rawConditionC0` rather than storing the expected result. -/
theorem conditionC0Check_false : presentation.conditionC0Check = false := by
  apply Bool.eq_false_of_not_eq_true
  intro htrue
  exact not_rawConditionC0 (of_decide_eq_true htrue)

/-- Semantic whole-nerve C0 fails on the generated comparison geometry, via
the generic raw/semantic C0 equivalence. -/
theorem not_conditionC0 : ¬ presentation.toGeometry.ConditionC0 := by
  intro hC0
  exact not_rawConditionC0
    (presentation.rawConditionC0_iff_conditionC0.mpr hC0)

/-- The all-subset Condition C package fails directly by its whole-nerve C0
projection; no reverse law-block transport is used. -/
theorem not_conditionCAllA :
    ¬ presentation.toGeometry.ConditionCAllA := by
  intro hAllA
  exact not_conditionC0 hAllA.conditionC0

/-- The generic all-subset Condition C checker evaluates to false because its
soundness theorem would otherwise contradict the direct C0 projection. -/
theorem conditionCAllACheck_false :
    presentation.conditionCAllACheck = false := by
  apply Bool.eq_false_of_not_eq_true
  intro htrue
  exact not_conditionCAllA
    (presentation.conditionCAllACheck_eq_true_iff.mp htrue)

/-! ## A nonconstant law-indexed failure -/

/-- The canonical Boolean indicator law family of the target-zero subset.
This family is generated from the coarse reading and stores no condition bit. -/
noncomputable def indicatorLaws : FiniteLawFamily presentation.Source :=
  indicatorLawFamily presentation.coarseReading
    (↑targetZero : Set (Fin 2))

/-- Canonical adequacy of the target-zero indicator for the coarse reading. -/
theorem indicatorCoarseAdequate :
    indicatorLaws.Adequate presentation.coarseReading :=
  indicatorLawFamily_adequate presentation.coarseReading
    (↑targetZero : Set (Fin 2))

/-- Canonical adequacy of the same indicator for the finer reading, derived
from the coarser-than relation. -/
theorem indicatorFineAdequate :
    indicatorLaws.Adequate presentation.fineReading :=
  indicatorLawFamily_adequate_of_coarserThan presentation.coarseReading
    presentation.fineReading presentation.coarserThan
    (↑targetZero : Set (Fin 2))

/-- The indicator genuinely distinguishes sources zero and two.  This
nondegeneracy statement is computed from raw readings and indicator semantics. -/
theorem indicatorLaw_nonconstant :
    ∃ left right : presentation.Source,
      indicatorLaws.eval PUnit.unit left ≠
        indicatorLaws.eval PUnit.unit right := by
  refine ⟨(0 : Fin 3), (2 : Fin 3), ?_⟩
  simp [indicatorLaws, indicatorLawFamily_eval, targetSubsetIndicator,
    presentation, coarseRead, targetZero]
  constructor
  · intro hequal
    have hval := congrArg Fin.val hequal
    norm_num at hval
  · intro hequal
    have hbool := congrArg ULift.down hequal
    simp at hbool

/-- The full law-indexed Condition C package fails for the proved-nonconstant
indicator family, by its C0 field and the direct semantic obstruction. -/
theorem indicator_not_conditionC :
    ¬ presentation.toGeometry.ConditionC indicatorLaws
      indicatorCoarseAdequate indicatorFineAdequate := by
  intro hC
  exact not_conditionC0 hC.c0

/-! ## Nonzero H¹ on the block meeting the failed support datum -/

/-- The actual coarse target-zero complex, named for the literal quotient-H¹
nonvacuity argument. -/
abbrev coarseTargetZeroComplex : ThreeCochainComplex ℚ :=
  coarseComplex targetZero

/-- The actual fine complex on the canonical preimage of target zero. -/
abbrev fineTargetZeroComplex : ThreeCochainComplex ℚ :=
  fineComplex targetZero

/-- The unique raw coarse self-loop selected by target zero, derived from the
raw selection predicate. -/
def coarseEdgeZero : presentation.CoarseEdgeIn targetZero :=
  ⟨(0 : Fin 1), by decide⟩

/-- The corresponding actual A-subnerve self-loop, obtained through the
owner-provided raw/semantic edge equivalence. -/
def coarseActualEdgeZero :
    presentation.coarseSupportedNerve.EdgeInTargetSubset
      (↑targetZero : Set (Fin 2)) :=
  presentation.coarseEdgeEquiv targetZero coarseEdgeZero

/-- Evaluation on the actual target-zero self-loop.  This linear functional
detects the explicit quotient-H¹ class. -/
def coarseTargetZeroPeriod (cochain : coarseTargetZeroComplex.C1) : ℚ :=
  cochain coarseActualEdgeZero

/-- Evaluation of the target-zero period functional is literal evaluation at
the named actual self-loop.  This fixture API lets later proofs avoid
expanding the functional definition. -/
@[simp]
theorem coarseTargetZeroPeriod_apply (cochain : coarseTargetZeroComplex.C1) :
    coarseTargetZeroPeriod cochain = cochain coarseActualEdgeZero :=
  rfl

/-- Every coarse coboundary has zero loop period, because the selected edge
has equal endpoints. -/
theorem coarseTargetZeroPeriod_boundary_zero
    (cochain : coarseTargetZeroComplex.C0) :
    coarseTargetZeroPeriod (coarseTargetZeroComplex.d0 cochain) = 0 := by
  rw [coarseTargetZeroPeriod_apply,
    TargetSupportedNerve.targetSubsetComplex_d0_apply]
  have hloop :
      presentation.coarseSupportedNerve.targetSubsetEdgeRight
          (↑targetZero : Set (Fin 2)) coarseActualEdgeZero =
        presentation.coarseSupportedNerve.targetSubsetEdgeLeft
          (↑targetZero : Set (Fin 2)) coarseActualEdgeZero := by
    apply Subtype.ext
    rfl
  rw [hloop]
  ring

/-- Constant coefficient one on the actual coarse self-loop.  This explicit
cochain is proof data, not a presentation field. -/
def coarseTargetZeroCochain : coarseTargetZeroComplex.C1 :=
  fun _ => 1

/-- The constant loop cochain is a cocycle because the coarse face type is
empty. -/
theorem coarseTargetZeroCochain_cocycle :
    coarseTargetZeroComplex.d1 coarseTargetZeroCochain = 0 :=
  coarse_d1_zero targetZero coarseTargetZeroCochain

/-- The explicit loop cocycle packaged in the actual degree-one kernel. -/
def coarseTargetZeroCycle : LinearMap.ker coarseTargetZeroComplex.d1 :=
  ⟨coarseTargetZeroCochain, coarseTargetZeroCochain_cocycle⟩

/-- The literal quotient-H¹ class of the explicit self-loop cocycle. -/
def coarseTargetZeroClass : coarseTargetZeroComplex.H1 :=
  (LinearMap.range coarseTargetZeroComplex.boundaryToCycles).mkQ
    coarseTargetZeroCycle

/-- The displayed cocycle has unit period on the selected self-loop. -/
theorem coarseTargetZeroPeriod_cycle :
    coarseTargetZeroPeriod coarseTargetZeroCycle.1 = 1 := by
  rfl

/-- The actual coarse target-zero quotient class is nonzero: boundaries have
zero period while the explicit cycle has period one. -/
theorem coarseTargetZeroClass_ne_zero : coarseTargetZeroClass ≠ 0 := by
  intro hzero
  have hmem := (Submodule.Quotient.mk_eq_zero
    (LinearMap.range coarseTargetZeroComplex.boundaryToCycles)).1 hzero
  rcases hmem with ⟨cochain, hcochain⟩
  have hperiod := congrArg
    (fun cycle : LinearMap.ker coarseTargetZeroComplex.d1 =>
      coarseTargetZeroPeriod cycle.1) hcochain
  change coarseTargetZeroPeriod
      (coarseTargetZeroComplex.boundaryToCycles cochain).1 =
    coarseTargetZeroPeriod coarseTargetZeroCycle.1 at hperiod
  rw [ThreeCochainComplex.boundaryToCycles_apply] at hperiod
  rw [coarseTargetZeroPeriod_boundary_zero,
    coarseTargetZeroPeriod_cycle] at hperiod
  exact zero_ne_one hperiod

/-- The coarse target-zero H¹ space has positive finite dimension, witnessed
by the explicit nonzero quotient class. -/
theorem targetZero_coarse_h1_pos :
    0 < Module.finrank ℚ coarseTargetZeroComplex.H1 :=
  Module.finrank_pos_iff_exists_ne_zero.mpr
    ⟨coarseTargetZeroClass, coarseTargetZeroClass_ne_zero⟩

/-- The fine target-zero class is the image of the explicit coarse class under
the actual canonical H¹ comparison map. -/
def fineTargetZeroClass : fineTargetZeroComplex.H1 :=
  (presentation.toGeometry.aSubnerveComparisonHom
    (↑targetZero : Set (Fin 2))).h1Map coarseTargetZeroClass

/-- The actual fine image class is nonzero by injectivity of the target-zero
canonical H¹ comparison. -/
theorem fineTargetZeroClass_ne_zero : fineTargetZeroClass ≠ 0 := by
  intro hzero
  apply coarseTargetZeroClass_ne_zero
  apply (aSubnerveComparisonHom_h1Map_bijective targetZero).1
  simpa only [fineTargetZeroClass, map_zero] using hzero

/-- The fine canonical-preimage H¹ space has positive finite dimension. -/
theorem targetZero_fine_h1_pos :
    0 < Module.finrank ℚ fineTargetZeroComplex.H1 :=
  Module.finrank_pos_iff_exists_ne_zero.mpr
    ⟨fineTargetZeroClass, fineTargetZeroClass_ne_zero⟩

/-- Both sides of the same target-zero comparison meeting the failed C0 datum
have nonzero H¹. -/
theorem targetZero_both_h1_pos :
    0 < Module.finrank ℚ coarseTargetZeroComplex.H1 ∧
      0 < Module.finrank ℚ fineTargetZeroComplex.H1 :=
  ⟨targetZero_coarse_h1_pos, targetZero_fine_h1_pos⟩

/-! ## Bounded R1 necessity conclusion -/

/-- Exact C0 non-necessity witness: the raw presentation is uniformly
invariant, fails C0 directly and inside both law-indexed and all-subset
Condition C packages, and has nonzero H¹ on both sides of a block containing
the failed support target.  Every component is a closed theorem above. -/
theorem c0_not_necessary :
    UniformPresentation presentation ∧
      (∃ left right : presentation.Source,
        indicatorLaws.eval PUnit.unit left ≠
          indicatorLaws.eval PUnit.unit right) ∧
      ¬ presentation.toGeometry.ConditionC indicatorLaws
        indicatorCoarseAdequate indicatorFineAdequate ∧
      ¬ presentation.toGeometry.ConditionC0 ∧
      ¬ presentation.toGeometry.ConditionCAllA ∧
      (↑targetZero : Set (Fin 2)).Nonempty ∧
      failedCoarseTarget ∈ targetZero ∧
      0 < Module.finrank ℚ coarseTargetZeroComplex.H1 ∧
      0 < Module.finrank ℚ fineTargetZeroComplex.H1 :=
  ⟨uniformPresentation, indicatorLaw_nonconstant,
    indicator_not_conditionC, not_conditionC0, not_conditionCAllA,
    targetZero_nonempty, failedCoarseTarget_mem_targetZero,
    targetZero_coarse_h1_pos, targetZero_fine_h1_pos⟩

end R1ConditionC0Witness

end AAT.AG.ResolutionInvariance

#assert_standard_axioms_only AAT.AG.ResolutionInvariance
