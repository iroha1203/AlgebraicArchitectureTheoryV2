import ResearchLean.AG.UniformInvariance.ConditionCAllABridge
import ResearchLean.AG.UniformInvariance.ConditionCAllAChecker
import ResearchLean.AG.UniformInvariance.UniformPresentationDecider
import Formal.Util.AssertStandardAxioms

/-!
# A uniform comparison outside the C2 locus

This module formalizes the exact `C2_not_necessary` fixture from the bounded
R1 necessity map for `G-107-aat-uniform-invariance-characterization`.  The
deterministic payload fixes the factor, target counts, nerves, supports, and
cell maps; the source and readings below are a canonical realization of that
factor.  The parent payload has SHA-256
`ff2d9fa12eb64bf343d3148f081e1164d4216d8548e53d90550eb53886dd359a`,
and the canonical name-free serializer recomputes SHA-256
`b0ff8026708b3a5466568682efc72b2758469ca3f526e75756eabcee24355cc9`.

The coarse nerve has one self-loop at chart zero and one extra edge from
chart one to chart two.  The fine nerve retains only the self-loop, and its
sole edge maps to the coarse self-loop.  Thus the extra coarse edge has no
fine lift on the full target subset.  The tree edge contributes no H¹, so the
actual comparison remains bijective on every nonempty target subset; on the
same full subset, the common self-loop gives nonzero H¹ on both sides.

The finite presentation stores only raw readings, incidence, support, partial
cell maps, and their well-formedness proofs.  It stores no factor, matrix,
rank, cohomology class, defect, condition result, checker result, or
uniformity certificate.  The R1 experiment is provenance for the table, not
a premise of any Lean theorem below.
-/

namespace AAT.AG.ResolutionInvariance

open CanonicalResolution Cohomology TwoPhase

namespace R1ConditionC2Witness

/-! ## Exact raw R1 presentation -/

/-- The proper coarse reading table `[0,0,1]`.  This fixture-local definition
is canonical raw R1 input to `presentation`, not a supplied factor or result. -/
def coarseRead (source : Fin 3) : Fin 2 :=
  if source = 2 then 1 else 0

/-- Left endpoints of the coarse edges `(0,0)` and `(1,2)`.  This is raw
incidence input and contains no lift or cohomology certificate. -/
def coarseEdgeLeft (edge : Fin 2) : Fin 3 :=
  if edge = 0 then 0 else 1

/-- Right endpoints of the coarse edges `(0,0)` and `(1,2)`.  This is raw
incidence input and contains no lift or cohomology certificate. -/
def coarseEdgeRight (edge : Fin 2) : Fin 3 :=
  if edge = 0 then 0 else 2

/-- Coarse chart supports `[{0},{1},{1}]`.  This raw support table carries no
C2 truth certificate. -/
def coarseChartSupport (chart : Fin 3) : Finset (Fin 2) :=
  if chart = 0 then {0} else {1}

/-- Fine chart supports `[{0,1},{2},{2}]`.  This raw support table carries no
C2 truth certificate. -/
def fineChartSupport (chart : Fin 3) : Finset (Fin 3) :=
  if chart = 0 then {0, 1} else {2}

/-- Exact finite R1 C2 presentation.  Its fields are only finite readings,
incidence, empty face tables, supports, partial cell maps, and well-formedness
proofs; it stores no factor, lift, H¹, rank, or result. -/
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
  CoarseChart := Fin 3
  coarseChartFintype := inferInstance
  coarseChartDecidableEq := inferInstance
  CoarseEdge := Fin 2
  coarseEdgeFintype := inferInstance
  coarseEdgeDecidableEq := inferInstance
  CoarseFace := Fin 0
  coarseFaceFintype := inferInstance
  coarseFaceDecidableEq := inferInstance
  coarseEdgeLeft := coarseEdgeLeft
  coarseEdgeRight := coarseEdgeRight
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
  FineChart := Fin 3
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
  edgeMap := fun _ => some 0
  faceMap := fun face => nomatch face
  edge_some_left := by
    intro fineEdge mappedEdge hmap
    fin_cases fineEdge
    fin_cases mappedEdge <;> simp at hmap
    rfl
  edge_some_right := by
    intro fineEdge mappedEdge hmap
    fin_cases fineEdge
    fin_cases mappedEdge <;> simp at hmap
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

/-! ## Canonical factor and raw degree-one comparison -/

/-- The factor computed from the source enumeration is `[0,0,1]`, derived
from raw readings rather than stored as a presentation field. -/
theorem computedFactor_eq_coarseRead : presentation.computedFactor = coarseRead := by
  funext target
  fin_cases target <;> decide

/-- The semantic canonical factor is the same raw table by generic uniqueness. -/
theorem comparisonFactor_eq_coarseRead :
    comparisonFactor presentation.coarseReading presentation.fineReading
      presentation.coarserThan = coarseRead := by
  rw [← presentation.computedFactor_eq_comparisonFactor]
  exact computedFactor_eq_coarseRead

/-- The coarse self-loop is selected exactly when target zero is selected.
This is a raw-support calculation used by the comparison proof. -/
theorem coarseLoop_mem_iff_zero_mem (A : Finset (Fin 2)) :
    (0 : Fin 2) ∈ presentation.coarseEdgesIn A ↔ (0 : Fin 2) ∈ A := by
  rw [presentation.mem_coarseEdgesIn_iff_raw]
  simp only [presentation.mem_coarseEdgeSupportFinset_iff_raw]
  simp [presentation, coarseChartSupport, coarseEdgeLeft, coarseEdgeRight]

/-- The coarse interval edge is selected exactly when target one is selected.
This is a raw-support calculation and contains no C2 conclusion. -/
theorem coarseInterval_mem_iff_one_mem (A : Finset (Fin 2)) :
    (1 : Fin 2) ∈ presentation.coarseEdgesIn A ↔ (1 : Fin 2) ∈ A := by
  rw [presentation.mem_coarseEdgesIn_iff_raw]
  simp only [presentation.mem_coarseEdgeSupportFinset_iff_raw]
  simp [presentation, coarseChartSupport, coarseEdgeLeft, coarseEdgeRight]

/-- The sole fine self-loop is selected exactly when coarse target zero is
selected under the computed factor. -/
theorem fineLoop_mem_iff_zero_mem (A : Finset (Fin 2)) :
    (0 : Fin 1) ∈ presentation.fineEdgesIn A ↔ (0 : Fin 2) ∈ A := by
  rw [presentation.mem_fineEdgesIn_iff_raw]
  simp only [presentation.mem_fineEdgeSupportFinset_iff_raw]
  rw [computedFactor_eq_coarseRead]
  simp [presentation, fineChartSupport, coarseRead]

/-- A raw coarse edge cochain lifting any raw fine edge cochain.  It assigns
the fine loop value to the coarse loop and zero to the interval edge. -/
noncomputable def rawEdgeLift (A : Finset (Fin 2))
    (cochain : presentation.FineEdgeIn A → ℚ) :
    presentation.CoarseEdgeIn A → ℚ := fun edge =>
  if h : (show Fin 2 from edge.1) = 0 then
    cochain ⟨(0 : Fin 1), (fineLoop_mem_iff_zero_mem A).2
      ((coarseLoop_mem_iff_zero_mem A).1 (h ▸ edge.2))⟩
  else 0

/-- Raw degree-one pullback applied to `rawEdgeLift` returns the original fine
cochain.  The proof uses the selected partial-map API. -/
theorem edgePullback1_rawEdgeLift (A : Finset (Fin 2))
    (cochain : presentation.FineEdgeIn A → ℚ) :
    presentation.edgePullback1LinearMap A (rawEdgeLift A cochain) = cochain := by
  funext fineEdge
  have hfine : (show Fin 1 from fineEdge.1) = 0 := Subsingleton.elim _ _
  have hzero : (0 : Fin 2) ∈ A :=
    (fineLoop_mem_iff_zero_mem A).1 (hfine ▸ fineEdge.2)
  let coarseEdge : presentation.CoarseEdgeIn A :=
    ⟨(0 : Fin 2), (coarseLoop_mem_iff_zero_mem A).2 hzero⟩
  have hmap : presentation.edgeMapOptionIn A fineEdge = some coarseEdge :=
    (presentation.edgeMapOptionIn_eq_some_iff A fineEdge coarseEdge).2 (by
      simp [presentation, coarseEdge])
  rw [presentation.edgePullback1LinearMap_apply, hmap]
  simp only [Option.elim_some]
  have hedge : (show Fin 2 from coarseEdge.1) = 0 := rfl
  rw [rawEdgeLift, dif_pos hedge]
  congr 1
  exact Subtype.ext hfine.symm

/-- A coarse self-loop coefficient vanishes whenever its raw pullback
vanishes. -/
theorem loop_eq_zero_of_pullback_eq_zero (A : Finset (Fin 2))
    (cochain : presentation.CoarseEdgeIn A → ℚ)
    (hpullback : presentation.edgePullback1LinearMap A cochain = 0)
    (edge : presentation.CoarseEdgeIn A)
    (hedge : (show Fin 2 from edge.1) = 0) : cochain edge = 0 := by
  have hzero : (0 : Fin 2) ∈ A :=
    (coarseLoop_mem_iff_zero_mem A).1 (hedge ▸ edge.2)
  let fineEdge : presentation.FineEdgeIn A :=
    ⟨(0 : Fin 1), (fineLoop_mem_iff_zero_mem A).2 hzero⟩
  have hmap : presentation.edgeMapOptionIn A fineEdge = some edge :=
    (presentation.edgeMapOptionIn_eq_some_iff A fineEdge edge).2 (by
      simpa [presentation] using congrArg some hedge.symm)
  have hvalue := congrFun hpullback fineEdge
  rw [presentation.edgePullback1LinearMap_apply, hmap] at hvalue
  simpa using hvalue

/-- A raw primitive for the interval-edge part of a coarse cochain.  The
finite sum makes the definition valid whether or not the interval is selected. -/
noncomputable def rawIntervalPrimitive (A : Finset (Fin 2))
    (cochain : presentation.CoarseEdgeIn A → ℚ) :
    presentation.CoarseChartIn A → ℚ := fun chart =>
  ∑ edge : presentation.CoarseEdgeIn A,
    if (show Fin 2 from edge.1) = 1 ∧
        (show Fin 3 from chart.1) = 2 then cochain edge else 0

/-- The interval primitive has coarse differential equal to any cochain whose
self-loop coefficient vanishes. -/
theorem coarseD0_rawIntervalPrimitive
    (A : Finset (Fin 2)) (cochain : presentation.CoarseEdgeIn A → ℚ)
    (hloop : ∀ edge, (show Fin 2 from edge.1) = 0 → cochain edge = 0) :
    presentation.coarseD0LinearMap A (rawIntervalPrimitive A cochain) =
      cochain := by
  classical
  funext edge
  rw [presentation.coarseD0LinearMap_apply]
  have hedgeCases : (show Fin 2 from edge.1) = 0 ∨
      (show Fin 2 from edge.1) = 1 := by omega
  rcases hedgeCases with hedge | hedge
  · have hend : presentation.coarseEdgeRightIn A edge =
        presentation.coarseEdgeLeftIn A edge := by
      apply Subtype.ext
      simp [presentation, hedge, coarseEdgeLeft, coarseEdgeRight]
    rw [hend, sub_self]
    exact (hloop edge hedge).symm
  · have hleft :
        (show Fin 3 from (presentation.coarseEdgeLeftIn A edge).1) = 1 := by
      simp [presentation, hedge, coarseEdgeLeft]
    have hright :
        (show Fin 3 from (presentation.coarseEdgeRightIn A edge).1) = 2 := by
      simp [presentation, hedge, coarseEdgeRight]
    have hrightValue :
        rawIntervalPrimitive A cochain
            (presentation.coarseEdgeRightIn A edge) = cochain edge := by
      simp only [rawIntervalPrimitive, hright, and_true]
      rw [Fintype.sum_eq_single edge]
      · simp [hedge]
      · intro candidate hne
        split_ifs with hcandidate
        · exact False.elim
            (hne (Subtype.ext (hcandidate.trans hedge.symm)))
        · rfl
    have hleftValue :
        rawIntervalPrimitive A cochain
            (presentation.coarseEdgeLeftIn A edge) = 0 := by
      simp only [rawIntervalPrimitive]
      apply Finset.sum_eq_zero
      intro candidate _hmember
      split_ifs with hcandidate
      · have hcontra :
            (show Fin 3 from
              (presentation.coarseEdgeLeftIn A edge).1) = 2 :=
          hcandidate.2
        omega
      · rfl
    rw [hrightValue, hleftValue, sub_zero]

/-- The raw degree-one pullback is surjective on every selected target subset. -/
theorem edgePullback1LinearMap_surjective (A : Finset (Fin 2)) :
    Function.Surjective (presentation.edgePullback1LinearMap A) := by
  intro cochain
  exact ⟨rawEdgeLift A cochain, edgePullback1_rawEdgeLift A cochain⟩

/-! ## Actual quotient-H¹ comparison on every target subset -/

/-- The actual coarse constant-rational A-subnerve complex. -/
abbrev coarseComplex (A : Finset (Fin 2)) : ThreeCochainComplex ℚ :=
  presentation.coarseSupportedNerve.targetSubsetComplex (↑A : Set (Fin 2))

/-- The actual fine complex on the canonical preimage of `A`. -/
abbrev fineComplex (A : Finset (Fin 2)) : ThreeCochainComplex ℚ :=
  presentation.fineSupportedNerve.targetSubsetComplex
    (presentation.canonicalFinePreimage A)

/-- Every fine degree-zero boundary vanishes because the only possible fine
edge is a self-loop. -/
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

/-- Every coarse degree-one differential vanishes because the coarse face
type is empty. -/
theorem coarse_d1_zero (A : Finset (Fin 2))
    (cochain : (coarseComplex A).C1) :
    (coarseComplex A).d1 cochain = 0 := by
  funext face
  exact Fin.elim0 face.1

/-- Every fine degree-one differential vanishes because the fine face type is
empty. -/
theorem fine_d1_zero (A : Finset (Fin 2))
    (cochain : (fineComplex A).C1) :
    (fineComplex A).d1 cochain = 0 := by
  funext face
  exact Fin.elim0 face.1

/-- The actual canonical H¹ comparison is bijective on every target subset.
Injectivity absorbs the unmapped coarse tree edge as an actual boundary;
surjectivity lifts the sole fine self-loop coefficient through the raw map. -/
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
    let rawDifference : presentation.CoarseEdgeIn A → ℚ :=
      presentation.coarseEdgeCochainEquiv A (leftCycle.1 - rightCycle.1)
    have hpullback :
        presentation.edgePullback1LinearMap A rawDifference = 0 := by
      rw [show rawDifference = presentation.coarseEdgeCochainEquiv A
        (leftCycle.1 - rightCycle.1) by rfl]
      rw [presentation.edgePullback1_commutes]
      rw [map_sub, hvalues.symm, map_zero]
    let rawPrimitive := rawIntervalPrimitive A rawDifference
    let semanticPrimitive : (coarseComplex A).C0 :=
      (presentation.coarseChartCochainEquiv A).symm rawPrimitive
    apply (Submodule.Quotient.eq _).2
    refine ⟨semanticPrimitive, ?_⟩
    apply Subtype.ext
    change (coarseComplex A).d0 semanticPrimitive =
      leftCycle.1 - rightCycle.1
    apply (presentation.coarseEdgeCochainEquiv A).injective
    have hcommutes := presentation.coarseD0_commutes A semanticPrimitive
    change presentation.coarseD0LinearMap A
        (presentation.coarseChartCochainEquiv A semanticPrimitive) =
      presentation.coarseEdgeCochainEquiv A
        ((coarseComplex A).d0 semanticPrimitive) at hcommutes
    rw [← hcommutes]
    change presentation.coarseD0LinearMap A rawPrimitive = rawDifference
    exact coarseD0_rawIntervalPrimitive A rawDifference
      (fun edge hedge =>
        loop_eq_zero_of_pullback_eq_zero A rawDifference hpullback edge hedge)
  · intro targetClass
    obtain ⟨targetCycle, rfl⟩ :=
      (LinearMap.range (fineComplex A).boundaryToCycles).mkQ_surjective targetClass
    obtain ⟨rawSource, hpullback⟩ :=
      edgePullback1LinearMap_surjective A
        (presentation.fineEdgeCochainEquiv A targetCycle.1)
    let sourceCochain : (coarseComplex A).C1 :=
      (presentation.coarseEdgeCochainEquiv A).symm rawSource
    have hcycle : (coarseComplex A).d1 sourceCochain = 0 :=
      coarse_d1_zero A sourceCochain
    let sourceCycle : LinearMap.ker (coarseComplex A).d1 :=
      ⟨sourceCochain, hcycle⟩
    refine ⟨(LinearMap.range (coarseComplex A).boundaryToCycles).mkQ
      sourceCycle, ?_⟩
    rw [ThreeCochainComplex.Hom.h1Map_mk]
    apply congrArg (LinearMap.range (fineComplex A).boundaryToCycles).mkQ
    apply Subtype.ext
    apply (presentation.fineEdgeCochainEquiv A).injective
    rw [ThreeCochainComplex.Hom.cyclesMap_apply]
    rw [← presentation.edgePullback1_commutes]
    change presentation.edgePullback1LinearMap A rawSource =
      presentation.fineEdgeCochainEquiv A targetCycle.1
    exact hpullback

/-- Every executable A-subnerve defect is literally `(0,0)`, by the generic
raw-to-actual theorem and the preceding actual quotient-H¹ proof. -/
theorem all_computedASubnerveDefects_zero (A : Finset (Fin 2)) :
    presentation.computedASubnerveDefect A = (0, 0) := by
  rw [presentation.computedASubnerveDefect_eq_aSubnerveDefect]
  exact
    (presentation.toGeometry.aSubnerveDefect_eq_zero_iff_bijective
      (↑A : Set (Fin 2))).2
      (aSubnerveComparisonHom_h1Map_bijective A)

/-- The generic finite all-subset checker accepts the fixture as a consequence
of the actual H¹ comparison theorem. -/
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

/-! ## Direct C2 and all-subset-condition failure -/

/-- The full coarse target subset.  It is a registered C2-failure subset and
retains the common nonzero H¹ self-loop. -/
def targetFull : Finset (Fin 2) := Finset.univ

/-- The full target subset is nonempty. -/
theorem targetFull_nonempty : (↑targetFull : Set (Fin 2)).Nonempty :=
  ⟨0, by simp [targetFull]⟩

/-- The extra coarse interval edge selected by the full subset. -/
def coarseEdgeOne : presentation.CoarseEdgeIn targetFull :=
  ⟨(1 : Fin 2), by decide⟩

/-- Raw C2 fails at the full target subset because the sole fine edge maps to
coarse edge zero, never to the displayed interval edge one. -/
theorem not_rawConditionC2At :
    ¬ presentation.RawConditionC2At targetFull := by
  intro hC2
  obtain ⟨fineEdge, hmap⟩ := hC2 coarseEdgeOne
  have hval : (0 : Fin 2) = 1 := by
    simpa [presentation, coarseEdgeOne] using Option.some.inj hmap
  omega

/-- The executable raw C2 checker evaluates to false on the same full target
subset. -/
theorem conditionC2AtTargetSubsetCheck_false :
    presentation.conditionC2AtTargetSubsetCheck targetFull = false := by
  apply Bool.eq_false_of_not_eq_true
  intro htrue
  exact not_rawConditionC2At (of_decide_eq_true htrue)

/-- Semantic C2 fails on the actual full A-subnerve by the generic raw/actual
soundness and completeness theorem. -/
theorem not_conditionC2AtTargetSubset :
    ¬ presentation.toGeometry.ConditionC2AtTargetSubset
      (↑targetFull : Set (Fin 2)) := by
  intro hC2
  exact not_rawConditionC2At
    ((presentation.rawConditionC2At_iff_conditionC2AtTargetSubset
      targetFull).mpr hC2)

/-- `ConditionCAllA` fails directly at its C2 projection on the named nonempty
full subset. -/
theorem not_conditionCAllA :
    ¬ presentation.toGeometry.ConditionCAllA := by
  intro hAllA
  exact not_conditionC2AtTargetSubset
    (hAllA.conditionC2At presentation.toGeometry
      (↑targetFull : Set (Fin 2)) targetFull_nonempty)

/-- The generic aggregate checker is false because semantic soundness would
contradict the direct full-subset C2 obstruction. -/
theorem conditionCAllACheck_false :
    presentation.conditionCAllACheck = false := by
  apply Bool.eq_false_of_not_eq_true
  intro htrue
  exact not_conditionCAllA
    (presentation.conditionCAllACheck_eq_true_iff.mp htrue)

/-! ## Law-indexed C2 failure on the same label fiber -/

/-- The canonical Boolean indicator family of the full coarse target subset.
It is constant true, as the fixed GOAL permits; the proper factor, missing
interval lift, and same-block nonzero H¹ provide nonvacuity. -/
noncomputable def indicatorLaws : FiniteLawFamily presentation.Source :=
  indicatorLawFamily presentation.coarseReading
    (↑targetFull : Set (Fin 2))

/-- Canonical adequacy of the full-subset indicator for the coarse reading. -/
theorem indicatorCoarseAdequate :
    indicatorLaws.Adequate presentation.coarseReading :=
  indicatorLawFamily_adequate presentation.coarseReading
    (↑targetFull : Set (Fin 2))

/-- Canonical adequacy of the same indicator for the finer reading. -/
theorem indicatorFineAdequate :
    indicatorLaws.Adequate presentation.fineReading :=
  indicatorLawFamily_adequate_of_coarserThan presentation.coarseReading
    presentation.fineReading presentation.coarserThan
    (↑targetFull : Set (Fin 2))

/-- The source-generated true label of the full-subset indicator. -/
noncomputable def indicatorLabel : LawValueLabel indicatorLaws :=
  indicatorLawFamilyTrueLabel presentation.coarseReading
    (↑targetFull : Set (Fin 2)) targetFull_nonempty

/-- The generated label fiber is exactly the selected full target subset. -/
theorem indicatorFiber_eq_targetFull :
    labelValueFiber indicatorLaws presentation.coarseReading
        indicatorCoarseAdequate indicatorLabel =
      (↑targetFull : Set (Fin 2)) :=
  indicatorLawFamily_trueFiber_eq presentation.coarseReading
    (↑targetFull : Set (Fin 2)) targetFull_nonempty

/-- Law-block C2 at the generated label would transport back to the already
refuted actual full-subset C2 proposition. -/
theorem indicator_not_conditionC2At :
    ¬ presentation.toGeometry.ConditionC2At indicatorLaws
      indicatorCoarseAdequate indicatorFineAdequate indicatorLabel := by
  intro hC2
  apply not_conditionC2AtTargetSubset
  rw [← indicatorFiber_eq_targetFull]
  exact
    presentation.toGeometry.conditionC2AtTargetSubset_of_conditionC2At_labelValueFiber
      indicatorLaws indicatorCoarseAdequate indicatorFineAdequate
      indicatorLabel hC2

/-- The law-indexed C2 package fails by evaluation at the generated true
label. -/
theorem indicator_not_conditionC2 :
    ¬ presentation.toGeometry.ConditionC2 indicatorLaws
      indicatorCoarseAdequate indicatorFineAdequate := by
  intro hC2
  exact indicator_not_conditionC2At (hC2 indicatorLabel)

/-- The complete G-104 Condition C package fails for the full-subset indicator
by its C2 field. -/
theorem indicator_not_conditionC :
    ¬ presentation.toGeometry.ConditionC indicatorLaws
      indicatorCoarseAdequate indicatorFineAdequate := by
  intro hC
  exact indicator_not_conditionC2 hC.c2

/-! ## Nonzero H¹ on the same full failure subset -/

/-- The actual coarse full-target complex used for the literal quotient-H¹
nonvacuity argument. -/
abbrev coarseTargetFullComplex : ThreeCochainComplex ℚ :=
  coarseComplex targetFull

/-- The actual fine complex on the canonical preimage of the full target. -/
abbrev fineTargetFullComplex : ThreeCochainComplex ℚ :=
  fineComplex targetFull

/-- The raw coarse self-loop selected by the full target. -/
def coarseEdgeZero : presentation.CoarseEdgeIn targetFull :=
  ⟨(0 : Fin 2), by decide⟩

/-- The corresponding actual A-subnerve self-loop. -/
def coarseActualEdgeZero :
    presentation.coarseSupportedNerve.EdgeInTargetSubset
      (↑targetFull : Set (Fin 2)) :=
  presentation.coarseEdgeEquiv targetFull coarseEdgeZero

/-- Evaluation on the actual full-target self-loop. -/
def coarseTargetFullPeriod (cochain : coarseTargetFullComplex.C1) : ℚ :=
  cochain coarseActualEdgeZero

/-- Evaluation of the full-target period is literal evaluation at the named
self-loop. -/
@[simp]
theorem coarseTargetFullPeriod_apply (cochain : coarseTargetFullComplex.C1) :
    coarseTargetFullPeriod cochain = cochain coarseActualEdgeZero :=
  rfl

/-- Every coarse coboundary has zero loop period because the selected edge has
equal endpoints. -/
theorem coarseTargetFullPeriod_boundary_zero
    (cochain : coarseTargetFullComplex.C0) :
    coarseTargetFullPeriod (coarseTargetFullComplex.d0 cochain) = 0 := by
  rw [coarseTargetFullPeriod_apply,
    TargetSupportedNerve.targetSubsetComplex_d0_apply]
  have hloop :
      presentation.coarseSupportedNerve.targetSubsetEdgeRight
          (↑targetFull : Set (Fin 2)) coarseActualEdgeZero =
        presentation.coarseSupportedNerve.targetSubsetEdgeLeft
          (↑targetFull : Set (Fin 2)) coarseActualEdgeZero := by
    apply Subtype.ext
    rfl
  rw [hloop]
  ring

/-- Coefficient one on the actual coarse self-loop and zero on the interval
edge.  This explicit cochain is proof data, not a presentation field. -/
noncomputable def coarseTargetFullCochain : coarseTargetFullComplex.C1 := by
  classical
  exact fun edge => if edge = coarseActualEdgeZero then 1 else 0

/-- The displayed cochain is a cocycle because the coarse face type is empty. -/
theorem coarseTargetFullCochain_cocycle :
    coarseTargetFullComplex.d1 coarseTargetFullCochain = 0 :=
  coarse_d1_zero targetFull coarseTargetFullCochain

/-- The explicit self-loop cocycle packaged in the actual degree-one kernel. -/
noncomputable def coarseTargetFullCycle : LinearMap.ker coarseTargetFullComplex.d1 :=
  ⟨coarseTargetFullCochain, coarseTargetFullCochain_cocycle⟩

/-- The literal quotient-H¹ class of the explicit self-loop cocycle. -/
noncomputable def coarseTargetFullClass : coarseTargetFullComplex.H1 :=
  (LinearMap.range coarseTargetFullComplex.boundaryToCycles).mkQ
    coarseTargetFullCycle

/-- The displayed cocycle has unit period on the selected self-loop. -/
theorem coarseTargetFullPeriod_cycle :
    coarseTargetFullPeriod coarseTargetFullCycle.1 = 1 := by
  change coarseTargetFullCochain coarseActualEdgeZero = 1
  simp [coarseTargetFullCochain]

/-- The actual coarse full-target quotient class is nonzero: boundaries have
zero period while the explicit cycle has period one. -/
theorem coarseTargetFullClass_ne_zero : coarseTargetFullClass ≠ 0 := by
  intro hzero
  have hmem := (Submodule.Quotient.mk_eq_zero
    (LinearMap.range coarseTargetFullComplex.boundaryToCycles)).1 hzero
  rcases hmem with ⟨cochain, hcochain⟩
  have hperiod := congrArg
    (fun cycle : LinearMap.ker coarseTargetFullComplex.d1 =>
      coarseTargetFullPeriod cycle.1) hcochain
  change coarseTargetFullPeriod
      (coarseTargetFullComplex.boundaryToCycles cochain).1 =
    coarseTargetFullPeriod coarseTargetFullCycle.1 at hperiod
  rw [ThreeCochainComplex.boundaryToCycles_apply] at hperiod
  rw [coarseTargetFullPeriod_boundary_zero,
    coarseTargetFullPeriod_cycle] at hperiod
  exact zero_ne_one hperiod

/-- The coarse full-target H¹ space has positive finite dimension. -/
theorem targetFull_coarse_h1_pos :
    0 < Module.finrank ℚ coarseTargetFullComplex.H1 :=
  Module.finrank_pos_iff_exists_ne_zero.mpr
    ⟨coarseTargetFullClass, coarseTargetFullClass_ne_zero⟩

/-- The fine full-target class is the actual canonical image of the explicit
coarse class. -/
noncomputable def fineTargetFullClass : fineTargetFullComplex.H1 :=
  (presentation.toGeometry.aSubnerveComparisonHom
    (↑targetFull : Set (Fin 2))).h1Map coarseTargetFullClass

/-- The fine image class is nonzero by injectivity of the full-target actual
H¹ comparison. -/
theorem fineTargetFullClass_ne_zero : fineTargetFullClass ≠ 0 := by
  intro hzero
  apply coarseTargetFullClass_ne_zero
  apply (aSubnerveComparisonHom_h1Map_bijective targetFull).1
  simpa only [fineTargetFullClass, map_zero] using hzero

/-- The fine canonical-preimage H¹ space has positive finite dimension. -/
theorem targetFull_fine_h1_pos :
    0 < Module.finrank ℚ fineTargetFullComplex.H1 :=
  Module.finrank_pos_iff_exists_ne_zero.mpr
    ⟨fineTargetFullClass, fineTargetFullClass_ne_zero⟩

/-- Both sides of the same full-target comparison carrying the C2 failure
have nonzero H¹. -/
theorem targetFull_both_h1_pos :
    0 < Module.finrank ℚ coarseTargetFullComplex.H1 ∧
      0 < Module.finrank ℚ fineTargetFullComplex.H1 :=
  ⟨targetFull_coarse_h1_pos, targetFull_fine_h1_pos⟩

/-! ## Bounded R1 necessity conclusion -/

/-- Exact C2 non-necessity witness: the raw presentation is uniformly
invariant, fails C2 law-indexedly and on the actual full A-subnerve, fails
ConditionCAllA directly, and has nonzero H¹ on both sides of that same subset. -/
theorem c2_not_necessary :
    UniformPresentation presentation ∧
      ¬ presentation.toGeometry.ConditionC indicatorLaws
        indicatorCoarseAdequate indicatorFineAdequate ∧
      ¬ presentation.toGeometry.ConditionC2 indicatorLaws
        indicatorCoarseAdequate indicatorFineAdequate ∧
      ¬ presentation.toGeometry.ConditionC2AtTargetSubset
        (↑targetFull : Set (Fin 2)) ∧
      ¬ presentation.toGeometry.ConditionCAllA ∧
      0 < Module.finrank ℚ coarseTargetFullComplex.H1 ∧
      0 < Module.finrank ℚ fineTargetFullComplex.H1 :=
  ⟨uniformPresentation, indicator_not_conditionC, indicator_not_conditionC2,
    not_conditionC2AtTargetSubset, not_conditionCAllA,
    targetFull_coarse_h1_pos, targetFull_fine_h1_pos⟩

end R1ConditionC2Witness

end AAT.AG.ResolutionInvariance

#assert_standard_axioms_only AAT.AG.ResolutionInvariance
