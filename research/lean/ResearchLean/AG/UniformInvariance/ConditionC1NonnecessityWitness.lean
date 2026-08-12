import ResearchLean.AG.UniformInvariance.ConditionCAllABridge
import ResearchLean.AG.UniformInvariance.ConditionCAllAChecker
import ResearchLean.AG.UniformInvariance.UniformPresentationDecider
import Formal.Util.AssertStandardAxioms

/-!
# A uniform comparison outside the C1 locus

This module formalizes the exact `C1_not_necessary` fixture from the bounded
R1 necessity map for `G-107-aat-uniform-invariance-characterization`.  The
deterministic payload fixes the factor, target counts, nerves, supports, and
cell maps; the source and readings below are a canonical realization of that
factor.  The parent payload has SHA-256
`ff2d9fa12eb64bf343d3148f081e1164d4216d8548e53d90550eb53886dd359a`,
and the canonical name-free serializer recomputes SHA-256
`59e02ca26270c672ee5b96791f48742f3e7171f165d5c236f8c796626ed1310a`.

The coarse nerve has two charts and the fine nerve has three.  Each has one
self-loop at chart zero and no faces.  The reading factor is the proper map
`[0,0,1]`, while the chart map is `[0,1,1]`.  Over coarse chart one, fine
charts one and two are distinct isolated vertices of the endpoint fiber.
Thus C1 fails on the full target subset, where the common chart-zero loop
also gives nonzero H¹ on both sides.  All actual A-subnerve H¹ comparisons
nevertheless remain bijective.

The finite presentation stores only raw readings, incidence, support, partial
cell maps, and their well-formedness proofs.  It stores no factor, matrix,
rank, cohomology class, defect, condition result, checker result, or
uniformity certificate.  The R1 experiment is provenance for the table, not
a premise of any Lean theorem below.
-/

namespace AAT.AG.ResolutionInvariance

open CanonicalResolution Cohomology TwoPhase

namespace R1ConditionC1Witness

/-! ## Exact raw R1 presentation -/

/-- The proper coarse reading table `[0,0,1]`.  This fixture-local definition
is canonical raw R1 input to `presentation`, not a supplied factor or result. -/
def coarseRead (source : Fin 3) : Fin 2 :=
  if source = 2 then 1 else 0

/-- Coarse chart supports `[{0},{1}]`.  This fixture-local function is raw
support input and contains no C1 truth certificate. -/
def coarseChartSupport (chart : Fin 2) : Finset (Fin 2) :=
  if chart = 0 then {0} else {1}

/-- Fine chart supports `[{0,1},{2},{2}]`.  This fixture-local function is
raw support input for the disconnected chart fiber. -/
def fineChartSupport (chart : Fin 3) : Finset (Fin 3) :=
  if chart = 0 then {0, 1} else {2}

/-- Exact finite R1 C1 presentation.  Its fields are only finite readings,
self-loop incidence, empty face tables, supports, partial cell maps, and
well-formedness proofs; it stores no factor, path, H¹, rank, or result.

Position: existing C1 witness input reused by the Cycle 23 production-kernel
validation.  Its new explicit entry lists are complete coverage data derived
from the raw finite types, not reducer, observation, or expected-result fields. -/
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
  coarseChartEntries := List.finRange 2
  coarseChart_mem_coarseChartEntries := by intro chart; simp
  CoarseEdge := Fin 1
  coarseEdgeFintype := inferInstance
  coarseEdgeDecidableEq := inferInstance
  coarseEdgeEntries := List.finRange 1
  coarseEdge_mem_coarseEdgeEntries := by intro edge; simp
  CoarseFace := Fin 0
  coarseFaceFintype := inferInstance
  coarseFaceDecidableEq := inferInstance
  coarseFaceEntries := List.finRange 0
  coarseFace_mem_coarseFaceEntries := by intro face; exact nomatch face
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
  FineChart := Fin 3
  fineChartFintype := inferInstance
  fineChartDecidableEq := inferInstance
  fineChartEntries := List.finRange 3
  fineChart_mem_fineChartEntries := by intro chart; simp
  FineEdge := Fin 1
  fineEdgeFintype := inferInstance
  fineEdgeDecidableEq := inferInstance
  fineEdgeEntries := List.finRange 1
  fineEdge_mem_fineEdgeEntries := by intro edge; simp
  FineFace := Fin 0
  fineFaceFintype := inferInstance
  fineFaceDecidableEq := inferInstance
  fineFaceEntries := List.finRange 0
  fineFace_mem_fineFaceEntries := by intro face; exact nomatch face
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
  chartMap := fun chart => if chart = 0 then 0 else 1
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

/-! ## Direct C1 and all-subset-condition failure -/

/-- The full coarse target subset.  It is a registered C1-failure subset and,
unlike the smaller failure subset `{1}`, retains the common nonzero H¹ loop. -/
def targetFull : Finset (Fin 2) := Finset.univ

/-- The full target subset is nonempty. -/
theorem targetFull_nonempty :
    (↑targetFull : Set (Fin 2)).Nonempty :=
  ⟨0, by simp [targetFull]⟩

/-- Coarse chart one selected by the full target subset. -/
def coarseChartOne : presentation.CoarseChartIn targetFull :=
  ⟨(1 : Fin 2), by decide⟩

/-- The first isolated fine chart over coarse chart one. -/
def fineChartOne : presentation.FineChartIn targetFull :=
  ⟨(1 : Fin 3), by decide⟩

/-- The second isolated fine chart over coarse chart one. -/
def fineChartTwo : presentation.FineChartIn targetFull :=
  ⟨(2 : Fin 3), by decide⟩

/-- Fine chart one maps to the displayed coarse chart in the raw selected
table. -/
theorem chartMapIn_fineChartOne :
    presentation.chartMapIn targetFull fineChartOne = coarseChartOne := by
  apply Subtype.ext
  rw [presentation.chartMapIn_coe]
  rfl

/-- Fine chart two maps to the same displayed coarse chart. -/
theorem chartMapIn_fineChartTwo :
    presentation.chartMapIn targetFull fineChartTwo = coarseChartOne := by
  apply Subtype.ext
  rw [presentation.chartMapIn_coe]
  rfl

/-- No selected fine edge lies in the endpoint fiber over coarse chart one:
the sole raw edge has both endpoints at fine chart zero, whose image is coarse
chart zero. -/
theorem no_rawFiberEdge (edge : presentation.FineEdgeIn targetFull) :
    ¬ presentation.rawFiberEdge targetFull coarseChartOne edge := by
  intro hfiber
  have hleft := congrArg Subtype.val hfiber.1
  simp only [presentation.chartMapIn_coe,
    presentation.fineEdgeLeftIn_coe] at hleft
  have hval := congrArg Fin.val hleft
  change (0 : Nat) = 1 at hval
  omega

/-- Raw fiber adjacency over coarse chart one is empty, independently of the
chosen pair of selected fine charts. -/
theorem no_rawFiberAdjacent
    (left right : presentation.FineChartIn targetFull) :
    ¬ presentation.rawFiberAdjacent targetFull coarseChartOne left right := by
  rintro ⟨edge, hfiber, _hendpoints⟩
  exact no_rawFiberEdge edge hfiber

/-- The executable fiber graph has no edge leaving fine chart one. -/
theorem no_fiberGraph_adjacent
    (other : presentation.FineChartIn targetFull) :
    ¬ (presentation.fiberGraph targetFull coarseChartOne).Adj
      fineChartOne other := by
  rw [presentation.fiberGraph_adj_iff]
  rintro ⟨_hne, hadjacent⟩
  exact hadjacent.elim
    (no_rawFiberAdjacent fineChartOne other)
    (no_rawFiberAdjacent other fineChartOne)

/-- The two displayed fine charts are not connected in the raw endpoint-fiber
graph.  The finite decision inspects the sole self-loop at chart zero. -/
theorem not_fiberGraph_reachable :
    ¬ (presentation.fiberGraph targetFull coarseChartOne).Reachable
      fineChartOne fineChartTwo := by
  rw [SimpleGraph.reachable_iff_reflTransGen]
  intro hpath
  have hequal : fineChartTwo = fineChartOne :=
    (Relation.reflTransGen_iff_eq no_fiberGraph_adjacent).mp hpath
  have hval := congrArg Subtype.val hequal
  have hnat := congrArg Fin.val hval
  norm_num [fineChartOne, fineChartTwo] at hnat

/-- Raw C1 fails directly at the full target subset and the named pair of
isolated charts. -/
theorem not_rawConditionC1At :
    ¬ presentation.RawConditionC1At targetFull := by
  intro hC1
  exact not_fiberGraph_reachable
    ((hC1 coarseChartOne).2 fineChartOne fineChartTwo
      chartMapIn_fineChartOne chartMapIn_fineChartTwo)

/-- The executable raw C1 checker evaluates to false on the same full target
subset. -/
theorem conditionC1AtTargetSubsetCheck_false :
    presentation.conditionC1AtTargetSubsetCheck targetFull = false := by
  apply Bool.eq_false_of_not_eq_true
  intro htrue
  exact not_rawConditionC1At (of_decide_eq_true htrue)

/-- Semantic C1 fails on the actual full A-subnerve under the canonical
raw/semantic chart equivalences. -/
theorem not_conditionC1AtTargetSubset :
    ¬ presentation.toGeometry.ConditionC1AtTargetSubset
      (↑targetFull : Set (Fin 2)) := by
  intro hC1
  exact not_rawConditionC1At
    ((presentation.rawConditionC1At_iff_conditionC1AtTargetSubset
      targetFull).mpr hC1)

/-- `ConditionCAllA` fails directly at its C1 projection on the named nonempty
full subset. -/
theorem not_conditionCAllA :
    ¬ presentation.toGeometry.ConditionCAllA := by
  intro hAllA
  exact not_conditionC1AtTargetSubset
    (hAllA.conditionC1At presentation.toGeometry
      (↑targetFull : Set (Fin 2)) targetFull_nonempty)

/-- The generic all-subset Condition C checker is false because its semantic
soundness would contradict the direct full-subset C1 obstruction. -/
theorem conditionCAllACheck_false :
    presentation.conditionCAllACheck = false := by
  apply Bool.eq_false_of_not_eq_true
  intro htrue
  exact not_conditionCAllA
    (presentation.conditionCAllACheck_eq_true_iff.mp htrue)

/-! ## Law-indexed C1 failure on the same label fiber -/

/-- The canonical Boolean indicator family of the full coarse target subset.
It is constant true, as the fixed GOAL permits; nonvacuity instead comes from
the proper factor, two isolated charts, and nonzero H¹ on this same fiber. -/
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

/-- Law-block C1 at the generated label would transport back to the already
refuted actual full-subset C1 proposition. -/
theorem indicator_not_conditionC1At :
    ¬ presentation.toGeometry.ConditionC1At indicatorLaws
      indicatorCoarseAdequate indicatorFineAdequate indicatorLabel := by
  intro hC1
  apply not_conditionC1AtTargetSubset
  rw [← indicatorFiber_eq_targetFull]
  exact
    presentation.toGeometry.conditionC1AtTargetSubset_of_conditionC1At_labelValueFiber
        indicatorLaws indicatorCoarseAdequate indicatorFineAdequate
        indicatorLabel hC1

/-- The law-indexed C1 package fails by evaluation at the generated true
label. -/
theorem indicator_not_conditionC1 :
    ¬ presentation.toGeometry.ConditionC1 indicatorLaws
      indicatorCoarseAdequate indicatorFineAdequate := by
  intro hC1
  exact indicator_not_conditionC1At (hC1 indicatorLabel)

/-- The complete G-104 Condition C package fails for the full-subset indicator
by its C1 field. -/
theorem indicator_not_conditionC :
    ¬ presentation.toGeometry.ConditionC indicatorLaws
      indicatorCoarseAdequate indicatorFineAdequate := by
  intro hC
  exact indicator_not_conditionC1 hC.c1
/-! ## Nonzero H¹ on the block meeting the C1 failure subset -/

/-- The actual coarse full-target complex, named for the literal quotient-H¹
nonvacuity argument. -/
abbrev coarseTargetFullComplex : ThreeCochainComplex ℚ :=
  coarseComplex targetFull

/-- The actual fine complex on the canonical preimage of the full target. -/
abbrev fineTargetFullComplex : ThreeCochainComplex ℚ :=
  fineComplex targetFull

/-- The unique raw coarse self-loop selected by the full target, derived from the
raw selection predicate. -/
def coarseEdgeZero : presentation.CoarseEdgeIn targetFull :=
  ⟨(0 : Fin 1), by decide⟩

/-- The corresponding actual A-subnerve self-loop, obtained through the
owner-provided raw/semantic edge equivalence. -/
def coarseActualEdgeZero :
    presentation.coarseSupportedNerve.EdgeInTargetSubset
      (↑targetFull : Set (Fin 2)) :=
  presentation.coarseEdgeEquiv targetFull coarseEdgeZero

/-- Evaluation on the actual full-target self-loop.  This linear functional
detects the explicit quotient-H¹ class. -/
def coarseTargetFullPeriod (cochain : coarseTargetFullComplex.C1) : ℚ :=
  cochain coarseActualEdgeZero

/-- Evaluation of the full-target period functional is literal evaluation at
the named actual self-loop.  This fixture API lets later proofs avoid
expanding the functional definition. -/
@[simp]
theorem coarseTargetFullPeriod_apply (cochain : coarseTargetFullComplex.C1) :
    coarseTargetFullPeriod cochain = cochain coarseActualEdgeZero :=
  rfl

/-- Every coarse coboundary has zero loop period, because the selected edge
has equal endpoints. -/
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

/-- Constant coefficient one on the actual coarse self-loop.  This explicit
cochain is proof data, not a presentation field. -/
def coarseTargetFullCochain : coarseTargetFullComplex.C1 :=
  fun _ => 1

/-- The constant loop cochain is a cocycle because the coarse face type is
empty. -/
theorem coarseTargetFullCochain_cocycle :
    coarseTargetFullComplex.d1 coarseTargetFullCochain = 0 :=
  coarse_d1_zero targetFull coarseTargetFullCochain

/-- The explicit loop cocycle packaged in the actual degree-one kernel. -/
def coarseTargetFullCycle : LinearMap.ker coarseTargetFullComplex.d1 :=
  ⟨coarseTargetFullCochain, coarseTargetFullCochain_cocycle⟩

/-- The literal quotient-H¹ class of the explicit self-loop cocycle. -/
def coarseTargetFullClass : coarseTargetFullComplex.H1 :=
  (LinearMap.range coarseTargetFullComplex.boundaryToCycles).mkQ
    coarseTargetFullCycle

/-- The displayed cocycle has unit period on the selected self-loop. -/
theorem coarseTargetFullPeriod_cycle :
    coarseTargetFullPeriod coarseTargetFullCycle.1 = 1 := by
  rfl

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

/-- The coarse full-target H¹ space has positive finite dimension, witnessed
by the explicit nonzero quotient class. -/
theorem targetFull_coarse_h1_pos :
    0 < Module.finrank ℚ coarseTargetFullComplex.H1 :=
  Module.finrank_pos_iff_exists_ne_zero.mpr
    ⟨coarseTargetFullClass, coarseTargetFullClass_ne_zero⟩

/-- The fine full-target class is the image of the explicit coarse class under
the actual canonical H¹ comparison map. -/
def fineTargetFullClass : fineTargetFullComplex.H1 :=
  (presentation.toGeometry.aSubnerveComparisonHom
    (↑targetFull : Set (Fin 2))).h1Map coarseTargetFullClass

/-- The actual fine image class is nonzero by injectivity of the full-target
canonical H¹ comparison. -/
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

/-- Both sides of the same full-target comparison meeting the C1 failure subset
have nonzero H¹. -/
theorem targetFull_both_h1_pos :
    0 < Module.finrank ℚ coarseTargetFullComplex.H1 ∧
      0 < Module.finrank ℚ fineTargetFullComplex.H1 :=
  ⟨targetFull_coarse_h1_pos, targetFull_fine_h1_pos⟩

/-! ## Bounded R1 necessity conclusion -/

/-- Exact C1 non-necessity witness: the raw presentation is uniformly
invariant, fails C1 both law-indexedly and on the actual full A-subnerve,
fails ConditionCAllA directly, and has nonzero H¹ on both sides of that
same failure subset.  Every component is a closed theorem above. -/
theorem c1_not_necessary :
    UniformPresentation presentation ∧
      ¬ presentation.toGeometry.ConditionC indicatorLaws
        indicatorCoarseAdequate indicatorFineAdequate ∧
      ¬ presentation.toGeometry.ConditionC1 indicatorLaws
        indicatorCoarseAdequate indicatorFineAdequate ∧
      ¬ presentation.toGeometry.ConditionC1AtTargetSubset
        (↑targetFull : Set (Fin 2)) ∧
      ¬ presentation.toGeometry.ConditionCAllA ∧
      0 < Module.finrank ℚ coarseTargetFullComplex.H1 ∧
      0 < Module.finrank ℚ fineTargetFullComplex.H1 :=
  ⟨uniformPresentation, indicator_not_conditionC, indicator_not_conditionC1,
    not_conditionC1AtTargetSubset, not_conditionCAllA,
    targetFull_coarse_h1_pos, targetFull_fine_h1_pos⟩

end R1ConditionC1Witness

end AAT.AG.ResolutionInvariance

#assert_standard_axioms_only AAT.AG.ResolutionInvariance
