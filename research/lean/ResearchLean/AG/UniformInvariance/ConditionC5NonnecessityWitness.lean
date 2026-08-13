import ResearchLean.AG.UniformInvariance.ConditionCAllAChecker
import ResearchLean.AG.UniformInvariance.UniformPresentationDecider
import Formal.Util.AssertStandardAxioms

/-!
# A uniform comparison outside the C5 locus

This module formalizes the exact `C5_not_necessary` fixture from the bounded
R1 necessity map for `G-107-aat-uniform-invariance-characterization`.  The
parent R1 payload has SHA-256
`ff2d9fa12eb64bf343d3148f081e1164d4216d8548e53d90550eb53886dd359a`,
and the canonical name-free serializer recomputes SHA-256
`a1907afb86e6a570e244676e48358f9d21a87077ee868b09308177aef04b7ca4`.

The coarse nerve has two self-loops and one repeated face on the chart-one
loop.  The fine nerve has the same chart-zero loop, two distinct chart-one
loops, and one repeated face on each of them.  Both chart-one fine loops map
to the single chart-one coarse loop, so whole-nerve lift uniqueness C5 fails.
The two fine face equations kill the two duplicate coefficients separately,
while the coarse face kills their common image coefficient.  Consequently
the actual comparison remains bijective on every target subset.  On the full
subset, the common chart-zero loop supplies nonzero H¹ on both sides and the
duplicate pair has common K1 support mapping into that same subset.

The experiment payload directly fixes the factor, target counts, nerves,
supports, and cell maps.  The `Fin 3` source and raw reading tables below are
the canonical finite realization of that factor.  The presentation stores no
factor, duplicate-lift certificate, matrix, rank, cohomology class, defect,
condition result, checker result, or uniformity certificate.
-/

namespace AAT.AG.ResolutionInvariance

open CanonicalResolution Cohomology TwoPhase

namespace R1ConditionC5Witness

/-! ## Exact raw R1 presentation -/

/-- The proper coarse reading table `[0,0,1]`, used as raw presentation input. -/
def coarseRead (source : Fin 3) : Fin 2 :=
  if source = 2 then 1 else 0

/-- Coarse chart supports `[{0},{1}]`, containing no C5 result. -/
def coarseChartSupport (chart : Fin 2) : Finset (Fin 2) :=
  if chart = 0 then {0} else {1}

/-- Fine chart supports `[{0,1},{2}]`, realizing the proper reading factor. -/
def fineChartSupport (chart : Fin 2) : Finset (Fin 3) :=
  if chart = 0 then {0, 1} else {2}

/-- The two chart-one fine loops have indices one and two. -/
def fineEdgeChart (edge : Fin 3) : Fin 2 :=
  if edge = 0 then 0 else 1

/-- Fine face zero is repeated on edge one and face one on edge two. -/
def fineFaceEdge (face : Fin 2) : Fin 3 :=
  if face = 0 then 1 else 2

/-- Both duplicate chart-one fine loops map to coarse edge one. -/
def rawEdgeMap (edge : Fin 3) : Option (Fin 2) :=
  some (fineEdgeChart edge)

/-- Exact finite R1 C5 presentation.  Its fields are only raw finite geometry
and well-formedness proofs; no uniqueness or cohomology answer is stored.

Position: existing C5 witness input reused by the Cycle 23 production-kernel
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
  CoarseEdge := Fin 2
  coarseEdgeFintype := inferInstance
  coarseEdgeDecidableEq := inferInstance
  coarseEdgeEntries := List.finRange 2
  coarseEdge_mem_coarseEdgeEntries := by intro edge; simp
  CoarseFace := Fin 1
  coarseFaceFintype := inferInstance
  coarseFaceDecidableEq := inferInstance
  coarseFaceEntries := List.finRange 1
  coarseFace_mem_coarseFaceEntries := by intro face; simp
  coarseEdgeLeft := id
  coarseEdgeRight := id
  coarseFaceEdge0 := fun _ => 1
  coarseFaceEdge1 := fun _ => 1
  coarseFaceEdge2 := fun _ => 1
  coarseFaceEdge0_left := by intro face; rfl
  coarseFaceEdge0_right := by intro face; rfl
  coarseFaceEdge1_right := by intro face; rfl
  coarseChartSupport := coarseChartSupport
  coarseChartSupport_nonempty := by
    intro chart
    fin_cases chart <;> simp [coarseChartSupport]
  FineChart := Fin 2
  fineChartFintype := inferInstance
  fineChartDecidableEq := inferInstance
  fineChartEntries := List.finRange 2
  fineChart_mem_fineChartEntries := by intro chart; simp
  FineEdge := Fin 3
  fineEdgeFintype := inferInstance
  fineEdgeDecidableEq := inferInstance
  fineEdgeEntries := List.finRange 3
  fineEdge_mem_fineEdgeEntries := by intro edge; simp
  FineFace := Fin 2
  fineFaceFintype := inferInstance
  fineFaceDecidableEq := inferInstance
  fineFaceEntries := List.finRange 2
  fineFace_mem_fineFaceEntries := by intro face; simp
  fineEdgeLeft := fineEdgeChart
  fineEdgeRight := fineEdgeChart
  fineFaceEdge0 := fineFaceEdge
  fineFaceEdge1 := fineFaceEdge
  fineFaceEdge2 := fineFaceEdge
  fineFaceEdge0_left := by intro face; rfl
  fineFaceEdge0_right := by intro face; rfl
  fineFaceEdge1_right := by intro face; rfl
  fineChartSupport := fineChartSupport
  fineChartSupport_nonempty := by
    intro chart
    fin_cases chart <;> simp [fineChartSupport]
  chartMap := id
  edgeMap := rawEdgeMap
  faceMap := fun _ => some 0
  edge_some_left := by
    intro fineEdge coarseEdge hmap
    fin_cases fineEdge <;> fin_cases coarseEdge <;>
      simp [rawEdgeMap, fineEdgeChart] at hmap ⊢
  edge_some_right := by
    intro fineEdge coarseEdge hmap
    fin_cases fineEdge <;> fin_cases coarseEdge <;>
      simp [rawEdgeMap, fineEdgeChart] at hmap ⊢
  edge_none_fiber := by intro fineEdge hmap; simp [rawEdgeMap] at hmap
  face_some_edge0 := by
    intro fineFace coarseFace hmap
    fin_cases fineFace <;> fin_cases coarseFace <;>
      simp [fineFaceEdge, rawEdgeMap, fineEdgeChart] at hmap ⊢
  face_some_edge1 := by
    intro fineFace coarseFace hmap
    fin_cases fineFace <;> fin_cases coarseFace <;>
      simp [fineFaceEdge, rawEdgeMap, fineEdgeChart] at hmap ⊢
  face_some_edge2 := by
    intro fineFace coarseFace hmap
    fin_cases fineFace <;> fin_cases coarseFace <;>
      simp [fineFaceEdge, rawEdgeMap, fineEdgeChart] at hmap ⊢
  face_none_edge0 := by intro fineFace hmap; simp at hmap
  face_none_edge1 := by intro fineFace hmap; simp at hmap
  face_none_edge2 := by intro fineFace hmap; simp at hmap
  chartSupport_compatible_source := by
    intro fineChart source hsource
    fin_cases fineChart <;> fin_cases source <;>
      simp [fineChartSupport, coarseChartSupport, coarseRead] at hsource ⊢

/-! ## Canonical factor and selected raw cells -/

/-- The executable factor is `[0,0,1]`, generated from the raw readings. -/
theorem computedFactor_eq_coarseRead : presentation.computedFactor = coarseRead := by
  funext target
  fin_cases target <;> decide

/-- The semantic canonical factor is the same table by generic uniqueness. -/
theorem comparisonFactor_eq_coarseRead :
    comparisonFactor presentation.coarseReading presentation.fineReading
      presentation.coarserThan = coarseRead := by
  rw [← presentation.computedFactor_eq_comparisonFactor]
  exact computedFactor_eq_coarseRead

/-- Coarse edge zero is selected exactly when target zero is selected. -/
theorem coarseEdgeZero_mem_iff_zero_mem (A : Finset (Fin 2)) :
    (0 : Fin 2) ∈ presentation.coarseEdgesIn A ↔ (0 : Fin 2) ∈ A := by
  rw [presentation.mem_coarseEdgesIn_iff_raw]
  simp only [presentation.mem_coarseEdgeSupportFinset_iff_raw]
  simp [presentation, coarseChartSupport]

/-- Coarse edge one is selected exactly when target one is selected. -/
theorem coarseEdgeOne_mem_iff_one_mem (A : Finset (Fin 2)) :
    (1 : Fin 2) ∈ presentation.coarseEdgesIn A ↔ (1 : Fin 2) ∈ A := by
  rw [presentation.mem_coarseEdgesIn_iff_raw]
  simp only [presentation.mem_coarseEdgeSupportFinset_iff_raw]
  simp [presentation, coarseChartSupport]

/-- Fine edge zero is selected exactly when coarse target zero is selected. -/
theorem fineEdgeZero_mem_iff_zero_mem (A : Finset (Fin 2)) :
    (0 : Fin 3) ∈ presentation.fineEdgesIn A ↔ (0 : Fin 2) ∈ A := by
  rw [presentation.mem_fineEdgesIn_iff_raw, computedFactor_eq_coarseRead]
  simp only [presentation.mem_fineEdgeSupportFinset_iff_raw]
  simp [presentation, fineChartSupport, fineEdgeChart, coarseRead]

/-- Fine edge one is selected exactly when coarse target one is selected. -/
theorem fineEdgeOne_mem_iff_one_mem (A : Finset (Fin 2)) :
    (1 : Fin 3) ∈ presentation.fineEdgesIn A ↔ (1 : Fin 2) ∈ A := by
  rw [presentation.mem_fineEdgesIn_iff_raw, computedFactor_eq_coarseRead]
  simp only [presentation.mem_fineEdgeSupportFinset_iff_raw]
  simp [presentation, fineChartSupport, fineEdgeChart, coarseRead]

/-- Fine edge two is selected exactly when coarse target one is selected. -/
theorem fineEdgeTwo_mem_iff_one_mem (A : Finset (Fin 2)) :
    (2 : Fin 3) ∈ presentation.fineEdgesIn A ↔ (1 : Fin 2) ∈ A := by
  rw [presentation.mem_fineEdgesIn_iff_raw, computedFactor_eq_coarseRead]
  simp only [presentation.mem_fineEdgeSupportFinset_iff_raw]
  simp [presentation, fineChartSupport, fineEdgeChart, coarseRead]

/-- Fine face zero is selected exactly when coarse target one is selected. -/
theorem fineFaceZero_mem_iff_one_mem (A : Finset (Fin 2)) :
    (0 : Fin 2) ∈ presentation.fineFacesIn A ↔ (1 : Fin 2) ∈ A := by
  rw [presentation.mem_fineFacesIn_iff_raw, computedFactor_eq_coarseRead]
  simp only [presentation.mem_fineFaceSupportFinset_iff_raw,
    presentation.mem_fineEdgeSupportFinset_iff_raw]
  simp [presentation, fineChartSupport, fineFaceEdge, fineEdgeChart, coarseRead]

/-- Fine face one is selected exactly when coarse target one is selected. -/
theorem fineFaceOne_mem_iff_one_mem (A : Finset (Fin 2)) :
    (1 : Fin 2) ∈ presentation.fineFacesIn A ↔ (1 : Fin 2) ∈ A := by
  rw [presentation.mem_fineFacesIn_iff_raw, computedFactor_eq_coarseRead]
  simp only [presentation.mem_fineFaceSupportFinset_iff_raw,
    presentation.mem_fineEdgeSupportFinset_iff_raw]
  simp [presentation, fineChartSupport, fineFaceEdge, fineEdgeChart, coarseRead]

/-! ## Raw degree-one comparison -/

/-- A canonical selected fine lift of each selected coarse edge.  Edge one
chooses the first of the duplicate raw lifts; this is proof-local data. -/
def selectedFineEdgeOfCoarse (A : Finset (Fin 2))
    (edge : presentation.CoarseEdgeIn A) : presentation.FineEdgeIn A :=
  if hzero : (show Fin 2 from edge.1) = 0 then
    ⟨(0 : Fin 3), (fineEdgeZero_mem_iff_zero_mem A).2
      ((coarseEdgeZero_mem_iff_zero_mem A).1 (hzero ▸ edge.2))⟩
  else
    ⟨(1 : Fin 3), (fineEdgeOne_mem_iff_one_mem A).2
      ((coarseEdgeOne_mem_iff_one_mem A).1
        ((show (show Fin 2 from edge.1) = 1 by omega) ▸ edge.2))⟩

/-- The selected coarse image of a selected fine edge, generated by the raw
partial edge map. -/
def selectedCoarseEdgeOfFine (A : Finset (Fin 2))
    (edge : presentation.FineEdgeIn A) : presentation.CoarseEdgeIn A :=
  if hzero : (show Fin 3 from edge.1) = 0 then
    ⟨(0 : Fin 2), (coarseEdgeZero_mem_iff_zero_mem A).2
      ((fineEdgeZero_mem_iff_zero_mem A).1 (hzero ▸ edge.2))⟩
  else
    ⟨(1 : Fin 2), (coarseEdgeOne_mem_iff_one_mem A).2 (by
      have hcases : (show Fin 3 from edge.1) = 1 ∨
          (show Fin 3 from edge.1) = 2 := by omega
      rcases hcases with hone | htwo
      · exact (fineEdgeOne_mem_iff_one_mem A).1 (hone ▸ edge.2)
      · exact (fineEdgeTwo_mem_iff_one_mem A).1 (htwo ▸ edge.2))⟩

/-- The selected raw edge map sends each fine edge to its generated selected
coarse image. -/
theorem edgeMapOptionIn_eq_some_selectedCoarse (A : Finset (Fin 2))
    (edge : presentation.FineEdgeIn A) :
    presentation.edgeMapOptionIn A edge =
      some (selectedCoarseEdgeOfFine A edge) := by
  apply (presentation.edgeMapOptionIn_eq_some_iff A edge _).2
  by_cases hzero : (show Fin 3 from edge.1) = 0
  · simp [selectedCoarseEdgeOfFine, hzero, presentation, rawEdgeMap,
      fineEdgeChart]
  · have hcases : (show Fin 3 from edge.1) = 1 ∨
        (show Fin 3 from edge.1) = 2 := by omega
    rcases hcases with hone | htwo
    · simp [selectedCoarseEdgeOfFine, presentation, rawEdgeMap,
        fineEdgeChart, hone]
    · simp [selectedCoarseEdgeOfFine, presentation, rawEdgeMap,
        fineEdgeChart, htwo]

/-- Choosing a fine lift and mapping it back recovers the selected coarse
edge, so the raw pullback is injective on all cochains. -/
theorem selectedCoarseEdgeOfFine_selectedFineEdgeOfCoarse
    (A : Finset (Fin 2)) (edge : presentation.CoarseEdgeIn A) :
    selectedCoarseEdgeOfFine A (selectedFineEdgeOfCoarse A edge) = edge := by
  apply Subtype.ext
  by_cases hzero : (show Fin 2 from edge.1) = 0
  · simp [selectedFineEdgeOfCoarse, selectedCoarseEdgeOfFine, hzero]
  · have hone : (show Fin 2 from edge.1) = 1 := by omega
    simp [selectedFineEdgeOfCoarse, selectedCoarseEdgeOfFine, hone]

/-- Project a raw fine edge cochain to the chosen lift of each coarse edge. -/
def rawCoarseProjection (A : Finset (Fin 2))
    (cochain : presentation.FineEdgeIn A → ℚ) :
    presentation.CoarseEdgeIn A → ℚ :=
  fun edge => cochain (selectedFineEdgeOfCoarse A edge)

/-- Raw projection is a left inverse to degree-one pullback. -/
theorem rawCoarseProjection_edgePullback (A : Finset (Fin 2))
    (cochain : presentation.CoarseEdgeIn A → ℚ) :
    rawCoarseProjection A
      (presentation.edgePullback1LinearMap A cochain) = cochain := by
  funext edge
  rw [rawCoarseProjection, presentation.edgePullback1LinearMap_apply,
    edgeMapOptionIn_eq_some_selectedCoarse]
  simp only [Option.elim_some]
  rw [selectedCoarseEdgeOfFine_selectedFineEdgeOfCoarse]

/-- Raw degree-one pullback is injective on every selected target subset. -/
theorem edgePullback1LinearMap_injective (A : Finset (Fin 2)) :
    Function.Injective (presentation.edgePullback1LinearMap A) := by
  intro left right hequal
  have := congrArg (rawCoarseProjection A) hequal
  simpa only [rawCoarseProjection_edgePullback] using this

/-! ## Raw repeated-face cocycle control -/

/-- The coefficient of a selected fine edge with nonzero index vanishes in
every fine raw cocycle, because its own repeated face has that boundary. -/
theorem fine_nonzero_edge_eq_zero_of_d1_eq_zero
    (A : Finset (Fin 2))
    (cochain : presentation.FineEdgeIn A → ℚ)
    (hcocycle : presentation.fineD1LinearMap A cochain = 0)
    (edge : presentation.FineEdgeIn A)
    (hnonzero : (show Fin 3 from edge.1) ≠ 0) :
    cochain edge = 0 := by
  have hcases : (show Fin 3 from edge.1) = 1 ∨
      (show Fin 3 from edge.1) = 2 := by omega
  rcases hcases with hone | htwo
  · have honeMem : (1 : Fin 2) ∈ A :=
      (fineEdgeOne_mem_iff_one_mem A).1 (hone ▸ edge.2)
    let face : presentation.FineFaceIn A :=
      ⟨(0 : Fin 2), (fineFaceZero_mem_iff_one_mem A).2 honeMem⟩
    have hvalue := congrFun hcocycle face
    rw [presentation.fineD1LinearMap_apply] at hvalue
    simp only [Pi.zero_apply] at hvalue
    have hedge0 : presentation.fineFaceEdge0In A face = edge := by
      apply Subtype.ext
      change (1 : Fin 3) = edge.1
      exact hone.symm
    have hedge1 : presentation.fineFaceEdge1In A face = edge := by
      apply Subtype.ext
      change (1 : Fin 3) = edge.1
      exact hone.symm
    have hedge2 : presentation.fineFaceEdge2In A face = edge := by
      apply Subtype.ext
      change (1 : Fin 3) = edge.1
      exact hone.symm
    simpa [hedge0, hedge1, hedge2] using hvalue
  · have htwoMem : (1 : Fin 2) ∈ A :=
      (fineEdgeTwo_mem_iff_one_mem A).1 (htwo ▸ edge.2)
    let face : presentation.FineFaceIn A :=
      ⟨(1 : Fin 2), (fineFaceOne_mem_iff_one_mem A).2 htwoMem⟩
    have hvalue := congrFun hcocycle face
    rw [presentation.fineD1LinearMap_apply] at hvalue
    simp only [Pi.zero_apply] at hvalue
    have hedge0 : presentation.fineFaceEdge0In A face = edge := by
      apply Subtype.ext
      change (2 : Fin 3) = edge.1
      exact htwo.symm
    have hedge1 : presentation.fineFaceEdge1In A face = edge := by
      apply Subtype.ext
      change (2 : Fin 3) = edge.1
      exact htwo.symm
    have hedge2 : presentation.fineFaceEdge2In A face = edge := by
      apply Subtype.ext
      change (2 : Fin 3) = edge.1
      exact htwo.symm
    simpa [hedge0, hedge1, hedge2] using hvalue

/-- On fine cocycles, projection followed by raw pullback is the identity.
The only non-chosen duplicate lift has coefficient zero by its face equation. -/
theorem edgePullback1_rawCoarseProjection_of_cycle
    (A : Finset (Fin 2))
    (cochain : presentation.FineEdgeIn A → ℚ)
    (hcocycle : presentation.fineD1LinearMap A cochain = 0) :
    presentation.edgePullback1LinearMap A
        (rawCoarseProjection A cochain) = cochain := by
  funext edge
  rw [presentation.edgePullback1LinearMap_apply,
    edgeMapOptionIn_eq_some_selectedCoarse]
  simp only [Option.elim_some, rawCoarseProjection]
  by_cases hzero : (show Fin 3 from edge.1) = 0
  · congr 1
    apply Subtype.ext
    simp [selectedCoarseEdgeOfFine, selectedFineEdgeOfCoarse, hzero]
  · have hleft : cochain
        (selectedFineEdgeOfCoarse A (selectedCoarseEdgeOfFine A edge)) = 0 := by
      apply fine_nonzero_edge_eq_zero_of_d1_eq_zero A cochain hcocycle
      simp [selectedCoarseEdgeOfFine, selectedFineEdgeOfCoarse, hzero]
    have hright : cochain edge = 0 :=
      fine_nonzero_edge_eq_zero_of_d1_eq_zero A cochain hcocycle edge hzero
    rw [hleft, hright]

/-- Projecting a fine raw cocycle gives a coarse raw cocycle.  The coarse
repeated-face equation is the equation on the chosen first duplicate lift. -/
theorem coarseD1_rawCoarseProjection_eq_zero
    (A : Finset (Fin 2))
    (cochain : presentation.FineEdgeIn A → ℚ)
    (hcocycle : presentation.fineD1LinearMap A cochain = 0) :
    presentation.coarseD1LinearMap A
        (rawCoarseProjection A cochain) = 0 := by
  funext face
  simp only [Pi.zero_apply]
  rw [presentation.coarseD1LinearMap_apply]
  have hedge0 :
      (show Fin 2 from (presentation.coarseFaceEdge0In A face).1) = 1 := rfl
  have hzero : rawCoarseProjection A cochain
      (presentation.coarseFaceEdge0In A face) = 0 := by
    apply fine_nonzero_edge_eq_zero_of_d1_eq_zero A cochain hcocycle
    simp [selectedFineEdgeOfCoarse, hedge0]
  have hedge1 : presentation.coarseFaceEdge1In A face =
      presentation.coarseFaceEdge0In A face := Subtype.ext rfl
  have hedge2 : presentation.coarseFaceEdge2In A face =
      presentation.coarseFaceEdge0In A face := Subtype.ext rfl
  rw [hedge1, hedge2, hzero]
  norm_num

/-! ## Actual quotient-H¹ comparison on every target subset -/

/-- The actual coarse constant-rational A-subnerve complex. -/
abbrev coarseComplex (A : Finset (Fin 2)) : ThreeCochainComplex ℚ :=
  presentation.coarseSupportedNerve.targetSubsetComplex (↑A : Set (Fin 2))

/-- The actual fine complex on the canonical preimage of `A`. -/
abbrev fineComplex (A : Finset (Fin 2)) : ThreeCochainComplex ℚ :=
  presentation.fineSupportedNerve.targetSubsetComplex
    (presentation.canonicalFinePreimage A)

/-- Every fine degree-zero boundary vanishes because all fine edges are
self-loops. -/
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

/-- The actual canonical H¹ comparison is bijective on every target subset.
Injectivity uses raw pullback injectivity and zero fine boundaries;
surjectivity projects a fine cocycle and uses both duplicate face equations. -/
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
    have hraw : rawDifference = 0 :=
      edgePullback1LinearMap_injective A hpullback
    have hdiff : leftCycle.1 - rightCycle.1 = 0 := by
      apply (presentation.coarseEdgeCochainEquiv A).injective
      simpa only [rawDifference, map_zero] using hraw
    have hcycles : leftCycle = rightCycle := by
      apply Subtype.ext
      exact sub_eq_zero.mp hdiff
    rw [hcycles]
  · intro targetClass
    obtain ⟨targetCycle, rfl⟩ :=
      (LinearMap.range (fineComplex A).boundaryToCycles).mkQ_surjective targetClass
    let rawTarget : presentation.FineEdgeIn A → ℚ :=
      presentation.fineEdgeCochainEquiv A targetCycle.1
    have hrawTargetCycle :
        presentation.fineD1LinearMap A rawTarget = 0 := by
      have hcomm := presentation.fineD1_commutes A targetCycle.1
      change presentation.fineD1LinearMap A rawTarget =
        presentation.fineFaceCochainEquiv A
          ((fineComplex A).d1 targetCycle.1) at hcomm
      rw [targetCycle.2, map_zero] at hcomm
      exact hcomm
    let rawSource : presentation.CoarseEdgeIn A → ℚ :=
      rawCoarseProjection A rawTarget
    have hrawSourceCycle :
        presentation.coarseD1LinearMap A rawSource = 0 := by
      exact coarseD1_rawCoarseProjection_eq_zero A rawTarget hrawTargetCycle
    let sourceCochain : (coarseComplex A).C1 :=
      (presentation.coarseEdgeCochainEquiv A).symm rawSource
    have hcycle : (coarseComplex A).d1 sourceCochain = 0 := by
      apply (presentation.coarseFaceCochainEquiv A).injective
      rw [map_zero]
      calc
        presentation.coarseFaceCochainEquiv A
            ((coarseComplex A).d1 sourceCochain) =
          presentation.coarseD1LinearMap A
            (presentation.coarseEdgeCochainEquiv A sourceCochain) := by
              simpa only [] using
                (presentation.coarseD1_commutes A sourceCochain).symm
        _ = presentation.coarseD1LinearMap A rawSource := by
          simp only [sourceCochain, LinearEquiv.apply_symm_apply]
        _ = 0 := hrawSourceCycle
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
    change presentation.edgePullback1LinearMap A rawSource = rawTarget
    exact edgePullback1_rawCoarseProjection_of_cycle A rawTarget hrawTargetCycle

/-! ## Exact uniformity and direct C5 failure -/

/-- Every executable A-subnerve defect is `(0,0)` by the actual H¹ theorem. -/
theorem all_computedASubnerveDefects_zero (A : Finset (Fin 2)) :
    presentation.computedASubnerveDefect A = (0, 0) := by
  rw [presentation.computedASubnerveDefect_eq_aSubnerveDefect]
  exact
    (presentation.toGeometry.aSubnerveDefect_eq_zero_iff_bijective
      (↑A : Set (Fin 2))).2
      (aSubnerveComparisonHom_h1Map_bijective A)

/-- The generic all-subset uniformity checker accepts the raw C5 fixture. -/
theorem uniformPresentationCheck_true :
    presentation.uniformPresentationCheck = true := by
  apply
    (presentation.uniformPresentationCheck_eq_true_iff_allNonemptyDefects).2
  intro A _hA
  exact all_computedASubnerveDefects_zero A

/-- The exact R1 presentation is semantically uniformly invariant. -/
theorem uniformPresentation : UniformPresentation presentation :=
  presentation.uniformPresentationCheck_eq_true_iff.mp
    uniformPresentationCheck_true

/-- The first chart-one coarse self-loop with duplicate fine lifts. -/
def failedCoarseEdge : presentation.CoarseEdge :=
  (show presentation.CoarseEdge from (1 : Fin 2))

/-- The first declared fine lift of the failed coarse edge. -/
def failedFineLeft : presentation.FineEdge :=
  (show presentation.FineEdge from (1 : Fin 3))

/-- The second, distinct declared fine lift of the failed coarse edge. -/
def failedFineRight : presentation.FineEdge :=
  (show presentation.FineEdge from (2 : Fin 3))

/-- The two displayed fine lifts are distinct. -/
theorem failedFineLeft_ne_failedFineRight :
    failedFineLeft ≠ failedFineRight := by
  intro hequal
  change (1 : Fin 3) = 2 at hequal
  omega

/-- Both distinct fine edges map to the same coarse edge in the raw table. -/
theorem failedLiftPair_same_image :
    presentation.edgeMap failedFineLeft = some failedCoarseEdge ∧
      presentation.edgeMap failedFineRight = some failedCoarseEdge := by
  constructor <;>
    rfl

/-- Raw whole-nerve C5 fails on the duplicate declared lifts. -/
theorem not_rawConditionC5 : ¬ presentation.RawConditionC5 := by
  intro hC5
  exact failedFineLeft_ne_failedFineRight
    (hC5 failedCoarseEdge failedFineLeft failedFineRight
      failedLiftPair_same_image.1 failedLiftPair_same_image.2)

/-- The executable whole-nerve C5 checker returns false. -/
theorem conditionC5Check_false : presentation.conditionC5Check = false := by
  apply Bool.eq_false_of_not_eq_true
  intro htrue
  exact not_rawConditionC5 (of_decide_eq_true htrue)

/-- Semantic whole-nerve C5 fails by the generic raw/semantic equivalence. -/
theorem not_conditionC5 : ¬ presentation.toGeometry.ConditionC5 := by
  intro hC5
  exact not_rawConditionC5
    (presentation.rawConditionC5_iff_conditionC5.mpr hC5)

/-- `ConditionCAllA` fails directly through its whole-nerve C5 projection. -/
theorem not_conditionCAllA : ¬ presentation.toGeometry.ConditionCAllA := by
  intro hAllA
  exact not_conditionC5 (hAllA.conditionC5 presentation.toGeometry)

/-- The aggregate finite checker is false by semantic soundness and C5. -/
theorem conditionCAllACheck_false : presentation.conditionCAllACheck = false := by
  apply Bool.eq_false_of_not_eq_true
  intro htrue
  exact not_conditionCAllA
    (presentation.conditionCAllACheck_eq_true_iff.mp htrue)

/-! ## Same-A support and law-indexed C5 failure -/

/-- The full coarse target subset meets the duplicate pair's common K1
support and retains the common nonzero chart-zero H¹ loop. -/
def targetFull : Finset (Fin 2) := Finset.univ

/-- The full target subset is nonempty. -/
theorem targetFull_nonempty : (↑targetFull : Set (Fin 2)).Nonempty :=
  ⟨0, by simp [targetFull]⟩

/-- The duplicate lift pair has the common fine target `2`, whose canonical
coarse image lies in the same full subset used for H¹ nonvanishing. -/
theorem failedLiftPair_support_meets_targetFull :
    ∃ fineTarget : presentation.FineTarget,
      fineTarget ∈ presentation.fineEdgeSupportFinset failedFineLeft ∧
      fineTarget ∈ presentation.fineEdgeSupportFinset failedFineRight ∧
      presentation.computedFactor fineTarget ∈ targetFull := by
  refine ⟨(2 : Fin 3), ?_, ?_, ?_⟩
  · rw [presentation.mem_fineEdgeSupportFinset_iff_raw]
    simp [presentation, failedFineLeft, fineChartSupport, fineEdgeChart]
  · rw [presentation.mem_fineEdgeSupportFinset_iff_raw]
    simp [presentation, failedFineRight, fineChartSupport, fineEdgeChart]
  · simp [targetFull]

/-- The canonical Boolean indicator family of the full coarse target subset. -/
noncomputable def indicatorLaws : FiniteLawFamily presentation.Source :=
  indicatorLawFamily presentation.coarseReading
    (↑targetFull : Set (Fin 2))

/-- Canonical adequacy of the full-subset indicator for the coarse reading. -/
theorem indicatorCoarseAdequate :
    indicatorLaws.Adequate presentation.coarseReading :=
  indicatorLawFamily_adequate presentation.coarseReading
    (↑targetFull : Set (Fin 2))

/-- Canonical adequacy of the same indicator for the fine reading. -/
theorem indicatorFineAdequate :
    indicatorLaws.Adequate presentation.fineReading :=
  indicatorLawFamily_adequate_of_coarserThan presentation.coarseReading
    presentation.fineReading presentation.coarserThan
    (↑targetFull : Set (Fin 2))

/-- The complete law-indexed Condition C package fails by its C5 field. -/
theorem indicator_not_conditionC :
    ¬ presentation.toGeometry.ConditionC indicatorLaws
      indicatorCoarseAdequate indicatorFineAdequate := by
  intro hC
  exact not_conditionC5 hC.c5

/-! ## Nonzero H¹ on the full block meeting the duplicate support -/

/-- The actual coarse full-target complex. -/
abbrev coarseTargetFullComplex : ThreeCochainComplex ℚ :=
  coarseComplex targetFull

/-- The actual fine complex on the canonical preimage of the full target. -/
abbrev fineTargetFullComplex : ThreeCochainComplex ℚ :=
  fineComplex targetFull

/-- The raw coarse chart-zero self-loop selected by the full target. -/
def coarseEdgeZero : presentation.CoarseEdgeIn targetFull :=
  ⟨(0 : Fin 2), by decide⟩

/-- The corresponding actual A-subnerve self-loop. -/
def coarseActualEdgeZero :
    presentation.coarseSupportedNerve.EdgeInTargetSubset
      (↑targetFull : Set (Fin 2)) :=
  presentation.coarseEdgeEquiv targetFull coarseEdgeZero

/-- Evaluation on the actual chart-zero self-loop. -/
def coarseTargetFullPeriod (cochain : coarseTargetFullComplex.C1) : ℚ :=
  cochain coarseActualEdgeZero

/-- Public evaluation rule for the period functional. -/
@[simp]
theorem coarseTargetFullPeriod_apply (cochain : coarseTargetFullComplex.C1) :
    coarseTargetFullPeriod cochain = cochain coarseActualEdgeZero :=
  rfl

/-- Every coarse coboundary has zero chart-zero loop period. -/
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

/-- The raw cochain which is one on chart-zero edge and zero on edge one. -/
def coarseTargetFullRawCochain :
    presentation.CoarseEdgeIn targetFull → ℚ :=
  fun edge => if (show Fin 2 from edge.1) = 0 then 1 else 0

/-- The same cochain on the actual A-subnerve via the canonical equivalence. -/
noncomputable def coarseTargetFullCochain : coarseTargetFullComplex.C1 :=
  (presentation.coarseEdgeCochainEquiv targetFull).symm
    coarseTargetFullRawCochain

/-- The raw chart-zero loop cochain satisfies the coarse repeated-face
cocycle equation. -/
theorem coarseTargetFullRawCochain_cocycle :
    presentation.coarseD1LinearMap targetFull
      coarseTargetFullRawCochain = 0 := by
  funext face
  rw [presentation.coarseD1LinearMap_apply]
  have hedge0 :
      (show Fin 2 from (presentation.coarseFaceEdge0In targetFull face).1) = 1 := rfl
  have hedge1 :
      (show Fin 2 from (presentation.coarseFaceEdge1In targetFull face).1) = 1 := rfl
  have hedge2 :
      (show Fin 2 from (presentation.coarseFaceEdge2In targetFull face).1) = 1 := rfl
  change
    (if (show Fin 2 from
          (presentation.coarseFaceEdge0In targetFull face).1) = 0 then 1 else 0) -
      (if (show Fin 2 from
          (presentation.coarseFaceEdge1In targetFull face).1) = 0 then 1 else 0) +
      (if (show Fin 2 from
          (presentation.coarseFaceEdge2In targetFull face).1) = 0 then 1 else 0) = 0
  rw [hedge0, hedge1, hedge2]
  norm_num

/-- The explicit actual cochain is a cocycle. -/
theorem coarseTargetFullCochain_cocycle :
    coarseTargetFullComplex.d1 coarseTargetFullCochain = 0 := by
  apply (presentation.coarseFaceCochainEquiv targetFull).injective
  rw [map_zero]
  calc
    presentation.coarseFaceCochainEquiv targetFull
        (coarseTargetFullComplex.d1 coarseTargetFullCochain) =
      presentation.coarseD1LinearMap targetFull
        (presentation.coarseEdgeCochainEquiv targetFull
          coarseTargetFullCochain) := by
            simpa only [] using
              (presentation.coarseD1_commutes targetFull
                coarseTargetFullCochain).symm
    _ = presentation.coarseD1LinearMap targetFull
        coarseTargetFullRawCochain := by
          simp only [coarseTargetFullCochain,
            LinearEquiv.apply_symm_apply]
    _ = 0 := coarseTargetFullRawCochain_cocycle

/-- The explicit loop cocycle in the actual degree-one kernel. -/
noncomputable def coarseTargetFullCycle :
    LinearMap.ker coarseTargetFullComplex.d1 :=
  ⟨coarseTargetFullCochain, coarseTargetFullCochain_cocycle⟩

/-- The literal quotient-H¹ class of the chart-zero loop. -/
noncomputable def coarseTargetFullClass : coarseTargetFullComplex.H1 :=
  (LinearMap.range coarseTargetFullComplex.boundaryToCycles).mkQ
    coarseTargetFullCycle

/-- The displayed cocycle has unit period. -/
theorem coarseTargetFullPeriod_cycle :
    coarseTargetFullPeriod coarseTargetFullCycle.1 = 1 := by
  have happly := congrFun
    ((presentation.coarseEdgeCochainEquiv targetFull).apply_symm_apply
      coarseTargetFullRawCochain) coarseEdgeZero
  change coarseTargetFullCochain
      (presentation.coarseEdgeEquiv targetFull coarseEdgeZero) = 1
  change coarseTargetFullCochain
      (presentation.coarseEdgeEquiv targetFull coarseEdgeZero) =
    coarseTargetFullRawCochain coarseEdgeZero at happly
  calc
    coarseTargetFullCochain
        (presentation.coarseEdgeEquiv targetFull coarseEdgeZero) =
      coarseTargetFullRawCochain coarseEdgeZero := happly
    _ = 1 := by rfl

/-- The coarse full-target quotient class is nonzero by the period argument. -/
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

/-- The coarse full-target H¹ space has positive dimension. -/
theorem targetFull_coarse_h1_pos :
    0 < Module.finrank ℚ coarseTargetFullComplex.H1 :=
  Module.finrank_pos_iff_exists_ne_zero.mpr
    ⟨coarseTargetFullClass, coarseTargetFullClass_ne_zero⟩

/-- The corresponding fine class is the actual canonical H¹ image. -/
noncomputable def fineTargetFullClass : fineTargetFullComplex.H1 :=
  (presentation.toGeometry.aSubnerveComparisonHom
    (↑targetFull : Set (Fin 2))).h1Map coarseTargetFullClass

/-- The fine image class is nonzero by actual-map injectivity. -/
theorem fineTargetFullClass_ne_zero : fineTargetFullClass ≠ 0 := by
  intro hzero
  apply coarseTargetFullClass_ne_zero
  apply (aSubnerveComparisonHom_h1Map_bijective targetFull).1
  simpa only [fineTargetFullClass, map_zero] using hzero

/-- The fine full-target H¹ space has positive dimension. -/
theorem targetFull_fine_h1_pos :
    0 < Module.finrank ℚ fineTargetFullComplex.H1 :=
  Module.finrank_pos_iff_exists_ne_zero.mpr
    ⟨fineTargetFullClass, fineTargetFullClass_ne_zero⟩

/-- Both actual H¹ spaces are nonzero on the same full subset that meets the
duplicate pair's common support. -/
theorem targetFull_both_h1_pos :
    0 < Module.finrank ℚ coarseTargetFullComplex.H1 ∧
      0 < Module.finrank ℚ fineTargetFullComplex.H1 :=
  ⟨targetFull_coarse_h1_pos, targetFull_fine_h1_pos⟩

/-! ## Bounded R1 necessity conclusion -/

/-- Exact C5 non-necessity witness: the presentation is uniformly invariant,
fails whole-nerve C5 and ConditionCAllA directly, the duplicate support meets
the named full subset, and actual H¹ is nonzero on both sides there. -/
theorem c5_not_necessary :
    UniformPresentation presentation ∧
      ¬ presentation.toGeometry.ConditionC indicatorLaws
        indicatorCoarseAdequate indicatorFineAdequate ∧
      ¬ presentation.toGeometry.ConditionC5 ∧
      ¬ presentation.toGeometry.ConditionCAllA ∧
      (∃ fineTarget : presentation.FineTarget,
        fineTarget ∈ presentation.fineEdgeSupportFinset failedFineLeft ∧
        fineTarget ∈ presentation.fineEdgeSupportFinset failedFineRight ∧
        presentation.computedFactor fineTarget ∈ targetFull) ∧
      0 < Module.finrank ℚ coarseTargetFullComplex.H1 ∧
      0 < Module.finrank ℚ fineTargetFullComplex.H1 :=
  ⟨uniformPresentation, indicator_not_conditionC, not_conditionC5,
    not_conditionCAllA, failedLiftPair_support_meets_targetFull,
    targetFull_both_h1_pos.1, targetFull_both_h1_pos.2⟩

end R1ConditionC5Witness

end AAT.AG.ResolutionInvariance

#assert_standard_axioms_only AAT.AG.ResolutionInvariance.R1ConditionC5Witness
