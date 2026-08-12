import ResearchLean.AG.UniformInvariance.ConditionCAllAChecker
import ResearchLean.AG.UniformInvariance.UniformPresentationDecider
import Formal.Util.AssertStandardAxioms

/-!
# A uniform comparison outside the C6 locus

This module formalizes the exact `C6_not_necessary` fixture from the bounded
R1 necessity map for `G-107-aat-uniform-invariance-characterization`.  The
parent R1 payload has SHA-256
`ff2d9fa12eb64bf343d3148f081e1164d4216d8548e53d90550eb53886dd359a`,
and the canonical name-free serializer recomputes SHA-256
`01839cd41c6418c92315cf1ea4693647c3109f077c32961cf929fefa1f98e91f`.

The coarse nerve has a chart-zero self-loop and a chart-one self-loop killed
by a repeated face.  The fine nerve has the same chart-zero self-loop and an
interval edge from charts one to two, with no faces.  The interval maps to the
coarse chart-one self-loop, so whole-nerve endpoint reflection C6 fails.  In
H¹, the coarse repeated face kills precisely the mapped loop coefficient,
while the fine interval is precisely a degree-zero boundary.  The actual H¹
comparison is therefore bijective for every target subset.

The experiment payload directly fixes the factor, target counts, nerves,
supports, and cell maps.  The `Fin 3` source and raw readings below are the
canonical finite realization of that factor.  The presentation stores no
factor, endpoint-reflection certificate, matrix, rank, cohomology class,
defect, checker result, or uniformity certificate.
-/

namespace AAT.AG.ResolutionInvariance

open CanonicalResolution Cohomology TwoPhase

namespace R1ConditionC6Witness

/-! ## Exact raw R1 presentation -/

/-- The proper coarse reading table `[0,0,1]`, used as raw presentation input. -/
def coarseRead (source : Fin 3) : Fin 2 :=
  if source = 2 then 1 else 0

/-- Coarse chart supports `[{0},{1}]`, containing no C6 result. -/
def coarseChartSupport (chart : Fin 2) : Finset (Fin 2) :=
  if chart = 0 then {0} else {1}

/-- Fine chart supports `[{0,1},{2},{2}]`, realizing the proper factor. -/
def fineChartSupport (chart : Fin 3) : Finset (Fin 3) :=
  if chart = 0 then {0, 1} else {2}

/-- Left endpoints of the fine loop and interval. -/
def fineEdgeLeft (edge : Fin 2) : Fin 3 :=
  if edge = 0 then 0 else 1

/-- Right endpoints of the fine loop and interval. -/
def fineEdgeRight (edge : Fin 2) : Fin 3 :=
  if edge = 0 then 0 else 2

/-- Both fine charts over coarse chart one use the same raw chart map. -/
def rawChartMap (chart : Fin 3) : Fin 2 :=
  if chart = 0 then 0 else 1

/-- Exact finite R1 C6 presentation.  Its fields contain only finite raw
geometry and well-formedness proofs; no C6 or H¹ answer is stored.

Position: existing C6 witness input reused by the Cycle 23 production-kernel
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
  FineChart := Fin 3
  fineChartFintype := inferInstance
  fineChartDecidableEq := inferInstance
  fineChartEntries := List.finRange 3
  fineChart_mem_fineChartEntries := by intro chart; simp
  FineEdge := Fin 2
  fineEdgeFintype := inferInstance
  fineEdgeDecidableEq := inferInstance
  fineEdgeEntries := List.finRange 2
  fineEdge_mem_fineEdgeEntries := by intro edge; simp
  FineFace := Fin 0
  fineFaceFintype := inferInstance
  fineFaceDecidableEq := inferInstance
  fineFaceEntries := List.finRange 0
  fineFace_mem_fineFaceEntries := by intro face; exact nomatch face
  fineEdgeLeft := fineEdgeLeft
  fineEdgeRight := fineEdgeRight
  fineFaceEdge0 := Fin.elim0
  fineFaceEdge1 := Fin.elim0
  fineFaceEdge2 := Fin.elim0
  fineFaceEdge0_left := by intro face; exact Fin.elim0 face
  fineFaceEdge0_right := by intro face; exact Fin.elim0 face
  fineFaceEdge1_right := by intro face; exact Fin.elim0 face
  fineChartSupport := fineChartSupport
  fineChartSupport_nonempty := by
    intro chart
    fin_cases chart <;> simp [fineChartSupport]
  chartMap := rawChartMap
  edgeMap := some
  faceMap := Fin.elim0
  edge_some_left := by
    intro fineEdge coarseEdge hmap
    have heq := Option.some.inj hmap
    subst coarseEdge
    fin_cases fineEdge <;>
      simp [fineEdgeLeft, rawChartMap]
  edge_some_right := by
    intro fineEdge coarseEdge hmap
    have heq := Option.some.inj hmap
    subst coarseEdge
    fin_cases fineEdge <;>
      simp [fineEdgeRight, rawChartMap]
  edge_none_fiber := by intro fineEdge hmap; simp at hmap
  face_some_edge0 := by intro fineFace; exact Fin.elim0 fineFace
  face_some_edge1 := by intro fineFace; exact Fin.elim0 fineFace
  face_some_edge2 := by intro fineFace; exact Fin.elim0 fineFace
  face_none_edge0 := by intro fineFace; exact Fin.elim0 fineFace
  face_none_edge1 := by intro fineFace; exact Fin.elim0 fineFace
  face_none_edge2 := by intro fineFace; exact Fin.elim0 fineFace
  chartSupport_compatible_source := by
    intro fineChart source hsource
    fin_cases fineChart <;> fin_cases source <;>
      simp [fineChartSupport, coarseChartSupport, coarseRead, rawChartMap] at hsource ⊢

/-! ## Canonical factor and raw selected cells -/

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

/-- Selected fine and coarse edge tables coincide for every target subset. -/
theorem fineEdgesIn_eq_coarseEdgesIn (A : Finset (Fin 2)) :
    presentation.fineEdgesIn A = presentation.coarseEdgesIn A := by
  ext edge
  rw [presentation.mem_fineEdgesIn_iff_raw,
    presentation.mem_coarseEdgesIn_iff_raw, computedFactor_eq_coarseRead]
  simp only [presentation.mem_fineEdgeSupportFinset_iff_raw,
    presentation.mem_coarseEdgeSupportFinset_iff_raw]
  fin_cases edge <;>
    simp [presentation, fineChartSupport, coarseChartSupport, fineEdgeLeft,
      fineEdgeRight, coarseRead]

/-- Forgetting selection proofs identifies selected fine and coarse edges. -/
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

/-- Reindex coarse edge cochains through the raw edge identity. -/
def rawEdgeCochainEquiv (A : Finset (Fin 2)) :
    (presentation.CoarseEdgeIn A → ℚ) ≃ₗ[ℚ]
      (presentation.FineEdgeIn A → ℚ) :=
  cochainEquivOfIndexEquiv (selectedEdgeEquiv A)

/-- The selected raw edge map is exactly the selected-edge equivalence. -/
theorem edgeMapOptionIn_eq_some_selected (A : Finset (Fin 2))
    (edge : presentation.FineEdgeIn A) :
    presentation.edgeMapOptionIn A edge = some (selectedEdgeEquiv A edge) := by
  exact (presentation.edgeMapOptionIn_eq_some_iff A edge
    (selectedEdgeEquiv A edge)).2 rfl

/-- Raw degree-one pullback is the edge reindexing induced by the identity
edge table. -/
theorem edgePullback1_eq_rawEdgeCochainEquiv (A : Finset (Fin 2))
    (cochain : presentation.CoarseEdgeIn A → ℚ) :
    presentation.edgePullback1LinearMap A cochain =
      rawEdgeCochainEquiv A cochain := by
  funext edge
  rw [presentation.edgePullback1LinearMap_apply,
    edgeMapOptionIn_eq_some_selected]
  rfl

/-- Coarse edge one is selected exactly when target one is selected. -/
theorem coarseEdgeOne_mem_iff_one_mem (A : Finset (Fin 2)) :
    (1 : Fin 2) ∈ presentation.coarseEdgesIn A ↔ (1 : Fin 2) ∈ A := by
  rw [presentation.mem_coarseEdgesIn_iff_raw]
  simp only [presentation.mem_coarseEdgeSupportFinset_iff_raw]
  simp [presentation, coarseChartSupport]

/-- The coarse repeated face is selected exactly when target one is selected. -/
theorem coarseFaceZero_mem_iff_one_mem (A : Finset (Fin 2)) :
    (0 : Fin 1) ∈ presentation.coarseFacesIn A ↔ (1 : Fin 2) ∈ A := by
  rw [presentation.mem_coarseFacesIn_iff_raw]
  simp only [presentation.mem_coarseFaceSupportFinset_iff_raw,
    presentation.mem_coarseEdgeSupportFinset_iff_raw]
  simp [presentation, coarseChartSupport]

/-! ## Raw cocycles and interval boundaries -/

/-- A coarse raw cocycle has zero coefficient on edge one because the
selected repeated face evaluates that coefficient. -/
theorem coarse_edge_one_eq_zero_of_d1_eq_zero
    (A : Finset (Fin 2))
    (cochain : presentation.CoarseEdgeIn A → ℚ)
    (hcocycle : presentation.coarseD1LinearMap A cochain = 0)
    (edge : presentation.CoarseEdgeIn A)
    (hone : (show Fin 2 from edge.1) = 1) : cochain edge = 0 := by
  have honeMem : (1 : Fin 2) ∈ A :=
    (coarseEdgeOne_mem_iff_one_mem A).1 (hone ▸ edge.2)
  let face : presentation.CoarseFaceIn A :=
    ⟨(0 : Fin 1), (coarseFaceZero_mem_iff_one_mem A).2 honeMem⟩
  have hvalue := congrFun hcocycle face
  rw [presentation.coarseD1LinearMap_apply] at hvalue
  simp only [Pi.zero_apply] at hvalue
  have hedge0 : presentation.coarseFaceEdge0In A face = edge := by
    apply Subtype.ext
    exact hone.symm
  have hedge1 : presentation.coarseFaceEdge1In A face = edge := by
    apply Subtype.ext
    exact hone.symm
  have hedge2 : presentation.coarseFaceEdge2In A face = edge := by
    apply Subtype.ext
    exact hone.symm
  simpa [hedge0, hedge1, hedge2] using hvalue

/-- A raw fine chart primitive for an edge cochain whose self-loop
coefficient is zero.  It places the interval coefficient at chart two. -/
noncomputable def rawFineIntervalPrimitive (A : Finset (Fin 2))
    (cochain : presentation.FineEdgeIn A → ℚ) :
    presentation.FineChartIn A → ℚ := fun chart =>
  ∑ edge : presentation.FineEdgeIn A,
    if (show Fin 2 from edge.1) = 1 ∧
        (show Fin 3 from chart.1) = 2 then cochain edge else 0

/-- The fine interval primitive differentiates to any raw cochain whose
chart-zero self-loop coefficient vanishes. -/
theorem fineD0_rawFineIntervalPrimitive
    (A : Finset (Fin 2)) (cochain : presentation.FineEdgeIn A → ℚ)
    (hloop : ∀ edge, (show Fin 2 from edge.1) = 0 → cochain edge = 0) :
    presentation.fineD0LinearMap A (rawFineIntervalPrimitive A cochain) =
      cochain := by
  classical
  funext edge
  rw [presentation.fineD0LinearMap_apply]
  have hedgeCases : (show Fin 2 from edge.1) = 0 ∨
      (show Fin 2 from edge.1) = 1 := by omega
  rcases hedgeCases with hedge | hedge
  · have hend : presentation.fineEdgeRightIn A edge =
        presentation.fineEdgeLeftIn A edge := by
      apply Subtype.ext
      simp [presentation, hedge, fineEdgeLeft, fineEdgeRight]
    rw [hend, sub_self]
    exact (hloop edge hedge).symm
  · have hleft :
        (show Fin 3 from (presentation.fineEdgeLeftIn A edge).1) = 1 := by
      simp [presentation, hedge, fineEdgeLeft]
    have hright :
        (show Fin 3 from (presentation.fineEdgeRightIn A edge).1) = 2 := by
      simp [presentation, hedge, fineEdgeRight]
    have hrightValue :
        rawFineIntervalPrimitive A cochain
            (presentation.fineEdgeRightIn A edge) = cochain edge := by
      simp only [rawFineIntervalPrimitive, hright, and_true]
      rw [Fintype.sum_eq_single edge]
      · simp [hedge]
      · intro candidate hne
        split_ifs with hcandidate
        · exact False.elim
            (hne (Subtype.ext (hcandidate.trans hedge.symm)))
        · rfl
    have hleftValue :
        rawFineIntervalPrimitive A cochain
            (presentation.fineEdgeLeftIn A edge) = 0 := by
      simp only [rawFineIntervalPrimitive]
      apply Finset.sum_eq_zero
      intro candidate _hmember
      split_ifs with hcandidate
      · have hcontra :
            (show Fin 3 from
              (presentation.fineEdgeLeftIn A edge).1) = 2 :=
          hcandidate.2
        omega
      · rfl
    rw [hrightValue, hleftValue, sub_zero]

/-! ## Actual quotient-H¹ comparison on every target subset -/

/-- The actual coarse constant-rational A-subnerve complex. -/
abbrev coarseComplex (A : Finset (Fin 2)) : ThreeCochainComplex ℚ :=
  presentation.coarseSupportedNerve.targetSubsetComplex (↑A : Set (Fin 2))

/-- The actual fine complex on the canonical preimage of `A`. -/
abbrev fineComplex (A : Finset (Fin 2)) : ThreeCochainComplex ℚ :=
  presentation.fineSupportedNerve.targetSubsetComplex
    (presentation.canonicalFinePreimage A)

/-- Degree-one equivalence between the actual selected edge cochains. -/
noncomputable def semanticEdgeCochainEquiv (A : Finset (Fin 2)) :
    (coarseComplex A).C1 ≃ₗ[ℚ] (fineComplex A).C1 :=
  (presentation.coarseEdgeCochainEquiv A).trans
    ((rawEdgeCochainEquiv A).trans
      (presentation.fineEdgeCochainEquiv A).symm)

/-- The actual comparison degree-one map equals the raw edge reindexing. -/
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

/-- A raw fine degree-zero boundary vanishes on the chart-zero self-loop. -/
theorem fineD0_eq_zero_at_loop
    (A : Finset (Fin 2))
    (cochain : presentation.FineChartIn A → ℚ)
    (edge : presentation.FineEdgeIn A)
    (hzero : (show Fin 2 from edge.1) = 0) :
    presentation.fineD0LinearMap A cochain edge = 0 := by
  rw [presentation.fineD0LinearMap_apply]
  have hloop : presentation.fineEdgeRightIn A edge =
      presentation.fineEdgeLeftIn A edge := by
    apply Subtype.ext
    simp [presentation, hzero, fineEdgeLeft, fineEdgeRight]
  rw [hloop, sub_self]

/-- Keep only the fine chart-zero loop coefficient as a raw coarse cochain. -/
def rawCoarseLoopProjection (A : Finset (Fin 2))
    (cochain : presentation.FineEdgeIn A → ℚ) :
    presentation.CoarseEdgeIn A → ℚ := fun edge =>
  if (show Fin 2 from edge.1) = 0 then
    cochain ((selectedEdgeEquiv A).symm edge)
  else 0

/-- The loop projection is a coarse raw cocycle because the repeated face
sees only coarse edge one. -/
theorem coarseD1_rawCoarseLoopProjection_eq_zero
    (A : Finset (Fin 2))
    (cochain : presentation.FineEdgeIn A → ℚ) :
    presentation.coarseD1LinearMap A
      (rawCoarseLoopProjection A cochain) = 0 := by
  funext face
  simp only [Pi.zero_apply]
  rw [presentation.coarseD1LinearMap_apply]
  have hedge0 :
      (show Fin 2 from (presentation.coarseFaceEdge0In A face).1) = 1 := rfl
  have hedge1 : presentation.coarseFaceEdge1In A face =
      presentation.coarseFaceEdge0In A face := Subtype.ext rfl
  have hedge2 : presentation.coarseFaceEdge2In A face =
      presentation.coarseFaceEdge0In A face := Subtype.ext rfl
  rw [hedge1, hedge2]
  simp [rawCoarseLoopProjection, hedge0]

/-- Pulling back the loop projection agrees with the original fine cochain on
the fine self-loop, so their difference has zero loop coefficient. -/
theorem rawEdgeCochainEquiv_projection_sub_eq_zero_at_loop
    (A : Finset (Fin 2))
    (cochain : presentation.FineEdgeIn A → ℚ)
    (edge : presentation.FineEdgeIn A)
    (hzero : (show Fin 2 from edge.1) = 0) :
    (rawEdgeCochainEquiv A (rawCoarseLoopProjection A cochain) - cochain)
      edge = 0 := by
  change rawCoarseLoopProjection A cochain (selectedEdgeEquiv A edge) -
      cochain edge = 0
  have hcoarseZero :
      (show Fin 2 from (selectedEdgeEquiv A edge).1) = 0 := hzero
  rw [rawCoarseLoopProjection]
  simp only [if_pos hcoarseZero]
  have hinv : (selectedEdgeEquiv A).symm (selectedEdgeEquiv A edge) = edge :=
    (selectedEdgeEquiv A).symm_apply_apply edge
  rw [hinv, sub_self]

/-- The actual canonical H¹ comparison is bijective on every target subset.
Injectivity combines the coarse repeated-face equation with vanishing of fine
boundaries on the common self-loop.  Surjectivity removes the fine interval
coefficient by an explicit degree-zero primitive. -/
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
    let rawDifference : presentation.CoarseEdgeIn A → ℚ :=
      presentation.coarseEdgeCochainEquiv A (leftCycle.1 - rightCycle.1)
    have hcycleDifference :
        (coarseComplex A).d1 (leftCycle.1 - rightCycle.1) = 0 := by
      rw [map_sub, leftCycle.2, rightCycle.2, sub_self]
    have hrawCycle :
        presentation.coarseD1LinearMap A rawDifference = 0 := by
      have hcomm := presentation.coarseD1_commutes A
        (leftCycle.1 - rightCycle.1)
      change presentation.coarseD1LinearMap A
          (presentation.coarseEdgeCochainEquiv A
            (leftCycle.1 - rightCycle.1)) = 0
      calc
        presentation.coarseD1LinearMap A
            (presentation.coarseEdgeCochainEquiv A
              (leftCycle.1 - rightCycle.1)) =
          presentation.coarseFaceCochainEquiv A
            ((coarseComplex A).d1 (leftCycle.1 - rightCycle.1)) := hcomm
        _ = 0 := by rw [hcycleDifference, map_zero]
    have hrawBoundary :
        presentation.fineD0LinearMap A
            (presentation.fineChartCochainEquiv A fineCochain) =
          presentation.edgePullback1LinearMap A rawDifference := by
      have hd0 := presentation.fineD0_commutes A fineCochain
      have hf1 := presentation.edgePullback1_commutes A
        (leftCycle.1 - rightCycle.1)
      change presentation.fineD0LinearMap A
          (presentation.fineChartCochainEquiv A fineCochain) =
        presentation.fineEdgeCochainEquiv A
          ((fineComplex A).d0 fineCochain) at hd0
      change presentation.edgePullback1LinearMap A rawDifference =
        presentation.fineEdgeCochainEquiv A
          ((presentation.toGeometry.aSubnerveComparisonHom
            (↑A : Set (Fin 2))).f1 (leftCycle.1 - rightCycle.1)) at hf1
      rw [hd0, hf1]
      apply congrArg (presentation.fineEdgeCochainEquiv A)
      simpa only [map_sub] using hvalues
    have hrawDifferenceZero : rawDifference = 0 := by
      funext edge
      have hedgeCases : (show Fin 2 from edge.1) = 0 ∨
          (show Fin 2 from edge.1) = 1 := by omega
      rcases hedgeCases with hzero | hone
      · let fineEdge : presentation.FineEdgeIn A :=
          (selectedEdgeEquiv A).symm edge
        have hfineZero : (show Fin 2 from fineEdge.1) = 0 := hzero
        have hvalue := congrFun hrawBoundary fineEdge
        rw [fineD0_eq_zero_at_loop A _ fineEdge hfineZero] at hvalue
        rw [edgePullback1_eq_rawEdgeCochainEquiv] at hvalue
        change 0 = rawDifference (selectedEdgeEquiv A fineEdge) at hvalue
        rw [(selectedEdgeEquiv A).apply_symm_apply edge] at hvalue
        exact hvalue.symm
      · exact coarse_edge_one_eq_zero_of_d1_eq_zero A rawDifference
          hrawCycle edge hone
    have hactualDifference : leftCycle.1 - rightCycle.1 = 0 := by
      apply (presentation.coarseEdgeCochainEquiv A).injective
      rw [map_zero]
      exact hrawDifferenceZero
    have hcycles : leftCycle = rightCycle := by
      apply Subtype.ext
      exact sub_eq_zero.mp hactualDifference
    rw [hcycles]
  · intro targetClass
    obtain ⟨targetCycle, rfl⟩ :=
      (LinearMap.range (fineComplex A).boundaryToCycles).mkQ_surjective targetClass
    let rawTarget : presentation.FineEdgeIn A → ℚ :=
      presentation.fineEdgeCochainEquiv A targetCycle.1
    let rawSource : presentation.CoarseEdgeIn A → ℚ :=
      rawCoarseLoopProjection A rawTarget
    let sourceCochain : (coarseComplex A).C1 :=
      (presentation.coarseEdgeCochainEquiv A).symm rawSource
    have hsourceCycle : (coarseComplex A).d1 sourceCochain = 0 := by
      apply (presentation.coarseFaceCochainEquiv A).injective
      rw [map_zero]
      have hcomm := presentation.coarseD1_commutes A sourceCochain
      calc
        presentation.coarseFaceCochainEquiv A
            ((coarseComplex A).d1 sourceCochain) =
          presentation.coarseD1LinearMap A
            (presentation.coarseEdgeCochainEquiv A sourceCochain) := by
              simpa only [] using hcomm.symm
        _ = presentation.coarseD1LinearMap A rawSource := by
          simp only [sourceCochain, LinearEquiv.apply_symm_apply]
        _ = 0 := coarseD1_rawCoarseLoopProjection_eq_zero A rawTarget
    let sourceCycle : LinearMap.ker (coarseComplex A).d1 :=
      ⟨sourceCochain, hsourceCycle⟩
    let rawDifference : presentation.FineEdgeIn A → ℚ :=
      rawEdgeCochainEquiv A rawSource - rawTarget
    have hloop : ∀ edge, (show Fin 2 from edge.1) = 0 →
        rawDifference edge = 0 := by
      intro edge hzero
      exact rawEdgeCochainEquiv_projection_sub_eq_zero_at_loop
        A rawTarget edge hzero
    let rawPrimitive := rawFineIntervalPrimitive A rawDifference
    let semanticPrimitive : (fineComplex A).C0 :=
      (presentation.fineChartCochainEquiv A).symm rawPrimitive
    have hboundary : (fineComplex A).d0 semanticPrimitive =
        (presentation.toGeometry.aSubnerveComparisonHom
          (↑A : Set (Fin 2))).f1 sourceCochain - targetCycle.1 := by
      apply (presentation.fineEdgeCochainEquiv A).injective
      have hd0 := presentation.fineD0_commutes A semanticPrimitive
      change presentation.fineD0LinearMap A
          (presentation.fineChartCochainEquiv A semanticPrimitive) =
        presentation.fineEdgeCochainEquiv A
          ((fineComplex A).d0 semanticPrimitive) at hd0
      rw [← hd0]
      change presentation.fineD0LinearMap A rawPrimitive = _
      rw [fineD0_rawFineIntervalPrimitive A rawDifference hloop]
      change rawEdgeCochainEquiv A rawSource - rawTarget = _
      rw [map_sub]
      have hf1 := presentation.edgePullback1_commutes A sourceCochain
      change presentation.edgePullback1LinearMap A rawSource =
        presentation.fineEdgeCochainEquiv A
          ((presentation.toGeometry.aSubnerveComparisonHom
            (↑A : Set (Fin 2))).f1 sourceCochain) at hf1
      rw [edgePullback1_eq_rawEdgeCochainEquiv] at hf1
      rw [hf1]
    refine ⟨(LinearMap.range (coarseComplex A).boundaryToCycles).mkQ
      sourceCycle, ?_⟩
    rw [ThreeCochainComplex.Hom.h1Map_mk]
    apply (Submodule.Quotient.eq _).2
    refine ⟨semanticPrimitive, ?_⟩
    apply Subtype.ext
    change (fineComplex A).d0 semanticPrimitive =
      (presentation.toGeometry.aSubnerveComparisonHom
        (↑A : Set (Fin 2))).f1 sourceCochain - targetCycle.1
    exact hboundary

/-! ## Uniformity and direct C6 failure -/

/-- Every executable A-subnerve defect is `(0,0)`, via the generic
raw-to-actual theorem and the literal quotient-H¹ proof above. -/
theorem all_computedASubnerveDefects_zero (A : Finset (Fin 2)) :
    presentation.computedASubnerveDefect A = (0, 0) := by
  rw [presentation.computedASubnerveDefect_eq_aSubnerveDefect]
  exact
    (presentation.toGeometry.aSubnerveDefect_eq_zero_iff_bijective
      (↑A : Set (Fin 2))).2
      (aSubnerveComparisonHom_h1Map_bijective A)

/-- The generic all-subset uniformity checker accepts the raw fixture because
all actual H¹ defects vanish. -/
theorem uniformPresentationCheck_true :
    presentation.uniformPresentationCheck = true := by
  apply
    (presentation.uniformPresentationCheck_eq_true_iff_allNonemptyDefects).2
  intro A _hA
  exact all_computedASubnerveDefects_zero A

/-- The exact R1 presentation is semantically uniformly invariant, retaining
the internal quantification over all law families and adequacy proofs. -/
theorem uniformPresentation : UniformPresentation presentation :=
  presentation.uniformPresentationCheck_eq_true_iff.mp
    uniformPresentationCheck_true

/-- The fine interval edge which maps to a coarse self-loop. -/
def failedFineEdge : presentation.FineEdge :=
  (show Fin 2 from 1)

/-- The mapped coarse chart-one self-loop. -/
def failedCoarseEdge : presentation.CoarseEdge :=
  (show Fin 2 from 1)

/-- Raw C6 fails because the displayed fine interval has distinct endpoints
but maps to the displayed coarse self-loop. -/
theorem not_rawConditionC6 : ¬ presentation.RawConditionC6 := by
  intro hC6
  have hendpoints := hC6 failedFineEdge failedCoarseEdge rfl rfl
  change (1 : Fin 3) = 2 at hendpoints
  exact (by decide : (1 : Fin 3) ≠ 2) hendpoints

/-- The executable whole-nerve C6 checker returns false. -/
theorem conditionC6Check_false : presentation.conditionC6Check = false := by
  apply Bool.eq_false_of_not_eq_true
  intro htrue
  exact not_rawConditionC6 (of_decide_eq_true htrue)

/-- Semantic whole-nerve C6 fails by the generic raw/semantic equivalence. -/
theorem not_conditionC6 : ¬ presentation.toGeometry.ConditionC6 := by
  intro hC6
  exact not_rawConditionC6
    (presentation.rawConditionC6_iff_conditionC6.mpr hC6)

/-- `ConditionCAllA` fails directly by its whole-nerve C6 projection. -/
theorem not_conditionCAllA : ¬ presentation.toGeometry.ConditionCAllA := by
  intro hAllA
  exact not_conditionC6 (hAllA.conditionC6 presentation.toGeometry)

/-- The generic aggregate Condition C checker is false by semantic soundness
and the direct C6 obstruction. -/
theorem conditionCAllACheck_false :
    presentation.conditionCAllACheck = false := by
  apply Bool.eq_false_of_not_eq_true
  intro htrue
  exact not_conditionCAllA
    (presentation.conditionCAllACheck_eq_true_iff.mp htrue)

/-! ## Same-A support and law-indexed failure -/

/-- The full coarse target subset meets the failed edge support and retains
the common chart-zero H¹ loop. -/
def targetFull : Finset (Fin 2) := Finset.univ

/-- The full target subset is nonempty. -/
theorem targetFull_nonempty : (↑targetFull : Set (Fin 2)).Nonempty :=
  ⟨0, by simp [targetFull]⟩

/-- The failed fine interval has support target `2`, whose canonical image is
in the same full subset used for H¹ nonvanishing. -/
theorem failedFineEdge_support_meets_targetFull :
    ∃ fineTarget : presentation.FineTarget,
      fineTarget ∈ presentation.fineEdgeSupportFinset failedFineEdge ∧
      presentation.computedFactor fineTarget ∈ targetFull := by
  refine ⟨(2 : Fin 3), ?_, ?_⟩
  · rw [presentation.mem_fineEdgeSupportFinset_iff_raw]
    simp [presentation, failedFineEdge, fineChartSupport, fineEdgeLeft,
      fineEdgeRight]
  · simp [targetFull]

/-- The canonical Boolean indicator family of the full target subset. -/
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

/-- The complete law-indexed Condition C package fails by its C6 field. -/
theorem indicator_not_conditionC :
    ¬ presentation.toGeometry.ConditionC indicatorLaws
      indicatorCoarseAdequate indicatorFineAdequate := by
  intro hC
  exact not_conditionC6 hC.c6

/-! ## Nonzero H¹ on the full block meeting the failed edge support -/

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

/-- Public evaluation rule for the full-target period functional. -/
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
failed edge support. -/
theorem targetFull_both_h1_pos :
    0 < Module.finrank ℚ coarseTargetFullComplex.H1 ∧
      0 < Module.finrank ℚ fineTargetFullComplex.H1 :=
  ⟨targetFull_coarse_h1_pos, targetFull_fine_h1_pos⟩

/-! ## Bounded R1 necessity conclusion -/

/-- Exact C6 non-necessity witness: the presentation is uniformly invariant,
fails whole-nerve C6 and ConditionCAllA directly, the failed edge support
meets the named full subset, and actual H¹ is nonzero on both sides there. -/
theorem c6_not_necessary :
    UniformPresentation presentation ∧
      ¬ presentation.toGeometry.ConditionC indicatorLaws
        indicatorCoarseAdequate indicatorFineAdequate ∧
      ¬ presentation.toGeometry.ConditionC6 ∧
      ¬ presentation.toGeometry.ConditionCAllA ∧
      (∃ fineTarget : presentation.FineTarget,
        fineTarget ∈ presentation.fineEdgeSupportFinset failedFineEdge ∧
        presentation.computedFactor fineTarget ∈ targetFull) ∧
      0 < Module.finrank ℚ coarseTargetFullComplex.H1 ∧
      0 < Module.finrank ℚ fineTargetFullComplex.H1 :=
  ⟨uniformPresentation, indicator_not_conditionC, not_conditionC6,
    not_conditionCAllA, failedFineEdge_support_meets_targetFull,
    targetFull_both_h1_pos.1, targetFull_both_h1_pos.2⟩

end R1ConditionC6Witness

end AAT.AG.ResolutionInvariance

#assert_standard_axioms_only AAT.AG.ResolutionInvariance.R1ConditionC6Witness
